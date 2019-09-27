theory AOT_Syntax_next
  imports AOT_Axioms AOT_Instantiation
begin

declare[[eta_contract = false]]
no_notation AOT_valid_in ("[_ \<Turnstile> _]")
notation AOT_valid_in ("[_ \<^bold>\<Turnstile> _]")

nonterminal \<phi>
nonterminal \<nu>
nonterminal \<Pi>
nonterminal \<Pi>0
nonterminal \<tau>
nonterminal AOT_id
nonterminal AOT_desc
nonterminal AOT_ids

consts dummyRel :: "<'a>"


syntax
  "" :: "\<Pi> \<Rightarrow> \<tau>" ("_")
  "" :: "\<Pi>0 \<Rightarrow> \<tau>" ("_")
  "" :: "id_position \<Rightarrow> \<tau>" ("_")
  "" :: "AOT_desc \<Rightarrow> \<tau>" ("_")
  AOT_valid_in :: "[i, \<phi>] \<Rightarrow> bool" ("[_ \<Turnstile> _]")

  "" :: "\<phi> \<Rightarrow> \<phi>" ("'(_')")
  AOT_not :: "\<phi> \<Rightarrow> \<phi>" ("\<not>_" [40] 70)
  AOT_not :: "\<phi> \<Rightarrow> \<phi>" ("~_" [40] 70)
  AOT_imp :: "[\<phi>, \<phi>] \<Rightarrow> \<phi>" (infixl "\<rightarrow>" 8)
  AOT_box :: "\<phi> \<Rightarrow> \<phi>" ("\<box>_" [62] 63)
  AOT_act :: "\<phi> \<Rightarrow> \<phi>" ("\<^bold>\<A>_" [64] 65)
  AOT_dia :: "\<phi> \<Rightarrow> \<phi>" ("\<diamond>_" [62] 63)
  AOT_conj :: "[\<phi>, \<phi>] \<Rightarrow> \<phi>" (infixl "&" 35)
  AOT_conj :: "[\<phi>, \<phi>] \<Rightarrow> \<phi>" (infixl "\<and>" 35)
  AOT_disj :: "[\<phi>, \<phi>] \<Rightarrow> \<phi>" (infixl "\<or>" 30)
  AOT_iff :: "[\<phi>, \<phi>] \<Rightarrow> \<phi>" (infixl "\<equiv>" 25)

  "_AOT_all" :: "[id_position, \<phi>] \<Rightarrow> \<phi>" ("\<forall>_ _" [10, 39] 50)
  "_AOT_ex" :: "[id_position, \<phi>] \<Rightarrow> \<phi>" ("\<exists>_ _" [10, 39] 50)
  AOT_denotes :: "\<tau> \<Rightarrow> \<phi>" ("_\<down>" [70] 60)
  AOT_id :: "[\<tau>, \<tau>] \<Rightarrow> \<phi>" (infixl "=" 63)

  "_AOT_lambda" :: "id_position \<Rightarrow> \<phi> \<Rightarrow> \<Pi>" ("[\<lambda>_ _]")
  "AOT_lambda0" :: "\<phi> \<Rightarrow> \<Pi>0" ("[\<lambda>'(')  _]")
  "" :: "\<Pi>0 \<Rightarrow> \<phi>" ("_" 900)
  "_AOT_lambda" :: "id_position \<Rightarrow> \<phi> \<Rightarrow> \<Pi>" ("[%_ _]")

  "_AOT_id" :: "id_position \<Rightarrow> AOT_id" ("_" 999)
  "" :: "AOT_id \<Rightarrow> AOT_ids" ("_" 999)
  "_AOT_ids" :: "AOT_id \<Rightarrow> AOT_ids \<Rightarrow> AOT_ids" ("__")
  "" :: "AOT_desc \<Rightarrow> AOT_id" ("_")
  "_AOT_desc" :: "id_position \<Rightarrow> \<phi> \<Rightarrow> AOT_desc" ("__")

  "_AOT_formula_free" :: "id_position => AOT_ids \<Rightarrow> \<phi>" ("_'{free:_'}" 900)
  "_AOT_atomic_formula" :: "AOT_ids => \<phi>" ("_" 900)

  "AOT_concrete" :: "\<Pi>" ("\<^bold>E!")
  "AOT_ordinary" :: "\<Pi>" ("\<^bold>O!")
  "AOT_abstract" :: "\<Pi>" ("\<^bold>A!")
  "dummyRel" :: "\<Pi>" ("\<^bold>D!")

syntax (input)
  "AOT_exe" :: "\<Pi> \<Rightarrow> AOT_ids \<Rightarrow> \<phi>" ("__" [900,901] 800)
  "AOT_enc" :: "AOT_ids \<Rightarrow> \<Pi> \<Rightarrow> \<phi>" ("__" [900,901] 800)

parse_ast_translation\<open>
let

fun isRelation name = (let val fst = (hd (Symbol.explode name)) in Symbol.is_ascii_upper fst orelse fst = "\<Pi>" end)

fun range_pos (fst, lst) = Position.range_position (Symbol_Pos.range [fst, lst])
fun decode_pos str = (case (Term_Position.decode str) of SOME pos => pos | _ => raise Fail "expected position")

fun AOT_merge_identifiers ((fst as (x,_))::("\<^sub>",_)::(lst as (n,_))::tl) = AOT_merge_identifiers ((x^"\<^sub>"^n, range_pos (fst, lst))::tl)
 | AOT_merge_identifiers ((fst as (x,_))::(lst as ("'",_))::tl) = AOT_merge_identifiers ((x^"'",range_pos (fst, lst))::tl)
 | AOT_merge_identifiers (x::tl) = x::AOT_merge_identifiers tl
 | AOT_merge_identifiers nil = nil

fun constrainWithConst (ast,typ) = Ast.Appl [Ast.Constant "_constrain", ast, Ast.Constant typ]

fun constrainTyp name = let
  val x = hd (Symbol.explode name)
in
  if x = "x" then
    (fn ast => constrainWithConst (ast, @{type_syntax \<kappa>}))
(*    (fn ast => constrainWithConst (Ast.Appl [Ast.Constant @{const_syntax Rep_var}, ast], @{type_syntax \<kappa>})) *)
  else
    I
end

fun constrainPos (name,pos) = (Ast.Appl [Ast.Constant "_constrain", Ast.Variable name, Ast.Variable (Term_Position.encode pos)])
fun constrainPosConst (name,pos) = Ast.Appl [Ast.Constant "_constrain", Ast.Constant name, Ast.Variable (Term_Position.encode pos)]

fun constrain (name,pos) = constrainTyp name (constrainPos (name,pos))

fun unconstrain (Ast.Variable name) = name
  | unconstrain (Ast.Appl [Ast.Constant _, ast]) = unconstrain ast
  | unconstrain (Ast.Appl [Ast.Constant "_constrain", ast, Ast.Variable pos]) = (unconstrain ast)
  | unconstrain (Ast.Appl [Ast.Constant "_constrain", ast, Ast.Constant typ]) = (unconstrain ast)

fun split_identifiers (ast as Ast.Appl [Ast.Constant "_constrain", Ast.Variable name, Ast.Variable pos]) =
  Symbol_Pos.explode (name, decode_pos pos) |> AOT_merge_identifiers |> (fn (syms as (hd::nil)) => Ast.mk_appl (Ast.Constant "_AOT_arg") [constrain hd]
  | (syms) => syms |>
  (Ast.mk_appl (Ast.Constant "_AOT_args")) o (map constrain))

fun parse_lambda (ast as Ast.Appl [Ast.Constant "_constrain", Ast.Variable name, Ast.Variable pos]) matrix = (
  let
    fun makeAbs (hd :: nil) =  Ast.Appl [ Ast.Constant "_abs", constrainPos hd, matrix]
      | makeAbs (hd :: tail) = Ast.Appl [Ast.Constant @{const_syntax case_prod}, Ast.Appl [ Ast.Constant "_abs", constrainPos hd, makeAbs tail]]
  in
    Ast.Appl [Ast.Constant @{const_syntax AOT_lambda}, Symbol_Pos.explode (name, decode_pos pos) |> AOT_merge_identifiers |> makeAbs]
  end
)

fun parse_atomic (ast as Ast.Appl ((Ast.Constant "_AOT_args")::args)) = (
  if isRelation (unconstrain (hd args))
  then Ast.mk_appl (Ast.Constant "_exe") args
  else Ast.mk_appl (Ast.Constant "_enc") args
) | parse_atomic (ast as Ast.Appl [(Ast.Constant "_AOT_arg"),arg]) = (arg)
  | parse_atomic ast = (@{print} "Weird atomic"; ast)

fun parse_quantifier const (bound) matrix = (Ast.Appl [const, Ast.Appl [ Ast.Constant "_abs", bound, matrix]])

fun 
  merge_identifiers (Ast.Appl (hd::tail)) (Ast.Appl (hd'::tail')) = Ast.mk_appl (Ast.Constant "_AOT_args") (tail@tail')

fun parse_desc (ast as Ast.Appl [Ast.Constant "_constrain", Ast.Variable name, Ast.Variable pos]) matrix =
  Symbol_Pos.explode (name, decode_pos pos) |> AOT_merge_identifiers |> List.rev |> (fn (syms as (hd::("\<iota>",pos)::tail)) =>
  Ast.mk_appl (Ast.Constant "_AOT_args") (rev ((Ast.mk_appl (constrainPosConst ("AOT_that",pos)) [Ast.mk_appl (Ast.Constant "_abs") [(constrainPos hd),matrix]])::((map constrainPos) tail))))
in
[
  ("_AOT_atomic_formula", (fn ctxt => fn [ast] => (@{print} ("atomic",ast); parse_atomic ast))),
  ("_AOT_formula_free", (fn ctxt => fn [metavar, (Ast.Appl ((Ast.Constant c)::args))] => (Ast.mk_appl metavar args))),
  ("_AOT_id", (fn ctxt => fn [ast] => split_identifiers ast)),
  ("_AOT_ids", (fn ctxt => fn [ast,ast'] => merge_identifiers ast ast')),
  ("_AOT_lambda", (fn ctxt => fn [bound, matrix] => parse_lambda bound matrix)),
  ("_AOT_all", (fn ctxt => fn [bound, matrix] => parse_quantifier (Ast.Constant @{const_syntax AOT_all}) bound matrix)),
  ("_AOT_ex", (fn ctxt => fn [bound, matrix] => parse_quantifier (Ast.Constant @{const_syntax AOT_ex}) bound matrix)),
  ("_AOT_desc", (fn ctxt => fn [ast, matrix] => parse_desc ast matrix))
]
end
\<close>

parse_translation\<open>
let

fun isRelation (Const ("_constrain", typ) $ Free (name, typ') $ Free (markup, typ'')) = let
  val fst = hd (Symbol.explode name)
in
  Symbol.is_ascii_upper fst orelse fst = "\<Pi>"
end
val dummyT = Type ("dummy",[])
fun makePairs (hd::nil) = hd | makePairs (hd::tail) = Const (@{const_name Pair}, dummyT) $ hd $ makePairs tail
fun parse_exe hd tail = (Const (@{const_name AOT_exe}, dummyT) $ hd $ makePairs tail)
fun parse_enc tail hd = (Const (@{const_name AOT_enc}, dummyT) $ makePairs tail $ hd)
in
[
  ("_exe", (fn ctxt => fn hd::tail => parse_exe hd tail)),
  ("_enc", (fn ctxt => List.rev #> (fn hd::tail => parse_enc (List.rev tail) hd))),
  ("_AOT_args", (fn ctxt => fn terms => makePairs terms)),
  ("_AOT_arg", (fn ctxt => fn [trm] => trm)),
  ("_prop", (fn ctxt => fn [terms] => terms))
]
end
\<close>

notepad
begin
  fix p
  have "\<And> v \<phi>. [v \<Turnstile> \<box>\<phi> \<rightarrow> p] = [v \<^bold>\<Turnstile> \<^bold>\<box>\<phi> \<^bold>\<rightarrow> p]" by simp
end

declare[[show_sorts]]
context
begin
private lemma "[v \<Turnstile> \<forall> x xyF] \<or> True" by simp
private lemma "[v \<Turnstile> \<^bold>D! \<iota>a(p)b] \<or> True" by simp
private lemma "[v \<Turnstile> U\<iota>x(p)] \<or> True" by simp
private lemma "[v \<Turnstile> U'a\<iota>x(p)] \<or> True" by simp
private lemma "[v \<Turnstile> U''\<iota>x(p)b] \<or> True" by simp
private lemma "[v \<Turnstile> U'''a\<iota>x(p)b] \<or> True" by simp
private lemma "[v \<Turnstile> \<^bold>E!\<iota>x(p)] \<or> True" by simp
private lemma "[v \<Turnstile> \<^bold>D!a\<iota>x(p)] \<or> True" by simp
private lemma "[v \<Turnstile> \<box>\<phi> \<rightarrow> p] = [v \<^bold>\<Turnstile> \<^bold>\<box>\<phi> \<^bold>\<rightarrow> p]" by simp
private lemma "\<forall> x . [v \<Turnstile> \<box>p \<rightarrow> p \<equiv> z = x] = [v \<^bold>\<Turnstile> \<^bold>\<box>p \<^bold>\<rightarrow> (p \<^bold>\<equiv> z \<^bold>= x)]" by simp
private lemma "[v \<Turnstile> \<Pi>\<down> \<rightarrow> \<Pi> = [\<lambda>xyz Fx'xyz]] = [v \<^bold>\<Turnstile> \<Pi>\<^bold>\<down> \<^bold>\<rightarrow> \<Pi> \<^bold>= [\<^bold>\<lambda>(x, y, z). \<lparr>F, (x', x, y, z)\<rparr>]]" by simp
private lemma "[v \<Turnstile> \<Pi>a] = [v \<^bold>\<Turnstile> \<lparr>\<Pi>, a\<rparr>]" by simp
private lemma "[v \<Turnstile>  [\<lambda>x Fx]y & y[\<lambda>x Fx] ] = [v \<^bold>\<Turnstile> \<lparr>[\<^bold>\<lambda>x. \<lparr>F, x\<rparr>], y\<rparr> \<^bold>& \<lbrace>y, [\<^bold>\<lambda>x. \<lparr>F, x\<rparr>]\<rbrace>]" by simp
private lemma "[v \<Turnstile> ([\<lambda>xyz Fx] a\<iota>q(Gq)q ) ] = [v \<^bold>\<Turnstile> \<lparr>[\<^bold>\<lambda>(x,y,z). \<lparr>F, x\<rparr>], (a, \<^bold>\<iota>q. \<lparr>G, q\<rparr>, q)\<rparr>]" by simp
private lemma "[v \<Turnstile> ([\<lambda>xy Fx] a\<iota>q(Gq) ) ] = [v \<^bold>\<Turnstile> \<lparr>[\<^bold>\<lambda>(x,y). \<lparr>F, x\<rparr>], (a, \<^bold>\<iota>q. \<lparr>G, q\<rparr>)\<rparr>]" by simp
private lemma "[v \<Turnstile> ([\<lambda>xyz Fx] a\<iota>q(Gq) q ) ] = [v \<^bold>\<Turnstile> \<lparr>[\<^bold>\<lambda>(x,y,z). \<lparr>F, x\<rparr>], (a, \<^bold>\<iota>q. \<lparr>G, q\<rparr>, q)\<rparr>]" by simp
private lemma "[v \<Turnstile> ([\<lambda>xyz Fx] a\<iota>q(Gq)q ) ] = [v \<^bold>\<Turnstile> \<lparr>[\<^bold>\<lambda>(x,y,z). \<lparr>F, x\<rparr>], (a, \<^bold>\<iota>q. \<lparr>G, q\<rparr>, q)\<rparr>] " by simp
private lemma "[v \<Turnstile> (\<^bold>D! a\<iota>q(Gq)q ) ] = [v \<^bold>\<Turnstile> \<lparr>dummyRel, (a, \<^bold>\<iota>q. \<lparr>G, q\<rparr>, q)\<rparr>]" by simp
private lemma "[v \<Turnstile> (\<^bold>D! a\<iota>q(Gq)\<iota>q(Gq)q ) ] = [v \<^bold>\<Turnstile> \<lparr>dummyRel, (a, \<^bold>\<iota>q. \<lparr>G, q\<rparr>, \<^bold>\<iota>q. \<lparr>G, q\<rparr>, q)\<rparr>]" by simp
private lemma "[v \<Turnstile> (\<^bold>D! \<iota>q(Gq)a\<iota>q(Gq) ) ] = [v \<^bold>\<Turnstile> \<lparr>dummyRel, (\<^bold>\<iota>q. \<lparr>G, q\<rparr>, a, \<^bold>\<iota>q. \<lparr>G, q\<rparr>)\<rparr>]" by simp
private lemma "[v \<Turnstile> ([\<lambda>xyz Fx] a\<iota>q(Gq) q ) ] = [v \<^bold>\<Turnstile> \<lparr>[\<^bold>\<lambda>(x,y,z). \<lparr>F, x\<rparr>], (a, \<^bold>\<iota>q. \<lparr>G, q\<rparr>, q)\<rparr>]" by simp
private lemma "[v \<Turnstile> \<forall>x ~Fxy & xyG] = [v \<^bold>\<Turnstile> (\<^bold>\<forall>x. \<^bold>\<not>\<lparr>F, (x, y)\<rparr>) \<^bold>& \<lbrace>(x, y), G\<rbrace>]" by simp
private lemma "[v \<Turnstile> \<forall>x\<exists>y ~Fxy & xyxG] = [v \<^bold>\<Turnstile> (\<^bold>\<forall>x. \<^bold>\<exists>y. \<^bold>\<not>\<lparr>F, (x, y)\<rparr>) \<^bold>& \<lbrace>(x, y, x), G\<rbrace>]"  by simp
private lemma "[v \<Turnstile> \<forall>x (~Fxy & xyG)] = [v \<^bold>\<Turnstile> \<^bold>\<forall>x. \<^bold>\<not>\<lparr>F, (x, y)\<rparr> \<^bold>& \<lbrace>(x, y), G\<rbrace>]" by simp
private lemma "[v \<Turnstile> \<forall>G (~Fxy & xyG)] = [v \<^bold>\<Turnstile> \<^bold>\<forall>G. \<^bold>\<not>\<lparr>F, (x, y)\<rparr> \<^bold>& \<lbrace>(x, y), G\<rbrace>]" by simp
private lemma "[v \<Turnstile> [\<lambda>xy Hyx]zz] = [v \<^bold>\<Turnstile> \<lparr>[\<^bold>\<lambda>(x, y). \<lparr>H, (y, x)\<rparr>], (z, z)\<rparr>]" by simp
private lemma "[v \<Turnstile> \<^bold>A!x & \<^bold>O!y & x\<^bold>E!] = [v \<^bold>\<Turnstile> \<lparr>A!, x\<rparr> \<^bold>& \<lparr>O!, y\<rparr> \<^bold>& \<lbrace>x, E!\<rbrace>] " by simp
private lemma "[v \<Turnstile> Fxy\<iota>z(p)] = [v \<^bold>\<Turnstile> \<lparr>F, (x, y, \<^bold>\<iota>z. p)\<rparr>]" by simp
private lemma "[v \<Turnstile> F\<iota>z(p)y\<iota>z(p)] = [v \<^bold>\<Turnstile> \<lparr>F, (\<^bold>\<iota>z. p, y, \<^bold>\<iota>z. p)\<rparr>]" by simp

private lemma "[v \<Turnstile> Fxy\<iota>z(\<phi>{free:z})] = [v \<^bold>\<Turnstile> \<lparr>F, (x, y, \<^bold>\<iota>z. \<phi> z)\<rparr>]" by simp
private lemma "[v \<Turnstile> Fxy\<iota>z(\<phi>{free:zy})] = [v \<^bold>\<Turnstile> \<lparr>F, (x, y, \<^bold>\<iota>z. \<phi> z y)\<rparr>]" by simp
end

term "[v \<Turnstile> [\<lambda>() p] ]"


end
