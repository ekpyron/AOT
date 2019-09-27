theory AOT_Syntax_next
  imports AOT_Axioms
begin

declare[[eta_contract = false]]
no_notation AOT_valid_in ("[_ \<Turnstile> _]")
notation AOT_valid_in ("[_ \<^bold>\<Turnstile> _]")

nonterminal \<phi>
nonterminal \<nu>
nonterminal identifiers
nonterminal \<Pi>
nonterminal \<tau>
nonterminal formula

syntax "" :: "\<Pi> \<Rightarrow> \<tau>" ("_")
syntax "" :: "id_position \<Rightarrow> \<tau>" ("_")

syntax
  AOT_valid_in :: "[i, \<phi>] \<Rightarrow> bool" ("[_ \<Turnstile> _]")

  "" :: "\<phi> \<Rightarrow> \<phi>" ("'(_')")
  AOT_not :: "\<phi> \<Rightarrow> \<phi>" ("\<not>_" [40] 40)
  AOT_not :: "\<phi> \<Rightarrow> \<phi>" ("~_" [40] 40)
  AOT_imp :: "[\<phi>, \<phi>] \<Rightarrow> \<phi>" (infixl "\<rightarrow>" 8)
  AOT_box :: "\<phi> \<Rightarrow> \<phi>" ("\<box>_" [62] 63)
  AOT_act :: "\<phi> \<Rightarrow> \<phi>" ("\<A>_" [64] 65)
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
  "_AOT_lambda" :: "id_position \<Rightarrow> \<phi> \<Rightarrow> \<Pi>" ("[%_ _]")

  "" :: "id_position => formula" ("_")
  "_AOT_concat_formulas" :: "formula => formula \<Rightarrow> formula" ("__")
  "_AOT_atomic_formula" :: "formula => \<phi>" ("_")

  "AOT_concrete" :: "\<Pi>" ("\<^bold>E!")
  "AOT_ordinary" :: "\<Pi>" ("\<^bold>O!")
  "AOT_abstract" :: "\<Pi>" ("\<^bold>A!")

  "_AOT_identifiers" :: "id_position \<Rightarrow> identifiers" ("_")
  "_AOT_concat_identifiers" :: "identifiers \<Rightarrow> identifiers \<Rightarrow> identifiers" ("__" [2,3] 2)
  "_AOT_desc" :: "identifiers \<Rightarrow> \<phi> \<Rightarrow> identifiers" ("_'(_')" [3,1] 4)
syntax (input)
  "AOT_exe" :: "\<Pi> \<Rightarrow> identifiers \<Rightarrow> \<phi>" ("__")
  "AOT_enc" :: "identifiers \<Rightarrow> \<Pi> \<Rightarrow> \<phi>" ("__")

parse_ast_translation\<open>
let

fun isRelation name = (let val fst = (hd (Symbol.explode name)) in Symbol.is_ascii_upper fst orelse fst = "\<Pi>" end)

fun range_pos (fst, lst) = Position.range_position (Symbol_Pos.range [fst, lst])
fun decode_pos str = (case (Term_Position.decode str) of SOME pos => pos | _ => raise Fail "expected position")

fun AOT_merge_identifiers ((fst as (x,_))::("\<^sub>",_)::(lst as (n,_))::tl) = AOT_merge_identifiers ((x^"\<^sub>"^n, range_pos (fst, lst))::tl)
 | AOT_merge_identifiers ((fst as (x,_))::(lst as ("'",_))::tl) = AOT_merge_identifiers ((x^"'",range_pos (fst, lst))::tl)
 | AOT_merge_identifiers (x::tl) = x::AOT_merge_identifiers tl
 | AOT_merge_identifiers nil = nil

fun constrain (name,pos) = Ast.Appl [Ast.Constant "_constrain", Ast.Variable name, Ast.Variable (Term_Position.encode pos)]
fun constrainConst (name,pos) = Ast.Appl [Ast.Constant "_constrain", Ast.Constant name, Ast.Variable (Term_Position.encode pos)]

fun unconstrain (Ast.Appl [Ast.Constant "_constrain", Ast.Variable name, Ast.Variable pos]) = (name, decode_pos pos)

fun split_atomic_formula (ast as Ast.Appl [Ast.Constant "_constrain", Ast.Variable name, Ast.Variable pos]) =
  Symbol_Pos.explode (name, decode_pos pos) |> AOT_merge_identifiers |>
  (fn (hd::nil) => Ast.mk_appl (Ast.Constant "_prop") [ast] | (syms as ((name,pos)::tail)) => Ast.Appl (
    (Ast.Constant (if isRelation name then "_exe" else "_enc"))::(map constrain syms)
  ))

fun split_identifiers (ast as Ast.Appl [Ast.Constant "_constrain", Ast.Variable name, Ast.Variable pos]) =
  Symbol_Pos.explode (name, decode_pos pos) |> AOT_merge_identifiers |>
  (Ast.mk_appl (Ast.Constant "_args")) o (map constrain)

fun parse_lambda (ast as Ast.Appl [Ast.Constant "_constrain", Ast.Variable name, Ast.Variable pos]) matrix = (
  let
    fun makeAbs (hd :: nil) =  Ast.Appl [ Ast.Constant "_abs", constrain hd, matrix]
      | makeAbs (hd :: tail) = Ast.Appl [Ast.Constant @{const_syntax case_prod}, Ast.Appl [ Ast.Constant "_abs", constrain hd, makeAbs tail]]
  in
    Ast.Appl [Ast.Constant @{const_syntax AOT_lambda}, Symbol_Pos.explode (name, decode_pos pos) |> AOT_merge_identifiers |> makeAbs]
  end
)

fun parse_quantifier const (bound) matrix = (Ast.Appl [const, Ast.Appl [ Ast.Constant "_abs", bound, matrix]])

fun 
  merge_identifiers (Ast.Appl (_::tail)) (Ast.Appl (_::tail')) = Ast.mk_appl (Ast.Constant "_args") (tail@tail')
in
[
  ("_AOT_atomic_formula", (fn ctxt => fn [ast] => split_atomic_formula ast)),
  ("_AOT_identifiers", (fn ctxt => fn [ast] => split_identifiers ast)),
  ("_AOT_concat_identifiers", (fn ctxt => fn [ast,ast'] => merge_identifiers ast ast')),
  ("_AOT_lambda", (fn ctxt => fn [bound, matrix] => parse_lambda bound matrix)),
  ("_AOT_all", (fn ctxt => fn [bound, matrix] => parse_quantifier (Ast.Constant @{const_syntax AOT_all}) bound matrix)),
  ("_AOT_ex", (fn ctxt => fn [bound, matrix] => parse_quantifier (Ast.Constant @{const_syntax AOT_ex}) bound matrix)),
  ("_AOT_desc", (fn ctxt => fn [Ast.Appl args, matrix] => (fn (hd::iota::tail) =>
      let
        val (iota, iotapos) = unconstrain iota
      in
        if iota = "\<iota>" then
          Ast.Appl (rev ((Ast.mk_appl (constrainConst (@{const_syntax AOT_that}, iotapos)) [Ast.mk_appl (Ast.Constant "_abs") [hd, matrix]])::tail))
        else
          raise Fail "Parser error"
      end ) (List.rev args)))
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
  ("_args", (fn ctxt => fn terms => makePairs terms)),
  ("_prop", (fn ctxt => fn [terms] => terms))
]
end
\<close>

notepad
begin
  fix p
  have "\<And> v \<phi>. [v \<Turnstile> \<box>\<phi> \<rightarrow> p] = [v \<^bold>\<Turnstile> \<^bold>\<box>\<phi> \<^bold>\<rightarrow> p]" by simp
end

context
begin
private lemma "[v \<Turnstile> \<box>\<phi> \<rightarrow> p] = [v \<^bold>\<Turnstile> \<^bold>\<box>\<phi> \<^bold>\<rightarrow> p]" by simp
private lemma "\<forall> x . [v \<Turnstile> \<box>p \<rightarrow> p \<equiv> z = x] = [v \<^bold>\<Turnstile> \<^bold>\<box>p \<^bold>\<rightarrow> (p \<^bold>\<equiv> z \<^bold>= x)]" by simp
private lemma "[v \<Turnstile> \<Pi>\<down> \<rightarrow> \<Pi> = [\<lambda>xyz Fx'xyz]] = [v \<^bold>\<Turnstile> \<Pi>\<^bold>\<down> \<^bold>\<rightarrow> \<Pi> \<^bold>= [\<^bold>\<lambda>(x, y, z). \<lparr>F, (x', x, y, z)\<rparr>]]" by simp
private lemma "[v \<Turnstile> \<Pi>a] = [v \<^bold>\<Turnstile> \<lparr>\<Pi>, a\<rparr>]" by simp
private lemma "[v \<Turnstile>  [\<lambda>x Fx]y & y[\<lambda>x Fx] ] = [v \<^bold>\<Turnstile> \<lparr>[\<^bold>\<lambda>x. \<lparr>F, x\<rparr>], y\<rparr> \<^bold>& \<lbrace>y, [\<^bold>\<lambda>x. \<lparr>F, x\<rparr>]\<rbrace>]" by simp
private lemma "[v \<Turnstile> ([\<lambda>x Fx] a\<iota>q(Gq)q ) ] = [v \<^bold>\<Turnstile> \<lparr>[\<^bold>\<lambda>x. \<lparr>F, x\<rparr>], (a, \<^bold>\<iota>q. \<lparr>G, q\<rparr>, q)\<rparr>]" by simp
private lemma "[v \<Turnstile> ([\<lambda>x Fx] a\<iota>q(Gq) q ) ] = [v \<Turnstile> ([\<lambda>x Fx] a\<iota>q(Gq) q ) ]" by simp
private lemma "[v \<Turnstile> ([\<lambda>x Fx] a \<iota>q(Gq)q ) ] = [v \<Turnstile> ([\<lambda>x Fx] a \<iota>q(Gq)q ) ]" by simp
private lemma "[v \<Turnstile> ([\<lambda>x Fx] a \<iota>q(Gq) q ) ] = [v \<^bold>\<Turnstile> \<lparr>[\<^bold>\<lambda>x. \<lparr>F, x\<rparr>], (a, \<^bold>\<iota>q. \<lparr>G, q\<rparr>, q)\<rparr>]" by simp
private lemma "[v \<Turnstile> \<forall>x ~Fxy & xyG] = [v \<^bold>\<Turnstile> (\<^bold>\<forall>x. \<^bold>\<not>\<lparr>F, (x, y)\<rparr>) \<^bold>& \<lbrace>(x, y), G\<rbrace>]" by simp
private lemma "[v \<Turnstile> \<forall>x\<exists>y ~Fxy & xyxG] = [v \<^bold>\<Turnstile> (\<^bold>\<forall>x. \<^bold>\<exists>y. \<^bold>\<not>\<lparr>F, (x, y)\<rparr>) \<^bold>& \<lbrace>(x, y, x), G\<rbrace>]"  by simp
private lemma "[v \<Turnstile> \<forall>x (~Fxy & xyG)] = [v \<^bold>\<Turnstile> \<^bold>\<forall>x. \<^bold>\<not>\<lparr>F, (x, y)\<rparr> \<^bold>& \<lbrace>(x, y), G\<rbrace>]" by simp
private lemma "[v \<Turnstile> \<forall>G (~Fxy & xyG)] = [v \<^bold>\<Turnstile> \<^bold>\<forall>G. \<^bold>\<not>\<lparr>F, (x, y)\<rparr> \<^bold>& \<lbrace>(x, y), G\<rbrace>]" by simp
private lemma "[v \<Turnstile> [\<lambda>xy Hyx]zz] = [v \<^bold>\<Turnstile> \<lparr>[\<^bold>\<lambda>(x, y). \<lparr>H, (y, x)\<rparr>], (z, z)\<rparr>]" by simp
private lemma "[v \<Turnstile> \<^bold>A!x & \<^bold>O!y & x\<^bold>E!] = [v \<Turnstile> \<^bold>A!x & \<^bold>O!y & x\<^bold>E!]" by simp
private lemma "[v \<Turnstile> Fxy\<iota>z(p)]" oops
end

end
