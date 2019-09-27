theory AOT_Syntax
  imports AOT_Axioms
begin

no_notation (input) AOT_valid_in ("[_ \<Turnstile> _]")

nonterminal \<phi>
nonterminal \<nu>
nonterminal \<kappa>s
nonterminal \<Pi>
nonterminal \<tau>

syntax "" :: "\<Pi> \<Rightarrow> \<tau>" ("_")
syntax "" :: "id_position \<Rightarrow> \<tau>" ("_")

syntax AOT_valid_in :: "[i, \<phi>] \<Rightarrow> bool" ("[_ \<Turnstile> _]")
syntax AOT_not :: "\<phi> \<Rightarrow> \<phi>" ("\<not>_" [40] 40)
syntax AOT_not :: "\<phi> \<Rightarrow> \<phi>" ("~_" [40] 40)
syntax AOT_imp :: "[\<phi>, \<phi>] \<Rightarrow> \<phi>" (infixl "\<rightarrow>" 8)
syntax AOT_box :: "\<phi> \<Rightarrow> \<phi>" ("\<box>_" [62] 63)
syntax AOT_act :: "\<phi> \<Rightarrow> \<phi>" ("\<A>_" [64] 65)
syntax AOT_dia :: "\<phi> \<Rightarrow> \<phi>" ("\<diamond>_" [62] 63)
syntax AOT_conj :: "[\<phi>, \<phi>] \<Rightarrow> \<phi>" (infixl "&" 35)
syntax AOT_conj :: "[\<phi>, \<phi>] \<Rightarrow> \<phi>" (infixl "\<and>" 35)
syntax AOT_disj :: "[\<phi>, \<phi>] \<Rightarrow> \<phi>" (infixl "\<or>" 30)
syntax AOT_iff :: "[\<phi>, \<phi>] \<Rightarrow> \<phi>" (infixl "\<equiv>" 25)

syntax "_AOT_all" :: "[id_position, \<phi>] \<Rightarrow> \<phi>" ("\<forall>_ _" [10, 39] 50)
syntax "_AOT_ex" :: "[id_position, \<phi>] \<Rightarrow> \<phi>" ("\<exists>_ _" [10, 39] 50)
syntax AOT_denotes :: "\<tau> \<Rightarrow> \<phi>" ("_\<down>" [70] 60)
syntax AOT_id :: "[\<tau>, \<tau>] \<Rightarrow> \<phi>" (infixl "=" 63)

syntax "_AOT_atomic_formula" :: "id_position \<Rightarrow> \<phi>" ("_")
syntax "_\<kappa>s" :: "id_position \<Rightarrow> \<kappa>s" ("_")

syntax "_AOT_lambda" :: "id_position \<Rightarrow> \<phi> \<Rightarrow> \<Pi>" ("[\<lambda>_ _]")
syntax "_AOT_lambda" :: "id_position \<Rightarrow> \<phi> \<Rightarrow> \<Pi>" ("[%_ _]")

syntax "" :: "\<phi> \<Rightarrow> \<phi>" ("'(_')")

syntax (input) "AOT_exe" :: "\<Pi> \<Rightarrow> \<kappa>s \<Rightarrow> \<phi>" ("__")
syntax (input) "AOT_enc" :: "\<kappa>s \<Rightarrow> \<Pi> \<Rightarrow> \<phi>" ("__")

syntax "AOT_concrete" :: "\<Pi>" ("\<^bold>E!")
syntax "AOT_ordinary" :: "\<Pi>" ("\<^bold>O!")
syntax "AOT_abstract" :: "\<Pi>" ("\<^bold>A!")

parse_ast_translation\<open>
let

val range_pos = Position.range_position o Position.range
fun range_pos (fst, lst) = Position.range_position (Symbol_Pos.range [fst, lst])
fun decode_pos str = (case (Term_Position.decode str) of SOME pos => pos | _ => raise Fail "expected position")

fun AOT_merge_identifiers ((fst as (x,_))::("\<^sub>",_)::(lst as (n,_))::tl) = AOT_merge_identifiers ((x^"\<^sub>"^n, range_pos (fst, lst))::tl)
 | AOT_merge_identifiers ((fst as (x,_))::(lst as ("'",_))::tl) = AOT_merge_identifiers ((x^"'",range_pos (fst, lst))::tl)
 | AOT_merge_identifiers (x::tl) = x::AOT_merge_identifiers tl
 | AOT_merge_identifiers nil = nil

fun constrain (name,pos) = Ast.Appl [Ast.Constant "_constrain", Ast.Variable name, Ast.Variable (Term_Position.encode pos)]

fun parse_kappas (ast as Ast.Appl [Ast.Constant "_constrain", Ast.Variable name, Ast.Variable pos]) =
  Symbol_Pos.explode (name, decode_pos pos) |> AOT_merge_identifiers |>
  (let fun AOT_makeArgs (hd :: nil) = constrain hd
         | AOT_makeArgs (hd :: tail) = Ast.Appl [(Ast.Constant "Pair"), constrain hd, AOT_makeArgs tail]
   in AOT_makeArgs end)

fun isRelation name = (let val fst = (hd (Symbol.explode name)) in
  Symbol.is_ascii_upper fst orelse fst = "\<Pi>" end)

fun parse_atomic_formula (ast as Ast.Appl [Ast.Constant "_constrain", Ast.Variable name, Ast.Variable pos]) = 
  Symbol_Pos.explode (name, decode_pos pos) |> AOT_merge_identifiers |>
  (
    fn (hd::nil) => (@{print} ("TODO: validate as prop:", hd); ast)
    | (syms as ((name,pos)::tail)) => 
      if isRelation name then
        Ast.Appl [ Ast.Constant @{const_syntax AOT_exe},
            constrain (name,pos),
            parse_kappas (
              constrain (Symbol_Pos.content tail, (Position.range_position o Symbol_Pos.range) tail)
            )
          ]
      else let val ((name,pos)::tail) = List.rev syms in
        if isRelation name then
        Ast.Appl [ Ast.Constant @{const_syntax AOT_enc},
            parse_kappas (
              constrain (Symbol_Pos.content (rev tail), (Position.range_position o Symbol_Pos.range) (rev tail))
            ),
            constrain (name,pos)
          ]        else
          raise Ast.AST ("Expected atomic formula, but got", [ast])
      end
  )


fun parse_lambda (ast as Ast.Appl [Ast.Constant "_constrain", Ast.Variable name, Ast.Variable pos]) matrix = (
  let
    val bound = Symbol_Pos.explode (name, decode_pos pos) |> AOT_merge_identifiers
    val _ =  @{print} ("Parse lambda:", bound, matrix)
    fun makeAbs (hd :: nil) =  Ast.Appl [ Ast.Constant "_abs", constrain hd, matrix]
      | makeAbs (hd :: tail) = Ast.Appl [Ast.Constant @{const_syntax case_prod}, Ast.Appl [ Ast.Constant "_abs", constrain hd, makeAbs tail]]
  in
    Ast.Appl [Ast.Constant @{const_syntax AOT_lambda}, makeAbs bound]
  end
)

fun parse_quantifier const (bound as Ast.Appl [Ast.Constant "_constrain", Ast.Variable name, Ast.Variable pos]) matrix = (
  let
  in
    Ast.Appl [const, Ast.Appl [ Ast.Constant "_abs", bound, matrix]]
  end
)

in
[
  ("_AOT_atomic_formula", (fn ctxt => fn [ast] => parse_atomic_formula ast)),
  ("_AOT_lambda", (fn ctxt => fn [bound, matrix] => parse_lambda bound matrix)),
  ("_AOT_all", (fn ctxt => fn [bound, matrix] => parse_quantifier (Ast.Constant @{const_syntax AOT_all}) bound matrix)),
  ("_AOT_ex", (fn ctxt => fn [bound, matrix] => parse_quantifier (Ast.Constant @{const_syntax AOT_ex}) bound matrix)),
  ("_\<kappa>s", (fn ctxt => fn [ast] => parse_kappas ast))
]
end
\<close>

lemma "\<forall> x . [v \<Turnstile> \<box>\<phi> \<rightarrow> p]" oops
lemma "\<forall> x . [v \<Turnstile> \<box>p \<rightarrow> p \<equiv> z = x]" oops
lemma "[v \<Turnstile> \<Pi>\<down> \<rightarrow> \<Pi> = [\<lambda>x \<Pi>x]]" oops
declare[[show_sorts]]
lemma "[v \<Turnstile> \<forall>x ~Fxy & xyG]" oops
lemma "[v \<Turnstile> \<forall>x\<exists>F ~Fxy & xyG]" oops
lemma "[v \<Turnstile> \<forall>x (~Fxy & xyG)]" oops
lemma "[v \<Turnstile> [\<lambda>xy Hyx]zz]" oops
lemma "[v \<Turnstile> \<^bold>A!x & \<^bold>O!y & x\<^bold>E!]" oops

end
