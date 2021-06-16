(*<*)
theory AOT_syntax
  imports AOT_commands
  keywords "AOT_register_variable_names" :: thy_decl
       and "AOT_register_metavariable_names" :: thy_decl
       and "AOT_register_premise_set_names" :: thy_decl
       and "AOT_register_type_constraints" :: thy_decl
     abbrevs "actually" = "\<^bold>\<A>"
         and "neccessarily" = "\<box>"
         and "possibly" = "\<diamond>"
         and "the" = "\<^bold>\<iota>"
         and "lambda" = "[\<lambda>]"
         and "being such that" = "[\<lambda> ]"
         and "forall" = "\<forall>"
         and "exists" = "\<exists>"
         and "equivalent" = "\<equiv>"
         and "not" = "\<not>"
         and "implies" = "\<rightarrow>"
         and "equal" = "="
         and "by definition" = "\<^sub>d\<^sub>f"
         and "df" = "\<^sub>d\<^sub>f"
         and "denotes" = "\<down>"
begin
(*>*)

section\<open>Approximation of the Syntax of PLM\<close>


locale AOT_meta_syntax
begin
notation AOT_model_valid_in ("\<^bold>[_ \<^bold>\<Turnstile> _\<^bold>]")
notation AOT_model_axiom ("\<^bold>\<box>\<^bold>[_\<^bold>]")
notation AOT_model_act_axiom ("\<^bold>\<A>\<^bold>[_\<^bold>]")
end
locale AOT_no_meta_syntax
begin
no_notation AOT_model_valid_in ("\<^bold>[_ \<^bold>\<Turnstile> _\<^bold>]")
no_notation AOT_model_axiom ("\<^bold>\<box>\<^bold>[_\<^bold>]")
no_notation AOT_model_act_axiom ("\<^bold>\<A>\<^bold>[_\<^bold>]")
end

syntax "_AOT_process_frees" :: \<open>\<phi> \<Rightarrow> \<phi>'\<close> ("_")

syntax "_AOT_verbatim" :: \<open>any \<Rightarrow> \<phi>\<close> (\<open>\<guillemotleft>_\<guillemotright>\<close>)
syntax "_AOT_quoted" :: \<open>\<phi>' \<Rightarrow> any\<close> (\<open>\<guillemotleft>_\<guillemotright>\<close>)

syntax "" :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>'(_')\<close>)

syntax "_AOT_process_frees" :: \<open>\<tau> \<Rightarrow> \<tau>'\<close> ("_")

syntax "_AOT_verbatim" :: \<open>any \<Rightarrow> \<tau>\<close> (\<open>\<guillemotleft>_\<guillemotright>\<close>)
syntax "_AOT_quoted" :: \<open>\<tau>' \<Rightarrow> any\<close> (\<open>\<guillemotleft>_\<guillemotright>\<close>)

nonterminal \<kappa>\<^sub>s
nonterminal \<Pi>
nonterminal \<alpha>
syntax "" :: \<open>\<kappa>\<^sub>s \<Rightarrow> \<tau>\<close> ("_")
syntax "" :: \<open>\<Pi> \<Rightarrow> \<tau>\<close> ("_")
syntax "" :: \<open>\<phi> \<Rightarrow> \<tau>\<close> ("'(_')")

nonterminal exe_arg
nonterminal lambda_args
syntax "_AOT_term_var" :: \<open>id_position \<Rightarrow> \<tau>\<close> ("_")
syntax "_AOT_term_var" :: \<open>id_position \<Rightarrow> \<phi>\<close> ("_")
syntax "_AOT_exe_vars" :: \<open>id_position \<Rightarrow> exe_arg\<close> ("_")
syntax "_AOT_lambda_vars" :: \<open>id_position \<Rightarrow> lambda_args\<close> ("_")
syntax "_AOT_var" :: \<open>id_position \<Rightarrow> \<alpha>\<close> ("_")
syntax "_AOT_verbatim" :: \<open>any \<Rightarrow> \<alpha>\<close> (\<open>\<guillemotleft>_\<guillemotright>\<close>)

syntax "_AOT_valid" :: \<open>w \<Rightarrow> \<phi>' \<Rightarrow> bool\<close> (\<open>[_ \<Turnstile> _]\<close>)

translations
  "[w \<Turnstile> \<phi>]" => "CONST AOT_model_valid_in w \<phi>"

AOT_syntax_print_translations
  "[w \<Turnstile> \<phi>]" <= "CONST AOT_model_valid_in w \<phi>"


ML\<open>
fun AOT_binder_trans thy bnd syntaxConst =
  (Lexicon.mark_const (Sign.full_name thy bnd), K (fn trms => Term.list_comb (Const (syntaxConst, dummyT),trms)))
\<close>

ML\<open>
datatype AOT_VariableKind = AOT_Variable of (term*term) option | AOT_MetaVariable
structure AOT_VariablePrefix = Theory_Data (
  type T = (AOT_VariableKind*string) Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.merge (K true)
);
structure AOT_PremiseSetPrefix = Theory_Data (
  type T = unit Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.merge (K true)
);
structure AOT_Constraints = Theory_Data (
  type T = (term*term) Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.merge (K true)
)
structure AOT_Restriction = Theory_Data (
  type T = (term*term) Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.merge (K true)
)

fun AOT_IsPremiseSetPrefix ctxt = Local_Theory.raw_theory_result (fn thy => (AOT_PremiseSetPrefix.get thy, thy)) ctxt |> fst |> Symtab.lookup #> Option.isSome

fun term_of_sort S =
  let
    val class = Syntax.const o Lexicon.mark_class;
    fun classes [c] = class c
      | classes (c :: cs) = Syntax.const "_classes" $ class c $ classes cs
      | classes _ = raise Fail "Unexpected.";
  in
    if S = dummyS then Syntax.const "_dummy_sort"
    else
      (case S of
        [] => Syntax.const "_topsort"
      | [c] => class c
      | cs => Syntax.const "_sort" $ classes cs)
  end
fun term_of (Type (a, Ts)) = 
      Term.list_comb (Syntax.const (Lexicon.mark_type a), map term_of Ts)
  | term_of (TFree ("'_dummy_",sort)) = (Const ("_dummy_ofsort", dummyT) $ term_of_sort sort)
  | term_of (t as TFree _) = (@{print} t; raise Term.TYPE ("", [t], []))
  | term_of (TVar _) = raise Fail "";

fun fetchTermCategory ctxt = Local_Theory.raw_theory_result (fn thy =>
  (Symtab.lookup (AOT_VariablePrefix.get thy), thy)) ctxt |> fst
fun maybeGetConstraint ctxt unary name = Local_Theory.raw_theory_result (fn thy => 
   ((if unary then Option.map fst else Option.map snd) (Symtab.lookup (AOT_Constraints.get thy) name), thy)) ctxt |> fst
fun getConstraint ctxt unary name =
  (case maybeGetConstraint ctxt unary name of SOME c => c |
   _ => raise Fail ("Unknown type category: " ^ name))

fun fetchTermConstraint ctxt name unary =
  Local_Theory.raw_theory_result (fn thy =>
    (Option.map (fn (meta, category) => (meta, getConstraint ctxt unary category))
    ((Symtab.lookup o AOT_VariablePrefix.get) thy (hd (Symbol.explode name))), thy)
) ctxt |> fst

fun register_constraint (name:string, (unaryConstraint:string,naryConstraint:string option)) thy = (
let
val unaryConstraint = (term_of (Syntax.parse_typ (Proof_Context.init_global thy) unaryConstraint))
val naryConstraint = (case naryConstraint of
  (SOME constraint) => (term_of (Syntax.parse_typ (Proof_Context.init_global thy) constraint))
  | _ => unaryConstraint
)
in 
AOT_Constraints.map (Symtab.update (name, (unaryConstraint, naryConstraint))) thy
end
)

fun register_variable_name meta (category, prefices) thy =
let
val restr = (Symtab.lookup (AOT_Restriction.get thy) category)
in
   fold (fn prefix => AOT_VariablePrefix.map (Symtab.update (prefix, (if meta then AOT_MetaVariable else AOT_Variable restr, category)))) prefices thy
end
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_register_variable_names\<close> "Register variable names for type categories."
    (Parse.and_list1 ((Parse.short_ident --| Parse.$$$ ":" ) -- Scan.repeat1 Parse.short_ident)  >> (Toplevel.theory o (fold (register_variable_name false))));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_register_metavariable_names\<close> "Register meta-variable names for type categories."
    (Parse.and_list1 ((Parse.short_ident --| Parse.$$$ ":") -- Scan.repeat1 Parse.short_ident) >> (Toplevel.theory o (fold (register_variable_name true))));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_register_premise_set_names\<close> "Register names for premise sets."
    (Scan.repeat1 Parse.short_ident >> (Toplevel.theory o fold (fn prefix => AOT_PremiseSetPrefix.map (Symtab.update (prefix,())))));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_register_type_constraints\<close> "Register constraints for term types."
    (Parse.and_list1 ((Parse.short_ident --| Parse.$$$ ":") -- (Parse.typ -- Scan.option Parse.typ)) >> (Toplevel.theory o fold register_constraint));
\<close>

AOT_register_type_constraints
  Individual: \<open>_::AOT_UnaryIndividualTerm\<close> \<open>_::AOT_IndividualTerm\<close> and
  Proposition: \<o> and
  Relation: \<open><_::AOT_IndividualTerm>\<close> and
  Term: \<open>_::AOT_Term\<close>

AOT_register_variable_names
  Individual: x y z \<nu> \<mu> a b c d and
  Proposition: p q r s and
  Relation: F G H P Q R S and
  Term: \<alpha> \<beta> \<gamma> \<delta>

AOT_register_metavariable_names
  Individual: \<kappa> and
  Proposition: \<phi> \<psi> \<chi> \<theta> \<zeta> \<xi> \<Theta> and
  Relation: \<Pi> and
  Term: \<tau> \<sigma>

AOT_register_premise_set_names \<Gamma> \<Delta> \<Lambda>


ML\<open>
fun decode_pos str =
  case (Term_Position.decode str) of SOME pos => pos
  | _ => raise Fail "expected position"
fun unconstrain_var (Ast.Appl [Ast.Constant "_constrain", Ast.Variable name, Ast.Variable pos]) = (name, decode_pos pos)
  | unconstrain_var ast = raise Ast.AST ("Expected position constrained variable.", [ast])
fun make_constrained_var sx = (Ast.Appl [Ast.Constant "_constrain", Ast.Variable (Symbol_Pos.implode sx), Ast.Variable (Term_Position.encode (Position.range_position (Symbol_Pos.range sx)))])
fun implode_pos x = (Symbol_Pos.implode_range (Symbol_Pos.range x) x) |> (fn (x,y) => (x,Position.range_position y))
fun splitFormulaParts x = x |> unconstrain_var |> Symbol_Pos.explode |>
   Scan.finite Symbol_Pos.stopper (Scan.repeat (
  (Scan.one (Symbol_Pos.symbol #> Symbol.is_letter) --
  (((Scan.repeat (Symbol_Pos.$$ "\<^sub>" -- (Scan.one (Symbol_Pos.symbol #> Symbol.is_digit)) >> (fn (x,y) => [x,y])) >> List.concat )
  -- (Scan.repeat (Symbol_Pos.$$ "'"))) >> (fn (x,y) => x@y)))))
fun parseFormulaParts x = (case splitFormulaParts x of (parts,[]) => parts |> map (fn (x,y) => implode_pos (x::y))
    | _ => raise Ast.AST ("Expected one or more variable or term names.", [x]))
fun foldAppl const = List.rev #> (fn list => fold (fn a => fn b => (Ast.mk_appl (Ast.Constant const) [a,b])) (tl list) (hd list))
fun dropConstraints (Const ("_constrain", _) $ x $ _) = dropConstraints x
  | dropConstraints (Const ("_constrainAbs", _) $ x $ _) = dropConstraints x
  | dropConstraints (Abs (a, b, x)) = Abs (a, b, dropConstraints x)
  | dropConstraints (x$y) = dropConstraints x $ dropConstraints y
  | dropConstraints x = x
\<close>


parse_ast_translation\<open>
let
fun constrain (name, pos) = Ast.mk_appl (Ast.Constant "_constrain") [Ast.Variable name, Ast.Variable (Term_Position.encode pos)]
fun splitExeVars [x] = x |> parseFormulaParts |> map constrain |> 
  map (fn x => Ast.mk_appl (Ast.Constant "_AOT_term_var") [x]) |>
  foldAppl "_AOT_exe_args"
fun splitLambdaVars [x] = x |> parseFormulaParts |> map constrain |> 
  map (fn x => Ast.mk_appl (Ast.Constant "_AOT_var") [x]) |>
  foldAppl \<^const_syntax>\<open>Pair\<close>
fun checkSingleVar [x] = x |> parseFormulaParts |> map constrain |>
  (fn [x] => Ast.mk_appl (Ast.Constant "_AOT_var") [x] | _ => raise Ast.AST ("Expected single variable.", [x]))
in
[
  (\<^syntax_const>\<open>_AOT_var\<close>, K checkSingleVar),
  (\<^syntax_const>\<open>_AOT_exe_vars\<close>, K splitExeVars),
  (\<^syntax_const>\<open>_AOT_lambda_vars\<close>, K splitLambdaVars)
]
end
\<close>

consts AOT_denotes :: \<open>'a::AOT_Term \<Rightarrow> \<o>\<close>
       AOT_imp :: \<open>[\<o>, \<o>] \<Rightarrow> \<o>\<close>
       AOT_not :: \<open>\<o> \<Rightarrow> \<o>\<close>
       AOT_box :: \<open>\<o> \<Rightarrow> \<o>\<close>
       AOT_act :: \<open>\<o> \<Rightarrow> \<o>\<close>
       AOT_forall :: \<open>('a::AOT_Term \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close>
       AOT_eq :: \<open>'a::AOT_Term \<Rightarrow> 'a::AOT_Term \<Rightarrow> \<o>\<close>
       AOT_desc :: \<open>('a::AOT_UnaryIndividualTerm \<Rightarrow> \<o>) \<Rightarrow> 'a\<close>
       AOT_exe :: \<open><'a::AOT_IndividualTerm> \<Rightarrow> 'a \<Rightarrow> \<o>\<close>
       AOT_lambda :: \<open>('a::AOT_IndividualTerm \<Rightarrow> \<o>) \<Rightarrow> <'a>\<close>
       AOT_lambda0 :: \<open>\<o> \<Rightarrow> \<o>\<close>
       AOT_concrete :: \<open><\<kappa>>\<close>
nonterminal desc
nonterminal exe_args
nonterminal \<Pi>0
syntax "_AOT_denotes" :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>_\<down>\<close>)
       "_AOT_imp" :: \<open>[\<phi>, \<phi>] \<Rightarrow> \<phi>\<close> (infixl \<open>\<rightarrow>\<close> 25)
       "_AOT_not" :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>~_\<close> [50] 50)
       "_AOT_not" :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>\<not>_\<close> [50] 50)
       "_AOT_box" :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>\<box>_\<close> [49] 54)
       "_AOT_act" :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>\<^bold>\<A>_\<close> [49] 54)
       "_AOT_all" :: \<open>\<alpha> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (\<open>\<forall>_ _\<close> [1,40])
       "_AOT_all_ellipse" :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (\<open>\<forall>_...\<forall>_ _\<close> [1,40])
       "_AOT_eq" :: \<open>[\<tau>, \<tau>] \<Rightarrow> \<phi>\<close> (infixl \<open>=\<close> 50)
       "_AOT_desc" :: \<open>\<alpha> \<Rightarrow> \<phi> \<Rightarrow> desc\<close> ("\<^bold>\<iota>__" [1,1000])
       "" :: \<open>desc \<Rightarrow> \<kappa>\<^sub>s\<close> ("_")
       "_AOT_lambda" :: \<open>lambda_args \<Rightarrow> \<phi> \<Rightarrow> \<Pi>\<close> (\<open>[\<lambda>_ _]\<close>)
       "_explicitRelation" :: \<open>\<tau> \<Rightarrow> \<Pi>\<close> ("[_]")
       "" :: \<open>\<kappa>\<^sub>s \<Rightarrow> exe_arg\<close> ("_")
       "" :: \<open>exe_arg \<Rightarrow> exe_args\<close> ("_")
       "_AOT_exe_args" :: \<open>exe_arg \<Rightarrow> exe_args \<Rightarrow> exe_args\<close> ("__")
       "_AOT_exe_arg_ellipse" :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> exe_arg\<close> ("_..._")
       "_AOT_lambda_arg_ellipse" :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> lambda_args\<close> ("_..._")
       "_AOT_term_ellipse" :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> \<tau>\<close> ("_..._")
       "_AOT_exe" :: \<open>\<Pi> \<Rightarrow> exe_args \<Rightarrow> \<phi>\<close> (\<open>__\<close>)
       "_AOT_enc" :: \<open>exe_args \<Rightarrow> \<Pi> \<Rightarrow> \<phi>\<close> (\<open>__\<close>)
       "_AOT_lambda0" :: \<open>\<phi> \<Rightarrow> \<Pi>0\<close> (\<open>[\<lambda> _]\<close>)
       "" :: \<open>\<Pi>0 \<Rightarrow> \<phi>\<close> ("_")
       "" :: \<open>\<Pi>0 \<Rightarrow> \<tau>\<close> ("_")
       "_AOT_concrete" :: \<open>\<Pi>\<close> (\<open>E!\<close>)
syntax "" :: \<open>any \<Rightarrow> exe_arg\<close> ("\<guillemotleft>_\<guillemotright>")

translations
  "_AOT_denotes \<tau>" => "CONST AOT_denotes \<tau>"
  "_AOT_imp \<phi> \<psi>" => "CONST AOT_imp \<phi> \<psi>"
  "_AOT_not \<phi>" => "CONST AOT_not \<phi>"
  "_AOT_box \<phi>" => "CONST AOT_box \<phi>"
  "_AOT_act \<phi>" => "CONST AOT_act \<phi>"
  "_AOT_eq \<tau> \<tau>'" => "CONST AOT_eq \<tau> \<tau>'"
  "_AOT_lambda0 \<phi>" => "CONST AOT_lambda0 \<phi>"
  "_AOT_concrete" => "CONST AOT_concrete"
  "_AOT_lambda \<alpha> \<phi>" => "CONST AOT_lambda (_abs \<alpha> \<phi>)"
  "_explicitRelation \<Pi>" => "\<Pi>"

AOT_syntax_print_translations
  "_AOT_denotes \<tau>" <= "CONST AOT_denotes \<tau>"
  "_AOT_imp \<phi> \<psi>" <= "CONST AOT_imp \<phi> \<psi>"
  "_AOT_not \<phi>" <= "CONST AOT_not \<phi>"
  "_AOT_box \<phi>" <= "CONST AOT_box \<phi>"
  "_AOT_act \<phi>" <= "CONST AOT_act \<phi>"
  "_AOT_all \<alpha> \<phi>" <= "CONST AOT_forall (_abs \<alpha> \<phi>)"
  "_AOT_all \<alpha> \<phi>" <= "CONST AOT_forall (\<lambda>\<alpha>. \<phi>)"
  "_AOT_eq \<tau> \<tau>'" <= "CONST AOT_eq \<tau> \<tau>'"
  "_AOT_desc x \<phi>" <= "CONST AOT_desc (_abs x \<phi>)"
  "_AOT_desc x \<phi>" <= "CONST AOT_desc (\<lambda>x. \<phi>)"
  "_AOT_lambda0 \<phi>" <= "CONST AOT_lambda0 \<phi>"
  "_AOT_concrete" <= "CONST AOT_concrete"
  "_AOT_lambda \<alpha> \<phi>" <= "CONST AOT_lambda (_abs \<alpha> \<phi>)"
  "_AOT_lambda \<alpha> \<phi>" <= "CONST AOT_lambda (\<lambda> \<alpha> . \<phi>)"
  "_AOT_exe (_AOT_lambda vars \<phi>) args" <= "CONST AOT_exe (_AOT_lambda vars \<phi>) args"
  "_AOT_exe (_explicitRelation \<Pi>) args" <= "CONST AOT_exe \<Pi> args"


nonterminal free_var
nonterminal free_vars
syntax "" :: \<open>desc \<Rightarrow> free_var\<close> ("_")
syntax "" :: \<open>\<Pi> \<Rightarrow> free_var\<close> ("_")
syntax "_AOT_appl" :: \<open>id_position \<Rightarrow> free_vars \<Rightarrow> \<phi>\<close> ("_'{_'}")
syntax "_AOT_appl" :: \<open>id_position \<Rightarrow> free_vars \<Rightarrow> \<tau>\<close> ("_'{_'}")
syntax "_AOT_appl" :: \<open>id_position \<Rightarrow> free_vars \<Rightarrow> free_vars\<close> ("_'{_'}")
syntax "_AOT_appl" :: \<open>id_position \<Rightarrow> free_vars \<Rightarrow> free_vars\<close> ("_'{_'}")
syntax "_AOT_term_var" :: \<open>id_position \<Rightarrow> free_var\<close> ("_")
syntax "" :: \<open>any \<Rightarrow> free_var\<close> ("\<guillemotleft>_\<guillemotright>")
syntax "" :: \<open>free_var \<Rightarrow> free_vars\<close> ("_")
syntax "_AOT_args" :: \<open>free_var \<Rightarrow> free_vars \<Rightarrow> free_vars\<close> ("_,_")
syntax "_AOT_free_var_ellipse" :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> free_var\<close> ("_..._")

translations
  "_AOT_appl \<phi> (_AOT_args a b)" => "_AOT_appl (\<phi> a) b"
  "_AOT_appl \<phi> a" => "\<phi> a"

ML\<open>
fun parseVar unary ctxt [var as Const ("_constrain", _) $ Free (x,_) $ Free _] =
        Const ("_constrain", dummyT) $ var $ (case fetchTermConstraint ctxt x unary of
            SOME (AOT_MetaVariable,_) => raise Term.TERM ("Expected variable prefix, but got metavariable prefix.", [var])
          | SOME (AOT_Variable _, constraint) => constraint
          | _ => raise Term.TERM ("Unknown variable prefix.", [var]))
  | parseVar _ _ var = raise Term.TERM ("Expected constrained free variable.", var)

fun constrainTrm ctxt forceMeta unary (Free (var, _)) = (fn trm =>
      case fetchTermConstraint ctxt var unary of
        SOME (AOT_MetaVariable,constraint) => Const ("_constrain", dummyT) $ trm $ constraint
      | SOME (AOT_Variable restr, constraint) =>
          if forceMeta then Const ("_constrain", dummyT) $ trm $ constraint
          else Const ("_constrain", dummyT) $ (Const (\<^const_name>\<open>AOT_term_of_var\<close>, dummyT) $ (case restr of SOME (_,r) => r $ trm | _ => trm)) $ constraint
      | _ => raise Term.TERM ("Unknown variable or metavariable prefix.", [trm]))
  | constrainTrm _ _ _ (Bound _) = (fn var => var)
  | constrainTrm _ _ _ trm = raise Term.TERM ("Expected free or bound variable.", [trm])
fun isPremiseVar ctxt (Free (var, _)) = AOT_IsPremiseSetPrefix ctxt (hd (Symbol.explode var))
  | isPremiseVar _ _ = false
fun getVarConstraint ctxt unary (Free (var, _)) = (case fetchTermConstraint ctxt var unary of
        SOME (AOT_MetaVariable,_) => NONE
      | SOME (AOT_Variable Rep_term,_) => Option.map fst Rep_term
      | _ => NONE)
  | getVarConstraint _ _ _ = NONE
fun getVarConstraints ctxt (Const (\<^syntax_const>\<open>_AOT_term_var\<close>, _) $ v) = (case (getVarConstraint ctxt true (dropConstraints v)) of SOME c => [(c,v)] | _ => [])
  | getVarConstraints ctxt (Const ("_AOT_term_vars", _) $ v) = (case (getVarConstraint ctxt true (dropConstraints v)) of SOME c => [(c,v)] | _ => [])
  | getVarConstraints _ (Const (\<^syntax_const>\<open>_AOT_verbatim\<close>, _) $ _) = []
  | getVarConstraints ctxt (x $ y)  = getVarConstraints ctxt x @ getVarConstraints ctxt y
  | getVarConstraints ctxt (Abs (_,_,z)) = getVarConstraints ctxt z
  | getVarConstraints _ _ = []
fun processFreesForceMeta forceMeta premiseVars ctxt (Const (\<^syntax_const>\<open>_AOT_term_var\<close>, _) $ v) = (
    if isPremiseVar ctxt (dropConstraints v) then (dropConstraints v, if List.find (fn x => x = v) premiseVars = NONE then v::premiseVars else premiseVars)
                         else (constrainTrm ctxt forceMeta true (dropConstraints v) v, premiseVars))
  | processFreesForceMeta forceMeta premiseVars ctxt (Const ("_AOT_term_vars", _) $ v) = (
    if isPremiseVar ctxt (dropConstraints v) then (v, if List.find (fn x => x = v) premiseVars = NONE then v::premiseVars else premiseVars)
     else (constrainTrm ctxt forceMeta false (dropConstraints v) v, premiseVars)
  )
  | processFreesForceMeta _ premiseVars _ (Const (\<^syntax_const>\<open>_AOT_verbatim\<close>, _) $ v) = (v, premiseVars)
  | processFreesForceMeta forceMeta premiseVars ctxt (x $ y)  = let
          val (x, premiseVars) = processFreesForceMeta forceMeta premiseVars ctxt x
          val (y, premiseVars) = processFreesForceMeta forceMeta premiseVars ctxt y
      in (x $ y, premiseVars) end
  | processFreesForceMeta forceMeta premiseVars ctxt (Abs (x,y,z)) = let
      val (z, premiseVars) = processFreesForceMeta forceMeta premiseVars ctxt z
      in (Abs (x,y,z), premiseVars) end
  | processFreesForceMeta _ premiseVars _ x = (x, premiseVars)
fun processFrees ctxt trm = (case processFreesForceMeta false [] ctxt trm of (r,[]) => r | _ => raise Term.TERM ("No premise set expected in term.", [trm]))
fun processFreesAlwaysMeta ctxt trm = (case processFreesForceMeta true [] ctxt trm of (r,[]) => r | _ => raise Term.TERM ("No premise set expected in term.", [trm]))
val processFreesAndPremises = processFreesForceMeta false []
\<close>

(* TODO: move *)

nonterminal AOT_props
nonterminal AOT_premises
nonterminal AOT_world_relative_prop
syntax "_AOT_premises" :: \<open>AOT_world_relative_prop \<Rightarrow> AOT_premises \<Rightarrow> AOT_premises\<close> (infixr \<open>,\<close> 3)
       "_AOT_world_relative_prop" :: "\<phi> \<Rightarrow> AOT_world_relative_prop" ("_")
       "" :: "AOT_world_relative_prop \<Rightarrow> AOT_premises" ("_")
       "_AOT_prop" :: \<open>AOT_world_relative_prop \<Rightarrow> AOT_prop\<close> (\<open>_\<close>)
       "" :: \<open>AOT_prop \<Rightarrow> AOT_props\<close> (\<open>_\<close>)
       "_AOT_derivable" :: "AOT_premises \<Rightarrow> \<phi>' \<Rightarrow> AOT_prop" (infixl \<open>\<^bold>\<turnstile>\<close> 2)
       "_AOT_nec_derivable" :: "AOT_premises \<Rightarrow> \<phi>' \<Rightarrow> AOT_prop" (infixl \<open>\<^bold>\<turnstile>\<^sub>\<box>\<close> 2)
       "_AOT_theorem" :: "\<phi>' \<Rightarrow> AOT_prop" (\<open>\<^bold>\<turnstile> _\<close>)
       "_AOT_nec_theorem" :: "\<phi>' \<Rightarrow> AOT_prop" (\<open>\<^bold>\<turnstile>\<^sub>\<box> _\<close>)
       "_AOT_equiv_def" :: \<open>\<phi> \<Rightarrow> \<phi> \<Rightarrow> AOT_prop\<close> (infixl \<open>\<equiv>\<^sub>d\<^sub>f\<close> 3)
       "_AOT_axiom" :: "\<phi>' \<Rightarrow> AOT_axiom" (\<open>_\<close>)
       "_AOT_act_axiom" :: "\<phi>' \<Rightarrow> AOT_act_axiom" (\<open>_\<close>)
       "_AOT_axiom" :: "\<phi>' \<Rightarrow> AOT_prop" (\<open>_ \<in> \<Lambda>\<^sub>\<box>\<close>)
       "_AOT_act_axiom" :: "\<phi>' \<Rightarrow> AOT_prop" (\<open>_ \<in> \<Lambda>\<close>)
       "_AOT_id_def" :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> AOT_prop\<close> (infixl \<open>=\<^sub>d\<^sub>f\<close> 3)
       "_AOT_for_arbitrary" :: \<open>id_position \<Rightarrow> AOT_prop \<Rightarrow> AOT_prop\<close> (\<open>for arbitrary _: _\<close> [1000,1] 1)

AOT_syntax_print_translations
  "_AOT_act_axiom \<phi>" <= "CONST AOT_model_act_axiom \<phi>"
  "_AOT_axiom \<phi>" <= "CONST AOT_model_axiom \<phi>"

parse_translation\<open>
let
fun makeArgList (Const (\<^syntax_const>\<open>_AOT_exe_args\<close>, _) $ y $ z) = makeArgList y @ makeArgList z
  | makeArgList t = [t]
fun makePairs (x::[]) = x
  | makePairs (x::xs) = Const (\<^const_syntax>\<open>Pair\<close>, dummyT) $ x $ makePairs xs
fun makeExeArgs y = makePairs (makeArgList y)
fun parseExe ctxt [x,y] = (Const (\<^const_syntax>\<open>AOT_exe\<close>, dummyT) $ x $ makeExeArgs y)
fun parseEnc ctxt [x,y] = (Const ("AOT_enc", dummyT) $ makeExeArgs x $ y)
fun parseEquivDef ctxt lhs rhs = let
val constraints = getVarConstraints ctxt lhs
fun collectConstraints c [] = c
 | collectConstraints NONE ((x,y)::xs) = collectConstraints (SOME (x $ y)) xs
 | collectConstraints (SOME c) ((x,y)::xs) = collectConstraints (SOME (Const ("AOT_conj", dummyT) $  c $ (x $ y))) xs
val rhs = (case collectConstraints NONE constraints of SOME c => Const ("AOT_conj", dummyT) $ c $ rhs | _ => rhs)
in
HOLogic.mk_Trueprop (\<^const>\<open>AOT_model_equiv_def\<close> $ processFreesAlwaysMeta ctxt lhs $ processFreesAlwaysMeta ctxt rhs)
end
in
[
  (\<^syntax_const>\<open>_AOT_var\<close>, parseVar true),
  ("_AOT_vars", parseVar false),
  (\<^syntax_const>\<open>_AOT_valid\<close>, fn ctxt => fn [w,x] => \<^const>\<open>AOT_model_valid_in\<close> $ w $ x),
  (\<^syntax_const>\<open>_AOT_quoted\<close>, fn ctxt => fn [x] => x),
  (\<^syntax_const>\<open>_AOT_process_frees\<close>, fn ctxt => fn [x] => processFrees ctxt x),
  (\<^syntax_const>\<open>_AOT_premises\<close>, fn ctxt => fn [x,y] => Abs ("v", dummyT, @{const Pure.conjunction} $ (x $ Bound 0) $ (y $ Bound 0))),
  (\<^syntax_const>\<open>_AOT_world_relative_prop\<close>, fn ctxt => fn [x] => let
    val (x, premises) = processFreesAndPremises ctxt x
    val (world::formulas) = Variable.variant_frees ctxt [x] (("v", dummyT)::(map (fn _ => ("\<phi>", dummyT)) premises))
    val term = HOLogic.mk_Trueprop (@{const AOT_model_valid_in} $ Free world $ processFrees ctxt x)
    val term = fold (fn (premise,form) => fn trm =>
         @{const "Pure.imp"} $
        HOLogic.mk_Trueprop (Const (\<^const_name>\<open>Set.member\<close>, dummyT) $ Free form $ premise) $
        (Term.absfree (Term.dest_Free (dropConstraints premise)) trm $ Free form)
    ) (ListPair.zipEq (premises,formulas)) term
    val term = fold (fn (form) => fn trm =>
         Const (\<^const_name>\<open>Pure.all\<close>, dummyT) $
        (Term.absfree form trm)
    ) formulas term
    val term = Term.absfree world term
    in term end),
  (\<^syntax_const>\<open>_AOT_prop\<close>, fn ctxt => fn [x] => let
    val world = case (AOT_ProofData.get ctxt) of SOME w => w | _ => raise Fail "Expected world to be stored in the proof state."
    in x $ world end),
  (\<^syntax_const>\<open>_AOT_theorem\<close>, fn ctxt => fn [x] => HOLogic.mk_Trueprop (@{const AOT_model_valid_in} $ @{const w\<^sub>0} $ x)),
  (\<^syntax_const>\<open>_AOT_axiom\<close>, fn ctxt => fn [x] => HOLogic.mk_Trueprop (@{const AOT_model_axiom} $ x)),
  (\<^syntax_const>\<open>_AOT_act_axiom\<close>, fn ctxt => fn [x] => HOLogic.mk_Trueprop (@{const AOT_model_act_axiom} $ x)),
  (\<^syntax_const>\<open>_AOT_nec_theorem\<close>, fn ctxt => fn [trm] => let
    val world = singleton (Variable.variant_frees ctxt [trm]) ("v", @{typ w})
    val trm = HOLogic.mk_Trueprop (@{const AOT_model_valid_in} $ Free world $ trm)
    val trm = Term.absfree world trm
    val trm = Const (\<^const_name>\<open>Pure.all\<close>, dummyT) $ trm
    in trm end),
  (\<^syntax_const>\<open>_AOT_derivable\<close>, fn ctxt => fn [x,y] => let
    val world = case (AOT_ProofData.get ctxt) of SOME w => w | _ => raise Fail "Expected world to be stored in the proof state."
    in @{const "Pure.imp"} $ (x $ world) $ HOLogic.mk_Trueprop  (@{const AOT_model_valid_in} $ world $ y) end),
  (\<^syntax_const>\<open>_AOT_nec_derivable\<close>, fn ctxt => fn [x,y] => let
    in Const (\<^const_name>\<open>Pure.all\<close>, dummyT) $ Abs ("v", dummyT, @{const "Pure.imp"} $ (x $ Bound 0) $ HOLogic.mk_Trueprop (@{const AOT_model_valid_in} $ Bound 0 $ y)) end),
  (\<^syntax_const>\<open>_AOT_for_arbitrary\<close>, fn ctxt => fn [_ $ var $ pos,trm] => let
    val trm = Const (\<^const_name>\<open>Pure.all\<close>, dummyT) $ (Const ("_constrainAbs", dummyT) $ Term.absfree (Term.dest_Free var) trm $ pos)
    in trm end),
  (\<^syntax_const>\<open>_AOT_equiv_def\<close>, fn ctxt => fn [x,y] => parseEquivDef ctxt x y),
  (\<^syntax_const>\<open>_AOT_exe\<close>, parseExe),
  (\<^syntax_const>\<open>_AOT_enc\<close>, parseEnc)
]
end
\<close>

ML\<open>
fun parseEllipseList constName _ [s,e] =
  let
    val (start_name, start_pos) = unconstrain_var s
    val (end_name, end_pos) = unconstrain_var e
    val _ = let val h = hd (Symbol.explode start_name) in
        if (h = hd (Symbol.explode end_name)) then h else raise Ast.AST ("Invalid ellipses.", [s,e])
      end
    val name = (Symbol_Pos.explode (start_name, start_pos)) @ (Symbol_Pos.explode (end_name, end_pos))
  in
    Ast.mk_appl (Ast.Constant constName) [make_constrained_var name]
  end
  | parseEllipseList _ _ _ = raise Fail "Invalid ellipse parsing."
\<close>

parse_ast_translation\<open>
[
  (\<^syntax_const>\<open>_AOT_exe_arg_ellipse\<close>, parseEllipseList "_AOT_term_vars"),
  (\<^syntax_const>\<open>_AOT_lambda_arg_ellipse\<close>, parseEllipseList "_AOT_vars"),
  (\<^syntax_const>\<open>_AOT_free_var_ellipse\<close>, parseEllipseList "_AOT_term_vars"),
  (\<^syntax_const>\<open>_AOT_term_ellipse\<close>, parseEllipseList "_AOT_term_vars"),
  (\<^syntax_const>\<open>_AOT_all_ellipse\<close>, fn ctx => fn [a,b,c] => Ast.mk_appl (Ast.Constant \<^const_name>\<open>AOT_forall\<close>) [
      Ast.mk_appl (Ast.Constant "_abs") [parseEllipseList "_AOT_vars" ctx [a,b],c]
  ]) (* TODO: restricted variables in ellipse quantification *)
]
\<close>

print_translation \<open>
AOT_syntax_print_translations
 [
  Syntax_Trans.preserve_binder_abs_tr' \<^const_syntax>\<open>AOT_forall\<close> \<^syntax_const>\<open>_AOT_all\<close>,
  AOT_binder_trans @{theory} @{binding "AOT_forall_binder"} \<^syntax_const>\<open>_AOT_all\<close>,
  Syntax_Trans.preserve_binder_abs_tr' \<^const_syntax>\<open>AOT_desc\<close> \<^syntax_const>\<open>_AOT_desc\<close>,
  AOT_binder_trans @{theory} @{binding "AOT_desc_binder"} \<^syntax_const>\<open>_AOT_desc\<close>,
  Syntax_Trans.preserve_binder_abs_tr' \<^const_syntax>\<open>AOT_lambda\<close> \<^syntax_const>\<open>_AOT_lambda\<close>,
  AOT_binder_trans @{theory} @{binding "AOT_lambda_binder"} \<^syntax_const>\<open>_AOT_lambda\<close>
 ]
\<close> \<comment> \<open>to avoid eta-contraction\<close>

parse_translation\<open>
let
fun parseIdDef ctxt [lhs, rhs] =
  let
    val lhs = processFreesAlwaysMeta ctxt lhs
    val rhs = processFreesAlwaysMeta ctxt rhs
    fun add_frees (Free _) frees = frees
      | add_frees (Const _) frees = frees
      | add_frees (Free _ $ args) frees = Term.add_frees args frees
      | add_frees (Const _ $ args) frees = Term.add_frees args frees
      | add_frees (args $ args') frees = Term.add_frees args' (Term.add_frees args frees)
      | add_frees trm _ = raise Term.TERM ("Expected definition term.", [trm])
    val lhs' = dropConstraints lhs
    val rhs' = dropConstraints rhs
    val frees = add_frees lhs' []
    val _ = frees = add_frees rhs' frees orelse
            raise Term.TERM ("Invalid free variables on RHS.", [lhs,rhs])
    fun mkabs trm = if frees = [] then Const (\<^const_name>\<open>case_unit\<close>, dummyT) $ trm else
       fold_rev (fn (s, T) => fn t => Const (\<^const_name>\<open>case_prod\<close>, dummyT) $ Term.absfree (s, T) t)
                (List.rev (tl frees)) (Term.absfree (hd frees) trm)
    val lhs_abs = mkabs lhs
    val rhs_abs = mkabs rhs
  in
(* Type ("fun", [Type ("fun", [dummyT, dummyT]), Type ("fun", [Type ("fun", [dummyT, dummyT]), @{typ bool}])]) *)
    (Const ("_constrain", dummyT) $
     Const (\<^const_name>\<open>AOT_model_id_def\<close>, dummyT) $
     (Const (\<^type_syntax>\<open>fun\<close>, dummyT) $
        (Const (\<^type_syntax>\<open>fun\<close>, dummyT) $ Const (\<^type_syntax>\<open>dummy\<close>, dummyT) $ (getConstraint ctxt false "Term")) $
        (Const (\<^type_syntax>\<open>dummy\<close>, dummyT)))
    )
    $ lhs_abs $ rhs_abs
  end
in
[(\<^syntax_const>\<open>_AOT_id_def\<close>, parseIdDef)]
end
\<close>

AOT_define AOT_dia :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>\<diamond>_\<close> [49] 54) \<open>\<diamond>\<phi> \<equiv>\<^sub>d\<^sub>f \<not>\<box>\<not>\<phi>\<close>
AOT_define AOT_conj :: \<open>[\<phi>, \<phi>] \<Rightarrow> \<phi>\<close> (infixl \<open>&\<close> 35) \<open>\<phi> & \<psi> \<equiv>\<^sub>d\<^sub>f \<not>(\<phi> \<rightarrow> \<not>\<psi>)\<close>
AOT_define AOT_disj :: \<open>[\<phi>, \<phi>] \<Rightarrow> \<phi>\<close> (infixl \<open>\<or>\<close> 35) \<open>\<phi> \<or> \<psi> \<equiv>\<^sub>d\<^sub>f \<not>\<phi> \<rightarrow> \<psi>\<close>
AOT_define AOT_equiv :: \<open>[\<phi>, \<phi>] \<Rightarrow> \<phi>\<close> (infix \<open>\<equiv>\<close> 20) \<open>\<phi> \<equiv> \<psi> \<equiv>\<^sub>d\<^sub>f (\<phi> \<rightarrow> \<psi>) & (\<psi> \<rightarrow> \<phi>)\<close>

context AOT_meta_syntax
begin
notation AOT_dia ("\<^bold>\<diamond>_" [49] 54)
notation AOT_conj (infixl \<open>\<^bold>&\<close> 35)
notation AOT_disj (infixl \<open>\<^bold>\<or>\<close> 35)
notation AOT_equiv (infixl \<open>\<^bold>\<equiv>\<close> 20)
end
context AOT_no_meta_syntax
begin
no_notation AOT_dia ("\<^bold>\<diamond>_" [49] 54)
no_notation AOT_conj (infixl \<open>\<^bold>&\<close> 35)
no_notation AOT_disj (infixl \<open>\<^bold>\<or>\<close> 35)
no_notation AOT_equiv (infixl \<open>\<^bold>\<equiv>\<close> 20)
end

ML\<open>
fun AOT_restricted_binder const connect = fn ctxt => (fn [a, b] => Ast.mk_appl (Ast.Constant const) [
let
val b = case a of (Ast.Appl [Ast.Constant "_AOT_var", var]) => (
case fetchTermCategory ctxt (hd (Symbol.explode (fst (unconstrain_var var)))) of SOME (AOT_Variable _, category) =>
  let
  val (restr, _) = Local_Theory.raw_theory_result (fn thy => (Symtab.lookup (AOT_Restriction.get thy) category, thy)) ctxt
  in case restr of SOME _ => Ast.mk_appl (Ast.Constant connect) [Ast.mk_appl (Ast.mk_appl (Ast.Constant "_AOT_restriction") [Ast.Constant category]) [a], b] | _ => b end | _ => b) | _ => b
in
  Ast.mk_appl (Ast.Constant "_abs")  [a,b]
end] | _ => raise Match)
\<close>

parse_ast_translation\<open>
[(\<^syntax_const>\<open>_AOT_all\<close>, AOT_restricted_binder \<^const_name>\<open>AOT_forall\<close> \<^const_name>\<open>AOT_imp\<close>),
 (\<^syntax_const>\<open>_AOT_desc\<close>, AOT_restricted_binder \<^const_name>\<open>AOT_desc\<close> \<^const_name>\<open>AOT_conj\<close>)]
\<close>


AOT_define AOT_exists :: \<open>\<alpha> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> \<open>\<guillemotleft>AOT_exists \<phi>\<guillemotright> \<equiv>\<^sub>d\<^sub>f \<not>\<forall>\<alpha> \<not>\<phi>{\<alpha>}\<close>
syntax "_AOT_exists" :: \<open>\<alpha> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> ("\<exists>_ _" [1,40])

AOT_syntax_print_translations
  "_AOT_exists \<alpha> \<phi>" <= "CONST AOT_exists (_abs \<alpha> \<phi>)"
  "_AOT_exists \<alpha> \<phi>" <= "CONST AOT_exists (\<lambda>\<alpha>. \<phi>)"

parse_ast_translation\<open>                              
[(\<^syntax_const>\<open>_AOT_exists\<close>, AOT_restricted_binder \<^const_name>\<open>AOT_exists\<close> \<^const_name>\<open>AOT_conj\<close>)]
\<close>

context AOT_meta_syntax
begin
notation AOT_exists (binder "\<^bold>\<exists>" 8)
end
context AOT_no_meta_syntax
begin
no_notation AOT_exists (binder "\<^bold>\<exists>" 8)
end


syntax
   "_AOT_exists_ellipse" :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (\<open>\<exists>_...\<exists>_ _\<close> [1,40])
parse_ast_translation\<open>[(\<^syntax_const>\<open>_AOT_exists_ellipse\<close>, fn ctx => fn [a,b,c] =>
  Ast.mk_appl (Ast.Constant "AOT_exists") [Ast.mk_appl (Ast.Constant "_abs") [parseEllipseList "_AOT_vars" ctx [a,b],c]])]\<close>
print_translation\<open>AOT_syntax_print_translations
  [Syntax_Trans.preserve_binder_abs_tr' \<^const_syntax>\<open>AOT_exists\<close> \<^syntax_const>\<open>_AOT_exists\<close>,
  AOT_binder_trans @{theory} @{binding "AOT_exists_binder"} \<^syntax_const>\<open>_AOT_exists\<close>]
\<close>



syntax "_AOT_DDDOT" :: "\<phi>" ("...")
syntax "_AOT_DDDOT" :: "\<phi>" ("\<dots>")
parse_translation\<open>
[(\<^syntax_const>\<open>_AOT_DDDOT\<close>, fn ctxt => fn ts =>
let
val trm = Proof_Context.get_fact_single ctxt (Facts.named (Long_Name.localN ^ Long_Name.separator ^ Auto_Bind.thisN))
val trm = Thm.concl_of trm
(* TODO: find a proper way to do this *)
fun mapTerms (Free (x,typ)) = (case List.rev (String.explode x) of #"_" :: #"_" :: tl =>
  Free (String.implode (List.rev tl), typ) | _ => Free (x,typ))
  | mapTerms x = x
val trm = Term.map_aterms mapTerms trm
fun readThisRHS (Const ("HOL.Trueprop", _) $ (Const ("AOT_model.AOT_model_valid_in", dummyT) $ _ $ (Const _ $ _ $ rhs))) = rhs
  | readThisRHS _ = raise Term.TERM ("Could not expand ... from term.", [trm])
in
readThisRHS trm
end
)]
\<close>



(* TODO: experimental printing mode: *)


print_translation\<open>AOT_syntax_print_translations
[(\<^const_syntax>\<open>Pure.all\<close>, fn ctxt => fn [Abs (_, _,
  Const (\<^const_syntax>\<open>HOL.Trueprop\<close>, _) $ (Const (\<^const_syntax>\<open>AOT_model_valid_in\<close>, _) $ Bound 0 $ y))] => let
    val y = (Const (\<^syntax_const>\<open>_AOT_process_frees\<close>, dummyT) $ y)
    in (Const (\<^syntax_const>\<open>_AOT_nec_theorem\<close>, dummyT) $ y) end
| [p as Abs (name, _,
  Const (\<^const_syntax>\<open>HOL.Trueprop\<close>, _) $ (Const (\<^const_syntax>\<open>AOT_model_valid_in\<close>, _) $ w $ y))]
=> (Const (\<^syntax_const>\<open>_AOT_for_arbitrary\<close>, dummyT) $ (Const ("_bound", dummyT) $ Free (name, dummyT)) $ (Term.betapply (p, (Const ("_bound", dummyT) $ Free (name, dummyT)))))
),

 (\<^const_syntax>\<open>AOT_model_valid_in\<close>, fn ctxt => fn [w as (Const ("_free", _) $ Free (v, _)), y] => let
    val is_world = (case (AOT_ProofData.get ctxt) of SOME (Free (w, _)) => Name.clean w = Name.clean v | _ => false)
    val y = (Const (\<^syntax_const>\<open>_AOT_process_frees\<close>, dummyT) $ y)
    in if is_world then y else Const (\<^syntax_const>\<open>_AOT_valid\<close>, dummyT) $ w $ y end
  | [Const (\<^const_syntax>\<open>w\<^sub>0\<close>, _), y] => let
    val y = (Const (\<^syntax_const>\<open>_AOT_process_frees\<close>, dummyT) $ y)
    in case (AOT_ProofData.get ctxt) of SOME (Const (\<^const_name>\<open>w\<^sub>0\<close>, _)) => y | _ => Const (\<^syntax_const>\<open>_AOT_theorem\<close>, dummyT) $ y end
  | [Const ("_var", _) $ _, y] => let
    val y = (Const (\<^syntax_const>\<open>_AOT_process_frees\<close>, dummyT) $ y)
    in Const (\<^syntax_const>\<open>_AOT_nec_theorem\<close>, dummyT) $ y end
  ),
(\<^syntax_const>\<open>_AOT_process_frees\<close>, fn _ =>  fn [t] => let
  fun mapAppls (x as Const ("_free", _) $ Free (_, Type ("_ignore_type", [Type ("fun", _)]))) = (Const ("_AOT_raw_appl", dummyT) $ x)
    | mapAppls (x as Const ("_free", _) $ Free (_, Type ("fun", _))) = (Const ("_AOT_raw_appl", dummyT) $ x)
    | mapAppls (x as Const ("_var", _) $ Var (_, Type ("_ignore_type", [Type ("fun", _)]))) = (Const ("_AOT_raw_appl", dummyT) $ x)
    | mapAppls (x as Const ("_var", _) $ Var (_, Type ("fun", _))) = (Const ("_AOT_raw_appl", dummyT) $ x)
    | mapAppls (x $ y) = mapAppls x $ mapAppls y
    | mapAppls (Abs (x,y,z)) = Abs (x,y, mapAppls z)
    | mapAppls x = x
  in mapAppls t end
)
]
\<close>

print_ast_translation\<open>AOT_syntax_print_ast_translations
[(\<^const_syntax>\<open>AOT_term_of_var\<close>,
let
fun handleTermOfVar x kind name = (
let
val _ = case kind of "_free" => () | "_var" => () | "_bound" => () | _ => raise Match
fun splitFormulaParts x = x |> Symbol.explode |>
   Scan.finite Symbol.stopper (Scan.repeat (
  (Scan.one (Symbol.is_letter) --
  (((Scan.repeat ($$ "\<^sub>" -- (Scan.one (Symbol.is_digit)) >> (fn (x,y) => [x,y])) >> List.concat )
  -- (Scan.repeat ($$ "'"))) >> (fn (x,y) => x@y)))))
val isSingleVariableName = case (splitFormulaParts (Name.clean name)) of
        ([v],[]) => true | _ => false
in
  if isSingleVariableName
        then Ast.Appl [Ast.Constant "_constrain", Ast.Appl [Ast.Constant kind, Ast.Variable name], Ast.Variable name]
        else Ast.mk_appl (Ast.Constant "_AOT_quoted") [Ast.mk_appl (Ast.Constant "_AOT_term_of_var") [x]]
end
)
in
fn ctxt => fn [x as Ast.Appl [Ast.Constant "_constrain", Ast.Appl [Ast.Constant kind, Ast.Variable name], _]] => handleTermOfVar x kind name
| [x as Ast.Appl [Ast.Constant kind, Ast.Variable name]] => handleTermOfVar x kind name
end
),
("_AOT_raw_appl", fn _ => fn t::a::args => let
val ts = fold (fn a => fn b => Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_args\<close>) [b,a]) args a
in Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_appl\<close>) [t,ts] end)]
\<close>

context AOT_meta_syntax
begin
notation AOT_denotes ("_\<^bold>\<down>")
notation AOT_imp (infixl "\<^bold>\<rightarrow>" 25)
notation AOT_not ("\<^bold>\<not>_" [50] 50)
notation AOT_box ("\<^bold>\<box>_" [49] 54)
notation AOT_act ("\<^bold>\<A>_" [49] 54)
notation AOT_forall (binder "\<^bold>\<forall>" 8)
notation AOT_eq (infixl "\<^bold>=" 50)
notation AOT_desc (binder "\<^bold>\<iota>" 100)
notation AOT_lambda (binder "\<^bold>\<lambda>" 100)
notation AOT_lambda0 ("\<^bold>[\<^bold>\<lambda> _\<^bold>]")
notation AOT_exe ("\<^bold>\<lparr>_,_\<^bold>\<rparr>")
notation AOT_model_equiv_def (infixl "\<^bold>\<equiv>\<^sub>d\<^sub>f" 10)
notation AOT_model_id_def (infixl "\<^bold>=\<^sub>d\<^sub>f" 10)
notation AOT_term_of_var ("\<^bold>\<langle>_\<^bold>\<rangle>")
notation AOT_concrete ("\<^bold>E\<^bold>!")
end
context AOT_no_meta_syntax
begin
no_notation AOT_denotes ("_\<^bold>\<down>")
no_notation AOT_imp (infixl "\<^bold>\<rightarrow>" 25)
no_notation AOT_not ("\<^bold>\<not>_" [50] 50)
no_notation AOT_box ("\<^bold>\<box>_" [49] 54)
no_notation AOT_act ("\<^bold>\<A>_" [49] 54)
no_notation AOT_forall (binder "\<^bold>\<forall>" 8)
no_notation AOT_eq (infixl "\<^bold>=" 50)
no_notation AOT_desc (binder "\<^bold>\<iota>" 100)
no_notation AOT_lambda (binder "\<^bold>\<lambda>" 100)
no_notation AOT_lambda0 ("\<^bold>[\<^bold>\<lambda> _\<^bold>]")
no_notation AOT_exe ("\<^bold>\<lparr>_,_\<^bold>\<rparr>")
no_notation AOT_model_equiv_def (infixl "\<^bold>\<equiv>\<^sub>d\<^sub>f" 10)
no_notation AOT_model_id_def (infixl "\<^bold>=\<^sub>d\<^sub>f" 10)
no_notation AOT_term_of_var ("\<^bold>\<langle>_\<^bold>\<rangle>")
no_notation AOT_concrete ("\<^bold>E\<^bold>!")
end


(* TODO for AOT syntax printing mode (not exhaustive):

\<equiv>\<^sub>d\<^sub>f; =\<^sub>d\<^sub>f ; sth \<^bold>\<turnstile> sth ; sth \<^bold>\<turnstile>\<^sub>\<box> sth ; INSTANCE_OF_CQT_2 ; ellipses; invalid term names ; cqt_2_const_var[axiom_inst];

\<And>v \<tau> \<tau>'. [v \<Turnstile> \<tau> = \<tau>' \<rightarrow> \<tau>'\<down>] (additional Pure.all quantified variables)

parentheses around \<forall> body

exemplification/encoding/lambda tuples

 *)

bundle AOT_syntax
begin
declare[[show_AOT_syntax=true, show_question_marks=false]]
end

bundle AOT_no_syntax
begin
declare[[show_AOT_syntax=false, show_question_marks=true]]
end

parse_translation\<open>
[("_AOT_restriction", fn ctxt => fn [Const (name,_)] =>
let
val (restr, ctxt) = Local_Theory.raw_theory_result (fn thy => (Option.map fst (Symtab.lookup (AOT_Restriction.get thy) name), thy)) ctxt
val restr = case restr of SOME x => x | _ => raise Fail ("Unknown restricted type: " ^ name)
in restr end
)]
\<close>

print_translation \<open>
AOT_syntax_print_translations [
(\<^const_syntax>\<open>AOT_exe\<close>, fn ctxt => fn [R, Const (\<^const_syntax>\<open>Pair\<close>, _) $ a $ b] => (
Const (\<^const_syntax>\<open>AOT_exe\<close>, dummyT) $ R $ (Const (\<^syntax_const>\<open>_AOT_exe_args\<close>, dummyT) $ a $ b))
)]\<close>

(*<*)
end
(*>*)
