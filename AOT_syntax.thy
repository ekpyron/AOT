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

nonterminal \<kappa>\<^sub>s and \<Pi> and \<Pi>0 and \<alpha> and exe_arg and exe_args
        and lambda_args and desc and free_var and free_vars
        and AOT_props and AOT_premises and AOT_world_relative_prop

syntax "_AOT_process_frees" :: \<open>\<phi> \<Rightarrow> \<phi>'\<close> ("_")
       "_AOT_verbatim" :: \<open>any \<Rightarrow> \<phi>\<close> (\<open>\<guillemotleft>_\<guillemotright>\<close>)
       "_AOT_verbatim" :: \<open>any \<Rightarrow> \<tau>\<close> (\<open>\<guillemotleft>_\<guillemotright>\<close>)
       "_AOT_quoted" :: \<open>\<phi>' \<Rightarrow> any\<close> (\<open>\<guillemotleft>_\<guillemotright>\<close>)
       "_AOT_quoted" :: \<open>\<tau>' \<Rightarrow> any\<close> (\<open>\<guillemotleft>_\<guillemotright>\<close>)
       "" :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>'(_')\<close>)
       "_AOT_process_frees" :: \<open>\<tau> \<Rightarrow> \<tau>'\<close> ("_")
       "" :: \<open>\<kappa>\<^sub>s \<Rightarrow> \<tau>\<close> ("_")
       "" :: \<open>\<Pi> \<Rightarrow> \<tau>\<close> ("_")
       "" :: \<open>\<phi> \<Rightarrow> \<tau>\<close> ("'(_')")
       "_AOT_term_var" :: \<open>id_position \<Rightarrow> \<tau>\<close> ("_")
       "_AOT_term_var" :: \<open>id_position \<Rightarrow> \<phi>\<close> ("_")
       "_AOT_exe_vars" :: \<open>id_position \<Rightarrow> exe_arg\<close> ("_")
       "_AOT_lambda_vars" :: \<open>id_position \<Rightarrow> lambda_args\<close> ("_")
       "_AOT_var" :: \<open>id_position \<Rightarrow> \<alpha>\<close> ("_")
       "_AOT_vars" :: \<open>id_position \<Rightarrow> any\<close>
       "_AOT_verbatim" :: \<open>any \<Rightarrow> \<alpha>\<close> (\<open>\<guillemotleft>_\<guillemotright>\<close>)
       "_AOT_valid" :: \<open>w \<Rightarrow> \<phi>' \<Rightarrow> bool\<close> (\<open>[_ \<Turnstile> _]\<close>)
       "_AOT_denotes" :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>_\<down>\<close>)
       "_AOT_imp" :: \<open>[\<phi>, \<phi>] \<Rightarrow> \<phi>\<close> (infixl \<open>\<rightarrow>\<close> 25)
       "_AOT_not" :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>~_\<close> [50] 50)
       "_AOT_not" :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>\<not>_\<close> [50] 50)
       "_AOT_box" :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>\<box>_\<close> [49] 54)
       "_AOT_act" :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>\<^bold>\<A>_\<close> [49] 54)
       "_AOT_all" :: \<open>\<alpha> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (\<open>\<forall>_ _\<close> [1,40])
       "_AOT_all_ellipse"
            :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (\<open>\<forall>_...\<forall>_ _\<close> [1,40])
       "_AOT_eq" :: \<open>[\<tau>, \<tau>] \<Rightarrow> \<phi>\<close> (infixl \<open>=\<close> 50)
       "_AOT_desc" :: \<open>\<alpha> \<Rightarrow> \<phi> \<Rightarrow> desc\<close> ("\<^bold>\<iota>__" [1,1000])
       "" :: \<open>desc \<Rightarrow> \<kappa>\<^sub>s\<close> ("_")
       "_AOT_lambda" :: \<open>lambda_args \<Rightarrow> \<phi> \<Rightarrow> \<Pi>\<close> (\<open>[\<lambda>_ _]\<close>)
       "_explicitRelation" :: \<open>\<tau> \<Rightarrow> \<Pi>\<close> ("[_]")
       "" :: \<open>\<kappa>\<^sub>s \<Rightarrow> exe_arg\<close> ("_")
       "" :: \<open>exe_arg \<Rightarrow> exe_args\<close> ("_")
       "_AOT_exe_args" :: \<open>exe_arg \<Rightarrow> exe_args \<Rightarrow> exe_args\<close> ("__")
       "_AOT_exe_arg_ellipse" :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> exe_arg\<close> ("_..._")
       "_AOT_lambda_arg_ellipse"
            :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> lambda_args\<close> ("_..._")
       "_AOT_term_ellipse" :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> \<tau>\<close> ("_..._")
       "_AOT_exe" :: \<open>\<Pi> \<Rightarrow> exe_args \<Rightarrow> \<phi>\<close> (\<open>__\<close>)
       "_AOT_enc" :: \<open>exe_args \<Rightarrow> \<Pi> \<Rightarrow> \<phi>\<close> (\<open>__\<close>)
       "_AOT_lambda0" :: \<open>\<phi> \<Rightarrow> \<Pi>0\<close> (\<open>[\<lambda> _]\<close>)
       "" :: \<open>\<Pi>0 \<Rightarrow> \<phi>\<close> ("_")
       "" :: \<open>\<Pi>0 \<Rightarrow> \<tau>\<close> ("_")
       "_AOT_concrete" :: \<open>\<Pi>\<close> (\<open>E!\<close>)
       "" :: \<open>any \<Rightarrow> exe_arg\<close> ("\<guillemotleft>_\<guillemotright>")
       "" :: \<open>desc \<Rightarrow> free_var\<close> ("_")
       "" :: \<open>\<Pi> \<Rightarrow> free_var\<close> ("_")
       "_AOT_appl" :: \<open>id_position \<Rightarrow> free_vars \<Rightarrow> \<phi>\<close> ("_'{_'}")
       "_AOT_appl" :: \<open>id_position \<Rightarrow> free_vars \<Rightarrow> \<tau>\<close> ("_'{_'}")
       "_AOT_appl" :: \<open>id_position \<Rightarrow> free_vars \<Rightarrow> free_vars\<close> ("_'{_'}")
       "_AOT_appl" :: \<open>id_position \<Rightarrow> free_vars \<Rightarrow> free_vars\<close> ("_'{_'}")
       "_AOT_term_var" :: \<open>id_position \<Rightarrow> free_var\<close> ("_")
       "" :: \<open>any \<Rightarrow> free_var\<close> ("\<guillemotleft>_\<guillemotright>")
       "" :: \<open>free_var \<Rightarrow> free_vars\<close> ("_")
       "_AOT_args" :: \<open>free_var \<Rightarrow> free_vars \<Rightarrow> free_vars\<close> ("_,_")
       "_AOT_free_var_ellipse" :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> free_var\<close> ("_..._")
syntax "_AOT_premises"
            :: \<open>AOT_world_relative_prop \<Rightarrow> AOT_premises \<Rightarrow> AOT_premises\<close> (infixr \<open>,\<close> 3)
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
       "_AOT_for_arbitrary"
            :: \<open>id_position \<Rightarrow> AOT_prop \<Rightarrow> AOT_prop\<close> (\<open>for arbitrary _: _\<close> [1000,1] 1)
syntax (output) "_lambda_args" :: \<open>any \<Rightarrow> patterns \<Rightarrow> patterns\<close> ("__")

translations
  "[w \<Turnstile> \<phi>]" => "CONST AOT_model_valid_in w \<phi>"

AOT_syntax_print_translations
  "[w \<Turnstile> \<phi>]" <= "CONST AOT_model_valid_in w \<phi>"

ML_file AOT_syntax.ML

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

parse_ast_translation\<open>[
  (\<^syntax_const>\<open>_AOT_var\<close>, K AOT_check_var),
  (\<^syntax_const>\<open>_AOT_exe_vars\<close>, K AOT_split_exe_vars),
  (\<^syntax_const>\<open>_AOT_lambda_vars\<close>, K AOT_split_lambda_args)
]\<close>

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
  "_AOT_lambda (_lambda_args x y) \<phi>" <= "CONST AOT_lambda (_abs (_pattern x y) \<phi>)"
  "_AOT_lambda (_lambda_args x y) \<phi>" <= "CONST AOT_lambda (_abs (_patterns x y) \<phi>)"
  "_AOT_lambda x \<phi>" <= "CONST AOT_lambda (_abs x \<phi>)"
  "_lambda_args x (_lambda_args y z)" <= "_lambda_args x (_patterns y z)"
  "_lambda_args (x y z)" <= "_lambda_args (_tuple x (_tuple_arg (_tuple y z)))"


AOT_syntax_print_translations
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

translations
  "_AOT_appl \<phi> (_AOT_args a b)" => "_AOT_appl (\<phi> a) b"
  "_AOT_appl \<phi> a" => "\<phi> a"


parse_translation\<open>
[
  (\<^syntax_const>\<open>_AOT_var\<close>, parseVar true),
  (\<^syntax_const>\<open>_AOT_vars\<close>, parseVar false),
  (\<^syntax_const>\<open>_AOT_valid\<close>, fn ctxt => fn [w,x] =>
    \<^const>\<open>AOT_model_valid_in\<close> $ w $ x),
  (\<^syntax_const>\<open>_AOT_quoted\<close>, fn ctxt => fn [x] => x),
  (\<^syntax_const>\<open>_AOT_process_frees\<close>, fn ctxt => fn [x] => processFrees ctxt x),
  (\<^syntax_const>\<open>_AOT_world_relative_prop\<close>, fn ctxt => fn [x] => let
    val (x, premises) = processFreesAndPremises ctxt x
    val (world::formulas) = Variable.variant_frees ctxt [x]
        (("v", dummyT)::(map (fn _ => ("\<phi>", dummyT)) premises))
    val term = HOLogic.mk_Trueprop
        (@{const AOT_model_valid_in} $ Free world $ processFrees ctxt x)
    val term = fold (fn (premise,form) => fn trm =>
         @{const "Pure.imp"} $
        HOLogic.mk_Trueprop
          (Const (\<^const_name>\<open>Set.member\<close>, dummyT) $ Free form $ premise) $
          (Term.absfree (Term.dest_Free (dropConstraints premise)) trm $ Free form)
    ) (ListPair.zipEq (premises,formulas)) term
    val term = fold (fn (form) => fn trm =>
         Const (\<^const_name>\<open>Pure.all\<close>, dummyT) $
        (Term.absfree form trm)
    ) formulas term
    val term = Term.absfree world term
    in term end),
  (\<^syntax_const>\<open>_AOT_prop\<close>, fn ctxt => fn [x] => let
    val world = case (AOT_ProofData.get ctxt) of SOME w => w
        | _ => raise Fail "Expected world to be stored in the proof state."
    in x $ world end),
  (\<^syntax_const>\<open>_AOT_theorem\<close>, fn ctxt => fn [x] =>
      HOLogic.mk_Trueprop (@{const AOT_model_valid_in} $ @{const w\<^sub>0} $ x)),
  (\<^syntax_const>\<open>_AOT_axiom\<close>, fn ctxt => fn [x] =>
      HOLogic.mk_Trueprop (@{const AOT_model_axiom} $ x)),
  (\<^syntax_const>\<open>_AOT_act_axiom\<close>, fn ctxt => fn [x] =>
      HOLogic.mk_Trueprop (@{const AOT_model_act_axiom} $ x)),
  (\<^syntax_const>\<open>_AOT_nec_theorem\<close>, fn ctxt => fn [trm] => let
    val world = singleton (Variable.variant_frees ctxt [trm]) ("v", @{typ w})
    val trm = HOLogic.mk_Trueprop (@{const AOT_model_valid_in} $ Free world $ trm)
    val trm = Term.absfree world trm
    val trm = Const (\<^const_name>\<open>Pure.all\<close>, dummyT) $ trm
    in trm end),
  (\<^syntax_const>\<open>_AOT_derivable\<close>, fn ctxt => fn [x,y] => let
    val world = case (AOT_ProofData.get ctxt) of SOME w => w
      | _ => raise Fail "Expected world to be stored in the proof state."
    in foldPremises world x y end),
  (\<^syntax_const>\<open>_AOT_nec_derivable\<close>, fn ctxt => fn [x,y] => let
    in Const (\<^const_name>\<open>Pure.all\<close>, dummyT) $
       Abs ("v", dummyT, foldPremises (Bound 0) x y) end),
  (\<^syntax_const>\<open>_AOT_for_arbitrary\<close>, fn ctxt => fn [_ $ var $ pos,trm] => let
    val trm = Const (\<^const_name>\<open>Pure.all\<close>, dummyT) $
        (Const ("_constrainAbs", dummyT) $ Term.absfree (Term.dest_Free var) trm $ pos)
    in trm end),
  (\<^syntax_const>\<open>_AOT_equiv_def\<close>, parseEquivDef),
  (\<^syntax_const>\<open>_AOT_exe\<close>, parseExe),
  (\<^syntax_const>\<open>_AOT_enc\<close>, parseEnc)
]
\<close>

parse_ast_translation\<open>
[
  (\<^syntax_const>\<open>_AOT_exe_arg_ellipse\<close>, parseEllipseList "_AOT_term_vars"),
  (\<^syntax_const>\<open>_AOT_lambda_arg_ellipse\<close>, parseEllipseList "_AOT_vars"),
  (\<^syntax_const>\<open>_AOT_free_var_ellipse\<close>, parseEllipseList "_AOT_term_vars"),
  (\<^syntax_const>\<open>_AOT_term_ellipse\<close>, parseEllipseList "_AOT_term_vars"),
  (\<^syntax_const>\<open>_AOT_all_ellipse\<close>, fn ctx => fn [a,b,c] =>
      Ast.mk_appl (Ast.Constant \<^const_name>\<open>AOT_forall\<close>) [
        Ast.mk_appl (Ast.Constant "_abs") [parseEllipseList "_AOT_vars" ctx [a,b],c]
      ]
  ) (* TODO: restricted variables in ellipse quantification *)
]
\<close>

syntax (output)
  "_AOT_individual_term" :: \<open>'a \<Rightarrow> tuple_args\<close> ("_")
  "_AOT_individual_terms" :: \<open>tuple_args \<Rightarrow> tuple_args \<Rightarrow> tuple_args\<close> ("__")
  "_AOT_relation_term" :: \<open>'a \<Rightarrow> \<Pi>\<close>
  "_AOT_any_term" :: \<open>'a \<Rightarrow> \<tau>\<close>


print_ast_translation\<open>AOT_syntax_print_ast_translations[
 (\<^syntax_const>\<open>_AOT_individual_term\<close>, AOT_print_individual_term),
 (\<^syntax_const>\<open>_AOT_relation_term\<close>, AOT_print_relation_term),
 (\<^syntax_const>\<open>_AOT_any_term\<close>, AOT_print_generic_term)
]\<close>

AOT_syntax_print_translations
  "_AOT_individual_terms (_AOT_individual_term x) (_AOT_individual_terms (_tuple y z))"
  <= "_AOT_individual_terms (_tuple x (_tuple_args y z))"
  "_AOT_individual_terms (_AOT_individual_term x) (_AOT_individual_term y)"
  <= "_AOT_individual_terms (_tuple x (_tuple_arg y))"
  "_AOT_individual_terms (_tuple x y)" <= "_AOT_individual_term (_tuple x y)"
  "_AOT_exe (_AOT_relation_term \<Pi>) (_AOT_individual_term \<kappa>)" <= "CONST AOT_exe \<Pi> \<kappa>"
  "_AOT_denotes (_AOT_any_term \<kappa>)" <= "CONST AOT_denotes \<kappa>"

AOT_define AOT_conj :: \<open>[\<phi>, \<phi>] \<Rightarrow> \<phi>\<close> (infixl \<open>&\<close> 35) \<open>\<phi> & \<psi> \<equiv>\<^sub>d\<^sub>f \<not>(\<phi> \<rightarrow> \<not>\<psi>)\<close>
declare "AOT_conj"[AOT del, AOT_defs del]
AOT_define AOT_disj :: \<open>[\<phi>, \<phi>] \<Rightarrow> \<phi>\<close> (infixl \<open>\<or>\<close> 35) \<open>\<phi> \<or> \<psi> \<equiv>\<^sub>d\<^sub>f \<not>\<phi> \<rightarrow> \<psi>\<close>
declare "AOT_disj"[AOT del, AOT_defs del]
AOT_define AOT_equiv :: \<open>[\<phi>, \<phi>] \<Rightarrow> \<phi>\<close> (infix \<open>\<equiv>\<close> 20) \<open>\<phi> \<equiv> \<psi> \<equiv>\<^sub>d\<^sub>f (\<phi> \<rightarrow> \<psi>) & (\<psi> \<rightarrow> \<phi>)\<close>
declare "AOT_equiv"[AOT del, AOT_defs del]
AOT_define AOT_dia :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>\<diamond>_\<close> [49] 54) \<open>\<diamond>\<phi> \<equiv>\<^sub>d\<^sub>f \<not>\<box>\<not>\<phi>\<close>
declare "AOT_dia"[AOT del, AOT_defs del]

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


print_translation \<open>
AOT_syntax_print_translations
 [
  AOT_preserve_binder_abs_tr'
    \<^const_syntax>\<open>AOT_forall\<close>
    \<^syntax_const>\<open>_AOT_all\<close>
    (\<^syntax_const>\<open>_AOT_all_ellipse\<close>, true)
    \<^const_name>\<open>AOT_imp\<close>,
  AOT_binder_trans @{theory} @{binding "AOT_forall_binder"} \<^syntax_const>\<open>_AOT_all\<close>,
  Syntax_Trans.preserve_binder_abs_tr'
    \<^const_syntax>\<open>AOT_desc\<close>
    \<^syntax_const>\<open>_AOT_desc\<close>,
  AOT_binder_trans @{theory} @{binding "AOT_desc_binder"} \<^syntax_const>\<open>_AOT_desc\<close>,
  AOT_preserve_binder_abs_tr'
    \<^const_syntax>\<open>AOT_lambda\<close>
    \<^syntax_const>\<open>_AOT_lambda\<close>
    (\<^syntax_const>\<open>_AOT_lambda_arg_ellipse\<close>, false)
    \<^const_name>\<open>undefined\<close>, (* TODO: constrained variables *)
  AOT_binder_trans
    @{theory}
    @{binding "AOT_lambda_binder"}
    \<^syntax_const>\<open>_AOT_lambda\<close>
 ]
\<close>

parse_translation\<open>
[(\<^syntax_const>\<open>_AOT_id_def\<close>, parseIdDef)]
\<close>

parse_ast_translation\<open>[
 (\<^syntax_const>\<open>_AOT_all\<close>,
  AOT_restricted_binder \<^const_name>\<open>AOT_forall\<close> \<^const_name>\<open>AOT_imp\<close>),
 (\<^syntax_const>\<open>_AOT_desc\<close>,
  AOT_restricted_binder \<^const_name>\<open>AOT_desc\<close> \<^const_name>\<open>AOT_conj\<close>)
]\<close>

AOT_define AOT_exists :: \<open>\<alpha> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> \<open>\<guillemotleft>AOT_exists \<phi>\<guillemotright> \<equiv>\<^sub>d\<^sub>f \<not>\<forall>\<alpha> \<not>\<phi>{\<alpha>}\<close>
declare AOT_exists[AOT del, AOT_defs del]
syntax "_AOT_exists" :: \<open>\<alpha> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> ("\<exists>_ _" [1,40])

AOT_syntax_print_translations
  "_AOT_exists \<alpha> \<phi>" <= "CONST AOT_exists (_abs \<alpha> \<phi>)"
  "_AOT_exists \<alpha> \<phi>" <= "CONST AOT_exists (\<lambda>\<alpha>. \<phi>)"

parse_ast_translation\<open>                              
[(\<^syntax_const>\<open>_AOT_exists\<close>,
  AOT_restricted_binder \<^const_name>\<open>AOT_exists\<close> \<^const_name>\<open>AOT_conj\<close>)]
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
  Ast.mk_appl (Ast.Constant "AOT_exists")
    [Ast.mk_appl (Ast.Constant "_abs") [parseEllipseList "_AOT_vars" ctx [a,b],c]])]\<close>
print_translation\<open>AOT_syntax_print_translations [
  AOT_preserve_binder_abs_tr'
    \<^const_syntax>\<open>AOT_exists\<close>
    \<^syntax_const>\<open>_AOT_exists\<close>
    (\<^syntax_const>\<open>_AOT_exists_ellipse\<close>,true) \<^const_name>\<open>AOT_conj\<close>,
  AOT_binder_trans
    @{theory}
    @{binding "AOT_exists_binder"}
    \<^syntax_const>\<open>_AOT_exists\<close>
]\<close>



syntax "_AOT_DDDOT" :: "\<phi>" ("...")
syntax "_AOT_DDDOT" :: "\<phi>" ("\<dots>")
parse_translation\<open>[(\<^syntax_const>\<open>_AOT_DDDOT\<close>, parseDDOT)]\<close>

(* TODO: experimental printing mode: *)


print_translation\<open>AOT_syntax_print_translations
[(\<^const_syntax>\<open>Pure.all\<close>, fn ctxt => fn [Abs (_, _,
  Const (\<^const_syntax>\<open>HOL.Trueprop\<close>, _) $
  (Const (\<^const_syntax>\<open>AOT_model_valid_in\<close>, _) $ Bound 0 $ y))] => let
    val y = (Const (\<^syntax_const>\<open>_AOT_process_frees\<close>, dummyT) $ y)
    in (Const (\<^syntax_const>\<open>_AOT_nec_theorem\<close>, dummyT) $ y) end
| [p as Abs (name, _,
  Const (\<^const_syntax>\<open>HOL.Trueprop\<close>, _) $
  (Const (\<^const_syntax>\<open>AOT_model_valid_in\<close>, _) $ w $ y))]
=> (Const (\<^syntax_const>\<open>_AOT_for_arbitrary\<close>, dummyT) $
    (Const ("_bound", dummyT) $ Free (name, dummyT)) $
    (Term.betapply (p, (Const ("_bound", dummyT) $ Free (name, dummyT)))))
),

 (\<^const_syntax>\<open>AOT_model_valid_in\<close>, fn ctxt =>
  fn [w as (Const ("_free", _) $ Free (v, _)), y] => let
    val is_world = (case (AOT_ProofData.get ctxt)
        of SOME (Free (w, _)) => Name.clean w = Name.clean v | _ => false)
    val y = (Const (\<^syntax_const>\<open>_AOT_process_frees\<close>, dummyT) $ y)
    in if is_world then y else Const (\<^syntax_const>\<open>_AOT_valid\<close>, dummyT) $ w $ y end
  | [Const (\<^const_syntax>\<open>w\<^sub>0\<close>, _), y] => let
    val y = (Const (\<^syntax_const>\<open>_AOT_process_frees\<close>, dummyT) $ y)
    in case (AOT_ProofData.get ctxt) of SOME (Const (\<^const_name>\<open>w\<^sub>0\<close>, _)) => y |
            _ => Const (\<^syntax_const>\<open>_AOT_theorem\<close>, dummyT) $ y end
  | [Const ("_var", _) $ _, y] => let
    val y = (Const (\<^syntax_const>\<open>_AOT_process_frees\<close>, dummyT) $ y)
    in Const (\<^syntax_const>\<open>_AOT_nec_theorem\<close>, dummyT) $ y end
  ),
 (\<^const_syntax>\<open>AOT_model_axiom\<close>, fn ctxt => fn [trm] =>
    Const (\<^syntax_const>\<open>_AOT_axiom\<close>, dummyT) $
    (Const (\<^syntax_const>\<open>_AOT_process_frees\<close>, dummyT) $ trm)),
 (\<^const_syntax>\<open>AOT_model_act_axiom\<close>, fn ctxt => fn [trm] =>
    Const (\<^syntax_const>\<open>_AOT_axiom\<close>, dummyT) $
    (Const (\<^syntax_const>\<open>_AOT_process_frees\<close>, dummyT) $ trm)),
(\<^syntax_const>\<open>_AOT_process_frees\<close>, fn _ =>  fn [t] => let
  fun mapAppls (x as Const ("_free", _) $
                     Free (_, Type ("_ignore_type", [Type ("fun", _)])))
        = (Const ("_AOT_raw_appl", dummyT) $ x)
    | mapAppls (x as Const ("_free", _) $ Free (_, Type ("fun", _)))
        = (Const ("_AOT_raw_appl", dummyT) $ x)
    | mapAppls (x as Const ("_var", _) $
                     Var (_, Type ("_ignore_type", [Type ("fun", _)])))
        = (Const ("_AOT_raw_appl", dummyT) $ x)
    | mapAppls (x as Const ("_var", _) $ Var (_, Type ("fun", _)))
        = (Const ("_AOT_raw_appl", dummyT) $ x)
    | mapAppls (x $ y) = mapAppls x $ mapAppls y
    | mapAppls (Abs (x,y,z)) = Abs (x,y, mapAppls z)
    | mapAppls x = x
  in mapAppls t end
)
]
\<close>

print_ast_translation\<open>AOT_syntax_print_ast_translations
let
fun handleTermOfVar x kind name = (
let
val _ = case kind of "_free" => () | "_var" => () | "_bound" => () | _ => raise Match
in
  case printVarKind name
    of (SingleVariable name) => Ast.Appl [Ast.Constant kind, Ast.Variable name]
    | (Ellipses (s, e)) =>  Ast.Appl [Ast.Constant "_AOT_free_var_ellipse",
    Ast.Appl [Ast.Constant kind, Ast.Variable s],
    Ast.Appl [Ast.Constant kind, Ast.Variable e]
      ]
  | Verbatim name => Ast.mk_appl (Ast.Constant "_AOT_quoted")
                        [Ast.mk_appl (Ast.Constant "_AOT_term_of_var") [x]]
end
)
fun termOfVar ctxt (Ast.Appl [Ast.Constant "_constrain",
      x as Ast.Appl [Ast.Constant kind, Ast.Variable name], _]) = termOfVar ctxt x
  | termOfVar ctxt (x as Ast.Appl [Ast.Constant kind, Ast.Variable name])
      = handleTermOfVar x kind name
  | termOfVar ctxt (x as Ast.Appl [Ast.Constant rep, y]) = (
let
val (restr,_) = Local_Theory.raw_theory_result (fn thy => (
let
val restrs = Symtab.dest (AOT_Restriction.get thy)
val restr = List.find (fn (n,(_,Const (c,t))) => (
  c = rep orelse c = Lexicon.unmark_const rep) | _ => false) restrs
in
(restr,thy)
end
)) ctxt
in
  case restr of SOME r => Ast.Appl [Ast.Constant (\<^const_syntax>\<open>AOT_term_of_var\<close>), y]
  | _ => raise Match
end)

in
[(\<^const_syntax>\<open>AOT_term_of_var\<close>, fn ctxt => fn [x] => termOfVar ctxt x),
("_AOT_raw_appl", fn ctxt => fn t::a::args => let
fun applyTermOfVar (t as Ast.Appl (Ast.Constant \<^const_syntax>\<open>AOT_term_of_var\<close>::[x]))
    = (case try (termOfVar ctxt) x of SOME y => y | _ => t)
  | applyTermOfVar y = (case try (termOfVar ctxt) y of SOME x => x | _ => y)
val ts = fold (fn a => fn b => Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_args\<close>)
              [b,applyTermOfVar a]) args (applyTermOfVar a)
in Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_appl\<close>) [t,ts] end)]
end
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

bundle AOT_syntax
begin
declare[[show_AOT_syntax=true, show_question_marks=false, eta_contract=false]]
end

bundle AOT_no_syntax
begin
declare[[show_AOT_syntax=false, show_question_marks=true]]
end

parse_translation\<open>
[("_AOT_restriction", fn ctxt => fn [Const (name,_)] =>
let
val (restr, ctxt) = ctxt |> Local_Theory.raw_theory_result
  (fn thy => (Option.map fst (Symtab.lookup (AOT_Restriction.get thy) name), thy))
val restr = case restr of SOME x => x
  | _ => raise Fail ("Unknown restricted type: " ^ name)
in restr end
)]
\<close>

print_translation\<open>
AOT_syntax_print_translations
[
(* TODO: restricted variables *)
  (\<^const_syntax>\<open>AOT_model_equiv_def\<close>, fn ctxt => fn [x,y] =>
    Const (\<^syntax_const>\<open>_AOT_equiv_def\<close>, dummyT) $
    (Const (\<^syntax_const>\<open>_AOT_process_frees\<close>, dummyT) $ x) $
    (Const (\<^syntax_const>\<open>_AOT_process_frees\<close>, dummyT) $ y))
]
\<close>

print_translation\<open>
AOT_syntax_print_translations [
(\<^const_syntax>\<open>AOT_model_id_def\<close>, fn ctxt =>
  fn [lhs as Abs (lhsName, lhsTy, lhsTrm), rhs as Abs (rhsName, rhsTy, rhsTrm)] =>
    let
      val (name,_) = Name.variant lhsName
        (Term.declare_term_names rhsTrm (Term.declare_term_names lhsTrm Name.context));
      val lhs = Term.betapply (lhs, Const ("_bound", dummyT) $ Free (name, lhsTy))
      val rhs = Term.betapply (rhs, Const ("_bound", dummyT) $ Free (name, rhsTy))
    in
      Const (\<^const_syntax>\<open>AOT_model_id_def\<close>, dummyT) $ lhs $ rhs
    end
  | [Const (\<^const_syntax>\<open>case_prod\<close>, _) $ lhs,
     Const (\<^const_syntax>\<open>case_prod\<close>, _) $ rhs] =>
    Const (\<^const_syntax>\<open>AOT_model_id_def\<close>, dummyT) $ lhs $ rhs
  | [Const (\<^const_syntax>\<open>case_unit\<close>, _) $ lhs,
      Const (\<^const_syntax>\<open>case_unit\<close>, _) $ rhs] =>
    Const (\<^const_syntax>\<open>AOT_model_id_def\<close>, dummyT) $ lhs $ rhs
  | [x, y] =>
       Const (\<^syntax_const>\<open>_AOT_id_def\<close>, dummyT) $
         (Const (\<^syntax_const>\<open>_AOT_process_frees\<close>, dummyT) $ x) $
         (Const (\<^syntax_const>\<open>_AOT_process_frees\<close>, dummyT) $ y)
)]\<close>

text\<open>Special marker for printing propositions as theorems
     and for pretty-printing AOT terms.\<close>
definition print_as_theorem :: \<open>\<o> \<Rightarrow> bool\<close> where
  \<open>print_as_theorem \<equiv> \<lambda> \<phi> . \<forall>v . [v \<Turnstile> \<phi>]\<close>
lemma print_as_theoremI:
  assumes \<open>\<And> v . [v \<Turnstile> \<phi>]\<close>
  shows \<open>print_as_theorem \<phi>\<close>
  using assms by (simp add: print_as_theorem_def)
attribute_setup print_as_theorem =
  \<open>Scan.succeed (Thm.rule_attribute []
      (K (fn thm => thm RS @{thm print_as_theoremI})))\<close>
  "Print as theorem."
print_translation\<open>AOT_syntax_print_translations [
  (\<^const_syntax>\<open>print_as_theorem\<close>, fn ctxt => fn [x] => 
   (Const (\<^syntax_const>\<open>_AOT_process_frees\<close>, dummyT) $ x))
]\<close>

definition print_term :: \<open>'a \<Rightarrow> 'a\<close> where \<open>print_term \<equiv> \<lambda> x . x\<close>
syntax "_AOT_print_term" :: \<open>\<tau> \<Rightarrow> 'a\<close> (\<open>AOT'_TERM[_]\<close>)
translations
  "_AOT_print_term \<phi>" => "CONST print_term (_AOT_process_frees \<phi>)"
print_translation\<open>AOT_syntax_print_translations [
  (\<^const_syntax>\<open>print_term\<close>, fn ctxt => fn [x] => 
    (Const (\<^syntax_const>\<open>_AOT_process_frees\<close>, dummyT) $ x))
]\<close>

(*<*)
end
(*>*)
