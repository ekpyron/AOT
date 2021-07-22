(*<*)
theory AOT_RestrictedVariables
  imports AOT_PLM
  keywords "AOT_register_rigid_restricted_type" :: thy_goal
       and "AOT_register_restricted_type" :: thy_goal
begin
(*>*)

section\<open>Restricted Variables\<close>

locale AOT_restriction_condition =
  fixes \<psi> :: \<open>'a::AOT_Term_id_2 \<Rightarrow> \<o>\<close>
  assumes "res-var:2"[AOT]: \<open>[v \<Turnstile> \<exists>\<alpha> \<psi>{\<alpha>}]\<close>
  assumes "res-var:3"[AOT]: \<open>[v \<Turnstile> \<psi>{\<tau>} \<rightarrow> \<tau>\<down>]\<close>

ML\<open>
fun register_restricted_type (name:string, restriction:string) thy =
let
val ctxt = thy
val ctxt = setupStrictWorld ctxt
val trm = Syntax.check_term ctxt (AOT_read_term @{nonterminal \<phi>'} ctxt restriction)
val free = case (Term.add_frees trm []) of [f] => f | _ => raise Term.TERM ("Expected single free variable.", [trm])
val trm = Term.absfree free trm
val localeTerm = Const (\<^const_name>\<open>AOT_restriction_condition\<close>, dummyT) $ trm
val localeTerm = Syntax.check_term ctxt localeTerm
fun after_qed thms thy = let
val st = Interpretation.global_interpretation (([(@{locale AOT_restriction_condition}, ((name, true),
           (Expression.Named [("\<psi>", trm)], [])))], [])) [] thy
val st = Proof.refine_insert (flat thms) st
val thy = Proof.global_immediate_proof st

val thy = Local_Theory.background_theory (AOT_Constraints.map (Symtab.update (name, (term_of (snd free), term_of (snd free))))) thy
val thy = Local_Theory.background_theory (AOT_Restriction.map (Symtab.update (name, (trm, Const (\<^const_name>\<open>AOT_term_of_var\<close>, dummyT))))) thy

in thy end
in
Proof.theorem NONE after_qed [[(HOLogic.mk_Trueprop localeTerm, [])]] ctxt
end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_register_restricted_type\<close> "Register a restricted type."
    (((Parse.short_ident --| Parse.$$$ ":") -- Parse.term) >> (Toplevel.local_theory_to_proof NONE NONE o register_restricted_type));

\<close>

locale AOT_rigid_restriction_condition = AOT_restriction_condition +
  assumes rigid_condition[AOT]: \<open>[v \<Turnstile> \<box>(\<psi>{\<alpha>} \<rightarrow> \<box>\<psi>{\<alpha>})]\<close>
begin
lemma type_set_nonempty[AOT_no_atp, no_atp]: \<open>\<exists>x . x \<in> { \<alpha> . [w\<^sub>0 \<Turnstile> \<psi>{\<alpha>}]}\<close>
  by (metis "instantiation" mem_Collect_eq "res-var:2")
end

locale AOT_restricted_type = AOT_rigid_restriction_condition +
  fixes Rep and Abs assumes AOT_restricted_type_definition[AOT_no_atp]: \<open>type_definition Rep Abs { \<alpha> . [w\<^sub>0 \<Turnstile> \<psi>{\<alpha>}]}\<close>
begin

AOT_theorem restricted_var_condition: \<open>\<psi>{\<guillemotleft>AOT_term_of_var (Rep \<alpha>)\<guillemotright>}\<close>
proof -
  interpret type_definition Rep Abs "{ \<alpha> . [w\<^sub>0 \<Turnstile> \<psi>{\<alpha>}]}"
    using AOT_restricted_type_definition.
  AOT_actually {
    AOT_have \<open>\<guillemotleft>AOT_term_of_var (Rep \<alpha>)\<guillemotright>\<down>\<close> and \<open>\<psi>{\<guillemotleft>AOT_term_of_var (Rep \<alpha>)\<guillemotright>}\<close>
      using AOT_sem_imp Rep "res-var:3" by auto
  }
  moreover AOT_actually {
    AOT_have \<open>\<psi>{\<alpha>} \<rightarrow> \<box>\<psi>{\<alpha>}\<close> for \<alpha>
      using AOT_sem_box rigid_condition by presburger
    AOT_hence \<open>\<psi>{\<tau>} \<rightarrow> \<box>\<psi>{\<tau>}\<close> if \<open>\<tau>\<down>\<close> for \<tau>
      by (metis AOT_model.AOT_term_of_var_cases AOT_sem_denotes that)
  }
  ultimately AOT_show \<open>\<psi>{\<guillemotleft>AOT_term_of_var (Rep \<alpha>)\<guillemotright>}\<close>
    using AOT_sem_box AOT_sem_imp by blast
qed
lemmas "\<psi>" = restricted_var_condition

AOT_theorem GEN: assumes \<open>for arbitrary \<alpha>: \<phi>{\<guillemotleft>AOT_term_of_var (Rep \<alpha>)\<guillemotright>}\<close>
  shows \<open>\<forall>\<alpha> (\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close>
proof(rule GEN; rule "\<rightarrow>I")
  interpret type_definition Rep Abs "{ \<alpha> . [w\<^sub>0 \<Turnstile> \<psi>{\<alpha>}]}"
    using AOT_restricted_type_definition.
  fix \<alpha>
  AOT_assume \<open>\<psi>{\<alpha>}\<close>
  AOT_hence \<open>\<^bold>\<A>\<psi>{\<alpha>}\<close>
    by (metis AOT_model_axiom_def AOT_sem_box AOT_sem_imp act_closure rigid_condition)
  hence 0: \<open>[w\<^sub>0 \<Turnstile> \<psi>{\<alpha>}]\<close> by (metis AOT_sem_act)
  {
    fix \<tau>
    assume \<alpha>_def: \<open>\<alpha> = Rep \<tau>\<close>
    AOT_have \<open>\<phi>{\<alpha>}\<close>
      unfolding \<alpha>_def
      using assms by blast
  }
  AOT_thus \<open>\<phi>{\<alpha>}\<close>
    using Rep_cases[simplified, OF 0]
    by blast
qed
lemmas "\<forall>I" = GEN

end


lemma AOT_restricted_type_intro[AOT_no_atp, no_atp]:
  assumes \<open>type_definition Rep Abs { \<alpha> . [w\<^sub>0 \<Turnstile> \<psi>{\<alpha>}]}\<close> and \<open>AOT_rigid_restriction_condition \<psi>\<close>
  shows \<open>AOT_restricted_type \<psi> Rep Abs\<close>
  by (auto intro!: assms AOT_restricted_type_axioms.intro AOT_restricted_type.intro)



ML\<open>
fun register_rigid_restricted_type (name:string, restriction:string) thy =
let
val ctxt = thy
val ctxt = setupStrictWorld ctxt
val trm = Syntax.check_term ctxt (AOT_read_term @{nonterminal \<phi>'} ctxt restriction)
val free = case (Term.add_frees trm []) of [f] => f | _ => raise Term.TERM ("Expected single free variable.", [trm])
val trm = Term.absfree free trm
val localeTerm = HOLogic.mk_Trueprop (Const (\<^const_name>\<open>AOT_rigid_restriction_condition\<close>, dummyT) $ trm)
val localeTerm = Syntax.check_prop ctxt localeTerm
val int_bnd = Binding.concealed (Binding.qualify true "internal" (Binding.name name))
val bnds = {Rep_name = Binding.qualify true name (Binding.name "Rep"),
            Abs_name = Binding.qualify true "Abs" int_bnd,
            type_definition_name = Binding.qualify true "type_definition" int_bnd}

fun after_qed witts thy = let
  val thms = (map (Element.conclude_witness ctxt) (flat witts))
  
  val typeset = HOLogic.mk_Collect ("\<alpha>", dummyT, \<^const>\<open>AOT_model_valid_in\<close> $ \<^const>\<open>w\<^sub>0\<close> $ (trm $ (Const (\<^const_name>\<open>AOT_term_of_var\<close>, dummyT) $ Bound 0)))
  val typeset = Syntax.check_term thy typeset
  val nonempty_thm = Drule.OF (@{thm AOT_rigid_restriction_condition.type_set_nonempty}, thms)

  val ((_,st),thy) = Typedef.add_typedef {overloaded=true} (Binding.name name, [], Mixfix.NoSyn) typeset (SOME bnds)
    (fn ctxt => (Tactic.resolve_tac ctxt ([nonempty_thm]) 1)) thy
  val ({rep_type = _, abs_type = _, Rep_name = Rep_name, Abs_name = Abs_name, axiom_name = _},
     {inhabited = _, type_definition = type_definition, Rep = _, Rep_inverse = _, Abs_inverse = _,
      Rep_inject = _, Abs_inject = _, Rep_cases = _, Abs_cases = _,
      Rep_induct = _, Abs_induct = _}) = st

  val locale_thm = Drule.OF (@{thm AOT_restricted_type_intro}, type_definition::thms)

  val st = Interpretation.global_interpretation (([(@{locale AOT_restricted_type}, ((name, true),
             (Expression.Named [("\<psi>", trm), ("Rep", Const (Rep_name, dummyT)), ("Abs", Const (Abs_name, dummyT))], [])))], [])) [] thy

  val st = Proof.refine_insert [locale_thm] st
  val thy = Proof.global_immediate_proof st

  val thy = Local_Theory.background_theory (AOT_Constraints.map (Symtab.update (name, (term_of (snd free), term_of (snd free))))) thy
  val thy = Local_Theory.background_theory (AOT_Restriction.map (Symtab.update (name, (trm, Const (Rep_name, dummyT))))) thy
  
  in thy end
in
Element.witness_proof after_qed [[localeTerm]] thy
end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_register_rigid_restricted_type\<close> "Register a restricted type."
    (((Parse.short_ident --| Parse.$$$ ":") -- Parse.term) >> (Toplevel.local_theory_to_proof NONE NONE o register_rigid_restricted_type)); 
\<close>

(* Generalized mechanism for "AOT_restricted_type.\<forall>I" followed by \<forall>E *)
ML\<open>
fun get_instantiated_allI ctxt varname thm = let
val trm = Thm.concl_of thm
val trm = case trm of (@{const Trueprop} $ (@{const AOT_model_valid_in} $ _ $ x)) => x
                      | _ => raise Term.TERM ("Expected simple theorem.", [trm])
fun extractVars (Const (\<^const_name>\<open>AOT_term_of_var\<close>, t) $ (Const rep $ Var v)) =
    (if fst (fst v) = fst varname then [Const (\<^const_name>\<open>AOT_term_of_var\<close>, t) $ (Const rep $ Var v)] else []) (* TODO: care about the index? *)
  | extractVars (t1 $ t2) = extractVars t1 @ extractVars t2
  | extractVars (Abs (_, _, t)) = extractVars t
  | extractVars _ = []
val vars = extractVars trm
val vartrm = hd vars
val vars = fold Term.add_vars vars []
val var = hd vars
val trmty = (case vartrm of (Const (_, Type ("fun", [_, ty])) $ _) => ty | _ => raise Match)
val varty = snd var
val tyname = fst (Term.dest_Type varty)
val b = tyname^".\<forall>I" (* TODO: better way to find the theorem *)
val thms = fst (Context.map_proof_result (fn ctxt => (Attrib.eval_thms ctxt [(Facts.Named ((b,Position.none),NONE),[])], ctxt)) ctxt)
val allthm = (case thms of (thm::_) => thm | _ => raise Fail "Unknown restricted type.")
val trm = Abs (Term.string_of_vname (fst var), trmty, Term.abstract_over (vartrm, trm))
val trm = Thm.cterm_of (Context.proof_of ctxt) trm
val phi = hd (Term.add_vars (Thm.prop_of allthm) [])
val allthm = Drule.instantiate_normalize ([],[(phi,trm)]) allthm
in
allthm
end
\<close>

(* TODO: unconstraining multiple variables does not work yet *)
attribute_setup "unconstrain" =
  \<open>Scan.lift (Scan.repeat1 Args.var) >> (fn args => Thm.rule_attribute []
  (fn ctxt => fn thm =>
    let
    val thm = fold (fn arg => fn thm => thm RS get_instantiated_allI ctxt arg thm) args thm
    val thm = fold (fn _ => fn thm => thm RS @{thm "\<forall>E"(2)}) args thm
    in
     thm
    end))\<close>
  "Generalize a statement about restricted variables to a statement about unrestricted variables with explicit restriction condition."



context AOT_restricted_type
begin

AOT_theorem "rule-ui":
  assumes \<open>\<forall>\<alpha>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close>
  shows \<open>\<phi>{\<guillemotleft>AOT_term_of_var (Rep \<alpha>)\<guillemotright>}\<close>
proof -
  AOT_have \<open>\<phi>{\<alpha>}\<close> if \<open>\<psi>{\<alpha>}\<close> for \<alpha> using assms[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] that by blast
  moreover AOT_have \<open>\<psi>{\<guillemotleft>AOT_term_of_var (Rep \<alpha>)\<guillemotright>}\<close>
    by (auto simp:  \<psi>)
  ultimately show ?thesis by blast
qed
lemmas "\<forall>E" = "rule-ui"

AOT_theorem "instantiation":
  assumes \<open>for arbitrary \<beta>: \<phi>{\<guillemotleft>AOT_term_of_var (Rep \<beta>)\<guillemotright>} \<^bold>\<turnstile> \<chi>\<close> and \<open>\<exists>\<alpha> (\<psi>{\<alpha>} & \<phi>{\<alpha>})\<close>
  shows \<open>\<chi>\<close>
proof -
  AOT_have \<open>\<phi>{\<guillemotleft>AOT_term_of_var (Rep \<alpha>)\<guillemotright>} \<rightarrow> \<chi>\<close> for \<alpha>
    using assms(1)
    by (simp add: "deduction-theorem")
  AOT_hence 0: \<open>\<forall>\<alpha> (\<psi>{\<alpha>} \<rightarrow> (\<phi>{\<alpha>} \<rightarrow> \<chi>))\<close>
    using GEN by simp
  moreover AOT_obtain \<alpha> where \<open>\<psi>{\<alpha>} & \<phi>{\<alpha>}\<close> using assms(2) "\<exists>E"[rotated] by blast
  ultimately AOT_show \<open>\<chi>\<close> using "AOT_PLM.\<forall>E"(2)[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "&E" by fast
qed
lemmas "\<exists>E" = "instantiation"

AOT_theorem existential: assumes \<open>\<phi>{\<guillemotleft>AOT_term_of_var (Rep \<beta>)\<guillemotright>}\<close>
  shows \<open>\<exists> \<alpha> (\<psi>{\<alpha>} & \<phi>{\<alpha>})\<close>
  by (meson AOT_restricted_type.\<psi> AOT_restricted_type_axioms assms "&I" "existential:2[const_var]")
lemmas "\<exists>I" = existential
end


context AOT_rigid_restriction_condition
begin

AOT_theorem "res-var-bound-reas[1]": \<open>\<forall>\<alpha>(\<psi>{\<alpha>} \<rightarrow> \<forall>\<beta> \<phi>{\<alpha>, \<beta>}) \<equiv> \<forall>\<beta>\<forall>\<alpha> (\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>, \<beta>})\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I" GEN)
  fix \<beta> \<alpha>
  AOT_assume \<open>\<forall>\<alpha> (\<psi>{\<alpha>} \<rightarrow> \<forall>\<beta> \<phi>{\<alpha>, \<beta>})\<close>
  AOT_hence \<open>\<psi>{\<alpha>} \<rightarrow> \<forall>\<beta> \<phi>{\<alpha>, \<beta>}\<close> using "\<forall>E"(2) by blast
  moreover AOT_assume \<open>\<psi>{\<alpha>}\<close>
  ultimately AOT_have \<open>\<forall>\<beta> \<phi>{\<alpha>, \<beta>}\<close> using "\<rightarrow>E" by blast
  AOT_thus \<open>\<phi>{\<alpha>, \<beta>}\<close> using "\<forall>E"(2) by blast
next
  fix \<alpha> \<beta>
  AOT_assume \<open>\<forall>\<beta>\<forall>\<alpha>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>, \<beta>})\<close>
  AOT_hence \<open>\<forall>\<alpha>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>, \<beta>})\<close> using "\<forall>E"(2) by blast
  AOT_hence \<open>\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>, \<beta>}\<close> using "\<forall>E"(2) by blast
  moreover AOT_assume \<open>\<psi>{\<alpha>}\<close>
  ultimately AOT_show \<open>\<phi>{\<alpha>, \<beta>}\<close> using "\<rightarrow>E" by blast
qed

(* TODO: PLM: easier proof with lemmas above *)
AOT_theorem "res-var-bound-reas[BF]": \<open>\<forall>\<alpha>(\<psi>{\<alpha>} \<rightarrow> \<box>\<phi>{\<alpha>}) \<rightarrow> \<box>\<forall>\<alpha>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_assume \<open>\<forall>\<alpha>(\<psi>{\<alpha>} \<rightarrow> \<box>\<phi>{\<alpha>})\<close>
  AOT_hence \<open>\<psi>{\<alpha>} \<rightarrow> \<box>\<phi>{\<alpha>}\<close> for \<alpha> using "\<forall>E"(2) by blast
  AOT_hence \<open>\<box>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close> for \<alpha> by (metis "sc-eq-box-box:6" rigid_condition "vdash-properties:6")
  AOT_hence \<open>\<forall>\<alpha> \<box>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close> by (rule GEN)
  AOT_thus \<open>\<box>\<forall>\<alpha> (\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close> by (metis "BF" "vdash-properties:6")
qed

AOT_theorem "res-var-bound-reas[CBF]": \<open>\<box>\<forall>\<alpha>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>}) \<rightarrow> \<forall>\<alpha>(\<psi>{\<alpha>} \<rightarrow> \<box>\<phi>{\<alpha>})\<close>
proof(safe intro!: "\<rightarrow>I" GEN)
  fix \<alpha>
  AOT_assume \<open>\<box>\<forall>\<alpha> (\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close>
  AOT_hence \<open>\<forall>\<alpha> \<box>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close> by (metis "CBF" "vdash-properties:6")
  AOT_hence 1: \<open>\<box>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close> using "\<forall>E"(2) by blast
  AOT_assume \<open>\<psi>{\<alpha>}\<close>
  AOT_hence \<open>\<box>\<psi>{\<alpha>}\<close>
    by (metis "B\<diamond>" "T\<diamond>" rigid_condition "vdash-properties:6")
  AOT_thus \<open>\<box>\<phi>{\<alpha>}\<close> using 1 "qml:1"[axiom_inst, THEN "\<rightarrow>E", THEN "\<rightarrow>E"] by blast
qed

AOT_theorem "res-var-bound-reas[2]": \<open>\<forall>\<alpha> (\<psi>{\<alpha>} \<rightarrow> \<^bold>\<A>\<phi>{\<alpha>}) \<rightarrow> \<^bold>\<A>\<forall>\<alpha> (\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_assume \<open>\<forall>\<alpha> (\<psi>{\<alpha>} \<rightarrow> \<^bold>\<A>\<phi>{\<alpha>})\<close>
  AOT_hence \<open>\<psi>{\<alpha>} \<rightarrow> \<^bold>\<A>\<phi>{\<alpha>}\<close> for \<alpha> using "\<forall>E"(2) by blast
  AOT_hence \<open>\<^bold>\<A>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close> for \<alpha> by (metis "sc-eq-box-box:7" rigid_condition "vdash-properties:6")
  AOT_hence \<open>\<forall>\<alpha> \<^bold>\<A>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close> by (rule GEN)
  AOT_thus \<open>\<^bold>\<A>\<forall>\<alpha>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close> by (metis "\<equiv>E"(2) "logic-actual-nec:3" "vdash-properties:1[2]")
qed


AOT_theorem "res-var-bound-reas[3]": \<open>\<^bold>\<A>\<forall>\<alpha> (\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>}) \<rightarrow> \<forall>\<alpha> (\<psi>{\<alpha>} \<rightarrow> \<^bold>\<A>\<phi>{\<alpha>})\<close>
proof(safe intro!: "\<rightarrow>I" GEN)
  fix \<alpha>
  AOT_assume \<open>\<^bold>\<A>\<forall>\<alpha> (\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close>
  AOT_hence \<open>\<forall>\<alpha> \<^bold>\<A>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close>
    by (metis "\<equiv>E"(1) "logic-actual-nec:3" "vdash-properties:1[2]")
  AOT_hence 1: \<open>\<^bold>\<A>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close> by (metis "rule-ui:3")
  AOT_assume \<open>\<psi>{\<alpha>}\<close>
  AOT_hence \<open>\<^bold>\<A>\<psi>{\<alpha>}\<close> by (metis "nec-imp-act" "qml:2" rigid_condition "vdash-properties:1[2]" "vdash-properties:6")
  AOT_thus \<open>\<^bold>\<A>\<phi>{\<alpha>}\<close> using 1 by (metis "act-cond" "vdash-properties:6")
qed

AOT_theorem "res-var-bound-reas[Buridan]": \<open>\<exists>\<alpha> (\<psi>{\<alpha>} & \<box>\<phi>{\<alpha>}) \<rightarrow> \<box>\<exists>\<alpha> (\<psi>{\<alpha>} & \<phi>{\<alpha>})\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>\<exists>\<alpha> (\<psi>{\<alpha>} & \<box>\<phi>{\<alpha>})\<close>
  then AOT_obtain \<alpha> where \<open>\<psi>{\<alpha>} & \<box>\<phi>{\<alpha>}\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<open>\<box>(\<psi>{\<alpha>} & \<phi>{\<alpha>})\<close> 
    by (metis "KBasic:11" "KBasic:3" "T\<diamond>" "&I" "&E"(1) "&E"(2)
              "\<equiv>E"(2) "reductio-aa:1" rigid_condition "vdash-properties:6")
  AOT_hence \<open>\<exists>\<alpha> \<box>(\<psi>{\<alpha>} & \<phi>{\<alpha>})\<close> by (rule "\<exists>I")
  AOT_thus \<open>\<box>\<exists>\<alpha> (\<psi>{\<alpha>} & \<phi>{\<alpha>})\<close> by (rule Buridan[THEN "\<rightarrow>E"])
qed

AOT_theorem "res-var-bound-reas[BF\<diamond>]": \<open>\<diamond>\<exists>\<alpha> (\<psi>{\<alpha>} & \<phi>{\<alpha>}) \<rightarrow> \<exists>\<alpha> (\<psi>{\<alpha>} & \<diamond>\<phi>{\<alpha>})\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<diamond>\<exists>\<alpha> (\<psi>{\<alpha>} & \<phi>{\<alpha>})\<close>
  AOT_hence \<open>\<exists>\<alpha> \<diamond>(\<psi>{\<alpha>} & \<phi>{\<alpha>})\<close>
    using "BF\<diamond>"[THEN "\<rightarrow>E"] by blast
  then AOT_obtain \<alpha> where \<open>\<diamond>(\<psi>{\<alpha>} & \<phi>{\<alpha>})\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<open>\<diamond>\<psi>{\<alpha>}\<close> and \<open>\<diamond>\<phi>{\<alpha>}\<close>
    using "KBasic2:3" "&E" "vdash-properties:10" by blast+
  moreover AOT_have \<open>\<psi>{\<alpha>}\<close> using calculation rigid_condition by (metis "B\<diamond>" "K\<diamond>" "vdash-properties:10")
  ultimately AOT_have \<open>\<psi>{\<alpha>} & \<diamond>\<phi>{\<alpha>}\<close> using "&I" by blast
  AOT_thus \<open>\<exists>\<alpha> (\<psi>{\<alpha>} & \<diamond>\<phi>{\<alpha>})\<close>
    by (rule "\<exists>I")
qed

AOT_theorem "res-var-bound-reas[CBF\<diamond>]": \<open>\<exists>\<alpha> (\<psi>{\<alpha>} & \<diamond>\<phi>{\<alpha>}) \<rightarrow> \<diamond>\<exists>\<alpha> (\<psi>{\<alpha>} & \<phi>{\<alpha>})\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<exists>\<alpha> (\<psi>{\<alpha>} & \<diamond>\<phi>{\<alpha>})\<close>
  then AOT_obtain \<alpha> where \<open>\<psi>{\<alpha>} & \<diamond>\<phi>{\<alpha>}\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<open>\<box>\<psi>{\<alpha>}\<close> and \<open>\<diamond>\<phi>{\<alpha>}\<close>
    using rigid_condition[THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"], THEN "\<rightarrow>E"] "&E" by blast+
  AOT_hence \<open>\<diamond>(\<psi>{\<alpha>} & \<phi>{\<alpha>})\<close> by (metis "KBasic:16" "con-dis-taut:5" "\<rightarrow>E")
  AOT_hence \<open>\<exists>\<alpha> \<diamond>(\<psi>{\<alpha>} & \<phi>{\<alpha>})\<close>
    by (rule "\<exists>I")
  AOT_thus \<open>\<diamond>\<exists>\<alpha> (\<psi>{\<alpha>} & \<phi>{\<alpha>})\<close> using "CBF\<diamond>"[THEN "\<rightarrow>E"] by fast
qed
end

(*<*)
end
(*>*)