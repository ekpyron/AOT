theory AOT_PLM
  imports AOT_axioms
begin

(* To enable meta syntax: *)
interpretation AOT_meta_syntax.
(* To disable meta syntax: *)
(* interpretation AOT_no_meta_syntax. *)

(* To enable AOT syntax (takes precedence over meta syntax; can be done locally using "including" or "include"): *)
(* unbundle AOT_syntax *)
(* To disable AOT syntax (restoring meta syntax or no syntax; can be done locally using "including" or "include"): *)
unbundle AOT_no_syntax

AOT_theorem modus_ponens: assumes \<open>\<phi>\<close> and \<open>\<phi> \<rightarrow> \<psi>\<close> shows \<open>\<psi>\<close>
  using assms by (simp add: AOT_sem_imp) (* NOTE: semantics needed *)
lemmas MP = modus_ponens

AOT_theorem non_con_thm_thm: assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi>\<close> shows \<open>\<^bold>\<turnstile> \<phi>\<close>
  using assms by simp

AOT_theorem vdash_properties_1_a: assumes \<open>\<phi> \<in> \<Lambda>\<close> shows \<open>\<^bold>\<turnstile> \<phi>\<close>
  using assms unfolding AOT_model_act_axiom_def by blast (* NOTE: semantics needed *)

attribute_setup act_axiom_inst =
  \<open>Scan.succeed (Thm.rule_attribute [] (K (fn thm => thm RS @{thm vdash_properties_1_a})))\<close>
  "Instantiate modally fragile axiom as modally fragile theorem."

AOT_theorem vdash_properties_1_b: assumes \<open>\<phi> \<in> \<Lambda>\<^sub>\<box>\<close> shows \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi>\<close>
  using assms unfolding AOT_model_axiom_def by blast (* NOTE: semantics needed *)

attribute_setup axiom_inst =
  \<open>Scan.succeed (Thm.rule_attribute [] (K (fn thm => thm RS @{thm vdash_properties_1_b})))\<close>
  "Instantiate axiom as theorem."

AOT_theorem vdash_properties_3: assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi>\<close> shows \<open>\<Gamma> \<^bold>\<turnstile> \<phi>\<close>
  using assms by blast

AOT_theorem vdash_properties_5: assumes \<open>\<Gamma>\<^sub>1 \<^bold>\<turnstile> \<phi>\<close> and \<open>\<Gamma>\<^sub>2 \<^bold>\<turnstile> \<phi> \<rightarrow> \<psi>\<close> shows \<open>\<Gamma>\<^sub>1, \<Gamma>\<^sub>2 \<^bold>\<turnstile> \<psi>\<close>
  using MP assms by blast

AOT_theorem vdash_properties_6: assumes \<open>\<phi>\<close> and \<open>\<phi> \<rightarrow> \<psi>\<close> shows \<open>\<psi>\<close>
  using MP assms by blast

AOT_theorem vdash_properties_8: assumes \<open>\<Gamma> \<^bold>\<turnstile> \<phi>\<close> and \<open>\<phi> \<^bold>\<turnstile> \<psi>\<close> shows \<open>\<Gamma> \<^bold>\<turnstile> \<psi>\<close>
  using assms by argo

AOT_theorem vdash_properties_9: assumes \<open>\<phi>\<close> shows \<open>\<psi> \<rightarrow> \<phi>\<close>
  using MP pl_1[axiom_inst] assms by blast

AOT_theorem vdash_properties_10: assumes \<open>\<phi> \<rightarrow> \<psi>\<close> and \<open>\<phi>\<close> shows \<open>\<psi>\<close>
  using MP assms by blast
lemmas "\<rightarrow>E" = vdash_properties_10

AOT_theorem rule_gen: assumes \<open>for arbitrary \<alpha>: \<phi>{\<alpha>}\<close> shows \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close>
  using assms by (metis AOT_var_of_term_inverse AOT_sem_denotes AOT_sem_forall) (* NOTE: semantics needed *)
lemmas GEN = rule_gen

AOT_theorem RN_prem: assumes \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<phi>\<close> shows \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<box>\<phi>\<close>
  by (meson AOT_sem_box assms image_iff) (* NOTE: semantics needed *)
AOT_theorem RN: assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi>\<close> shows \<open>\<box>\<phi>\<close>
  using RN_prem assms by blast


AOT_theorem df_rules_formulas_1: assumes \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>\<close> shows \<open>\<phi> \<rightarrow> \<psi>\<close>
  using assms by (simp_all add: AOT_model_equiv_def AOT_sem_imp) (* NOTE: semantics needed *)
AOT_theorem df_rules_formulas_2: assumes \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>\<close> shows \<open>\<psi> \<rightarrow> \<phi>\<close>
  using assms by (simp_all add: AOT_model_equiv_def AOT_sem_imp) (* NOTE: semantics needed *)
(* To also get the closures of them, derive them as axioms as well *)
AOT_axiom df_rules_formulas_3: assumes \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>\<close> shows \<open>\<phi> \<rightarrow> \<psi>\<close>
  by (rule AOT_model_axiomI) (simp add: df_rules_formulas_1[OF assms]) (* NOTE: semantics needed *)
AOT_axiom df_rules_formulas_4: assumes \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>\<close> shows \<open>\<psi> \<rightarrow> \<phi>\<close>
  by (rule AOT_model_axiomI) (simp add: df_rules_formulas_2[OF assms]) (* NOTE: semantics needed *)


AOT_theorem df_rules_terms_1:
  assumes \<open>\<tau>{\<alpha>\<^sub>1...\<alpha>\<^sub>n} =\<^sub>d\<^sub>f \<sigma>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}\<close>
  shows \<open>(\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down> \<rightarrow> \<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n} = \<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}) & (\<not>\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down> \<rightarrow> \<not>\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down>)\<close>
  using assms by (simp add: AOT_sem_conj AOT_sem_imp AOT_sem_eq AOT_sem_not AOT_sem_denotes AOT_model_id_def) (* NOTE: semantics needed *)
AOT_theorem df_rules_terms_2:
  assumes \<open>\<tau> =\<^sub>d\<^sub>f \<sigma>\<close>
  shows \<open>(\<sigma>\<down> \<rightarrow> \<tau> = \<sigma>) & (\<not>\<sigma>\<down> \<rightarrow> \<not>\<tau>\<down>)\<close>
  using assms by (metis df_rules_terms_1 case_unit_Unity) (* NOTE: semantics needed *)
(* To also get the closures of them, derive them as axioms as well *)
AOT_axiom df_rules_terms_3:
  assumes \<open>\<tau>{\<alpha>\<^sub>1...\<alpha>\<^sub>n} =\<^sub>d\<^sub>f \<sigma>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}\<close>
  shows \<open>(\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down> \<rightarrow> \<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n} = \<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}) & (\<not>\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down> \<rightarrow> \<not>\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down>)\<close>
  by (rule AOT_model_axiomI) (simp add: df_rules_terms_1[OF assms]) (* NOTE: semantics needed *)
AOT_axiom df_rules_terms_4:
  assumes \<open>\<tau> =\<^sub>d\<^sub>f \<sigma>\<close>
  shows \<open>(\<sigma>\<down> \<rightarrow> \<tau> = \<sigma>) & (\<not>\<sigma>\<down> \<rightarrow> \<not>\<tau>\<down>)\<close>
  by (rule AOT_model_axiomI) (simp add: df_rules_terms_2[OF assms]) (* NOTE: semantics needed *)


AOT_theorem if_p_then_p: \<open>\<phi> \<rightarrow> \<phi>\<close>
  by (meson pl_1[axiom_inst] pl_2[axiom_inst] MP)

AOT_theorem deduction_theorem: assumes \<open>\<phi> \<^bold>\<turnstile> \<psi>\<close> shows \<open>\<phi> \<rightarrow> \<psi>\<close>
  using assms by (simp add: AOT_sem_imp) (* NOTE: semantics needed *)
lemmas CP = deduction_theorem
lemmas "\<rightarrow>I" = deduction_theorem

AOT_theorem ded_thm_cor_1: assumes \<open>\<phi> \<rightarrow> \<psi>\<close> and \<open>\<psi> \<rightarrow> \<chi>\<close> shows \<open>\<phi> \<rightarrow> \<chi>\<close>
  using "\<rightarrow>E" "\<rightarrow>I" assms by blast
declare ded_thm_cor_1[trans]
AOT_theorem ded_thm_cor_2: assumes \<open>\<phi> \<rightarrow> (\<psi> \<rightarrow> \<chi>)\<close> and \<open>\<psi>\<close> shows \<open>\<phi> \<rightarrow> \<chi>\<close>
  using "\<rightarrow>E" "\<rightarrow>I" assms by blast

AOT_theorem useful_tautologies_1: \<open>\<not>\<not>\<phi> \<rightarrow> \<phi>\<close>
  by (metis pl_3[axiom_inst] "\<rightarrow>I" ded_thm_cor_1)
AOT_theorem useful_tautologies_2: \<open>\<phi> \<rightarrow> \<not>\<not>\<phi>\<close>
  by (metis pl_3[axiom_inst] "\<rightarrow>I" ded_thm_cor_2)
AOT_theorem useful_tautologies_3: \<open>\<not>\<phi> \<rightarrow> (\<phi> \<rightarrow> \<psi>)\<close>
  by (meson ded_thm_cor_2 pl_3[axiom_inst] "\<rightarrow>I")
AOT_theorem useful_tautologies_4: \<open>(\<not>\<psi> \<rightarrow> \<not>\<phi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>)\<close>
  by (meson pl_3[axiom_inst] ded_thm_cor_1 "\<rightarrow>I")
AOT_theorem useful_tautologies_5: \<open>(\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<not>\<psi> \<rightarrow> \<not>\<phi>)\<close>
  by (metis useful_tautologies_4 ded_thm_cor_1 "\<rightarrow>I")

AOT_theorem useful_tautologies_6: \<open>(\<phi> \<rightarrow> \<not>\<psi>) \<rightarrow> (\<psi> \<rightarrow> \<not>\<phi>)\<close>
  by (metis "\<rightarrow>I" MP useful_tautologies_4)

AOT_theorem useful_tautologies_7: \<open>(\<not>\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<not>\<psi> \<rightarrow> \<phi>)\<close>
  by (metis "\<rightarrow>I" MP useful_tautologies_3 useful_tautologies_5)

AOT_theorem useful_tautologies_8: \<open>\<phi> \<rightarrow> (\<not>\<psi> \<rightarrow> \<not>(\<phi> \<rightarrow> \<psi>))\<close>
  by (metis "\<rightarrow>I" MP useful_tautologies_5)

AOT_theorem useful_tautologies_9: \<open>(\<phi> \<rightarrow> \<psi>) \<rightarrow> ((\<not>\<phi> \<rightarrow> \<psi>) \<rightarrow> \<psi>)\<close>
  by (metis "\<rightarrow>I" MP useful_tautologies_6)

AOT_theorem useful_tautologies_10: \<open>(\<phi> \<rightarrow> \<not>\<psi>) \<rightarrow> ((\<phi> \<rightarrow> \<psi>) \<rightarrow> \<not>\<phi>)\<close>
  by (metis "\<rightarrow>I" MP pl_3[axiom_inst])

AOT_theorem dn_i_e_1: assumes \<open>\<phi>\<close> shows \<open>\<not>\<not>\<phi>\<close>
  using MP useful_tautologies_2 assms by blast
lemmas "\<not>\<not>I" = dn_i_e_1
AOT_theorem dn_i_e_2: assumes \<open>\<not>\<not>\<phi>\<close> shows \<open>\<phi>\<close>
  using MP useful_tautologies_1 assms by blast
lemmas "\<not>\<not>E" = dn_i_e_2

AOT_theorem modus_tollens_1: assumes \<open>\<phi> \<rightarrow> \<psi>\<close> and \<open>\<not>\<psi>\<close> shows \<open>\<not>\<phi>\<close>
  using MP useful_tautologies_5 assms by blast
AOT_theorem modus_tollens_2: assumes \<open>\<phi> \<rightarrow> \<not>\<psi>\<close> and \<open>\<psi>\<close> shows \<open>\<not>\<phi>\<close>
  using "\<not>\<not>I" modus_tollens_1 assms by blast
lemmas "MT" = modus_tollens_1 modus_tollens_2

AOT_theorem contraposition_1_a: assumes \<open>\<phi> \<rightarrow> \<psi>\<close> shows \<open>\<not>\<psi> \<rightarrow> \<not>\<phi>\<close>
  using "\<rightarrow>I" MT(1) assms by blast
AOT_theorem contraposition_1_b: assumes \<open>\<not>\<psi> \<rightarrow> \<not>\<phi>\<close> shows \<open>\<phi> \<rightarrow> \<psi>\<close>
  using "\<rightarrow>I" "\<not>\<not>E" MT(2) assms by blast

AOT_theorem contraposition_2_a: assumes \<open>\<phi> \<rightarrow> \<not>\<psi>\<close> shows \<open>\<psi> \<rightarrow> \<not>\<phi>\<close>
  using "\<rightarrow>I" MT(2) assms by blast
AOT_theorem contraposition_2_b: assumes \<open>\<psi> \<rightarrow> \<not>\<phi>\<close> shows \<open>\<phi> \<rightarrow> \<not>\<psi>\<close> (* TODO: note same as above! *)
  by (simp add: contraposition_2_a assms)

AOT_theorem reductio_aa_1:
  assumes \<open>\<not>\<phi> \<^bold>\<turnstile> \<not>\<psi>\<close> and \<open>\<not>\<phi> \<^bold>\<turnstile> \<psi>\<close> shows \<open>\<phi>\<close>
  using "\<rightarrow>I" "\<not>\<not>E" MT(2) assms by blast
AOT_theorem reductio_aa_2:
  assumes \<open>\<phi> \<^bold>\<turnstile> \<not>\<psi>\<close> and \<open>\<phi> \<^bold>\<turnstile> \<psi>\<close> shows \<open>\<not>\<phi>\<close>
  using reductio_aa_1 assms by blast
lemmas "RAA" = reductio_aa_1 reductio_aa_2

AOT_theorem exc_mid: \<open>\<phi> \<or> \<not>\<phi>\<close>
  using df_rules_formulas_2 if_p_then_p MP AOT_disj by blast

AOT_theorem non_contradiction: \<open>\<not>(\<phi> & \<not>\<phi>)\<close>
  using df_rules_formulas_1 MT(2) useful_tautologies_2 AOT_conj by blast

AOT_theorem con_dis_taut_1: \<open>(\<phi> & \<psi>) \<rightarrow> \<phi>\<close>
  by (meson "\<rightarrow>I" df_rules_formulas_1 MP RAA(1) AOT_conj)
AOT_theorem con_dis_taut_2: \<open>(\<phi> & \<psi>) \<rightarrow> \<psi>\<close>
  by (metis "\<rightarrow>I" df_rules_formulas_1 MT(2) RAA(2) "\<not>\<not>E" AOT_conj)
AOT_theorem con_dis_taut_3: \<open>\<phi> \<rightarrow> (\<phi> \<or> \<psi>)\<close>
  by (meson contraposition_1_b df_rules_formulas_2 MP "\<rightarrow>I" AOT_disj)
AOT_theorem con_dis_taut_4: \<open>\<psi> \<rightarrow> (\<phi> \<or> \<psi>)\<close>
  using ded_thm_cor_1 df_rules_formulas_2 pl_1[axiom_inst] AOT_disj by blast
AOT_theorem con_dis_taut_5: \<open>\<phi> \<rightarrow> (\<psi> \<rightarrow> (\<phi> & \<psi>))\<close>
  by (metis contraposition_2_a ded_thm_cor_1 "\<rightarrow>I" df_rules_formulas_2 AOT_conj)
AOT_theorem con_dis_taut_6: \<open>(\<phi> & \<phi>) \<equiv> \<phi>\<close>
  by (metis con_dis_taut_5 "\<rightarrow>I" df_rules_formulas_2 MP con_dis_taut_1 AOT_equiv)
(* TODO: note surprisingly no automatic proof here! *)
AOT_theorem con_dis_taut_7: \<open>(\<phi> \<or> \<phi>) \<equiv> \<phi>\<close>
proof -
  {
    AOT_assume \<open>\<phi> \<or> \<phi>\<close>
    AOT_hence \<open>\<not>\<phi> \<rightarrow> \<phi>\<close>
      using AOT_disj[THEN df_rules_formulas_1] MP by blast
    AOT_hence \<open>\<phi>\<close> using if_p_then_p RAA(1) MP by blast
  }
  moreover {
    AOT_assume \<open>\<phi>\<close>
    AOT_hence \<open>\<phi> \<or> \<phi>\<close> using con_dis_taut_3 MP by blast
  }
  ultimately AOT_show \<open>(\<phi> \<or> \<phi>) \<equiv> \<phi>\<close>
    using AOT_equiv[THEN df_rules_formulas_2] MP
    by (metis con_dis_taut_5 "\<rightarrow>I")
qed

(* NOTE: this makes the last proof go through automatically and appears to be independently provable *)
AOT_theorem con_dis_i_e_1: assumes \<open>\<phi>\<close> and \<open>\<psi>\<close> shows \<open>\<phi> & \<psi>\<close>
  using con_dis_taut_5 MP assms by blast
lemmas "&I" = con_dis_i_e_1

AOT_theorem con_dis_i_e_2_a: assumes \<open>\<phi> & \<psi>\<close> shows \<open>\<phi>\<close>
  using con_dis_taut_1 MP assms by blast
AOT_theorem con_dis_i_e_2_b: assumes \<open>\<phi> & \<psi>\<close> shows \<open>\<psi>\<close>
  using con_dis_taut_2 MP assms by blast
lemmas "&E" = con_dis_i_e_2_a con_dis_i_e_2_b

AOT_theorem con_dis_i_e_3_a: assumes \<open>\<phi>\<close> shows \<open>\<phi> \<or> \<psi>\<close>
  using con_dis_taut_3 MP assms by blast
AOT_theorem con_dis_i_e_3_b: assumes \<open>\<psi>\<close> shows \<open>\<phi> \<or> \<psi>\<close>
  using con_dis_taut_4 MP assms by blast
AOT_theorem con_dis_i_e_3_c: assumes \<open>\<phi> \<or> \<psi>\<close> and \<open>\<phi> \<rightarrow> \<chi>\<close> and \<open>\<psi> \<rightarrow> \<Theta>\<close> shows \<open>\<chi> \<or> \<Theta>\<close>
  by (metis con_dis_i_e_3_a con_dis_taut_4 df_rules_formulas_1 MT(1) RAA(1) AOT_disj assms)
lemmas "\<or>I" = con_dis_i_e_3_a con_dis_i_e_3_b con_dis_i_e_3_c

AOT_theorem con_dis_i_e_4_a: assumes \<open>\<phi> \<or> \<psi>\<close> and \<open>\<phi> \<rightarrow> \<chi>\<close> and \<open>\<psi> \<rightarrow> \<chi>\<close> shows \<open>\<chi>\<close>
  by (metis MP RAA(2) df_rules_formulas_1 AOT_disj assms)
AOT_theorem con_dis_i_e_4_b: assumes \<open>\<phi> \<or> \<psi>\<close> and \<open>\<not>\<phi>\<close> shows \<open>\<psi>\<close>
  using con_dis_i_e_4_a RAA(1) "\<rightarrow>I" assms by blast
AOT_theorem con_dis_i_e_4_c: assumes \<open>\<phi> \<or> \<psi>\<close> and \<open>\<not>\<psi>\<close> shows \<open>\<phi>\<close>
  using con_dis_i_e_4_a RAA(1) "\<rightarrow>I" assms by blast
lemmas "\<or>E" = con_dis_i_e_4_a con_dis_i_e_4_b con_dis_i_e_4_c

AOT_theorem raa_cor_1: assumes \<open>\<not>\<phi> \<^bold>\<turnstile> \<psi> & \<not>\<psi>\<close> shows \<open>\<phi>\<close>
  using "&E" "\<or>E"(3) "\<or>I"(2) RAA(2) assms by blast
AOT_theorem raa_cor_2: assumes \<open>\<phi> \<^bold>\<turnstile> \<psi> & \<not>\<psi>\<close> shows \<open>\<not>\<phi>\<close>
  using raa_cor_1 assms by blast
AOT_theorem raa_cor_3: assumes \<open>\<phi>\<close> and \<open>\<not>\<psi> \<^bold>\<turnstile> \<not>\<phi>\<close> shows \<open>\<psi>\<close>
  using RAA assms by blast
AOT_theorem raa_cor_4: assumes \<open>\<not>\<phi>\<close> and \<open>\<not>\<psi> \<^bold>\<turnstile> \<phi>\<close> shows \<open>\<psi>\<close>
  using RAA assms by blast
AOT_theorem raa_cor_5: assumes \<open>\<phi>\<close> and \<open>\<psi> \<^bold>\<turnstile> \<not>\<phi>\<close> shows \<open>\<not>\<psi>\<close>
  using RAA assms by blast
AOT_theorem raa_cor_6: assumes \<open>\<not>\<phi>\<close> and \<open>\<psi> \<^bold>\<turnstile> \<phi>\<close> shows \<open>\<not>\<psi>\<close>
  using RAA assms by blast

(* TODO: note these need manual introduction rules *)
AOT_theorem oth_class_taut_1_a: \<open>(\<phi> \<rightarrow> \<psi>) \<equiv> \<not>(\<phi> & \<not>\<psi>)\<close>
  by (rule AOT_equiv[THEN df_rules_formulas_2, THEN "\<rightarrow>E"])
     (metis "&E" "&I" raa_cor_3 "\<rightarrow>I" MP)
AOT_theorem oth_class_taut_1_b: \<open>\<not>(\<phi> \<rightarrow> \<psi>) \<equiv> (\<phi> & \<not>\<psi>)\<close>
  by (rule AOT_equiv[THEN df_rules_formulas_2, THEN "\<rightarrow>E"])
     (metis "&E" "&I" raa_cor_3 "\<rightarrow>I" MP)
AOT_theorem oth_class_taut_1_c: \<open>(\<phi> \<rightarrow> \<psi>) \<equiv> (\<not>\<phi> \<or> \<psi>)\<close>
  by (rule AOT_equiv[THEN df_rules_formulas_2, THEN "\<rightarrow>E"])
     (metis "&I" "\<or>I"(1, 2) "\<or>E"(3) "\<rightarrow>I" MP raa_cor_1)

AOT_theorem oth_class_taut_2_a: \<open>(\<phi> & \<psi>) \<equiv> (\<psi> & \<phi>)\<close>
  by (rule AOT_equiv[THEN df_rules_formulas_2, THEN "\<rightarrow>E"])
     (meson "&I" "&E" "\<rightarrow>I")
AOT_theorem oth_class_taut_2_b: \<open>(\<phi> & (\<psi> & \<chi>)) \<equiv> ((\<phi> & \<psi>) & \<chi>)\<close>
  by (rule AOT_equiv[THEN df_rules_formulas_2, THEN "\<rightarrow>E"])
     (metis "&I" "&E" "\<rightarrow>I")
AOT_theorem oth_class_taut_2_c: \<open>(\<phi> \<or> \<psi>) \<equiv> (\<psi> \<or> \<phi>)\<close>
  by (rule AOT_equiv[THEN df_rules_formulas_2, THEN "\<rightarrow>E"])
     (metis "&I" "\<or>I"(1, 2) "\<or>E"(1) "\<rightarrow>I")
AOT_theorem oth_class_taut_2_d: \<open>(\<phi> \<or> (\<psi> \<or> \<chi>)) \<equiv> ((\<phi> \<or> \<psi>) \<or> \<chi>)\<close>
  by (rule AOT_equiv[THEN df_rules_formulas_2, THEN "\<rightarrow>E"])
     (metis "&I" "\<or>I"(1, 2) "\<or>E"(1) "\<rightarrow>I")
AOT_theorem oth_class_taut_2_e: \<open>(\<phi> \<equiv> \<psi>) \<equiv> (\<psi> \<equiv> \<phi>)\<close>
  by (rule AOT_equiv[THEN df_rules_formulas_2, THEN "\<rightarrow>E"]; rule "&I";
      metis "&I" df_rules_formulas_2 AOT_equiv "&E" ded_thm_cor_1 "\<rightarrow>I" df_rules_formulas_1)
AOT_theorem oth_class_taut_2_f: \<open>(\<phi> \<equiv> (\<psi> \<equiv> \<chi>)) \<equiv> ((\<phi> \<equiv> \<psi>) \<equiv> \<chi>)\<close>
  using AOT_equiv[THEN df_rules_formulas_2] AOT_equiv[THEN df_rules_formulas_1]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I"
  by metis

AOT_theorem oth_class_taut_3_a: \<open>\<phi> \<equiv> \<phi>\<close>
  using "&I" vdash_properties_6 if_p_then_p df_rules_formulas_2 AOT_equiv by blast
AOT_theorem oth_class_taut_3_b: \<open>\<phi> \<equiv> \<not>\<not>\<phi>\<close>
  using "&I" useful_tautologies_1 useful_tautologies_2 vdash_properties_6 df_rules_formulas_2 AOT_equiv by blast
AOT_theorem oth_class_taut_3_c: \<open>\<not>(\<phi> \<equiv> \<not>\<phi>)\<close>
  by (metis "&E" "\<rightarrow>E" RAA df_rules_formulas_1 AOT_equiv)

AOT_theorem oth_class_taut_4_a: \<open>(\<phi> \<rightarrow> \<psi>) \<rightarrow> ((\<psi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> \<chi>))\<close>
  by (metis "\<rightarrow>E" "\<rightarrow>I")
AOT_theorem oth_class_taut_4_b: \<open>(\<phi> \<equiv> \<psi>) \<equiv> (\<not>\<phi> \<equiv> \<not>\<psi>)\<close>
  using AOT_equiv[THEN df_rules_formulas_2] AOT_equiv[THEN df_rules_formulas_1]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" RAA by metis
AOT_theorem oth_class_taut_4_c: \<open>(\<phi> \<equiv> \<psi>) \<rightarrow> ((\<phi> \<rightarrow> \<chi>) \<equiv> (\<psi> \<rightarrow> \<chi>))\<close>
  using AOT_equiv[THEN df_rules_formulas_2] AOT_equiv[THEN df_rules_formulas_1]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" by metis
AOT_theorem oth_class_taut_4_d: \<open>(\<phi> \<equiv> \<psi>) \<rightarrow> ((\<chi> \<rightarrow> \<phi>) \<equiv> (\<chi> \<rightarrow> \<psi>))\<close>
  using AOT_equiv[THEN df_rules_formulas_2] AOT_equiv[THEN df_rules_formulas_1]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" by metis
AOT_theorem oth_class_taut_4_e: \<open>(\<phi> \<equiv> \<psi>) \<rightarrow> ((\<phi> & \<chi>) \<equiv> (\<psi> & \<chi>))\<close>
  using AOT_equiv[THEN df_rules_formulas_2] AOT_equiv[THEN df_rules_formulas_1]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" by metis
AOT_theorem oth_class_taut_4_f: \<open>(\<phi> \<equiv> \<psi>) \<rightarrow> ((\<chi> & \<phi>) \<equiv> (\<chi> & \<psi>))\<close>
  using AOT_equiv[THEN df_rules_formulas_2] AOT_equiv[THEN df_rules_formulas_1]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" by metis
(* TODO: nicer proof *)
AOT_theorem oth_class_taut_4_g: \<open>(\<phi> \<equiv> \<psi>) \<equiv> ((\<phi> & \<psi>) \<or> (\<not>\<phi> & \<not>\<psi>))\<close>
  apply (rule AOT_equiv[THEN df_rules_formulas_2, THEN "\<rightarrow>E"]; rule "&I"; rule "\<rightarrow>I")
   apply (drule AOT_equiv[THEN df_rules_formulas_1, THEN "\<rightarrow>E"])
   apply (metis "&I" "&E" "\<or>I"(1,2) MT(1) raa_cor_3)
  apply (rule AOT_equiv[THEN df_rules_formulas_2, THEN "\<rightarrow>E"]; rule "&I"; rule "\<rightarrow>I")
  using "&E" "\<or>E"(2) raa_cor_3 by blast+
AOT_theorem oth_class_taut_4_h: \<open>\<not>(\<phi> \<equiv> \<psi>) \<equiv> ((\<phi> & \<not>\<psi>) \<or> (\<not>\<phi> & \<psi>))\<close>
  apply (rule AOT_equiv[THEN df_rules_formulas_2, THEN "\<rightarrow>E"]; rule "&I"; rule "\<rightarrow>I")
  apply (metis "&I" "\<or>I"(1, 2) "\<rightarrow>I" MT(1) df_rules_formulas_2 raa_cor_3 AOT_equiv)
  by (metis "&E" "\<or>E"(2) "\<rightarrow>E" df_rules_formulas_1 raa_cor_3 AOT_equiv)
AOT_theorem oth_class_taut_5_a: \<open>(\<phi> & \<psi>) \<equiv> \<not>(\<not>\<phi> \<or> \<not>\<psi>)\<close>
  using AOT_equiv[THEN df_rules_formulas_2]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" "\<or>I" "\<or>E" RAA by metis
AOT_theorem oth_class_taut_5_b: \<open>(\<phi> \<or> \<psi>) \<equiv> \<not>(\<not>\<phi> & \<not>\<psi>)\<close>
  using AOT_equiv[THEN df_rules_formulas_2]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" "\<or>I" "\<or>E" RAA by metis
AOT_theorem oth_class_taut_5_c: \<open>\<not>(\<phi> & \<psi>) \<equiv> (\<not>\<phi> \<or> \<not>\<psi>)\<close>
  using AOT_equiv[THEN df_rules_formulas_2]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" "\<or>I" "\<or>E" RAA by metis
AOT_theorem oth_class_taut_5_d: \<open>\<not>(\<phi> \<or> \<psi>) \<equiv> (\<not>\<phi> & \<not>\<psi>)\<close>
  using AOT_equiv[THEN df_rules_formulas_2]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" "\<or>I" "\<or>E" RAA by metis

AOT_theorem oth_class_taut_6_a: \<open>(\<phi> & (\<psi> \<or> \<chi>)) \<equiv> ((\<phi> & \<psi>) \<or> (\<phi> & \<chi>))\<close>
  using AOT_equiv[THEN df_rules_formulas_2]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" "\<or>I" "\<or>E" RAA by metis
AOT_theorem oth_class_taut_6_b: \<open>(\<phi> \<or> (\<psi> & \<chi>)) \<equiv> ((\<phi> \<or> \<psi>) & (\<phi> \<or> \<chi>))\<close>
  using AOT_equiv[THEN df_rules_formulas_2]
        "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" "\<or>I" "\<or>E" RAA by metis

AOT_theorem oth_class_taut_7_a: \<open>((\<phi> & \<psi>) \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> (\<psi> \<rightarrow> \<chi>))\<close>
  by (metis "&I" "\<rightarrow>E" "\<rightarrow>I")
AOT_theorem oth_class_taut_7_b: \<open>(\<phi> \<rightarrow> (\<psi> \<rightarrow>\<chi>)) \<rightarrow> ((\<phi> & \<psi>) \<rightarrow> \<chi>)\<close>
  by (metis "&E" "\<rightarrow>E" "\<rightarrow>I")

AOT_theorem oth_class_taut_8_a: \<open>(\<phi> \<rightarrow> (\<psi> \<rightarrow> \<chi>)) \<equiv> (\<psi> \<rightarrow> (\<phi> \<rightarrow> \<chi>))\<close>
  using AOT_equiv[THEN df_rules_formulas_2] "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" by metis
AOT_theorem oth_class_taut_8_b: \<open>(\<phi> \<rightarrow> \<psi>) \<rightarrow> ((\<phi> \<rightarrow> \<chi>) \<rightarrow> (\<phi> \<rightarrow> (\<psi> & \<chi>)))\<close>
  by (metis "&I" "\<rightarrow>E" "\<rightarrow>I")
AOT_theorem oth_class_taut_8_c: \<open>(\<phi> \<rightarrow> \<chi>) \<rightarrow> ((\<psi> \<rightarrow> \<chi>) \<rightarrow> ((\<psi> \<or> \<chi>) \<rightarrow> \<chi>))\<close>
  by (metis "\<or>E"(2) "\<rightarrow>E" "\<rightarrow>I" RAA(1))
AOT_theorem oth_class_taut_8_d: \<open>((\<phi> \<rightarrow> \<psi>) & (\<chi> \<rightarrow> \<Theta>)) \<rightarrow> ((\<phi> & \<chi>) \<rightarrow> (\<psi> & \<Theta>))\<close>
  by (metis "&E" "&I" "\<rightarrow>E" "\<rightarrow>I")
AOT_theorem oth_class_taut_8_e: \<open>((\<phi> & \<psi>) \<equiv> (\<phi> & \<chi>)) \<equiv> (\<phi> \<rightarrow> (\<psi> \<equiv> \<chi>))\<close>
  by (metis AOT_equiv[THEN df_rules_formulas_2] AOT_equiv[THEN df_rules_formulas_1]
            "\<rightarrow>I" "\<rightarrow>E" "&E" "&I")
AOT_theorem oth_class_taut_8_f: \<open>((\<phi> & \<psi>) \<equiv> (\<chi> & \<psi>)) \<equiv> (\<psi> \<rightarrow> (\<phi> \<equiv> \<chi>))\<close>
  by (metis AOT_equiv[THEN df_rules_formulas_2] AOT_equiv[THEN df_rules_formulas_1]
            "\<rightarrow>I" "\<rightarrow>E" "&E" "&I")
AOT_theorem oth_class_taut_8_g: \<open>(\<psi> \<equiv> \<chi>) \<rightarrow> ((\<phi> \<or> \<psi>) \<equiv> (\<phi> \<or> \<chi>))\<close>
  by (metis AOT_equiv[THEN df_rules_formulas_2] AOT_equiv[THEN df_rules_formulas_1]
            "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" "\<or>I" "\<or>E"(1))
AOT_theorem oth_class_taut_8_h: \<open>(\<psi> \<equiv> \<chi>) \<rightarrow> ((\<psi> \<or> \<phi>) \<equiv> (\<chi> \<or> \<phi>))\<close>
  by (metis AOT_equiv[THEN df_rules_formulas_2] AOT_equiv[THEN df_rules_formulas_1]
            "\<rightarrow>I" "\<rightarrow>E" "&E" "&I" "\<or>I" "\<or>E"(1))
AOT_theorem oth_class_taut_8_i: \<open>(\<phi> \<equiv> (\<psi> & \<chi>)) \<rightarrow> (\<psi> \<rightarrow> (\<phi> \<equiv> \<chi>))\<close>
  by (metis AOT_equiv[THEN df_rules_formulas_2] AOT_equiv[THEN df_rules_formulas_1]
            "\<rightarrow>I" "\<rightarrow>E" "&E" "&I")

AOT_theorem intro_elim_1: assumes \<open>\<phi> \<or> \<psi>\<close> and \<open>\<phi> \<equiv> \<chi>\<close> and \<open>\<psi> \<equiv> \<Theta>\<close> shows \<open>\<chi> \<or> \<Theta>\<close>
  by (metis assms "\<or>I"(1, 2) "\<or>E"(1) AOT_equiv[THEN df_rules_formulas_1] "\<rightarrow>I" "\<rightarrow>E" "&E"(1))

AOT_theorem intro_elim_2: assumes \<open>\<phi> \<rightarrow> \<psi>\<close> and \<open>\<psi> \<rightarrow> \<phi>\<close> shows \<open>\<phi> \<equiv> \<psi>\<close>
  by (meson "&I" AOT_equiv df_rules_formulas_2 MP assms)
lemmas "\<equiv>I" = intro_elim_2

AOT_theorem intro_elim_3_a: assumes \<open>\<phi> \<equiv> \<psi>\<close> and \<open>\<phi>\<close> shows \<open>\<psi>\<close>
  by (metis "\<or>I"(1) "\<rightarrow>I" "\<or>E"(1) intro_elim_1 assms)
AOT_theorem intro_elim_3_b: assumes \<open>\<phi> \<equiv> \<psi>\<close> and \<open>\<psi>\<close> shows \<open>\<phi>\<close>
  using intro_elim_3_a oth_class_taut_2_e assms by blast
AOT_theorem intro_elim_3_c: assumes \<open>\<phi> \<equiv> \<psi>\<close> and \<open>\<not>\<phi>\<close> shows \<open>\<not>\<psi>\<close>
  using intro_elim_3_b raa_cor_3 assms by blast
AOT_theorem intro_elim_3_d: assumes \<open>\<phi> \<equiv> \<psi>\<close> and \<open>\<not>\<psi>\<close> shows \<open>\<not>\<phi>\<close>
  using intro_elim_3_a raa_cor_3 assms by blast
AOT_theorem intro_elim_3_e: assumes \<open>\<phi> \<equiv> \<psi>\<close> and \<open>\<psi> \<equiv> \<chi>\<close> shows \<open>\<phi> \<equiv> \<chi>\<close>
  by (metis "\<equiv>I" "\<rightarrow>I" intro_elim_3_a intro_elim_3_b assms)
declare intro_elim_3_e[trans]
AOT_theorem intro_elim_3_f: assumes \<open>\<phi> \<equiv> \<psi>\<close> and \<open>\<phi> \<equiv> \<chi>\<close> shows \<open>\<chi> \<equiv> \<psi>\<close>
  by (metis "\<equiv>I" "\<rightarrow>I" intro_elim_3_a intro_elim_3_b assms)
lemmas "\<equiv>E" = intro_elim_3_a intro_elim_3_b intro_elim_3_c intro_elim_3_d intro_elim_3_e intro_elim_3_f

AOT_theorem rule_eq_df_1: assumes \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>\<close> shows \<open>\<phi> \<equiv> \<psi>\<close>
  by (simp add: "\<equiv>I" df_rules_formulas_1 df_rules_formulas_2 assms)
lemmas "\<equiv>Df" = rule_eq_df_1
AOT_theorem rule_eq_df_2: assumes \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>\<close> and \<open>\<phi>\<close> shows \<open>\<psi>\<close>
  using "\<equiv>Df" "\<equiv>E"(1) assms by blast
lemmas "\<equiv>\<^sub>d\<^sub>fE" = rule_eq_df_2
AOT_theorem rule_eq_df_3: assumes \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>\<close> and \<open>\<psi>\<close> shows \<open>\<phi>\<close>
  using "\<equiv>Df" "\<equiv>E"(2) assms by blast
lemmas "\<equiv>\<^sub>d\<^sub>fI" = rule_eq_df_3

AOT_theorem df_simplify_1: assumes \<open>\<phi> \<equiv> (\<psi> & \<chi>)\<close> and \<open>\<psi>\<close> shows \<open>\<phi> \<equiv> \<chi>\<close>
  by (metis "&E"(2) "&I" "\<equiv>E"(1, 2) "\<equiv>I" "\<rightarrow>I" assms)
(* TODO: this is a slight variation from PLM *)
AOT_theorem df_simplify_2: assumes \<open>\<phi> \<equiv> (\<psi> & \<chi>)\<close> and \<open>\<chi>\<close> shows \<open>\<phi> \<equiv> \<psi>\<close>
  by (metis "&E"(1) "&I" "\<equiv>E"(1, 2) "\<equiv>I" "\<rightarrow>I" assms)
lemmas "\<equiv>S" = df_simplify_1 df_simplify_2

AOT_theorem rule_ui_1: assumes \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close> and \<open>\<tau>\<down>\<close> shows \<open>\<phi>{\<tau>}\<close>
  using "\<rightarrow>E" cqt_1[axiom_inst] assms by blast
AOT_theorem rule_ui_2_a: assumes \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close> shows \<open>\<phi>{\<beta>}\<close>
  by (simp add: rule_ui_1 cqt_2_const_var[axiom_inst] assms)
(* TODO: precise proviso in PLM *)
AOT_theorem rule_ui_2_b:
  assumes \<open>\<forall>F \<phi>{F}\<close> and \<open>INSTANCE_OF_CQT_2(\<psi>)\<close>
  shows \<open>\<phi>{[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<psi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]}\<close>
  by (simp add: rule_ui_1 cqt_2_lambda[axiom_inst] assms)
AOT_theorem rule_ui_3: assumes \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close> shows \<open>\<phi>{\<alpha>}\<close>
  by (simp add: rule_ui_2_a assms)
lemmas "\<forall>E" = rule_ui_1 rule_ui_2_a rule_ui_2_b rule_ui_3

AOT_theorem cqt_orig_1_a: \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<phi>{\<beta>}\<close> by (simp add: "\<forall>E"(2) "\<rightarrow>I")
AOT_theorem cqt_orig_1_b:
  assumes \<open>INSTANCE_OF_CQT_2(\<psi>)\<close>
  shows \<open>\<forall>F \<phi>{F} \<rightarrow> \<phi>{[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<psi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]}\<close>
  by (simp add: "\<forall>E"(3) "\<rightarrow>I" assms)
AOT_theorem cqt_orig_2: \<open>\<forall>\<alpha> (\<phi> \<rightarrow> \<psi>{\<alpha>}) \<rightarrow> (\<phi> \<rightarrow> \<forall>\<alpha> \<psi>{\<alpha>})\<close>
  by (metis "\<rightarrow>I" GEN vdash_properties_6 "\<forall>E"(4))
AOT_theorem cqt_orig_3: \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>}\<close> using cqt_orig_1_a .

(* TODO: work out difference to GEN *)
AOT_theorem universal: assumes \<open>for arbitrary \<beta>: \<phi>{\<beta>}\<close> shows \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close>
  using GEN assms .
lemmas "\<forall>I" = universal

(* TODO: rereplace-lem does not apply to the embedding *)

AOT_theorem cqt_basic_1: \<open>\<forall>\<alpha>\<forall>\<beta> \<phi>{\<alpha>,\<beta>} \<equiv> \<forall>\<beta>\<forall>\<alpha> \<phi>{\<alpha>,\<beta>}\<close>
  by (metis "\<equiv>I" "\<forall>E"(2) "\<forall>I" "\<rightarrow>I")

AOT_theorem cqt_basic_2: \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}) \<equiv> (\<forall>\<alpha>(\<phi>{\<alpha>} \<rightarrow> \<psi>{\<alpha>}) & \<forall>\<alpha>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>}))\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close>
  AOT_hence \<open>\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}\<close> for \<alpha> using "\<forall>E"(2) by blast
  AOT_hence \<open>\<phi>{\<alpha>} \<rightarrow> \<psi>{\<alpha>}\<close> and \<open>\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>}\<close> for \<alpha>
    using "\<equiv>E"(1,2) "\<rightarrow>I" by blast+
  AOT_thus \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<rightarrow> \<psi>{\<alpha>}) & \<forall>\<alpha>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close>
    by (auto intro: "&I" "\<forall>I")
next
  AOT_assume \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<rightarrow> \<psi>{\<alpha>}) & \<forall>\<alpha>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close>
  AOT_hence \<open>\<phi>{\<alpha>} \<rightarrow> \<psi>{\<alpha>}\<close> and \<open>\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>}\<close> for \<alpha>
    using "\<forall>E"(2) "&E" by blast+
  AOT_hence \<open>\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}\<close> for \<alpha>
    using "\<equiv>I" by blast
  AOT_thus \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close> by (auto intro: "\<forall>I")
qed

AOT_theorem cqt_basic_3: \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}) \<rightarrow> (\<forall>\<alpha> \<phi>{\<alpha>} \<equiv> \<forall>\<alpha> \<psi>{\<alpha>})\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close>
  AOT_hence 1: \<open>\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}\<close> for \<alpha> using "\<forall>E"(2) by blast
  {
    AOT_assume \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close>
    AOT_hence \<open>\<forall>\<alpha> \<psi>{\<alpha>}\<close> using 1 "\<forall>I" "\<forall>E"(4) "\<equiv>E" by metis
  }
  moreover {
    AOT_assume \<open>\<forall>\<alpha> \<psi>{\<alpha>}\<close>
    AOT_hence \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close> using 1 "\<forall>I" "\<forall>E"(4) "\<equiv>E" by metis
  }
  ultimately AOT_show \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<equiv> \<forall>\<alpha> \<psi>{\<alpha>}\<close>
    using "\<equiv>I" "\<rightarrow>I" by auto
qed

AOT_theorem cqt_basic_4: \<open>\<forall>\<alpha>(\<phi>{\<alpha>} & \<psi>{\<alpha>}) \<rightarrow> (\<forall>\<alpha> \<phi>{\<alpha>} & \<forall>\<alpha> \<psi>{\<alpha>})\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<forall>\<alpha>(\<phi>{\<alpha>} & \<psi>{\<alpha>})\<close>
  AOT_have \<open>\<phi>{\<alpha>}\<close> and \<open>\<psi>{\<alpha>}\<close> for \<alpha> using "\<forall>E"(2) 0 "&E" by blast+
  AOT_thus \<open>\<forall>\<alpha> \<phi>{\<alpha>} & \<forall>\<alpha> \<psi>{\<alpha>}\<close>
    by (auto intro: "\<forall>I" "&I")
qed

AOT_theorem cqt_basic_5: \<open>(\<forall>\<alpha>\<^sub>1...\<forall>\<alpha>\<^sub>n(\<phi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n})) \<rightarrow> \<phi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}\<close>
  using cqt_orig_3 by blast

AOT_theorem cqt_basic_6: \<open>\<forall>\<alpha>\<forall>\<alpha> \<phi>{\<alpha>} \<equiv> \<forall>\<alpha> \<phi>{\<alpha>}\<close>
  by (meson "\<equiv>I" "\<rightarrow>I" GEN cqt_orig_1_a)

AOT_theorem cqt_basic_7: \<open>(\<phi> \<rightarrow> \<forall>\<alpha> \<psi>{\<alpha>}) \<equiv> \<forall>\<alpha>(\<phi> \<rightarrow> \<psi>{\<alpha>})\<close>
  by (metis "\<rightarrow>I" vdash_properties_6 rule_ui_3 "\<equiv>I" GEN)

AOT_theorem cqt_basic_8: \<open>(\<forall>\<alpha> \<phi>{\<alpha>} \<or> \<forall>\<alpha> \<psi>{\<alpha>}) \<rightarrow> \<forall>\<alpha> (\<phi>{\<alpha>} \<or> \<psi>{\<alpha>})\<close>
  by (simp add: "\<or>I"(3) "\<rightarrow>I" GEN cqt_orig_1_a)

AOT_theorem cqt_basic_9: \<open>(\<forall>\<alpha> (\<phi>{\<alpha>} \<rightarrow> \<psi>{\<alpha>}) & \<forall>\<alpha> (\<psi>{\<alpha>} \<rightarrow> \<chi>{\<alpha>})) \<rightarrow> \<forall>\<alpha>(\<phi>{\<alpha>} \<rightarrow> \<chi>{\<alpha>})\<close>
proof -
  {
    AOT_assume \<open>\<forall>\<alpha> (\<phi>{\<alpha>} \<rightarrow> \<psi>{\<alpha>})\<close>
    moreover AOT_assume \<open>\<forall>\<alpha> (\<psi>{\<alpha>} \<rightarrow> \<chi>{\<alpha>})\<close>
    ultimately AOT_have \<open>\<phi>{\<alpha>} \<rightarrow> \<psi>{\<alpha>}\<close> and \<open>\<psi>{\<alpha>} \<rightarrow> \<chi>{\<alpha>}\<close> for \<alpha> using "\<forall>E" by blast+
    AOT_hence \<open>\<phi>{\<alpha>} \<rightarrow> \<chi>{\<alpha>}\<close> for \<alpha> by (metis "\<rightarrow>E" "\<rightarrow>I")
    AOT_hence \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<rightarrow> \<chi>{\<alpha>})\<close> using "\<forall>I" by fast
  }
  thus ?thesis using "&I" "\<rightarrow>I" "&E" by meson
qed

AOT_theorem cqt_basic_10: \<open>(\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}) & \<forall>\<alpha>(\<psi>{\<alpha>} \<equiv> \<chi>{\<alpha>})) \<rightarrow> \<forall>\<alpha> (\<phi>{\<alpha>} \<equiv> \<chi>{\<alpha>})\<close>
proof(rule "\<rightarrow>I"; rule "\<forall>I")
  fix \<beta>
  AOT_assume \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}) & \<forall>\<alpha>(\<psi>{\<alpha>} \<equiv> \<chi>{\<alpha>})\<close>
  AOT_hence \<open>\<phi>{\<beta>} \<equiv> \<psi>{\<beta>}\<close> and \<open>\<psi>{\<beta>} \<equiv> \<chi>{\<beta>}\<close> using "&E" "\<forall>E" by blast+
  AOT_thus \<open>\<phi>{\<beta>} \<equiv> \<chi>{\<beta>}\<close> using "\<equiv>I" "\<equiv>E" by blast
qed

AOT_theorem cqt_basic_11: \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}) \<equiv> \<forall>\<alpha> (\<psi>{\<alpha>} \<equiv> \<phi>{\<alpha>})\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close>
  {
    fix \<alpha>
    AOT_have \<open>\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}\<close> using 0 "\<forall>E" by blast
    AOT_hence \<open>\<psi>{\<alpha>} \<equiv> \<phi>{\<alpha>}\<close> using "\<equiv>I" "\<equiv>E" "\<rightarrow>I" "\<rightarrow>E" by metis
  }
  AOT_thus \<open>\<forall>\<alpha>(\<psi>{\<alpha>} \<equiv> \<phi>{\<alpha>})\<close> using "\<forall>I" by fast
next
  AOT_assume 0: \<open>\<forall>\<alpha>(\<psi>{\<alpha>} \<equiv> \<phi>{\<alpha>})\<close>
  {
    fix \<alpha>
    AOT_have \<open>\<psi>{\<alpha>} \<equiv> \<phi>{\<alpha>}\<close> using 0 "\<forall>E" by blast
    AOT_hence \<open>\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}\<close> using "\<equiv>I" "\<equiv>E" "\<rightarrow>I" "\<rightarrow>E" by metis
  }
  AOT_thus \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close> using "\<forall>I" by fast
qed

AOT_theorem cqt_basic_12: \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<forall>\<alpha> (\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close>
  by (simp add: "\<forall>E"(2) "\<rightarrow>I" GEN)

AOT_theorem cqt_basic_13: \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<equiv> \<forall>\<beta> \<phi>{\<beta>}\<close>
  using "\<equiv>I" "\<rightarrow>I" by blast

AOT_theorem cqt_basic_14: \<open>(\<forall>\<alpha>\<^sub>1...\<forall>\<alpha>\<^sub>n (\<phi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n} \<rightarrow> \<psi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n})) \<rightarrow> ((\<forall>\<alpha>\<^sub>1...\<forall>\<alpha>\<^sub>n \<phi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}) \<rightarrow> (\<forall>\<alpha>\<^sub>1...\<forall>\<alpha>\<^sub>n \<psi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}))\<close>
  using cqt_3[axiom_inst] by auto

AOT_theorem cqt_basic_15: \<open>(\<forall>\<alpha>\<^sub>1...\<forall>\<alpha>\<^sub>n (\<phi> \<rightarrow> \<psi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n})) \<rightarrow> (\<phi> \<rightarrow> (\<forall>\<alpha>\<^sub>1...\<forall>\<alpha>\<^sub>n \<psi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}))\<close>
  using cqt_orig_2 by auto

(* TODO: once more the same in the embedding... need to distinguish these better *)
AOT_theorem universal_cor: assumes \<open>for arbitrary \<beta>: \<phi>{\<beta>}\<close>  shows \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close>
  using GEN assms .

AOT_theorem existential_1: assumes \<open>\<phi>{\<tau>}\<close> and \<open>\<tau>\<down>\<close> shows \<open>\<exists>\<alpha> \<phi>{\<alpha>}\<close>
proof(rule raa_cor_1)
  AOT_assume \<open>\<not>\<exists>\<alpha> \<phi>{\<alpha>}\<close>
  AOT_hence \<open>\<forall>\<alpha> \<not>\<phi>{\<alpha>}\<close>
    using "\<equiv>\<^sub>d\<^sub>fI" AOT_exists RAA "&I" by blast
  AOT_hence \<open>\<not>\<phi>{\<tau>}\<close> using assms(2) "\<forall>E"(1) "\<rightarrow>E" by blast
  AOT_thus \<open>\<phi>{\<tau>} & \<not>\<phi>{\<tau>}\<close> using assms(1) "&I" by blast
qed

AOT_theorem existential_2_a: assumes \<open>\<phi>{\<beta>}\<close> shows \<open>\<exists>\<alpha> \<phi>{\<alpha>}\<close>
  using existential_1 cqt_2_const_var[axiom_inst] assms by blast

AOT_theorem existential_2_b:
  assumes \<open>\<phi>{[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<psi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]}\<close> and \<open>INSTANCE_OF_CQT_2(\<psi>)\<close>
  shows \<open>\<exists>\<alpha> \<phi>{\<alpha>}\<close>
  using existential_1 cqt_2_lambda[axiom_inst] assms by blast
lemmas "\<exists>I" = existential_1 existential_2_a existential_2_b 

AOT_theorem "instantiation":
  assumes \<open>for arbitrary \<beta>: \<phi>{\<beta>} \<^bold>\<turnstile> \<psi>\<close> and \<open>\<exists>\<alpha> \<phi>{\<alpha>}\<close>
  shows \<open>\<psi>\<close>
  by (metis (no_types, lifting) "\<equiv>\<^sub>d\<^sub>fE" GEN raa_cor_3 AOT_exists assms)
lemmas "\<exists>E" = "instantiation"

AOT_theorem cqt_further_1: \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<exists>\<alpha> \<phi>{\<alpha>}\<close>
  using "\<forall>E"(4) "\<exists>I"(2) "\<rightarrow>I" by metis

AOT_theorem cqt_further_2: \<open>\<not>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<exists>\<alpha> \<not>\<phi>{\<alpha>}\<close>
  using "\<forall>I" "\<exists>I"(2) "\<rightarrow>I" RAA by metis

AOT_theorem cqt_further_3: \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<not>\<exists>\<alpha> \<not>\<phi>{\<alpha>}\<close>
  using "\<forall>E"(4) "\<exists>E" "\<rightarrow>I" RAA by metis

AOT_theorem cqt_further_4: \<open>\<not>\<exists>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<forall>\<alpha> \<not>\<phi>{\<alpha>}\<close>
  using "\<forall>I" "\<exists>I"(2)"\<rightarrow>I" RAA by metis

AOT_theorem cqt_further_5: \<open>\<exists>\<alpha> (\<phi>{\<alpha>} & \<psi>{\<alpha>}) \<rightarrow> (\<exists>\<alpha> \<phi>{\<alpha>} & \<exists>\<alpha> \<psi>{\<alpha>})\<close>
  by (metis (no_types, lifting) "&E" "&I" "\<exists>E" "\<exists>I"(2) "\<rightarrow>I")

AOT_theorem cqt_further_6: \<open>\<exists>\<alpha> (\<phi>{\<alpha>} \<or> \<psi>{\<alpha>}) \<rightarrow> (\<exists>\<alpha> \<phi>{\<alpha>} \<or> \<exists>\<alpha> \<psi>{\<alpha>})\<close>
  by (metis (mono_tags, lifting) "\<exists>E" "\<exists>I"(2) "\<or>E"(3) "\<or>I"(1, 2) "\<rightarrow>I" RAA(2))

AOT_theorem cqt_further_7: \<open>\<exists>\<alpha> \<phi>{\<alpha>} \<equiv> \<exists>\<beta> \<phi>{\<beta>}\<close> (* TODO: vacuous in the embedding *)
  by (simp add: oth_class_taut_3_a)

AOT_theorem cqt_further_8: \<open>(\<forall>\<alpha> \<phi>{\<alpha>} & \<forall>\<alpha> \<psi>{\<alpha>}) \<rightarrow> \<forall>\<alpha> (\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close>
  by (metis (mono_tags, lifting) "&E" "\<equiv>I" "\<forall>E"(2) "\<rightarrow>I" GEN)

AOT_theorem cqt_further_9: \<open>(\<not>\<exists>\<alpha> \<phi>{\<alpha>} & \<not>\<exists>\<alpha> \<psi>{\<alpha>}) \<rightarrow> \<forall>\<alpha> (\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close>
  by (metis (mono_tags, lifting) "&E" "\<equiv>I" "\<exists>I"(2) "\<rightarrow>I" GEN raa_cor_4)

AOT_theorem cqt_further_10: \<open>(\<exists>\<alpha> \<phi>{\<alpha>} & \<not>\<exists>\<alpha> \<psi>{\<alpha>}) \<rightarrow> \<not>\<forall>\<alpha> (\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close>
proof(rule "\<rightarrow>I"; rule raa_cor_2)
  AOT_assume 0: \<open>\<exists>\<alpha> \<phi>{\<alpha>} & \<not>\<exists>\<alpha> \<psi>{\<alpha>}\<close>
  then AOT_obtain \<alpha> where \<open>\<phi>{\<alpha>}\<close> using "\<exists>E" "&E"(1) by metis
  moreover AOT_assume \<open>\<forall>\<alpha> (\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close>
  ultimately AOT_have \<open>\<psi>{\<alpha>}\<close> using "\<forall>E"(4) "\<equiv>E"(1) by blast
  AOT_hence \<open>\<exists>\<alpha> \<psi>{\<alpha>}\<close> using "\<exists>I" by blast
  AOT_thus \<open>\<exists>\<alpha> \<psi>{\<alpha>} & \<not>\<exists>\<alpha> \<psi>{\<alpha>}\<close> using 0 "&E"(2) "&I" by blast
qed

AOT_theorem cqt_further_11: \<open>\<exists>\<alpha>\<exists>\<beta> \<phi>{\<alpha>,\<beta>} \<equiv> \<exists>\<beta>\<exists>\<alpha> \<phi>{\<alpha>,\<beta>}\<close>
  using "\<equiv>I" "\<rightarrow>I" "\<exists>I"(2) "\<exists>E" by metis

AOT_theorem log_prop_prop_1: \<open>[\<lambda> \<phi>]\<down>\<close>
  using cqt_2_lambda0[axiom_inst] by auto

AOT_theorem log_prop_prop_2: \<open>\<phi>\<down>\<close>
  by (rule "\<equiv>\<^sub>d\<^sub>fI"[OF existence_3]; rule cqt_2_lambda[axiom_inst])
     (auto intro!: AOT_instance_of_cqt_2_intro)

AOT_theorem exist_nec: \<open>\<tau>\<down> \<rightarrow> \<box>\<tau>\<down>\<close>
proof -
  AOT_have \<open>\<forall>\<beta> \<box>\<beta>\<down>\<close>
    by (simp add: GEN RN cqt_2_const_var[axiom_inst])
  AOT_thus \<open>\<tau>\<down> \<rightarrow> \<box>\<tau>\<down>\<close>
    using cqt_1[axiom_inst] "\<rightarrow>E" by blast
qed

(* TODO: replace this mechanism by a "proof by types" command *)
class AOT_Term_id = AOT_Term +
  assumes "t=t-proper_1"[AOT]: \<open>[v \<Turnstile> \<tau> = \<tau>' \<rightarrow> \<tau>\<down>]\<close>
      and "t=t-proper_2"[AOT]: \<open>[v \<Turnstile> \<tau> = \<tau>' \<rightarrow> \<tau>'\<down>]\<close>

instance AOT_\<kappa> \<subseteq> AOT_Term_id
proof
  AOT_modally_strict {
    AOT_show \<open>\<kappa> = \<kappa>' \<rightarrow> \<kappa>\<down>\<close> for \<kappa> \<kappa>' :: 'a (* TODO: how to get rid of the fixes, resp. the warning without the type? *)
    proof(rule "\<rightarrow>I")
      AOT_assume \<open>\<kappa> = \<kappa>'\<close>
      AOT_hence \<open>O!\<kappa> \<or> A!\<kappa>\<close>
        by (rule "\<or>I"(3)[OF "\<equiv>\<^sub>d\<^sub>fE"[OF identity]])
           (meson "\<rightarrow>I" "\<or>I"(1) "&E"(1))+
      AOT_thus \<open>\<kappa>\<down>\<close>
        by (rule "\<or>E"(1))
           (metis cqt_5a[axiom_inst] "\<rightarrow>I" "\<rightarrow>E" "&E"(2))+
    qed
  }
next
  AOT_modally_strict {
    AOT_show \<open>\<kappa> = \<kappa>' \<rightarrow> \<kappa>'\<down>\<close> for \<kappa> \<kappa>' :: 'a
    proof(rule "\<rightarrow>I")
      AOT_assume \<open>\<kappa> = \<kappa>'\<close>
      AOT_hence \<open>O!\<kappa>' \<or> A!\<kappa>'\<close>
        by (rule "\<or>I"(3)[OF "\<equiv>\<^sub>d\<^sub>fE"[OF identity]])
           (meson "\<rightarrow>I" "\<or>I" "&E")+
      AOT_thus \<open>\<kappa>'\<down>\<close>
        by (rule "\<or>E"(1))
           (metis cqt_5a[axiom_inst] "\<rightarrow>I" "\<rightarrow>E" "&E"(2))+
    qed
  }
qed

instance rel :: (AOT_\<kappa>s) AOT_Term_id
proof
  AOT_modally_strict {
    AOT_show \<open>\<Pi> = \<Pi>' \<rightarrow> \<Pi>\<down>\<close> for \<Pi> \<Pi>' :: \<open><'a>\<close> (* TODO: how to get rid of the fixes? *)
    proof(rule "\<rightarrow>I")
      AOT_assume \<open>\<Pi> = \<Pi>'\<close>
      AOT_thus \<open>\<Pi>\<down>\<close> using "\<equiv>\<^sub>d\<^sub>fE"[OF p_identity_2_generic[of \<Pi> \<Pi>']] "&E" by blast
    qed
  }
next
  AOT_modally_strict {
    AOT_show \<open>\<Pi> = \<Pi>' \<rightarrow> \<Pi>'\<down>\<close> for \<Pi> \<Pi>' :: \<open><'a>\<close> (* TODO: how to get rid of the fixes? *)
    proof(rule "\<rightarrow>I")
      AOT_assume \<open>\<Pi> = \<Pi>'\<close>
      AOT_thus \<open>\<Pi>'\<down>\<close> using "\<equiv>\<^sub>d\<^sub>fE"[OF p_identity_2_generic[of \<Pi> \<Pi>']] "&E" by blast
    qed
  }
qed

instance \<o> :: AOT_Term_id
proof
  AOT_modally_strict {
    fix \<phi> \<psi>
    AOT_show \<open>\<phi> = \<psi> \<rightarrow> \<phi>\<down>\<close>
    proof(rule "\<rightarrow>I")
      AOT_assume \<open>\<phi> = \<psi>\<close>
      AOT_thus \<open>\<phi>\<down>\<close> using "\<equiv>\<^sub>d\<^sub>fE"[OF p_identity_3[of \<phi> \<psi>]] "&E" by blast
    qed
  }
next
  AOT_modally_strict {
    fix \<phi> \<psi>
    AOT_show \<open>\<phi> = \<psi> \<rightarrow> \<psi>\<down>\<close>
    proof(rule "\<rightarrow>I")
      AOT_assume \<open>\<phi> = \<psi>\<close>
      AOT_thus \<open>\<psi>\<down>\<close> using "\<equiv>\<^sub>d\<^sub>fE"[OF p_identity_3[of \<phi> \<psi>]] "&E" by blast
    qed
  }
qed

(* TODO: this is the end of the "proof by types" and makes the results available on new theorems *)
AOT_add_term_sort AOT_Term_id

AOT_theorem id_rel_nec_equiv_1: \<open>\<Pi> = \<Pi>' \<rightarrow> \<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([\<Pi>]x\<^sub>1...x\<^sub>n \<equiv> [\<Pi>']x\<^sub>1...x\<^sub>n)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume assumption: \<open>\<Pi> = \<Pi>'\<close>
  AOT_hence \<open>\<Pi>\<down>\<close> and \<open>\<Pi>'\<down>\<close>
    using "t=t-proper_1" "t=t-proper_2" MP by blast+
  moreover AOT_have \<open>\<forall>F\<forall>G (F = G \<rightarrow> ((\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([F]x\<^sub>1...x\<^sub>n \<equiv> [F]x\<^sub>1...x\<^sub>n)) \<rightarrow> \<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([F]x\<^sub>1...x\<^sub>n \<equiv> [G]x\<^sub>1...x\<^sub>n)))\<close>
    apply (rule GEN)+ using l_identity[axiom_inst] by force
  ultimately AOT_have \<open>\<Pi> = \<Pi>' \<rightarrow> ((\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([\<Pi>]x\<^sub>1...x\<^sub>n \<equiv> [\<Pi>]x\<^sub>1...x\<^sub>n)) \<rightarrow> \<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([\<Pi>]x\<^sub>1...x\<^sub>n \<equiv> [\<Pi>']x\<^sub>1...x\<^sub>n))\<close>
    using "\<forall>E"(1) by blast
  AOT_hence \<open>(\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([\<Pi>]x\<^sub>1...x\<^sub>n \<equiv> [\<Pi>]x\<^sub>1...x\<^sub>n)) \<rightarrow> \<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([\<Pi>]x\<^sub>1...x\<^sub>n \<equiv> [\<Pi>']x\<^sub>1...x\<^sub>n)\<close>
    using assumption "\<rightarrow>E" by blast
  moreover AOT_have \<open>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([\<Pi>]x\<^sub>1...x\<^sub>n \<equiv> [\<Pi>]x\<^sub>1...x\<^sub>n)\<close>
    by (simp add: RN oth_class_taut_3_a universal_cor)
  ultimately AOT_show \<open>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([\<Pi>]x\<^sub>1...x\<^sub>n \<equiv> [\<Pi>']x\<^sub>1...x\<^sub>n)\<close>
    using "\<rightarrow>E" by blast
qed

AOT_theorem id_rel_nec_equiv_2: \<open>\<phi> = \<psi> \<rightarrow> \<box>(\<phi> \<equiv> \<psi>)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume assumption: \<open>\<phi> = \<psi>\<close>
  AOT_hence \<open>\<phi>\<down>\<close> and \<open>\<psi>\<down>\<close>
    using "t=t-proper_1" "t=t-proper_2" MP by blast+
  moreover AOT_have \<open>\<forall>p\<forall>q (p = q \<rightarrow> ((\<box>(p \<equiv> p) \<rightarrow> \<box>(p \<equiv> q))))\<close>
    apply (rule GEN)+ using l_identity[axiom_inst] by force
  ultimately AOT_have \<open>\<phi> = \<psi> \<rightarrow> (\<box>(\<phi> \<equiv> \<phi>) \<rightarrow> \<box>(\<phi> \<equiv> \<psi>))\<close>
    using "\<forall>E"(1) by blast
  AOT_hence \<open>\<box>(\<phi> \<equiv> \<phi>) \<rightarrow> \<box>(\<phi> \<equiv> \<psi>)\<close>
    using assumption "\<rightarrow>E" by blast
  moreover AOT_have \<open>\<box>(\<phi> \<equiv> \<phi>)\<close>
    by (simp add: RN oth_class_taut_3_a universal_cor)
  ultimately AOT_show \<open>\<box>(\<phi> \<equiv> \<psi>)\<close>
    using "\<rightarrow>E" by blast
qed

AOT_theorem "rule=E": assumes \<open>\<phi>{\<tau>}\<close> and \<open>\<tau> = \<sigma>\<close> shows \<open>\<phi>{\<sigma>}\<close>
proof -
  AOT_have \<open>\<tau>\<down>\<close> and \<open>\<sigma>\<down>\<close> using assms(2) "t=t-proper_1" "t=t-proper_2" "\<rightarrow>E" by blast+
  moreover AOT_have \<open>\<forall>\<alpha>\<forall>\<beta>(\<alpha> = \<beta> \<rightarrow> (\<phi>{\<alpha>} \<rightarrow> \<phi>{\<beta>}))\<close>
    apply (rule GEN)+ using l_identity[axiom_inst] by blast
  ultimately AOT_have \<open>\<tau> = \<sigma> \<rightarrow> (\<phi>{\<tau>} \<rightarrow> \<phi>{\<sigma>})\<close>
    using "\<forall>E"(1) by blast
  AOT_thus \<open>\<phi>{\<sigma>}\<close> using assms "\<rightarrow>E" by blast
qed
lemmas "=E" = "rule=E"

AOT_theorem propositions_lemma_1: \<open>[\<lambda> \<phi>] = \<phi>\<close>
proof -
  AOT_have \<open>\<phi>\<down>\<close> by (simp add: log_prop_prop_2)
  moreover AOT_have \<open>\<forall>p [\<lambda> p] = p\<close> using lambda_predicates_3_b[axiom_inst] "\<forall>I" by fast
  ultimately AOT_show \<open>[\<lambda> \<phi>] = \<phi>\<close>
    using "\<forall>E" by blast
qed

AOT_theorem propositions_lemma_2: \<open>[\<lambda> \<phi>] \<equiv> \<phi>\<close>
proof -
  AOT_have \<open>[\<lambda> \<phi>] \<equiv> [\<lambda> \<phi>]\<close> by (simp add: oth_class_taut_3_a)
  AOT_thus \<open>[\<lambda> \<phi>] \<equiv> \<phi>\<close> using propositions_lemma_1 "=E" by blast
qed

(* propositions_lemma_3 through propositions_lemma_5 do not apply *)

AOT_theorem propositions_lemma_6: \<open>(\<phi> \<equiv> \<psi>) \<equiv> ([\<lambda> \<phi>] \<equiv> [\<lambda> \<psi>])\<close>
  by (metis intro_elim_3_a intro_elim_3_e oth_class_taut_2_f propositions_lemma_2)

(* dr_alphabetic_rules does not apply *)

AOT_theorem oa_exist_1: \<open>O!\<down>\<close>
proof -
  AOT_have \<open>[\<lambda>x \<diamond>[E!]x]\<down>\<close>
    by (rule cqt_2_lambda[axiom_inst]) (auto intro!: AOT_instance_of_cqt_2_intro) (* TODO: make this a proof method *)
  AOT_hence 1: \<open>O! = [\<lambda>x \<diamond>[E!]x]\<close> using df_rules_terms_2[OF oa_1, THEN "&E"(1)] "\<rightarrow>E" by blast
  AOT_show \<open>O!\<down>\<close> using "t=t-proper_1"[THEN "\<rightarrow>E", OF 1] by simp
qed

AOT_theorem oa_exist_2: \<open>A!\<down>\<close>
proof -
  AOT_have \<open>[\<lambda>x \<not>\<diamond>[E!]x]\<down>\<close>
    by (rule cqt_2_lambda[axiom_inst]) (auto intro!: AOT_instance_of_cqt_2_intro) (* TODO: make this a proof method *)
  AOT_hence 1: \<open>A! = [\<lambda>x \<not>\<diamond>[E!]x]\<close> using df_rules_terms_2[OF oa_2, THEN "&E"(1)] "\<rightarrow>E" by blast
  AOT_show \<open>A!\<down>\<close> using "t=t-proper_1"[THEN "\<rightarrow>E", OF 1] by simp
qed

AOT_theorem oa_exist_3: \<open>O!x \<or> A!x\<close>
proof(rule raa_cor_1)
  AOT_assume \<open>\<not>(O!x \<or> A!x)\<close>
  AOT_hence A: \<open>\<not>O!x\<close> and B: \<open>\<not>A!x\<close>
    using con_dis_taut_3 modus_tollens_1 con_dis_i_e_3_b raa_cor_5 by blast+
  AOT_have C: \<open>O! = [\<lambda>x \<diamond>[E!]x]\<close>
    by (rule df_rules_terms_2[OF oa_1, THEN "&E"(1), THEN "\<rightarrow>E"]; rule cqt_2_lambda[axiom_inst])
       (auto intro!: AOT_instance_of_cqt_2_intro)
  AOT_have D: \<open>A! = [\<lambda>x \<not>\<diamond>[E!]x]\<close>
    by (rule df_rules_terms_2[OF oa_2, THEN "&E"(1), THEN "\<rightarrow>E"]; rule cqt_2_lambda[axiom_inst])
       (auto intro!: AOT_instance_of_cqt_2_intro)
  AOT_have E: \<open>\<not>[\<lambda>x \<diamond>[E!]x]x\<close>
    using A C "=E" by fast
  AOT_have F: \<open>\<not>[\<lambda>x \<not>\<diamond>[E!]x]x\<close>
    using B D "=E" by fast
  AOT_have G: \<open>[\<lambda>x \<diamond>[E!]x]x \<equiv> \<diamond>[E!]x\<close>
    by (rule lambda_predicates_2[axiom_inst, THEN "\<rightarrow>E"]; rule cqt_2_lambda[axiom_inst])
       (auto intro!: AOT_instance_of_cqt_2_intro)
  AOT_have H: \<open>[\<lambda>x \<not>\<diamond>[E!]x]x \<equiv> \<not>\<diamond>[E!]x\<close>
    by (rule lambda_predicates_2[axiom_inst, THEN "\<rightarrow>E"]; rule cqt_2_lambda[axiom_inst])
       (auto intro!: AOT_instance_of_cqt_2_intro)
  AOT_show \<open>\<not>\<diamond>[E!]x & \<not>\<not>\<diamond>[E!]x\<close> using G E "\<equiv>E" H F "\<equiv>E" "&I" by metis
qed

AOT_theorem p_identity_thm2_1: \<open>F = G \<equiv> \<box>\<forall>x(x[F] \<equiv> x[G])\<close>
proof -
  AOT_have \<open>F = G \<equiv> F\<down> & G\<down> & \<box>\<forall>x(x[F] \<equiv> x[G])\<close>
    using p_identity df_rules_formulas_1 df_rules_formulas_2 "\<rightarrow>E" "&E" "\<equiv>I" "\<rightarrow>I" by blast
  moreover AOT_have \<open>F\<down>\<close> and \<open>G\<down>\<close>
    by (auto simp: cqt_2_const_var[axiom_inst])
  ultimately AOT_show \<open>F = G \<equiv> \<box>\<forall>x(x[F] \<equiv> x[G])\<close>
    using df_simplify_1 "&I" by blast
qed

AOT_theorem p_identity_thm2_2_a: \<open>F = G \<equiv> \<forall>y\<^sub>1([\<lambda>x [F]xy\<^sub>1] = [\<lambda>x [G]xy\<^sub>1] & [\<lambda>x [F]y\<^sub>1x] = [\<lambda>x [G]y\<^sub>1x])\<close>
proof -
  AOT_have \<open>F = G \<equiv> F\<down> & G\<down> & \<forall>y\<^sub>1([\<lambda>x [F]xy\<^sub>1] = [\<lambda>x [G]xy\<^sub>1] & [\<lambda>x [F]y\<^sub>1x] = [\<lambda>x [G]y\<^sub>1x])\<close>
    using p_identity_2_a df_rules_formulas_1 df_rules_formulas_2 "\<rightarrow>E" "&E" "\<equiv>I" "\<rightarrow>I" by blast
  moreover AOT_have \<open>F\<down>\<close> and \<open>G\<down>\<close>
    by (auto simp: cqt_2_const_var[axiom_inst])
  ultimately show ?thesis
    using df_simplify_1 "&I" by blast
qed
    
AOT_theorem p_identity_thm2_2_b: \<open>F = G \<equiv> \<forall>y\<^sub>1\<forall>y\<^sub>2([\<lambda>x [F]xy\<^sub>1y\<^sub>2] = [\<lambda>x [G]xy\<^sub>1y\<^sub>2] & [\<lambda>x [F]y\<^sub>1xy\<^sub>2] = [\<lambda>x [G]y\<^sub>1xy\<^sub>2] & [\<lambda>x [F]y\<^sub>1y\<^sub>2x] = [\<lambda>x [G]y\<^sub>1y\<^sub>2x])\<close>
proof -
  AOT_have \<open>F = G \<equiv> F\<down> & G\<down> & \<forall>y\<^sub>1\<forall>y\<^sub>2([\<lambda>x [F]xy\<^sub>1y\<^sub>2] = [\<lambda>x [G]xy\<^sub>1y\<^sub>2] & [\<lambda>x [F]y\<^sub>1xy\<^sub>2] = [\<lambda>x [G]y\<^sub>1xy\<^sub>2] & [\<lambda>x [F]y\<^sub>1y\<^sub>2x] = [\<lambda>x [G]y\<^sub>1y\<^sub>2x])\<close>
    using p_identity_2_b df_rules_formulas_1 df_rules_formulas_2 "\<rightarrow>E" "&E" "\<equiv>I" "\<rightarrow>I" by blast
  moreover AOT_have \<open>F\<down>\<close> and \<open>G\<down>\<close>
    by (auto simp: cqt_2_const_var[axiom_inst])
  ultimately show ?thesis
    using df_simplify_1 "&I" by blast
qed

AOT_theorem p_identity_thm2_2_c: \<open>F = G \<equiv> \<forall>y\<^sub>1\<forall>y\<^sub>2\<forall>y\<^sub>3([\<lambda>x [F]xy\<^sub>1y\<^sub>2y\<^sub>3] = [\<lambda>x [G]xy\<^sub>1y\<^sub>2y\<^sub>3] & [\<lambda>x [F]y\<^sub>1xy\<^sub>2y\<^sub>3] = [\<lambda>x [G]y\<^sub>1xy\<^sub>2y\<^sub>3] & [\<lambda>x [F]y\<^sub>1y\<^sub>2xy\<^sub>3] = [\<lambda>x [G]y\<^sub>1y\<^sub>2xy\<^sub>3] & [\<lambda>x [F]y\<^sub>1y\<^sub>2y\<^sub>3x] = [\<lambda>x [G]y\<^sub>1y\<^sub>2y\<^sub>3x])\<close>
proof -
  AOT_have \<open>F = G \<equiv> F\<down> & G\<down> & \<forall>y\<^sub>1\<forall>y\<^sub>2\<forall>y\<^sub>3([\<lambda>x [F]xy\<^sub>1y\<^sub>2y\<^sub>3] = [\<lambda>x [G]xy\<^sub>1y\<^sub>2y\<^sub>3] & [\<lambda>x [F]y\<^sub>1xy\<^sub>2y\<^sub>3] = [\<lambda>x [G]y\<^sub>1xy\<^sub>2y\<^sub>3] & [\<lambda>x [F]y\<^sub>1y\<^sub>2xy\<^sub>3] = [\<lambda>x [G]y\<^sub>1y\<^sub>2xy\<^sub>3] & [\<lambda>x [F]y\<^sub>1y\<^sub>2y\<^sub>3x] = [\<lambda>x [G]y\<^sub>1y\<^sub>2y\<^sub>3x])\<close>
    using p_identity_2_c df_rules_formulas_1 df_rules_formulas_2 "\<rightarrow>E" "&E" "\<equiv>I" "\<rightarrow>I" by blast
  moreover AOT_have \<open>F\<down>\<close> and \<open>G\<down>\<close>
    by (auto simp: cqt_2_const_var[axiom_inst])
  ultimately show ?thesis
    using df_simplify_1 "&I" by blast
qed

AOT_theorem p_identity_thm2_2_generic:
  \<open>F = G \<equiv> \<forall>x\<^sub>1...\<forall>x\<^sub>n \<guillemotleft>AOT_sem_proj_id x\<^sub>1x\<^sub>n (\<lambda> \<tau> . \<guillemotleft>[F]\<tau>\<guillemotright>) (\<lambda> \<tau> . \<guillemotleft>[G]\<tau>\<guillemotright>)\<guillemotright>\<close>
proof -
  AOT_have \<open>F = G \<equiv> F\<down> & G\<down> & \<forall>x\<^sub>1...\<forall>x\<^sub>n \<guillemotleft>AOT_sem_proj_id x\<^sub>1x\<^sub>n (\<lambda> \<tau> . \<guillemotleft>[F]\<tau>\<guillemotright>) (\<lambda> \<tau> . \<guillemotleft>[G]\<tau>\<guillemotright>)\<guillemotright>\<close>
    using p_identity_2_generic df_rules_formulas_1 df_rules_formulas_2 "\<rightarrow>E" "&E" "\<equiv>I" "\<rightarrow>I" by blast
  moreover AOT_have \<open>F\<down>\<close> and \<open>G\<down>\<close>
    by (auto simp: cqt_2_const_var[axiom_inst])
  ultimately show ?thesis
    using df_simplify_1 "&I" by blast
qed

AOT_theorem p_identity_thm2_3:
  \<open>p = q \<equiv> [\<lambda>x p] = [\<lambda>x q]\<close>
proof -
  AOT_have \<open>p = q \<equiv> p\<down> & q\<down> & [\<lambda>x p] = [\<lambda>x q]\<close>
    using p_identity_3 df_rules_formulas_1 df_rules_formulas_2 "\<rightarrow>E" "&E" "\<equiv>I" "\<rightarrow>I" by blast
  moreover AOT_have \<open>p\<down>\<close> and \<open>q\<down>\<close>
    by (auto simp: cqt_2_const_var[axiom_inst])
  ultimately show ?thesis
    using df_simplify_1 "&I" by blast
qed

class AOT_Term_id_2 = AOT_Term_id + assumes id_eq_1: \<open>[v \<Turnstile> \<alpha> = \<alpha>]\<close>

instance AOT_\<kappa> \<subseteq> AOT_Term_id_2
proof
  AOT_modally_strict {
    fix x :: "'a AOT_var"
    {
      AOT_assume \<open>O!x\<close>
      moreover AOT_have \<open>\<box>\<forall>F([F]x \<equiv> [F]x)\<close>
        using RN GEN oth_class_taut_3_a by fast
      ultimately AOT_have \<open>O!x & O!x & \<box>\<forall>F([F]x \<equiv> [F]x)\<close> using "&I" by simp
    }
    moreover {
      AOT_assume \<open>A!x\<close>
      moreover AOT_have \<open>\<box>\<forall>F(x[F] \<equiv> x[F])\<close>
        using RN GEN oth_class_taut_3_a by fast
      ultimately AOT_have \<open>A!x & A!x & \<box>\<forall>F(x[F] \<equiv> x[F])\<close> using "&I" by simp
    }
    ultimately AOT_have \<open>(O!x & O!x & \<box>\<forall>F([F]x \<equiv> [F]x)) \<or> (A!x & A!x & \<box>\<forall>F(x[F] \<equiv> x[F]))\<close>
      using oa_exist_3 con_dis_i_e_3_a con_dis_i_e_3_b con_dis_i_e_4_c raa_cor_1 by blast
    AOT_thus \<open>x = x\<close>
      using identity[THEN df_rules_formulas_2] "\<rightarrow>E" by blast
  }
qed

instance rel :: (AOT_\<kappa>s) AOT_Term_id_2
proof
  AOT_modally_strict {
    fix F :: "<'a> AOT_var"
    AOT_have 0: \<open>[\<lambda>x\<^sub>1...x\<^sub>n [F]x\<^sub>1...x\<^sub>n] = F\<close>
      by (simp add: lambda_predicates_3[axiom_inst])
    AOT_have \<open>[\<lambda>x\<^sub>1...x\<^sub>n [F]x\<^sub>1...x\<^sub>n]\<down>\<close>
      by (rule cqt_2_lambda[axiom_inst])
         (auto intro: AOT_instance_of_cqt_2_intro)
    AOT_hence \<open>[\<lambda>x\<^sub>1...x\<^sub>n [F]x\<^sub>1...x\<^sub>n] = [\<lambda>x\<^sub>1...x\<^sub>n [F]x\<^sub>1...x\<^sub>n]\<close>
      using lambda_predicates_1[axiom_inst] "\<rightarrow>E" by blast
    AOT_show \<open>F = F\<close> using "=E" 0 by force 
  }
qed

instance \<o> :: AOT_Term_id_2
proof
  AOT_modally_strict {
    fix p :: "\<o> AOT_var"
    AOT_have 0: \<open>[\<lambda> p] = p\<close>
      by (simp add: lambda_predicates_3_b[axiom_inst])
    AOT_have \<open>[\<lambda> p]\<down>\<close>
      by (rule cqt_2_lambda0[axiom_inst])
    AOT_hence \<open>[\<lambda> p] = [\<lambda> p]\<close>
      using lambda_predicates_1_b[axiom_inst] "\<rightarrow>E" by blast
    AOT_show \<open>p = p\<close> using "=E" 0 by force
  }
qed

AOT_add_term_sort AOT_Term_id_2

(* TODO: Interestingly, this doesn't depend on id_eq_1 at all! *)
AOT_theorem id_eq_2: \<open>\<alpha> = \<beta> \<rightarrow> \<beta> = \<alpha>\<close>
(*
  TODO: look at this proof generated using:
        including AOT_no_atp sledgehammer[isar_proofs = true]
proof -
  have "(\<exists>\<phi>. [v \<Turnstile> ~\<beta> = \<alpha> \<rightarrow> ~\<phi>] \<and> [v \<Turnstile> \<alpha> = \<beta> \<rightarrow> \<phi>]) \<or> (\<exists>\<phi>. \<not> [v \<Turnstile> \<phi>{\<alpha>} \<rightarrow> \<phi>{\<beta>}])"
    by meson
  then show ?thesis
    by (meson contraposition_2_a ded_thm_cor_1 deduction_theorem l_identity useful_tautologies_1)
qed
*)
(*  by (meson "rule=E" deduction_theorem) *)
proof (rule "\<rightarrow>I")
  AOT_assume \<open>\<alpha> = \<beta>\<close>
  moreover AOT_have \<open>\<beta> = \<beta>\<close> using calculation "=E"[of v "\<lambda> \<tau> . \<guillemotleft>\<tau> = \<beta>\<guillemotright>" "AOT_term_of_var \<alpha>" "AOT_term_of_var \<beta>"] by blast
  moreover AOT_have \<open>\<alpha> = \<alpha> \<rightarrow> \<alpha> = \<alpha>\<close> using if_p_then_p by blast
  ultimately AOT_show \<open>\<beta> = \<alpha>\<close>
    using "\<rightarrow>E" "\<rightarrow>I" "=E"[of v "\<lambda> \<tau> . \<guillemotleft>(\<tau> = \<tau>) \<rightarrow> (\<tau> = \<alpha>)\<guillemotright>" "AOT_term_of_var \<alpha>" "AOT_term_of_var \<beta>"] by blast
qed

AOT_theorem id_eq_3: \<open>\<alpha> = \<beta> & \<beta> = \<gamma> \<rightarrow> \<alpha> = \<gamma>\<close>
  using "rule=E" "\<rightarrow>I" "&E" by blast

AOT_theorem id_eq_4: \<open>\<alpha> = \<beta> \<equiv> \<forall>\<gamma> (\<alpha> = \<gamma> \<equiv> \<beta> = \<gamma>)\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<alpha> = \<beta>\<close>
  AOT_hence 1: \<open>\<beta> = \<alpha>\<close> using id_eq_2 "\<rightarrow>E" by blast
  AOT_show \<open>\<forall>\<gamma> (\<alpha> = \<gamma> \<equiv> \<beta> = \<gamma>)\<close>
    by (rule GEN) (metis "\<equiv>I" "\<rightarrow>I" 0 "1" "rule=E")
next
  AOT_assume \<open>\<forall>\<gamma> (\<alpha> = \<gamma> \<equiv> \<beta> = \<gamma>)\<close>
  AOT_hence \<open>\<alpha> = \<alpha> \<equiv> \<beta> = \<alpha>\<close> using "\<forall>E"(2) by blast
  AOT_hence \<open>\<alpha> = \<alpha> \<rightarrow> \<beta> = \<alpha>\<close> using "\<equiv>E"(1) "\<rightarrow>I" by blast
  AOT_hence \<open>\<beta> = \<alpha>\<close> using id_eq_1 "\<rightarrow>E" by blast
  AOT_thus \<open>\<alpha> = \<beta>\<close> using id_eq_2 "\<rightarrow>E" by blast
qed

AOT_theorem "rule=I_1": assumes \<open>\<tau>\<down>\<close> shows \<open>\<tau> = \<tau>\<close>
proof -
  AOT_have \<open>\<forall>\<alpha> (\<alpha> = \<alpha>)\<close>
    by (rule GEN) (metis id_eq_1)
  AOT_thus \<open>\<tau> = \<tau>\<close> using assms "\<forall>E" by blast
qed

AOT_theorem "rule=I_2": assumes \<open>INSTANCE_OF_CQT_2(\<phi>)\<close> shows "[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}] = [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]"
proof -
  AOT_have \<open>\<forall>\<alpha> (\<alpha> = \<alpha>)\<close>
    by (rule GEN) (metis id_eq_1)
  moreover AOT_have \<open>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down>\<close> using assms by (rule cqt_2_lambda[axiom_inst])
  ultimately AOT_show \<open>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}] = [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<close> using assms "\<forall>E" by blast
qed

lemmas "=I" = "rule=I_1" id_eq_1 "rule=I_2"

AOT_theorem rule_id_def_1:
  assumes \<open>\<tau>{\<alpha>\<^sub>1...\<alpha>\<^sub>n} =\<^sub>d\<^sub>f \<sigma>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}\<close> and \<open>\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down>\<close>
  shows \<open>\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n} = \<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<close>
proof -
  AOT_have \<open>\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down> \<rightarrow> \<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n} = \<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<close>
    using df_rules_terms_1 assms(1) "&E" by blast
  AOT_thus \<open>\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n} = \<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<close>
    using assms(2) "\<rightarrow>E" by blast
qed

AOT_theorem rule_id_def_1_b:
  assumes \<open>\<tau> =\<^sub>d\<^sub>f \<sigma>\<close> and \<open>\<sigma>\<down>\<close>
  shows \<open>\<tau> = \<sigma>\<close>
proof -
  AOT_have \<open>\<sigma>\<down> \<rightarrow> \<tau> = \<sigma>\<close>
    using df_rules_terms_2 assms(1) "&E" by blast
  AOT_thus \<open>\<tau> = \<sigma>\<close>
    using assms(2) "\<rightarrow>E" by blast
qed

AOT_theorem rule_id_def_2_a:
  assumes \<open>\<tau>{\<alpha>\<^sub>1...\<alpha>\<^sub>n} =\<^sub>d\<^sub>f \<sigma>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}\<close> and \<open>\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down>\<close> and \<open>\<phi>{\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n}}\<close>
  shows \<open>\<phi>{\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}}\<close>
proof -
  AOT_have \<open>\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n} = \<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<close> using rule_id_def_1 assms(1,2) by blast
  AOT_thus \<open>\<phi>{\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}}\<close> using assms(3) "=E" by blast
qed

AOT_theorem rule_id_def_2_a':
  assumes \<open>\<tau> =\<^sub>d\<^sub>f \<sigma>\<close> and \<open>\<sigma>\<down>\<close> and \<open>\<phi>{\<tau>}\<close>
  shows \<open>\<phi>{\<sigma>}\<close>
proof -
  AOT_have \<open>\<tau> = \<sigma>\<close> using rule_id_def_1_b assms(1,2) by blast
  AOT_thus \<open>\<phi>{\<sigma>}\<close> using assms(3) "=E" by blast
qed

lemmas "=\<^sub>d\<^sub>fE" = rule_id_def_2_a rule_id_def_2_a'

AOT_theorem rule_id_def_2_b:
  assumes \<open>\<tau>{\<alpha>\<^sub>1...\<alpha>\<^sub>n} =\<^sub>d\<^sub>f \<sigma>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}\<close> and \<open>\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down>\<close> and \<open>\<phi>{\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}}\<close>
  shows \<open>\<phi>{\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n}}\<close>
proof -
  AOT_have \<open>\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n} = \<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<close> using rule_id_def_1 assms(1,2) by blast
  AOT_hence \<open>\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n} = \<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<close>
    using "=E" "=I"(1) "t=t-proper_1" "\<rightarrow>E" by fast
  AOT_thus \<open>\<phi>{\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n}}\<close> using assms(3) "=E" by blast
qed

AOT_theorem rule_id_def_2_b':
  assumes \<open>\<tau> =\<^sub>d\<^sub>f \<sigma>\<close> and \<open>\<sigma>\<down>\<close> and \<open>\<phi>{\<sigma>}\<close>
  shows \<open>\<phi>{\<tau>}\<close>
proof -
  AOT_have \<open>\<tau> = \<sigma>\<close> using rule_id_def_1_b assms(1,2) by blast
  AOT_hence \<open>\<sigma> = \<tau>\<close>
    using "=E" "=I"(1) "t=t-proper_1" "\<rightarrow>E" by fast
  AOT_thus \<open>\<phi>{\<tau>}\<close> using assms(3) "=E" by blast
qed

lemmas "=\<^sub>d\<^sub>fI" = rule_id_def_2_b rule_id_def_2_b'

AOT_theorem free_thms_1: \<open>\<tau>\<down> \<equiv> \<exists>\<beta> (\<beta> = \<tau>)\<close>
  by (metis "\<exists>E" "rule=I_1" "t=t-proper_2" "\<rightarrow>I" "\<exists>I"(1) "\<equiv>I" "\<rightarrow>E")

AOT_theorem free_thms_2: \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> (\<exists>\<beta> (\<beta> = \<tau>) \<rightarrow> \<phi>{\<tau>})\<close>
  by (metis "\<exists>E" "rule=E" cqt_2_const_var[axiom_inst] "\<rightarrow>I" "\<forall>E"(1))

AOT_theorem free_thms_3_a: \<open>\<exists>\<beta> (\<beta> = \<alpha>)\<close>
  by (meson "\<exists>I"(2) id_eq_1)

AOT_theorem free_thms_3_b: assumes \<open>INSTANCE_OF_CQT_2(\<phi>)\<close> shows \<open>\<exists>\<beta> (\<beta> = [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}])\<close>
  by (meson "=I"(3) assms cqt_2_lambda[axiom_inst] existential_1)

AOT_theorem free_thms_4_a: \<open>([\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n \<or> \<kappa>\<^sub>1...\<kappa>\<^sub>n[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<Pi>)\<close>
  by (metis "rule=I_1" "&E"(1) "\<or>E"(1) cqt_5a[axiom_inst] cqt_5b[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))

(* TODO: this is a rather weird way to formulate this and we don't have tuple-existential-elimination
         or tuple-equality-elimination in the theory... Splitting them is also a bit unfortunate, though.*)
AOT_theorem free_thms_4_b: \<open>([\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n \<or> \<kappa>\<^sub>1...\<kappa>\<^sub>n[\<Pi>]) \<rightarrow> \<exists>\<beta>\<^sub>1...\<exists>\<beta>\<^sub>n (\<beta>\<^sub>1...\<beta>\<^sub>n = \<kappa>\<^sub>1...\<kappa>\<^sub>n)\<close>
  by (metis "rule=I_1" "&E"(2) "\<or>E"(1) cqt_5a[axiom_inst] cqt_5b[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))

AOT_theorem free_thms_4_b_1_0: \<open>([\<Pi>]\<kappa> \<or> \<kappa>[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<Pi>)\<close>
  by (metis "rule=I_1" "&E"(1) "\<or>E"(1) cqt_5a[axiom_inst] cqt_5b[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem free_thms_4_b_1_1: \<open>([\<Pi>]\<kappa> \<or> \<kappa>[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<kappa>)\<close>
  by (metis "rule=I_1" "&E"(2) "\<or>E"(1) cqt_5a[axiom_inst] cqt_5b[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))

AOT_theorem free_thms_4_b_2_0: \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<Pi>)\<close>
  by (metis "rule=I_1" "&E"(1) "\<or>E"(1) cqt_5a_2[axiom_inst] cqt_5b_2[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem free_thms_4_b_2_1: \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<kappa>\<^sub>1)\<close>
  by (metis "rule=I_1" "&E" "\<or>E"(1) cqt_5a_2[axiom_inst] cqt_5b_2[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem free_thms_4_b_2_2: \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<kappa>\<^sub>2)\<close>
  by (metis "rule=I_1" "&E"(2) "\<or>E"(1) cqt_5a_2[axiom_inst] cqt_5b_2[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem free_thms_4_b_3_0: \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<Pi>)\<close>
  by (metis "rule=I_1" "&E"(1) "\<or>E"(1) cqt_5a_3[axiom_inst] cqt_5b_3[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem free_thms_4_b_3_1: \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<kappa>\<^sub>1)\<close>
  by (metis "rule=I_1" "&E" "\<or>E"(1) cqt_5a_3[axiom_inst] cqt_5b_3[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem free_thms_4_b_3_2: \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<kappa>\<^sub>2)\<close>
  by (metis "rule=I_1" "&E" "\<or>E"(1) cqt_5a_3[axiom_inst] cqt_5b_3[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem free_thms_4_b_3_3: \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<kappa>\<^sub>3)\<close>
  by (metis "rule=I_1" "&E"(2) "\<or>E"(1) cqt_5a_3[axiom_inst] cqt_5b_3[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem free_thms_4_b_4_0: \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<Pi>)\<close>
  by (metis "rule=I_1" "&E"(1) "\<or>E"(1) cqt_5a_4[axiom_inst] cqt_5b_4[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem free_thms_4_b_4_1: \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<kappa>\<^sub>1)\<close>
  by (metis "rule=I_1" "&E" "\<or>E"(1) cqt_5a_4[axiom_inst] cqt_5b_4[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem free_thms_4_b_4_2: \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<kappa>\<^sub>2)\<close>
  by (metis "rule=I_1" "&E" "\<or>E"(1) cqt_5a_4[axiom_inst] cqt_5b_4[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem free_thms_4_b_4_3: \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<kappa>\<^sub>3)\<close>
  by (metis "rule=I_1" "&E" "\<or>E"(1) cqt_5a_4[axiom_inst] cqt_5b_4[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))
AOT_theorem free_thms_4_b_4_4: \<open>([\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4[\<Pi>]) \<rightarrow> \<exists>\<beta> (\<beta> = \<kappa>\<^sub>4)\<close>
  by (metis "rule=I_1" "&E"(2) "\<or>E"(1) cqt_5a_4[axiom_inst] cqt_5b_4[axiom_inst] "\<rightarrow>I" "\<exists>I"(1))

AOT_theorem ex_1_a: \<open>\<forall>\<alpha> \<alpha>\<down>\<close>
  by (rule GEN) (fact cqt_2_const_var[axiom_inst])
AOT_theorem ex_1_b: \<open>\<forall>\<alpha>\<exists>\<beta>(\<beta> = \<alpha>)\<close>
  by (rule GEN) (fact free_thms_3_a)

AOT_theorem ex_2_a: \<open>\<box>\<alpha>\<down>\<close>
  by (rule RN) (fact cqt_2_const_var[axiom_inst])
AOT_theorem ex_2_b: \<open>\<box>\<exists>\<beta>(\<beta> = \<alpha>)\<close>
  by (rule RN) (fact free_thms_3_a)

AOT_theorem ex_3_a: \<open>\<box>\<forall>\<alpha> \<alpha>\<down>\<close>
  by (rule RN) (fact ex_1_a)
AOT_theorem ex_3_b: \<open>\<box>\<forall>\<alpha>\<exists>\<beta>(\<beta> = \<alpha>)\<close>
  by (rule RN) (fact ex_1_b)

AOT_theorem ex_4_a: \<open>\<forall>\<alpha> \<box>\<alpha>\<down>\<close>
  by (rule GEN; rule RN) (fact cqt_2_const_var[axiom_inst])
AOT_theorem ex_4_b: \<open>\<forall>\<alpha>\<box>\<exists>\<beta>(\<beta> = \<alpha>)\<close>
  by (rule GEN; rule RN) (fact free_thms_3_a)

AOT_theorem ex_5_a: \<open>\<box>\<forall>\<alpha> \<box>\<alpha>\<down>\<close>
  by (rule RN) (simp add: ex_4_a)
AOT_theorem ex_5_b: \<open>\<box>\<forall>\<alpha>\<box>\<exists>\<beta>(\<beta> = \<alpha>)\<close>
  by (rule RN) (simp add: ex_4_b)

AOT_theorem "all-self=_1": \<open>\<box>\<forall>\<alpha>(\<alpha> = \<alpha>)\<close>
  by (rule RN; rule GEN) (fact id_eq_1)
AOT_theorem "all-self=_2": \<open>\<forall>\<alpha>\<box>(\<alpha> = \<alpha>)\<close>
  by (rule GEN; rule RN) (fact id_eq_1)

AOT_theorem id_nec_1: \<open>\<alpha> = \<beta> \<rightarrow> \<box>(\<alpha> = \<beta>)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<alpha> = \<beta>\<close>
  moreover AOT_have \<open>\<box>(\<alpha> = \<alpha>)\<close>
    by (rule RN) (fact id_eq_1)
  ultimately AOT_show \<open>\<box>(\<alpha> = \<beta>)\<close> using "=E" by fast
qed

AOT_theorem id_nec_2: \<open>\<tau> = \<sigma> \<rightarrow> \<box>(\<tau> = \<sigma>)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume asm: \<open>\<tau> = \<sigma>\<close>
  moreover AOT_have \<open>\<tau>\<down>\<close>
    using calculation "t=t-proper_1" "\<rightarrow>E" by blast
  moreover AOT_have \<open>\<box>(\<tau> = \<tau>)\<close>
    using calculation "all-self=_2" "\<forall>E"(1) by blast
  ultimately AOT_show \<open>\<box>(\<tau> = \<sigma>)\<close> using "=E" by fast
qed

AOT_theorem term_out_1: \<open>\<phi>{\<alpha>} \<equiv> \<exists>\<beta> (\<beta> = \<alpha> & \<phi>{\<beta>})\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume asm: \<open>\<phi>{\<alpha>}\<close>
  AOT_show \<open>\<exists>\<beta> (\<beta> = \<alpha> & \<phi>{\<beta>})\<close>
    by (rule_tac \<beta>=\<alpha> in "\<exists>I"(2); rule "&I")
       (auto simp: id_eq_1 asm)
next
  AOT_assume 0: \<open>\<exists>\<beta> (\<beta> = \<alpha> & \<phi>{\<beta>})\<close>
  (* TODO: have another look at this instantiation. Ideally AOT_obtain would resolve directly to the existential
           statement as proof obligation *)
  AOT_obtain \<beta> where \<open>\<beta> = \<alpha> & \<phi>{\<beta>}\<close> using "instantiation"[rotated, OF 0] by blast
  AOT_thus \<open>\<phi>{\<alpha>}\<close> using "&E" "=E" by blast
qed

AOT_theorem term_out_2: \<open>\<tau>\<down> \<rightarrow> (\<phi>{\<tau>} \<equiv> \<exists>\<alpha>(\<alpha> = \<tau> & \<phi>{\<alpha>}))\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<tau>\<down>\<close>
  moreover AOT_have \<open>\<forall>\<alpha> (\<phi>{\<alpha>} \<equiv> \<exists>\<beta> (\<beta> = \<alpha> & \<phi>{\<beta>}))\<close>
    by (rule GEN) (fact term_out_1)
  ultimately AOT_show \<open>\<phi>{\<tau>} \<equiv> \<exists>\<alpha>(\<alpha> = \<tau> & \<phi>{\<alpha>})\<close>
    using "\<forall>E" by blast
qed

(* TODO: example of an apply-style proof. Keep or reformulate? *)
AOT_theorem term_out_3: \<open>(\<phi>{\<alpha>} & \<forall>\<beta>(\<phi>{\<beta>} \<rightarrow> \<beta> = \<alpha>)) \<equiv> \<forall>\<beta>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
  apply (rule "\<equiv>I"; rule "\<rightarrow>I")
   apply (frule "&E"(1)) apply (drule "&E"(2))
   apply (rule GEN; rule "\<equiv>I"; rule "\<rightarrow>I")
  using rule_ui_2_a vdash_properties_5 apply blast
  apply (meson "rule=E" id_eq_1)
  apply (rule "&I")
  using id_eq_1 intro_elim_3_b rule_ui_3 apply blast
  apply (rule GEN; rule "\<rightarrow>I")
  using intro_elim_3_a rule_ui_2_a by blast

AOT_theorem term_out_4: \<open>(\<phi>{\<beta>} & \<forall>\<alpha>(\<phi>{\<alpha>} \<rightarrow> \<alpha> = \<beta>)) \<equiv> \<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<alpha> = \<beta>)\<close>
  using term_out_3 . (* TODO: same as above - another instance of the generalized alphabetic variant rule... *)

(* TODO: would of course be nice to define it without the syntax magic *)
AOT_define AOT_exists_unique :: \<open>\<alpha> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close>  ("\<exists>!_ _" [1,40])
  uniqueness_1: \<open>\<guillemotleft>AOT_exists_unique \<phi>\<guillemotright> \<equiv>\<^sub>d\<^sub>f \<exists>\<alpha> (\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> = \<alpha>))\<close>
translations
  "AOT_exists_unique \<tau> \<phi>" => "CONST AOT_exists_unique (_abs \<tau> \<phi>)"
AOT_syntax_print_translations
  "AOT_exists_unique \<tau> \<phi>" <= "CONST AOT_exists_unique (_abs \<tau> \<phi>)"
syntax
   "_AOT_exists_unique_ellipse" :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (\<open>\<exists>!_...\<exists>!_ _\<close> [1,40])
parse_ast_translation\<open>[(\<^syntax_const>\<open>_AOT_exists_unique_ellipse\<close>, fn ctx => fn [a,b,c] =>
  Ast.mk_appl (Ast.Constant "AOT_exists_unique") [parseEllipseList "_AOT_vars" ctx [a,b],c])]\<close>
print_translation\<open>AOT_syntax_print_translations
  [Syntax_Trans.preserve_binder_abs_tr' \<^const_syntax>\<open>AOT_exists_unique\<close> \<^syntax_const>\<open>AOT_exists_unique\<close>,
  AOT_binder_trans @{theory} @{binding "AOT_exists_unique_binder"} \<^syntax_const>\<open>AOT_exists_unique\<close>]
\<close>


context AOT_meta_syntax
begin
notation AOT_exists_unique (binder "\<^bold>\<exists>\<^bold>!" 20)
end
context AOT_no_meta_syntax
begin
no_notation AOT_exists_unique (binder "\<^bold>\<exists>\<^bold>!" 20)
end

AOT_theorem uniqueness_2: \<open>\<exists>!\<alpha> \<phi>{\<alpha>} \<equiv>\<^sub>d\<^sub>f \<exists>\<alpha>\<forall>\<beta>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
proof(rule AOT_sem_equiv_defI) (* NOTE: appeal to semantics to accomodate PLMs double definition *)
  (* TODO: hard to spot that AOT_modally_strict is needed here *)
  AOT_modally_strict {
    AOT_assume \<open>\<exists>!\<alpha> \<phi>{\<alpha>}\<close>
    AOT_hence \<open>\<exists>\<alpha> (\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> = \<alpha>))\<close>
      using uniqueness_1 "\<equiv>\<^sub>d\<^sub>fE" by blast
    then AOT_obtain \<alpha> where \<open>\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> = \<alpha>)\<close> using "instantiation"[rotated] by blast
    AOT_hence \<open>\<forall>\<beta>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close> using term_out_3 "\<equiv>E" by blast
    AOT_thus \<open>\<exists>\<alpha>\<forall>\<beta>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
      using "\<exists>I" by fast
  }
next
  AOT_modally_strict {
    AOT_assume \<open>\<exists>\<alpha>\<forall>\<beta>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
    then AOT_obtain \<alpha> where \<open>\<forall>\<beta> (\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close> using "instantiation"[rotated] by blast
    AOT_hence \<open>\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> = \<alpha>)\<close> using term_out_3 "\<equiv>E" by blast
    AOT_hence \<open>\<exists>\<alpha> (\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> = \<alpha>))\<close>
      using "\<exists>I" by fast
    AOT_thus \<open>\<exists>!\<alpha> \<phi>{\<alpha>}\<close>
      using uniqueness_1 "\<equiv>\<^sub>d\<^sub>fI" by blast
  }
qed

AOT_theorem uni_most: \<open>\<exists>!\<alpha> \<phi>{\<alpha>} \<rightarrow> \<forall>\<beta>\<forall>\<gamma>((\<phi>{\<beta>} & \<phi>{\<gamma>}) \<rightarrow> \<beta> = \<gamma>)\<close>
proof(rule "\<rightarrow>I"; rule GEN; rule GEN; rule "\<rightarrow>I")
  fix \<beta> \<gamma>
  AOT_assume \<open>\<exists>!\<alpha> \<phi>{\<alpha>}\<close>
  AOT_hence \<open>\<exists>\<alpha>\<forall>\<beta>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
    using uniqueness_2 "\<equiv>\<^sub>d\<^sub>fE" by blast
  then AOT_obtain \<alpha> where \<open>\<forall>\<beta>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
    using "instantiation"[rotated] by blast
  moreover AOT_assume \<open>\<phi>{\<beta>} & \<phi>{\<gamma>}\<close>
  ultimately AOT_have \<open>\<beta> = \<alpha>\<close> and \<open>\<gamma> = \<alpha>\<close>
    using "\<forall>E"(2) "&E" "\<equiv>E"(1,2) by blast+
  AOT_thus \<open>\<beta> = \<gamma>\<close>
    by (metis "rule=E" id_eq_2 "\<rightarrow>E")
qed

AOT_theorem "nec-exist-!": \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<rightarrow> \<box>\<phi>{\<alpha>}) \<rightarrow> (\<exists>!\<alpha> \<phi>{\<alpha>} \<rightarrow> \<exists>!\<alpha> \<box>\<phi>{\<alpha>})\<close>
proof (rule "\<rightarrow>I"; rule "\<rightarrow>I")
  AOT_assume a: \<open>\<forall>\<alpha>(\<phi>{\<alpha>} \<rightarrow> \<box>\<phi>{\<alpha>})\<close>
  AOT_assume \<open>\<exists>!\<alpha> \<phi>{\<alpha>}\<close>
  AOT_hence \<open>\<exists>\<alpha> (\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> = \<alpha>))\<close> using uniqueness_1 "\<equiv>\<^sub>d\<^sub>fE" by blast
  then AOT_obtain \<alpha> where \<xi>: \<open>\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> = \<alpha>)\<close> using "instantiation"[rotated] by blast
  AOT_have \<open>\<box>\<phi>{\<alpha>}\<close>
    using \<xi> a "&E" "\<forall>E" "\<rightarrow>E" by fast
  moreover AOT_have \<open>\<forall>\<beta> (\<box>\<phi>{\<beta>} \<rightarrow> \<beta> = \<alpha>)\<close>
    apply (rule GEN; rule "\<rightarrow>I")
    using \<xi>[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"] qml_2[axiom_inst, THEN "\<rightarrow>E"] by blast
  ultimately AOT_have \<open>(\<box>\<phi>{\<alpha>} & \<forall>\<beta> (\<box>\<phi>{\<beta>} \<rightarrow> \<beta> = \<alpha>))\<close>
    using "&I" by blast
  AOT_thus \<open>\<exists>!\<alpha> \<box>\<phi>{\<alpha>}\<close>
    using uniqueness_1 "\<equiv>\<^sub>d\<^sub>fI" "\<exists>I" by fast
qed

AOT_theorem act_cond: \<open>\<^bold>\<A>(\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<^bold>\<A>\<phi> \<rightarrow> \<^bold>\<A>\<psi>)\<close>
  using "\<rightarrow>I" "\<equiv>E"(1) logic_actual_nec_2[axiom_inst] by blast

AOT_theorem nec_imp_act: \<open>\<box>\<phi> \<rightarrow> \<^bold>\<A>\<phi>\<close>
  by (metis act_cond contraposition_1_b "\<equiv>E"(4) qml_2[THEN act_closure, axiom_inst] qml_act_2[axiom_inst] RAA(1) "\<rightarrow>E" "\<rightarrow>I")

AOT_theorem act_conj_act_1: \<open>\<^bold>\<A>(\<^bold>\<A>\<phi> \<rightarrow> \<phi>)\<close>
  using "\<rightarrow>I" "\<equiv>E"(2) logic_actual_nec_2[axiom_inst] logic_actual_nec_4[axiom_inst] by blast

AOT_theorem act_conj_act_2: \<open>\<^bold>\<A>(\<phi> \<rightarrow> \<^bold>\<A>\<phi>)\<close>
  by (metis "\<rightarrow>I" "\<equiv>E"(2, 4) logic_actual_nec_2[axiom_inst] logic_actual_nec_4[axiom_inst] RAA(1))

AOT_theorem act_conj_act_3: \<open>(\<^bold>\<A>\<phi> & \<^bold>\<A>\<psi>) \<rightarrow> \<^bold>\<A>(\<phi> & \<psi>)\<close>
proof -
  AOT_have \<open>\<box>(\<phi> \<rightarrow> (\<psi> \<rightarrow> (\<phi> & \<psi>)))\<close>
    by (rule RN) (fact con_dis_taut_5)
  AOT_hence \<open>\<^bold>\<A>(\<phi> \<rightarrow> (\<psi> \<rightarrow> (\<phi> & \<psi>)))\<close>
    using nec_imp_act "\<rightarrow>E" by blast
  AOT_hence \<open>\<^bold>\<A>\<phi> \<rightarrow> \<^bold>\<A>(\<psi> \<rightarrow> (\<phi> & \<psi>))\<close>
    using act_cond "\<rightarrow>E" by blast
  moreover AOT_have \<open>\<^bold>\<A>(\<psi> \<rightarrow> (\<phi> & \<psi>)) \<rightarrow> (\<^bold>\<A>\<psi> \<rightarrow> \<^bold>\<A>(\<phi> & \<psi>))\<close>
    by (fact act_cond)
  ultimately AOT_have \<open>\<^bold>\<A>\<phi> \<rightarrow> (\<^bold>\<A>\<psi> \<rightarrow> \<^bold>\<A>(\<phi> & \<psi>))\<close>
    using "\<rightarrow>I" "\<rightarrow>E" by metis
  AOT_thus \<open>(\<^bold>\<A>\<phi> & \<^bold>\<A>\<psi>) \<rightarrow> \<^bold>\<A>(\<phi> & \<psi>)\<close>
    by (metis oth_class_taut_7_b "\<rightarrow>E")
qed

AOT_theorem act_conj_act_4: \<open>\<^bold>\<A>(\<^bold>\<A>\<phi> \<equiv> \<phi>)\<close>
proof -
  AOT_have \<open>(\<^bold>\<A>(\<^bold>\<A>\<phi> \<rightarrow> \<phi>) & \<^bold>\<A>(\<phi> \<rightarrow> \<^bold>\<A>\<phi>)) \<rightarrow> \<^bold>\<A>((\<^bold>\<A>\<phi> \<rightarrow> \<phi>) & (\<phi> \<rightarrow> \<^bold>\<A>\<phi>))\<close>
    by (fact act_conj_act_3)
  moreover AOT_have \<open>\<^bold>\<A>(\<^bold>\<A>\<phi> \<rightarrow> \<phi>) & \<^bold>\<A>(\<phi> \<rightarrow> \<^bold>\<A>\<phi>)\<close>
    using "&I" act_conj_act_1 act_conj_act_2 by simp
  ultimately AOT_have \<zeta>: \<open>\<^bold>\<A>((\<^bold>\<A>\<phi> \<rightarrow> \<phi>) & (\<phi> \<rightarrow> \<^bold>\<A>\<phi>))\<close>
    using "\<rightarrow>E" by blast
  AOT_have \<open>\<^bold>\<A>(((\<^bold>\<A>\<phi> \<rightarrow> \<phi>) & (\<phi> \<rightarrow> \<^bold>\<A>\<phi>)) \<rightarrow> (\<^bold>\<A>\<phi> \<equiv> \<phi>))\<close>
    using AOT_equiv[THEN df_rules_formulas_4, THEN act_closure, axiom_inst] by blast
  AOT_hence \<open>\<^bold>\<A>((\<^bold>\<A>\<phi> \<rightarrow> \<phi>) & (\<phi> \<rightarrow> \<^bold>\<A>\<phi>)) \<rightarrow> \<^bold>\<A>(\<^bold>\<A>\<phi> \<equiv> \<phi>)\<close>
    using act_cond "\<rightarrow>E" by blast
  AOT_thus \<open>\<^bold>\<A>(\<^bold>\<A>\<phi> \<equiv> \<phi>)\<close> using \<zeta> "\<rightarrow>E" by blast
qed

(* TODO: consider introducing AOT_inductive *)
inductive arbitrary_actualization for \<phi> where
  \<open>arbitrary_actualization \<phi> \<guillemotleft>\<^bold>\<A>\<phi>\<guillemotright>\<close>
| \<open>arbitrary_actualization \<phi> \<guillemotleft>\<^bold>\<A>\<psi>\<guillemotright>\<close> if \<open>arbitrary_actualization \<phi> \<psi>\<close>
declare arbitrary_actualization.cases[AOT] arbitrary_actualization.induct[AOT]
        arbitrary_actualization.simps[AOT] arbitrary_actualization.intros[AOT]
syntax arbitrary_actualization :: \<open>\<phi>' \<Rightarrow> \<phi>' \<Rightarrow> AOT_prop\<close> ("ARBITRARY'_ACTUALIZATION'(_,_')")

notepad
begin
  AOT_modally_strict {
    fix \<phi>
    AOT_have \<open>ARBITRARY_ACTUALIZATION(\<^bold>\<A>\<phi> \<equiv> \<phi>, \<^bold>\<A>(\<^bold>\<A>\<phi> \<equiv> \<phi>))\<close>
      using AOT_PLM.arbitrary_actualization.intros by metis
    AOT_have \<open>ARBITRARY_ACTUALIZATION(\<^bold>\<A>\<phi> \<equiv> \<phi>, \<^bold>\<A>\<^bold>\<A>(\<^bold>\<A>\<phi> \<equiv> \<phi>))\<close>
      using AOT_PLM.arbitrary_actualization.intros by metis
    AOT_have \<open>ARBITRARY_ACTUALIZATION(\<^bold>\<A>\<phi> \<equiv> \<phi>, \<^bold>\<A>\<^bold>\<A>\<^bold>\<A>(\<^bold>\<A>\<phi> \<equiv> \<phi>))\<close>
      using AOT_PLM.arbitrary_actualization.intros by metis
  }
end


AOT_theorem closure_act_1: assumes \<open>ARBITRARY_ACTUALIZATION(\<^bold>\<A>\<phi> \<equiv> \<phi>, \<psi>)\<close> shows \<open>\<psi>\<close>
using assms proof(induct)
  case 1
  AOT_show \<open>\<^bold>\<A>(\<^bold>\<A>\<phi> \<equiv> \<phi>)\<close>
    by (simp add: act_conj_act_4)
next
  case (2 \<psi>)
  AOT_thus \<open>\<^bold>\<A>\<psi>\<close>
    by (metis arbitrary_actualization.simps "\<equiv>E"(1) logic_actual_nec_4[axiom_inst])
qed

AOT_theorem closure_act_2: \<open>\<forall>\<alpha> \<^bold>\<A>(\<^bold>\<A>\<phi>{\<alpha>} \<equiv> \<phi>{\<alpha>})\<close>
  by (simp add: act_conj_act_4 "\<forall>I")

AOT_theorem closure_act_3: \<open>\<^bold>\<A>\<forall>\<alpha> \<^bold>\<A>(\<^bold>\<A>\<phi>{\<alpha>} \<equiv> \<phi>{\<alpha>})\<close>
  by (metis (no_types, lifting) act_conj_act_4 "\<equiv>E"(1,2) logic_actual_nec_3[axiom_inst] logic_actual_nec_4[axiom_inst] "\<forall>I")

AOT_theorem closure_act_4: \<open>\<^bold>\<A>\<forall>\<alpha>\<^sub>1...\<forall>\<alpha>\<^sub>n \<^bold>\<A>(\<^bold>\<A>\<phi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n} \<equiv> \<phi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n})\<close>
  using closure_act_3 .

(* TODO: examine these proofs *)
AOT_theorem RA_1: assumes \<open>\<^bold>\<turnstile> \<phi>\<close> shows \<open>\<^bold>\<turnstile> \<^bold>\<A>\<phi>\<close>
  (* This proof is the one rejected in remark (136) (meta-rule) *)
  using "\<not>\<not>E" assms "\<equiv>E"(3) logic_actual[act_axiom_inst] logic_actual_nec_1[axiom_inst] modus_tollens_2 by blast
AOT_theorem RA_2: assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi>\<close> shows \<open>\<^bold>\<A>\<phi>\<close>
  (* This is actually \<Gamma> \<turnstile>\<^sub>\<box> \<phi> \<Longrightarrow> \<box>\<Gamma> \<turnstile>\<^sub>\<box> \<A>\<phi>*)
  using RN assms nec_imp_act vdash_properties_5 by blast
AOT_theorem RA_3: assumes \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<phi>\<close> shows \<open>\<^bold>\<A>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<^bold>\<A>\<phi>\<close>
  using assms by (meson AOT_sem_act imageI)
  (* This is not exactly right either. *)

lemmas RA = RA_1 RA_2

AOT_act_theorem ANeg_1: \<open>\<not>\<^bold>\<A>\<phi> \<equiv> \<not>\<phi>\<close>
  by (simp add: RA_1 contraposition_1_a deduction_theorem intro_elim_2 logic_actual[act_axiom_inst])

AOT_act_theorem ANeg_2: \<open>\<not>\<^bold>\<A>\<not>\<phi> \<equiv> \<phi>\<close>
  using ANeg_1 intro_elim_2 intro_elim_3_e useful_tautologies_1 useful_tautologies_2 by blast

AOT_theorem Act_Basic_1: \<open>\<^bold>\<A>\<phi> \<or> \<^bold>\<A>\<not>\<phi>\<close>
  by (meson "\<or>I"(1,2) "\<equiv>E"(2) logic_actual_nec_1[axiom_inst] raa_cor_1)

AOT_theorem Act_Basic_2: \<open>\<^bold>\<A>(\<phi> & \<psi>) \<equiv> (\<^bold>\<A>\<phi> & \<^bold>\<A>\<psi>)\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<A>(\<phi> & \<psi>)\<close>
  moreover AOT_have \<open>\<^bold>\<A>((\<phi> & \<psi>) \<rightarrow> \<phi>)\<close>
    by (simp add: RA_2 con_dis_taut_1)
  moreover AOT_have \<open>\<^bold>\<A>((\<phi> & \<psi>) \<rightarrow> \<psi>)\<close>
    by (simp add: RA_2 con_dis_taut_2)
  ultimately AOT_show \<open>\<^bold>\<A>\<phi> & \<^bold>\<A>\<psi>\<close>
    using act_cond[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "&I" by metis
next
  AOT_assume \<open>\<^bold>\<A>\<phi> & \<^bold>\<A>\<psi>\<close>
  AOT_thus \<open>\<^bold>\<A>(\<phi> & \<psi>)\<close>
    using act_conj_act_3 vdash_properties_6 by blast
qed

AOT_theorem Act_Basic_3: \<open>\<^bold>\<A>(\<phi> \<equiv> \<psi>) \<equiv> (\<^bold>\<A>(\<phi> \<rightarrow> \<psi>) & \<^bold>\<A>(\<psi> \<rightarrow> \<phi>))\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<A>(\<phi> \<equiv> \<psi>)\<close>
  moreover AOT_have \<open>\<^bold>\<A>((\<phi> \<equiv> \<psi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>))\<close>
    by (simp add: RA_2 deduction_theorem intro_elim_3_a)
  moreover AOT_have \<open>\<^bold>\<A>((\<phi> \<equiv> \<psi>) \<rightarrow> (\<psi> \<rightarrow> \<phi>))\<close>
    by (simp add: RA_2 deduction_theorem intro_elim_3_b)
  ultimately AOT_show \<open>\<^bold>\<A>(\<phi> \<rightarrow> \<psi>) & \<^bold>\<A>(\<psi> \<rightarrow> \<phi>)\<close>
    using act_cond[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "&I" by metis
next
  AOT_assume \<open>\<^bold>\<A>(\<phi> \<rightarrow> \<psi>) & \<^bold>\<A>(\<psi> \<rightarrow> \<phi>)\<close>
  AOT_hence \<open>\<^bold>\<A>((\<phi> \<rightarrow> \<psi>) & (\<psi> \<rightarrow> \<phi>))\<close>
    by (metis act_conj_act_3 vdash_properties_10)
  moreover AOT_have \<open>\<^bold>\<A>(((\<phi> \<rightarrow> \<psi>) & (\<psi> \<rightarrow> \<phi>)) \<rightarrow> (\<phi> \<equiv> \<psi>))\<close>
    by (simp add: AOT_equiv RA_2 df_rules_formulas_4 vdash_properties_1_b)
  ultimately AOT_show \<open>\<^bold>\<A>(\<phi> \<equiv> \<psi>)\<close>
    using act_cond[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] by metis
qed

AOT_theorem Act_Basic_4: \<open>(\<^bold>\<A>(\<phi> \<rightarrow> \<psi>) & \<^bold>\<A>(\<psi> \<rightarrow> \<phi>)) \<equiv> (\<^bold>\<A>\<phi> \<equiv> \<^bold>\<A>\<psi>)\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<^bold>\<A>(\<phi> \<rightarrow> \<psi>) & \<^bold>\<A>(\<psi> \<rightarrow> \<phi>)\<close>
  AOT_show \<open>\<^bold>\<A>\<phi> \<equiv> \<^bold>\<A>\<psi>\<close>
    using 0 "&E" act_cond[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "\<equiv>I" "\<rightarrow>I" by metis
next
  AOT_assume \<open>\<^bold>\<A>\<phi> \<equiv> \<^bold>\<A>\<psi>\<close>
  AOT_thus \<open>\<^bold>\<A>(\<phi> \<rightarrow> \<psi>) & \<^bold>\<A>(\<psi> \<rightarrow> \<phi>)\<close>
    by (metis "\<rightarrow>I" logic_actual_nec_2[axiom_inst] "\<equiv>E"(1,2) "&I")
qed

AOT_theorem Act_Basic_5: \<open>\<^bold>\<A>(\<phi> \<equiv> \<psi>) \<equiv> (\<^bold>\<A>\<phi> \<equiv> \<^bold>\<A>\<psi>)\<close>
  using Act_Basic_3 Act_Basic_4 intro_elim_3_e by blast

AOT_theorem Act_Basic_6: \<open>\<^bold>\<A>\<phi> \<equiv> \<box>\<^bold>\<A>\<phi>\<close>
  by (simp add: intro_elim_2 qml_2[axiom_inst] qml_act_1[axiom_inst])

AOT_theorem Act_Basic_7: \<open>\<^bold>\<A>\<box>\<phi> \<rightarrow> \<box>\<^bold>\<A>\<phi>\<close>
  by (metis Act_Basic_6 "\<rightarrow>I" "\<rightarrow>E" "\<equiv>E"(1,2) nec_imp_act qml_act_2[axiom_inst])

AOT_theorem Act_Basic_8: \<open>\<box>\<phi> \<rightarrow> \<box>\<^bold>\<A>\<phi>\<close>
  using ded_thm_cor_1 nec_imp_act qml_act_1[axiom_inst] by blast

AOT_theorem Act_Basic_9: \<open>\<^bold>\<A>(\<phi> \<or> \<psi>) \<equiv> (\<^bold>\<A>\<phi> \<or> \<^bold>\<A>\<psi>)\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<A>(\<phi> \<or> \<psi>)\<close>
  AOT_thus \<open>\<^bold>\<A>\<phi> \<or> \<^bold>\<A>\<psi>\<close>
  proof (rule raa_cor_3)
    AOT_assume \<open>\<not>(\<^bold>\<A>\<phi> \<or> \<^bold>\<A>\<psi>)\<close>
    AOT_hence \<open>\<not>\<^bold>\<A>\<phi> & \<not>\<^bold>\<A>\<psi>\<close>
      by (metis intro_elim_3_a oth_class_taut_5_d)
    AOT_hence \<open>\<^bold>\<A>\<not>\<phi> & \<^bold>\<A>\<not>\<psi>\<close>
      using logic_actual_nec_1[axiom_inst, THEN "\<equiv>E"(2)] "&E" "&I" by metis
    AOT_hence \<open>\<^bold>\<A>(\<not>\<phi> & \<not>\<psi>)\<close>
      using "\<equiv>E" Act_Basic_2 by metis
    moreover AOT_have \<open>\<^bold>\<A>((\<not>\<phi> & \<not>\<psi>) \<equiv> \<not>(\<phi> \<or> \<psi>))\<close>
      using RA_2 intro_elim_3_f oth_class_taut_3_a oth_class_taut_5_d by blast
    moreover AOT_have \<open>\<^bold>\<A>(\<not>\<phi> & \<not>\<psi>) \<equiv> \<^bold>\<A>(\<not>(\<phi> \<or> \<psi>))\<close>
      using calculation(2) by (metis Act_Basic_5 intro_elim_3_a)
    ultimately AOT_have \<open>\<^bold>\<A>(\<not>(\<phi> \<or> \<psi>))\<close> using "\<equiv>E" by blast
    AOT_thus \<open>\<not>\<^bold>\<A>(\<phi> \<or> \<psi>)\<close>
      using logic_actual_nec_1[axiom_inst, THEN "\<equiv>E"(1)] by auto
  qed
next
  AOT_assume \<open>\<^bold>\<A>\<phi> \<or> \<^bold>\<A>\<psi>\<close>
  AOT_thus \<open>\<^bold>\<A>(\<phi> \<or> \<psi>)\<close>
    by (meson RA_2 act_cond con_dis_i_e_3_a con_dis_i_e_4_a con_dis_taut_3 con_dis_taut_4)
qed

AOT_theorem Act_Basic_10: \<open>\<^bold>\<A>\<exists>\<alpha> \<phi>{\<alpha>} \<equiv> \<exists>\<alpha> \<^bold>\<A>\<phi>{\<alpha>}\<close>
proof -
  AOT_have \<theta>: \<open>\<not>\<^bold>\<A>\<forall>\<alpha> \<not>\<phi>{\<alpha>} \<equiv> \<not>\<forall>\<alpha> \<^bold>\<A>\<not>\<phi>{\<alpha>}\<close>
    by (rule oth_class_taut_4_b[THEN "\<equiv>E"(1)])
       (metis logic_actual_nec_3[axiom_inst])
  AOT_have \<xi>: \<open>\<not>\<forall>\<alpha> \<^bold>\<A>\<not>\<phi>{\<alpha>} \<equiv> \<not>\<forall>\<alpha> \<not>\<^bold>\<A>\<phi>{\<alpha>}\<close>
    by (rule oth_class_taut_4_b[THEN "\<equiv>E"(1)])
       (rule logic_actual_nec_1[THEN universal_closure, axiom_inst, THEN cqt_basic_3[THEN "\<rightarrow>E"]])
  AOT_have \<open>\<^bold>\<A>(\<exists>\<alpha> \<phi>{\<alpha>}) \<equiv> \<^bold>\<A>(\<not>\<forall>\<alpha> \<not>\<phi>{\<alpha>})\<close>
    using AOT_exists[THEN df_rules_formulas_3, THEN act_closure, axiom_inst]
          AOT_exists[THEN df_rules_formulas_4, THEN act_closure, axiom_inst]
    Act_Basic_4[THEN "\<equiv>E"(1)] "&I" Act_Basic_5[THEN "\<equiv>E"(2)] by metis
  also AOT_have \<open>\<dots> \<equiv> \<not>\<^bold>\<A>\<forall>\<alpha> \<not>\<phi>{\<alpha>}\<close>
    by (simp add: logic_actual_nec_1 vdash_properties_1_b)
  also AOT_have \<open>\<dots> \<equiv> \<not>\<forall>\<alpha> \<^bold>\<A> \<not>\<phi>{\<alpha>}\<close> using \<theta> by blast
  also AOT_have \<open>\<dots> \<equiv> \<not>\<forall>\<alpha> \<not>\<^bold>\<A> \<phi>{\<alpha>}\<close> using \<xi> by blast
  also AOT_have \<open>\<dots> \<equiv> \<exists>\<alpha> \<^bold>\<A> \<phi>{\<alpha>}\<close>
    using AOT_exists[THEN "\<equiv>Df"] by (metis intro_elim_3_f oth_class_taut_3_a)
  finally AOT_show \<open>\<^bold>\<A>\<exists>\<alpha> \<phi>{\<alpha>} \<equiv> \<exists>\<alpha> \<^bold>\<A>\<phi>{\<alpha>}\<close> .
qed


AOT_theorem Act_Basic_11: \<open>\<^bold>\<A>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>}) \<equiv> \<forall>\<alpha>(\<^bold>\<A>\<phi>{\<alpha>} \<equiv> \<^bold>\<A>\<psi>{\<alpha>})\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<A>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close>
  AOT_hence \<open>\<forall>\<alpha>\<^bold>\<A>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close>
    using logic_actual_nec_3[axiom_inst, THEN "\<equiv>E"(1)] by blast
  AOT_hence \<open>\<^bold>\<A>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close> for \<alpha> using "\<forall>E" by blast
  AOT_hence \<open>\<^bold>\<A>\<phi>{\<alpha>} \<equiv> \<^bold>\<A>\<psi>{\<alpha>}\<close> for \<alpha> by (metis Act_Basic_5 intro_elim_3_a)
  AOT_thus \<open>\<forall>\<alpha>(\<^bold>\<A>\<phi>{\<alpha>} \<equiv> \<^bold>\<A>\<psi>{\<alpha>})\<close> by (rule "\<forall>I")
next
  AOT_assume \<open>\<forall>\<alpha>(\<^bold>\<A>\<phi>{\<alpha>} \<equiv> \<^bold>\<A>\<psi>{\<alpha>})\<close>
  AOT_hence \<open>\<^bold>\<A>\<phi>{\<alpha>} \<equiv> \<^bold>\<A>\<psi>{\<alpha>}\<close> for \<alpha> using "\<forall>E" by blast
  AOT_hence \<open>\<^bold>\<A>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close> for \<alpha> by (metis Act_Basic_5 intro_elim_3_b)
  AOT_hence \<open>\<forall>\<alpha> \<^bold>\<A>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close> by (rule "\<forall>I")
  AOT_thus \<open>\<^bold>\<A>\<forall>\<alpha>(\<phi>{\<alpha>} \<equiv> \<psi>{\<alpha>})\<close>
    using logic_actual_nec_3[axiom_inst, THEN "\<equiv>E"(2)] by fast
qed

AOT_act_theorem act_quant_uniq: \<open>\<forall>\<beta>(\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>) \<equiv> \<forall>\<beta>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<forall>\<beta>(\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
  AOT_hence \<open>\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>\<close> for \<beta> using "\<forall>E" by blast
  AOT_hence \<open>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>\<close> for \<beta>
    using "\<equiv>I" "\<rightarrow>I" RA_1 intro_elim_3_a intro_elim_3_b logic_actual[act_axiom_inst] vdash_properties_6
    by metis
  AOT_thus \<open>\<forall>\<beta>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close> by (rule "\<forall>I")
next
  AOT_assume \<open>\<forall>\<beta>(\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
  AOT_hence \<open>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>\<close> for \<beta> using "\<forall>E" by blast
  AOT_hence \<open>\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>\<close> for \<beta>
    using "\<equiv>I" "\<rightarrow>I" RA_1 intro_elim_3_a intro_elim_3_b logic_actual[act_axiom_inst] vdash_properties_6
    by metis
  AOT_thus \<open>\<forall>\<beta>(\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close> by (rule "\<forall>I")
qed

AOT_act_theorem fund_cont_desc: \<open>x = \<^bold>\<iota>x(\<phi>{x}) \<equiv> \<forall>z(\<phi>{z} \<equiv> z = x)\<close>
  using descriptions[axiom_inst] act_quant_uniq intro_elim_3_e by fast

AOT_act_theorem hintikka: \<open>x = \<^bold>\<iota>x(\<phi>{x}) \<equiv> (\<phi>{x} & \<forall>z (\<phi>{z} \<rightarrow> z = x))\<close>
  using oth_class_taut_2_e[THEN "\<equiv>E"(1)] term_out_3 fund_cont_desc intro_elim_3_e by blast


locale russel_axiom =
  fixes \<psi>
  assumes \<psi>_denotes_asm: "[v \<Turnstile> \<psi>{\<kappa>}] \<Longrightarrow> [v \<Turnstile> \<kappa>\<down>]"
begin
AOT_act_theorem russell_axiom: \<open>\<psi>{\<^bold>\<iota>x \<phi>{x}} \<equiv> \<exists>x(\<phi>{x} & \<forall>z(\<phi>{z} \<rightarrow> z = x) & \<psi>{x})\<close>
proof -
  AOT_have b: \<open>\<forall>x (x = \<^bold>\<iota>x \<phi>{x} \<equiv> (\<phi>{x} & \<forall>z(\<phi>{z} \<rightarrow> z = x)))\<close>
    using hintikka "\<forall>I" by fast
  show ?thesis
  proof(rule "\<equiv>I"; rule "\<rightarrow>I")
    AOT_assume c: \<open>\<psi>{\<^bold>\<iota>x \<phi>{x}}\<close>
    AOT_hence d: \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close> using \<psi>_denotes_asm by blast
    AOT_hence \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> by (metis "rule=I_1" existential_1)
    then AOT_obtain a where a_def: \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "instantiation"[rotated] by blast
    moreover AOT_have \<open>a = \<^bold>\<iota>x \<phi>{x} \<equiv> (\<phi>{a} & \<forall>z(\<phi>{z} \<rightarrow> z = a))\<close> using b "\<forall>E" by blast
    ultimately AOT_have \<open>\<phi>{a} & \<forall>z(\<phi>{z} \<rightarrow> z = a)\<close> using "\<equiv>E" by blast
    moreover AOT_have \<open>\<psi>{a}\<close>
    proof - 
      AOT_have \<open>\<forall>x\<forall>y(x = y \<rightarrow> y = x)\<close>
        by (simp add: id_eq_2 universal_cor)
      AOT_hence \<open>a = \<^bold>\<iota>x \<phi>{x} \<rightarrow>  \<^bold>\<iota>x \<phi>{x} = a\<close>
        by (rule_tac \<tau>="\<guillemotleft>\<^bold>\<iota>x \<phi>{x}\<guillemotright>" in "\<forall>E"(1); rule_tac \<beta>=a in "\<forall>E"(2))
           (auto simp: d universal_cor)
      AOT_thus \<open>\<psi>{a}\<close>
        using a_def c "=E" "\<rightarrow>E" by blast
    qed
    ultimately AOT_have \<open>\<phi>{a} & \<forall>z(\<phi>{z} \<rightarrow> z = a) & \<psi>{a}\<close> by (rule "&I")
    AOT_thus \<open>\<exists>x(\<phi>{x} & \<forall>z(\<phi>{z} \<rightarrow> z = x) & \<psi>{x})\<close> by (rule "\<exists>I")
  next
    AOT_assume \<open>\<exists>x(\<phi>{x} & \<forall>z(\<phi>{z} \<rightarrow> z = x) & \<psi>{x})\<close>
    then AOT_obtain b where g: \<open>\<phi>{b} & \<forall>z(\<phi>{z} \<rightarrow> z = b) & \<psi>{b}\<close> using "instantiation"[rotated] by blast
    AOT_hence h: \<open>b = \<^bold>\<iota>x \<phi>{x} \<equiv> (\<phi>{b} & \<forall>z(\<phi>{z} \<rightarrow> z = b))\<close> using b "\<forall>E" by blast
    AOT_have \<open>\<phi>{b} & \<forall>z(\<phi>{z} \<rightarrow> z = b)\<close> and j: \<open>\<psi>{b}\<close> using g "&E" by blast+
    AOT_hence \<open>b = \<^bold>\<iota>x \<phi>{x}\<close> using h "\<equiv>E" by blast
    AOT_thus \<open>\<psi>{\<^bold>\<iota>x \<phi>{x}}\<close> using j "=E" by blast
  qed
qed
end

(* TODO: this nicely shows off using locales with the embedding, but maybe there is still a nicer way *)
interpretation russell_axiom_exe_1: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>\<guillemotright>"
  by standard (metis cqt_5a_1[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation russell_axiom_exe_2_1: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>\<kappa>'\<guillemotright>"
  by standard (metis cqt_5a_2[axiom_inst, THEN "\<rightarrow>E"] "&E")
interpretation russell_axiom_exe_2_2: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>'\<kappa>\<guillemotright>"
  by standard (metis cqt_5a_2[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation russell_axiom_exe_2_3: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>\<kappa>\<guillemotright>"
  by standard (metis cqt_5a_2[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation russell_axiom_exe_3_1_1: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>\<kappa>'\<kappa>''\<guillemotright>"
  by standard (metis cqt_5a_3[axiom_inst, THEN "\<rightarrow>E"] "&E")
interpretation russell_axiom_exe_3_1_2: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>'\<kappa>\<kappa>''\<guillemotright>"
  by standard (metis cqt_5a_3[axiom_inst, THEN "\<rightarrow>E"] "&E")
interpretation russell_axiom_exe_3_1_3: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>'\<kappa>''\<kappa>\<guillemotright>"
  by standard (metis cqt_5a_3[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation russell_axiom_exe_3_2_1: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>\<kappa>\<kappa>'\<guillemotright>"
  by standard (metis cqt_5a_3[axiom_inst, THEN "\<rightarrow>E"] "&E")
interpretation russell_axiom_exe_3_2_2: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>\<kappa>'\<kappa>\<guillemotright>"
  by standard (metis cqt_5a_3[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation russell_axiom_exe_3_2_3: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>'\<kappa>\<kappa>\<guillemotright>"
  by standard (metis cqt_5a_3[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation russell_axiom_exe_3_3: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>[\<Pi>]\<kappa>\<kappa>\<kappa>\<guillemotright>"
  by standard (metis cqt_5a_3[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))

interpretation russell_axiom_enc_1: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>\<kappa>[\<Pi>]\<guillemotright>"
  by standard (metis cqt_5b_1[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation russell_axiom_enc_2_1: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>\<kappa>\<kappa>'[\<Pi>]\<guillemotright>"
  by standard (metis cqt_5b_2[axiom_inst, THEN "\<rightarrow>E"] "&E")
interpretation russell_axiom_enc_2_2: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>\<kappa>'\<kappa>[\<Pi>]\<guillemotright>"
  by standard (metis cqt_5b_2[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation russell_axiom_enc_2_3: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>\<kappa>\<kappa>[\<Pi>]\<guillemotright>"
  by standard (metis cqt_5b_2[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation russell_axiom_enc_3_1_1: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>\<kappa>\<kappa>'\<kappa>''[\<Pi>]\<guillemotright>"
  by standard (metis cqt_5b_3[axiom_inst, THEN "\<rightarrow>E"] "&E")
interpretation russell_axiom_enc_3_1_2: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>\<kappa>'\<kappa>\<kappa>''[\<Pi>]\<guillemotright>"
  by standard (metis cqt_5b_3[axiom_inst, THEN "\<rightarrow>E"] "&E")
interpretation russell_axiom_enc_3_1_3: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>\<kappa>'\<kappa>''\<kappa>[\<Pi>]\<guillemotright>"
  by standard (metis cqt_5b_3[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation russell_axiom_enc_3_2_1: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>\<kappa>\<kappa>\<kappa>'[\<Pi>]\<guillemotright>"
  by standard (metis cqt_5b_3[axiom_inst, THEN "\<rightarrow>E"] "&E")
interpretation russell_axiom_enc_3_2_2: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>\<kappa>\<kappa>'\<kappa>[\<Pi>]\<guillemotright>"
  by standard (metis cqt_5b_3[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation russell_axiom_enc_3_2_3: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>\<kappa>'\<kappa>\<kappa>[\<Pi>]\<guillemotright>"
  by standard (metis cqt_5b_3[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))
interpretation russell_axiom_enc_3_3: russel_axiom "\<lambda> \<kappa> . \<guillemotleft>\<kappa>\<kappa>\<kappa>[\<Pi>]\<guillemotright>"
  by standard (metis cqt_5b_3[axiom_inst, THEN "\<rightarrow>E"] "&E"(2))

AOT_act_theorem "!-exists_1": \<open>\<^bold>\<iota>x \<phi>{x}\<down> \<equiv> \<exists>!x \<phi>{x}\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close>
  AOT_hence \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> by (metis "rule=I_1" existential_1)
  then AOT_obtain a where \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "instantiation"[rotated] by blast
  AOT_hence \<open>\<phi>{a} & \<forall>z (\<phi>{z} \<rightarrow> z = a)\<close> using hintikka "\<equiv>E" by blast
  AOT_hence \<open>\<exists>x (\<phi>{x} & \<forall>z (\<phi>{z} \<rightarrow> z = x))\<close> by (rule "\<exists>I")
  AOT_thus \<open>\<exists>!x \<phi>{x}\<close> using uniqueness_1[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
next
  AOT_assume \<open>\<exists>!x \<phi>{x}\<close>
  AOT_hence \<open>\<exists>x (\<phi>{x} & \<forall>z (\<phi>{z} \<rightarrow> z = x))\<close>
    using uniqueness_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain b where \<open>\<phi>{b} & \<forall>z (\<phi>{z} \<rightarrow> z = b)\<close> using "instantiation"[rotated] by blast
  AOT_hence \<open>b = \<^bold>\<iota>x \<phi>{x}\<close> using hintikka "\<equiv>E" by blast
  AOT_thus \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close> by (metis "t=t-proper_2" vdash_properties_6)
qed

AOT_act_theorem "!-exists_2": \<open>\<exists>y(y=\<^bold>\<iota>x \<phi>{x}) \<equiv> \<exists>!x \<phi>{x}\<close>
  using "!-exists_1" free_thms_1 intro_elim_3_f by blast

AOT_act_theorem y_in_1: \<open>x = \<^bold>\<iota>x \<phi>{x} \<rightarrow> \<phi>{x}\<close>
  using "&E"(1) "\<rightarrow>I" hintikka "\<equiv>E"(1) by blast

AOT_act_theorem y_in_2: \<open>z = \<^bold>\<iota>x \<phi>{x} \<rightarrow> \<phi>{z}\<close> using y_in_1. (* TODO: same as above *)

AOT_act_theorem y_in_3: \<open>\<^bold>\<iota>x \<phi>{x}\<down> \<rightarrow> \<phi>{\<^bold>\<iota>x \<phi>{x}}\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close>
  AOT_hence \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> by (metis "rule=I_1" existential_1)
  then AOT_obtain a where \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "instantiation"[rotated] by blast
  moreover AOT_have \<open>\<phi>{a}\<close> using calculation hintikka "\<equiv>E"(1) "&E" by blast
  ultimately AOT_show \<open>\<phi>{\<^bold>\<iota>x \<phi>{x}}\<close> using "=E" by blast
qed

AOT_act_theorem y_in_4: \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x}) \<rightarrow> \<phi>{\<^bold>\<iota>x \<phi>{x}}\<close>
  using y_in_3[THEN "\<rightarrow>E"] free_thms_1[THEN "\<equiv>E"(2)] "\<rightarrow>I" by blast


AOT_theorem act_quant_nec: \<open>\<forall>\<beta> (\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>) \<equiv> \<forall>\<beta>(\<^bold>\<A>\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<forall>\<beta> (\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
  AOT_hence \<open>\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>\<close> for \<beta> using "\<forall>E" by blast
  AOT_hence \<open>\<^bold>\<A>\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>\<close> for \<beta> 
    by (metis Act_Basic_5 act_conj_act_4 intro_elim_3_a intro_elim_3_e)
  AOT_thus \<open>\<forall>\<beta>(\<^bold>\<A>\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
    by (rule "\<forall>I")
next
  AOT_assume \<open>\<forall>\<beta>(\<^bold>\<A>\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
  AOT_hence \<open>\<^bold>\<A>\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>\<close> for \<beta> using "\<forall>E" by blast
  AOT_hence \<open>\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>\<close> for \<beta>
    by (metis Act_Basic_5 act_conj_act_4 intro_elim_3_a intro_elim_3_f)
  AOT_thus \<open>\<forall>\<beta> (\<^bold>\<A>\<phi>{\<beta>} \<equiv> \<beta> = \<alpha>)\<close>
    by (rule "\<forall>I")
qed

AOT_theorem equi_desc_descA_1: \<open>x = \<^bold>\<iota>x \<phi>{x} \<equiv> x = \<^bold>\<iota>x(\<^bold>\<A>\<phi>{x})\<close>
proof -
  AOT_have \<open>x = \<^bold>\<iota>x \<phi>{x} \<equiv> \<forall>z (\<^bold>\<A>\<phi>{z} \<equiv> z = x)\<close>  using descriptions[axiom_inst] by blast
  also AOT_have \<open>... \<equiv> \<forall>z (\<^bold>\<A>\<^bold>\<A>\<phi>{z} \<equiv> z = x)\<close>
  proof(rule "\<equiv>I"; rule "\<rightarrow>I"; rule "\<forall>I")
    AOT_assume \<open>\<forall>z (\<^bold>\<A>\<phi>{z} \<equiv> z = x)\<close>
    AOT_hence \<open>\<^bold>\<A>\<phi>{a} \<equiv> a = x\<close> for a using "\<forall>E" by blast
    AOT_thus \<open>\<^bold>\<A>\<^bold>\<A>\<phi>{a} \<equiv> a = x\<close> for a by (metis Act_Basic_5 act_conj_act_4 intro_elim_3_a intro_elim_3_e)
  next
    AOT_assume \<open>\<forall>z (\<^bold>\<A>\<^bold>\<A>\<phi>{z} \<equiv> z = x)\<close>
    AOT_hence \<open>\<^bold>\<A>\<^bold>\<A>\<phi>{a} \<equiv> a = x\<close> for a using "\<forall>E" by blast
    AOT_thus \<open>\<^bold>\<A>\<phi>{a} \<equiv> a = x\<close> for a  by (metis Act_Basic_5 act_conj_act_4 intro_elim_3_a intro_elim_3_f)
  qed
  also AOT_have \<open>... \<equiv> x = \<^bold>\<iota>x(\<^bold>\<A>\<phi>{x})\<close>
    using oth_class_taut_2_e[THEN "\<equiv>E"(1)] descriptions[axiom_inst] by fast
  finally show ?thesis .
qed

AOT_theorem equi_desc_descA_2: \<open>\<^bold>\<iota>x \<phi>{x}\<down> \<rightarrow> \<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x(\<^bold>\<A>\<phi>{x})\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close>
  AOT_hence \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> by (metis "rule=I_1" existential_1)
  then AOT_obtain a where \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "instantiation"[rotated] by blast
  moreover AOT_have \<open>a = \<^bold>\<iota>x(\<^bold>\<A>\<phi>{x})\<close> using calculation equi_desc_descA_1[THEN "\<equiv>E"(1)] by blast
  ultimately AOT_show \<open>\<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x(\<^bold>\<A>\<phi>{x})\<close> using "=E" by fast
qed

AOT_theorem nec_hintikka_scheme: \<open>x = \<^bold>\<iota>x \<phi>{x} \<equiv> \<^bold>\<A>\<phi>{x} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = x)\<close>
proof -
  AOT_have \<open>x = \<^bold>\<iota>x \<phi>{x} \<equiv> \<forall>z(\<^bold>\<A>\<phi>{z} \<equiv> z = x)\<close> using descriptions[axiom_inst] by blast
  also AOT_have \<open>\<dots> \<equiv> (\<^bold>\<A>\<phi>{x} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = x))\<close>
    using oth_class_taut_2_e[THEN "\<equiv>E"(1)] term_out_3 by fast
  finally show ?thesis.
qed

AOT_theorem equiv_desc_eq_1: \<open>\<^bold>\<A>\<forall>x(\<phi>{x} \<equiv> \<psi>{x}) \<rightarrow> \<forall>x (x = \<^bold>\<iota>x \<phi>{x} \<equiv> x = \<^bold>\<iota>x \<psi>{x})\<close>
proof(rule "\<rightarrow>I"; rule "\<forall>I")
  fix \<beta>
  AOT_assume \<open>\<^bold>\<A>\<forall>x(\<phi>{x} \<equiv> \<psi>{x})\<close>
  AOT_hence \<open>\<^bold>\<A>(\<phi>{x} \<equiv> \<psi>{x})\<close> for x using logic_actual_nec_3[axiom_inst, THEN "\<equiv>E"(1)] "\<forall>E"(2) by blast
  AOT_hence 0: \<open>\<^bold>\<A>\<phi>{x} \<equiv> \<^bold>\<A>\<psi>{x}\<close> for x by (metis Act_Basic_5 intro_elim_3_a)
  AOT_have \<open>\<beta> = \<^bold>\<iota>x \<phi>{x} \<equiv> \<^bold>\<A>\<phi>{\<beta>} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = \<beta>)\<close> using nec_hintikka_scheme by blast
  also AOT_have \<open>... \<equiv> \<^bold>\<A>\<psi>{\<beta>} & \<forall>z(\<^bold>\<A>\<psi>{z} \<rightarrow> z = \<beta>)\<close>
  proof (rule "\<equiv>I"; rule "\<rightarrow>I")
    AOT_assume 1: \<open>\<^bold>\<A>\<phi>{\<beta>} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = \<beta>)\<close>
    AOT_hence \<open>\<^bold>\<A>\<phi>{z} \<rightarrow> z = \<beta>\<close> for z using "&E" "\<forall>E" by blast
    AOT_hence \<open>\<^bold>\<A>\<psi>{z} \<rightarrow> z = \<beta>\<close> for z using 0 "\<equiv>E" "\<rightarrow>I" "\<rightarrow>E" by metis
    AOT_hence \<open>\<forall>z(\<^bold>\<A>\<psi>{z} \<rightarrow> z = \<beta>)\<close> using "\<forall>I" by fast
    moreover AOT_have \<open>\<^bold>\<A>\<psi>{\<beta>}\<close> using "&E" 0[THEN "\<equiv>E"(1)] 1 by blast
    ultimately AOT_show \<open>\<^bold>\<A>\<psi>{\<beta>} & \<forall>z(\<^bold>\<A>\<psi>{z} \<rightarrow> z = \<beta>)\<close> using "&I" by blast
  next
    AOT_assume 1: \<open>\<^bold>\<A>\<psi>{\<beta>} & \<forall>z(\<^bold>\<A>\<psi>{z} \<rightarrow> z = \<beta>)\<close>
    AOT_hence \<open>\<^bold>\<A>\<psi>{z} \<rightarrow> z = \<beta>\<close> for z using "&E" "\<forall>E" by blast
    AOT_hence \<open>\<^bold>\<A>\<phi>{z} \<rightarrow> z = \<beta>\<close> for z using 0 "\<equiv>E" "\<rightarrow>I" "\<rightarrow>E" by metis
    AOT_hence \<open>\<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = \<beta>)\<close> using "\<forall>I" by fast
    moreover AOT_have \<open>\<^bold>\<A>\<phi>{\<beta>}\<close> using "&E" 0[THEN "\<equiv>E"(2)] 1 by blast
    ultimately AOT_show \<open>\<^bold>\<A>\<phi>{\<beta>} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = \<beta>)\<close> using "&I" by blast
  qed
  also AOT_have \<open>... \<equiv> \<beta> = \<^bold>\<iota>x \<psi>{x}\<close>
    using oth_class_taut_2_e[THEN "\<equiv>E"(1)] nec_hintikka_scheme by blast
  finally AOT_show \<open>\<beta> = \<^bold>\<iota>x \<phi>{x} \<equiv> \<beta> = \<^bold>\<iota>x \<psi>{x}\<close> .
qed

AOT_theorem equiv_desc_eq_2: \<open>\<^bold>\<iota>x \<phi>{x}\<down> & \<^bold>\<A>\<forall>x(\<phi>{x} \<equiv> \<psi>{x}) \<rightarrow> \<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x \<psi>{x}\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<iota>x \<phi>{x}\<down> & \<^bold>\<A>\<forall>x(\<phi>{x} \<equiv> \<psi>{x})\<close>
  AOT_hence 0: \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> and
            1: \<open>\<forall>x (x = \<^bold>\<iota>x \<phi>{x} \<equiv> x = \<^bold>\<iota>x \<psi>{x})\<close>
    using "&E" free_thms_1[THEN "\<equiv>E"(1)] equiv_desc_eq_1 "\<rightarrow>E" by blast+
  then AOT_obtain a where \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "instantiation"[rotated] by blast
  moreover AOT_have \<open>a = \<^bold>\<iota>x \<psi>{x}\<close> using calculation 1 "\<forall>E" "\<equiv>E"(1) by fast
  ultimately AOT_show \<open>\<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x \<psi>{x}\<close>
    using "=E" by fast
qed

AOT_theorem equiv_desc_eq_3: \<open>\<^bold>\<iota>x \<phi>{x}\<down> & \<box>\<forall>x(\<phi>{x} \<equiv> \<psi>{x}) \<rightarrow> \<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x \<psi>{x}\<close>
  using "\<rightarrow>I" equiv_desc_eq_2[THEN "\<rightarrow>E", OF "&I"] "&E" nec_imp_act[THEN "\<rightarrow>E"] by metis

(* TODO: this is part of exist_nec *)
AOT_theorem equiv_desc_eq_4: \<open>\<^bold>\<iota>x \<phi>{x}\<down> \<rightarrow> \<box>\<^bold>\<iota>x \<phi>{x}\<down>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close>
  AOT_hence \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> by (metis "rule=I_1" existential_1)
  then AOT_obtain a where \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "instantiation"[rotated] by blast
  AOT_thus \<open>\<box>\<^bold>\<iota>x \<phi>{x}\<down>\<close>
    using ex_2_a "=E" by fast
qed

AOT_theorem equiv_desc_eq_5: \<open>\<^bold>\<iota>x \<phi>{x}\<down> \<rightarrow> \<exists>y \<box>(y = \<^bold>\<iota>x \<phi>{x})\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close>
  AOT_hence \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> by (metis "rule=I_1" existential_1)
  then AOT_obtain a where \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "instantiation"[rotated] by blast
  AOT_hence \<open>\<box>(a = \<^bold>\<iota>x \<phi>{x})\<close> by (metis id_nec_2 vdash_properties_10)
  AOT_thus \<open>\<exists>y \<box>(y = \<^bold>\<iota>x \<phi>{x})\<close> by (rule "\<exists>I")
qed

AOT_act_theorem equiv_desc_eq2_1: \<open>\<forall>x (\<phi>{x} \<equiv> \<psi>{x}) \<rightarrow> \<forall>x (x = \<^bold>\<iota>x \<phi>{x} \<equiv> x = \<^bold>\<iota>x \<psi>{x})\<close>
  using "\<rightarrow>I" logic_actual[act_axiom_inst, THEN "\<rightarrow>E"] equiv_desc_eq_1[THEN "\<rightarrow>E"]
        RA_1 deduction_theorem by blast

AOT_act_theorem equiv_desc_eq2_2: \<open>\<^bold>\<iota>x \<phi>{x}\<down> & \<forall>x (\<phi>{x} \<equiv> \<psi>{x}) \<rightarrow> \<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x \<psi>{x}\<close>
  using "\<rightarrow>I" logic_actual[act_axiom_inst, THEN "\<rightarrow>E"] equiv_desc_eq_2[THEN "\<rightarrow>E", OF "&I"]
        RA_1 deduction_theorem "&E" by metis

context russel_axiom
begin
AOT_theorem nec_russell_axiom: \<open>\<psi>{\<^bold>\<iota>x \<phi>{x}} \<equiv> \<exists>x(\<^bold>\<A>\<phi>{x} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = x) & \<psi>{x})\<close>
proof -
  AOT_have b: \<open>\<forall>x (x = \<^bold>\<iota>x \<phi>{x} \<equiv> (\<^bold>\<A>\<phi>{x} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = x)))\<close>
    using nec_hintikka_scheme "\<forall>I" by fast
  show ?thesis
  proof(rule "\<equiv>I"; rule "\<rightarrow>I")
    AOT_assume c: \<open>\<psi>{\<^bold>\<iota>x \<phi>{x}}\<close>
    AOT_hence d: \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close> using \<psi>_denotes_asm by blast
    AOT_hence \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> by (metis "rule=I_1" existential_1)
    then AOT_obtain a where a_def: \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "instantiation"[rotated] by blast
    moreover AOT_have \<open>a = \<^bold>\<iota>x \<phi>{x} \<equiv> (\<^bold>\<A>\<phi>{a} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = a))\<close> using b "\<forall>E" by blast
    ultimately AOT_have \<open>\<^bold>\<A>\<phi>{a} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = a)\<close> using "\<equiv>E" by blast
    moreover AOT_have \<open>\<psi>{a}\<close>
    proof - 
      AOT_have \<open>\<forall>x\<forall>y(x = y \<rightarrow> y = x)\<close>
        by (simp add: id_eq_2 universal_cor)
      AOT_hence \<open>a = \<^bold>\<iota>x \<phi>{x} \<rightarrow>  \<^bold>\<iota>x \<phi>{x} = a\<close>
        by (rule_tac \<tau>="\<guillemotleft>\<^bold>\<iota>x \<phi>{x}\<guillemotright>" in "\<forall>E"(1); rule_tac \<beta>=a in "\<forall>E"(2))
           (auto simp: d universal_cor)
      AOT_thus \<open>\<psi>{a}\<close>
        using a_def c "=E" "\<rightarrow>E" by metis
    qed
    ultimately AOT_have \<open>\<^bold>\<A>\<phi>{a} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = a) & \<psi>{a}\<close> by (rule "&I")
    AOT_thus \<open>\<exists>x(\<^bold>\<A>\<phi>{x} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = x) & \<psi>{x})\<close> by (rule "\<exists>I")
  next
    AOT_assume \<open>\<exists>x(\<^bold>\<A>\<phi>{x} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = x) & \<psi>{x})\<close>
    then AOT_obtain b where g: \<open>\<^bold>\<A>\<phi>{b} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = b) & \<psi>{b}\<close> using "instantiation"[rotated] by blast
    AOT_hence h: \<open>b = \<^bold>\<iota>x \<phi>{x} \<equiv> (\<^bold>\<A>\<phi>{b} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = b))\<close> using b "\<forall>E" by blast
    AOT_have \<open>\<^bold>\<A>\<phi>{b} & \<forall>z(\<^bold>\<A>\<phi>{z} \<rightarrow> z = b)\<close> and j: \<open>\<psi>{b}\<close> using g "&E" by blast+
    AOT_hence \<open>b = \<^bold>\<iota>x \<phi>{x}\<close> using h "\<equiv>E" by blast
    AOT_thus \<open>\<psi>{\<^bold>\<iota>x \<phi>{x}}\<close> using j "=E" by blast
  qed
qed
end

AOT_theorem actual_desc_1: \<open>\<^bold>\<iota>x \<phi>{x}\<down> \<equiv> \<exists>!x \<^bold>\<A>\<phi>{x}\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close>
  AOT_hence \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> by (metis "rule=I_1" existential_1)
  then AOT_obtain a where \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "instantiation"[rotated] by blast
  moreover AOT_have \<open>a = \<^bold>\<iota>x \<phi>{x} \<equiv> \<forall>z(\<^bold>\<A>\<phi>{z} \<equiv> z = a)\<close>
    using descriptions[axiom_inst] by blast
  ultimately AOT_have \<open>\<forall>z(\<^bold>\<A>\<phi>{z} \<equiv> z = a)\<close>
    using "\<equiv>E" by blast
  AOT_hence \<open>\<exists>x\<forall>z(\<^bold>\<A>\<phi>{z} \<equiv> z = x)\<close> by (rule "\<exists>I")
  AOT_thus \<open>\<exists>!x \<^bold>\<A>\<phi>{x}\<close>
    using uniqueness_2[THEN "\<equiv>\<^sub>d\<^sub>fI"] by fast
next
  AOT_assume \<open>\<exists>!x \<^bold>\<A>\<phi>{x}\<close>
  AOT_hence \<open>\<exists>x\<forall>z(\<^bold>\<A>\<phi>{z} \<equiv> z = x)\<close>
    using uniqueness_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] by fast
  then AOT_obtain a where \<open>\<forall>z(\<^bold>\<A>\<phi>{z} \<equiv> z = a)\<close> using "instantiation"[rotated] by blast
  moreover AOT_have \<open>a = \<^bold>\<iota>x \<phi>{x} \<equiv> \<forall>z(\<^bold>\<A>\<phi>{z} \<equiv> z = a)\<close>
    using descriptions[axiom_inst] by blast
  ultimately AOT_have \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "\<equiv>E" by blast
  AOT_thus \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close> by (metis "t=t-proper_2" vdash_properties_6)
qed

AOT_theorem actual_desc_2: \<open>x = \<^bold>\<iota>x \<phi>{x} \<rightarrow> \<^bold>\<A>\<phi>{x}\<close>
  using con_dis_i_e_2_a contraposition_1_b intro_elim_3_a nec_hintikka_scheme reductio_aa_2 vdash_properties_9 by blast

AOT_theorem actual_desc_3: \<open>z = \<^bold>\<iota>x \<phi>{x} \<rightarrow> \<^bold>\<A>\<phi>{z}\<close>
  using actual_desc_2. (* TODO: same as above *)

AOT_theorem actual_desc_4: \<open>\<^bold>\<iota>x \<phi>{x}\<down> \<rightarrow> \<^bold>\<A>\<phi>{\<^bold>\<iota>x \<phi>{x}}\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close>
  AOT_hence \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> by (metis "rule=I_1" existential_1)
  then AOT_obtain a where \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> using "instantiation"[rotated] by blast
  AOT_thus \<open>\<^bold>\<A>\<phi>{\<^bold>\<iota>x \<phi>{x}}\<close>
    using actual_desc_2 "=E" "\<rightarrow>E" by fast
qed

(* TODO: the proof of this in PLM seems fishy *)
AOT_theorem actual_desc_5: \<open>\<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x \<psi>{x} \<rightarrow> \<^bold>\<A>\<forall>x(\<phi>{x} \<equiv> \<psi>{x})\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x \<psi>{x}\<close>
  AOT_hence \<phi>_down: \<open>\<^bold>\<iota>x \<phi>{x}\<down>\<close> and \<psi>_down: \<open>\<^bold>\<iota>x \<psi>{x}\<down>\<close>
    using "t=t-proper_1" "t=t-proper_2" vdash_properties_6 by blast+
  AOT_hence \<open>\<exists>y (y = \<^bold>\<iota>x \<phi>{x})\<close> and \<open>\<exists>y (y = \<^bold>\<iota>x \<psi>{x})\<close> by (metis "rule=I_1" existential_1)+
  then AOT_obtain a and b where a_eq: \<open>a = \<^bold>\<iota>x \<phi>{x}\<close> and b_eq: \<open>b = \<^bold>\<iota>x \<psi>{x}\<close>
    using "instantiation"[rotated] by metis

  AOT_have \<open>\<forall>\<alpha>\<forall>\<beta> (\<alpha> = \<beta> \<rightarrow> \<beta> = \<alpha>)\<close> by (rule "\<forall>I"; rule "\<forall>I"; rule id_eq_2)
  AOT_hence \<open>\<forall>\<beta> (\<^bold>\<iota>x \<phi>{x} = \<beta> \<rightarrow> \<beta> = \<^bold>\<iota>x \<phi>{x})\<close>
    using "\<forall>E" \<phi>_down by blast
  AOT_hence \<open>\<^bold>\<iota>x \<phi>{x} = \<^bold>\<iota>x \<psi>{x} \<rightarrow> \<^bold>\<iota>x \<psi>{x} = \<^bold>\<iota>x \<phi>{x}\<close>
    using "\<forall>E" \<psi>_down by blast
  AOT_hence 1: \<open>\<^bold>\<iota>x \<psi>{x} = \<^bold>\<iota>x \<phi>{x}\<close> using 0
    "\<rightarrow>E" by blast

  AOT_have \<open>\<^bold>\<A>\<phi>{x} \<equiv> \<^bold>\<A>\<psi>{x}\<close> for x
  proof(rule "\<equiv>I"; rule "\<rightarrow>I")
    AOT_assume \<open>\<^bold>\<A>\<phi>{x}\<close>
    moreover AOT_have \<open>\<^bold>\<A>\<phi>{x} \<rightarrow> x = a\<close> for x
      using nec_hintikka_scheme[THEN "\<equiv>E"(1), OF a_eq, THEN "&E"(2)] "\<forall>E" by blast
    ultimately AOT_have \<open>x = a\<close> using "\<rightarrow>E" by blast
    AOT_hence \<open>x = \<^bold>\<iota>x \<phi>{x}\<close> using a_eq "=E" by blast
    AOT_hence \<open>x = \<^bold>\<iota>x \<psi>{x}\<close> using 0 "=E" by blast
    AOT_thus \<open>\<^bold>\<A>\<psi>{x}\<close> by (metis actual_desc_3 vdash_properties_6)
  next
    AOT_assume \<open>\<^bold>\<A>\<psi>{x}\<close>
    moreover AOT_have \<open>\<^bold>\<A>\<psi>{x} \<rightarrow> x = b\<close> for x
      using nec_hintikka_scheme[THEN "\<equiv>E"(1), OF b_eq, THEN "&E"(2)] "\<forall>E" by blast
    ultimately AOT_have \<open>x = b\<close> using "\<rightarrow>E" by blast
    AOT_hence \<open>x = \<^bold>\<iota>x \<psi>{x}\<close> using b_eq "=E" by blast
    AOT_hence \<open>x = \<^bold>\<iota>x \<phi>{x}\<close> using 1 "=E" by blast
    AOT_thus \<open>\<^bold>\<A>\<phi>{x}\<close> by (metis actual_desc_3 vdash_properties_6)
  qed
  AOT_hence \<open>\<^bold>\<A>(\<phi>{x} \<equiv> \<psi>{x})\<close> for x by (metis Act_Basic_5 intro_elim_3_b)
  AOT_hence \<open>\<forall>x \<^bold>\<A>(\<phi>{x} \<equiv> \<psi>{x})\<close> by (rule "\<forall>I")
  AOT_thus \<open>\<^bold>\<A>\<forall>x (\<phi>{x} \<equiv> \<psi>{x})\<close>
    using logic_actual_nec_3[axiom_inst, THEN "\<equiv>E"(2)] by fast
qed    

AOT_theorem "!box-desc_1": \<open>\<exists>!x \<box>\<phi>{x} \<rightarrow> \<forall>y (y = \<^bold>\<iota>x \<phi>{x} \<rightarrow> \<phi>{y})\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<exists>!x \<box>\<phi>{x}\<close>
  AOT_hence \<zeta>: \<open>\<exists>x (\<box>\<phi>{x} & \<forall>z (\<box>\<phi>{z} \<rightarrow> z = x))\<close>
    using uniqueness_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain b where \<theta>: \<open>\<box>\<phi>{b} & \<forall>z (\<box>\<phi>{z} \<rightarrow> z = b)\<close> using "instantiation"[rotated] by blast
  AOT_show \<open>\<forall>y (y = \<^bold>\<iota>x \<phi>{x} \<rightarrow> \<phi>{y})\<close>
  proof(rule GEN; rule "\<rightarrow>I")
    fix y
    AOT_assume \<open>y = \<^bold>\<iota>x \<phi>{x}\<close>
    AOT_hence \<open>\<^bold>\<A>\<phi>{y} & \<forall>z (\<^bold>\<A>\<phi>{z} \<rightarrow> z = y)\<close> using nec_hintikka_scheme[THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>\<^bold>\<A>\<phi>{b} \<rightarrow> b = y\<close> using "&E" "\<forall>E" by blast
    moreover AOT_have \<open>\<^bold>\<A>\<phi>{b}\<close> using \<theta>[THEN "&E"(1)]  by (metis nec_imp_act "\<rightarrow>E")
    ultimately AOT_have \<open>b = y\<close> using "\<rightarrow>E" by blast
    moreover AOT_have \<open>\<phi>{b}\<close> using \<theta>[THEN "&E"(1)]  by (metis qml_2[axiom_inst] "\<rightarrow>E") 
    ultimately AOT_show \<open>\<phi>{y}\<close> using "=E" by blast
  qed
qed

AOT_theorem "!box-desc_2": \<open>\<forall>x (\<phi>{x} \<rightarrow> \<box>\<phi>{x}) \<rightarrow> (\<exists>!x \<phi>{x} \<rightarrow> \<forall>y (y = \<^bold>\<iota>x \<phi>{x} \<rightarrow> \<phi>{y}))\<close>
proof(rule "\<rightarrow>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<forall>x (\<phi>{x} \<rightarrow> \<box>\<phi>{x})\<close>
  moreover AOT_assume \<open>\<exists>!x \<phi>{x}\<close>
  ultimately AOT_have \<open>\<exists>!x \<box>\<phi>{x}\<close>
    using "nec-exist-!"[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] by blast
  AOT_thus \<open>\<forall>y (y = \<^bold>\<iota>x \<phi>{x} \<rightarrow> \<phi>{y})\<close>
    using "!box-desc_1" "\<rightarrow>E" by blast
qed

AOT_theorem dr_alphabetic_thm: \<open>\<^bold>\<iota>\<nu> \<phi>{\<nu>}\<down> \<rightarrow> \<^bold>\<iota>\<nu> \<phi>{\<nu>} = \<^bold>\<iota>\<mu> \<phi>{\<mu>}\<close> (* TODO: vacuous *)
  by (simp add: "rule=I_1" "\<rightarrow>I")

AOT_theorem RM_1_prem: assumes \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<phi> \<rightarrow> \<psi>\<close> shows \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<box>\<phi> \<rightarrow> \<box>\<psi>\<close>
proof -
  AOT_have \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<box>(\<phi> \<rightarrow> \<psi>)\<close> using RN_prem assms by blast
  AOT_thus \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<box>\<phi> \<rightarrow> \<box>\<psi>\<close> by (metis qml_1[axiom_inst] "\<rightarrow>E")
qed

AOT_theorem RM_1: assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi> \<rightarrow> \<psi>\<close> shows \<open>\<^bold>\<turnstile>\<^sub>\<box> \<box>\<phi> \<rightarrow> \<box>\<psi>\<close>
  using RM_1_prem assms by blast

lemmas RM = RM_1

AOT_theorem RM_2_prem: assumes \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<phi> \<rightarrow> \<psi>\<close> shows \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<phi> \<rightarrow> \<diamond>\<psi>\<close>
proof -
  AOT_have \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<not>\<psi> \<rightarrow> \<not>\<phi>\<close> using assms 
    by (simp add: contraposition_1_a)
  AOT_hence \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<box>\<not>\<psi> \<rightarrow> \<box>\<not>\<phi>\<close> using RM_1_prem by blast
  AOT_thus \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<phi> \<rightarrow> \<diamond>\<psi>\<close>
    by (meson "\<equiv>\<^sub>d\<^sub>fE" "\<equiv>\<^sub>d\<^sub>fI" AOT_dia deduction_theorem modus_tollens_1)
qed

AOT_theorem RM_2: assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi> \<rightarrow> \<psi>\<close> shows \<open>\<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<phi> \<rightarrow> \<diamond>\<psi>\<close>
  using RM_2_prem assms by blast

lemmas "RM\<diamond>" = RM_2

AOT_theorem RM_3_prem: assumes \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<phi> \<equiv> \<psi>\<close> shows \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<box>\<phi> \<equiv> \<box>\<psi>\<close>
proof -
  AOT_have \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<phi> \<rightarrow> \<psi>\<close> and \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<psi> \<rightarrow> \<phi>\<close> using assms "\<equiv>E" "\<rightarrow>I" by metis+
  AOT_hence \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<box>\<phi> \<rightarrow> \<box>\<psi>\<close> and \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<box>\<psi> \<rightarrow> \<box>\<phi>\<close> using RM_1_prem by metis+
  AOT_thus \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<box>\<phi> \<equiv> \<box>\<psi>\<close>
    by (simp add: intro_elim_2)
qed

AOT_theorem RM_3: assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi> \<equiv> \<psi>\<close> shows \<open>\<^bold>\<turnstile>\<^sub>\<box> \<box>\<phi> \<equiv> \<box>\<psi>\<close>
  using RM_3_prem assms by blast

lemmas RE = RM_3

AOT_theorem RM_4_prem: assumes \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<phi> \<equiv> \<psi>\<close> shows \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<phi> \<equiv> \<diamond>\<psi>\<close>
proof -
  AOT_have \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<phi> \<rightarrow> \<psi>\<close> and \<open>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<psi> \<rightarrow> \<phi>\<close> using assms "\<equiv>E" "\<rightarrow>I" by metis+
  AOT_hence \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<phi> \<rightarrow> \<diamond>\<psi>\<close> and \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<psi> \<rightarrow> \<diamond>\<phi>\<close> using RM_2_prem by metis+
  AOT_thus \<open>\<box>\<Gamma> \<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<phi> \<equiv> \<diamond>\<psi>\<close> by (simp add: intro_elim_2)
qed

AOT_theorem RM_4: assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi> \<equiv> \<psi>\<close> shows \<open>\<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<phi> \<equiv> \<diamond>\<psi>\<close>
  using RM_4_prem assms by blast

lemmas "RE\<diamond>" = RM_4

AOT_theorem KBasic_1: \<open>\<box>\<phi> \<rightarrow> \<box>(\<psi> \<rightarrow> \<phi>)\<close>
  by (simp add: RM pl_1[axiom_inst])

AOT_theorem KBasic_2: \<open>\<box>\<not>\<phi> \<rightarrow> \<box>(\<phi> \<rightarrow> \<psi>)\<close>
  by (simp add: RM useful_tautologies_3)

AOT_theorem KBasic_3: \<open>\<box>(\<phi> & \<psi>) \<equiv> (\<box>\<phi> & \<box>\<psi>)\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<box>(\<phi> & \<psi>)\<close>
  AOT_thus \<open>\<box>\<phi> & \<box>\<psi>\<close>
    by (meson RM con_dis_i_e_1 con_dis_taut_1 con_dis_taut_2 vdash_properties_6)
next
  AOT_have \<open>\<box>\<phi> \<rightarrow> \<box>(\<psi> \<rightarrow> (\<phi> & \<psi>))\<close> by (simp add: RM_1 con_dis_taut_5)
  AOT_hence \<open>\<box>\<phi> \<rightarrow> (\<box>\<psi> \<rightarrow> \<box>(\<phi> & \<psi>))\<close>  by (metis ded_thm_cor_1 qml_1[axiom_inst])
  moreover AOT_assume \<open>\<box>\<phi> & \<box>\<psi>\<close>
  ultimately AOT_show \<open>\<box>(\<phi> & \<psi>)\<close>
    using "\<rightarrow>E" "&E" by blast
qed

AOT_theorem KBasic_4: \<open>\<box>(\<phi> \<equiv> \<psi>) \<equiv> (\<box>(\<phi> \<rightarrow> \<psi>) & \<box>(\<psi> \<rightarrow> \<phi>))\<close>
proof -
  AOT_have \<theta>: \<open>\<box>((\<phi> \<rightarrow> \<psi>) & (\<psi> \<rightarrow> \<phi>)) \<equiv> (\<box>(\<phi> \<rightarrow> \<psi>) & \<box>(\<psi> \<rightarrow> \<phi>))\<close>
    by (fact KBasic_3)
  AOT_modally_strict {
    AOT_have \<open>(\<phi> \<equiv> \<psi>) \<equiv> ((\<phi> \<rightarrow> \<psi>) & (\<psi> \<rightarrow> \<phi>))\<close>
      by (fact AOT_equiv[THEN "\<equiv>Df"])
  }
  AOT_hence \<xi>: \<open>\<box>(\<phi> \<equiv> \<psi>) \<equiv> \<box>((\<phi> \<rightarrow> \<psi>) & (\<psi> \<rightarrow> \<phi>))\<close>
    by (rule RE)
  with \<xi> and \<theta> AOT_show \<open>\<box>(\<phi> \<equiv> \<psi>) \<equiv> (\<box>(\<phi> \<rightarrow> \<psi>) & \<box>(\<psi> \<rightarrow> \<phi>))\<close>
    using "\<equiv>E"(5) by blast
qed

AOT_theorem KBasic_5: \<open>(\<box>(\<phi> \<rightarrow> \<psi>) & \<box>(\<psi> \<rightarrow> \<phi>)) \<rightarrow> (\<box>\<phi> \<equiv> \<box>\<psi>)\<close>
proof -
  AOT_have \<open>\<box>(\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<box>\<phi> \<rightarrow> \<box>\<psi>)\<close>
    by (fact qml_1[axiom_inst])
  moreover AOT_have \<open>\<box>(\<psi> \<rightarrow> \<phi>) \<rightarrow> (\<box>\<psi> \<rightarrow> \<box>\<phi>)\<close>
    by (fact qml_1[axiom_inst])
  ultimately AOT_have \<open>(\<box>(\<phi> \<rightarrow> \<psi>) & \<box>(\<psi> \<rightarrow> \<phi>)) \<rightarrow> ((\<box>\<phi> \<rightarrow> \<box>\<psi>) & (\<box>\<psi> \<rightarrow> \<box>\<phi>))\<close>
    by (metis "&I" MP oth_class_taut_8_d)
  moreover AOT_have \<open>((\<box>\<phi> \<rightarrow> \<box>\<psi>) & (\<box>\<psi> \<rightarrow> \<box>\<phi>)) \<rightarrow> (\<box>\<phi> \<equiv> \<box>\<psi>)\<close>
    using AOT_equiv[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<rightarrow>I" by blast
  ultimately AOT_show \<open>(\<box>(\<phi> \<rightarrow> \<psi>) & \<box>(\<psi> \<rightarrow> \<phi>)) \<rightarrow> (\<box>\<phi> \<equiv> \<box>\<psi>)\<close>
    by (metis ded_thm_cor_1)
qed

AOT_theorem KBasic_6: \<open>\<box>(\<phi>\<equiv> \<psi>) \<rightarrow> (\<box>\<phi> \<equiv> \<box>\<psi>)\<close>
  using KBasic_4 KBasic_5 deduction_theorem intro_elim_3_a vdash_properties_10 by blast
AOT_theorem KBasic_7: \<open>((\<box>\<phi> & \<box>\<psi>) \<or> (\<box>\<not>\<phi> & \<box>\<not>\<psi>)) \<rightarrow> \<box>(\<phi> \<equiv> \<psi>)\<close>
proof (rule "\<rightarrow>I"; drule "\<or>E"(1); (rule "\<rightarrow>I")?)
  AOT_assume \<open>\<box>\<phi> & \<box>\<psi>\<close>
  AOT_hence \<open>\<box>\<phi>\<close> and \<open>\<box>\<psi>\<close> using "&E" by blast+
  AOT_hence \<open>\<box>(\<phi> \<rightarrow> \<psi>)\<close> and \<open>\<box>(\<psi> \<rightarrow> \<phi>)\<close> using KBasic_1 "\<rightarrow>E" by blast+
  AOT_hence \<open>\<box>(\<phi> \<rightarrow> \<psi>) & \<box>(\<psi> \<rightarrow> \<phi>)\<close> using "&I" by blast
  AOT_thus \<open>\<box>(\<phi> \<equiv> \<psi>)\<close>  by (metis KBasic_4 intro_elim_3_b)
next
  AOT_assume \<open>\<box>\<not>\<phi> & \<box>\<not>\<psi>\<close>
  AOT_hence 0: \<open>\<box>(\<not>\<phi> & \<not>\<psi>)\<close> using KBasic_3[THEN "\<equiv>E"(2)] by blast
  AOT_modally_strict {
    AOT_have \<open>(\<not>\<phi> & \<not>\<psi>) \<rightarrow> (\<phi> \<equiv> \<psi>)\<close>
      by (metis con_dis_i_e_2_a con_dis_i_e_2_b deduction_theorem intro_elim_2 reductio_aa_1)
  }
  AOT_hence \<open>\<box>(\<not>\<phi> & \<not>\<psi>) \<rightarrow> \<box>(\<phi> \<equiv> \<psi>)\<close>
    by (rule RM)
  AOT_thus \<open>\<box>(\<phi> \<equiv> \<psi>)\<close> using 0 "\<rightarrow>E" by blast
qed(auto)

AOT_theorem KBasic_8: \<open>\<box>(\<phi> & \<psi>) \<rightarrow> \<box>(\<phi> \<equiv> \<psi>)\<close>
  by (meson RM_1 con_dis_i_e_2_a con_dis_i_e_2_b deduction_theorem intro_elim_2)
AOT_theorem KBasic_9: \<open>\<box>(\<not>\<phi> & \<not>\<psi>) \<rightarrow> \<box>(\<phi> \<equiv> \<psi>)\<close>
  by (metis RM_1 con_dis_i_e_2_a con_dis_i_e_2_b deduction_theorem intro_elim_2 raa_cor_4)
AOT_theorem KBasic_10: \<open>\<box>\<phi> \<equiv> \<box>\<not>\<not>\<phi>\<close>
  by (simp add: RM_3 oth_class_taut_3_b)
AOT_theorem KBasic_11: \<open>\<not>\<box>\<phi> \<equiv> \<diamond>\<not>\<phi>\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_show \<open>\<diamond>\<not>\<phi>\<close> if \<open>\<not>\<box>\<phi>\<close>
    using that "\<equiv>\<^sub>d\<^sub>fI" AOT_dia KBasic_10 intro_elim_3_c by blast
next
  AOT_show \<open>\<not>\<box>\<phi>\<close> if \<open>\<diamond>\<not>\<phi>\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" AOT_dia KBasic_10 intro_elim_3_d that by blast
qed
AOT_theorem KBasic_12: \<open>\<box>\<phi> \<equiv> \<not>\<diamond>\<not>\<phi>\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_show \<open>\<not>\<diamond>\<not>\<phi>\<close> if \<open>\<box>\<phi>\<close>
    using "\<not>\<not>I" KBasic_11 intro_elim_3_c that by blast
next
  AOT_show \<open>\<box>\<phi>\<close> if \<open>\<not>\<diamond>\<not>\<phi>\<close>
  using KBasic_11 intro_elim_3_a reductio_aa_1 that by blast
qed
AOT_theorem KBasic_13: \<open>\<box>(\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<diamond>\<phi> \<rightarrow> \<diamond>\<psi>)\<close>
proof -
  AOT_have \<open>\<phi> \<rightarrow> \<psi> \<^bold>\<turnstile>\<^sub>\<box> \<phi> \<rightarrow> \<psi>\<close> by blast
  AOT_hence \<open>\<box>(\<phi> \<rightarrow> \<psi>) \<^bold>\<turnstile>\<^sub>\<box> \<diamond>\<phi> \<rightarrow> \<diamond>\<psi>\<close>
    using RM_2_prem by blast
  AOT_thus \<open>\<box>(\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<diamond>\<phi> \<rightarrow> \<diamond>\<psi>)\<close> using "\<rightarrow>I" by blast
qed

AOT_theorem KBasic_14: \<open>\<diamond>\<box>\<phi> \<equiv> \<not>\<box>\<diamond>\<not>\<phi>\<close>
  by (meson "RE\<diamond>" KBasic_11 KBasic_12 intro_elim_3_f oth_class_taut_3_a)
AOT_theorem KBasic_15: \<open>(\<box>\<phi> \<or> \<box>\<psi>) \<rightarrow> \<box>(\<phi> \<or> \<psi>)\<close>
proof -
  AOT_modally_strict {
    AOT_have \<open>\<phi> \<rightarrow> (\<phi> \<or> \<psi>)\<close> and \<open>\<psi> \<rightarrow> (\<phi> \<or> \<psi>)\<close>
      by (auto simp: con_dis_taut_3 con_dis_taut_4)
  }
  AOT_hence \<open>\<box>\<phi> \<rightarrow> \<box>(\<phi> \<or> \<psi>)\<close> and \<open>\<box>\<psi> \<rightarrow> \<box>(\<phi> \<or> \<psi>)\<close>
    using RM by blast+
  AOT_thus \<open>(\<box>\<phi> \<or> \<box>\<psi>) \<rightarrow> \<box>(\<phi> \<or> \<psi>)\<close>
    by (metis con_dis_i_e_4_a deduction_theorem)
qed

AOT_theorem KBasic_16: \<open>(\<box>\<phi> & \<diamond>\<psi>) \<rightarrow> \<diamond>(\<phi> & \<psi>)\<close>
  by (meson KBasic_13 RM_1 con_dis_taut_5 ded_thm_cor_1 oth_class_taut_7_b vdash_properties_6)

AOT_theorem rule_sub_lem_1_a:
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<box>(\<psi> \<equiv> \<chi>)\<close>
  shows \<open>\<^bold>\<turnstile>\<^sub>\<box> \<not>\<psi> \<equiv> \<not>\<chi>\<close>
  using qml_2[axiom_inst, THEN "\<rightarrow>E", OF assms]
        intro_elim_3_a oth_class_taut_4_b by blast
    
AOT_theorem rule_sub_lem_1_b:
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<box>(\<psi> \<equiv> \<chi>)\<close>
  shows \<open>\<^bold>\<turnstile>\<^sub>\<box> (\<psi> \<rightarrow> \<Theta>) \<equiv> (\<chi> \<rightarrow> \<Theta>)\<close>
  using qml_2[axiom_inst, THEN "\<rightarrow>E", OF assms]
  using oth_class_taut_4_c vdash_properties_6 by blast

AOT_theorem rule_sub_lem_1_c:
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<box>(\<psi> \<equiv> \<chi>)\<close>
  shows \<open>\<^bold>\<turnstile>\<^sub>\<box> (\<Theta> \<rightarrow> \<psi>) \<equiv> (\<Theta> \<rightarrow> \<chi>)\<close>
  using qml_2[axiom_inst, THEN "\<rightarrow>E", OF assms]
  using oth_class_taut_4_d vdash_properties_6 by blast

AOT_theorem rule_sub_lem_1_d:
  assumes \<open>for arbitrary \<alpha>: \<^bold>\<turnstile>\<^sub>\<box> \<box>(\<psi>{\<alpha>} \<equiv> \<chi>{\<alpha>})\<close>
  shows \<open>\<^bold>\<turnstile>\<^sub>\<box> \<forall>\<alpha> \<psi>{\<alpha>} \<equiv> \<forall>\<alpha> \<chi>{\<alpha>}\<close>
proof -
  AOT_modally_strict {
    AOT_have \<open>\<forall>\<alpha> (\<psi>{\<alpha>} \<equiv> \<chi>{\<alpha>})\<close>
      using qml_2[axiom_inst, THEN "\<rightarrow>E", OF assms] "\<forall>I" by fast
    AOT_hence 0: \<open>\<psi>{\<alpha>} \<equiv> \<chi>{\<alpha>}\<close> for \<alpha> using "\<forall>E" by blast
    AOT_show \<open>\<forall>\<alpha> \<psi>{\<alpha>} \<equiv> \<forall>\<alpha> \<chi>{\<alpha>}\<close>
    proof (rule "\<equiv>I"; rule "\<rightarrow>I")
      AOT_assume \<open>\<forall>\<alpha> \<psi>{\<alpha>}\<close>
      AOT_hence \<open>\<psi>{\<alpha>}\<close> for \<alpha> using "\<forall>E" by blast
      AOT_hence \<open>\<chi>{\<alpha>}\<close> for \<alpha> using 0 "\<equiv>E" by blast
      AOT_thus \<open>\<forall>\<alpha> \<chi>{\<alpha>}\<close> by (rule "\<forall>I")
    next
      AOT_assume \<open>\<forall>\<alpha> \<chi>{\<alpha>}\<close>
      AOT_hence \<open>\<chi>{\<alpha>}\<close> for \<alpha> using "\<forall>E" by blast
      AOT_hence \<open>\<psi>{\<alpha>}\<close> for \<alpha> using 0 "\<equiv>E" by blast
      AOT_thus \<open>\<forall>\<alpha> \<psi>{\<alpha>}\<close> by (rule "\<forall>I")
    qed
  }
qed

AOT_theorem rule_sub_lem_1_e:
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<box>(\<psi> \<equiv> \<chi>)\<close>
  shows \<open>\<^bold>\<turnstile>\<^sub>\<box> [\<lambda> \<psi>] \<equiv> [\<lambda> \<chi>]\<close>
  using qml_2[axiom_inst, THEN "\<rightarrow>E", OF assms]
  using intro_elim_3_a propositions_lemma_6 by blast

AOT_theorem rule_sub_lem_1_f:
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<box>(\<psi> \<equiv> \<chi>)\<close>
  shows \<open>\<^bold>\<turnstile>\<^sub>\<box> \<^bold>\<A>\<psi> \<equiv> \<^bold>\<A>\<chi>\<close>
  using qml_2[axiom_inst, THEN "\<rightarrow>E", OF assms, THEN RA(2)]
  by (metis Act_Basic_5 intro_elim_3_a)

AOT_theorem rule_sub_lem_1_g:
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<box>(\<psi> \<equiv> \<chi>)\<close>
  shows \<open>\<^bold>\<turnstile>\<^sub>\<box> \<box>\<psi> \<equiv> \<box>\<chi>\<close>
  using KBasic_6 assms vdash_properties_6 by blast

inductive AOT_subformula where
  AOT_subformula_self: "AOT_subformula \<phi> \<phi>"
| AOT_subformula_not: "AOT_subformula \<phi> \<psi> \<Longrightarrow> AOT_subformula \<phi> \<guillemotleft>\<not>\<psi>\<guillemotright>"
| AOT_subformula_imp_1: "AOT_subformula \<phi> \<psi> \<Longrightarrow> AOT_subformula \<phi> \<guillemotleft>\<psi> \<rightarrow> \<chi>\<guillemotright>"
| AOT_subformula_imp_2: "AOT_subformula \<phi> \<psi> \<Longrightarrow> AOT_subformula \<phi> \<guillemotleft>\<chi> \<rightarrow> \<psi>\<guillemotright>"
| AOT_subformula_imp_box: "AOT_subformula \<phi> \<psi> \<Longrightarrow> AOT_subformula \<phi> \<guillemotleft>\<box>\<psi>\<guillemotright>"
| AOT_subformula_imp_act: "AOT_subformula \<phi> \<psi> \<Longrightarrow> AOT_subformula \<phi> \<guillemotleft>\<^bold>\<A>\<psi>\<guillemotright>"
| AOT_subformula_by_def: "AOT_model_equiv_def \<phi> \<psi> \<Longrightarrow> AOT_subformula \<chi> \<psi> \<Longrightarrow> AOT_subformula \<chi> \<phi>"

inductive AOT_subformula_subst where
  AOT_subformula_subst_id: "AOT_subformula_subst (\<lambda>\<phi>. \<phi>)"
| AOT_subformula_subst_const: "AOT_subformula_subst (\<lambda>\<phi>. \<psi>)"
| AOT_subformula_subst_not: "AOT_subformula_subst \<Theta> \<Longrightarrow> AOT_subformula_subst (\<lambda> \<phi>. \<guillemotleft>\<not>\<Theta>{\<phi>}\<guillemotright>)"
| AOT_subformula_subst_imp: "AOT_subformula_subst \<Theta> \<Longrightarrow> AOT_subformula_subst \<Xi> \<Longrightarrow> AOT_subformula_subst (\<lambda> \<phi>. \<guillemotleft>\<Theta>{\<phi>} \<rightarrow> \<Xi>{\<phi>}\<guillemotright>)"
| AOT_subformula_subst_lambda0: "AOT_subformula_subst \<Theta> \<Longrightarrow> AOT_subformula_subst (\<lambda> \<phi>. (AOT_lambda0 (\<Theta> \<phi>)))"
| AOT_subformula_subst_act: "AOT_subformula_subst \<Theta> \<Longrightarrow> AOT_subformula_subst (\<lambda> \<phi>. \<guillemotleft>\<^bold>\<A>\<Theta>{\<phi>}\<guillemotright>)"
| AOT_subformula_subst_box: "AOT_subformula_subst \<Theta> \<Longrightarrow> AOT_subformula_subst (\<lambda> \<phi>. \<guillemotleft>\<box>\<Theta>{\<phi>}\<guillemotright>)"
| AOT_subformula_subst_by_def: "(\<And> \<psi> . AOT_model_equiv_def (\<Theta> \<psi>) (\<Xi> \<psi>)) \<Longrightarrow> AOT_subformula_subst \<Xi> \<Longrightarrow> AOT_subformula_subst \<Theta>"

lemma "AOT_subformula_subst (\<lambda> \<phi> .\<guillemotleft>\<not>(\<phi> \<rightarrow> \<psi>)\<guillemotright>)"
  using AOT_subformula_subst.intros by blast

lemma "AOT_subformula_subst \<Theta> \<Longrightarrow> AOT_subformula_subst \<Xi> \<Longrightarrow> AOT_subformula_subst (\<lambda> \<phi> .\<guillemotleft>\<Theta>{\<phi>} & \<Xi>{\<phi>}\<guillemotright>)"
  apply (rule AOT_subformula_subst_by_def[OF AOT_conj])
  using AOT_subformula_subst.intros by fastforce

lemma "AOT_subformula_subst \<Theta> \<Longrightarrow> AOT_subformula_subst \<Xi> \<Longrightarrow> AOT_subformula_subst (\<lambda> \<phi> .\<guillemotleft>\<Theta>{\<phi>} \<or> \<Xi>{\<phi>}\<guillemotright>)"
  apply (rule AOT_subformula_subst_by_def[OF AOT_disj])
  using AOT_subformula_subst.intros by fastforce

syntax "_AOT_subformula" :: "\<phi>' \<Rightarrow> \<phi>' \<Rightarrow> AOT_prop" ("SUBFORMULA'(_,_')")
syntax "_AOT_subformula_subst" :: "any \<Rightarrow> AOT_prop" ("SUBFORMULA'_SUBST'(_')")

translations
  "_AOT_subformula \<phi> \<psi>" => "CONST Trueprop (CONST AOT_subformula \<phi> \<psi>)"
  "_AOT_subformula_subst \<phi>" => "CONST Trueprop (CONST AOT_subformula_subst \<phi>)"

AOT_syntax_print_translations
  "_AOT_subformula \<phi> \<psi>" <= "CONST AOT_subformula \<phi> \<psi>"
  "_AOT_subformula_subst \<phi>" <= "CONST AOT_subformula_subst \<phi>"

AOT_theorem rule_sub_lem_2_a: assumes "SUBFORMULA_SUBST(\<phi>)" and "\<^bold>\<turnstile>\<^sub>\<box> \<box>(\<psi> \<equiv> \<chi>)" shows "\<^bold>\<turnstile>\<^sub>\<box> \<phi>{\<psi>} \<equiv> \<phi>{\<chi>}"
  using assms including AOT_syntax
proof (induct arbitrary: \<psi> \<chi>)
  case AOT_subformula_subst_id
  then show ?case
    using intro_elim_3_b oth_class_taut_4_b rule_sub_lem_1_a by blast
next
  case (AOT_subformula_subst_const \<psi>) 
  then show ?case by (simp add: oth_class_taut_3_a)
next
  case (AOT_subformula_subst_not \<Theta>)
  then show ?case
    by (simp add: RN rule_sub_lem_1_a)
next
  case (AOT_subformula_subst_imp \<Theta> \<Xi>)
  then show ?case
    by (meson RN intro_elim_3_e rule_sub_lem_1_b rule_sub_lem_1_c)
next
  case (AOT_subformula_subst_lambda0 \<Theta>)
  then show ?case by (simp add: RN rule_sub_lem_1_e)
next
  case (AOT_subformula_subst_act \<Theta>)
  then show ?case by (simp add: RN rule_sub_lem_1_f)
next
  case (AOT_subformula_subst_box \<Theta>)
  then show ?case by (simp add: RM_3)
next
  case (AOT_subformula_subst_by_def \<Theta> \<Xi>)
  AOT_modally_strict {
    AOT_have \<open>\<Xi>{\<psi>} \<equiv> \<Xi>{\<chi>}\<close> using AOT_subformula_subst_by_def by simp
    AOT_thus \<open>\<Theta>{\<psi>} \<equiv> \<Theta>{\<chi>}\<close>
      using "\<equiv>Df"[OF AOT_subformula_subst_by_def(1), of _ \<psi>] "\<equiv>Df"[OF AOT_subformula_subst_by_def(1), of _ \<chi>]
       by (metis intro_elim_3_f oth_class_taut_3_a)
  }
qed

AOT_theorem rule_sub_lem_2_b: assumes "for arbitrary \<alpha>: SUBFORMULA_SUBST(\<phi> \<alpha>)"
  and "for arbitrary \<alpha>: \<^bold>\<turnstile>\<^sub>\<box> \<box>(\<psi>{\<alpha>} \<equiv> \<chi>{\<alpha>})" shows "\<^bold>\<turnstile>\<^sub>\<box> \<forall>\<alpha> \<phi>{\<alpha>,\<psi>{\<alpha>}} \<equiv> \<forall>\<alpha> \<phi>{\<alpha>,\<chi>{\<alpha>}}"
proof -
  AOT_modally_strict {
    AOT_show \<open>\<forall>\<alpha> \<phi>{\<alpha>,\<psi>{\<alpha>}} \<equiv> \<forall>\<alpha> \<phi>{\<alpha>,\<chi>{\<alpha>}}\<close>
      using rule_sub_lem_2_a[OF assms(1), OF assms(2), THEN RN]
      by (simp add: rule_sub_lem_1_d)
  }
qed

AOT_theorem assumes "for arbitrary \<alpha>:  \<^bold>\<turnstile>\<^sub>\<box> \<box>(\<psi>{\<alpha>} \<equiv> \<chi>{\<alpha>})"
  shows "\<forall>\<alpha> (\<psi>{\<alpha>} \<rightarrow> \<not>\<psi>{\<alpha>} \<rightarrow> p) \<equiv> \<forall>\<alpha> (\<chi>{\<alpha>} \<rightarrow> \<not>\<chi>{\<alpha>} \<rightarrow> p)"
  apply (rule rule_sub_lem_2_b[rotated, of \<psi> \<chi>])
  using assms apply simp
  by (simp add: AOT_subformula_subst.intros)

lemma "AOT_subformula \<phi> \<psi> \<Longrightarrow> AOT_subformula \<phi> \<guillemotleft>\<chi> & \<psi>\<guillemotright>"
  apply (rule AOT_subformula_by_def)
  using AOT_conj apply blast
  by(auto intro: AOT_subformula.intros)
lemma "AOT_subformula \<phi> \<psi> \<Longrightarrow> AOT_subformula \<phi> \<guillemotleft>\<psi> & \<chi>\<guillemotright>"
  apply (rule AOT_subformula_by_def)
  using AOT_conj apply blast
  by(auto intro: AOT_subformula.intros)



end
