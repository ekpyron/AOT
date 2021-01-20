theory AOT_PLM
  imports AOT_axioms
begin

AOT_theorem modus_ponens: assumes \<open>\<phi>\<close> and \<open>\<phi> \<rightarrow> \<psi>\<close> shows \<open>\<psi>\<close>
  using assms by (simp add: AOT_sem_imp) (* NOTE: semantics needed *)
lemmas MP = modus_ponens

AOT_theorem non_con_thm_thm: assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi>\<close> shows \<open>\<^bold>\<turnstile> \<phi>\<close>
  using assms by simp

AOT_theorem vdash_properties_3: assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi>\<close> shows \<open>\<Gamma> \<^bold>\<turnstile> \<phi>\<close>
  using assms by blast

AOT_theorem vdash_properties_5: assumes \<open>\<Gamma>\<^sub>1 \<^bold>\<turnstile> \<phi>\<close> and \<open>\<Gamma>\<^sub>2 \<^bold>\<turnstile> \<phi> \<rightarrow> \<psi>\<close> shows \<open>\<Gamma>\<^sub>1, \<Gamma>\<^sub>2 \<^bold>\<turnstile> \<psi>\<close>
  using MP assms by blast

AOT_theorem vdash_properties_6: assumes \<open>\<phi>\<close> and \<open>\<phi> \<rightarrow> \<psi>\<close> shows \<open>\<psi>\<close>
  using MP assms by blast

AOT_theorem vdash_properties_8: assumes \<open>\<Gamma> \<^bold>\<turnstile> \<phi>\<close> and \<open>\<phi> \<^bold>\<turnstile> \<psi>\<close> shows \<open>\<Gamma> \<^bold>\<turnstile> \<psi>\<close>
  using assms by argo

AOT_theorem vdash_properties_9: assumes \<open>\<phi>\<close> shows \<open>\<psi> \<rightarrow> \<phi>\<close>
  using MP pl_1 assms by blast

AOT_theorem vdash_properties_10: assumes \<open>\<phi> \<rightarrow> \<psi>\<close> and \<open>\<phi>\<close> shows \<open>\<psi>\<close>
  using MP assms by blast
lemmas "\<rightarrow>E" = vdash_properties_10

AOT_theorem rule_gen: assumes \<open>for arbitrary \<alpha>: \<phi>{\<alpha>}\<close> shows \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close>
  using assms by (metis AOT_var_of_term_inverse AOT_sem_denotes AOT_sem_forall) (* NOTE: semantics needed *)
lemmas GEN = rule_gen
AOT_theorem RN: assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi>\<close> shows \<open>\<box>\<phi>\<close>
  by (simp add: AOT_sem_box assms) (* NOTE: semantics needed *)
AOT_theorem df_rules_formulas_1: assumes \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>\<close> shows \<open>\<phi> \<rightarrow> \<psi>\<close>
  using assms by (simp_all add: AOT_model_equiv_def AOT_sem_imp) (* NOTE: semantics needed *)
AOT_theorem df_rules_formulas_2: assumes \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>\<close> shows \<open>\<psi> \<rightarrow> \<phi>\<close>
  using assms by (simp_all add: AOT_model_equiv_def AOT_sem_imp) (* NOTE: semantics needed *)


AOT_theorem df_rules_terms_1:
  assumes \<open>\<tau>{\<alpha>\<^sub>1...\<alpha>\<^sub>n} =\<^sub>d\<^sub>f \<sigma>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}\<close>
  shows \<open>(\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down> \<rightarrow> \<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n} = \<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}) & (\<not>\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down> \<rightarrow> \<not>\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down>)\<close>
  using assms by (simp add: AOT_sem_conj AOT_sem_imp AOT_sem_eq AOT_sem_not AOT_sem_denotes AOT_model_id_def) (* NOTE: semantics needed *)
AOT_theorem df_rules_terms_2:
  assumes \<open>\<tau> =\<^sub>d\<^sub>f \<sigma>\<close>
  shows \<open>(\<sigma>\<down> \<rightarrow> \<tau> = \<sigma>) & (\<not>\<sigma>\<down> \<rightarrow> \<not>\<tau>\<down>)\<close>
  using assms by (metis df_rules_terms_1 case_unit_Unity)


AOT_theorem if_p_then_p: \<open>\<phi> \<rightarrow> \<phi>\<close>
  by (meson pl_1 pl_2 MP)

AOT_theorem deduction_theorem: assumes \<open>\<phi> \<^bold>\<turnstile> \<psi>\<close> shows \<open>\<phi> \<rightarrow> \<psi>\<close>
  using assms by (simp add: AOT_sem_imp) (* NOTE: semantics needed *)
lemmas CP = deduction_theorem
lemmas "\<rightarrow>I" = deduction_theorem

AOT_theorem ded_thm_cor_1: assumes \<open>\<phi> \<rightarrow> \<psi>\<close> and \<open>\<psi> \<rightarrow> \<chi>\<close> shows \<open>\<phi> \<rightarrow> \<chi>\<close>
  using "\<rightarrow>E" "\<rightarrow>I" assms by blast
AOT_theorem ded_thm_cor_2: assumes \<open>\<phi> \<rightarrow> (\<psi> \<rightarrow> \<chi>)\<close> and \<open>\<psi>\<close> shows \<open>\<phi> \<rightarrow> \<chi>\<close>
  using "\<rightarrow>E" "\<rightarrow>I" assms by blast

AOT_theorem useful_tautologies_1: \<open>\<not>\<not>\<phi> \<rightarrow> \<phi>\<close>
  by (metis pl_3 "\<rightarrow>I" ded_thm_cor_1)
AOT_theorem useful_tautologies_2: \<open>\<phi> \<rightarrow> \<not>\<not>\<phi>\<close>
  by (metis pl_3 "\<rightarrow>I" ded_thm_cor_2)
AOT_theorem useful_tautologies_3: \<open>\<not>\<phi> \<rightarrow> (\<phi> \<rightarrow> \<psi>)\<close>
  by (meson ded_thm_cor_2 pl_3 "\<rightarrow>I")
AOT_theorem useful_tautologies_4: \<open>(\<not>\<psi> \<rightarrow> \<not>\<phi>) \<rightarrow> (\<phi> \<rightarrow> \<psi>)\<close>
  by (meson pl_3 ded_thm_cor_1 "\<rightarrow>I")
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
  by (metis "\<rightarrow>I" MP pl_3)

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
  using ded_thm_cor_1 df_rules_formulas_2 pl_1 AOT_disj by blast
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
  using "\<rightarrow>E" cqt_1 assms by blast
AOT_theorem rule_ui_2_a: assumes \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close> shows \<open>\<phi>{\<beta>}\<close>
  by (simp add: rule_ui_1 cqt_2_const_var assms)
(* TODO: precise proviso in PLM *)
AOT_theorem rule_ui_2_b:
  assumes \<open>\<forall>F \<phi>{F}\<close> and \<open>INSTANCE_OF_CQT_2(\<psi>)\<close>
  shows \<open>\<phi>{[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<psi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]}\<close>
  by (simp add: rule_ui_1 cqt_2_lambda assms)
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
  using cqt_3 by auto

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
  using existential_1 cqt_2_const_var assms by blast

AOT_theorem existential_2_b:
  assumes \<open>\<phi>{[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<psi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]}\<close> and \<open>INSTANCE_OF_CQT_2(\<psi>)\<close>
  shows \<open>\<exists>\<alpha> \<phi>{\<alpha>}\<close>
  using existential_1 cqt_2_lambda assms by blast
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
  using cqt_2_lambda0 by auto

AOT_theorem log_prop_prop_2: \<open>\<phi>\<down>\<close>
  by (rule "\<equiv>\<^sub>d\<^sub>fI"[OF existence_3]; rule cqt_2_lambda)
     (auto intro!: AOT_instance_of_cqt_2_intro)

AOT_theorem exist_nec: \<open>\<tau>\<down> \<rightarrow> \<box>\<tau>\<down>\<close>
proof -
  AOT_have \<open>\<forall>\<beta> \<box>\<beta>\<down>\<close>
    by (simp add: GEN RN cqt_2_const_var)
  AOT_thus \<open>\<tau>\<down> \<rightarrow> \<box>\<tau>\<down>\<close>
    using cqt_1 "\<rightarrow>E" by blast
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
           (metis cqt_5a "\<rightarrow>I" "\<rightarrow>E" "&E"(2))+
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
           (metis cqt_5a "\<rightarrow>I" "\<rightarrow>E" "&E"(2))+
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
    apply (rule GEN)+ using l_identity by force
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
    apply (rule GEN)+ using l_identity by force
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
    apply (rule GEN)+ using l_identity by blast
  ultimately AOT_have \<open>\<tau> = \<sigma> \<rightarrow> (\<phi>{\<tau>} \<rightarrow> \<phi>{\<sigma>})\<close>
    using "\<forall>E"(1) by blast
  AOT_thus \<open>\<phi>{\<sigma>}\<close> using assms "\<rightarrow>E" by blast
qed
lemmas "=E" = "rule=E"

AOT_theorem propositions_lemma_1: \<open>[\<lambda> \<phi>] = \<phi>\<close>
proof -
  AOT_have \<open>\<phi>\<down>\<close> by (simp add: log_prop_prop_2)
  moreover AOT_have \<open>\<forall>p [\<lambda> p] = p\<close> using lambda_predicates_3_b "\<forall>I" by fast
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
    by (rule cqt_2_lambda) (auto intro!: AOT_instance_of_cqt_2_intro) (* TODO: make this a proof method *)
  AOT_hence 1: \<open>O! = [\<lambda>x \<diamond>[E!]x]\<close> using df_rules_terms_2[OF oa_1, THEN "&E"(1)] "\<rightarrow>E" by blast
  AOT_show \<open>O!\<down>\<close> using "t=t-proper_1"[THEN "\<rightarrow>E", OF 1] by simp
qed

AOT_theorem oa_exist_2: \<open>A!\<down>\<close>
proof -
  AOT_have \<open>[\<lambda>x \<not>\<diamond>[E!]x]\<down>\<close>
    by (rule cqt_2_lambda) (auto intro!: AOT_instance_of_cqt_2_intro) (* TODO: make this a proof method *)
  AOT_hence 1: \<open>A! = [\<lambda>x \<not>\<diamond>[E!]x]\<close> using df_rules_terms_2[OF oa_2, THEN "&E"(1)] "\<rightarrow>E" by blast
  AOT_show \<open>A!\<down>\<close> using "t=t-proper_1"[THEN "\<rightarrow>E", OF 1] by simp
qed

AOT_theorem oa_exist_3: \<open>O!x \<or> A!x\<close>
proof(rule raa_cor_1)
  AOT_assume \<open>\<not>(O!x \<or> A!x)\<close>
  AOT_hence A: \<open>\<not>O!x\<close> and B: \<open>\<not>A!x\<close>
    using con_dis_taut_3 modus_tollens_1 con_dis_i_e_3_b raa_cor_5 by blast+
  AOT_have C: \<open>O! = [\<lambda>x \<diamond>[E!]x]\<close>
    by (rule df_rules_terms_2[OF oa_1, THEN "&E"(1), THEN "\<rightarrow>E"]; rule cqt_2_lambda)
       (auto intro!: AOT_instance_of_cqt_2_intro)
  AOT_have D: \<open>A! = [\<lambda>x \<not>\<diamond>[E!]x]\<close>
    by (rule df_rules_terms_2[OF oa_2, THEN "&E"(1), THEN "\<rightarrow>E"]; rule cqt_2_lambda)
       (auto intro!: AOT_instance_of_cqt_2_intro)
  AOT_have E: \<open>\<not>[\<lambda>x \<diamond>[E!]x]x\<close>
    using A C "=E" by fast
  AOT_have F: \<open>\<not>[\<lambda>x \<not>\<diamond>[E!]x]x\<close>
    using B D "=E" by fast
  AOT_have G: \<open>[\<lambda>x \<diamond>[E!]x]x \<equiv> \<diamond>[E!]x\<close>
    by (rule lambda_predicates_2[THEN "\<rightarrow>E"]; rule cqt_2_lambda)
       (auto intro!: AOT_instance_of_cqt_2_intro)
  AOT_have H: \<open>[\<lambda>x \<not>\<diamond>[E!]x]x \<equiv> \<not>\<diamond>[E!]x\<close>
    by (rule lambda_predicates_2[THEN "\<rightarrow>E"]; rule cqt_2_lambda)
       (auto intro!: AOT_instance_of_cqt_2_intro)
  AOT_show \<open>\<not>\<diamond>[E!]x & \<not>\<not>\<diamond>[E!]x\<close> using G E "\<equiv>E" H F "\<equiv>E" "&I" by metis
qed

AOT_theorem p_identity_thm2_1: \<open>F = G \<equiv> \<box>\<forall>x(x[F] \<equiv> x[G])\<close>
proof -
  AOT_have \<open>F = G \<equiv> F\<down> & G\<down> & \<box>\<forall>x(x[F] \<equiv> x[G])\<close>
    using p_identity df_rules_formulas_1 df_rules_formulas_2 "\<rightarrow>E" "&E" "\<equiv>I" "\<rightarrow>I" by blast
  moreover AOT_have \<open>F\<down>\<close> and \<open>G\<down>\<close>
    by (auto simp: cqt_2_const_var)
  ultimately AOT_show \<open>F = G \<equiv> \<box>\<forall>x(x[F] \<equiv> x[G])\<close>
    using df_simplify_1 "&I" by blast
qed

AOT_theorem p_identity_thm2_2_a: \<open>F = G \<equiv> \<forall>y\<^sub>1([\<lambda>x [F]xy\<^sub>1] = [\<lambda>x [G]xy\<^sub>1] & [\<lambda>x [F]y\<^sub>1x] = [\<lambda>x [G]y\<^sub>1x])\<close>
proof -
  AOT_have \<open>F = G \<equiv> F\<down> & G\<down> & \<forall>y\<^sub>1([\<lambda>x [F]xy\<^sub>1] = [\<lambda>x [G]xy\<^sub>1] & [\<lambda>x [F]y\<^sub>1x] = [\<lambda>x [G]y\<^sub>1x])\<close>
    using p_identity_2_a df_rules_formulas_1 df_rules_formulas_2 "\<rightarrow>E" "&E" "\<equiv>I" "\<rightarrow>I" by blast
  moreover AOT_have \<open>F\<down>\<close> and \<open>G\<down>\<close>
    by (auto simp: cqt_2_const_var)
  ultimately show ?thesis
    using df_simplify_1 "&I" by blast
qed
    
AOT_theorem p_identity_thm2_2_b: \<open>F = G \<equiv> \<forall>y\<^sub>1\<forall>y\<^sub>2([\<lambda>x [F]xy\<^sub>1y\<^sub>2] = [\<lambda>x [G]xy\<^sub>1y\<^sub>2] & [\<lambda>x [F]y\<^sub>1xy\<^sub>2] = [\<lambda>x [G]y\<^sub>1xy\<^sub>2] & [\<lambda>x [F]y\<^sub>1y\<^sub>2x] = [\<lambda>x [G]y\<^sub>1y\<^sub>2x])\<close>
proof -
  AOT_have \<open>F = G \<equiv> F\<down> & G\<down> & \<forall>y\<^sub>1\<forall>y\<^sub>2([\<lambda>x [F]xy\<^sub>1y\<^sub>2] = [\<lambda>x [G]xy\<^sub>1y\<^sub>2] & [\<lambda>x [F]y\<^sub>1xy\<^sub>2] = [\<lambda>x [G]y\<^sub>1xy\<^sub>2] & [\<lambda>x [F]y\<^sub>1y\<^sub>2x] = [\<lambda>x [G]y\<^sub>1y\<^sub>2x])\<close>
    using p_identity_2_b df_rules_formulas_1 df_rules_formulas_2 "\<rightarrow>E" "&E" "\<equiv>I" "\<rightarrow>I" by blast
  moreover AOT_have \<open>F\<down>\<close> and \<open>G\<down>\<close>
    by (auto simp: cqt_2_const_var)
  ultimately show ?thesis
    using df_simplify_1 "&I" by blast
qed

AOT_theorem p_identity_thm2_2_c: \<open>F = G \<equiv> \<forall>y\<^sub>1\<forall>y\<^sub>2\<forall>y\<^sub>3([\<lambda>x [F]xy\<^sub>1y\<^sub>2y\<^sub>3] = [\<lambda>x [G]xy\<^sub>1y\<^sub>2y\<^sub>3] & [\<lambda>x [F]y\<^sub>1xy\<^sub>2y\<^sub>3] = [\<lambda>x [G]y\<^sub>1xy\<^sub>2y\<^sub>3] & [\<lambda>x [F]y\<^sub>1y\<^sub>2xy\<^sub>3] = [\<lambda>x [G]y\<^sub>1y\<^sub>2xy\<^sub>3] & [\<lambda>x [F]y\<^sub>1y\<^sub>2y\<^sub>3x] = [\<lambda>x [G]y\<^sub>1y\<^sub>2y\<^sub>3x])\<close>
proof -
  AOT_have \<open>F = G \<equiv> F\<down> & G\<down> & \<forall>y\<^sub>1\<forall>y\<^sub>2\<forall>y\<^sub>3([\<lambda>x [F]xy\<^sub>1y\<^sub>2y\<^sub>3] = [\<lambda>x [G]xy\<^sub>1y\<^sub>2y\<^sub>3] & [\<lambda>x [F]y\<^sub>1xy\<^sub>2y\<^sub>3] = [\<lambda>x [G]y\<^sub>1xy\<^sub>2y\<^sub>3] & [\<lambda>x [F]y\<^sub>1y\<^sub>2xy\<^sub>3] = [\<lambda>x [G]y\<^sub>1y\<^sub>2xy\<^sub>3] & [\<lambda>x [F]y\<^sub>1y\<^sub>2y\<^sub>3x] = [\<lambda>x [G]y\<^sub>1y\<^sub>2y\<^sub>3x])\<close>
    using p_identity_2_c df_rules_formulas_1 df_rules_formulas_2 "\<rightarrow>E" "&E" "\<equiv>I" "\<rightarrow>I" by blast
  moreover AOT_have \<open>F\<down>\<close> and \<open>G\<down>\<close>
    by (auto simp: cqt_2_const_var)
  ultimately show ?thesis
    using df_simplify_1 "&I" by blast
qed

AOT_theorem p_identity_thm2_2_generic:
  \<open>F = G \<equiv> \<forall>x\<^sub>1...\<forall>x\<^sub>n \<guillemotleft>AOT_sem_proj_id x\<^sub>1x\<^sub>n (\<lambda> \<tau> . \<guillemotleft>[F]\<tau>\<guillemotright>) (\<lambda> \<tau> . \<guillemotleft>[G]\<tau>\<guillemotright>)\<guillemotright>\<close>
proof -
  AOT_have \<open>F = G \<equiv> F\<down> & G\<down> & \<forall>x\<^sub>1...\<forall>x\<^sub>n \<guillemotleft>AOT_sem_proj_id x\<^sub>1x\<^sub>n (\<lambda> \<tau> . \<guillemotleft>[F]\<tau>\<guillemotright>) (\<lambda> \<tau> . \<guillemotleft>[G]\<tau>\<guillemotright>)\<guillemotright>\<close>
    using p_identity_2_generic df_rules_formulas_1 df_rules_formulas_2 "\<rightarrow>E" "&E" "\<equiv>I" "\<rightarrow>I" by blast
  moreover AOT_have \<open>F\<down>\<close> and \<open>G\<down>\<close>
    by (auto simp: cqt_2_const_var)
  ultimately show ?thesis
    using df_simplify_1 "&I" by blast
qed

AOT_theorem p_identity_thm2_3:
  \<open>p = q \<equiv> [\<lambda>x p] = [\<lambda>x q]\<close>
proof -
  AOT_have \<open>p = q \<equiv> p\<down> & q\<down> & [\<lambda>x p] = [\<lambda>x q]\<close>
    using p_identity_3 df_rules_formulas_1 df_rules_formulas_2 "\<rightarrow>E" "&E" "\<equiv>I" "\<rightarrow>I" by blast
  moreover AOT_have \<open>p\<down>\<close> and \<open>q\<down>\<close>
    by (auto simp: cqt_2_const_var)
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
      by (simp add: lambda_predicates_3)
    AOT_have \<open>[\<lambda>x\<^sub>1...x\<^sub>n [F]x\<^sub>1...x\<^sub>n]\<down>\<close>
      by (rule cqt_2_lambda)
         (auto intro: AOT_instance_of_cqt_2_intro)
    AOT_hence \<open>[\<lambda>x\<^sub>1...x\<^sub>n [F]x\<^sub>1...x\<^sub>n] = [\<lambda>x\<^sub>1...x\<^sub>n [F]x\<^sub>1...x\<^sub>n]\<close>
      using lambda_predicates_1 "\<rightarrow>E" by blast
    AOT_show \<open>F = F\<close> using "=E" 0 by force 
  }
qed

instance \<o> :: AOT_Term_id_2
proof
  AOT_modally_strict {
    fix p :: "\<o> AOT_var"
    AOT_have 0: \<open>[\<lambda> p] = p\<close>
      by (simp add: lambda_predicates_3_b)
    AOT_have \<open>[\<lambda> p]\<down>\<close>
      by (rule cqt_2_lambda0)
    AOT_hence \<open>[\<lambda> p] = [\<lambda> p]\<close>
      using lambda_predicates_1_b "\<rightarrow>E" by blast
    AOT_show \<open>p = p\<close> using "=E" 0 by force
  }
qed

AOT_add_term_sort AOT_Term_id_2

(* TODO: Interestingly, this doesn't depend on id_eq_1 at all! *)
AOT_theorem id_eq_2: \<open>\<alpha> = \<beta> \<rightarrow> \<beta> = \<alpha>\<close>
(*  by (meson "rule=E" deduction_theorem) *)
proof (rule "\<rightarrow>I")
  AOT_assume \<open>\<alpha> = \<beta>\<close>
  moreover AOT_hence \<open>\<beta> = \<beta>\<close> using "=E"[of v "\<lambda> \<tau> . \<guillemotleft>\<tau> = \<beta>\<guillemotright>" "AOT_term_of_var \<alpha>" "AOT_term_of_var \<beta>"] by blast
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
  moreover AOT_have \<open>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down>\<close> using assms by (rule cqt_2_lambda)
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
  fixes \<phi> :: \<open>'a::AOT_Term_id \<Rightarrow> \<o>\<close> (* TODO: how to avoid this *)
  assumes \<open>\<tau>{\<alpha>\<^sub>1...\<alpha>\<^sub>n} =\<^sub>d\<^sub>f \<sigma>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}\<close> and \<open>\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down>\<close> and \<open>\<phi>{\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n}}\<close>
  shows \<open>\<phi>{\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}}\<close>
proof -
  AOT_have \<open>\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n} = \<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<close> using rule_id_def_1 assms(1,2) by blast
  AOT_thus \<open>\<phi>{\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}}\<close> using assms(3) "=E" by blast
qed

AOT_theorem rule_id_def_2_b:
  fixes \<phi> :: \<open>'a::AOT_Term_id_2 \<Rightarrow> \<o>\<close> (* TODO: how to avoid this *)
  assumes \<open>\<tau>{\<alpha>\<^sub>1...\<alpha>\<^sub>n} =\<^sub>d\<^sub>f \<sigma>{\<alpha>\<^sub>1...\<alpha>\<^sub>n}\<close> and \<open>\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<down>\<close> and \<open>\<phi>{\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}}\<close>
  shows \<open>\<phi>{\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n}}\<close>
proof -
  AOT_have \<open>\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n} = \<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<close> using rule_id_def_1 assms(1,2) by blast
  AOT_hence \<open>\<sigma>{\<tau>\<^sub>1...\<tau>\<^sub>n} = \<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n}\<close>
    using "=E" "=I"(1) "t=t-proper_1" "\<rightarrow>E" by fast
  AOT_thus \<open>\<phi>{\<tau>{\<tau>\<^sub>1...\<tau>\<^sub>n}}\<close> using assms(3) "=E" by blast
qed

end
