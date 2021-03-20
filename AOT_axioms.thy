theory AOT_axioms
  imports AOT_semantics
begin

(* To enable meta syntax: *)
interpretation AOT_meta_syntax.
(* To disable meta syntax: *)
(* interpretation AOT_no_meta_syntax. *)

(* To enable AOT syntax (takes precedence over meta syntax; can be done locally using "including" or "include"): *)
(* unbundle AOT_syntax *)
(* To disable AOT syntax (restoring meta syntax or no syntax; can be done locally using "including" or "include"): *)
unbundle AOT_no_syntax

(* conventions - these are already defined, resp. valid, so just note them here again *)
notepad
begin
  fix \<phi> \<psi> \<chi>

  AOT_have conventions_1: \<open>\<phi> & \<psi> \<equiv>\<^sub>d\<^sub>f \<not>(\<phi> \<rightarrow> \<not>\<psi>)\<close>
    using AOT_conj .
  AOT_have conventions_2: \<open>\<phi> \<or> \<psi> \<equiv>\<^sub>d\<^sub>f \<not>\<phi> \<rightarrow> \<psi>\<close>
    using AOT_disj .
  AOT_have conventions_3: \<open>\<phi> \<equiv> \<psi> \<equiv>\<^sub>d\<^sub>f (\<phi> \<rightarrow> \<psi>) & (\<psi> \<rightarrow> \<phi>)\<close>
    using AOT_equiv .
  {
    fix \<phi> :: \<open>'a::AOT_Term \<Rightarrow> \<o>\<close>
    AOT_have conventions_4: \<open>\<exists>\<alpha> \<phi>{\<alpha>} \<equiv>\<^sub>d\<^sub>f \<not>\<forall>\<alpha> \<not>\<phi>{\<alpha>}\<close>
      using AOT_exists .
  }
  AOT_have conventions_5: \<open>\<diamond>\<phi> \<equiv>\<^sub>d\<^sub>f \<not>\<box>\<not>\<phi>\<close>
    using AOT_dia .

  have conventions3_1: \<open>\<guillemotleft>\<phi> \<rightarrow> \<psi> \<equiv> \<not>\<psi> \<rightarrow> \<not>\<phi>\<guillemotright> = \<guillemotleft>(\<phi> \<rightarrow> \<psi>) \<equiv> (\<not>\<psi> \<rightarrow> \<not>\<phi>)\<guillemotright>\<close> by blast
  have conventions3_2: \<open>\<guillemotleft>\<phi> & \<psi> \<rightarrow> \<chi>\<guillemotright> = \<guillemotleft>(\<phi> & \<psi>) \<rightarrow> \<chi>\<guillemotright>\<close>
                   and \<open>\<guillemotleft>\<phi> \<or> \<psi> \<rightarrow> \<chi>\<guillemotright> = \<guillemotleft>(\<phi> \<or> \<psi>) \<rightarrow> \<chi>\<guillemotright>\<close>
    by blast+
  have conventions3_3: \<open>\<guillemotleft>\<phi> \<or> \<psi> & \<chi>\<guillemotright> = \<guillemotleft>(\<phi> \<or> \<psi>) & \<chi>\<guillemotright>\<close>
                   and \<open>\<guillemotleft>\<phi> & \<psi> \<or> \<chi>\<guillemotright> = \<guillemotleft>(\<phi> & \<psi>) \<or> \<chi>\<guillemotright>\<close> (* not exactly, but close enough *)
     by blast+
end

AOT_theorem existence_1: \<open>\<kappa>\<down> \<equiv>\<^sub>d\<^sub>f \<exists>F [F]\<kappa>\<close>
  by (simp add: AOT_sem_denotes AOT_sem_exists AOT_model_equiv_def)
     (metis AOT_sem_denotes AOT_sem_exe AOT_sem_lambda_beta AOT_sem_lambda_denotes)
AOT_theorem existence_2: \<open>\<Pi>\<down> \<equiv>\<^sub>d\<^sub>f \<exists>x\<^sub>1...\<exists>x\<^sub>n x\<^sub>1...x\<^sub>n[\<Pi>]\<close>
  using AOT_sem_denotes AOT_sem_enc_denotes AOT_sem_universal_encoder
  by (simp add: AOT_sem_denotes AOT_sem_exists AOT_model_equiv_def) blast
AOT_theorem existence_2a: \<open>\<Pi>\<down> \<equiv>\<^sub>d\<^sub>f \<exists>x x[\<Pi>]\<close>
  using existence_2[of \<Pi>] by simp
AOT_theorem existence_2b: \<open>\<Pi>\<down> \<equiv>\<^sub>d\<^sub>f \<exists>x\<exists>y xy[\<Pi>]\<close>
  using existence_2[of \<Pi>]
  by (simp add: AOT_sem_denotes AOT_sem_exists AOT_model_equiv_def AOT_model_denotes_prod_def)
AOT_theorem existence_2c: \<open>\<Pi>\<down> \<equiv>\<^sub>d\<^sub>f \<exists>x\<exists>y\<exists>z xyz[\<Pi>]\<close>
  using existence_2[of \<Pi>]
  by (simp add: AOT_sem_denotes AOT_sem_exists AOT_model_equiv_def AOT_model_denotes_prod_def)
AOT_theorem existence_2d: \<open>\<Pi>\<down> \<equiv>\<^sub>d\<^sub>f \<exists>x\<^sub>1\<exists>x\<^sub>2\<exists>x\<^sub>3\<exists>x\<^sub>4 x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[\<Pi>]\<close>
  using existence_2[of \<Pi>]
  by (simp add: AOT_sem_denotes AOT_sem_exists AOT_model_equiv_def AOT_model_denotes_prod_def)

AOT_theorem existence_3: \<open>\<phi>\<down> \<equiv>\<^sub>d\<^sub>f [\<lambda>x \<phi>]\<down>\<close>
  by (simp add: AOT_sem_denotes AOT_model_denotes_\<o>_def AOT_model_equiv_def
                AOT_model_lambda_denotes)

AOT_theorem oa_1: \<open>O! =\<^sub>d\<^sub>f [\<lambda>x \<diamond>E!x]\<close> using AOT_ordinary .
AOT_theorem oa_2: \<open>A! =\<^sub>d\<^sub>f [\<lambda>x \<not>\<diamond>E!x]\<close> using AOT_abstract .

AOT_theorem identity: \<open>x = y \<equiv>\<^sub>d\<^sub>f ([O!]x & [O!]y & \<box>\<forall>F ([F]x \<equiv> [F]y)) \<or> ([A!]x & [A!]y & \<box>\<forall>F (x[F] \<equiv> y[F]))\<close>
  unfolding AOT_model_equiv_def
  using AOT_sem_ind_eq[of _ x y]
  by (simp add: AOT_sem_ordinary AOT_concrete_sem AOT_sem_abstract AOT_sem_conj AOT_sem_box AOT_sem_equiv AOT_sem_forall AOT_sem_disj AOT_sem_eq AOT_sem_denotes)

AOT_theorem p_identity:
  \<open>F = G \<equiv>\<^sub>d\<^sub>f F\<down> & G\<down> & \<box>\<forall>x(x[F] \<equiv> x[G])\<close>
  using AOT_sem_enc_eq[of _ F G]
  by (auto simp: AOT_model_equiv_def AOT_sem_imp AOT_sem_denotes AOT_sem_eq AOT_sem_conj
                 AOT_sem_forall AOT_sem_box AOT_sem_equiv)
AOT_theorem p_identity_2_a:
  \<open>F = G \<equiv>\<^sub>d\<^sub>f F\<down> & G\<down> & \<forall>y([\<lambda>z [F]zy] = [\<lambda>z [G]zy] & [\<lambda>z [F]yz] = [\<lambda>z [G]yz])\<close>
  by (auto simp: AOT_model_equiv_def AOT_sem_proj_id_prop[of _ F G] AOT_sem_proj_id_prod_def AOT_sem_conj
                 AOT_sem_denotes AOT_sem_forall AOT_sem_unary_proj_id AOT_model_denotes_prod_def)
AOT_theorem p_identity_2_b:
  \<open>F = G \<equiv>\<^sub>d\<^sub>f F\<down> & G\<down> & \<forall>y\<^sub>1\<forall>y\<^sub>2([\<lambda>z [F]zy\<^sub>1y\<^sub>2] = [\<lambda>z [G]zy\<^sub>1y\<^sub>2] & [\<lambda>z [F]y\<^sub>1zy\<^sub>2] = [\<lambda>z [G]y\<^sub>1zy\<^sub>2] & [\<lambda>z [F]y\<^sub>1y\<^sub>2z] = [\<lambda>z [G]y\<^sub>1y\<^sub>2z])\<close>
  by (auto simp: AOT_model_equiv_def AOT_sem_proj_id_prop[of _ F G] AOT_sem_proj_id_prod_def AOT_sem_conj
                 AOT_sem_denotes AOT_sem_forall AOT_sem_unary_proj_id AOT_model_denotes_prod_def)

AOT_theorem p_identity_2_c:
  \<open>F = G \<equiv>\<^sub>d\<^sub>f F\<down> & G\<down> & \<forall>y\<^sub>1\<forall>y\<^sub>2\<forall>y\<^sub>3([\<lambda>z [F]zy\<^sub>1y\<^sub>2y\<^sub>3] = [\<lambda>z [G]zy\<^sub>1y\<^sub>2y\<^sub>3] & [\<lambda>z [F]y\<^sub>1zy\<^sub>2y\<^sub>3] = [\<lambda>z [G]y\<^sub>1zy\<^sub>2y\<^sub>3] & [\<lambda>z [F]y\<^sub>1y\<^sub>2zy\<^sub>3] = [\<lambda>z [G]y\<^sub>1y\<^sub>2zy\<^sub>3] & [\<lambda>z [F]y\<^sub>1y\<^sub>2y\<^sub>3z] = [\<lambda>z [G]y\<^sub>1y\<^sub>2y\<^sub>3z])\<close>
  by (auto simp: AOT_model_equiv_def AOT_sem_proj_id_prop[of _ F G] AOT_sem_proj_id_prod_def AOT_sem_conj
                 AOT_sem_denotes AOT_sem_forall AOT_sem_unary_proj_id AOT_model_denotes_prod_def)

AOT_theorem p_identity_2_generic:
  \<open>F = G \<equiv>\<^sub>d\<^sub>f F\<down> & G\<down> & \<forall>x\<^sub>1...\<forall>x\<^sub>n \<guillemotleft>AOT_sem_proj_id x\<^sub>1x\<^sub>n (\<lambda> \<tau> . AOT_exe F \<tau>) (\<lambda> \<tau> . AOT_exe G \<tau>)\<guillemotright>\<close> (* TODO: is it ok to state this as axiom? *)
  by (auto simp: AOT_model_equiv_def AOT_sem_proj_id_prop[of _ F G] AOT_sem_proj_id_prod_def AOT_sem_conj
                 AOT_sem_denotes AOT_sem_forall AOT_sem_unary_proj_id AOT_model_denotes_prod_def)

AOT_theorem p_identity_3:
  \<open>p = q \<equiv>\<^sub>d\<^sub>f p\<down> & q\<down> & [\<lambda>x p] = [\<lambda>x q]\<close>
  by (auto simp: AOT_model_equiv_def AOT_sem_eq AOT_sem_denotes AOT_sem_conj
                 AOT_model_lambda_denotes AOT_sem_lambda_eq_prop_eq)

AOT_define AOT_nonidentical :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl "\<noteq>" 50)
  noneq_infix: \<open>\<tau> \<noteq> \<sigma> \<equiv>\<^sub>d\<^sub>f \<not>(\<tau> = \<sigma>)\<close>

context AOT_meta_syntax
begin
notation AOT_nonidentical (infixl "\<^bold>\<noteq>" 50)
end
context AOT_no_meta_syntax
begin
no_notation AOT_nonidentical (infixl "\<^bold>\<noteq>" 50)
end

AOT_axiom pl_1: \<open>\<phi> \<rightarrow> (\<psi> \<rightarrow> \<phi>)\<close>
  by (auto simp: AOT_sem_imp AOT_model_axiomI)
AOT_axiom pl_2: \<open>(\<phi> \<rightarrow> (\<psi> \<rightarrow> \<chi>)) \<rightarrow> ((\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<phi> \<rightarrow> \<chi>))\<close>
  by (auto simp: AOT_sem_imp AOT_model_axiomI)
AOT_axiom pl_3: \<open>(\<not>\<phi> \<rightarrow> \<not>\<psi>) \<rightarrow> ((\<not>\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>)\<close>
  by (auto simp: AOT_sem_imp AOT_sem_not AOT_model_axiomI)

AOT_axiom cqt_1: \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> (\<tau>\<down> \<rightarrow> \<phi>{\<tau>})\<close>
  by (auto simp: AOT_sem_denotes AOT_sem_forall AOT_sem_imp AOT_model_axiomI)

AOT_axiom cqt_2_const_var: \<open>\<alpha>\<down>\<close> using AOT_sem_vars_denote by (rule AOT_model_axiomI)
AOT_axiom cqt_2_lambda:
  assumes \<open>INSTANCE_OF_CQT_2(\<phi>)\<close>
  shows \<open>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down>\<close>
  using assms by (simp add: AOT_sem_denotes AOT_instance_of_cqt_2_def AOT_model_axiomI)
AOT_axiom cqt_2_lambda0:
  shows \<open>[\<lambda> \<phi>]\<down>\<close>
  apply (rule AOT_model_axiomI)
  using AOT_model_equiv_def AOT_sem_lambda_denotes existence_3 by fastforce
AOT_axiom cqt_2_concrete: \<open>E!\<down>\<close>
  apply (rule AOT_model_axiomI)
  using AOT_sem_concrete_denotes AOT_concrete_sem by auto

AOT_axiom cqt_3: \<open>\<forall>\<alpha> (\<phi>{\<alpha>} \<rightarrow> \<psi>{\<alpha>}) \<rightarrow> (\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<forall>\<alpha> \<psi>{\<alpha>})\<close>
  by (simp add: AOT_sem_forall AOT_sem_imp AOT_model_axiomI)
AOT_axiom cqt_4: \<open>\<phi> \<rightarrow> \<forall>\<alpha> \<phi>\<close>
  by (simp add: AOT_sem_forall AOT_sem_imp AOT_model_axiomI)
AOT_axiom cqt_5a: \<open>[\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>)\<close>
  by (simp add: AOT_sem_conj AOT_sem_denotes AOT_sem_exe AOT_sem_imp AOT_model_axiomI)
AOT_axiom cqt_5a_1: \<open>[\<Pi>]\<kappa> \<rightarrow> (\<Pi>\<down> & \<kappa>\<down>)\<close>
  using cqt_5a AOT_model_axiomI by blast
AOT_axiom cqt_5a_2: \<open>[\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2 \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1\<down> & \<kappa>\<^sub>2\<down>)\<close>
  by (rule AOT_model_axiomI)
     (metis AOT_model_denotes_prod_def AOT_sem_conj AOT_sem_denotes AOT_sem_exe AOT_sem_imp case_prodD)
AOT_axiom cqt_5a_3: \<open>[\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3 \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1\<down> & \<kappa>\<^sub>2\<down> & \<kappa>\<^sub>3\<down>)\<close>
  by (rule AOT_model_axiomI)
     (metis AOT_model_denotes_prod_def AOT_sem_conj AOT_sem_denotes AOT_sem_exe AOT_sem_imp case_prodD)
AOT_axiom cqt_5a_4: \<open>[\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4 \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1\<down> & \<kappa>\<^sub>2\<down> & \<kappa>\<^sub>3\<down> & \<kappa>\<^sub>4\<down>)\<close>
  by (rule AOT_model_axiomI)
     (metis AOT_model_denotes_prod_def AOT_sem_conj AOT_sem_denotes AOT_sem_exe AOT_sem_imp case_prodD)
AOT_axiom cqt_5b: \<open>\<kappa>\<^sub>1...\<kappa>\<^sub>n[\<Pi>] \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>)\<close>
  by (rule AOT_model_axiomI)
     (insert AOT_sem_enc_denotes; auto simp: AOT_sem_conj AOT_sem_denotes AOT_sem_imp)
AOT_axiom cqt_5b_1: \<open>\<kappa>[\<Pi>] \<rightarrow> (\<Pi>\<down> & \<kappa>\<down>)\<close>
  using cqt_5b AOT_model_axiomI by blast
AOT_axiom cqt_5b_2: \<open>\<kappa>\<^sub>1\<kappa>\<^sub>2[\<Pi>] \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1\<down> & \<kappa>\<^sub>2\<down>)\<close>
  by (rule AOT_model_axiomI)
     (metis AOT_model_denotes_prod_def AOT_sem_conj AOT_sem_denotes AOT_sem_enc_denotes AOT_sem_imp case_prodD)
AOT_axiom cqt_5b_3: \<open>\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3[\<Pi>] \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1\<down> & \<kappa>\<^sub>2\<down> & \<kappa>\<^sub>3\<down>)\<close>
  by (rule AOT_model_axiomI)
     (metis AOT_model_denotes_prod_def AOT_sem_conj AOT_sem_denotes AOT_sem_enc_denotes AOT_sem_imp case_prodD)
AOT_axiom cqt_5b_4: \<open>\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4[\<Pi>] \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1\<down> & \<kappa>\<^sub>2\<down> & \<kappa>\<^sub>3\<down> & \<kappa>\<^sub>4\<down>)\<close>
  by (rule AOT_model_axiomI)
     (metis AOT_model_denotes_prod_def AOT_sem_conj AOT_sem_denotes AOT_sem_enc_denotes AOT_sem_imp case_prodD)

AOT_axiom l_identity: \<open>\<alpha> = \<beta> \<rightarrow> (\<phi>{\<alpha>} \<rightarrow> \<phi>{\<beta>})\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_eq AOT_sem_imp)

AOT_act_axiom logic_actual: \<open>\<^bold>\<A>\<phi> \<rightarrow> \<phi>\<close>
  by (rule AOT_model_act_axiomI)
     (simp add: AOT_sem_act AOT_sem_imp)

AOT_axiom logic_actual_nec_1: \<open>\<^bold>\<A>\<not>\<phi> \<equiv> \<not>\<^bold>\<A>\<phi>\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_act AOT_sem_equiv AOT_sem_not)
AOT_axiom logic_actual_nec_2: \<open>\<^bold>\<A>(\<phi> \<rightarrow> \<psi>) \<equiv> (\<^bold>\<A>\<phi> \<rightarrow> \<^bold>\<A>\<psi>)\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_act AOT_sem_equiv AOT_sem_imp)

AOT_axiom logic_actual_nec_3: \<open>\<^bold>\<A>(\<forall>\<alpha> \<phi>{\<alpha>}) \<equiv> \<forall>\<alpha> \<^bold>\<A>\<phi>{\<alpha>}\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_act AOT_sem_equiv AOT_sem_forall AOT_sem_denotes)
AOT_axiom logic_actual_nec_4: \<open>\<^bold>\<A>\<phi> \<equiv> \<^bold>\<A>\<^bold>\<A>\<phi>\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_act AOT_sem_equiv)

AOT_axiom qml_1: \<open>\<box>(\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<box>\<phi> \<rightarrow> \<box>\<psi>)\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_box AOT_sem_imp)
AOT_axiom qml_2: \<open>\<box>\<phi> \<rightarrow> \<phi>\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_box AOT_sem_imp)
AOT_axiom qml_3: \<open>\<diamond>\<phi> \<rightarrow> \<box>\<diamond>\<phi>\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_box AOT_sem_dia AOT_sem_imp)

AOT_axiom qml_4: \<open>\<diamond>\<exists>x (E!x & \<not>\<^bold>\<A>E!x)\<close>
  apply (rule AOT_model_axiomI)
  using AOT_sem_concrete AOT_model_contingent
  by (auto simp: AOT_sem_box AOT_sem_dia AOT_sem_imp AOT_sem_exists AOT_sem_denotes
                 AOT_sem_conj AOT_sem_not AOT_sem_act AOT_sem_exe AOT_concrete_sem)

AOT_axiom qml_act_1: \<open>\<^bold>\<A>\<phi> \<rightarrow> \<box>\<^bold>\<A>\<phi>\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_act AOT_sem_box AOT_sem_imp)
AOT_axiom qml_act_2: \<open>\<box>\<phi> \<equiv> \<^bold>\<A>\<box>\<phi>\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_act AOT_sem_box AOT_sem_equiv)

AOT_axiom descriptions: \<open>x = \<^bold>\<iota>x(\<phi>{x}) \<equiv> \<forall>z(\<^bold>\<A>\<phi>{z} \<equiv> z = x)\<close>
proof (rule AOT_model_axiomI)
  AOT_modally_strict {
    AOT_show \<open>x = \<^bold>\<iota>x(\<phi>{x}) \<equiv> \<forall>z(\<^bold>\<A>\<phi>{z} \<equiv> z = x)\<close>
      by (induct; simp add: AOT_sem_equiv AOT_sem_forall AOT_sem_act AOT_sem_eq)
        (metis (no_types, hide_lams) AOT_sem_desc_denotes AOT_sem_desc_prop AOT_sem_denotes)
  }
qed

AOT_axiom lambda_predicates_1: \<open>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down> \<rightarrow> [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}] = [\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n}]\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_denotes AOT_sem_eq AOT_sem_imp)
AOT_axiom lambda_predicates_1_b: \<open>[\<lambda> p]\<down> \<rightarrow> [\<lambda> p] = [\<lambda> p]\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_denotes AOT_sem_eq AOT_sem_imp)
AOT_axiom lambda_predicates_2: \<open>[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]\<down> \<rightarrow> ([\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]x\<^sub>1...x\<^sub>n \<equiv> \<phi>{x\<^sub>1...x\<^sub>n})\<close>
proof (rule AOT_model_axiomI)
  AOT_modally_strict {
    AOT_show \<open>[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]\<down> \<rightarrow> ([\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]x\<^sub>1...x\<^sub>n \<equiv> \<phi>{x\<^sub>1...x\<^sub>n})\<close>
      by induct (simp add: AOT_sem_denotes AOT_sem_equiv AOT_sem_imp AOT_sem_lambda_beta)
  }
qed
AOT_axiom lambda_predicates_3: \<open>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n [F]\<nu>\<^sub>1...\<nu>\<^sub>n] = F\<close>
proof (rule AOT_model_axiomI)
  AOT_modally_strict {
    AOT_show \<open>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n [F]\<nu>\<^sub>1...\<nu>\<^sub>n] = F\<close>
      by induct (simp add: AOT_sem_denotes AOT_sem_lambda_eta AOT_sem_vars_denote)
  }
qed
AOT_axiom lambda_predicates_3_b: \<open>[\<lambda> p] = p\<close>
proof (rule AOT_model_axiomI)
  AOT_modally_strict {
    AOT_show \<open>[\<lambda> p] = p\<close>
      by induct (simp add: AOT_sem_eq AOT_sem_lambda0)
  }
qed
AOT_axiom safe_ext: \<open>([\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down> & \<box>\<forall>\<nu>\<^sub>1...\<forall>\<nu>\<^sub>n (\<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n} \<equiv> \<psi>{\<nu>\<^sub>1...\<nu>\<^sub>n})) \<rightarrow> [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<psi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down>\<close>
  apply (rule AOT_model_axiomI)
  using AOT_sem_lambda_coex
  by (simp add: AOT_sem_imp AOT_sem_denotes AOT_sem_conj AOT_sem_equiv AOT_sem_box AOT_sem_forall) blast
AOT_axiom safe_ext_2: \<open>([\<lambda>\<nu>\<^sub>1\<nu>\<^sub>2 \<phi>{\<nu>\<^sub>1,\<nu>\<^sub>2}]\<down> & \<box>\<forall>\<nu>\<^sub>1\<forall>\<nu>\<^sub>2 (\<phi>{\<nu>\<^sub>1, \<nu>\<^sub>2} \<equiv> \<psi>{\<nu>\<^sub>1, \<nu>\<^sub>2})) \<rightarrow> [\<lambda>\<nu>\<^sub>1\<nu>\<^sub>2 \<psi>{\<nu>\<^sub>1,\<nu>\<^sub>2}]\<down>\<close>
  using safe_ext[where \<phi>="\<lambda>(x,y). \<phi> x y"]
  by (simp add: AOT_model_axiom_def AOT_sem_imp AOT_model_denotes_prod_def AOT_sem_forall
                AOT_sem_denotes AOT_sem_conj AOT_sem_equiv AOT_sem_box)
AOT_axiom safe_ext_3: \<open>([\<lambda>\<nu>\<^sub>1\<nu>\<^sub>2\<nu>\<^sub>3 \<phi>{\<nu>\<^sub>1,\<nu>\<^sub>2,\<nu>\<^sub>3}]\<down> & \<box>\<forall>\<nu>\<^sub>1\<forall>\<nu>\<^sub>2\<forall>\<nu>\<^sub>3 (\<phi>{\<nu>\<^sub>1, \<nu>\<^sub>2, \<nu>\<^sub>3} \<equiv> \<psi>{\<nu>\<^sub>1, \<nu>\<^sub>2, \<nu>\<^sub>3})) \<rightarrow> [\<lambda>\<nu>\<^sub>1\<nu>\<^sub>2\<nu>\<^sub>3 \<psi>{\<nu>\<^sub>1,\<nu>\<^sub>2,\<nu>\<^sub>3}]\<down>\<close>
  using safe_ext[where \<phi>="\<lambda>(x,y,z). \<phi> x y z"]
  by (simp add: AOT_model_axiom_def AOT_sem_imp AOT_model_denotes_prod_def AOT_sem_forall
                AOT_sem_denotes AOT_sem_conj AOT_sem_equiv AOT_sem_box)
AOT_axiom safe_ext_4: \<open>([\<lambda>\<nu>\<^sub>1\<nu>\<^sub>2\<nu>\<^sub>3\<nu>\<^sub>4 \<phi>{\<nu>\<^sub>1,\<nu>\<^sub>2,\<nu>\<^sub>3,\<nu>\<^sub>4}]\<down> & \<box>\<forall>\<nu>\<^sub>1\<forall>\<nu>\<^sub>2\<forall>\<nu>\<^sub>3\<forall>\<nu>\<^sub>4 (\<phi>{\<nu>\<^sub>1, \<nu>\<^sub>2, \<nu>\<^sub>3, \<nu>\<^sub>4} \<equiv> \<psi>{\<nu>\<^sub>1, \<nu>\<^sub>2, \<nu>\<^sub>3, \<nu>\<^sub>4})) \<rightarrow> [\<lambda>\<nu>\<^sub>1\<nu>\<^sub>2\<nu>\<^sub>3\<nu>\<^sub>4 \<psi>{\<nu>\<^sub>1,\<nu>\<^sub>2,\<nu>\<^sub>3,\<nu>\<^sub>4}]\<down>\<close>
  using safe_ext[where \<phi>="\<lambda>(x,y,z,w). \<phi> x y z w"]
  by (simp add: AOT_model_axiom_def AOT_sem_imp AOT_model_denotes_prod_def AOT_sem_forall
                AOT_sem_denotes AOT_sem_conj AOT_sem_equiv AOT_sem_box)

AOT_axiom nary_encoding_2: \<open>xy[F] \<equiv> x[\<lambda>\<nu> [F]\<nu>y] & y[\<lambda>\<nu> [F]x\<nu>]\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_conj AOT_sem_equiv AOT_enc_prod_def AOT_proj_enc_prod_def
                AOT_sem_unary_proj_enc AOT_sem_vars_denote)
AOT_axiom nary_encoding_3: \<open>xyz[F] \<equiv> x[\<lambda>\<nu> [F]\<nu>yz] & y[\<lambda>\<nu> [F]x\<nu>z] & z[\<lambda>\<nu> [F]xy\<nu>]\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_conj AOT_sem_equiv AOT_enc_prod_def AOT_proj_enc_prod_def
                AOT_sem_unary_proj_enc AOT_sem_vars_denote)
AOT_axiom nary_encoding_4: \<open>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F] \<equiv> x\<^sub>1[\<lambda>\<nu> [F]\<nu>x\<^sub>2x\<^sub>3x\<^sub>4] & x\<^sub>2[\<lambda>\<nu> [F]x\<^sub>1\<nu>x\<^sub>3x\<^sub>4] &
                                           x\<^sub>3[\<lambda>\<nu> [F]x\<^sub>1x\<^sub>2\<nu>x\<^sub>4] & x\<^sub>4[\<lambda>\<nu> [F]x\<^sub>1x\<^sub>2x\<^sub>3\<nu>]\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_conj AOT_sem_equiv AOT_enc_prod_def AOT_proj_enc_prod_def
                AOT_sem_unary_proj_enc AOT_sem_vars_denote)

AOT_axiom encoding: \<open>x[F] \<rightarrow> \<box>x[F]\<close>
  apply (rule AOT_model_axiomI)
  using AOT_sem_enc_nec 
  by (simp add: AOT_sem_imp AOT_sem_box) blast

AOT_axiom nocoder: \<open>O!x \<rightarrow> \<not>\<exists>F x[F]\<close>
  apply (rule AOT_model_axiomI)
  by (simp add: AOT_sem_imp AOT_sem_not AOT_sem_exists AOT_sem_ordinary AOT_sem_dia AOT_concrete_sem
                AOT_sem_lambda_beta[OF AOT_sem_ordinary_def_denotes,
                                     OF AOT_sem_vars_denote])
     (metis AOT_sem_nocoder)

AOT_axiom a_objects: \<open>\<exists>x (A!x & \<forall>F(x[F] \<equiv> \<phi>{F}))\<close>
proof(rule AOT_model_axiomI)
  AOT_modally_strict {
    AOT_obtain \<kappa> where \<open>\<kappa>\<down> & \<box>\<not>E!\<kappa> & \<forall>F (\<kappa>[F] \<equiv> \<phi>{F})\<close>
      using AOT_sem_a_objects[of _ \<phi>]
      by (auto simp: AOT_sem_imp AOT_sem_box AOT_sem_forall AOT_sem_exists AOT_sem_conj
                     AOT_sem_not AOT_sem_dia AOT_sem_denotes AOT_sem_equiv AOT_concrete_sem) blast
    AOT_thus \<open>\<exists>x (A!x & \<forall>F(x[F] \<equiv> \<phi>{F}))\<close>
      unfolding AOT_sem_exists
      by (rule_tac x=\<kappa> in exI)
         (auto simp: AOT_sem_lambda_beta[OF AOT_sem_abstract_def_denotes]
                     AOT_sem_box AOT_sem_dia AOT_sem_not AOT_sem_denotes AOT_var_of_term_inverse
                     AOT_sem_equiv AOT_sem_forall AOT_sem_conj AOT_sem_abstract AOT_concrete_sem)
  }
qed

AOT_theorem universal_closure: assumes \<open>for arbitrary \<alpha>: \<phi>{\<alpha>} \<in> \<Lambda>\<^sub>\<box>\<close> shows \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<in> \<Lambda>\<^sub>\<box>\<close>
  using assms
  by (metis AOT_term_of_var_cases AOT_model_axiom_def AOT_sem_denotes AOT_sem_forall)

AOT_theorem act_closure: assumes \<open>\<phi> \<in> \<Lambda>\<^sub>\<box>\<close> shows \<open>\<^bold>\<A>\<phi> \<in> \<Lambda>\<^sub>\<box>\<close>
  using assms by (simp add: AOT_model_axiom_def AOT_sem_act)

AOT_theorem nec_closure: assumes \<open>\<phi> \<in> \<Lambda>\<^sub>\<box>\<close> shows \<open>\<box>\<phi> \<in> \<Lambda>\<^sub>\<box>\<close>
  using assms by (simp add: AOT_model_axiom_def AOT_sem_box)

AOT_theorem universal_closure_act: assumes \<open>for arbitrary \<alpha>: \<phi>{\<alpha>} \<in> \<Lambda>\<close> shows \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<in> \<Lambda>\<close>
  using assms
  by (metis AOT_term_of_var_cases AOT_model_act_axiom_def AOT_sem_denotes AOT_sem_forall)

AOT_theorem act_closure_act: assumes \<open>\<phi> \<in> \<Lambda>\<close> shows \<open>\<^bold>\<A>\<phi> \<in> \<Lambda>\<close>
  using assms by (simp add: AOT_model_act_axiom_def AOT_sem_act)

AOT_theorem tuple_denotes: \<open>\<guillemotleft>(\<tau>,\<tau>')\<guillemotright>\<down> \<equiv>\<^sub>d\<^sub>f \<tau>\<down> & \<tau>'\<down>\<close>
  by (simp add: AOT_model_denotes_prod_def AOT_model_equiv_def AOT_sem_conj AOT_sem_denotes)

end
