theory AOT_axioms
  imports AOT_semantics
begin

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

AOT_theorem identity: \<open>\<kappa> = \<kappa>' \<equiv>\<^sub>d\<^sub>f ([O!]\<kappa> & [O!]\<kappa>' & \<box>\<forall>F ([F]\<kappa> \<equiv> [F]\<kappa>')) \<or> ([A!]\<kappa> & [A!]\<kappa>' & \<box>\<forall>F (\<kappa>[F] \<equiv> \<kappa>'[F]))\<close>
  unfolding AOT_model_equiv_def
  using AOT_sem_ind_eq[of _ \<kappa> \<kappa>']
  by (simp add: AOT_sem_ordinary AOT_sem_abstract AOT_sem_conj AOT_sem_box AOT_sem_equiv AOT_sem_forall AOT_sem_disj AOT_sem_eq AOT_sem_denotes)

(* TODO: remove, resp. move to later *)
(*
AOT_define AOT_eq_E :: \<open>\<Pi>\<close> ("'(=\<^sub>E')") \<open>(=\<^sub>E) =\<^sub>d\<^sub>f [\<lambda>xy O!x & O!y & \<box>\<forall>F ([F]x \<equiv> [F]y)]\<close>
syntax "_AOT_eq_E_infix" :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl "=\<^sub>E" 50)
translations (\<phi>) "\<kappa> =\<^sub>E \<kappa>'" == (\<phi>) "[(=\<^sub>E)]\<kappa> \<kappa>'" 
lemma identity_old: \<open>\<kappa> = \<kappa>' \<equiv>\<^sub>d\<^sub>f \<kappa> =\<^sub>E \<kappa>' \<or> ([A!]\<kappa> & [A!]\<kappa>' & \<box>\<forall>F (\<kappa>[F] \<equiv> \<kappa>'[F]))\<close>
proof -
  have ax42_2: \<open>AOT_instance_of_cqt_2 \<phi> \<Longrightarrow> [w \<Turnstile> [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down>]\<close> for w \<phi>
    by (simp add: AOT_instance_of_cqt_2_def)
  have 1: \<open>[v \<Turnstile> [\<lambda>xy O!x & O!y & \<box>\<forall>F ([F]x \<equiv> [F]y)]\<down>]\<close> for v
    by (rule ax42_2) (auto intro!: AOT_instance_of_cqt_2_intro)
  hence \<open>[v \<Turnstile> [(=\<^sub>E)] = [\<lambda>xy O!x & O!y & \<box>\<forall>F ([F]x \<equiv> [F]y)]]\<close> for v
    using AOT_eq_E[THEN AOT_sem_id_def0E1] by blast
  hence \<open>[v \<Turnstile> [(=\<^sub>E)]\<down>]\<close> and AOT_eq_E_eq: \<open>\<guillemotleft>(=\<^sub>E)\<guillemotright> = \<guillemotleft>[\<lambda>xy O!x & O!y & \<box>\<forall>F ([F]x \<equiv> [F]y)]\<guillemotright>\<close> for v
    unfolding AOT_sem_eq AOT_sem_denotes by blast+
  {
    fix v
    assume a: \<open>AOT_model_denotes \<kappa> \<and> AOT_model_denotes \<kappa>' \<and> \<kappa> = \<kappa>'\<close>
    hence 0: \<open>[v \<Turnstile> O!\<kappa> & O!\<kappa>' & \<box>\<forall>F ([F]\<kappa> \<equiv> [F]\<kappa>')] \<or> [v \<Turnstile>[A!]\<kappa> & [A!]\<kappa>' & \<box>\<forall>F (\<kappa>[F] \<equiv> \<kappa>'[F])]\<close>
      using AOT_sem_ind_eq[THEN iffD1, of v \<kappa> \<kappa>']
      by (simp add: AOT_sem_conj AOT_sem_box AOT_sem_forall AOT_sem_equiv AOT_sem_denotes)
    have den: \<open>AOT_model_denotes (\<kappa>,\<kappa>')\<close>
      by (simp add: AOT_model_denotes_prod_def a)
    {
      assume 0: \<open>[v \<Turnstile> O!\<kappa> & O!\<kappa>' & \<box>\<forall>F ([F]\<kappa> \<equiv> [F]\<kappa>')]\<close>
      hence \<open>[v \<Turnstile> \<kappa> =\<^sub>E \<kappa>']\<close>
        unfolding AOT_eq_E_eq
        by (rule AOT_sem_lambda_beta[OF 1, unfolded AOT_sem_denotes, OF den, THEN iffD2, simplified])
    }
    hence \<open>[v \<Turnstile> \<kappa> =\<^sub>E \<kappa>'] \<or> ([v \<Turnstile> [A!]\<kappa>] \<and> [v \<Turnstile> [A!]\<kappa>'] \<and> (\<forall> v \<Pi> . AOT_model_denotes \<Pi> \<longrightarrow> [v \<Turnstile> \<kappa>[\<Pi>]] = [v \<Turnstile> \<kappa>'[\<Pi>]]))\<close>
      using "0" AOT_sem_conj a by blast
  }
  moreover {
    fix v
    assume 0: \<open>[v \<Turnstile> \<kappa> =\<^sub>E \<kappa>']\<close>
    hence den: \<open>AOT_model_denotes (\<kappa>,\<kappa>')\<close>
      using AOT_sem_exe AOT_sem_denotes by blast
    have \<open>[v \<Turnstile> O!\<kappa> & O!\<kappa>' & \<box>\<forall>F ([F]\<kappa> \<equiv> [F]\<kappa>')]\<close>
      using 0 unfolding AOT_eq_E_eq
      using AOT_sem_lambda_beta[OF 1, unfolded AOT_sem_denotes, OF den]
      by auto
    hence \<open>AOT_model_denotes \<kappa> \<and> AOT_model_denotes \<kappa>' \<and> \<kappa> = \<kappa>'\<close>
      using AOT_sem_ind_eq[THEN iffD2, of v \<kappa> \<kappa>']
      by (simp add: AOT_sem_conj AOT_sem_box AOT_sem_forall AOT_sem_equiv AOT_sem_denotes)
  }
  moreover {
    fix v
    assume \<open>[v \<Turnstile> [A!]\<kappa>]\<close>
    moreover assume \<open>[v \<Turnstile> [A!]\<kappa>']\<close>
    moreover assume \<open>AOT_model_denotes \<Pi> \<Longrightarrow> [v \<Turnstile> \<kappa>[\<Pi>]] = [v \<Turnstile> \<kappa>'[\<Pi>]]\<close> for v \<Pi>
    ultimately have \<open>AOT_model_denotes \<kappa> \<and> AOT_model_denotes \<kappa>' \<and> \<kappa> = \<kappa>'\<close>
      using AOT_sem_ind_eq[THEN iffD2, of v \<kappa> \<kappa>']
      unfolding AOT_sem_denotes by auto
  }
  ultimately show ?thesis
    by (auto simp: AOT_sem_denotes AOT_model_equiv_def AOT_sem_disj AOT_sem_conj
                   AOT_sem_box AOT_sem_forall AOT_sem_eq AOT_sem_equiv)
qed
*)
AOT_theorem p_identity:
  \<open>\<Pi> = \<Pi>' \<equiv>\<^sub>d\<^sub>f \<Pi>\<down> & \<Pi>'\<down> & \<box>\<forall>x(x[\<Pi>] \<equiv> x[\<Pi>'])\<close>
  using AOT_sem_enc_eq[of _ \<Pi> \<Pi>']
  by (auto simp: AOT_model_equiv_def AOT_sem_imp AOT_sem_denotes AOT_sem_eq AOT_sem_conj
                 AOT_sem_forall AOT_sem_box AOT_sem_equiv)

AOT_theorem p_identity_2_a:
  \<open>\<Pi> = \<Pi>' \<equiv>\<^sub>d\<^sub>f \<Pi>\<down> & \<Pi>'\<down> & \<forall>y\<^sub>1\<forall>y\<^sub>2([\<lambda>z [\<Pi>]zy\<^sub>2] = [\<lambda>z [\<Pi>']zy\<^sub>2] & [\<lambda>z [\<Pi>]y\<^sub>1z] = [\<lambda>z [\<Pi>']y\<^sub>1z])\<close>
  by (auto simp: AOT_model_equiv_def AOT_sem_proj_id_prop[of _ \<Pi> \<Pi>'] AOT_sem_proj_id_prod_def AOT_sem_conj
                 AOT_sem_denotes AOT_sem_forall AOT_sem_unary_proj_id AOT_model_denotes_prod_def)
AOT_theorem p_identity_2_b:
  \<open>\<Pi> = \<Pi>' \<equiv>\<^sub>d\<^sub>f \<Pi>\<down> & \<Pi>'\<down> & \<forall>y\<^sub>1\<forall>y\<^sub>2\<forall>y\<^sub>3([\<lambda>z [\<Pi>]zy\<^sub>2y\<^sub>3] = [\<lambda>z [\<Pi>']zy\<^sub>2y\<^sub>3] & [\<lambda>z [\<Pi>]y\<^sub>1zy\<^sub>3] = [\<lambda>z [\<Pi>']y\<^sub>1zy\<^sub>3] & [\<lambda>z [\<Pi>]y\<^sub>1y\<^sub>2z] = [\<lambda>z [\<Pi>']y\<^sub>1y\<^sub>2z])\<close>
  by (auto simp: AOT_model_equiv_def AOT_sem_proj_id_prop[of _ \<Pi> \<Pi>'] AOT_sem_proj_id_prod_def AOT_sem_conj
                 AOT_sem_denotes AOT_sem_forall AOT_sem_unary_proj_id AOT_model_denotes_prod_def)
AOT_theorem p_identity_2_c:
  \<open>\<Pi> = \<Pi>' \<equiv>\<^sub>d\<^sub>f \<Pi>\<down> & \<Pi>'\<down> & \<forall>y\<^sub>1\<forall>y\<^sub>2\<forall>y\<^sub>3\<forall>y\<^sub>4([\<lambda>z [\<Pi>]zy\<^sub>2y\<^sub>3y\<^sub>4] = [\<lambda>z [\<Pi>']zy\<^sub>2y\<^sub>3y\<^sub>4] & [\<lambda>z [\<Pi>]y\<^sub>1zy\<^sub>3y\<^sub>4] = [\<lambda>z [\<Pi>']y\<^sub>1zy\<^sub>3y\<^sub>4] & [\<lambda>z [\<Pi>]y\<^sub>1y\<^sub>2zy\<^sub>4] = [\<lambda>z [\<Pi>']y\<^sub>1y\<^sub>2zy\<^sub>4] & [\<lambda>z [\<Pi>]y\<^sub>1y\<^sub>2y\<^sub>3z] = [\<lambda>z [\<Pi>']y\<^sub>1y\<^sub>2y\<^sub>3z])\<close>
  by (auto simp: AOT_model_equiv_def AOT_sem_proj_id_prop[of _ \<Pi> \<Pi>'] AOT_sem_proj_id_prod_def AOT_sem_conj
                 AOT_sem_denotes AOT_sem_forall AOT_sem_unary_proj_id AOT_model_denotes_prod_def)

AOT_theorem p_identity_2_generic:
  \<open>\<Pi> = \<Pi>' \<equiv>\<^sub>d\<^sub>f \<Pi>\<down> & \<Pi>'\<down> & \<forall>x\<^sub>1...\<forall>x\<^sub>n \<guillemotleft>AOT_sem_proj_id x\<^sub>1x\<^sub>n (\<lambda> \<tau> . \<guillemotleft>[\<Pi>]\<tau>\<guillemotright>) (\<lambda> \<tau> . \<guillemotleft>[\<Pi>']\<tau>\<guillemotright>)\<guillemotright>\<close> (* TODO: is it ok to state this as axiom? *)
  by (auto simp: AOT_model_equiv_def AOT_sem_proj_id_prop[of _ \<Pi> \<Pi>'] AOT_sem_proj_id_prod_def AOT_sem_conj
                 AOT_sem_denotes AOT_sem_forall AOT_sem_unary_proj_id AOT_model_denotes_prod_def)

AOT_theorem p_identity_3:
  \<open>\<phi> = \<psi> \<equiv>\<^sub>d\<^sub>f \<phi>\<down> & \<psi>\<down> & [\<lambda>x \<phi>] = [\<lambda>x \<psi>]\<close>
  by (auto simp: AOT_model_equiv_def AOT_sem_eq AOT_sem_denotes AOT_sem_conj
                 AOT_model_lambda_denotes AOT_sem_lambda_eq_prop_eq)

AOT_define AOT_nonidentical :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl "\<noteq>" 50)
  noneq_infix: \<open>\<tau> \<noteq> \<sigma> \<equiv>\<^sub>d\<^sub>f \<not>(\<tau> = \<sigma>)\<close>

AOT_theorem pl_1: \<open>\<phi> \<rightarrow> (\<psi> \<rightarrow> \<phi>)\<close>
  by (auto simp: AOT_sem_imp)
AOT_theorem pl_2: \<open>(\<phi> \<rightarrow> (\<psi> \<rightarrow> \<chi>)) \<rightarrow> ((\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<phi> \<rightarrow> \<chi>))\<close>
  by (auto simp: AOT_sem_imp)
AOT_theorem pl_3: \<open>(\<not>\<phi> \<rightarrow> \<not>\<psi>) \<rightarrow> ((\<not>\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>)\<close>
  by (auto simp: AOT_sem_imp AOT_sem_not)

AOT_theorem cqt_1: \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> (\<tau>\<down> \<rightarrow> \<phi>{\<tau>})\<close>
  by (auto simp: AOT_sem_denotes AOT_sem_forall AOT_sem_imp)

AOT_theorem cqt_2_const_var: \<open>\<alpha>\<down>\<close> using AOT_sem_vars_denote .
AOT_theorem cqt_2_lambda:
  assumes \<open>INSTANCE_OF_CQT_2(\<phi>)\<close>
  shows \<open>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down>\<close>
  using assms by (simp add: AOT_sem_denotes AOT_instance_of_cqt_2_def)
AOT_theorem cqt_2_lambda0:
  shows \<open>[\<lambda> \<phi>]\<down>\<close>
  using AOT_model_equiv_def AOT_sem_lambda_denotes existence_3 by fastforce

AOT_theorem cqt_3: \<open>\<forall>\<alpha> (\<phi>{\<alpha>} \<rightarrow> \<psi>{\<alpha>}) \<rightarrow> (\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<forall>\<alpha> \<psi>{\<alpha>})\<close>
  by (simp add: AOT_sem_forall AOT_sem_imp)
AOT_theorem cqt_4: \<open>\<phi> \<rightarrow> \<forall>\<alpha> \<phi>\<close>
  by (simp add: AOT_sem_forall AOT_sem_imp)
AOT_theorem cqt_5a: \<open>[\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>)\<close>
  by (simp add: AOT_sem_conj AOT_sem_denotes AOT_sem_exe AOT_sem_imp)
AOT_theorem cqt_5b: \<open>\<kappa>\<^sub>1...\<kappa>\<^sub>n[\<Pi>] \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>)\<close>
  using AOT_sem_enc_denotes
  by (auto simp: AOT_sem_conj AOT_sem_denotes AOT_sem_imp)

AOT_theorem l_identity: \<open>\<alpha> = \<beta> \<rightarrow> (\<phi>{\<alpha>} \<rightarrow> \<phi>{\<beta>})\<close>
  by (simp add: AOT_sem_eq AOT_sem_imp)

AOT_act_theorem logic_actual: \<open>\<^bold>\<A>\<phi> \<rightarrow> \<phi>\<close>
  by (simp add: AOT_sem_act AOT_sem_imp)

AOT_theorem logic_actual_nec_1: \<open>\<^bold>\<A>\<not>\<phi> \<equiv> \<not>\<^bold>\<A>\<phi>\<close>
  by (simp add: AOT_sem_act AOT_sem_equiv AOT_sem_not)
AOT_theorem logic_actual_nec_2: \<open>\<^bold>\<A>(\<phi> \<rightarrow> \<psi>) \<equiv> (\<^bold>\<A>\<phi> \<rightarrow> \<^bold>\<A>\<psi>)\<close>
  by (simp add: AOT_sem_act AOT_sem_equiv AOT_sem_imp)

AOT_theorem logic_actual_nec_3: \<open>\<^bold>\<A>(\<forall>\<alpha> \<phi>{\<alpha>}) \<equiv> \<forall>\<alpha> \<^bold>\<A>\<phi>{\<alpha>}\<close>
  by (simp add: AOT_sem_act AOT_sem_equiv AOT_sem_forall AOT_sem_denotes)
AOT_theorem logic_actual_nec_4: \<open>\<^bold>\<A>\<phi> \<equiv> \<^bold>\<A>\<^bold>\<A>\<phi>\<close>
  by (simp add: AOT_sem_act AOT_sem_equiv)

AOT_theorem qml_1: \<open>\<box>(\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<box>\<phi> \<rightarrow> \<box>\<psi>)\<close>
  by (simp add: AOT_sem_box AOT_sem_imp)
AOT_theorem qml_2: \<open>\<box>\<phi> \<rightarrow> \<phi>\<close>
  by (simp add: AOT_sem_box AOT_sem_imp)
AOT_theorem qml_3: \<open>\<diamond>\<phi> \<rightarrow> \<box>\<diamond>\<phi>\<close>
  by (simp add: AOT_sem_box AOT_sem_dia AOT_sem_imp)

AOT_theorem qml_4: \<open>\<diamond>\<exists>x (E!x & \<not>\<^bold>\<A>E!x)\<close>
  using AOT_sem_concrete AOT_model_contingent
  by (auto simp: AOT_sem_box AOT_sem_dia AOT_sem_imp AOT_sem_exists AOT_sem_denotes
                 AOT_sem_conj AOT_sem_not AOT_sem_act AOT_sem_exe)

AOT_theorem qml_act_1: \<open>\<^bold>\<A>\<phi> \<rightarrow> \<box>\<^bold>\<A>\<phi>\<close>
  by (simp add: AOT_sem_act AOT_sem_box AOT_sem_imp)
AOT_theorem qml_act_2: \<open>\<box>\<phi> \<equiv> \<^bold>\<A>\<box>\<phi>\<close>
  by (simp add: AOT_sem_act AOT_sem_box AOT_sem_equiv)

AOT_theorem descriptions: \<open>x = \<^bold>\<iota>x(\<phi>{x}) \<equiv> \<forall>z(\<^bold>\<A>\<phi>{z} \<equiv> z = x)\<close>
  by (induct; simp add: AOT_sem_equiv AOT_sem_forall AOT_sem_act AOT_sem_eq)
     (metis (no_types, hide_lams) AOT_sem_desc_denotes AOT_sem_desc_prop AOT_sem_denotes)

AOT_theorem lambda_predicates_1: \<open>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down> \<rightarrow> [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}] = [\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n}]\<close> (* TODO: vacuous *)
  by (simp add: AOT_sem_denotes AOT_sem_eq AOT_sem_imp)
AOT_theorem lambda_predicates_2: \<open>[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]\<down> \<rightarrow> ([\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]x\<^sub>1...x\<^sub>n \<equiv> \<phi>{x\<^sub>1...x\<^sub>n})\<close>
  by induct (simp add: AOT_sem_denotes AOT_sem_equiv AOT_sem_imp AOT_sem_lambda_beta)
AOT_theorem lambda_predicates_3: \<open>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n [F]\<nu>\<^sub>1...\<nu>\<^sub>n] = F\<close>
  by induct (simp add: AOT_sem_denotes AOT_sem_lambda_eta AOT_sem_vars_denote)
AOT_theorem lambda_predicates_3_b: \<open>[\<lambda> p] = p\<close>
  by induct (simp add: AOT_sem_eq AOT_sem_lambda0)
AOT_theorem safe_ext: \<open>([\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down> & \<box>\<forall>\<nu>\<^sub>1...\<forall>\<nu>\<^sub>n (\<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n} \<equiv> \<psi>{\<nu>\<^sub>1...\<nu>\<^sub>n})) \<rightarrow> [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<psi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down>\<close>
  using AOT_sem_lambda_coex 
  by (simp add: AOT_sem_imp AOT_sem_denotes AOT_sem_conj AOT_sem_equiv AOT_sem_box AOT_sem_forall) blast

AOT_theorem nary_encoding_2: \<open>xy[F] \<equiv> x[\<lambda>\<nu> [F]\<nu>y] & y[\<lambda>\<nu> [F]x\<nu>]\<close>
  by (simp add: AOT_sem_conj AOT_sem_equiv AOT_enc_prod_def AOT_proj_enc_prod_def
                AOT_sem_unary_proj_enc AOT_sem_vars_denote)
AOT_theorem nary_encoding_3: \<open>xyz[F] \<equiv> x[\<lambda>\<nu> [F]\<nu>yz] & y[\<lambda>\<nu> [F]x\<nu>z] & z[\<lambda>\<nu> [F]xy\<nu>]\<close>
  by (simp add: AOT_sem_conj AOT_sem_equiv AOT_enc_prod_def AOT_proj_enc_prod_def
                AOT_sem_unary_proj_enc AOT_sem_vars_denote)
AOT_theorem nary_encoding_4: \<open>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F] \<equiv> x\<^sub>1[\<lambda>\<nu> [F]\<nu>x\<^sub>2x\<^sub>3x\<^sub>4] & x\<^sub>2[\<lambda>\<nu> [F]x\<^sub>1\<nu>x\<^sub>3x\<^sub>4] &
                                           x\<^sub>3[\<lambda>\<nu> [F]x\<^sub>1x\<^sub>2\<nu>x\<^sub>4] & x\<^sub>4[\<lambda>\<nu> [F]x\<^sub>1x\<^sub>2x\<^sub>3\<nu>]\<close>
  by (simp add: AOT_sem_conj AOT_sem_equiv AOT_enc_prod_def AOT_proj_enc_prod_def
                AOT_sem_unary_proj_enc AOT_sem_vars_denote)

AOT_theorem encoding: \<open>x[F] \<rightarrow> \<box>x[F]\<close>
  using AOT_sem_enc_nec 
  by (simp add: AOT_sem_imp AOT_sem_box) blast

AOT_theorem nocoder: \<open>O!x \<rightarrow> \<not>\<exists>F x[F]\<close>
  by (simp add: AOT_sem_imp AOT_sem_not AOT_sem_exists AOT_sem_ordinary AOT_sem_dia
                AOT_sem_lambda_beta[OF AOT_sem_ordinary_def_denotes,
                                     OF AOT_sem_vars_denote])
     (metis AOT_sem_nocoder)

AOT_theorem a_objects: \<open>\<exists>x (A!x & \<forall>F(x[F] \<equiv> \<phi>{F}))\<close>
proof -
  AOT_obtain \<kappa> where \<open>\<kappa>\<down> & \<box>\<not>E!\<kappa> & \<forall>F (\<kappa>[F] \<equiv> \<phi>{F})\<close>
    using AOT_sem_a_objects[of _ \<phi>]
    by (auto simp: AOT_sem_imp AOT_sem_box AOT_sem_forall AOT_sem_exists AOT_sem_conj
                   AOT_sem_not AOT_sem_dia AOT_sem_denotes AOT_sem_equiv) blast
  thus ?thesis
    unfolding AOT_sem_exists
    by (rule_tac x=\<kappa> in exI)
       (auto simp: AOT_sem_lambda_beta[OF AOT_sem_abstract_def_denotes]
                   AOT_sem_box AOT_sem_dia AOT_sem_not AOT_sem_denotes AOT_var_of_term_inverse
                   AOT_sem_equiv AOT_sem_forall AOT_sem_conj AOT_sem_abstract)
qed

end
