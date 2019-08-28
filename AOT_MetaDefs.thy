theory AOT_MetaDefs
  imports AOT_Kappa
begin

definition equivalent_by_definition :: "\<o>\<Rightarrow>\<o>\<Rightarrow>bool" (infixl "\<equiv>\<^sub>d\<^sub>f" 3) where
  [AOT_meta_simp]: "\<phi> \<equiv>\<^sub>d\<^sub>f \<psi> \<equiv> (\<forall> v . [v \<Turnstile> \<phi>] \<longleftrightarrow> [v \<Turnstile> \<psi>])"

lemma equivalent_by_definitionI[AOT_meta_intro]:
  assumes "\<And> v. [v \<Turnstile> \<phi>] \<longleftrightarrow> [v \<Turnstile> \<psi>]"
  shows "\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>"
  by (simp add: assms equivalent_by_definition_def)

lemma equivalent_by_definitionE[AOT_meta_elim]:
  assumes "\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>"
  shows "[v \<Turnstile> \<phi>] \<longleftrightarrow> [v \<Turnstile> \<psi>]"
  using assms equivalent_by_definition_def by auto

definition AOT_Rigid :: "<'a::AOT_Term> \<Rightarrow> \<o>" ("Rigid'(_')") where
  "AOT_Rigid \<equiv> \<lambda> \<Pi> . \<Pi>\<^bold>\<down> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>x. \<lparr>\<Pi>,x\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>\<Pi>,x\<rparr>)"

definition AOT_Rigidifies :: "<'a::AOT_Term> \<Rightarrow> <'a> \<Rightarrow> \<o>" ("Rigidifies'(_,_')") where
  "AOT_Rigidifies \<equiv> \<lambda> \<Pi> \<Pi>' . Rigid(\<Pi>) \<^bold>& (\<^bold>\<forall>x . \<lparr>\<Pi>,x\<rparr> \<^bold>\<equiv> \<lparr>\<Pi>',x\<rparr>)"

definition AOT_equal_def :: "'a::AOT_Identity \<Rightarrow> 'a::AOT_Identity \<Rightarrow> bool" (infixl "=\<^sub>d\<^sub>f" 5) where
  "AOT_equal_def \<equiv> \<lambda> \<tau> \<sigma> . \<forall> v . [v \<Turnstile> ((\<sigma>\<^bold>\<down>) \<^bold>\<rightarrow> \<tau> \<^bold>= \<sigma>) \<^bold>& ((\<^bold>\<not>(\<sigma>\<^bold>\<down>)) \<^bold>\<rightarrow> \<^bold>\<not>(\<tau>\<^bold>\<down>))]"

lemma AOT_equal_defI: assumes "\<tau> = \<sigma>" shows "\<tau> =\<^sub>d\<^sub>f \<sigma>"
  unfolding AOT_equal_def_def
  apply AOT_meta_auto
  using AOT_boxE AOT_nec_selfeq assms apply blast
  by (simp add: assms)


definition AOT_equal_def_free :: "('a::AOT_Term \<Rightarrow> 'b::AOT_Identity) \<Rightarrow> ('a::AOT_Term \<Rightarrow> 'b::AOT_Identity) \<Rightarrow> bool" (infixl "=\<^sub>d\<^sub>f[1]" 5) where
  "AOT_equal_def_free \<equiv> \<lambda> (\<tau> :: 'a\<Rightarrow>'b) (\<sigma> :: 'a\<Rightarrow>'b) . \<forall> (v::i) (\<tau>\<^sub>1 :: 'a) . [v \<Turnstile> ((\<tau>\<^sub>1\<^bold>\<down> \<^bold>& (\<sigma> \<tau>\<^sub>1)\<^bold>\<down>) \<^bold>\<rightarrow> (\<tau> \<tau>\<^sub>1 \<^bold>= \<sigma> \<tau>\<^sub>1)) \<^bold>& ((\<^bold>\<not>(\<tau>\<^sub>1\<^bold>\<down>) \<^bold>\<or> (\<^bold>\<not>((\<sigma> \<tau>\<^sub>1)\<^bold>\<down>))) \<^bold>\<rightarrow> \<^bold>\<not>((\<tau> \<tau>\<^sub>1)\<^bold>\<down>))]"

lemma AOT_equal_def_freeI: assumes "\<And> \<alpha> . [v \<Turnstile> \<alpha>\<^bold>\<down>] \<Longrightarrow> \<tau> \<alpha> = \<sigma> \<alpha>" and "\<And> \<alpha> . [v \<Turnstile> (\<tau> \<alpha>)\<^bold>\<down>] \<Longrightarrow> [v \<Turnstile> \<alpha>\<^bold>\<down>]" shows "\<tau> =\<^sub>d\<^sub>f[1] \<sigma>"
  unfolding AOT_equal_def_free_def apply AOT_meta_auto
  using AOT_boxS AOT_logical_existsE AOT_logical_existsI AOT_nec_selfeq assms apply fastforce
  apply (meson AOT_exists_necI AOT_notE assms)
  by (metis (full_types) AOT_exists_necI assms)

end
