theory AOT_PLM
  imports AOT_Axioms
begin

named_theorems PLM

declare Axioms[PLM]

lemma mp[PLM]: assumes "[v \<Turnstile> \<phi>]" and "[v \<Turnstile> \<phi> \<^bold>\<rightarrow> \<psi>]"
  shows "[v \<Turnstile> \<psi>]" using assms by AOT_meta_auto

lemma GEN[PLM]: assumes "\<And> \<alpha> . [v \<Turnstile> \<phi> \<langle>\<alpha>\<rangle>]" shows "[v \<Turnstile> \<^bold>\<forall> \<alpha>. \<phi> \<alpha>]"
  using assms
  using AOT_allI AOT_exists_necI Rep_var_cases by blast

lemma RN[PLM]: assumes "\<And> v.  [v \<Turnstile> \<phi>]" shows "[v \<Turnstile> \<^bold>\<box>\<phi>]"
  using assms by AOT_meta_auto

lemma RN_weak[PLM]: assumes "\<And> v.  [v \<Turnstile> \<phi>]" shows "[dw \<Turnstile> \<^bold>\<box>\<phi>]"
  using assms RN by simp

lemma equivE1[PLM]: assumes "\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>"
  shows "[v \<Turnstile> \<phi> \<^bold>\<rightarrow> \<psi>]"
  using assms by AOT_meta_auto

lemma equivE2[PLM]: assumes "\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>"
  shows "[v \<Turnstile> \<psi> \<^bold>\<rightarrow> \<phi>]"
  using assms by AOT_meta_auto

lemma equalDefE[PLM]: assumes "\<tau> =\<^sub>d\<^sub>f \<sigma>"
  shows "[v \<Turnstile> (\<sigma>\<^bold>\<down> \<^bold>\<rightarrow> \<tau> \<^bold>= \<sigma>) \<^bold>& (\<^bold>\<not>(\<sigma>\<^bold>\<down>) \<^bold>\<rightarrow> \<^bold>\<not>(\<tau>\<^bold>\<down>))]"
  by (meson AOT_equal_def_def assms)

lemma equalDef1E[PLM]: assumes "(\<lambda> \<alpha> . \<tau> \<alpha>) =\<^sub>d\<^sub>f[1] (\<lambda> \<alpha> . \<sigma> \<alpha>)"
  shows "[v \<Turnstile> ((\<tau>\<^sub>1\<^bold>\<down> \<^bold>& (\<sigma> \<tau>\<^sub>1)\<^bold>\<down>) \<^bold>\<rightarrow> (\<tau> \<tau>\<^sub>1 \<^bold>= \<sigma> \<tau>\<^sub>1)) \<^bold>& ((\<^bold>\<not>(\<tau>\<^sub>1\<^bold>\<down>) \<^bold>\<or> (\<^bold>\<not>((\<sigma> \<tau>\<^sub>1)\<^bold>\<down>))) \<^bold>\<rightarrow> \<^bold>\<not>((\<tau> \<tau>\<^sub>1)\<^bold>\<down>))]"
  by (meson AOT_equal_def_free_def assms)

end
