theory AOT_MetaDefs
  imports AOT_Individual
begin

definition equivalent_by_definition :: "[\<o>, \<o>] \<Rightarrow> bool" (infixl "\<equiv>\<^sub>d\<^sub>f" 3) where
  [AOT_meta_simp]: "\<phi> \<equiv>\<^sub>d\<^sub>f \<psi> \<equiv> (\<forall> v . [v \<Turnstile> \<phi>] \<longleftrightarrow> [v \<Turnstile> \<psi>])"

lemma equivalent_by_definitionI:
  assumes "\<And> v. [v \<Turnstile> \<phi>] \<Longrightarrow> [v \<Turnstile> \<psi>]" and "\<And> v. [v \<Turnstile> \<psi>] \<Longrightarrow> [v \<Turnstile> \<phi>]"
  shows "\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>"
  using assms equivalent_by_definition_def by blast

lemma equivalent_by_definitionE:
  assumes "\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>"
  shows "[v \<Turnstile> \<phi>] = [v \<Turnstile> \<psi>]"
  using assms equivalent_by_definition_def by auto
lemma equivalent_by_definitionE1:
  assumes "\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>" and "[v \<Turnstile> \<phi>]"
  shows "[v \<Turnstile> \<psi>]"
  using assms equivalent_by_definition_def by auto
lemma equivalent_by_definitionE2:
  assumes "\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>" and "[v \<Turnstile> \<psi>]"
  shows "[v \<Turnstile> \<phi>]"
  using assms equivalent_by_definition_def by auto

definition AOT_Rigid :: "<'a::AOT_Term> \<Rightarrow> \<o>" ("Rigid'(_')") where
  "Rigid(\<Pi>) \<equiv> \<Pi>\<^bold>\<down> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>x. \<lparr>\<Pi>,x\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>\<Pi>,x\<rparr>)"

definition AOT_Rigidifies :: "[<'a::AOT_Term>, <'a>] \<Rightarrow> \<o>" ("Rigidifies'(_,_')") where
  "Rigidifies(\<Pi>, \<Pi>') \<equiv> Rigid(\<Pi>) \<^bold>& (\<^bold>\<forall>x . \<lparr>\<Pi>,x\<rparr> \<^bold>\<equiv> \<lparr>\<Pi>',x\<rparr>)"

definition AOT_equal_def :: "['a::AOT_Term, 'a] \<Rightarrow> bool" (infixl "=\<^sub>d\<^sub>f" 5) where
  "\<tau> =\<^sub>d\<^sub>f \<sigma> \<equiv> \<forall> v . [v \<Turnstile> ((\<sigma>\<^bold>\<down>) \<^bold>\<rightarrow> \<tau> \<^bold>= \<sigma>) \<^bold>& ((\<^bold>\<not>(\<sigma>\<^bold>\<down>)) \<^bold>\<rightarrow> \<^bold>\<not>(\<tau>\<^bold>\<down>))]"

lemma AOT_equal_defI: assumes "\<tau> = \<sigma>" shows "\<tau> =\<^sub>d\<^sub>f \<sigma>"
  unfolding AOT_equal_def_def
  by (simp add: AOT_conjS AOT_denotesS AOT_idS AOT_impS assms)

lemma AOT_equal_defE1: assumes "\<tau> =\<^sub>d\<^sub>f \<sigma>" and "[v \<Turnstile> \<sigma>\<^bold>\<down>]" shows "\<tau> = \<sigma>"
  using assms unfolding AOT_equal_def_def by (simp add: AOT_meta_simp)

lemma AOT_equal_defE2: assumes "\<tau> =\<^sub>d\<^sub>f \<sigma>" and "\<not>[v \<Turnstile> \<sigma>\<^bold>\<down>]" shows "\<not>[v \<Turnstile> \<tau>\<^bold>\<down>]"
  using assms unfolding AOT_equal_def_def by (simp add: AOT_meta_simp)

definition AOT_identity\<^sub>E where "AOT_identity\<^sub>E \<equiv> [\<^bold>\<lambda> (x,y) . \<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>)]"
lemma AOT_identity\<^sub>E_denotes: "[v \<Turnstile> AOT_identity\<^sub>E\<^bold>\<down>]"
  unfolding AOT_identity\<^sub>E_def
  by (rule AOT_lambda_denotes_intros)+

definition AOT_identity\<^sub>E_infix (infixl "\<^bold>=\<^sub>E" 64) where "(\<kappa> \<^bold>=\<^sub>E \<kappa>') \<equiv> \<lparr>AOT_identity\<^sub>E, \<kappa>, \<kappa>'\<rparr>"

lemma identity\<^sub>E_equivE:
  assumes "[v \<Turnstile> \<kappa>\<^sub>1 \<^bold>=\<^sub>E \<kappa>\<^sub>2]"
  shows "\<kappa>\<^sub>1 \<approx> \<kappa>\<^sub>2" and "[v \<Turnstile> \<lparr>O!, \<kappa>\<^sub>1\<rparr>]" and "[v \<Turnstile> \<lparr>O!, \<kappa>\<^sub>2\<rparr>]"
  using assms unfolding AOT_identity\<^sub>E_infix_def AOT_identity\<^sub>E_def
  using AOT_meta_beta[OF AOT_identity\<^sub>E_denotes[unfolded AOT_identity\<^sub>E_def], OF assms[unfolded AOT_identity\<^sub>E_infix_def AOT_identity\<^sub>E_def, THEN AOT_exeE2]]
  apply auto
  apply (simp add: AOT_conjS AOT_boxS AOT_iffS AOT_allS)
    apply (meson AOT_denotesS AOT_exeE2 AOT_meta_equiv_indistinguishable)
  by (auto simp: AOT_conjS)
lemma identity\<^sub>E_equivI:
  assumes "\<kappa>\<^sub>1 \<approx> \<kappa>\<^sub>2" and "[v \<Turnstile> \<lparr>O!, \<kappa>\<^sub>1\<rparr>]" and "[v \<Turnstile> \<lparr>O!, \<kappa>\<^sub>2\<rparr>]"
  shows "[v \<Turnstile> \<kappa>\<^sub>1 \<^bold>=\<^sub>E \<kappa>\<^sub>2]"
  unfolding AOT_identity\<^sub>E_infix_def AOT_identity\<^sub>E_def
  apply (rule AOT_meta_beta[THEN iffD2])
  using AOT_identity\<^sub>E_denotes[unfolded AOT_identity\<^sub>E_def] apply blast
  using assms(1)
   apply (metis (no_types, lifting) AOT_denotesS AOT_equiv_prod_def case_prod_conv AOT_meta_equiv_indistinguishable)
  apply (simp add: AOT_conjS AOT_boxS AOT_iffS AOT_allS)
  using AOT_meta_equiv_indistinguishable[THEN iffD1, OF assms(1)]
  using AOT_exeE1 assms(2) assms(3) by blast

class \<kappa> = AOT_UnaryIndividual

end
