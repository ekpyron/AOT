theory AOT_Truth
  imports Main "~~/src/HOL/Eisbach/Eisbach"
begin

typedecl i
typedecl j
consts dw :: i
consts dj :: j

typedef \<o> = "UNIV::(j\<Rightarrow>i\<Rightarrow>bool) set" ..

setup_lifting type_definition_\<o>

named_theorems AOT_meta_simp
named_theorems AOT_meta_intro_safe
named_theorems AOT_meta_elim_safe
named_theorems AOT_meta_intro
named_theorems AOT_meta_elim

consts AOT_I_NOT :: "(j\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>(j\<Rightarrow>i\<Rightarrow>bool)"
consts AOT_I_BOX :: "(j\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>(j\<Rightarrow>i\<Rightarrow>bool)"
consts AOT_I_ACTUAL :: "(j\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>(j\<Rightarrow>i\<Rightarrow>bool)"
consts AOT_I_IMPL :: "(j\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>(j\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>(j\<Rightarrow>i\<Rightarrow>bool)"

lift_definition AOT_valid_in :: "i\<Rightarrow>\<o>\<Rightarrow>bool" ("[_ \<Turnstile> _]") is
  "\<lambda> w p . p dj w" .

lift_definition AOT_not :: "\<o> \<Rightarrow> \<o>" ("\<^bold>\<not>_" [54] 70) is
  "\<lambda> p s w . (s = dj \<and> \<not>p s w) \<or> (s \<noteq> dj \<and> AOT_I_NOT p s w)" .

lemma AOT_notS[AOT_meta_simp]: "[v \<Turnstile> \<^bold>\<not>p] = (\<not>[v \<Turnstile> p])"
  apply transfer by auto

lift_definition AOT_impl :: "\<o> \<Rightarrow> \<o> \<Rightarrow> \<o>" (infixl "\<^bold>\<rightarrow>" 51) is
  "\<lambda> p q s w . (s = dj \<and> (p s w \<longrightarrow> q s w)) \<or> (s \<noteq> dj \<and> AOT_I_IMPL p q s w)" .

lemma AOT_implS[AOT_meta_simp]: "[v \<Turnstile> p \<^bold>\<rightarrow> q] = ([v \<Turnstile> p] \<longrightarrow> [v \<Turnstile> q])"
  apply transfer by auto

lift_definition AOT_box :: "\<o> \<Rightarrow> \<o>" ("\<^bold>\<box>_" [62] 63) is
  "\<lambda> p s w . (s = dj \<and> (\<forall> v . p s v)) \<or> (s \<noteq> dj \<and> AOT_I_BOX p s w)" .
lemma AOT_boxS[AOT_meta_simp]: "[v \<Turnstile> \<^bold>\<box>p] = (\<forall> v . [v \<Turnstile> p])"
  apply transfer by auto


lift_definition AOT_actual :: "\<o>\<Rightarrow>\<o>" ("\<^bold>\<A>_" [64] 65) is
  "\<lambda> p s w . (s = dj \<and> p s dw) \<or> (s \<noteq> dj \<and> AOT_I_ACTUAL p s w)" .
lemma AOT_actualS[AOT_meta_simp]: "[v \<Turnstile> \<^bold>\<A>p] = [dw \<Turnstile> p]"
  apply transfer by auto

lemma AOT_notI[AOT_meta_intro_safe]:
  assumes "[v \<Turnstile> p] \<Longrightarrow> False"
  shows "[v \<Turnstile> \<^bold>\<not>p]"
  using AOT_notS assms by auto
lemma AOT_notE[AOT_meta_elim]:
  assumes "[v \<Turnstile> \<^bold>\<not>p]" and "[v \<Turnstile> p]"
  shows "[v \<Turnstile> q]"
  using AOT_notS assms by auto

lemma AOT_impI[AOT_meta_intro_safe]:
  assumes "[v \<Turnstile> p] \<Longrightarrow> [v \<Turnstile> q]"
  shows "[v \<Turnstile> p \<^bold>\<rightarrow> q]"
  using AOT_implS assms by auto
lemma AOT_impE[AOT_meta_elim]:
  assumes "[v \<Turnstile> p \<^bold>\<rightarrow> q]"
      and "[v \<Turnstile> q] \<Longrightarrow> [v \<Turnstile> r]"
      and "[v \<Turnstile> p \<^bold>\<rightarrow> q] \<Longrightarrow> [v \<Turnstile> p]"
  shows "[v \<Turnstile> r]"
  using AOT_implS assms by blast
lemma AOT_impCE[AOT_meta_elim_safe]:
  assumes "[v \<Turnstile> p \<^bold>\<rightarrow> q]"
      and "[v \<Turnstile> \<^bold>\<not>p] \<Longrightarrow> [v \<Turnstile> r]"
      and "[v \<Turnstile> q] \<Longrightarrow> [v \<Turnstile> r]"
  shows "[v \<Turnstile> r]"
  using AOT_implS AOT_notS assms by blast

lemma AOT_boxI[AOT_meta_intro_safe]:
  assumes "\<And> v . [v \<Turnstile> p]"
  shows "[v \<Turnstile> \<^bold>\<box>p]"
  using AOT_boxS assms by auto
lemma AOT_boxE[AOT_meta_elim]:
  assumes "[v \<Turnstile> \<^bold>\<box>p]"
      and "[w \<Turnstile> p] \<Longrightarrow> [w \<Turnstile> q]"
  shows "[w \<Turnstile> q]"
  using AOT_boxS assms by auto

lemma AOT_actualI[AOT_meta_intro]:
  assumes "[dw \<Turnstile> p]"
  shows "[v \<Turnstile> \<^bold>\<A>p]"
  using AOT_actualS assms by auto
lemma AOT_actualE[AOT_meta_elim]:
  assumes "[v \<Turnstile> \<^bold>\<A>p]"
      and "[dw \<Turnstile> p] \<Longrightarrow> [dw \<Turnstile> r]"
  shows "[dw \<Turnstile> r]"
  using AOT_actualS assms by auto

definition AOT_conj::"\<o>\<Rightarrow>\<o>\<Rightarrow>\<o>" (infixl "\<^bold>&" 53) where
  "AOT_conj \<equiv> \<lambda> p q . \<^bold>\<not>(p \<^bold>\<rightarrow> \<^bold>\<not>q)"
lemma AOT_conjS[AOT_meta_simp]: "[v \<Turnstile> p \<^bold>& q] = ([v \<Turnstile> p] \<and> [v \<Turnstile> q])"
  unfolding AOT_conj_def by (simp add: AOT_implS AOT_notS)

lemma AOT_conjI[AOT_meta_intro_safe]:
  assumes "[v \<Turnstile> p]"
      and "[v \<Turnstile> q]"
    shows "[v \<Turnstile> p \<^bold>& q]"
  using AOT_conjS assms by blast 
lemma AOT_conjE[AOT_meta_elim_safe]:
  assumes "[v \<Turnstile> p \<^bold>& q]"
      and "[v \<Turnstile> p] \<Longrightarrow> [v \<Turnstile> q] \<Longrightarrow> [v \<Turnstile> r]"
    shows "[v \<Turnstile> r]"
  using AOT_conjS assms by blast 

definition AOT_disj::"\<o> \<Rightarrow> \<o> \<Rightarrow> \<o>" (infixl "\<^bold>\<or>" 52) where
  "AOT_disj \<equiv> \<lambda> p q . \<^bold>\<not>p \<^bold>\<rightarrow> q"
lemma AOT_disjS[AOT_meta_simp]: "[v \<Turnstile> p \<^bold>\<or> q] = ([v \<Turnstile> p] \<or> [v \<Turnstile> q])"
  unfolding AOT_disj_def using AOT_implS AOT_notS by auto

lemma AOT_disjCI[AOT_meta_intro_safe]:
  assumes "[v \<Turnstile> \<^bold>\<not>q] \<Longrightarrow> [v \<Turnstile> p]"
  shows "[v \<Turnstile> p \<^bold>\<or> q]"
  using AOT_disjS AOT_notS assms by blast
lemma AOT_disjI1[AOT_meta_intro]:
  assumes "[v \<Turnstile> p]"
  shows "[v \<Turnstile> p \<^bold>\<or> q]"
  using AOT_disjS assms by blast
lemma AOT_disjI2[AOT_meta_intro]:
  assumes "[v \<Turnstile> q]"
  shows "[v \<Turnstile> p \<^bold>\<or> q]"
  using AOT_disjS assms by blast
lemma AOT_disjE[AOT_meta_elim_safe]:
  assumes "[v \<Turnstile> p \<^bold>\<or> q]"
      and "[v \<Turnstile> p] \<Longrightarrow> [v \<Turnstile> r]"
      and "[v \<Turnstile> q] \<Longrightarrow> [v \<Turnstile> r]"
  shows "[v \<Turnstile> r]"
  using AOT_disjS assms by blast

definition AOT_iff::"\<o> \<Rightarrow> \<o> \<Rightarrow> \<o>" (infixl "\<^bold>\<equiv>" 51) where
  "AOT_iff \<equiv> \<lambda> p q . (p \<^bold>\<rightarrow> q) \<^bold>& (q \<^bold>\<rightarrow> p)"
lemma AOT_iffS[AOT_meta_simp]: "[v \<Turnstile> p \<^bold>\<equiv> q] = ([v \<Turnstile> p] \<longleftrightarrow> [v \<Turnstile> q])"
  unfolding AOT_iff_def using AOT_conjS AOT_implS by auto

lemma AOT_iffI[AOT_meta_intro_safe]:
  assumes "[v \<Turnstile> p] \<Longrightarrow> [v \<Turnstile> q]"
      and "[v \<Turnstile> q] \<Longrightarrow> [v \<Turnstile> p]"
    shows "[v \<Turnstile> p \<^bold>\<equiv> q]"
  using AOT_iffS assms by auto
lemma AOT_iffE[AOT_meta_elim_safe]:
  assumes "[v \<Turnstile> p \<^bold>\<equiv> q]"
      and "[v \<Turnstile> p \<^bold>\<rightarrow> q] \<Longrightarrow> [v \<Turnstile> q \<^bold>\<rightarrow> p] \<Longrightarrow> [v \<Turnstile> r]"
    shows "[v \<Turnstile> r]"
  using AOT_iffS AOT_implS assms by blast 
lemma AOT_iffCE[AOT_meta_elim_safe]:
  assumes "[v \<Turnstile> p \<^bold>\<equiv> q]"
      and "[v \<Turnstile> p] \<Longrightarrow> [v \<Turnstile> q] \<Longrightarrow> [v \<Turnstile> r]"
      and "[v \<Turnstile> \<^bold>\<not>p] \<Longrightarrow> [v \<Turnstile> \<^bold>\<not>q] \<Longrightarrow> [v \<Turnstile> r]"
    shows "[v \<Turnstile> r]"
  using AOT_iffS AOT_notS assms by blast

definition AOT_diamond::"\<o> \<Rightarrow> \<o>" ("\<^bold>\<diamond>_" [62] 63) where
  "AOT_diamond \<equiv> \<lambda> p . \<^bold>\<not>\<^bold>\<box>\<^bold>\<not>p"
lemma AOT_diamondS[AOT_meta_simp]: "[v \<Turnstile> \<^bold>\<diamond>p] = (\<exists> v . [v \<Turnstile> p])"
  unfolding AOT_diamond_def by (simp add: AOT_boxS AOT_notS)

lemma AOT_diamondI[AOT_meta_intro]:
  assumes "[w \<Turnstile> p]"
  shows "[v \<Turnstile> \<^bold>\<diamond>p]"
  using AOT_diamondS assms by auto
lemma AOT_diamondE[AOT_meta_elim]:
  assumes "[v \<Turnstile> \<^bold>\<diamond>p]"
      and "\<And> w . [w \<Turnstile> p] \<Longrightarrow> [v' \<Turnstile> q]"
  shows "[v' \<Turnstile> q]"
  using AOT_diamondS assms by auto

lemma AOT_refl_iff[AOT_meta_intro_safe]:
  shows "[v \<Turnstile> p \<^bold>\<equiv> p]"
  using AOT_iffS by auto

lemma AOT_refl_impl[AOT_meta_intro_safe]:
  shows "[v \<Turnstile> p \<^bold>\<rightarrow> p]"
  using AOT_implS by auto

lift_definition AOT_nec_false :: "\<o>" is "\<lambda> s w . False" .
lift_definition AOT_nec_true :: "\<o>" is "\<lambda> s w . True" .

lemma AOT_nec_trueI[AOT_meta_intro_safe]:
  "[v \<Turnstile> AOT_nec_true]"
  apply transfer by simp
lemma AOT_nec_falseE[AOT_meta_elim_safe]:
  assumes "[v \<Turnstile> AOT_nec_false]" shows "False"
  using assms apply transfer by simp

lemma AOT_nec_falseS[AOT_meta_simp]:
  "[v \<Turnstile> AOT_nec_false] = False"
  using AOT_nec_falseE by auto

lemma AOT_nec_trueS[AOT_meta_simp]:
  "[v \<Turnstile> AOT_nec_true] = True"
  by (simp add: AOT_nec_trueI)

lemma AOT_nec_false_not_true[AOT_meta_simp]:
  "(AOT_nec_false = AOT_nec_true) = False"
  using AOT_nec_falseE AOT_nec_trueI by auto

lemma AOT_nec_true_not_false[AOT_meta_simp]:
  "(AOT_nec_true = AOT_nec_false) = False"
  using AOT_nec_falseE AOT_nec_trueI by auto

method AOT_meta_blast = (blast intro!: AOT_meta_intro_safe elim!: AOT_meta_elim_safe intro: AOT_meta_intro elim: AOT_meta_elim)
method AOT_meta_fast = (fast intro!: AOT_meta_intro_safe elim!: AOT_meta_elim_safe intro: AOT_meta_intro elim: AOT_meta_elim)
method AOT_meta_slow = (slow intro!: AOT_meta_intro_safe elim!: AOT_meta_elim_safe intro: AOT_meta_intro elim: AOT_meta_elim)
method AOT_meta_best = (best intro!: AOT_meta_intro_safe elim!: AOT_meta_elim_safe intro: AOT_meta_intro elim: AOT_meta_elim)
method AOT_meta_deepen = (deepen intro!: AOT_meta_intro_safe elim!: AOT_meta_elim_safe intro: AOT_meta_intro elim: AOT_meta_elim)
method AOT_meta_clarify = (clarify intro!: AOT_meta_intro_safe elim!: AOT_meta_elim_safe intro: AOT_meta_intro elim: AOT_meta_elim)
method AOT_meta_safe = (safe intro!: AOT_meta_intro_safe elim!: AOT_meta_elim_safe intro: AOT_meta_intro elim: AOT_meta_elim)
method AOT_meta_simp = (simp add: AOT_meta_simp)
method AOT_meta_auto = (auto simp: AOT_meta_simp intro!: AOT_meta_intro_safe intro: AOT_meta_intro elim!: AOT_meta_elim_safe elim: AOT_meta_elim)
method AOT_meta_force = (force simp: AOT_meta_simp intro!: AOT_meta_intro_safe intro: AOT_meta_intro elim!: AOT_meta_elim_safe elim: AOT_meta_elim)
method AOT_meta_fastforce = (fastforce simp: AOT_meta_simp intro!: AOT_meta_intro_safe intro: AOT_meta_intro elim!: AOT_meta_elim_safe elim: AOT_meta_elim)
method AOT_meta_slowsimp = (slowsimp simp: AOT_meta_simp intro!: AOT_meta_intro_safe intro: AOT_meta_intro elim!: AOT_meta_elim_safe elim: AOT_meta_elim)
method AOT_meta_bestsimp = (bestsimp simp: AOT_meta_simp intro!: AOT_meta_intro_safe intro: AOT_meta_intro elim!: AOT_meta_elim_safe elim: AOT_meta_elim)

bundle AOT_meta = AOT_meta_intro_safe[intro!] AOT_meta_elim_safe[elim!] AOT_meta_intro[intro] AOT_meta_elim[elim] AOT_meta_simp[simp]

end
