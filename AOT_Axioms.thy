theory AOT_Axioms
  imports AOT_Kappa
begin

section{* Meta-Definitions *}

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

section{* Definitions *}

lemma conj_def: "\<phi> \<^bold>& \<psi> \<equiv>\<^sub>d\<^sub>f \<^bold>\<not>(\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi>)"
  by AOT_meta_auto
lemma disj_def: "\<phi> \<^bold>\<or> \<psi> \<equiv>\<^sub>d\<^sub>f \<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<psi>"
  by AOT_meta_auto
lemma iff_def: "\<phi> \<^bold>\<equiv> \<psi> \<equiv>\<^sub>d\<^sub>f ((\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>& (\<psi> \<^bold>\<rightarrow> \<phi>))"
  by AOT_meta_auto
lemma ex_def: "(\<^bold>\<exists> \<alpha> . \<phi> \<alpha>) \<equiv>\<^sub>d\<^sub>f (\<^bold>\<not>(\<^bold>\<forall> \<alpha> . \<^bold>\<not>\<phi> \<alpha>))"
  by AOT_meta_auto
lemma dia_def: "\<^bold>\<diamond>\<phi> \<equiv>\<^sub>d\<^sub>f \<^bold>\<not>(\<^bold>\<box>\<^bold>\<not>\<phi>)"
  by AOT_meta_auto

lemma exists_individual_def: "\<kappa>\<^bold>\<down> \<equiv>\<^sub>d\<^sub>f (\<^bold>\<exists> \<Omega> . \<lparr>\<Omega>, \<kappa>\<rparr>)"
  by (metis AOT_ex_def AOT_logical_exists_def ex_def)
lemma exists_relation_def: "\<Pi>\<^bold>\<down>  \<equiv>\<^sub>d\<^sub>f \<^bold>\<exists> \<nu> . \<lbrace>\<nu>,\<Pi>\<rbrace>"
  by (meson AOT_enc_impl_exists AOT_exS AOT_universal_encoder equivalent_by_definition_def)
lemma exists_relation2_def: "\<Pi>\<^bold>\<down> \<equiv>\<^sub>d\<^sub>f \<^bold>\<exists> \<nu>\<^sub>1 \<nu>\<^sub>2 . \<lbrace>\<nu>\<^sub>1,\<nu>\<^sub>2,\<Pi>\<rbrace>"
  apply (rule equivalent_by_definitionI)
  apply rule
  using AOT_universal_encoder[where 'a="'a\<times>'a"] unfolding AOT_universal_encoder_prod_def
   apply - apply (rule_tac x="AOT_universal_encoder" in AOT_exI, simp add: AOT_universal_encoder_exists)+
  apply (metis AOT_universal_encoder AOT_universal_encoder_prod_def)
  by (meson AOT_enc_impl_exists AOT_exS)
lemma exists_relation3_def: "\<Pi>\<^bold>\<down> \<equiv>\<^sub>d\<^sub>f \<^bold>\<exists> \<nu>\<^sub>1 \<nu>\<^sub>2 \<nu>\<^sub>3 . \<lbrace>\<nu>\<^sub>1,\<nu>\<^sub>2,\<nu>\<^sub>3,\<Pi>\<rbrace>"
  apply (rule equivalent_by_definitionI)
  apply rule
  using AOT_universal_encoder[where 'a="'a\<times>'a\<times>'a"] unfolding AOT_universal_encoder_prod_def
   apply - apply (rule_tac x="AOT_universal_encoder" in AOT_exI, simp add: AOT_universal_encoder_exists)+
  apply (metis AOT_universal_encoder AOT_universal_encoder_prod_def)
  by (meson AOT_enc_impl_exists AOT_exS)
lemma exists_relation4_def: "\<Pi>\<^bold>\<down> \<equiv>\<^sub>d\<^sub>f \<^bold>\<exists> \<nu>\<^sub>1 \<nu>\<^sub>2 \<nu>\<^sub>3 \<nu>\<^sub>4 . \<lbrace>\<nu>\<^sub>1,\<nu>\<^sub>2,\<nu>\<^sub>3,\<nu>\<^sub>4,\<Pi>\<rbrace>"
  apply (rule equivalent_by_definitionI)
  apply rule
  using AOT_universal_encoder[where 'a="'a\<times>'a\<times>'a\<times>'a"] unfolding AOT_universal_encoder_prod_def
   apply - apply (rule_tac x="AOT_universal_encoder" in AOT_exI, simp add: AOT_universal_encoder_exists)+
   apply (metis AOT_universal_encoder AOT_universal_encoder_prod_def)
  by (meson AOT_enc_impl_exists AOT_exS)
lemma exists_relation5_def: "\<Pi>\<^bold>\<down> \<equiv>\<^sub>d\<^sub>f \<^bold>\<exists> \<nu>\<^sub>1 \<nu>\<^sub>2 \<nu>\<^sub>3 \<nu>\<^sub>4 \<nu>\<^sub>5  . \<lbrace>\<nu>\<^sub>1,\<nu>\<^sub>2,\<nu>\<^sub>3,\<nu>\<^sub>4,\<nu>\<^sub>5,\<Pi>\<rbrace>"
  apply (rule equivalent_by_definitionI)
  apply rule
  using AOT_universal_encoder[where 'a="'a\<times>'a\<times>'a\<times>'a\<times>'a"] unfolding AOT_universal_encoder_prod_def
   apply - apply (rule_tac x="AOT_universal_encoder" in AOT_exI, simp add: AOT_universal_encoder_exists)+
   apply (metis AOT_universal_encoder AOT_universal_encoder_prod_def)
  by (meson AOT_enc_impl_exists AOT_exS)

lemma exists_relation0_def: "(\<Pi>::unit relation)\<^bold>\<down> \<equiv>\<^sub>d\<^sub>f [\<^bold>\<lambda> y . \<lparr>\<Pi>\<rparr>]\<^bold>\<down>"
  apply (rule equivalent_by_definitionI)
  apply rule
   apply (rule AOT_lambda_existsI) apply simp
  by (simp add: AOT_exists_relI AOT_logical_existsI AOT_meta_equiv_unit_def)

lemma Ordinary_def: "O! = [\<^bold>\<lambda>x. \<^bold>\<diamond>\<lparr>E!,x\<rparr>]"
  by (simp add: AOT_Ordinary_def)
lemma Abstract_def: "A! = [\<^bold>\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<rparr>]"
  by (simp add: AOT_Abstract_def)

lemma identity\<^sub>E_def: "AOT_identity\<^sub>E = [\<^bold>\<lambda> (x,y) . \<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>)]"
  unfolding AOT_identity\<^sub>E_def by simp

lemma identity\<^sub>E_infix_def: "(\<kappa> \<^bold>=\<^sub>E \<kappa>') = \<lparr>[\<^bold>\<lambda> (x,y) . \<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>)], \<kappa>, \<kappa>'\<rparr>"
  unfolding AOT_identity\<^sub>E_infix_def AOT_identity\<^sub>E_def by simp

lemma identity\<kappa>_def: "(\<kappa>::'a::\<kappa>) \<^bold>= \<kappa>' \<equiv>\<^sub>d\<^sub>f (\<kappa> \<^bold>=\<^sub>E \<kappa>') \<^bold>\<or> (\<lparr>A!,\<kappa>\<rparr> \<^bold>& \<lparr>A!,\<kappa>'\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>\<Omega> . \<lbrace>\<kappa>,\<Omega>\<rbrace> \<^bold>\<equiv> \<lbrace>\<kappa>',\<Omega>\<rbrace>))"
  by (simp add: AOT_individual_identity equivalent_by_definition_def)
lemma identity\<Pi>1_def: "\<Pi> \<^bold>= \<Pi>' \<equiv>\<^sub>d\<^sub>f \<Pi>\<^bold>\<down> \<^bold>& \<Pi>'\<^bold>\<down> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>\<nu> :: 'a :: \<kappa>. \<lbrace>\<nu>,\<Pi>\<rbrace> \<^bold>\<equiv> \<lbrace>\<nu>,\<Pi>'\<rbrace>)"
  by (simp add: AOT_identity_relation_def AOT_unary_relation_identity equivalent_by_definition_def)

lemma identity\<Pi>2_def: "\<Pi> \<^bold>= \<Pi>' \<equiv>\<^sub>d\<^sub>f \<Pi>\<^bold>\<down> \<^bold>& \<Pi>'\<^bold>\<down> \<^bold>& (\<^bold>\<forall>\<nu> . [\<^bold>\<lambda>\<mu> . \<lparr>\<Pi>,\<mu>,\<nu>\<rparr>] \<^bold>= [\<^bold>\<lambda>\<mu> . \<lparr>\<Pi>',\<mu>,\<nu>\<rparr>]
                                                                  \<^bold>& [\<^bold>\<lambda>\<mu> . \<lparr>\<Pi>,\<nu>,\<mu>\<rparr>] \<^bold>= [\<^bold>\<lambda>\<mu> . \<lparr>\<Pi>',\<nu>,\<mu>\<rparr>])"
  unfolding AOT_identity_relation_def AOT_relation_identity_prod_def apply (AOT_meta_simp)
  by blast

lemma identity\<Pi>3_def: "\<Pi> \<^bold>= \<Pi>' \<equiv>\<^sub>d\<^sub>f \<Pi>\<^bold>\<down> \<^bold>& \<Pi>'\<^bold>\<down> \<^bold>& (\<^bold>\<forall>\<nu>\<^sub>1 \<nu>\<^sub>2 . [\<^bold>\<lambda>\<mu> . \<lparr>\<Pi>,\<mu>,\<nu>\<^sub>1,\<nu>\<^sub>2\<rparr>] \<^bold>= [\<^bold>\<lambda>\<mu> . \<lparr>\<Pi>',\<mu>,\<nu>\<^sub>1,\<nu>\<^sub>2\<rparr>]
                                                      \<^bold>& [\<^bold>\<lambda>\<mu> . \<lparr>\<Pi>,\<nu>\<^sub>1,\<mu>,\<nu>\<^sub>2\<rparr>] \<^bold>= [\<^bold>\<lambda>\<mu> . \<lparr>\<Pi>',\<nu>\<^sub>1,\<mu>,\<nu>\<^sub>2\<rparr>]
                                                      \<^bold>& [\<^bold>\<lambda>\<mu> . \<lparr>\<Pi>,\<nu>\<^sub>1,\<nu>\<^sub>2,\<mu>\<rparr>] \<^bold>= [\<^bold>\<lambda>\<mu> . \<lparr>\<Pi>',\<nu>\<^sub>1,\<nu>\<^sub>2,\<mu>\<rparr>])"
  unfolding AOT_identity_relation_def AOT_relation_identity_prod_def apply (AOT_meta_auto)
           apply (simp add: AOT_exists_prodI)
  oops

lemma identity\<Pi>0_def: "\<Pi> \<^bold>= \<Pi>' \<equiv>\<^sub>d\<^sub>f \<Pi>\<^bold>\<down> \<^bold>& \<Pi>'\<^bold>\<down> \<^bold>& [\<^bold>\<lambda>x . \<lparr>\<Pi>\<rparr>] \<^bold>= [\<^bold>\<lambda>x . \<lparr>\<Pi>'\<rparr>]"
  by (simp add: AOT_identity\<^sub>0 equivalent_by_definition_def)

section{* Axioms *}

lemma ax44_1: "[v \<Turnstile> \<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<phi>)]" by AOT_meta_auto
lemma ax44_2: "[v \<Turnstile> (\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<chi>)) \<^bold>\<rightarrow> ((\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<chi>))]" by AOT_meta_auto
lemma ax44_3: "[v \<Turnstile> (\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi>) \<^bold>\<rightarrow> ((\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> \<phi>)]" by AOT_meta_auto

lemma ax45_1: "[v \<Turnstile> (\<^bold>\<forall> \<alpha> . \<phi> \<alpha>) \<^bold>\<rightarrow> (\<tau>\<^bold>\<down> \<^bold>\<rightarrow> \<phi> \<tau>)]" by AOT_meta_auto
lemma ax45_2: "[v \<Turnstile> \<langle>\<tau>\<rangle>\<^bold>\<down>]" by AOT_meta_auto
lemma ax45_2: "[v \<Turnstile> \<tau>\<^bold>\<down>]" oops (* TODO: verify that this works for all description-free lambda expressions without encoding subformulas *)
lemma ax45_3: "[v \<Turnstile> (\<^bold>\<forall> \<alpha> . \<phi> \<alpha> \<^bold>\<rightarrow> \<psi> \<alpha>) \<^bold>\<rightarrow> ((\<^bold>\<forall> \<alpha> . \<phi> \<alpha>) \<^bold>\<rightarrow> (\<^bold>\<forall> \<alpha> . \<psi> \<alpha>))]" by AOT_meta_auto
lemma ax45_4: "[v \<Turnstile> \<phi> \<^bold>\<rightarrow> (\<^bold>\<forall> \<alpha> . \<phi>)]" by AOT_meta_auto
lemma ax45_5_1: "[v \<Turnstile> (\<lparr>\<Pi>, \<kappa>\<rparr> \<^bold>\<or> \<lbrace>\<kappa>, \<Pi>\<rbrace>) \<^bold>\<rightarrow> (\<Pi>\<^bold>\<down> \<^bold>& \<kappa>\<^bold>\<down>)]"
  by (simp add: AOT_conjI AOT_disjS AOT_enc_impl_exists AOT_exeS AOT_implS)
lemma ax45_5_2: "[v \<Turnstile> (\<lparr>\<Pi>, \<kappa>\<^sub>1, \<kappa>\<^sub>2\<rparr> \<^bold>\<or> \<lbrace>\<kappa>\<^sub>1, \<kappa>\<^sub>2, \<Pi>\<rbrace>) \<^bold>\<rightarrow> (\<Pi>\<^bold>\<down> \<^bold>& \<kappa>\<^sub>1\<^bold>\<down> \<^bold>& \<kappa>\<^sub>2\<^bold>\<down>)]"
  by (metis AOT_conjS AOT_disjS AOT_enc_impl_exists AOT_exeS AOT_exists_prodE1 AOT_exists_prodE2 AOT_impI)
lemma ax45_5_3: "[v \<Turnstile> (\<lparr>\<Pi>, \<kappa>\<^sub>1, \<kappa>\<^sub>2, \<kappa>\<^sub>3\<rparr> \<^bold>\<or> \<lbrace>\<kappa>\<^sub>1, \<kappa>\<^sub>2, \<kappa>\<^sub>3, \<Pi>\<rbrace>) \<^bold>\<rightarrow> (\<Pi>\<^bold>\<down> \<^bold>& \<kappa>\<^sub>1\<^bold>\<down> \<^bold>& \<kappa>\<^sub>2\<^bold>\<down> \<^bold>& \<kappa>\<^sub>3\<^bold>\<down>)]"
  by (metis AOT_conjS AOT_disjS AOT_enc_impl_exists AOT_exeS AOT_exists_prodE1 AOT_exists_prodE2 AOT_impI)
lemma ax45_5_4: "[v \<Turnstile> (\<lparr>\<Pi>, \<kappa>\<^sub>1, \<kappa>\<^sub>2, \<kappa>\<^sub>3, \<kappa>\<^sub>4\<rparr> \<^bold>\<or> \<lbrace>\<kappa>\<^sub>1, \<kappa>\<^sub>2, \<kappa>\<^sub>3, \<kappa>\<^sub>4, \<Pi>\<rbrace>) \<^bold>\<rightarrow> (\<Pi>\<^bold>\<down> \<^bold>& \<kappa>\<^sub>1\<^bold>\<down> \<^bold>& \<kappa>\<^sub>2\<^bold>\<down> \<^bold>& \<kappa>\<^sub>3\<^bold>\<down> \<^bold>& \<kappa>\<^sub>4\<^bold>\<down>)]"
  by (metis AOT_conjS AOT_disjS AOT_enc_impl_exists AOT_exeS AOT_exists_prodE1 AOT_exists_prodE2 AOT_impI)

lemma ax46: "[v \<Turnstile> \<langle>\<alpha>\<rangle> \<^bold>= \<langle>\<beta>\<rangle> \<^bold>\<rightarrow> (\<phi> \<langle>\<alpha>\<rangle> \<^bold>\<rightarrow> \<phi> \<langle>\<beta>\<rangle>)]"
  using AOT_impI AOT_l_identity by metis
(* not really an axiom, but a theorem - here to make sure the stronger theorem stays true in the models *)
lemma ax46_terms: "[v \<Turnstile> \<alpha> \<^bold>= \<beta> \<^bold>\<rightarrow> (\<phi> \<alpha> \<^bold>\<rightarrow> \<phi> \<beta>)]"
  using AOT_impI AOT_l_identity by metis

lemma ax48: "[dw \<Turnstile> \<^bold>\<A>\<phi> \<^bold>\<equiv> \<phi>]" by AOT_meta_auto

lemma ax49_1: "[v \<Turnstile> \<^bold>\<A>\<^bold>\<not>\<phi> \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<A>\<phi>]" by AOT_meta_auto
lemma ax49_2: "[v \<Turnstile> \<^bold>\<A>(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<equiv> (\<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<^bold>\<A>\<psi>)]" by AOT_meta_auto
lemma ax49_3: "[v \<Turnstile> \<^bold>\<A>(\<^bold>\<forall> \<alpha> . \<phi> \<alpha>) \<^bold>\<equiv> (\<^bold>\<forall> \<alpha> . \<^bold>\<A>\<phi> \<alpha>)]" by AOT_meta_auto
lemma ax49_4: "[v \<Turnstile> \<^bold>\<A>\<phi> \<^bold>\<equiv> \<^bold>\<A>\<^bold>\<A>\<phi>]" by AOT_meta_auto

lemma ax50_1: "[v \<Turnstile> \<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>)]" by AOT_meta_auto
lemma ax50_2: "[v \<Turnstile> \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>]" by AOT_meta_auto
lemma ax50_3: "[v \<Turnstile> \<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>]" by AOT_meta_auto
lemma ax50_4: "[v \<Turnstile> \<^bold>\<diamond>(\<^bold>\<exists>x . \<lparr>E!,x\<rparr> \<^bold>& \<^bold>\<not>\<^bold>\<A>\<lparr>E!,x\<rparr>)]"
  using AOT_contingent .

lemma ax51_1: "[v \<Turnstile> \<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<A>\<phi>]" by AOT_meta_auto
lemma ax51_2: "[v \<Turnstile> \<^bold>\<box>\<phi> \<^bold>\<equiv> \<^bold>\<A>(\<^bold>\<box>\<phi>)]" by AOT_meta_auto

lemma ax52: "[v \<Turnstile> (\<langle>x\<rangle> \<^bold>= (\<^bold>\<iota>x. \<phi> x)) \<^bold>\<equiv> (\<^bold>\<forall> z . (\<^bold>\<A>\<phi> z \<^bold>\<equiv> z \<^bold>= \<langle>x\<rangle>))]"
  using AOT_descriptions by AOT_meta_auto

(* axiom 53.1 is implicitly true, since alphabetic variant are meta-logically identical in Isabelle/HOL already *)

lemma ax53_2: "[v \<Turnstile> [\<^bold>\<lambda>x . \<phi> x]\<^bold>\<down> \<^bold>\<rightarrow> (\<lparr>[\<^bold>\<lambda>x . \<phi> x],\<langle>x\<rangle>\<rparr> \<^bold>\<equiv> \<phi> \<langle>x\<rangle>)]"
  by AOT_meta_auto
lemma ax53_3: "[v \<Turnstile> [\<^bold>\<lambda>x . \<lparr>\<langle>F\<rangle>,x\<rparr>] \<^bold>= \<langle>F\<rangle>]" using AOT_eta[of v "\<langle>F\<rangle>", OF ax45_2]
  by (metis AOT_identity_relation_def AOT_relation_identity ax45_2)

lemma ax54_1: "[v \<Turnstile> ([\<^bold>\<lambda>y . \<phi> y]\<^bold>\<down> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> y . \<phi> y \<^bold>\<equiv> \<psi> y)) \<^bold>\<rightarrow> [\<^bold>\<lambda>y . \<psi> y]\<^bold>\<down>]"
  apply AOT_meta_simp using AOT_lambda_equiv_exists by blast

abbreviation AOT_lambda0 ("[\<^bold>\<lambda> _]") where "[\<^bold>\<lambda> \<phi>] \<equiv> [\<^bold>\<lambda>(). \<phi>]"

lemma ax54_2: "[v \<Turnstile> [\<^bold>\<lambda> \<lparr>\<phi>\<rparr>]\<^bold>\<down> \<^bold>\<equiv> \<phi>\<^bold>\<down>]"
  by (simp add: AOT_enc_impl_exists AOT_enc_unit_def AOT_iffS AOT_nec_trueI)

lemma ax54_3_stronger: "[v \<Turnstile> [\<^bold>\<lambda> \<^bold>\<forall>x . \<phi> x]\<^bold>\<down>]" (* TODO: sort out type correctness for \<o>; note: this is stronger than the actual axiom *)
  by (simp add: AOT_lambda_existsI)
lemma ax54_3: "[v \<Turnstile> [\<^bold>\<lambda> \<phi> x]\<^bold>\<down> \<^bold>\<rightarrow> [\<^bold>\<lambda> \<^bold>\<forall>x . \<phi> x]\<^bold>\<down>]"
  using AOT_implS ax54_3_stronger by blast
(* Missing: Rigidification! *)
lemma ax57_2: "[v \<Turnstile> \<lbrace>\<langle>x\<^sub>1\<rangle>::'a::\<kappa>,\<langle>x\<^sub>2\<rangle>::'a,\<langle>F\<rangle>\<rbrace> \<^bold>\<equiv> \<lbrace>\<langle>x\<^sub>1\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,y,\<langle>x\<^sub>2\<rangle>\<rparr>]\<rbrace>
                                              \<^bold>& \<lbrace>\<langle>x\<^sub>2\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,\<langle>x\<^sub>1\<rangle>,y\<rparr>]\<rbrace>]"
  by AOT_meta_auto
lemma ax57_3: "[v \<Turnstile> \<lbrace>\<langle>x\<^sub>1\<rangle>::'a::\<kappa>,\<langle>x\<^sub>2\<rangle>::'a,\<langle>x\<^sub>3\<rangle>::'a,\<langle>F\<rangle>\<rbrace> \<^bold>\<equiv> \<lbrace>\<langle>x\<^sub>1\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,y,\<langle>x\<^sub>2\<rangle>,\<langle>x\<^sub>3\<rangle>\<rparr>]\<rbrace>
                                                      \<^bold>& \<lbrace>\<langle>x\<^sub>2\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,\<langle>x\<^sub>1\<rangle>,y,\<langle>x\<^sub>3\<rangle>\<rparr>]\<rbrace>
                                                      \<^bold>& \<lbrace>\<langle>x\<^sub>3\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,\<langle>x\<^sub>1\<rangle>,\<langle>x\<^sub>2\<rangle>,y\<rparr>]\<rbrace>]"
  by AOT_meta_auto
lemma ax57_4: "[v \<Turnstile> \<lbrace>\<langle>x\<^sub>1\<rangle>::'a::\<kappa>,\<langle>x\<^sub>2\<rangle>::'a,\<langle>x\<^sub>3\<rangle>::'a,\<langle>x\<^sub>4\<rangle>::'a,\<langle>F\<rangle>\<rbrace> \<^bold>\<equiv> \<lbrace>\<langle>x\<^sub>1\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,y,\<langle>x\<^sub>2\<rangle>,\<langle>x\<^sub>3\<rangle>,\<langle>x\<^sub>4\<rangle>\<rparr>]\<rbrace>
                                                              \<^bold>& \<lbrace>\<langle>x\<^sub>2\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,\<langle>x\<^sub>1\<rangle>,y,\<langle>x\<^sub>3\<rangle>,\<langle>x\<^sub>4\<rangle>\<rparr>]\<rbrace>
                                                              \<^bold>& \<lbrace>\<langle>x\<^sub>3\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,\<langle>x\<^sub>1\<rangle>,\<langle>x\<^sub>2\<rangle>,y,\<langle>x\<^sub>4\<rangle>\<rparr>]\<rbrace>
                                                              \<^bold>& \<lbrace>\<langle>x\<^sub>4\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,\<langle>x\<^sub>1\<rangle>,\<langle>x\<^sub>2\<rangle>,\<langle>x\<^sub>3\<rangle>,y\<rparr>]\<rbrace>]"
  by AOT_meta_auto
lemma ax57_5: "[v \<Turnstile> \<lbrace>\<langle>x\<^sub>1\<rangle>::'a::\<kappa>,\<langle>x\<^sub>2\<rangle>::'a,\<langle>x\<^sub>3\<rangle>::'a,\<langle>x\<^sub>4\<rangle>::'a,\<langle>x\<^sub>5\<rangle>::'a,\<langle>F\<rangle>\<rbrace>
                     \<^bold>\<equiv> \<lbrace>\<langle>x\<^sub>1\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,y,\<langle>x\<^sub>2\<rangle>,\<langle>x\<^sub>3\<rangle>,\<langle>x\<^sub>4\<rangle>,\<langle>x\<^sub>5\<rangle>\<rparr>]\<rbrace>
                     \<^bold>& \<lbrace>\<langle>x\<^sub>2\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,\<langle>x\<^sub>1\<rangle>,y,\<langle>x\<^sub>3\<rangle>,\<langle>x\<^sub>4\<rangle>,\<langle>x\<^sub>5\<rangle>\<rparr>]\<rbrace>
                     \<^bold>& \<lbrace>\<langle>x\<^sub>3\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,\<langle>x\<^sub>1\<rangle>,\<langle>x\<^sub>2\<rangle>,y,\<langle>x\<^sub>4\<rangle>,\<langle>x\<^sub>5\<rangle>\<rparr>]\<rbrace>
                     \<^bold>& \<lbrace>\<langle>x\<^sub>4\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,\<langle>x\<^sub>1\<rangle>,\<langle>x\<^sub>2\<rangle>,\<langle>x\<^sub>3\<rangle>,y,\<langle>x\<^sub>5\<rangle>\<rparr>]\<rbrace>
                     \<^bold>& \<lbrace>\<langle>x\<^sub>5\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,\<langle>x\<^sub>1\<rangle>,\<langle>x\<^sub>2\<rangle>,\<langle>x\<^sub>3\<rangle>,\<langle>x\<^sub>4\<rangle>,y\<rparr>]\<rbrace>]"
  by AOT_meta_auto

lemma ax58: "[v \<Turnstile> \<lbrace>\<langle>x\<rangle>,\<langle>F\<rangle>\<rbrace> \<^bold>\<rightarrow> \<^bold>\<box>\<lbrace>\<langle>x\<rangle>,\<langle>F\<rangle>\<rbrace>]"
  using AOT_boxI AOT_enc_rigid AOT_impI by blast

lemma ax59: "[v \<Turnstile> \<lparr>O!,\<langle>x\<rangle>\<rparr> \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<exists> F . \<lbrace>\<langle>x\<rangle>,F\<rbrace>)]"
  apply (rule AOT_impI)
  unfolding AOT_Ordinary_def
  apply (drule AOT_beta1)
  apply AOT_meta_simp
  apply (simp add: ax45_2 AOT_concrete_exists)
  using AOT_concrete_exists AOT_enc_rigid AOT_exeI AOT_meta_nocoder ax45_2
  by blast

lemma ax60: "[v \<Turnstile> \<^bold>\<exists> x . (\<lparr>A!,x\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<phi> F))]"
  by (simp add: AOT_meta_A_objects Abstract_def)

end
