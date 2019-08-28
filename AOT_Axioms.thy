theory AOT_Axioms
  imports AOT_MetaDefs
begin

named_theorems Axioms

section\<open> Definitions \<close>

lemma conj_def[Axioms]: "\<phi> \<^bold>& \<psi> \<equiv>\<^sub>d\<^sub>f \<^bold>\<not>(\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi>)"
  by AOT_meta_auto
lemma disj_def[Axioms]: "\<phi> \<^bold>\<or> \<psi> \<equiv>\<^sub>d\<^sub>f \<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<psi>"
  by AOT_meta_auto
lemma iff_def[Axioms]: "\<phi> \<^bold>\<equiv> \<psi> \<equiv>\<^sub>d\<^sub>f ((\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>& (\<psi> \<^bold>\<rightarrow> \<phi>))"
  by AOT_meta_auto
lemma ex_def[Axioms]: "(\<^bold>\<exists> \<alpha> . \<phi> \<alpha>) \<equiv>\<^sub>d\<^sub>f (\<^bold>\<not>(\<^bold>\<forall> \<alpha> . \<^bold>\<not>\<phi> \<alpha>))"
  by AOT_meta_auto
lemma dia_def[Axioms]: "\<^bold>\<diamond>\<phi> \<equiv>\<^sub>d\<^sub>f \<^bold>\<not>(\<^bold>\<box>\<^bold>\<not>\<phi>)"
  by AOT_meta_auto

lemma exists_individual_def[Axioms]: "\<kappa>\<^bold>\<down> \<equiv>\<^sub>d\<^sub>f (\<^bold>\<exists> \<Omega> . \<lparr>\<Omega>, \<kappa>\<rparr>)"
  by (metis AOT_ex_def AOT_logical_exists_def ex_def)
lemma exists_relation_def[Axioms]: "\<Pi>\<^bold>\<down>  \<equiv>\<^sub>d\<^sub>f \<^bold>\<exists> \<nu> . \<lbrace>\<nu>,\<Pi>\<rbrace>"
  by (meson AOT_enc_impl_exists AOT_exS AOT_universal_encoder equivalent_by_definition_def)
lemma exists_relation2_def[Axioms]: "\<Pi>\<^bold>\<down> \<equiv>\<^sub>d\<^sub>f \<^bold>\<exists> \<nu>\<^sub>1 \<nu>\<^sub>2 . \<lbrace>\<nu>\<^sub>1,\<nu>\<^sub>2,\<Pi>\<rbrace>"
  apply (rule equivalent_by_definitionI)
  apply rule
  using AOT_universal_encoder[where 'a="'a\<times>'a"] unfolding AOT_universal_encoder_prod_def
   apply - apply (rule_tac x="AOT_universal_encoder" in AOT_exI, simp add: AOT_universal_encoder_exists)+
  apply (metis AOT_universal_encoder AOT_universal_encoder_prod_def)
  by (meson AOT_enc_impl_exists AOT_exS)
lemma exists_relation3_def[Axioms]: "\<Pi>\<^bold>\<down> \<equiv>\<^sub>d\<^sub>f \<^bold>\<exists> \<nu>\<^sub>1 \<nu>\<^sub>2 \<nu>\<^sub>3 . \<lbrace>\<nu>\<^sub>1,\<nu>\<^sub>2,\<nu>\<^sub>3,\<Pi>\<rbrace>"
  apply (rule equivalent_by_definitionI)
  apply rule
  using AOT_universal_encoder[where 'a="'a\<times>'a\<times>'a"] unfolding AOT_universal_encoder_prod_def
   apply - apply (rule_tac x="AOT_universal_encoder" in AOT_exI, simp add: AOT_universal_encoder_exists)+
  apply (metis AOT_universal_encoder AOT_universal_encoder_prod_def)
  by (meson AOT_enc_impl_exists AOT_exS)
lemma exists_relation4_def[Axioms]: "\<Pi>\<^bold>\<down> \<equiv>\<^sub>d\<^sub>f \<^bold>\<exists> \<nu>\<^sub>1 \<nu>\<^sub>2 \<nu>\<^sub>3 \<nu>\<^sub>4 . \<lbrace>\<nu>\<^sub>1,\<nu>\<^sub>2,\<nu>\<^sub>3,\<nu>\<^sub>4,\<Pi>\<rbrace>"
  apply (rule equivalent_by_definitionI)
  apply rule
  using AOT_universal_encoder[where 'a="'a\<times>'a\<times>'a\<times>'a"] unfolding AOT_universal_encoder_prod_def
   apply - apply (rule_tac x="AOT_universal_encoder" in AOT_exI, simp add: AOT_universal_encoder_exists)+
   apply (metis AOT_universal_encoder AOT_universal_encoder_prod_def)
  by (meson AOT_enc_impl_exists AOT_exS)
lemma exists_relation5_def[Axioms]: "\<Pi>\<^bold>\<down> \<equiv>\<^sub>d\<^sub>f \<^bold>\<exists> \<nu>\<^sub>1 \<nu>\<^sub>2 \<nu>\<^sub>3 \<nu>\<^sub>4 \<nu>\<^sub>5  . \<lbrace>\<nu>\<^sub>1,\<nu>\<^sub>2,\<nu>\<^sub>3,\<nu>\<^sub>4,\<nu>\<^sub>5,\<Pi>\<rbrace>"
  apply (rule equivalent_by_definitionI)
  apply rule
  using AOT_universal_encoder[where 'a="'a\<times>'a\<times>'a\<times>'a\<times>'a"] unfolding AOT_universal_encoder_prod_def
   apply - apply (rule_tac x="AOT_universal_encoder" in AOT_exI, simp add: AOT_universal_encoder_exists)+
   apply (metis AOT_universal_encoder AOT_universal_encoder_prod_def)
  by (meson AOT_enc_impl_exists AOT_exS)

lemma exists_relation0_def[Axioms]: "(\<Pi>::unit relation)\<^bold>\<down> \<equiv>\<^sub>d\<^sub>f [\<^bold>\<lambda> y . \<lparr>\<Pi>\<rparr>]\<^bold>\<down>"
  apply (rule equivalent_by_definitionI)
  apply rule
   apply (rule AOT_lambda_existsI) apply simp
  by (simp add: AOT_exists_relI AOT_logical_existsI AOT_meta_equiv_unit_def)

lemma Ordinary_def: "O! =\<^sub>d\<^sub>f [\<^bold>\<lambda>x. \<^bold>\<diamond>\<lparr>E!,x\<rparr>]"
  by (simp add: AOT_Ordinary_def AOT_equal_defI)

lemma Abstract_def: "A! =\<^sub>d\<^sub>f [\<^bold>\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<rparr>]"
  by (simp add: AOT_Abstract_def AOT_equal_defI)

lemma identity\<^sub>E_def: "AOT_identity\<^sub>E =\<^sub>d\<^sub>f [\<^bold>\<lambda> (x,y) . \<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>)]"
  apply (rule AOT_equal_defI)
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

section\<open> Axioms \<close>

lemma ax44_1: "[v \<Turnstile> \<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<phi>)]" by AOT_meta_auto
lemma ax44_2: "[v \<Turnstile> (\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<chi>)) \<^bold>\<rightarrow> ((\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<chi>))]" by AOT_meta_auto
lemma ax44_3: "[v \<Turnstile> (\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi>) \<^bold>\<rightarrow> ((\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> \<phi>)]" by AOT_meta_auto

lemma ax45_1: "[v \<Turnstile> (\<^bold>\<forall> \<alpha> . \<phi> \<alpha>) \<^bold>\<rightarrow> (\<tau>\<^bold>\<down> \<^bold>\<rightarrow> \<phi> \<tau>)]" by AOT_meta_auto
lemma ax45_2: "[v \<Turnstile> \<langle>\<tau>\<rangle>\<^bold>\<down>]" by AOT_meta_auto
lemma ax45_2: "[v \<Turnstile> \<tau>\<^bold>\<down>]" oops (* TODO: verify that this works for all description-free lambda expressions without encoding subformulas *)

lemma ax45_2_lambda_prop_denotes: "[v \<Turnstile> [\<^bold>\<lambda>x. \<psi>]\<^bold>\<down>]"
  by (simp add: AOT_lambda_existsI)
lemma ax45_2_lambda_exe_denotes: "[v \<Turnstile> [\<^bold>\<lambda>x. \<lparr>\<langle>F\<rangle>,x\<rparr>]\<^bold>\<down>]"
  by (simp add: AOT_exe_trans2 AOT_lambda_existsI)
lemma ax45_2_lambda_exe_denotes1: "[v \<Turnstile> [\<^bold>\<lambda>x. \<lparr>\<langle>F\<rangle>,x,\<langle>y\<rangle>\<rparr>]\<^bold>\<down>]"
  apply (rule AOT_lambda_existsI)
  by (metis AOT_equiv_existsE AOT_equiv_prodI AOT_equiv_sym AOT_exeS AOT_exe_trans AOT_exists_prodE2 fst_conv snd_conv)
lemma ax45_2_lambda_exe_denotes2: "[v \<Turnstile> [\<^bold>\<lambda>x. \<lparr>\<langle>F\<rangle>,\<langle>y\<rangle>,x\<rparr>]\<^bold>\<down>]"
  apply (rule AOT_lambda_existsI)
  by (metis AOT_equiv_existsE AOT_equiv_prodI AOT_equiv_sym AOT_exeS AOT_exe_trans AOT_exists_prodE1 fst_conv snd_conv)
lemma ax45_2_lambda_neg_denotes:
  assumes "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<^bold>\<not>(\<phi> x)]\<^bold>\<down>]"
  by (simp add: assms AOT_lambda_not_exists)
lemma ax45_2_lambda_impl_denotes:
  assumes "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x]\<^bold>\<down>]" and "[v \<Turnstile> [\<^bold>\<lambda>x. \<psi> x]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x \<^bold>\<rightarrow> \<psi> x]\<^bold>\<down>]"
  by (simp add: assms AOT_lambda_impl_exists)
lemma ax45_2_lambda_box_denotes:
  assumes "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<^bold>\<box>(\<phi> x)]\<^bold>\<down>]"
  by (simp add: assms AOT_lambda_box_exists)
lemma ax45_2_lambda_actual_denotes:
  assumes "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<^bold>\<A>(\<phi> x)]\<^bold>\<down>]"
  by (simp add: assms AOT_lambda_actual_exists)
lemma ax45_2_lambda_all_denotes:
  assumes "[v \<Turnstile> \<^bold>\<forall>y. [\<^bold>\<lambda>x. \<phi> x y]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<^bold>\<forall>y. \<phi> x y]\<^bold>\<down>]"
  using AOT_allS AOT_lambda_all_exists assms by fastforce
lemma ax45_2_lambda_all_denotes_alt:
  assumes "\<And>y. [v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x \<langle>y\<rangle>]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<^bold>\<forall>y. \<phi> x y]\<^bold>\<down>]"
  using ax45_2_lambda_all_denotes[OF AOT_meta_var_allI[of v "\<lambda> y . [\<^bold>\<lambda>x. \<phi> x y]\<^bold>\<down>", OF assms]]
  by blast


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

lemma ax54_2: "[v \<Turnstile> [\<^bold>\<lambda> \<lparr>\<phi>\<rparr>]\<^bold>\<down> \<^bold>\<equiv> \<phi>\<^bold>\<down>]"
  by (simp add: AOT_enc_impl_exists AOT_enc_unit_def AOT_iffS AOT_nec_trueI)

lemma ax54_3_stronger: "[v \<Turnstile> [\<^bold>\<lambda> \<^bold>\<forall>x . \<phi> x]\<^bold>\<down>]" (* TODO: note: this is stronger than the actual axiom *)
  by (simp add: AOT_lambda_existsI)
lemma ax54_3: "[v \<Turnstile> [\<^bold>\<lambda> \<phi> x]\<^bold>\<down> \<^bold>\<rightarrow> [\<^bold>\<lambda> \<^bold>\<forall>x . \<phi> x]\<^bold>\<down>]"
  using AOT_implS ax54_3_stronger by blast

lemma ax55_1: "Rigid(F) \<equiv>\<^sub>d\<^sub>f F\<^bold>\<down> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>x. \<lparr>F,x\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>F,x\<rparr>)"
  by (simp add: AOT_Rigid_def equivalent_by_definitionI)
lemma ax55_2: "Rigidifies(F,G) \<equiv>\<^sub>d\<^sub>f Rigid(F) \<^bold>& (\<^bold>\<forall> x . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>G,x\<rparr>)"
  by (simp add: AOT_Rigidifies_def equivalent_by_definitionI)

(* TODO: simplify proof *)
lemma ax56: "[v \<Turnstile> \<^bold>\<exists>F . Rigidifies(F,\<langle>G\<rangle>)]"
  apply AOT_meta_simp
  apply (rule_tac x="Abs_relation (\<lambda> x . if [v \<Turnstile> \<lparr>\<langle>G\<rangle>,x\<rparr>] then AOT_nec_true else AOT_nec_false)" in exI)
  apply (rule conjI)
   apply (rule AOT_logical_existsI)
  unfolding AOT_meta_equiv_relation_def
   apply (simp add: Abs_relation_inverse)
   apply (metis AOT_equivI AOT_exe_def AOT_exe_trans2 AOT_nec_falseE)
  unfolding AOT_Rigidifies_def AOT_Rigid_def
  apply AOT_meta_auto
  using AOT_equivE3 AOT_exists_necI apply blast
  apply (metis (full_types) AOT_exeS AOT_exe_trans2)
  using AOT_equivE2 AOT_exists_necI apply blast
  apply (simp add: AOT_exeE3 AOT_exeI AOT_exe_trans2)
  apply (meson AOT_exists_necI)
  using AOT_equivE3 AOT_exists_necI apply blast
  apply (metis AOT_exeE3 AOT_exeI AOT_exe_trans2)
  using AOT_equivE2 AOT_exists_necI apply blast
  apply (simp add: AOT_exeE3 AOT_exeI AOT_exe_trans2)
  apply (meson AOT_exists_necI)
  using AOT_equivE3 AOT_logical_existsS apply blast
  apply (metis AOT_exeE3 AOT_exeI AOT_exe_trans2)
  using AOT_equivE2 AOT_exists_necI apply blast
  apply (simp add: AOT_exeE3 AOT_exeI AOT_exe_trans2)
  by (meson AOT_exists_necI)

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
  by (simp add: AOT_Abstract_def AOT_meta_A_objects)

end
