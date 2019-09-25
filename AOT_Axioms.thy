theory AOT_Axioms
  imports AOT_MetaDefs
begin        

named_theorems Axioms

section\<open> Definitions \<close>

lemma conj_def[Axioms]: "\<phi> \<^bold>& \<psi> \<equiv>\<^sub>d\<^sub>f \<^bold>\<not>(\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi>)"
  by (auto simp: AOT_meta_simp)
lemma disj_def[Axioms]: "\<phi> \<^bold>\<or> \<psi> \<equiv>\<^sub>d\<^sub>f \<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<psi>"
  by (auto simp: AOT_meta_simp)
lemma iff_def[Axioms]: "\<phi> \<^bold>\<equiv> \<psi> \<equiv>\<^sub>d\<^sub>f ((\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>& (\<psi> \<^bold>\<rightarrow> \<phi>))"
  by (auto simp: AOT_meta_simp)
lemma ex_def[Axioms]: "(\<^bold>\<exists> \<alpha> . \<phi> \<alpha>) \<equiv>\<^sub>d\<^sub>f (\<^bold>\<not>(\<^bold>\<forall> \<alpha> . \<^bold>\<not>\<phi> \<alpha>))"
  by (auto simp: AOT_meta_simp)
lemma dia_def[Axioms]: "\<^bold>\<diamond>\<phi> \<equiv>\<^sub>d\<^sub>f \<^bold>\<not>(\<^bold>\<box>\<^bold>\<not>\<phi>)"
  by (auto simp: AOT_meta_simp)

lemma exists_individual_def[Axioms]: "\<kappa>\<^bold>\<down> \<equiv>\<^sub>d\<^sub>f (\<^bold>\<exists> \<Omega> . \<lparr>\<Omega>, \<kappa>\<rparr>)"
  by (rule equivalent_by_definitionI; (rule_tac \<tau>="drel (\<lambda> x . \<epsilon>\<^sub>\<o> v . True)" in AOT_exI)?)
     (insert AOT_exeE2, auto simp: AOT_meta_simp)

lemma exists_relation_def[Axioms]: "\<Pi>\<^bold>\<down>  \<equiv>\<^sub>d\<^sub>f \<^bold>\<exists> \<nu> . \<lbrace>\<nu>,\<Pi>\<rbrace>"
  by (rule equivalent_by_definitionI; simp add: AOT_meta_simp)
     (insert AOT_universal_encoder[of "reld \<Pi>"], blast)+

lemma exists_relation2_def[Axioms]: "\<Pi>\<^bold>\<down> \<equiv>\<^sub>d\<^sub>f \<^bold>\<exists> \<nu>\<^sub>1 \<nu>\<^sub>2 . \<lbrace>\<nu>\<^sub>1,\<nu>\<^sub>2,\<Pi>\<rbrace>"
  using exists_relation_def[where 'a="'a\<times>'b", THEN equivalent_by_definitionE]
  by (auto simp: AOT_meta_simp)

lemma exists_relation3_def[Axioms]: "\<Pi>\<^bold>\<down> \<equiv>\<^sub>d\<^sub>f \<^bold>\<exists> \<nu>\<^sub>1 \<nu>\<^sub>2 \<nu>\<^sub>3 . \<lbrace>\<nu>\<^sub>1,\<nu>\<^sub>2,\<nu>\<^sub>3,\<Pi>\<rbrace>"
  using exists_relation_def[where 'a="'a\<times>'b\<times>'c", THEN equivalent_by_definitionE]
  by (auto simp: AOT_meta_simp)

lemma exists_relation0_def[Axioms]: "\<phi>\<^bold>\<down> \<equiv>\<^sub>d\<^sub>f [\<^bold>\<lambda> y . \<phi>]\<^bold>\<down>"
  by (rule equivalent_by_definitionI)
     (auto simp: AOT_lambda_denotes_propI AOT_denotesS AOT_equiv_\<o>_def
                 AOT_equiv_rel.simps(1) AOT_lambda_def)

lemma Ordinary_def[Axioms]: "O! =\<^sub>d\<^sub>f [\<^bold>\<lambda>x. \<^bold>\<diamond>\<lparr>E!,x\<rparr>]"
  by (rule AOT_equal_defI) (simp add: AOT_ordinary_def)

lemma Abstract_def[Axioms]: "A! =\<^sub>d\<^sub>f [\<^bold>\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<rparr>]"
  by (rule AOT_equal_defI) (simp add: AOT_abstract_def)

lemma identity\<^sub>E_def[Axioms]:
  "AOT_identity\<^sub>E =\<^sub>d\<^sub>f [\<^bold>\<lambda> (x,y) . \<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>)]"
  by (rule AOT_equal_defI) (simp add: AOT_identity\<^sub>E_def)

lemma identity\<^sub>E_infix_def[Axioms]:
  "(\<kappa> \<^bold>=\<^sub>E \<kappa>') = \<lparr>[\<^bold>\<lambda> (x,y) . \<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>)], \<kappa>, \<kappa>'\<rparr>"
  unfolding AOT_identity\<^sub>E_infix_def AOT_identity\<^sub>E_def by simp

(* TODO: nicer proof *)
lemma identity\<kappa>_def[Axioms]:
  "(\<kappa>::'a::\<kappa>) \<^bold>= \<kappa>' \<equiv>\<^sub>d\<^sub>f (\<kappa> \<^bold>=\<^sub>E \<kappa>') \<^bold>\<or> (\<lparr>A!,\<kappa>\<rparr> \<^bold>& \<lparr>A!,\<kappa>'\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>\<Omega> . \<lbrace>\<kappa>,\<Omega>\<rbrace> \<^bold>\<equiv> \<lbrace>\<kappa>',\<Omega>\<rbrace>))"
  apply (rule equivalent_by_definitionI)
   apply (simp add: AOT_meta_simp)
   apply safe
   apply (rule identity\<^sub>E_equivI)
     apply (auto simp: AOT_not_abstract_is_ordinary AOT_disjS)
  using AOT_idS identity\<^sub>E_equivE(1) identity\<^sub>E_equivE(2)
        identity\<^sub>E_equivE(3) AOT_meta_ordinary_identity apply fastforce
  apply (simp add: AOT_conjS AOT_boxS AOT_allS AOT_idS AOT_iffS AOT_enc_metaS)
  using AOT_meta_abstract_identity[of _ \<kappa> \<kappa>'] AOT_denotesS AOT_exeE2 AOT_meta_enc_eqI by blast

lemma identity\<Pi>1_def[Axioms]: "\<Pi> \<^bold>= \<Pi>' \<equiv>\<^sub>d\<^sub>f \<Pi>\<^bold>\<down> \<^bold>& \<Pi>'\<^bold>\<down> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>\<nu> :: 'a :: \<kappa>. \<lbrace>\<nu>,\<Pi>\<rbrace> \<^bold>\<equiv> \<lbrace>\<nu>,\<Pi>'\<rbrace>)"
  by (rule equivalent_by_definitionI) (auto simp: AOT_meta_simp AOT_relation_identity)
lemma identity\<Pi>2_def[Axioms]:
  "\<Pi> \<^bold>= \<Pi>' \<equiv>\<^sub>d\<^sub>f \<Pi>\<^bold>\<down> \<^bold>& \<Pi>'\<^bold>\<down> \<^bold>& (\<^bold>\<forall>\<nu> . [\<^bold>\<lambda>\<mu> . \<lparr>\<Pi>,\<mu>,\<nu>\<rparr>] \<^bold>= [\<^bold>\<lambda>\<mu> . \<lparr>\<Pi>',\<mu>,\<nu>\<rparr>] \<^bold>& [\<^bold>\<lambda>\<mu> . \<lparr>\<Pi>,\<nu>,\<mu>\<rparr>] \<^bold>= [\<^bold>\<lambda>\<mu> . \<lparr>\<Pi>',\<nu>,\<mu>\<rparr>])"
  by (rule equivalent_by_definitionI)
     (auto simp: AOT_meta_simp AOT_projection_identity AOT_lambda_prod1_denotesI
                 AOT_lambda_prod2_denotesI)

(* TODO: nicer proof *)
lemma identity\<Pi>3_def[Axioms]: "\<Pi> \<^bold>= \<Pi>' \<equiv>\<^sub>d\<^sub>f \<Pi>\<^bold>\<down> \<^bold>& \<Pi>'\<^bold>\<down> \<^bold>& (\<^bold>\<forall>\<nu>\<^sub>1 \<nu>\<^sub>2 . [\<^bold>\<lambda>\<mu> . \<lparr>\<Pi>,\<mu>,\<nu>\<^sub>1,\<nu>\<^sub>2\<rparr>] \<^bold>= [\<^bold>\<lambda>\<mu> . \<lparr>\<Pi>',\<mu>,\<nu>\<^sub>1,\<nu>\<^sub>2\<rparr>]
                                                      \<^bold>& [\<^bold>\<lambda>\<mu> . \<lparr>\<Pi>,\<nu>\<^sub>1,\<mu>,\<nu>\<^sub>2\<rparr>] \<^bold>= [\<^bold>\<lambda>\<mu> . \<lparr>\<Pi>',\<nu>\<^sub>1,\<mu>,\<nu>\<^sub>2\<rparr>]
                                                      \<^bold>& [\<^bold>\<lambda>\<mu> . \<lparr>\<Pi>,\<nu>\<^sub>1,\<nu>\<^sub>2,\<mu>\<rparr>] \<^bold>= [\<^bold>\<lambda>\<mu> . \<lparr>\<Pi>',\<nu>\<^sub>1,\<nu>\<^sub>2,\<mu>\<rparr>])"
  apply (rule equivalent_by_definitionI)
   apply (auto simp: AOT_meta_simp AOT_lambda_prod1_denotesI AOT_lambda_prod2_denotesI)
    apply (rule AOT_lambda_denotesI[simplified AOT_denotesS]; rule AOT_meta_equiv_indistinguishableI; simp add: AOT_meta_simp)+
  apply (subst AOT_projection_identity[of \<Pi> \<Pi>']; simp?)
     apply (rule prod.induct) by (auto simp: AOT_meta_simp)

lemma identity\<Pi>0_def[Axioms]: "\<Pi> \<^bold>= \<Pi>' \<equiv>\<^sub>d\<^sub>f \<Pi>\<^bold>\<down> \<^bold>& \<Pi>'\<^bold>\<down> \<^bold>& [\<^bold>\<lambda>x . \<Pi>] \<^bold>= [\<^bold>\<lambda>x . \<Pi>']"
  by (rule equivalent_by_definitionI; simp add: AOT_meta_simp AOT_lambda_def) meson

section\<open> Axioms \<close>

lemma ax44_1: "[v \<Turnstile> \<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<phi>)]" by (auto simp: AOT_meta_simp)
lemma ax44_2: "[v \<Turnstile> (\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<chi>)) \<^bold>\<rightarrow> ((\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<chi>))]" by (auto simp: AOT_meta_simp)
lemma ax44_3: "[v \<Turnstile> (\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi>) \<^bold>\<rightarrow> ((\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> \<phi>)]" by (auto simp: AOT_meta_simp)

lemma ax45_1: "[v \<Turnstile> (\<^bold>\<forall> \<alpha> . \<phi> \<alpha>) \<^bold>\<rightarrow> (\<tau>\<^bold>\<down> \<^bold>\<rightarrow> \<phi> \<tau>)]" by (auto simp: AOT_meta_simp)
lemma ax45_2: "[v \<Turnstile> \<langle>\<tau>\<rangle>\<^bold>\<down>]" by (simp add: AOT_var_denotes)
lemma ax45_2: "[v \<Turnstile> \<tau>\<^bold>\<down>]" oops (* TODO: verify that this works for all description-free lambda expressions without encoding subformulas *)

lemma ax45_2_lambda_prop_denotes: "[v \<Turnstile> [\<^bold>\<lambda>x. p]\<^bold>\<down>]" by (rule AOT_lambda_denotes_intros)+

lemma ax45_2_lambda_exe_denotes: "[v \<Turnstile> [\<^bold>\<lambda>x. \<lparr>\<langle>F\<rangle>,x\<rparr>]\<^bold>\<down>]"
  by (rule AOT_lambda_denotes_intros)
(* TODO: complete this *)
lemma ax45_2_lambda_exe_denotes1: "[v \<Turnstile> [\<^bold>\<lambda>x. \<lparr>\<langle>F\<rangle>,x,\<langle>y\<rangle>\<rparr>]\<^bold>\<down>]"
  including AOT_induct
  by (induct F; induct y; rule AOT_lambda_denotesI)
     (simp add: AOT_equiv_prodI AOT_equiv_rel.simps(1) AOT_meta_equiv_indistinguishableI)
lemma ax45_2_lambda_exe_denotes2: "[v \<Turnstile> [\<^bold>\<lambda>x. \<lparr>\<langle>F\<rangle>,\<langle>y\<rangle>,x\<rparr>]\<^bold>\<down>]"
  including AOT_induct
  by (induct F; induct y; rule AOT_lambda_denotesI)
     (simp add: AOT_equiv_prodI AOT_equiv_rel.simps(1) AOT_meta_equiv_indistinguishableI)

lemma ax45_2_lambda_neg_denotes:
  assumes "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<^bold>\<not>(\<phi> x)]\<^bold>\<down>]"
  using assms by (rule AOT_lambda_denotes_intros)
lemma ax45_2_lambda_impl_denotes:
  assumes "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x]\<^bold>\<down>]" and "[v \<Turnstile> [\<^bold>\<lambda>x. \<psi> x]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x \<^bold>\<rightarrow> \<psi> x]\<^bold>\<down>]"
  using assms by (rule AOT_lambda_denotes_intros)
lemma ax45_2_lambda_box_denotes:
  assumes "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<^bold>\<box>(\<phi> x)]\<^bold>\<down>]"
  using assms by (rule AOT_lambda_denotes_intros)
lemma ax45_2_lambda_actual_denotes:
  assumes "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<^bold>\<A>(\<phi> x)]\<^bold>\<down>]"
  using assms by (rule AOT_lambda_denotes_intros)
lemma ax45_2_lambda_all_denotes:
  assumes "[v \<Turnstile> \<^bold>\<forall>y. [\<^bold>\<lambda>x. \<phi> x y]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<^bold>\<forall>y. \<phi> x y]\<^bold>\<down>]"
  using assms by (clarify intro!: AOT_lambda_denotes_intros; auto simp: AOT_meta_simp)
lemma ax45_2_lambda_all_denotes_alt:
  assumes "\<And>y. [v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x \<langle>y\<rangle>]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<^bold>\<forall>y. \<phi> x y]\<^bold>\<down>]"
  using assms
  by (clarify intro!: AOT_lambda_denotes_intros; simp add: AOT_meta_simp)
     (insert Rep_var_cases; auto)

lemma ax45_3: "[v \<Turnstile> (\<^bold>\<forall> \<alpha> . \<phi> \<alpha> \<^bold>\<rightarrow> \<psi> \<alpha>) \<^bold>\<rightarrow> ((\<^bold>\<forall> \<alpha> . \<phi> \<alpha>) \<^bold>\<rightarrow> (\<^bold>\<forall> \<alpha> . \<psi> \<alpha>))]"
  by (auto simp: AOT_meta_simp)
lemma ax45_4: "[v \<Turnstile> \<phi> \<^bold>\<rightarrow> (\<^bold>\<forall> \<alpha> . \<phi>)]" by (auto simp: AOT_meta_simp)
lemma ax45_5_1: "[v \<Turnstile> (\<lparr>\<Pi>, \<kappa>\<rparr> \<^bold>\<or> \<lbrace>\<kappa>, \<Pi>\<rbrace>) \<^bold>\<rightarrow> (\<Pi>\<^bold>\<down> \<^bold>& \<kappa>\<^bold>\<down>)]"
  by (simp add: AOT_meta_simp) (meson AOT_denotesS AOT_exeE1 AOT_exeE2)

lemma ax45_5_2: "[v \<Turnstile> (\<lparr>\<Pi>, \<kappa>\<^sub>1, \<kappa>\<^sub>2\<rparr> \<^bold>\<or> \<lbrace>\<kappa>\<^sub>1, \<kappa>\<^sub>2, \<Pi>\<rbrace>) \<^bold>\<rightarrow> (\<Pi>\<^bold>\<down> \<^bold>& \<kappa>\<^sub>1\<^bold>\<down> \<^bold>& \<kappa>\<^sub>2\<^bold>\<down>)]"
  using ax45_5_1[of v \<Pi> "(\<kappa>\<^sub>1, \<kappa>\<^sub>2)"] by (simp add: AOT_meta_simp)
lemma ax45_5_3: "[v \<Turnstile> (\<lparr>\<Pi>, \<kappa>\<^sub>1, \<kappa>\<^sub>2, \<kappa>\<^sub>3\<rparr> \<^bold>\<or> \<lbrace>\<kappa>\<^sub>1, \<kappa>\<^sub>2, \<kappa>\<^sub>3, \<Pi>\<rbrace>) \<^bold>\<rightarrow> (\<Pi>\<^bold>\<down> \<^bold>& \<kappa>\<^sub>1\<^bold>\<down> \<^bold>& \<kappa>\<^sub>2\<^bold>\<down> \<^bold>& \<kappa>\<^sub>3\<^bold>\<down>)]"
  using ax45_5_1[of v \<Pi> "(\<kappa>\<^sub>1, \<kappa>\<^sub>2, \<kappa>\<^sub>3)"] by (simp add: AOT_meta_simp)
lemma ax45_5_4: "[v \<Turnstile> (\<lparr>\<Pi>, \<kappa>\<^sub>1, \<kappa>\<^sub>2, \<kappa>\<^sub>3, \<kappa>\<^sub>4\<rparr> \<^bold>\<or> \<lbrace>\<kappa>\<^sub>1, \<kappa>\<^sub>2, \<kappa>\<^sub>3, \<kappa>\<^sub>4, \<Pi>\<rbrace>) \<^bold>\<rightarrow> (\<Pi>\<^bold>\<down> \<^bold>& \<kappa>\<^sub>1\<^bold>\<down> \<^bold>& \<kappa>\<^sub>2\<^bold>\<down> \<^bold>& \<kappa>\<^sub>3\<^bold>\<down> \<^bold>& \<kappa>\<^sub>4\<^bold>\<down>)]"
  using ax45_5_1[of v \<Pi> "(\<kappa>\<^sub>1, \<kappa>\<^sub>2, \<kappa>\<^sub>3, \<kappa>\<^sub>4)"] by (simp add: AOT_meta_simp)


lemma ax46: "[v \<Turnstile> \<langle>\<alpha>\<rangle> \<^bold>= \<langle>\<beta>\<rangle> \<^bold>\<rightarrow> (\<phi> \<langle>\<alpha>\<rangle> \<^bold>\<rightarrow> \<phi> \<langle>\<beta>\<rangle>)]"
  by (simp add: AOT_meta_simp)

(* not really an axiom, but a theorem - here to make sure the stronger theorem stays true in the models *)
lemma ax46_terms: "[v \<Turnstile> \<alpha> \<^bold>= \<beta> \<^bold>\<rightarrow> (\<phi> \<alpha> \<^bold>\<rightarrow> \<phi> \<beta>)]"
  by (simp add: AOT_meta_simp)

lemma ax48: "[dw \<Turnstile> \<^bold>\<A>\<phi> \<^bold>\<equiv> \<phi>]" by (simp add: AOT_meta_simp)

lemma ax49_1: "[v \<Turnstile> \<^bold>\<A>\<^bold>\<not>\<phi> \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<A>\<phi>]" by (simp add: AOT_meta_simp)
lemma ax49_2: "[v \<Turnstile> \<^bold>\<A>(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<equiv> (\<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<^bold>\<A>\<psi>)]" by (simp add: AOT_meta_simp)
lemma ax49_3: "[v \<Turnstile> \<^bold>\<A>(\<^bold>\<forall> \<alpha> . \<phi> \<alpha>) \<^bold>\<equiv> (\<^bold>\<forall> \<alpha> . \<^bold>\<A>\<phi> \<alpha>)]" by (simp add: AOT_meta_simp)
lemma ax49_4: "[v \<Turnstile> \<^bold>\<A>\<phi> \<^bold>\<equiv> \<^bold>\<A>\<^bold>\<A>\<phi>]" by (simp add: AOT_meta_simp)

lemma ax50_1: "[v \<Turnstile> \<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>)]" by (simp add: AOT_meta_simp)
lemma ax50_2: "[v \<Turnstile> \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>]" by (simp add: AOT_meta_simp)
lemma ax50_3: "[v \<Turnstile> \<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>]" by (simp add: AOT_meta_simp)
lemma ax50_4: "[v \<Turnstile> \<^bold>\<diamond>(\<^bold>\<exists>x::'a::\<kappa> . \<lparr>E!,x\<rparr> \<^bold>& \<^bold>\<not>\<^bold>\<A>\<lparr>E!,x\<rparr>)]"
  using AOT_denotesS AOT_exeE2 AOT_meta_contingently_concrete_object
  by (simp add: AOT_meta_simp) blast

lemma ax51_1: "[v \<Turnstile> \<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<A>\<phi>]" by (simp add: AOT_meta_simp)
lemma ax51_2: "[v \<Turnstile> \<^bold>\<box>\<phi> \<^bold>\<equiv> \<^bold>\<A>(\<^bold>\<box>\<phi>)]" by (simp add: AOT_meta_simp)


lemma ax52: "[v \<Turnstile> (\<langle>x\<rangle> \<^bold>= (\<^bold>\<iota>x. \<phi> x)) \<^bold>\<equiv> (\<^bold>\<forall> z . (\<^bold>\<A>\<phi> z \<^bold>\<equiv> z \<^bold>= \<langle>x\<rangle>))]"
  using AOT_meta_descriptions[of "\<langle>x\<rangle>" v \<phi>]
  using Rep_var by (auto simp: AOT_meta_simp Rep_var)
  

(* axiom 53.1 is implicitly true, since alphabetic variant are meta-logically identical in Isabelle/HOL already *)

lemma ax53_2: "[v \<Turnstile> [\<^bold>\<lambda>x . \<phi> x]\<^bold>\<down> \<^bold>\<rightarrow> (\<lparr>[\<^bold>\<lambda>x . \<phi> x],\<langle>x\<rangle>\<rparr> \<^bold>\<equiv> \<phi> \<langle>x\<rangle>)]"
  by (simp add: AOT_meta_beta AOT_iffS AOT_impS AOT_var_denotes)

lemma ax53_3: "[v \<Turnstile> [\<^bold>\<lambda>x . \<lparr>\<langle>F\<rangle>,x\<rparr>] \<^bold>= \<langle>F\<rangle>]"
  by (simp add: AOT_meta_eta AOT_idS AOT_var_equiv)

lemma ax54_1: "[v \<Turnstile> ([\<^bold>\<lambda>y . \<phi> y]\<^bold>\<down> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> y . \<phi> y \<^bold>\<equiv> \<psi> y)) \<^bold>\<rightarrow> [\<^bold>\<lambda>y . \<psi> y]\<^bold>\<down>]"
  by (simp add: AOT_impS AOT_conjS AOT_boxS AOT_allS AOT_iffS)
     (metis (full_types) AOT_lambda_denotesE AOT_lambda_denotesI AOT_meta_equiv_indistinguishable)

lemma ax54_2: "[v \<Turnstile> [\<^bold>\<lambda> \<phi>]\<^bold>\<down> \<^bold>\<equiv> \<phi>\<^bold>\<down>]"
  by (simp add: AOT_meta_simp)

lemma ax54_3_stronger[AOT_meta]: "[v \<Turnstile> [\<^bold>\<lambda> \<^bold>\<forall>x . \<phi> x]\<^bold>\<down>]" (* TODO: note: this is stronger than the actual axiom *)
  by (simp add: AOT_meta_simp AOT_equiv_\<o>_def)
lemma ax54_3: "[v \<Turnstile> [\<^bold>\<lambda> \<phi> x]\<^bold>\<down> \<^bold>\<rightarrow> [\<^bold>\<lambda> \<^bold>\<forall>x . \<phi> x]\<^bold>\<down>]"
  by (simp add: AOT_meta_simp AOT_equiv_\<o>_def)

lemma ax55_1: "Rigid(F) \<equiv>\<^sub>d\<^sub>f F\<^bold>\<down> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>x. \<lparr>F,x\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>F,x\<rparr>)"
  by (simp add: AOT_Rigid_def equivalent_by_definitionI)
lemma ax55_2: "Rigidifies(F,G) \<equiv>\<^sub>d\<^sub>f Rigid(F) \<^bold>& (\<^bold>\<forall> x . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>G,x\<rparr>)"
  by (simp add: AOT_Rigidifies_def equivalent_by_definitionI)

(* TODO: simplify proof *)
lemma ax56: "[v \<Turnstile> \<^bold>\<exists>F . Rigidifies(F,\<langle>G\<rangle>)]"
  apply (rule_tac \<tau>="[\<^bold>\<lambda> x. \<epsilon>\<^sub>\<o> w . [v \<Turnstile> \<lparr>\<langle>G\<rangle>, x\<rparr>]]" in AOT_exI)
  apply (simp add: AOT_lambda_denotesI AOT_meta_equiv_indistinguishableI AOT_var_equiv)
  unfolding AOT_Rigidifies_def AOT_Rigid_def
   apply (auto simp: AOT_conjS AOT_iffS AOT_impS AOT_boxS AOT_allS)
  apply (rule AOT_lambda_denotesI; metis AOT_exeE1 AOT_proposition_choice AOT_meta_equiv_indistinguishable)
  apply (metis AOT_meta_beta AOT_denotesS AOT_exeE1 AOT_proposition_choice)
   apply (meson AOT_meta_betaE AOT_proposition_choice)
  apply (rule AOT_meta_beta[THEN iffD2])
  apply (rule AOT_lambda_denotesI; metis AOT_exeE1 AOT_proposition_choice AOT_meta_equiv_indistinguishable)
  by (auto simp: AOT_meta_simp)

lemma ax57_2: "[v \<Turnstile> \<lbrace>\<langle>x\<^sub>1\<rangle>::'a::\<kappa>,\<langle>x\<^sub>2\<rangle>::'a::\<kappa>,\<langle>F\<rangle>\<rbrace> \<^bold>\<equiv> \<lbrace>\<langle>x\<^sub>1\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,y,\<langle>x\<^sub>2\<rangle>\<rparr>]\<rbrace>
                                                 \<^bold>& \<lbrace>\<langle>x\<^sub>2\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,\<langle>x\<^sub>1\<rangle>,y\<rparr>]\<rbrace>]"
  including AOT_induct
  by (induct F; induct x\<^sub>1; induct x\<^sub>2)
     (simp add: AOT_meta_equiv_indistinguishableI AOT_meta_simp AOT_meta_enc_prod_def)

lemma ax57_3: "[v \<Turnstile> \<lbrace>\<langle>x\<^sub>1\<rangle>::'a::\<kappa>,\<langle>x\<^sub>2\<rangle>::'a::\<kappa>,\<langle>x\<^sub>3\<rangle>::'a::\<kappa>,\<langle>F\<rangle>\<rbrace> \<^bold>\<equiv> \<lbrace>\<langle>x\<^sub>1\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,y,\<langle>x\<^sub>2\<rangle>,\<langle>x\<^sub>3\<rangle>\<rparr>]\<rbrace>
                                                            \<^bold>& \<lbrace>\<langle>x\<^sub>2\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,\<langle>x\<^sub>1\<rangle>,y,\<langle>x\<^sub>3\<rangle>\<rparr>]\<rbrace>
                                                            \<^bold>& \<lbrace>\<langle>x\<^sub>3\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,\<langle>x\<^sub>1\<rangle>,\<langle>x\<^sub>2\<rangle>,y\<rparr>]\<rbrace>]"
  including AOT_induct
  by (induct F; induct x\<^sub>1; induct x\<^sub>2; induct x\<^sub>3)
     (simp add: AOT_meta_equiv_indistinguishableI AOT_meta_simp AOT_meta_enc_prod_def)


lemma ax57_4: "[v \<Turnstile> \<lbrace>\<langle>x\<^sub>1\<rangle>::'a::\<kappa>,\<langle>x\<^sub>2\<rangle>::'a,\<langle>x\<^sub>3\<rangle>::'a,\<langle>x\<^sub>4\<rangle>::'a,\<langle>F\<rangle>\<rbrace> \<^bold>\<equiv> \<lbrace>\<langle>x\<^sub>1\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,y,\<langle>x\<^sub>2\<rangle>,\<langle>x\<^sub>3\<rangle>,\<langle>x\<^sub>4\<rangle>\<rparr>]\<rbrace>
                                                              \<^bold>& \<lbrace>\<langle>x\<^sub>2\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,\<langle>x\<^sub>1\<rangle>,y,\<langle>x\<^sub>3\<rangle>,\<langle>x\<^sub>4\<rangle>\<rparr>]\<rbrace>
                                                              \<^bold>& \<lbrace>\<langle>x\<^sub>3\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,\<langle>x\<^sub>1\<rangle>,\<langle>x\<^sub>2\<rangle>,y,\<langle>x\<^sub>4\<rangle>\<rparr>]\<rbrace>
                                                              \<^bold>& \<lbrace>\<langle>x\<^sub>4\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,\<langle>x\<^sub>1\<rangle>,\<langle>x\<^sub>2\<rangle>,\<langle>x\<^sub>3\<rangle>,y\<rparr>]\<rbrace>]"
  including AOT_induct
  by (induct F; induct x\<^sub>1; induct x\<^sub>2; induct x\<^sub>3; induct x\<^sub>4)
     (simp add: AOT_meta_equiv_indistinguishableI AOT_meta_simp AOT_meta_enc_prod_def)

lemma ax57_5: "[v \<Turnstile> \<lbrace>\<langle>x\<^sub>1\<rangle>::'a::\<kappa>,\<langle>x\<^sub>2\<rangle>::'a,\<langle>x\<^sub>3\<rangle>::'a,\<langle>x\<^sub>4\<rangle>::'a,\<langle>x\<^sub>5\<rangle>::'a,\<langle>F\<rangle>\<rbrace>
                     \<^bold>\<equiv> \<lbrace>\<langle>x\<^sub>1\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,y,\<langle>x\<^sub>2\<rangle>,\<langle>x\<^sub>3\<rangle>,\<langle>x\<^sub>4\<rangle>,\<langle>x\<^sub>5\<rangle>\<rparr>]\<rbrace>
                     \<^bold>& \<lbrace>\<langle>x\<^sub>2\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,\<langle>x\<^sub>1\<rangle>,y,\<langle>x\<^sub>3\<rangle>,\<langle>x\<^sub>4\<rangle>,\<langle>x\<^sub>5\<rangle>\<rparr>]\<rbrace>
                     \<^bold>& \<lbrace>\<langle>x\<^sub>3\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,\<langle>x\<^sub>1\<rangle>,\<langle>x\<^sub>2\<rangle>,y,\<langle>x\<^sub>4\<rangle>,\<langle>x\<^sub>5\<rangle>\<rparr>]\<rbrace>
                     \<^bold>& \<lbrace>\<langle>x\<^sub>4\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,\<langle>x\<^sub>1\<rangle>,\<langle>x\<^sub>2\<rangle>,\<langle>x\<^sub>3\<rangle>,y,\<langle>x\<^sub>5\<rangle>\<rparr>]\<rbrace>
                     \<^bold>& \<lbrace>\<langle>x\<^sub>5\<rangle>,[\<^bold>\<lambda>y . \<lparr>\<langle>F\<rangle>,\<langle>x\<^sub>1\<rangle>,\<langle>x\<^sub>2\<rangle>,\<langle>x\<^sub>3\<rangle>,\<langle>x\<^sub>4\<rangle>,y\<rparr>]\<rbrace>]"
  including AOT_induct
  by (induct F; induct x\<^sub>1; induct x\<^sub>2; induct x\<^sub>3; induct x\<^sub>4; induct x\<^sub>5)
     (simp add: AOT_meta_equiv_indistinguishableI AOT_meta_simp AOT_meta_enc_prod_def)

lemma ax58: "[v \<Turnstile> \<lbrace>\<langle>x\<rangle>,\<langle>F\<rangle>\<rbrace> \<^bold>\<rightarrow> \<^bold>\<box>\<lbrace>\<langle>x\<rangle>,\<langle>F\<rangle>\<rbrace>]"
  by (simp add: AOT_boxS AOT_impS AOT_enc_metaS) 

lemma ax59: "[v \<Turnstile> \<lparr>O!,\<langle>x\<rangle>::'a::\<kappa>\<rparr> \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<exists> F . \<lbrace>\<langle>x\<rangle>,F\<rbrace>)]"
  by (auto simp: AOT_nocoder AOT_notS AOT_impS AOT_exS AOT_ordinaryS)

lemma ax60: "[v \<Turnstile> \<^bold>\<exists> x :: 'a::\<kappa>. (\<lparr>A!,x\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<phi> F))]"
  using AOT_A_objects AOT_denotesS AOT_exeE2
  by (simp add: AOT_exS AOT_conjS AOT_allS AOT_iffS) blast

end
