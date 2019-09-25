theory AOT_Relation
  imports AOT_Term
begin

typedecl 'a nullrel

datatype 'a rel ("<_>") = drel (reld: "'a \<upsilon> \<Rightarrow> \<o>") | nullrel "'a nullrel"
consts nullrel_choice :: "'a \<Rightarrow> 'b nullrel"

instantiation rel :: (AOT_Term) AOT_Term
begin
fun AOT_equiv_rel where
  [AOT_meta_simp]: "(drel x \<approx> drel y) = (x = y)"
| [AOT_meta_simp]: "(nullrel x \<approx> _) = False"
| [AOT_meta_simp]: "(_ \<approx> nullrel x) = False"
declare AOT_equiv_rel.cases[AOT_meta] AOT_equiv_rel.elims[AOT_meta]
        AOT_equiv_rel.induct[AOT_meta, induct del] AOT_equiv_rel.pelims[AOT_meta]
        AOT_equiv_rel.simps[AOT_meta, simp del]
instance apply (standard; rule part_equivpI; (rule sympI | rule transpI)?)
  using AOT_equiv_rel.simps(1) apply blast
  using AOT_equiv_rel.elims(2) apply blast
  using AOT_equiv_rel.elims(2) by blast
end

function AOT_exe where
  [AOT_meta_simp]: "AOT_exe (drel F) \<kappa> = F (abs_\<upsilon> \<kappa>)" if "\<kappa> \<approx> \<kappa>"
| [AOT_meta_simp]: "AOT_exe (drel F) \<kappa> = \<bottom>((F,\<kappa>))" if "\<not>(\<kappa> \<approx> \<kappa>)"
| [AOT_meta_simp]: "AOT_exe (nullrel F) \<kappa> = \<bottom>((F,\<kappa>))"
  by (metis is_drel_def old.prod.exhaust rel.collapse(2)) auto
termination using "termination" by auto
declare AOT_exe.elims[AOT_meta] AOT_exe.simps[AOT_meta, simp del] AOT_exe.induct[AOT_meta, induct del]
        AOT_exe.cases[AOT_meta] AOT_exe.pelims[AOT_meta] AOT_exe.pinduct[AOT_meta, induct del]
        AOT_exe.psimps[AOT_meta]

nonterminal exe_args
syntax
  AOT_exe :: "<'a::AOT_Term> \<Rightarrow> exe_args \<Rightarrow> 'b" ("\<lparr>_,/ _\<rparr>")
  "" :: "'a::AOT_Term \<Rightarrow> exe_args" ("_")
  Pair :: "'a::AOT_Term \<Rightarrow> exe_args \<Rightarrow> exe_args" ("_,/ _")
translations
  "\<lparr>F, x\<rparr>" \<rightleftharpoons> "CONST AOT_exe F x"

lemma AOT_exeE1[AOT_meta]: "[v \<Turnstile> \<lparr>\<Pi>, \<kappa>\<rparr>] \<Longrightarrow> [v \<Turnstile> \<Pi>\<^bold>\<down>]"
  by (induct "\<Pi>") (auto simp: AOT_meta_simp)
lemma AOT_exeE2[AOT_meta]: "[v \<Turnstile> \<lparr>\<Pi>, \<kappa>\<rparr>] \<Longrightarrow> [v \<Turnstile> \<kappa>\<^bold>\<down>]"
  by (cases "\<kappa> \<approx> \<kappa>"; induct \<Pi>) (auto simp: AOT_meta_simp)
lemma AOT_exeE3[AOT_meta]: "[v \<Turnstile> \<lparr>\<Pi>, \<kappa>\<rparr>] \<Longrightarrow> [v \<Turnstile> (reld \<Pi>) (abs_\<upsilon> \<kappa>)]"
  by (cases "\<kappa> \<approx> \<kappa>"; induct \<Pi>) (auto simp: AOT_meta_simp)


term "\<lparr>F, x\<rparr>"
term "\<lparr>F, x, y\<rparr>"
term "\<lparr>F, x, y, z\<rparr>"

definition AOT_lambda :: "('a::AOT_Term \<Rightarrow> \<o>) \<Rightarrow> <'a>" where
  [AOT_meta]: "AOT_lambda \<equiv> \<lambda> \<phi> .
    if (\<forall> x y v . x \<approx> y \<longrightarrow> [v \<Turnstile> \<phi> x] = [v \<Turnstile> \<phi> y])
    then
      drel (\<lambda> u . \<phi> (rep_\<upsilon> u))
    else
      nullrel (nullrel_choice \<phi>)"

syntax
  AOT_lambda :: "[pttrn, \<o>] \<Rightarrow> <'a::AOT_Term>" ("(3[\<^bold>\<lambda>_/. _])")
translations
  "[\<^bold>\<lambda>x. b]" \<rightleftharpoons> "CONST AOT_lambda (\<lambda> x . b)"

lemma AOT_denoting_lambda_simp[AOT_meta_simp]:
  assumes "\<And> x y v . x \<approx> y \<Longrightarrow> [v \<Turnstile> \<phi> x] = [v \<Turnstile> \<phi> y]"
  shows "[\<^bold>\<lambda>y . \<phi> y] = drel (\<lambda> u . \<phi> (rep_\<upsilon> u))"
  using assms unfolding AOT_lambda_def by auto

definition AOT_lambda0 :: "\<o> \<Rightarrow> \<o>" ("[\<^bold>\<lambda> _]")where
  [AOT_meta, AOT_meta_simp]: "AOT_lambda0 \<equiv> \<lambda> x. x"

lemma AOT_lambda_denotesE[AOT_meta]:
  assumes "[w \<Turnstile> [\<^bold>\<lambda> x. \<phi> x]\<^bold>\<down>]"
  shows "x \<approx> y \<Longrightarrow> [v \<Turnstile> \<phi> x] = [v \<Turnstile> \<phi> y]"
  using assms by (metis AOT_denotesS AOT_lambda_def AOT_equiv_rel.simps(2))
lemma AOT_lambda_denotesI[AOT_meta]:
  assumes "\<And> x y v . x \<approx> y \<Longrightarrow> [v \<Turnstile> \<phi> x] = [v \<Turnstile> \<phi> y]"
  shows "[v \<Turnstile> [\<^bold>\<lambda> x. \<phi> x]\<^bold>\<down>]"
  using assms by (simp add: AOT_lambda_def AOT_meta_simp)

lemma AOT_denoting_lambda_def[AOT_meta]:
  assumes "[w \<Turnstile> [\<^bold>\<lambda> x . \<phi> x]\<^bold>\<down>]"
  shows "[\<^bold>\<lambda> x . \<phi> x] = drel (\<lambda> u . \<phi> (rep_\<upsilon> u))"
  using assms[THEN AOT_lambda_denotesE]
  unfolding AOT_lambda_def by auto

named_theorems AOT_lambda_denotes_intros

lemma AOT_lambda_denotes_propI[AOT_meta, AOT_lambda_denotes_intros]:
  "[v \<Turnstile> [\<^bold>\<lambda>x . \<Theta>]\<^bold>\<down>]"
  by (rule AOT_lambda_denotesI) (auto simp: AOT_meta_simp)
lemma AOT_lambda_denotes_exeI[AOT_meta, AOT_lambda_denotes_intros]:
  "[v \<Turnstile> [\<^bold>\<lambda>x . \<lparr>\<Pi>,x\<rparr>]\<^bold>\<down>]" (* TODO *)
  by (rule AOT_lambda_denotesI; induct \<Pi>; (simp add: AOT_meta_simp)?)
     (metis AOT_exe.simps(1) Quotient_\<upsilon> Quotient_refl1 Quotient_refl2 Quotient_rel_abs)
lemma AOT_lambda_denotes_negI[AOT_meta, AOT_lambda_denotes_intros]:
  assumes "[v \<Turnstile> [\<^bold>\<lambda> x . \<phi> x]\<^bold>\<down>]" shows "[v \<Turnstile> [\<^bold>\<lambda>x . \<^bold>\<not>\<phi> x]\<^bold>\<down>]"
  by (rule AOT_lambda_denotesI) (auto simp: AOT_meta_simp assms[THEN AOT_lambda_denotesE])
lemma AOT_lambda_denotes_boxI[AOT_meta, AOT_lambda_denotes_intros]:
  assumes "[v \<Turnstile> [\<^bold>\<lambda> x . \<phi> x]\<^bold>\<down>]" shows "[v \<Turnstile> [\<^bold>\<lambda>x . \<^bold>\<box>\<phi> x]\<^bold>\<down>]"
  by (rule AOT_lambda_denotesI) (auto simp: AOT_meta_simp assms[THEN AOT_lambda_denotesE])
lemma AOT_lambda_denotes_actI[AOT_meta, AOT_lambda_denotes_intros]:
  assumes "[v \<Turnstile> [\<^bold>\<lambda> x . \<phi> x]\<^bold>\<down>]" shows "[v \<Turnstile> [\<^bold>\<lambda>x . \<^bold>\<A>\<phi> x]\<^bold>\<down>]"
  by (rule AOT_lambda_denotesI) (auto simp: AOT_meta_simp assms[THEN AOT_lambda_denotesE])
lemma AOT_lambda_denotes_diaI[AOT_meta, AOT_lambda_denotes_intros]:
  assumes "[v \<Turnstile> [\<^bold>\<lambda> x . \<phi> x]\<^bold>\<down>]" shows "[v \<Turnstile> [\<^bold>\<lambda>x . \<^bold>\<diamond>\<phi> x]\<^bold>\<down>]"
  by (rule AOT_lambda_denotesI) (auto simp: AOT_meta_simp assms[THEN AOT_lambda_denotesE])
lemma AOT_lambda_denotes_impI[AOT_meta, AOT_lambda_denotes_intros]:
  assumes "[v \<Turnstile> [\<^bold>\<lambda> x . \<phi> x]\<^bold>\<down>]" and "[v \<Turnstile> [\<^bold>\<lambda> x . \<psi> x]\<^bold>\<down>]" shows "[v \<Turnstile> [\<^bold>\<lambda>x . \<phi> x \<^bold>\<rightarrow> \<psi> x]\<^bold>\<down>]"
  by (rule AOT_lambda_denotesI) (auto simp: AOT_meta_simp assms[THEN AOT_lambda_denotesE])
lemma AOT_lambda_denotes_conjI[AOT_meta, AOT_lambda_denotes_intros]:
  assumes "[v \<Turnstile> [\<^bold>\<lambda> x . \<phi> x]\<^bold>\<down>]" and "[v \<Turnstile> [\<^bold>\<lambda> x . \<psi> x]\<^bold>\<down>]" shows "[v \<Turnstile> [\<^bold>\<lambda>x . \<phi> x \<^bold>& \<psi> x]\<^bold>\<down>]"
  by (rule AOT_lambda_denotesI) (auto simp: AOT_meta_simp assms[THEN AOT_lambda_denotesE])
lemma AOT_lambda_denotes_disjI[AOT_meta, AOT_lambda_denotes_intros]:
  assumes "[v \<Turnstile> [\<^bold>\<lambda> x . \<phi> x]\<^bold>\<down>]" and "[v \<Turnstile> [\<^bold>\<lambda> x . \<psi> x]\<^bold>\<down>]" shows "[v \<Turnstile> [\<^bold>\<lambda>x . \<phi> x \<^bold>\<or> \<psi> x]\<^bold>\<down>]"
  by (rule AOT_lambda_denotesI) (auto simp: AOT_meta_simp assms[THEN AOT_lambda_denotesE])
lemma AOT_lambda_denotes_iffI[AOT_meta, AOT_lambda_denotes_intros]:
  assumes "[v \<Turnstile> [\<^bold>\<lambda> x . \<phi> x]\<^bold>\<down>]" and "[v \<Turnstile> [\<^bold>\<lambda> x . \<psi> x]\<^bold>\<down>]" shows "[v \<Turnstile> [\<^bold>\<lambda>x . \<phi> x \<^bold>\<equiv> \<psi> x]\<^bold>\<down>]"
  by (rule AOT_lambda_denotesI) (auto simp: AOT_meta_simp assms[THEN AOT_lambda_denotesE])
lemma AOT_lambda_denotes_allI[AOT_meta, AOT_lambda_denotes_intros]:
  assumes "\<And> y . [v \<Turnstile> y\<^bold>\<down>] \<Longrightarrow> [v \<Turnstile> [\<^bold>\<lambda> x . \<phi> x y]\<^bold>\<down>]" shows  "[v \<Turnstile> [\<^bold>\<lambda> x . \<^bold>\<forall> y. \<phi> x y]\<^bold>\<down>]"
  by (rule AOT_lambda_denotesI) (auto simp: AOT_meta_simp assms[THEN AOT_lambda_denotesE])

lemma AOT_lambda_denotes_prodI[AOT_meta, AOT_lambda_denotes_intros]:
  assumes "\<And> y . [v \<Turnstile> y\<^bold>\<down>] \<Longrightarrow> [v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x y]\<^bold>\<down>]" and "\<And> x . [v \<Turnstile> x\<^bold>\<down>] \<Longrightarrow> [v \<Turnstile> [\<^bold>\<lambda>y. \<phi> x y]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda> (x,y). \<phi> x y]\<^bold>\<down>]"
  apply (simp add: AOT_lambda_def AOT_meta_simp)
  using assms[THEN AOT_lambda_denotesE]
  apply (simp add: AOT_meta_simp)
  by (meson Quotient3_\<upsilon> Quotient3_refl1 Quotient3_refl2)

lemma AOT_abs_\<upsilon>_inverse[AOT_meta]: "[v \<Turnstile> \<kappa>\<^bold>\<down>] \<Longrightarrow> (rep_\<upsilon> (abs_\<upsilon> \<kappa>)) \<approx> \<kappa>"
  by (simp add: AOT_denotesS Quotient3_\<upsilon> rep_abs_rsp_left)

lemma AOT_meta_beta[AOT_meta]:
  assumes "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x]\<^bold>\<down>]"
      and "[v \<Turnstile> \<kappa>\<^bold>\<down>]"
    shows "[v \<Turnstile> \<lparr>[\<^bold>\<lambda>x. \<phi> x], \<kappa>\<rparr>] = [v \<Turnstile> \<phi> \<kappa>]"
  apply (rule)
   apply (drule AOT_exeE3)
  unfolding AOT_denoting_lambda_def[OF assms(1)]
  using AOT_lambda_denotesE[OF assms(1)]
   apply (simp add: AOT_meta_simp) using  AOT_abs_\<upsilon>_inverse[OF assms(2)] apply blast
  apply (cases "\<kappa> \<approx> \<kappa>"; simp add: AOT_meta_simp)
  using AOT_lambda_denotesE[OF assms(1)] AOT_abs_\<upsilon>_inverse[OF assms(2)] apply blast
  using AOT_denotesS assms(2) by auto

lemma AOT_meta_betaE[AOT_meta]: "[v \<Turnstile> \<lparr>[\<^bold>\<lambda>x. \<phi> x], \<kappa>\<rparr>] \<Longrightarrow> [v \<Turnstile> \<phi> \<kappa>]"
  using AOT_meta_beta AOT_exeE1 AOT_exeE2 by blast

term "[\<^bold>\<lambda>x. \<phi> x]"
term "[\<^bold>\<lambda>(x,y). \<phi> x]"
term "[\<^bold>\<lambda>(x,y,z). \<phi> x]"

lemma AOT_meta_equiv_indistinguishable[AOT_meta]:
  "(\<kappa>\<^sub>1 \<approx> \<kappa>\<^sub>2) = ((\<kappa>\<^sub>1 \<approx> \<kappa>\<^sub>1 \<and> \<kappa>\<^sub>2 \<approx> \<kappa>\<^sub>2) \<and> (\<forall> \<Pi> v . [v \<Turnstile> \<Pi>\<^bold>\<down>] \<longrightarrow> [v \<Turnstile> \<lparr>\<Pi>, \<kappa>\<^sub>1\<rparr>] = [v \<Turnstile> \<lparr>\<Pi>, \<kappa>\<^sub>2\<rparr>]))"
proof
  assume equiv: "\<kappa>\<^sub>1 \<approx> \<kappa>\<^sub>2"
  show "(\<kappa>\<^sub>1 \<approx> \<kappa>\<^sub>1 \<and> \<kappa>\<^sub>2 \<approx> \<kappa>\<^sub>2) \<and> (\<forall>\<Pi> v. [v \<Turnstile> \<Pi>\<^bold>\<down>] \<longrightarrow> [v \<Turnstile> \<lparr>\<Pi>, \<kappa>\<^sub>1\<rparr>] = [v \<Turnstile> \<lparr>\<Pi>, \<kappa>\<^sub>2\<rparr>])"
    apply (rule conjI)
    using equiv apply (meson Quotient_\<upsilon> Quotient_rel)
    using equiv AOT_lambda_denotesE AOT_lambda_denotes_exeI by blast
next
  assume assm: "(\<kappa>\<^sub>1 \<approx> \<kappa>\<^sub>1 \<and> \<kappa>\<^sub>2 \<approx> \<kappa>\<^sub>2) \<and> (\<forall>\<Pi> v. [v \<Turnstile> \<Pi>\<^bold>\<down>] \<longrightarrow> [v \<Turnstile> \<lparr>\<Pi>, \<kappa>\<^sub>1\<rparr>] = [v \<Turnstile> \<lparr>\<Pi>, \<kappa>\<^sub>2\<rparr>])"
  have 0: "[dw \<Turnstile> [\<^bold>\<lambda> x . \<epsilon>\<^sub>\<o> v . x \<approx> \<kappa>\<^sub>1]\<^bold>\<down>]"
    by (rule AOT_lambda_denotesI)
       (metis (mono_tags, lifting) AOT_proposition_choice Quotient3_\<upsilon> assm[THEN conjunct1] equals_rsp)
  have "[v \<Turnstile> \<lparr>[\<^bold>\<lambda> x . \<epsilon>\<^sub>\<o> v . x \<approx> \<kappa>\<^sub>1], \<kappa>\<^sub>1\<rparr>] = [v \<Turnstile> \<lparr>[\<^bold>\<lambda> x . \<epsilon>\<^sub>\<o> v . x \<approx> \<kappa>\<^sub>1], \<kappa>\<^sub>2\<rparr>]" for v
    using assm[THEN conjunct2] 0 AOT_exeE1 by blast
  hence "[v \<Turnstile> (\<epsilon>\<^sub>\<o> v . \<kappa>\<^sub>1 \<approx> \<kappa>\<^sub>1)] = [v \<Turnstile> (\<epsilon>\<^sub>\<o> v . \<kappa>\<^sub>2 \<approx> \<kappa>\<^sub>1)]" for v
    using assm[THEN conjunct1] AOT_meta_beta[OF 0] by (simp add: AOT_meta_simp) blast
  thus "\<kappa>\<^sub>1 \<approx> \<kappa>\<^sub>2"
    using assm[THEN conjunct1] by (simp add: AOT_meta_simp AOT_equiv_part_equivp part_equivp_symp)
qed

lemma AOT_meta_equiv_indistinguishableI[AOT_meta]:
  assumes "(\<kappa>\<^sub>1 \<approx> \<kappa>\<^sub>2)" and "\<Pi> \<approx> \<Pi>"
  shows "[v \<Turnstile> \<lparr>\<Pi>, \<kappa>\<^sub>1\<rparr>] = [v \<Turnstile> \<lparr>\<Pi>, \<kappa>\<^sub>2\<rparr>]"
  using assms AOT_meta_equiv_indistinguishable AOT_exeE1 by blast

lemma AOT_meta_eta[AOT_meta]: assumes "\<Pi> \<approx> \<Pi>" shows "[\<^bold>\<lambda> x . \<lparr>\<Pi>, x\<rparr>] = \<Pi>"
proof -
  have "[dw \<Turnstile> [\<^bold>\<lambda> x. \<lparr>\<Pi>, x\<rparr>]\<^bold>\<down>]" by (simp add: AOT_lambda_denotes_exeI)
  then obtain r where lambda_def: "[\<^bold>\<lambda> x. \<lparr>\<Pi>, x\<rparr>] = drel r"
    using AOT_denoting_lambda_def by blast
  hence r_def: "r = (\<lambda>u. \<lparr>\<Pi>, rep_\<upsilon> u\<rparr>)" unfolding AOT_lambda_def
    by (metis rel.inject(1) rel.simps(4))
  obtain r2 where \<Pi>_def: "\<Pi> = drel r2" using assms AOT_equiv_rel.elims(2) by blast
  show "[\<^bold>\<lambda> x . \<lparr>\<Pi>, x\<rparr>] = \<Pi>"
    unfolding lambda_def r_def
    unfolding \<Pi>_def
    by (rule rel.simps(1)[THEN iffD2]; rule ext)
       (metis (full_types) AOT_exe.simps(1) Quotient3_\<upsilon> Quotient3_def)
qed


lemma AOT_lambda_prod1_denotesI[AOT_meta]: "\<Pi> \<approx> \<Pi> \<Longrightarrow> \<nu> \<approx> \<nu> \<Longrightarrow> [\<^bold>\<lambda>\<mu>. \<lparr>\<Pi>, (\<mu>, \<nu>)\<rparr>] \<approx> [\<^bold>\<lambda>\<mu>. \<lparr>\<Pi>, (\<mu>, \<nu>)\<rparr>]"
  by (rule AOT_lambda_denotesI[unfolded AOT_denotesS])
     (metis (no_types, lifting) AOT_equiv_prod_def AOT_exeE1 AOT_lambda_denotesE AOT_meta_eta old.prod.case)
lemma AOT_lambda_prod2_denotesI[AOT_meta]: "\<Pi> \<approx> \<Pi> \<Longrightarrow> \<nu> \<approx> \<nu> \<Longrightarrow> [\<^bold>\<lambda>\<mu>. \<lparr>\<Pi>, (\<nu>, \<mu>)\<rparr>] \<approx> [\<^bold>\<lambda>\<mu>. \<lparr>\<Pi>, (\<nu>, \<mu>)\<rparr>]"
  by (rule AOT_lambda_denotesI[unfolded AOT_denotesS])
     (metis (no_types, lifting) AOT_equiv_prod_def AOT_exeE1 AOT_lambda_denotesE AOT_meta_eta old.prod.case)

lemma AOT_rel_var_induct[AOT_meta]:
  assumes "\<And> F . \<phi> (drel F)"
  shows "\<phi> \<langle>\<Pi>\<rangle>"
  using assms by (metis AOT_equiv_rel.elims(2) AOT_var_equiv)

lemma AOT_lambda_exe_simp[AOT_meta]:
  assumes "\<And> x y . x \<approx> y \<Longrightarrow> A x \<approx> A y"
  shows "[\<^bold>\<lambda>y. \<lparr>drel F, A y\<rparr>] = drel (\<lambda>u. F (abs_\<upsilon> (A (rep_\<upsilon> u))))"
  by (subst AOT_denoting_lambda_simp; (rule AOT_meta_equiv_indistinguishableI)?)
     (auto simp: AOT_equiv_rel.simps(1) AOT_exe.simps(1) assms rep_\<upsilon>)

end
