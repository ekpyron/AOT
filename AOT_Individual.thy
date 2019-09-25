theory AOT_Individual
  imports AOT_Relation
begin

class AOT_Concrete =
  fixes AOT_concrete :: "<'a::AOT_Term>" ("E!")
  assumes AOT_concrete_denotes[AOT_meta, AOT_lambda_denotes_intros]: "[v \<Turnstile> E!\<^bold>\<down>]"

definition (in AOT_Concrete) AOT_ordinary ("O!") where "AOT_ordinary \<equiv> [\<^bold>\<lambda>x. \<^bold>\<diamond>\<lparr>E!,x\<rparr>]"
lemma (in AOT_Concrete) AOT_ordinary_denotes[AOT_meta, AOT_lambda_denotes_intros]: "[v \<Turnstile> O!\<^bold>\<down>]"
  unfolding AOT_ordinary_def by (rule AOT_lambda_denotes_intros)+
definition (in AOT_Concrete) AOT_abstract ("A!") where "AOT_abstract \<equiv> [\<^bold>\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<rparr>]"
lemma (in AOT_Concrete) AOT_abstract_denotes[AOT_meta, AOT_lambda_denotes_intros]: "[v \<Turnstile> A!\<^bold>\<down>]"
  unfolding AOT_abstract_def by (rule AOT_lambda_denotes_intros)+

lemma (in AOT_Concrete)
      AOT_not_abstract_is_ordinary[AOT_meta]: "\<kappa> \<approx> \<kappa> \<Longrightarrow> \<not>[v \<Turnstile> \<lparr>A!, \<kappa>\<rparr>] \<Longrightarrow> [v \<Turnstile> \<lparr>O!, \<kappa>\<rparr>]"
  and AOT_not_ordinary_is_abstract[AOT_meta]: "\<kappa> \<approx> \<kappa> \<Longrightarrow> \<not>[v \<Turnstile> \<lparr>O!, \<kappa>\<rparr>] \<Longrightarrow> [v \<Turnstile> \<lparr>A!, \<kappa>\<rparr>]"
  by (metis AOT_denoting_lambda_def AOT_exe.simps(1) AOT_notS AOT_abstract_def
            AOT_abstract_denotes AOT_ordinary_def AOT_ordinary_denotes)+

lemma (in AOT_Concrete) AOT_not_abstract_and_ordinary: "[v \<Turnstile> \<lparr>A!, \<kappa>\<rparr>] \<Longrightarrow> [v \<Turnstile> \<lparr>O!, \<kappa>\<rparr>] \<Longrightarrow> False"
  by (metis AOT_abstract_def AOT_meta_betaE AOT_notS AOT_ordinary_def)

lemma (in AOT_Concrete) AOT_ordinaryS[AOT_meta]:
  "[v \<Turnstile> \<lparr>O!, \<kappa>\<rparr>] = (\<exists> w . [w \<Turnstile> \<lparr>E!, \<kappa>\<rparr>])"
  unfolding AOT_ordinary_def
  using AOT_meta_beta[of v "\<lambda> \<kappa> . \<^bold>\<diamond>\<lparr>E!, \<kappa>\<rparr>" \<kappa>]
  apply (simp add: AOT_lambda_denotes_intros AOT_diaS AOT_notS AOT_boxS)
  using AOT_denotesS AOT_exeE2 by blast

lemma (in AOT_Concrete) AOT_abstractS[AOT_meta]:
  "[v \<Turnstile> \<lparr>A!, \<kappa>\<rparr>] = (\<forall> w . \<kappa> \<approx> \<kappa> \<and> \<not> [w \<Turnstile> \<lparr>E!, \<kappa>\<rparr>])"
  unfolding AOT_abstract_def
  using AOT_meta_beta[of v "\<lambda> \<kappa> . \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!, \<kappa>\<rparr>" \<kappa>]
  apply (simp add: AOT_lambda_denotes_intros AOT_diaS AOT_notS AOT_boxS)
  using AOT_denotesS AOT_exeE2 by blast

class AOT_Individual = AOT_Term + fixes AOT_meta_enc :: "['a::AOT_Term, 'a \<upsilon> \<Rightarrow> \<o>] \<Rightarrow> bool"
  assumes AOT_universal_encoder[AOT_meta]: "\<exists> \<kappa> . \<kappa> \<approx> \<kappa> \<and> AOT_meta_enc \<kappa> \<phi>"

class AOT_UnaryIndividual = AOT_Concrete + AOT_Individual +
  fixes AOT_that :: "('a::AOT_Term \<Rightarrow> \<o>) \<Rightarrow> 'a" (binder "\<^bold>\<iota>" 8)
  assumes AOT_meta_nocoder[AOT_meta]: "[v \<Turnstile> \<lparr>E!,\<kappa>\<rparr>] \<Longrightarrow> \<not>AOT_meta_enc \<kappa> \<Pi>"
      and AOT_meta_contingently_concrete_object[AOT_meta]: "\<exists> \<kappa> v . \<not>[dw \<Turnstile> \<lparr>E!,\<kappa>\<rparr>] \<and> [v \<Turnstile> \<lparr>E!,\<kappa>\<rparr>]"
      and AOT_meta_A_objects[AOT_meta]: "\<And> \<phi> v . \<exists> \<kappa> :: 'a . [v \<Turnstile> \<lparr>A!,\<kappa>\<rparr>] \<and> (\<forall> F . AOT_meta_enc \<kappa> F \<longleftrightarrow> [v \<Turnstile> \<phi> F])"
      and AOT_meta_descriptions[AOT_meta]: "\<And> \<phi> \<kappa> v . \<kappa> \<approx> \<kappa> \<Longrightarrow> [v \<Turnstile> \<kappa> \<^bold>= (\<^bold>\<iota>x. \<phi> x)] = (\<forall> \<kappa>' . \<kappa>' \<approx> \<kappa>' \<longrightarrow> ([dw \<Turnstile> \<phi> \<kappa>'] = [v \<Turnstile> \<kappa>' \<^bold>= \<kappa>]))"
      and AOT_meta_relation_identity[AOT_meta]: "(F = G) = (\<forall> \<kappa> . \<kappa> \<approx> \<kappa> \<longrightarrow> AOT_meta_enc \<kappa> F = AOT_meta_enc \<kappa> G)"
      and AOT_meta_ordinary_identity[AOT_meta]: "[v \<Turnstile> \<lparr>O!, \<kappa>\<^sub>1\<rparr>] \<Longrightarrow> [v \<Turnstile> \<lparr>O!, \<kappa>\<^sub>2\<rparr>] \<Longrightarrow> (\<kappa>\<^sub>1 \<approx> \<kappa>\<^sub>2) = (\<kappa>\<^sub>1 = \<kappa>\<^sub>2)"
      and AOT_meta_abstract_identity[AOT_meta]: "[v \<Turnstile> \<lparr>A!, \<kappa>\<^sub>1\<rparr>] \<Longrightarrow> [v \<Turnstile> \<lparr>A!, \<kappa>\<^sub>2\<rparr>] \<Longrightarrow> (AOT_meta_enc \<kappa>\<^sub>1 = AOT_meta_enc \<kappa>\<^sub>2) = (\<kappa>\<^sub>1 = \<kappa>\<^sub>2)"
begin
lemma AOT_relation_identity[AOT_meta]:
  assumes "\<Pi> \<approx> \<Pi>"
      and "\<Pi>' \<approx> \<Pi>'"
      and "\<forall> \<nu> :: 'a . \<nu> \<approx> \<nu> \<longrightarrow> (\<Pi> \<approx> \<Pi> \<and> AOT_meta_enc \<nu> (reld \<Pi>)) = (\<Pi>' \<approx> \<Pi>' \<and> AOT_meta_enc \<nu> (reld \<Pi>'))"
  shows "\<Pi> = \<Pi>'"
  using assms AOT_meta_relation_identity[of "reld \<Pi>" "reld \<Pi>'"]
  by (metis AOT_equiv_rel.elims(2) rel.sel(1))
end

instantiation prod :: (AOT_UnaryIndividual, AOT_Individual) AOT_Individual
begin
definition AOT_meta_enc_prod :: "['a\<times>'b, ('a\<times>'b) \<upsilon> \<Rightarrow> \<o>] \<Rightarrow> bool" where
  "AOT_meta_enc_prod \<equiv> \<lambda>(\<kappa>\<^sub>1, \<kappa>\<^sub>2) \<phi>. AOT_meta_enc \<kappa>\<^sub>1 (\<lambda> u . \<phi> (abs_\<upsilon> (rep_\<upsilon> u, \<kappa>\<^sub>2))) \<and> AOT_meta_enc \<kappa>\<^sub>2 (\<lambda> u . \<phi> (abs_\<upsilon> (\<kappa>\<^sub>1, rep_\<upsilon> u)))"

instance proof
  fix \<phi> :: "('a\<times>'b) \<upsilon> \<Rightarrow> \<o>"
  obtain \<kappa>\<^sub>1 where "\<kappa>\<^sub>1 \<approx> \<kappa>\<^sub>1" and "\<forall> \<kappa>\<^sub>2 . \<kappa>\<^sub>2 \<approx> \<kappa>\<^sub>2 \<longrightarrow> AOT_meta_enc \<kappa>\<^sub>1 (\<lambda>u. \<phi> (abs_\<upsilon> (rep_\<upsilon> u, \<kappa>\<^sub>2)))"
    using AOT_meta_A_objects[of dw "\<lambda> F . \<epsilon>\<^sub>\<o> v . \<exists> \<kappa>\<^sub>2 . F = (\<lambda>u. \<phi> (abs_\<upsilon> (rep_\<upsilon> u, \<kappa>\<^sub>2)))"]
          AOT_denotesS AOT_exeE2 
    by (simp add: AOT_meta_simp) blast
  moreover obtain \<kappa>\<^sub>2 where "\<kappa>\<^sub>2 \<approx> \<kappa>\<^sub>2" and "AOT_meta_enc \<kappa>\<^sub>2 (\<lambda>u. \<phi> (abs_\<upsilon> (\<kappa>\<^sub>1, rep_\<upsilon> u)))"
    using AOT_universal_encoder by blast
  ultimately show "\<exists> \<kappa> . \<kappa> \<approx> \<kappa> \<and> AOT_meta_enc \<kappa> \<phi>"
    by (rule_tac x="(\<kappa>\<^sub>1, \<kappa>\<^sub>2)" in exI) (simp add: AOT_equiv_prod_def AOT_meta_enc_prod_def)
qed
end

definition (in AOT_Individual) AOT_enc where
  [AOT_meta]: "AOT_enc \<equiv> SOME \<phi> . \<forall> v \<kappa> \<Pi> . [v \<Turnstile> \<phi> \<kappa> \<Pi>] = (\<Pi> \<approx> \<Pi> \<and> \<kappa> \<approx> \<kappa> \<and> AOT_meta_enc \<kappa> (reld \<Pi>))"

nonterminal enc_args
syntax
  AOT_enc :: "[enc_args, 'a::AOT_Individual \<Rightarrow> \<o>] \<Rightarrow> \<o>" ("\<lbrace>_,/ _\<rbrace>")
  "" :: "'a::AOT_Term \<Rightarrow> enc_args" ("_")
  Pair :: "['a::AOT_Term, enc_args] \<Rightarrow> enc_args" ("_,/ _")
translations
  "\<lbrace>x, F\<rbrace>" \<rightleftharpoons> "CONST AOT_enc x F"

lemma (in AOT_Individual) AOT_enc_metaS[AOT_meta, AOT_meta_simp]:
  "[v \<Turnstile> \<lbrace>\<kappa>, \<Pi>\<rbrace>] = (\<Pi> \<approx> \<Pi> \<and> \<kappa> \<approx> \<kappa> \<and> AOT_meta_enc \<kappa> (reld \<Pi>))"
proof -
  have 0: "\<exists> \<phi> . \<forall> v \<kappa> \<Pi> . [v \<Turnstile> \<phi> \<kappa> \<Pi>] = (\<Pi> \<approx> \<Pi> \<and> \<kappa> \<approx> \<kappa> \<and> AOT_meta_enc \<kappa> (reld \<Pi>))"
    by (rule_tac x="\<lambda> \<kappa> \<Pi> . \<epsilon>\<^sub>\<o> v . \<Pi> \<approx> \<Pi> \<and> \<kappa> \<approx> \<kappa> \<and> AOT_meta_enc \<kappa> (reld \<Pi>)" in exI) (simp add: AOT_meta_simp)
  show ?thesis using someI_ex[OF 0] unfolding AOT_enc_def by auto
qed

lemma (in AOT_UnaryIndividual) AOT_nocoder[AOT_meta]: "[v \<Turnstile> \<lparr>E!,\<kappa>\<rparr>] \<Longrightarrow> \<not>[w \<Turnstile> \<lbrace>\<kappa>, \<Pi>\<rbrace>]"
  by (simp add: AOT_enc_metaS AOT_meta_nocoder)

lemma (in AOT_UnaryIndividual) AOT_A_objects[AOT_meta]:
  "\<exists> \<kappa> . [v \<Turnstile> \<lparr>A!,\<kappa>\<rparr>] \<and> (\<forall> \<Pi> . \<Pi> \<approx> \<Pi> \<longrightarrow> [v \<Turnstile> \<lbrace>\<kappa>, \<Pi>\<rbrace>] \<longleftrightarrow> [v \<Turnstile> \<phi> \<Pi>])"
proof -
  obtain \<kappa> where \<kappa>_prop: "[v \<Turnstile> \<lparr>A!, \<kappa>\<rparr>] \<and> (\<forall>F. AOT_meta_enc \<kappa> F = [v \<Turnstile> \<phi> (drel F)])"
    using AOT_meta_A_objects by force
  thus ?thesis
    by (rule_tac x=\<kappa> in exI; simp add: AOT_meta_simp)
       (metis AOT_denotesS AOT_equiv_rel.simps(2) AOT_exeE2 rel.exhaust_sel)
qed

lemma AOT_projection_identity:
  assumes "\<Pi> \<approx> \<Pi>" and "\<Pi>' \<approx> \<Pi>'" and "\<And> \<kappa> . \<kappa> \<approx> \<kappa> \<longrightarrow> [\<^bold>\<lambda> x . \<lparr>\<Pi>,x,\<kappa>\<rparr>] = [\<^bold>\<lambda> x . \<lparr>\<Pi>',x,\<kappa>\<rparr>]"
  shows "\<Pi> = \<Pi>'"
proof -
  obtain F where \<Pi>_def: "\<Pi> = drel F" using assms(1) AOT_equiv_rel.elims(2) by blast
  obtain G where \<Pi>'_def: "\<Pi>' = drel G" using assms(2) AOT_equiv_rel.elims(2) by blast
  {
    fix u :: "('a \<times> 'b) \<upsilon>"
    obtain \<kappa> where \<kappa>_prop: "\<kappa> \<approx> \<kappa> \<and> u = abs_\<upsilon> \<kappa>" by (metis Quotient3_\<upsilon> Quotient3_def)
    have fst_\<kappa>_denotes: "fst \<kappa> \<approx> fst \<kappa>" and snd_\<kappa>_denotes: "snd \<kappa> \<approx> snd \<kappa>"
      using \<kappa>_prop by (induct \<kappa>) (auto simp: AOT_equiv_prod_def)
    hence "\<forall>x y v. x \<approx> y \<longrightarrow> [v \<Turnstile> \<lparr>drel F, (x, snd \<kappa>)\<rparr>] = [v \<Turnstile> \<lparr>drel F, (y, snd \<kappa>)\<rparr>]"
      and "\<forall>x y v. x \<approx> y \<longrightarrow> [v \<Turnstile> \<lparr>drel G, (x, snd \<kappa>)\<rparr>] = [v \<Turnstile> \<lparr>drel G, (y, snd \<kappa>)\<rparr>]"
      by (metis (no_types, lifting) AOT_equiv_prod_def AOT_equiv_rel.simps(1) AOT_exeE1
                                    AOT_lambda_denotesE AOT_meta_eta old.prod.case)+
    moreover have "[\<^bold>\<lambda> x . \<lparr>\<Pi>,x,snd \<kappa>\<rparr>] = [\<^bold>\<lambda> x . \<lparr>\<Pi>',x,snd \<kappa>\<rparr>]"
      using assms(3) snd_\<kappa>_denotes unfolding AOT_equiv_prod_def by (induct \<kappa>) auto
    ultimately have "drel (\<lambda>u. \<lparr>drel F, (rep_\<upsilon> u, snd \<kappa>)\<rparr>) = drel (\<lambda>u. \<lparr>drel G, (rep_\<upsilon> u, snd \<kappa>)\<rparr>)"
      unfolding \<Pi>_def \<Pi>'_def AOT_lambda_def by simp
    hence "\<lparr>drel F, (rep_\<upsilon> (abs_\<upsilon> (fst \<kappa>)), snd \<kappa>)\<rparr> = \<lparr>drel G, (rep_\<upsilon> (abs_\<upsilon> (fst \<kappa>)), snd \<kappa>)\<rparr>"
      by (metis rel.inject(1))
    moreover have "rep_\<upsilon> (abs_\<upsilon> (fst \<kappa>)) \<approx> fst \<kappa>"
      by (simp add: AOT_abs_\<upsilon>_inverse AOT_denotesS fst_\<kappa>_denotes)
    moreover have "(rep_\<upsilon> (abs_\<upsilon> (fst \<kappa>)), snd \<kappa>) \<approx> (fst \<kappa>, snd \<kappa>)"
      using calculation snd_\<kappa>_denotes unfolding AOT_equiv_prod_def by blast
    moreover have "(abs_\<upsilon> (rep_\<upsilon> (abs_\<upsilon> (fst \<kappa>)), snd \<kappa>)) = (abs_\<upsilon> (fst \<kappa>, snd \<kappa>))"
      using calculation Quotient3_rel_abs[OF Quotient3_\<upsilon>] by blast
    moreover have "(rep_\<upsilon> (abs_\<upsilon> (fst \<kappa>)), snd \<kappa>) \<approx> (rep_\<upsilon> (abs_\<upsilon> (fst \<kappa>)), snd \<kappa>)"
      using calculation by (metis (full_types) Quotient3_\<upsilon> Quotient3_def)
    ultimately have "F (abs_\<upsilon> (fst \<kappa>, snd \<kappa>)) = G (abs_\<upsilon> (fst \<kappa>, snd \<kappa>))"
      using AOT_exe.simps(1) by metis
    hence "F u = G u" using \<kappa>_prop by auto
  }
  hence "F = G" by blast
  thus "\<Pi> = \<Pi>'" unfolding \<Pi>_def \<Pi>'_def by blast
qed

lemma AOT_meta_enc_eqI[AOT_meta]:
  assumes "\<And> \<Omega>. \<Omega> \<approx> \<Omega> \<Longrightarrow> (\<kappa> \<approx> \<kappa> \<and> AOT_meta_enc \<kappa> (reld \<Omega>)) = (\<kappa>' \<approx> \<kappa>' \<and> AOT_meta_enc \<kappa>' (reld \<Omega>))"
      and "[v \<Turnstile> \<lparr>A!, \<kappa>\<rparr>]" and "[v \<Turnstile> \<lparr>A!, \<kappa>'\<rparr>]"
  shows "AOT_meta_enc \<kappa> = AOT_meta_enc \<kappa>'"
proof
  fix \<phi> :: "'a \<upsilon> \<Rightarrow> \<o>"
  obtain \<Omega> where "\<Omega> \<approx> \<Omega>" and \<phi>_def: "reld \<Omega> = \<phi>" using AOT_equiv_rel.simps(1) rel.sel(1) by blast
  hence "(\<kappa> \<approx> \<kappa> \<and> AOT_meta_enc \<kappa> (reld \<Omega>)) = (\<kappa>' \<approx> \<kappa>' \<and> AOT_meta_enc \<kappa>' (reld \<Omega>))"
    using assms by blast
  thus "AOT_meta_enc \<kappa> \<phi> = AOT_meta_enc \<kappa>' \<phi>"
    unfolding \<phi>_def[symmetric]
    using AOT_denotesS AOT_exeE2 assms(2) assms(3) by blast
qed

end
