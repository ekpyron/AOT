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


class AOT_Individual = AOT_Term + fixes AOT_enc :: "['a::AOT_Term, <'a>] \<Rightarrow> \<o>" ("\<lbrace>_,_\<rbrace>")
  assumes AOT_meta_enc_denotes[AOT_meta]: "[v \<Turnstile> \<lbrace>\<kappa>, \<Pi>\<rbrace>] \<Longrightarrow> \<kappa> \<approx> \<kappa> \<and> \<Pi> \<approx> \<Pi>"
      and AOT_meta_enc_nec[AOT_meta]: "[v \<Turnstile> \<lbrace>\<kappa>, \<Pi>\<rbrace>] \<Longrightarrow> [w \<Turnstile> \<lbrace>\<kappa>, \<Pi>\<rbrace>]"
      and AOT_universal_encoder[AOT_meta]: "\<Pi> \<approx> \<Pi> \<Longrightarrow> \<exists> \<kappa> . [v \<Turnstile> \<lbrace>\<kappa>, \<Pi>\<rbrace>]"

no_notation AOT_enc ("\<lbrace>_,_\<rbrace>")
nonterminal enc_args
syntax
  AOT_enc :: "[enc_args, 'a::AOT_Individual \<Rightarrow> \<o>] \<Rightarrow> \<o>" ("\<lbrace>_,/ _\<rbrace>")
  "" :: "'a::AOT_Term \<Rightarrow> enc_args" ("_")
  Pair :: "['a::AOT_Term, enc_args] \<Rightarrow> enc_args" ("_,/ _")
translations
  "\<lbrace>x, F\<rbrace>" \<rightleftharpoons> "CONST AOT_enc x F"

class AOT_UnaryIndividual = AOT_Concrete + AOT_Individual +
  fixes AOT_that :: "('a::AOT_Term \<Rightarrow> \<o>) \<Rightarrow> 'a" (binder "\<^bold>\<iota>" 8)
  assumes AOT_meta_nocoder[AOT_meta]: "\<kappa> \<approx> \<kappa> \<Longrightarrow> [w \<Turnstile> \<lparr>E!,\<kappa>\<rparr>] \<Longrightarrow> \<not>[v \<Turnstile> \<lbrace>\<kappa>, \<Pi>\<rbrace>]"
      and AOT_meta_contingently_concrete_object[AOT_meta]: "\<exists> \<kappa> v . \<not>[dw \<Turnstile> \<lparr>E!,\<kappa>\<rparr>] \<and> [v \<Turnstile> \<lparr>E!,\<kappa>\<rparr>]"
      and AOT_meta_A_objects[AOT_meta]: "\<And> \<phi> v . \<exists> \<kappa> :: 'a . [v \<Turnstile> \<lparr>A!,\<kappa>\<rparr>] \<and> (\<forall> F . F \<approx> F \<longrightarrow> ([v \<Turnstile> \<lbrace>\<kappa>, F\<rbrace>] \<longleftrightarrow> [v \<Turnstile> \<phi> F]))"
      and AOT_meta_descriptions[AOT_meta]: "\<And> \<phi> \<kappa> v . \<kappa> \<approx> \<kappa> \<Longrightarrow> [v \<Turnstile> \<kappa> \<^bold>= (\<^bold>\<iota>x. \<phi> x)] = (\<forall> \<kappa>' . \<kappa>' \<approx> \<kappa>' \<longrightarrow> ([dw \<Turnstile> \<phi> \<kappa>'] = [v \<Turnstile> \<kappa>' \<^bold>= \<kappa>]))"
      and AOT_meta_relation_identity[AOT_meta]: "\<Pi> \<approx> \<Pi> \<Longrightarrow> \<Pi>' \<approx> \<Pi>' \<Longrightarrow> (\<Pi> = \<Pi>') = (\<forall> \<kappa> v . \<kappa> \<approx> \<kappa> \<longrightarrow> [v \<Turnstile> \<lbrace>\<kappa>, \<Pi>\<rbrace>] = [v \<Turnstile> \<lbrace>\<kappa>, \<Pi>'\<rbrace>])"
      and AOT_meta_ordinary_identity[AOT_meta]: "[v \<Turnstile> \<lparr>O!, \<kappa>\<^sub>1\<rparr>] \<Longrightarrow> [v \<Turnstile> \<lparr>O!, \<kappa>\<^sub>2\<rparr>] \<Longrightarrow> (\<kappa>\<^sub>1 \<approx> \<kappa>\<^sub>2) = (\<kappa>\<^sub>1 = \<kappa>\<^sub>2)"
      and AOT_meta_abstract_identity[AOT_meta]: "[v \<Turnstile> \<lparr>A!, \<kappa>\<^sub>1\<rparr>] \<Longrightarrow> [v \<Turnstile> \<lparr>A!, \<kappa>\<^sub>2\<rparr>] \<Longrightarrow> (\<forall> \<Pi> v . [v \<Turnstile> \<lbrace>\<kappa>\<^sub>1,drel \<Pi>\<rbrace>] = [v \<Turnstile> \<lbrace>\<kappa>\<^sub>2,drel \<Pi>\<rbrace>]) = (\<kappa>\<^sub>1 = \<kappa>\<^sub>2)"

instantiation prod :: (AOT_UnaryIndividual, AOT_Individual) AOT_Individual
begin
definition AOT_enc_prod :: "['a\<times>'b, <'a\<times>'b>] \<Rightarrow> \<o>" where
  [AOT_meta]: "AOT_enc_prod \<equiv> SOME \<phi> . \<forall> v \<kappa> \<Pi> . [v \<Turnstile> \<phi> \<kappa> \<Pi>] =
    ([v \<Turnstile> \<Pi>\<^bold>\<down>] \<and> [v \<Turnstile> \<lbrace>fst \<kappa>, [\<^bold>\<lambda>y. \<lparr>\<Pi>,y,snd \<kappa>\<rparr>]\<rbrace>] \<and> [v \<Turnstile> \<lbrace>snd \<kappa>, [\<^bold>\<lambda>y. \<lparr>\<Pi>,fst \<kappa>, y\<rparr>]\<rbrace>])"
lemma AOT_enc_prodS[AOT_meta, AOT_meta_simp]:
  "[v \<Turnstile> \<lbrace>\<kappa>::'a\<times>'b, \<Pi>\<rbrace>] = ([v \<Turnstile> \<Pi>\<^bold>\<down>] \<and> [v \<Turnstile> \<lbrace>fst \<kappa>, [\<^bold>\<lambda>y. \<lparr>\<Pi>, y, snd \<kappa>\<rparr>]\<rbrace>] \<and> [v \<Turnstile> \<lbrace>snd \<kappa>, [\<^bold>\<lambda>y. \<lparr>\<Pi>, fst \<kappa>, y\<rparr>]\<rbrace>])"
  (is "(?LHS v \<kappa> \<Pi>) = (?RHS v \<kappa> \<Pi>)")
proof -
  have 0: "\<exists> \<phi> . \<forall> v \<kappa> \<Pi> . [v \<Turnstile> \<phi> \<kappa> \<Pi>] = (?RHS v \<kappa> \<Pi>)"
    by (rule_tac x="\<lambda> \<kappa> \<Pi> . \<epsilon>\<^sub>\<o> v . (?RHS v \<kappa> \<Pi>)" in exI)
       (auto simp: AOT_meta_simp)
  show ?thesis using someI_ex[OF 0] unfolding AOT_enc_prod_def by blast
qed
instance proof
  fix v :: i and \<kappa> :: "'a\<times>'b" and \<Pi> :: "<'a\<times>'b>"
  assume "[v \<Turnstile> \<lbrace>\<kappa>, \<Pi>\<rbrace>]"
  hence "[v \<Turnstile> \<Pi>\<^bold>\<down>]" and "[v \<Turnstile> \<lbrace>fst \<kappa>, [\<^bold>\<lambda>y . \<lparr>\<Pi>, y, snd \<kappa>\<rparr>]\<rbrace>]" and "[v \<Turnstile> \<lbrace>snd \<kappa>, [\<^bold>\<lambda>y . \<lparr>\<Pi>, fst \<kappa>, y\<rparr>]\<rbrace>]"
    by (auto simp: AOT_meta_simp)
  hence "\<Pi> \<approx> \<Pi>" and "fst \<kappa> \<approx> fst \<kappa>" and "snd \<kappa> \<approx> snd \<kappa>"
    using AOT_denotesS AOT_meta_enc_denotes by blast+
  thus "\<kappa> \<approx> \<kappa> \<and> \<Pi> \<approx> \<Pi>"
    unfolding AOT_equiv_prod_def by (induct \<kappa>) auto
next
  fix v w :: i and \<kappa> :: "'a\<times>'b" and \<Pi> :: "<'a\<times>'b>"
  assume "[v \<Turnstile> \<lbrace>\<kappa>, \<Pi>\<rbrace>]"
  hence "[v \<Turnstile> \<Pi>\<^bold>\<down>]" and "[v \<Turnstile> \<lbrace>fst \<kappa>, [\<^bold>\<lambda>y . \<lparr>\<Pi>, y, snd \<kappa>\<rparr>]\<rbrace>]" and "[v \<Turnstile> \<lbrace>snd \<kappa>, [\<^bold>\<lambda>y . \<lparr>\<Pi>, fst \<kappa>, y\<rparr>]\<rbrace>]"
    by (auto simp: AOT_meta_simp)
  hence "[w \<Turnstile> \<Pi>\<^bold>\<down>]" and "[w \<Turnstile> \<lbrace>fst \<kappa>, [\<^bold>\<lambda>y . \<lparr>\<Pi>, y, snd \<kappa>\<rparr>]\<rbrace>]" and "[w \<Turnstile> \<lbrace>snd \<kappa>, [\<^bold>\<lambda>y . \<lparr>\<Pi>, fst \<kappa>, y\<rparr>]\<rbrace>]"
    using AOT_denotesS AOT_meta_enc_nec by blast+
  thus "[w \<Turnstile> \<lbrace>\<kappa>, \<Pi>\<rbrace>]"
    by (auto simp: AOT_meta_simp)
next
  fix \<Pi> :: "<'a\<times>'b>" and v :: i
  assume \<Pi>_denotes: "\<Pi> \<approx> \<Pi>"
  {
    fix \<kappa>\<^sub>2 :: 'b
    assume \<kappa>\<^sub>2_denotes: "\<kappa>\<^sub>2 \<approx> \<kappa>\<^sub>2"
    {
      fix x y :: 'a and v :: i
      assume "x \<approx> y"
      hence "(x, \<kappa>\<^sub>2) \<approx> (y, \<kappa>\<^sub>2)" by (simp add: AOT_equiv_prod_def \<kappa>\<^sub>2_denotes)
      hence "[v \<Turnstile> \<lparr>\<Pi>, (x, \<kappa>\<^sub>2)\<rparr>] = [v \<Turnstile> \<lparr>\<Pi>, (y, \<kappa>\<^sub>2)\<rparr>]"
        using AOT_lambda_denotesE AOT_lambda_denotes_exeI by blast
    }
    hence "[\<^bold>\<lambda>y . \<lparr>\<Pi>, y, \<kappa>\<^sub>2\<rparr>] \<approx> [\<^bold>\<lambda>y . \<lparr>\<Pi>, y, \<kappa>\<^sub>2\<rparr>]"
      apply - by (rule AOT_denotesS[THEN iffD1]; rule AOT_lambda_denotesI) blast
  }
  then obtain \<kappa>\<^sub>1 :: 'a where \<kappa>\<^sub>1_prop: "\<And> \<kappa>\<^sub>2 . \<kappa>\<^sub>2 \<approx> \<kappa>\<^sub>2 \<Longrightarrow> [v \<Turnstile> \<lbrace>\<kappa>\<^sub>1, [\<^bold>\<lambda>y . \<lparr>\<Pi>,y,\<kappa>\<^sub>2\<rparr>]\<rbrace>]"
    using AOT_meta_A_objects by (metis AOT_denotesS)
  hence \<kappa>\<^sub>1_denotes: "\<kappa>\<^sub>1 \<approx> \<kappa>\<^sub>1" using AOT_meta_enc_denotes AOT_var_equiv by blast
  {
    {
      fix x y :: 'b and v :: i
      assume "x \<approx> y"
      hence "(\<kappa>\<^sub>1, x) \<approx> (\<kappa>\<^sub>1, y)" using \<kappa>\<^sub>1_denotes by (simp add: AOT_equiv_prod_def)
      hence "[v \<Turnstile> \<lparr>\<Pi>, (\<kappa>\<^sub>1, x)\<rparr>] = [v \<Turnstile> \<lparr>\<Pi>, (\<kappa>\<^sub>1, y)\<rparr>]"
        using AOT_lambda_denotesE AOT_lambda_denotes_exeI by blast
    } note 2 = this
    hence "[\<^bold>\<lambda>y . \<lparr>\<Pi>, \<kappa>\<^sub>1, y\<rparr>] \<approx> [\<^bold>\<lambda>y . \<lparr>\<Pi>, \<kappa>\<^sub>1, y\<rparr>]"
      apply - by (rule AOT_denotesS[THEN iffD1]; rule AOT_lambda_denotesI) blast
  }
  then obtain \<kappa>\<^sub>2 :: 'b where \<kappa>\<^sub>2_prop: "[v \<Turnstile> \<lbrace>\<kappa>\<^sub>2, [\<^bold>\<lambda>y . \<lparr>\<Pi>, \<kappa>\<^sub>1, y\<rparr>]\<rbrace>]"
    using AOT_universal_encoder by blast
  hence \<kappa>\<^sub>2_denotes: "\<kappa>\<^sub>2 \<approx> \<kappa>\<^sub>2"
    using AOT_meta_enc_denotes by blast

  thus "\<exists>\<kappa>. [v \<Turnstile> \<lbrace>\<kappa>, \<Pi>\<rbrace>]"
    by (rule_tac x="(\<kappa>\<^sub>1, \<kappa>\<^sub>2)" in exI)
       (auto simp: AOT_enc_prodS \<kappa>\<^sub>1_prop[OF \<kappa>\<^sub>2_denotes] \<kappa>\<^sub>2_prop \<Pi>_denotes AOT_denotesS)
qed
end

lemma AOT_projection_identity1:
  assumes "\<Pi> \<approx> \<Pi>" and "\<Pi>' \<approx> \<Pi>'" and "\<And> \<kappa> . \<kappa> \<approx> \<kappa> \<Longrightarrow> [\<^bold>\<lambda> x . \<lparr>\<Pi>,x,\<kappa>\<rparr>] = [\<^bold>\<lambda> x . \<lparr>\<Pi>',x,\<kappa>\<rparr>]"
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
      using assms(3)[OF snd_\<kappa>_denotes] unfolding AOT_equiv_prod_def by (induct \<kappa>) auto
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

lemma AOT_projection_identity2:
  assumes "\<Pi> \<approx> \<Pi>" and "\<Pi>' \<approx> \<Pi>'" and "\<And> \<kappa> . \<kappa> \<approx> \<kappa> \<Longrightarrow> [\<^bold>\<lambda> x . \<lparr>\<Pi>, \<kappa>, x\<rparr>] = [\<^bold>\<lambda> x . \<lparr>\<Pi>', \<kappa>, x\<rparr>]"
  shows "\<Pi> = \<Pi>'"
proof -
  obtain F where \<Pi>_def: "\<Pi> = drel F" using assms(1) AOT_equiv_rel.elims(2) by blast
  obtain G where \<Pi>'_def: "\<Pi>' = drel G" using assms(2) AOT_equiv_rel.elims(2) by blast
  {
    fix u :: "('a \<times> 'b) \<upsilon>"
    obtain \<kappa> where \<kappa>_prop: "\<kappa> \<approx> \<kappa> \<and> u = abs_\<upsilon> \<kappa>" by (metis Quotient3_\<upsilon> Quotient3_def)
    have fst_\<kappa>_denotes: "fst \<kappa> \<approx> fst \<kappa>" and snd_\<kappa>_denotes: "snd \<kappa> \<approx> snd \<kappa>"
      using \<kappa>_prop by (induct \<kappa>) (auto simp: AOT_equiv_prod_def)
    hence "\<forall>x y v. x \<approx> y \<longrightarrow> [v \<Turnstile> \<lparr>drel F, (fst \<kappa>, x)\<rparr>] = [v \<Turnstile> \<lparr>drel F, (fst \<kappa>, y)\<rparr>]"
      and "\<forall>x y v. x \<approx> y \<longrightarrow> [v \<Turnstile> \<lparr>drel G, (fst \<kappa>, x)\<rparr>] = [v \<Turnstile> \<lparr>drel G, (fst \<kappa>, y)\<rparr>]"
      by (metis (no_types, lifting) AOT_equiv_prod_def AOT_equiv_rel.simps(1) AOT_exeE1
                                    AOT_lambda_denotesE AOT_meta_eta old.prod.case)+
    moreover have "[\<^bold>\<lambda> x . \<lparr>\<Pi>,fst \<kappa>, x\<rparr>] = [\<^bold>\<lambda> x . \<lparr>\<Pi>',fst \<kappa>, x\<rparr>]"
      using assms(3)[OF fst_\<kappa>_denotes] unfolding AOT_equiv_prod_def by (induct \<kappa>) auto
    ultimately have "drel (\<lambda>u. \<lparr>drel F, (fst \<kappa>, rep_\<upsilon> u)\<rparr>) = drel (\<lambda>u. \<lparr>drel G, (fst \<kappa>, rep_\<upsilon> u)\<rparr>)"
      unfolding \<Pi>_def \<Pi>'_def AOT_lambda_def by simp
    hence "\<lparr>drel F, (fst \<kappa>, rep_\<upsilon> (abs_\<upsilon> (snd \<kappa>)))\<rparr> = \<lparr>drel G, (fst \<kappa>, rep_\<upsilon> (abs_\<upsilon> (snd \<kappa>)))\<rparr>"
      by (metis rel.inject(1))
    moreover have "rep_\<upsilon> (abs_\<upsilon> (snd \<kappa>)) \<approx> snd \<kappa>"
      by (simp add: AOT_abs_\<upsilon>_inverse AOT_denotesS snd_\<kappa>_denotes)
    moreover have "(fst \<kappa>, rep_\<upsilon> (abs_\<upsilon> (snd \<kappa>))) \<approx> (fst \<kappa>, snd \<kappa>)"
      using calculation fst_\<kappa>_denotes unfolding AOT_equiv_prod_def by blast
    moreover have "(abs_\<upsilon> (fst \<kappa>, rep_\<upsilon> (abs_\<upsilon> (snd \<kappa>)))) = (abs_\<upsilon> (fst \<kappa>, snd \<kappa>))"
      using calculation Quotient3_rel_abs[OF Quotient3_\<upsilon>] by blast
    moreover have "(fst \<kappa>, rep_\<upsilon> (abs_\<upsilon> (snd \<kappa>))) \<approx> (fst \<kappa>, rep_\<upsilon> (abs_\<upsilon> (snd \<kappa>)))"
      using calculation by (metis (full_types) Quotient3_\<upsilon> Quotient3_def)
    ultimately have "F (abs_\<upsilon> (fst \<kappa>, snd \<kappa>)) = G (abs_\<upsilon> (fst \<kappa>, snd \<kappa>))"
      using AOT_exe.simps(1) by metis
    hence "F u = G u" using \<kappa>_prop by auto
  }
  thus "\<Pi> = \<Pi>'" unfolding \<Pi>_def \<Pi>'_def by blast
qed

end
