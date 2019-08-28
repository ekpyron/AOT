theory AOT_Individual
  imports AOT_Relation
begin

class AOT_Individual = AOT_Term +
  fixes AOT_enc :: "'a::AOT_Term \<Rightarrow> <'a> \<Rightarrow> \<o>"
    and AOT_universal_encoder :: 'a
    and AOT_relation_identity :: "<'a> \<Rightarrow> <'a> \<Rightarrow> \<o>" (infixl "\<^bold>=\<^sub>r" 63)
    and AOT_proj_enc :: "'a \<Rightarrow> ('a\<Rightarrow>\<o>) \<Rightarrow> \<o>"
  assumes AOT_universal_encoder_exists: "[v \<Turnstile> AOT_universal_encoder\<^bold>\<down>]"
      and AOT_universal_encoder: "[v \<Turnstile> F\<^bold>\<down>] \<Longrightarrow> [v \<Turnstile> AOT_enc AOT_universal_encoder F]"
      and AOT_relation_identity: "[v \<Turnstile> F \<^bold>=\<^sub>r G] = ([v \<Turnstile> F\<^bold>\<down>] \<and> [v \<Turnstile> G\<^bold>\<down>] \<and> F = G)"
      and AOT_enc_rigid: "[v \<Turnstile> AOT_enc x F] = (\<forall> v . [v \<Turnstile> AOT_enc x F])"
      and AOT_enc_impl_exists: "[v \<Turnstile> AOT_enc x F] \<Longrightarrow> [v \<Turnstile> x\<^bold>\<down>] \<and> [v \<Turnstile> F\<^bold>\<down>]"
      and AOT_proj_enc_universal: "(\<And> v x y . [v \<Turnstile> x \<^bold>~ y] \<Longrightarrow> [v \<Turnstile> \<phi> x] = [v \<Turnstile> \<phi> y]) \<Longrightarrow> [v \<Turnstile> AOT_proj_enc AOT_universal_encoder \<phi>]"
      and AOT_proj_enc_nec: "[v \<Turnstile> AOT_proj_enc x \<phi>] \<Longrightarrow> (\<And> v . [v \<Turnstile> AOT_proj_enc x \<phi>])"
      and AOT_proj_enc_impl_ex: "[v \<Turnstile> AOT_proj_enc x \<phi>] \<Longrightarrow> [v \<Turnstile> x\<^bold>\<down>]"

nonterminal enc_args
syntax
  AOT_enc :: "enc_args \<Rightarrow> ('a::AOT_Individual\<Rightarrow>\<o>) \<Rightarrow> \<o>" ("\<lbrace>_,/ _\<rbrace>")
  "" :: "'a::AOT_Term \<Rightarrow> enc_args" ("_")
  Pair :: "'a::AOT_Term \<Rightarrow> enc_args \<Rightarrow> enc_args" ("_,/ _")
translations
  "\<lbrace>x, F\<rbrace>" \<rightleftharpoons> "CONST AOT_enc x F"

class AOT_UnaryIndividual = AOT_Individual +
  fixes AOT_concrete :: "<'a::AOT_Term>" ("E!")
  assumes AOT_concrete_exists[AOT_lambda_exists_intros]: "[v \<Turnstile> E!\<^bold>\<down>]"
      and AOT_meta_nocoder: "[v \<Turnstile> \<lparr>E!,x\<rparr>] \<Longrightarrow> \<not>[v \<Turnstile> \<lbrace>x,F\<rbrace>]"
      and AOT_meta_ordinary_exists: "\<exists> x v . [v \<Turnstile> \<lparr>E!,x\<rparr>]"
      and AOT_meta_A_objects: "\<And>\<phi> v . [v \<Turnstile> \<^bold>\<exists> x . \<lparr>[\<^bold>\<lambda>y . \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,y\<rparr>], x\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<phi> F)]"
(*      and AOT_unary_relation_identity: "[v \<Turnstile> (F :: 'a relation) \<^bold>=\<^sub>r G] = [v \<Turnstile> F\<^bold>\<down> \<^bold>& G\<^bold>\<down> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> x . \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>x,G\<rbrace>)]"*)
      and AOT_unary_relation_identity: "((F :: <'a>) \<^bold>=\<^sub>r G) = (F\<^bold>\<down> \<^bold>& G\<^bold>\<down> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> x . \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>x,G\<rbrace>))"
(*      and AOT_contingent_old: "[v \<Turnstile> \<^bold>\<diamond>(\<^bold>\<exists>x . \<lparr>E!,x\<rparr> \<^bold>& \<^bold>\<diamond>\<^bold>\<not>\<lparr>E!,x\<rparr>) \<^bold>& \<^bold>\<diamond>\<^bold>\<not>(\<^bold>\<exists> x . \<lparr>E!,x\<rparr> \<^bold>& \<^bold>\<diamond>\<^bold>\<not>\<lparr>E!,x\<rparr>)]" *)
      and AOT_contingent: "[v \<Turnstile> \<^bold>\<diamond>(\<^bold>\<exists>x . \<lparr>E!,x\<rparr> \<^bold>& \<^bold>\<not>\<^bold>\<A>\<lparr>E!,x\<rparr>)]"
      and AOT_unary_proj_enc: "AOT_proj_enc x \<phi> = AOT_enc x [\<^bold>\<lambda>z . \<phi> z]"
begin
  definition AOT_Ordinary :: "<'a>" ("O!") where
    "AOT_Ordinary \<equiv> [\<^bold>\<lambda> y . \<^bold>\<diamond>\<lparr>E!,y\<rparr>]"
  definition AOT_Abstract :: "<'a>" ("A!") where
    "AOT_Abstract \<equiv> [\<^bold>\<lambda> y . \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,y\<rparr>]"
end

lemma AOT_Ordinary_exists[AOT_lambda_exists_intros]: shows "[v \<Turnstile> O!\<^bold>\<down>]"
  unfolding AOT_Ordinary_def
  by (fast intro: AOT_lambda_exists_intros)
lemma AOT_Abstract_exists[AOT_lambda_exists_intros]: "[v \<Turnstile> A!\<^bold>\<down>]"
  unfolding AOT_Abstract_def
  by (fast intro: AOT_lambda_exists_intros)

lemma AOT_rel_proj_exists1: assumes "[v \<Turnstile> G\<^bold>\<down>]"
  shows "\<And> y. [v \<Turnstile> y\<^bold>\<down>] \<Longrightarrow> [v \<Turnstile> [\<^bold>\<lambda>z. \<lparr>G, (z, y)\<rparr>]\<^bold>\<down>]"
  apply (rule AOT_lambda_existsI) using assms[THEN AOT_exists_necI]
  by (metis AOT_equivS AOT_equiv_prodI AOT_equiv_sym AOT_exe_trans AOT_logical_existsE fst_conv snd_conv)

lemma AOT_rel_proj_exists2: assumes "[v \<Turnstile> G\<^bold>\<down>]"
  shows "\<And> y. [v \<Turnstile> y\<^bold>\<down>] \<Longrightarrow> [v \<Turnstile> [\<^bold>\<lambda>z. \<lparr>G, (y, z)\<rparr>]\<^bold>\<down>]"
  apply (rule AOT_lambda_existsI) using assms[THEN AOT_exists_necI]
  by (metis AOT_equivS AOT_equiv_prodI AOT_equiv_sym AOT_exe_trans AOT_logical_existsE fst_conv snd_conv)


lemma AOT_lambda_exists_simple_def: assumes "[v \<Turnstile> (Abs_relation \<phi>)\<^bold>\<down>]"
  shows "[\<^bold>\<lambda>y . \<phi> y] = Abs_relation (\<lambda> x . if (\<forall>v . [v \<Turnstile> x\<^bold>\<down>]) then \<phi> x else AOT_nec_false)"
proof -
  {
    fix x :: 'a
    {
    assume 1: "[dw \<Turnstile> x\<^bold>\<down>]"
    {
      fix s w
      have "(s = dj \<and> Rep_\<o> (id \<phi> x) s w \<or> s \<noteq> dj \<and> (\<forall>y. [dw \<Turnstile> x \<^bold>~ y] \<longrightarrow> Rep_\<o> (id \<phi> y) s w))
            = Rep_\<o> (\<phi> x) s w" apply (cases "s = dj")
         apply simp
        apply simp using assms[THEN AOT_exists_necI, THEN AOT_equiv_existsE, THEN AOT_equiv_relE1, THEN Rep_\<o>_inject[THEN iffD2]]
        apply (simp add: Abs_relation_inverse)
        using "1" AOT_equivS AOT_logical_existsE by fastforce
    } note 1 = this
    have "(if \<forall>v. [v \<Turnstile> x\<^bold>\<down>] then Abs_\<o> (\<lambda>s w. s = dj \<and> Rep_\<o> (id \<phi> x) s w \<or>
              s \<noteq> dj \<and> (\<forall>y. [dw \<Turnstile> x \<^bold>~ y] \<longrightarrow> Rep_\<o> (id \<phi> y) s w)) else AOT_nec_false)
              = (if \<forall>v. [v \<Turnstile> x\<^bold>\<down>] then \<phi> x else AOT_nec_false)"
      apply (subst 1) by (simp add: Rep_\<o>_inverse)
  }
  moreover {
    assume 1: "\<not>[dw \<Turnstile> x\<^bold>\<down>]"
    have "(if \<forall>v. [v \<Turnstile> x\<^bold>\<down>] then Abs_\<o> (\<lambda>s w. s = dj \<and> Rep_\<o> (id \<phi> x) s w \<or>
              s \<noteq> dj \<and> (\<forall>y. [dw \<Turnstile> x \<^bold>~ y] \<longrightarrow> Rep_\<o> (id \<phi> y) s w)) else AOT_nec_false)
              = (if \<forall>v. [v \<Turnstile> x\<^bold>\<down>] then \<phi> x else AOT_nec_false)"
      using "1" by auto
  }
  ultimately have "(if \<forall>v. [v \<Turnstile> x\<^bold>\<down>] then Abs_\<o> (\<lambda>s w. s = dj \<and> Rep_\<o> (id \<phi> x) s w \<or>
              s \<noteq> dj \<and> (\<forall>y. [dw \<Turnstile> x \<^bold>~ y] \<longrightarrow> Rep_\<o> (id \<phi> y) s w)) else AOT_nec_false)
              = (if \<forall>v. [v \<Turnstile> x\<^bold>\<down>] then \<phi> x else AOT_nec_false)" by auto
  }
  thus ?thesis unfolding AOT_lambda_def by simp
qed

lemma AOT_lambda_exists_simple_def2: assumes "[v \<Turnstile> (Abs_relation \<phi>)\<^bold>\<down>]"
  shows "Rep_relation [\<^bold>\<lambda>y . \<phi> y] = (\<lambda> x . if (\<forall>v . [v \<Turnstile> x\<^bold>\<down>]) then \<phi> x else AOT_nec_false)"
  using AOT_lambda_exists_simple_def[OF assms] by (simp add: Abs_relation_inverse)

instantiation prod :: (AOT_UnaryIndividual, AOT_Individual) AOT_Individual
begin
  definition AOT_enc_prod :: "'a\<times>'b \<Rightarrow> <'a\<times>'b> \<Rightarrow> \<o>" where
    "AOT_enc_prod \<equiv> \<lambda> (a,b) F . F\<^bold>\<down> \<^bold>& \<lbrace>a, [\<^bold>\<lambda>y . \<lparr>F,y,b\<rparr>]\<rbrace> \<^bold>& AOT_proj_enc b (\<lambda>y . \<lparr>F,a,y\<rparr>)"
  definition AOT_universal_encoder_prod :: "'a\<times>'b" where
    "AOT_universal_encoder_prod \<equiv> (AOT_universal_encoder, AOT_universal_encoder)"
  definition AOT_relation_identity_prod :: "<'a\<times>'b> \<Rightarrow> <'a\<times>'b> \<Rightarrow> \<o>" where
    "AOT_relation_identity_prod \<equiv> \<lambda> F G . F\<^bold>\<down> \<^bold>& G\<^bold>\<down> \<^bold>&
      (\<^bold>\<forall> y . [\<^bold>\<lambda>z . \<lparr>F,z,y\<rparr>] \<^bold>=\<^sub>r [\<^bold>\<lambda>z . \<lparr>G,z,y\<rparr>]) \<^bold>&
      (\<^bold>\<forall> y . [\<^bold>\<lambda>z . \<lparr>F,y,z\<rparr>] \<^bold>=\<^sub>r [\<^bold>\<lambda>z . \<lparr>G,y,z\<rparr>])"
  definition AOT_proj_enc_prod :: "'a\<times>'b \<Rightarrow> (('a\<times>'b) \<Rightarrow> \<o>) \<Rightarrow> \<o>" where
    "AOT_proj_enc_prod \<equiv> (\<lambda> x \<phi> . \<lbrace>fst x, [\<^bold>\<lambda>y . \<phi> (y,snd x)]\<rbrace> \<^bold>& AOT_proj_enc (snd x) (\<lambda> y . \<phi> (fst x, y)))"
instance proof
  fix v
  show "[v \<Turnstile> (AOT_universal_encoder::'a\<times>'b)\<^bold>\<down>]"
    unfolding AOT_universal_encoder_prod_def
    by (metis AOT_equiv_existsS AOT_equiv_prodI AOT_universal_encoder_exists fst_conv snd_conv)
next
  fix F :: "<'a\<times>'b>" and v :: i
  assume F_ex: "[v \<Turnstile> F\<^bold>\<down>]"
  {
    fix y :: 'b
    assume y_ex: "[v \<Turnstile> y\<^bold>\<down>]"
    have "[v \<Turnstile> [\<^bold>\<lambda>x . \<lparr>F,x,y\<rparr>]\<^bold>\<down>]"
      apply (rule AOT_lambda_existsI)
      by (metis (no_types, hide_lams) AOT_equivS AOT_equiv_prodI AOT_eta AOT_lambda_existsE AOT_logical_existsS F_ex fst_conv snd_conv y_ex)
    hence "[v \<Turnstile> \<lbrace>AOT_universal_encoder,[\<^bold>\<lambda>x . \<lparr>F,x,y\<rparr>]\<rbrace>]"
      using AOT_universal_encoder by blast
  }
  moreover {
    fix x :: 'a
    assume x_ex: "[v \<Turnstile> x\<^bold>\<down>]"
    have "[v \<Turnstile> [\<^bold>\<lambda>y . \<lparr>F,x,y\<rparr>]\<^bold>\<down>]"
      apply (rule AOT_lambda_existsI)
      by (metis (no_types, hide_lams) AOT_equivS AOT_equiv_prodI AOT_eta AOT_lambda_existsE AOT_logical_existsS F_ex fst_conv snd_conv x_ex)
    hence "[v \<Turnstile> \<lbrace>AOT_universal_encoder,[\<^bold>\<lambda>y . \<lparr>F,x,y\<rparr>]\<rbrace>]"
      using AOT_universal_encoder by blast
  }
  moreover have "\<And> v x y . [v \<Turnstile> x \<^bold>~ y] \<Longrightarrow> [v \<Turnstile> (\<lambda>y. \<lparr>F, (AOT_universal_encoder, y)\<rparr>) x] = [v \<Turnstile> (\<lambda>y. \<lparr>F, (AOT_universal_encoder, y)\<rparr>) y]"
    by (metis (no_types, lifting) AOT_equiv_existsS AOT_equiv_prodI AOT_equiv_sym AOT_exeE2 AOT_exe_trans AOT_exists_prodE1 fst_conv snd_conv)
  ultimately show "[v \<Turnstile> \<lbrace>AOT_universal_encoder,F\<rbrace>]"
    unfolding AOT_enc_prod_def AOT_universal_encoder_prod_def
    using AOT_universal_encoder_exists[where 'a='a]
          AOT_universal_encoder_exists[where 'a='b] apply simp
    by (simp add: AOT_conjS AOT_proj_enc_universal F_ex)
next
  fix F G :: "<'a\<times>'b>" and v :: i
  {
    assume "[v \<Turnstile> F \<^bold>=\<^sub>r G]"
    hence 0: "[v \<Turnstile> F\<^bold>\<down>] \<and> [v \<Turnstile> G\<^bold>\<down>] \<and> (\<forall> y . [v \<Turnstile> y\<^bold>\<down>] \<longrightarrow> [v \<Turnstile> [\<^bold>\<lambda>z. \<lparr>F, (z, y)\<rparr>] \<^bold>=\<^sub>r [\<^bold>\<lambda>z. \<lparr>G, (z, y)\<rparr>]])
              \<and> (\<forall> y . [v \<Turnstile> y\<^bold>\<down>] \<longrightarrow> [v \<Turnstile> [\<^bold>\<lambda>z. \<lparr>F, (y, z)\<rparr>] \<^bold>=\<^sub>r [\<^bold>\<lambda>z. \<lparr>G, (y, z)\<rparr>]])"
      unfolding AOT_relation_identity_prod_def by AOT_meta_simp
    hence 1: "(\<forall>y. [v \<Turnstile> y\<^bold>\<down>] \<longrightarrow> [\<^bold>\<lambda>z. \<lparr>F, (z, y)\<rparr>] = [\<^bold>\<lambda>z. \<lparr>G, (z, y)\<rparr>])"
      unfolding AOT_relation_identity_prod_def
      using AOT_relation_identity AOT_allE AOT_conjS by fastforce
    {
      fix y :: 'b
      assume y_ex: "[v \<Turnstile> y\<^bold>\<down>]"
      hence "[\<^bold>\<lambda>z. \<lparr>F, (z, y)\<rparr>] = [\<^bold>\<lambda>z. \<lparr>G, (z, y)\<rparr>]"
        by (simp add: 1)
      hence 2: "\<And> x . Rep_relation [\<^bold>\<lambda>z. \<lparr>F, (z, y)\<rparr>] x = Rep_relation [\<^bold>\<lambda>z. \<lparr>G, (z, y)\<rparr>] x" by auto
      have "\<And> (F :: <'a\<times>'b>) (x :: 'a) (ya :: 'a) (v :: i) . [v \<Turnstile> x \<^bold>~ ya] \<Longrightarrow> \<lparr>F, (x, y)\<rparr> = \<lparr>F, (ya, y)\<rparr>"
      proof -
        fix F :: "<'a\<times>'b>" and x ya :: 'a and v :: i
        assume "[v \<Turnstile> x \<^bold>~ ya]"
        hence "[v \<Turnstile> (x,y) \<^bold>~ (ya,y)]" using y_ex
          using AOT_equiv_existsS AOT_equiv_prodI AOT_logical_existsE AOT_logical_existsI by fastforce
        thus "\<lparr>F, (x, y)\<rparr> = \<lparr>F, (ya, y)\<rparr>"
          using AOT_exe_trans2 by blast
      qed
      hence 3: "\<And> F :: <'a\<times>'b> . [v \<Turnstile> (Abs_relation (\<lambda> z . \<lparr>F, (z,y)\<rparr>))\<^bold>\<down>]"
        apply - apply (rule AOT_exists_relI)
         apply (simp add: Abs_relation_inverse)+
        by (meson AOT_exe_def AOT_exists_prodE1 AOT_logical_existsS)
      have "\<And> z . (\<forall> v . [v \<Turnstile> z\<^bold>\<down>]) \<Longrightarrow> \<lparr>F, (z, y)\<rparr> = \<lparr>G, (z, y)\<rparr>" using AOT_lambda_exists_simple_def2[OF 3] 2
        by presburger
      hence "\<And> z . [v \<Turnstile> z\<^bold>\<down>] \<Longrightarrow> \<lparr>F, (z, y)\<rparr> = \<lparr>G, (z, y)\<rparr>"
        by (simp add: AOT_logical_existsS)
      moreover have zy_eq: "\<And> z . [v \<Turnstile> z\<^bold>\<down>] \<Longrightarrow> (\<forall> v . [v \<Turnstile> (z,y)\<^bold>\<down>])" using y_ex
        by (meson AOT_exists_prodI AOT_logical_existsS)
      ultimately have "\<And> z . [v \<Turnstile> z\<^bold>\<down>] \<Longrightarrow> Rep_relation F (z, y) = Rep_relation G (z, y)"
        unfolding AOT_exe_def
        by (metis "0" AOT_logical_existsE)
    } note 2 = this
    have "F = G" apply (rule AOT_fun_equiv_equal[where v=v])
      apply (rule AOT_equiv_relI) using 2
        apply (metis (no_types, lifting) "0" AOT_conjS AOT_equiv_def AOT_equiv_existsE AOT_equiv_prodE1 AOT_equiv_prodE2 AOT_equiv_relE1 surjective_pairing)
      by (metis "0" AOT_eta AOT_lambda.rep_eq)+
    hence "[v \<Turnstile> F\<^bold>\<down>] \<and> [v \<Turnstile> G\<^bold>\<down>] \<and> F = G" using 0 by auto
  }
  moreover {
    assume 1: "[v \<Turnstile> F\<^bold>\<down>] \<and> [v \<Turnstile> G\<^bold>\<down>] \<and> F = G"
    have "[v \<Turnstile> F \<^bold>=\<^sub>r G]"
      unfolding AOT_relation_identity_prod_def apply (subst 1[THEN conjunct2, THEN conjunct2])+
      apply AOT_meta_simp using 1  apply (subst AOT_relation_identity)+
      by (simp add: AOT_rel_proj_exists1 AOT_rel_proj_exists2)
      
  }
  ultimately show "[v \<Turnstile> F \<^bold>=\<^sub>r G] = ([v \<Turnstile> F \<^bold>\<down>] \<and> [v \<Turnstile> G\<^bold>\<down>] \<and> F = G)" by argo
next
  fix v :: i and x :: "'a\<times>'b" and F :: "<'a\<times>'b>"
  show "[v \<Turnstile> \<lbrace>x, F\<rbrace>] = (\<forall>v. [v \<Turnstile> \<lbrace>x, F\<rbrace>])"
    unfolding AOT_enc_prod_def apply (induct x) apply simp
    by (meson AOT_conjS AOT_enc_rigid AOT_proj_enc_nec AOT_logical_existsS)
next
  fix v :: i and x :: "'a\<times>'b" and F :: "<'a\<times>'b>"
  show "[v \<Turnstile> \<lbrace>x, F\<rbrace>] \<Longrightarrow> [v \<Turnstile> x\<^bold>\<down>] \<and> [v \<Turnstile> F\<^bold>\<down>]"
    unfolding AOT_enc_prod_def apply (induct x)
    unfolding AOT_meta_equiv_prod_def apply simp
    by (meson AOT_conjS AOT_enc_impl_exists AOT_exists_prodI AOT_proj_enc_impl_ex)
next
  fix v :: i and \<phi> :: "'a\<times>'b\<Rightarrow>\<o>" and x :: "'a\<times>'b" and y :: "'a\<times>'b"
  assume 1: "\<And> v x y . ([v \<Turnstile> x \<^bold>~ y] \<Longrightarrow> [v \<Turnstile> \<phi> x] = [v \<Turnstile> \<phi> y])"
  have 2: "\<And>(y::'a) ya v. [v \<Turnstile> y \<^bold>~ ya] \<Longrightarrow> [v \<Turnstile> (y,AOT_universal_encoder::'b) \<^bold>~ (ya, AOT_universal_encoder)]"
    by (simp add: AOT_equiv_existsE AOT_equiv_prodI AOT_universal_encoder_exists)
  have 3: "[v \<Turnstile> [\<^bold>\<lambda>y. \<phi> (y, AOT_universal_encoder)]\<^bold>\<down>]" apply (rule AOT_lambda_existsI)
    using 1 2 by blast
  have 4: "\<And>v x y. [v \<Turnstile> x \<^bold>~ y] \<Longrightarrow> [v \<Turnstile> \<phi> (AOT_universal_encoder, x)] = [v \<Turnstile> \<phi> (AOT_universal_encoder, y)]"
    by (simp add: "1" AOT_equiv_existsS AOT_equiv_prodI AOT_universal_encoder_exists)
  show "[v \<Turnstile> AOT_proj_enc AOT_universal_encoder \<phi>]"
    unfolding AOT_proj_enc_prod_def AOT_universal_encoder_prod_def apply AOT_meta_auto
    apply (simp add: "3" AOT_universal_encoder)
    using AOT_proj_enc_universal[of "(\<lambda>y. \<phi> (AOT_universal_encoder, y))" v] 4 by auto
next
  fix v w :: i and x :: "'a\<times>'b" and \<phi> :: "('a\<times>'b) \<Rightarrow> \<o>"
  assume "[v \<Turnstile> AOT_proj_enc x \<phi>]"
  thus "[w \<Turnstile> AOT_proj_enc x \<phi>]" unfolding AOT_proj_enc_prod_def
    using AOT_conjS AOT_enc_rigid AOT_proj_enc_nec by blast
next
  fix v :: i and x :: "'a\<times>'b" and \<phi> :: "('a\<times>'b) \<Rightarrow> \<o>"
  assume "[v \<Turnstile> AOT_proj_enc x \<phi>]"
  thus "[v \<Turnstile> x\<^bold>\<down>]" unfolding AOT_proj_enc_prod_def
    by (metis AOT_conjE AOT_enc_impl_exists AOT_exists_prodI AOT_proj_enc_impl_ex prod.collapse)
qed
end

lemma AOT_encE2[AOT_meta_elim]:
  assumes "[v \<Turnstile> \<lbrace>x,F\<rbrace>]"
    shows "[v \<Turnstile> x\<^bold>\<down>]"
  using assms AOT_enc_impl_exists by blast
lemma AOT_encE3[AOT_meta_elim]:
  assumes "[v \<Turnstile> \<lbrace>x,F\<rbrace>]"
  shows "[v \<Turnstile> F\<^bold>\<down>]"
  using assms AOT_enc_impl_exists by blast

lemma AOT_proj_enc_I[AOT_meta_intro_safe]:
  assumes "[v \<Turnstile> \<lbrace>b::'a::AOT_UnaryIndividual, [\<^bold>\<lambda>z. \<phi> z]\<rbrace>]"
    shows "[v \<Turnstile> AOT_proj_enc b \<phi>]"
  apply (subst AOT_unary_proj_enc) using assms by simp

lemma AOT_proj_enc_E[AOT_meta_elim_safe]:
  assumes "[v \<Turnstile> AOT_proj_enc b \<phi>]"
  shows "[v \<Turnstile> \<lbrace>b::'a::AOT_UnaryIndividual, [\<^bold>\<lambda>z. \<phi> z]\<rbrace>]"
  by (metis AOT_unary_proj_enc assms)

lemma AOT_prod_enc_I[AOT_meta_intro_safe]:
  assumes "[v \<Turnstile> F\<^bold>\<down>]"
      and "[v \<Turnstile> \<lbrace>a, [\<^bold>\<lambda>z. \<lparr>F,z,b\<rparr>]\<rbrace>]"
      and "[v \<Turnstile> AOT_proj_enc b (\<lambda>y. \<lparr>F, a, y\<rparr>)]"
    shows "[v \<Turnstile> \<lbrace>a,b,F\<rbrace>]"
  unfolding AOT_enc_prod_def using assms apply simp
  by (simp add: AOT_conjI)
lemma AOT_prod_enc_E1[AOT_meta_elim]:
  assumes "[v \<Turnstile> \<lbrace>x,y,F\<rbrace>]"
  shows "[v \<Turnstile> \<lbrace>x, [\<^bold>\<lambda>z. \<lparr>F,z,y\<rparr>]\<rbrace>]"
  using assms unfolding AOT_enc_prod_def by AOT_meta_auto
lemma AOT_prod_enc_E2[AOT_meta_elim]:
  assumes "[v \<Turnstile> \<lbrace>x,y,F\<rbrace>]"
  shows "[v \<Turnstile> AOT_proj_enc y (\<lambda>y. \<lparr>F, x, y\<rparr>)]"
  using assms unfolding AOT_enc_prod_def by AOT_meta_simp
lemma AOT_prod_enc_E3[AOT_meta_elim]:
  assumes "[v \<Turnstile> \<lbrace>x,y::'b::AOT_UnaryIndividual,F\<rbrace>]"
  shows "[v \<Turnstile> \<lbrace>y,[\<^bold>\<lambda>y. \<lparr>F, x, y\<rparr>]\<rbrace>]"
  using assms unfolding AOT_enc_prod_def by AOT_meta_auto

lemma AOT_proj_enc_prod_I[AOT_meta_intro_safe]:
  assumes "[v \<Turnstile> \<lbrace>b, [\<^bold>\<lambda>y. \<lparr>F, (a, y, c)\<rparr>]\<rbrace>]"
      and "[v \<Turnstile> AOT_proj_enc c (\<lambda>y. \<lparr>F, a, b, y\<rparr>)]"
  shows "[v \<Turnstile> AOT_proj_enc (b, c) (\<lambda>y. \<lparr>F, a, y\<rparr>)]"
  unfolding AOT_proj_enc_prod_def apply AOT_meta_simp using assms by auto

lemma AOT_proj_enc_prod_E1[AOT_meta_elim]:
  assumes "[v \<Turnstile> AOT_proj_enc (b, c) (\<lambda>y. \<lparr>F, a, y\<rparr>)]"
  shows  "[v \<Turnstile> \<lbrace>b, [\<^bold>\<lambda>y. \<lparr>F, a, y, c\<rparr>]\<rbrace>]"
  using assms unfolding AOT_proj_enc_prod_def by AOT_meta_simp

lemma AOT_proj_enc_prod_E2[AOT_meta_elim]:
  assumes "[v \<Turnstile> AOT_proj_enc (b, c) (\<lambda>y. \<lparr>F, a, y\<rparr>)]"
  shows  "[v \<Turnstile> AOT_proj_enc c (\<lambda>y. \<lparr>F, a, b, y\<rparr>)]"
  using assms unfolding AOT_proj_enc_prod_def by AOT_meta_simp

lemma AOT_prod_enc_I2:
  assumes "[v \<Turnstile> F\<^bold>\<down>]"
      and "[v \<Turnstile> \<lbrace>a, [\<^bold>\<lambda>z. \<lparr>F,z,b,c\<rparr>]\<rbrace>]"
      and "[v \<Turnstile> \<lbrace>b, [\<^bold>\<lambda>z. \<lparr>F,a,z,c\<rparr>]\<rbrace>]"
      and "[v \<Turnstile> \<lbrace>c::'c::AOT_UnaryIndividual, [\<^bold>\<lambda>z. \<lparr>F,a,b,z\<rparr>]\<rbrace>]"
    shows "[v \<Turnstile> \<lbrace>a,b,c,F\<rbrace>]"
  apply (rule AOT_prod_enc_I)
  using assms(1) apply simp
  using assms(2) apply simp
  apply (rule AOT_proj_enc_prod_I)
  using assms(3) apply simp
  apply (rule AOT_proj_enc_I)
  using assms(4) by simp
 
declare AOT_enc_prod_def[AOT_meta_simp] AOT_unary_proj_enc[AOT_meta_simp] AOT_proj_enc_prod_def[AOT_meta_simp]

instantiation unit :: AOT_Individual
begin
definition AOT_enc_unit :: "unit \<Rightarrow> <unit> \<Rightarrow> \<o>" where
  "AOT_enc_unit \<equiv> (\<lambda> () p . AOT_nec_true)"
definition AOT_universal_encoder_unit :: "unit" where "AOT_universal_encoder_unit \<equiv> ()"
definition AOT_relation_identity_unit :: "<unit> \<Rightarrow> <unit> \<Rightarrow> \<o>" where
  "AOT_relation_identity_unit \<equiv> (\<lambda> p q . Abs_\<o> (\<lambda> s w . p = q))"
definition AOT_proj_enc_unit :: "unit \<Rightarrow> (unit \<Rightarrow> \<o>) \<Rightarrow> \<o>" where
  "AOT_proj_enc_unit \<equiv> (\<lambda> () \<phi> . AOT_nec_true)"
instance proof
  fix v
  show "[v \<Turnstile> (AOT_universal_encoder::unit)\<^bold>\<down>]"
    apply (rule AOT_logical_existsI)
    by (simp add: AOT_term_equiv_unitI)
next
  fix v :: i and F :: "<unit>"
  assume "[v \<Turnstile> F\<^bold>\<down>]"
  have 1: "\<And> x . (case x of () \<Rightarrow> (\<lambda>p. AOT_nec_true)) = (\<lambda>p. AOT_nec_true)"
    by (simp add: case_unit_Unity)
  show "[v \<Turnstile> \<lbrace>AOT_universal_encoder, F\<rbrace>]"
    unfolding AOT_enc_unit_def AOT_universal_encoder_unit_def apply (subst 1)
    unfolding AOT_nec_true_def AOT_valid_in_def by (simp add: Abs_\<o>_inverse)
next
  fix v :: i and F G :: "<unit>"
  have F_ex: "[v \<Turnstile> F\<^bold>\<down>]" apply (rule AOT_logical_existsI)
    by (metis (full_types) AOT_meta_equiv_part_equivp AOT_meta_equiv_relation.rep_eq old.unit.exhaust part_equivp_def)
  have G_ex: "[v \<Turnstile> G\<^bold>\<down>]" apply (rule AOT_logical_existsI)
    by (metis (full_types) AOT_meta_equiv_part_equivp AOT_meta_equiv_relation.rep_eq old.unit.exhaust part_equivp_def)
  show "[v \<Turnstile> F \<^bold>=\<^sub>r G] = ([v \<Turnstile> F\<^bold>\<down>] \<and> [v \<Turnstile> G\<^bold>\<down>] \<and> F = G)"
    unfolding AOT_relation_identity_unit_def apply (simp add: F_ex G_ex)
    unfolding AOT_valid_in_def by (simp add: Abs_\<o>_inverse)
next
  fix v :: i and x :: unit and F :: "<unit>"
  have 1: "(case x of () \<Rightarrow> (\<lambda>p. AOT_nec_true)) = (\<lambda>p. AOT_nec_true)"
    by (simp add: case_unit_Unity)
  show "[v \<Turnstile> \<lbrace>x, F\<rbrace>] = (\<forall>v. [v \<Turnstile> \<lbrace>x, F\<rbrace>])" unfolding AOT_enc_unit_def apply (subst 1)+
    unfolding AOT_valid_in_def AOT_nec_true_def by (simp add: Abs_\<o>_inverse)
next
  fix v :: i and x :: unit and F :: "<unit>"
  assume "[v \<Turnstile> \<lbrace>x, F\<rbrace>]"
  have F_ex: "[v \<Turnstile> F\<^bold>\<down>]" apply (rule AOT_logical_existsI)
    by (metis (full_types) AOT_meta_equiv_part_equivp AOT_meta_equiv_relation.rep_eq old.unit.exhaust part_equivp_def)
  have x_ex: "[v \<Turnstile> x\<^bold>\<down>]" apply (rule AOT_logical_existsI) unfolding AOT_meta_equiv_unit_def by auto
  show "[v \<Turnstile> x\<^bold>\<down>] \<and> [v \<Turnstile> F\<^bold>\<down>]" using F_ex x_ex by auto
next
  fix \<phi> :: "unit \<Rightarrow> \<o>" and v :: i
  have 1: "\<And> x . (case x of () \<Rightarrow> (\<lambda>p. AOT_nec_true)) = (\<lambda>p. AOT_nec_true)"
    by (simp add: case_unit_Unity)
  show "[v \<Turnstile> AOT_proj_enc AOT_universal_encoder \<phi>]"
    unfolding AOT_proj_enc_unit_def apply (subst 1)
    by (rule AOT_nec_trueI)
next
  fix v va :: i and x :: unit and \<phi> :: "unit \<Rightarrow> \<o>"
  have 1: "\<And> x . (case x of () \<Rightarrow> (\<lambda>p. AOT_nec_true)) = (\<lambda>p. AOT_nec_true)"
    by (simp add: case_unit_Unity)
  show "[va \<Turnstile> AOT_proj_enc x \<phi>]"
    unfolding AOT_proj_enc_unit_def apply (subst 1)
    by (rule AOT_nec_trueI)
next
  fix v :: i and x :: unit and \<phi> :: "unit \<Rightarrow> \<o>"
  show "[v \<Turnstile> x\<^bold>\<down>]"
    apply (rule AOT_logical_existsI) unfolding AOT_meta_equiv_unit_def by simp
qed
end

end
