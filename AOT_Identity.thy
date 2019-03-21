theory AOT_Identity
  imports AOT_Individual
begin

class AOT_Identity = AOT_Term +
  fixes AOT_identity :: "'a::AOT_Term \<Rightarrow> 'a \<Rightarrow> \<o>" (infixl "\<^bold>=" 63)
  assumes AOT_l_identity: "[v \<Turnstile> x \<^bold>= y] \<Longrightarrow> [v \<Turnstile> \<phi> x] \<Longrightarrow> [v \<Turnstile> \<phi> y]"
      and AOT_eq_exist: "[v \<Turnstile> x \<^bold>= y] \<Longrightarrow> [v \<Turnstile> x\<^bold>\<down>] \<and> [v \<Turnstile> y\<^bold>\<down>]"
      and AOT_nec_selfeq: "[v \<Turnstile> x\<^bold>\<down>] \<Longrightarrow> [v \<Turnstile> \<^bold>\<box>(x \<^bold>= x)]"

lemma AOT_eq_nec: "[v \<Turnstile> x \<^bold>= y] \<Longrightarrow> [w \<Turnstile> x \<^bold>= y]"
proof -
  assume 1: "[v \<Turnstile> x \<^bold>= y]"
  hence "[v \<Turnstile> x\<^bold>\<down>]" using AOT_eq_exist by auto
  hence "[v \<Turnstile> \<^bold>\<box>(x \<^bold>= x)]" using AOT_nec_selfeq by auto
  thus ?thesis
    using AOT_l_identity[where v=v and x=x and y=y and \<phi>="\<lambda> y . \<^bold>\<box>(x \<^bold>= y)", OF 1]
    using AOT_boxS by blast
qed    

lemma AOT_non_exist_non_eq: "\<not>[v \<Turnstile> x\<^bold>\<down>] \<or> \<not>[v \<Turnstile> y\<^bold>\<down>] \<Longrightarrow> \<not>[v \<Turnstile> x \<^bold>= y]" using AOT_eq_exist by blast

definition AOT_identity\<^sub>E :: "('a::AOT_UnaryIndividual\<times>'a) relation" where
  "AOT_identity\<^sub>E \<equiv> [\<^bold>\<lambda> (x,y) . \<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F. \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>)]"

lemma AOT_identity\<^sub>E_exists[AOT_lambda_exists_intros]: "[v \<Turnstile> AOT_identity\<^sub>E\<^bold>\<down>]"
  unfolding AOT_identity\<^sub>E_def
  by (fast intro: AOT_lambda_exists_intros)

definition AOT_identity\<^sub>E_infix :: "'a::AOT_UnaryIndividual \<Rightarrow> 'a \<Rightarrow> \<o>" (infixl "\<^bold>=\<^sub>E" 63) where
  "AOT_identity\<^sub>E_infix \<equiv> (\<lambda> x y . \<lparr>AOT_identity\<^sub>E, x, y\<rparr>)"

instantiation relation :: (AOT_Individual) AOT_Identity
begin
definition AOT_identity_relation :: "('a relation) \<Rightarrow> ('a relation) \<Rightarrow> \<o>" where
  "AOT_identity_relation \<equiv> \<lambda> F G . F \<^bold>=\<^sub>r G"
instance proof
  fix v :: i and F G :: "'a relation" and \<phi> :: "('a relation) \<Rightarrow> \<o>"
  assume "[v \<Turnstile> F \<^bold>= G]"
  hence F_ex: "[v \<Turnstile> F\<^bold>\<down>]"
    and G_ex: "[v \<Turnstile> G\<^bold>\<down>]"
    and F_eq_G: "F = G" apply -
    unfolding AOT_identity_relation_def
    by (auto simp: AOT_relation_identity AOT_valid_in.abs_eq)
  moreover assume "[v \<Turnstile> \<phi> F]"
  ultimately show "[v \<Turnstile> \<phi> G]" by auto
next
  fix v :: i and F G :: "'a relation"
  assume "[v \<Turnstile> F \<^bold>= G]"
  thus "[v \<Turnstile> F\<^bold>\<down>] \<and> [v \<Turnstile> G\<^bold>\<down>]"
    unfolding AOT_identity_relation_def
    by (auto simp: AOT_relation_identity AOT_valid_in.abs_eq)
next
  fix v and x :: "'a relation"
  assume "[v \<Turnstile> x\<^bold>\<down>]"
  thus "[v \<Turnstile> \<^bold>\<box>(x \<^bold>= x)]"
    by (metis AOT_Identity.AOT_identity_relation_def AOT_boxI AOT_exists_necI AOT_relation_identity)
qed
end

class AOT_IndividualIdentity = AOT_Term + AOT_Individual + AOT_Identity

class AOT_UnaryIndividualIdentity = AOT_IndividualIdentity + AOT_UnaryIndividual +
  fixes AOT_that :: "('a::{AOT_UnaryIndividual, AOT_Identity} \<Rightarrow> \<o>) \<Rightarrow> 'a" (binder "\<^bold>\<iota>" [8] 9)
  assumes AOT_individual_identity: "((x::'a) \<^bold>= y) = (x \<^bold>=\<^sub>E y \<^bold>\<or> \<lparr>A!,x\<rparr> \<^bold>& \<lparr>A!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F . \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>y,F\<rbrace>))"
(*AOT_individual_identity: "[v \<Turnstile> (x::'a) \<^bold>= y] = [v \<Turnstile> x \<^bold>=\<^sub>E y \<^bold>\<or> \<lparr>A!,x\<rparr> \<^bold>& \<lparr>A!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F . \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>y,F\<rbrace>)]"*)
      and AOT_descriptions: "[v \<Turnstile> x\<^bold>\<down>] \<Longrightarrow> [v \<Turnstile> (x \<^bold>= (\<^bold>\<iota>x. \<phi> x)) \<^bold>\<equiv> (\<^bold>\<forall> z . (\<^bold>\<A>\<phi> z \<^bold>\<equiv> z \<^bold>= x))]"

lemma AOT_identity\<^sub>0: "[v \<Turnstile> \<Pi> \<^bold>= \<Pi>'] = [v \<Turnstile> \<Pi>\<^bold>\<down> \<^bold>& \<Pi>'\<^bold>\<down> \<^bold>& [\<^bold>\<lambda>x . \<lparr>\<Pi>,()\<rparr>] \<^bold>= [\<^bold>\<lambda>x . \<lparr>\<Pi>',()\<rparr>]]"
proof
  assume "[v \<Turnstile> \<Pi> \<^bold>= \<Pi>']"
  hence 1: "\<Pi> = \<Pi>'" unfolding AOT_identity_relation_def AOT_relation_identity_unit_def AOT_valid_in_def by (simp add: Abs_\<o>_inverse)
  have \<Pi>_ex: "[v \<Turnstile> \<Pi>\<^bold>\<down>]" apply (rule AOT_logical_existsI)
    by (metis (full_types) AOT_meta_equiv_part_equivp AOT_meta_equiv_relation.rep_eq old.unit.exhaust part_equivp_def)
  have \<Pi>'_ex: "[v \<Turnstile> \<Pi>'\<^bold>\<down>]" apply (rule AOT_logical_existsI)
    by (metis (full_types) AOT_meta_equiv_part_equivp AOT_meta_equiv_relation.rep_eq old.unit.exhaust part_equivp_def)
  have "[\<^bold>\<lambda>x :: 'a. \<lparr>\<Pi>, ()\<rparr>] = [\<^bold>\<lambda>x. \<lparr>\<Pi>', ()\<rparr>]" using 1 by blast
  hence "[v \<Turnstile> [\<^bold>\<lambda>x :: 'a. \<lparr>\<Pi>, ()\<rparr>] \<^bold>= [\<^bold>\<lambda>x. \<lparr>\<Pi>', ()\<rparr>]]"
    using AOT_nec_selfeq[of v "[\<^bold>\<lambda>x :: 'a. \<lparr>\<Pi>, ()\<rparr>]"] 1
    using AOT_boxS AOT_lambda_const_exists by blast
  thus "[v \<Turnstile> \<Pi>\<^bold>\<down> \<^bold>& \<Pi>'\<^bold>\<down> \<^bold>& [\<^bold>\<lambda>x :: 'a. \<lparr>\<Pi>, ()\<rparr>] \<^bold>= [\<^bold>\<lambda>x. \<lparr>\<Pi>', ()\<rparr>]]"
    apply AOT_meta_simp by (simp add: \<Pi>_ex \<Pi>'_ex)
next
  assume 0: "[v \<Turnstile> \<Pi>\<^bold>\<down> \<^bold>& \<Pi>'\<^bold>\<down> \<^bold>& [\<^bold>\<lambda>x :: 'a. \<lparr>\<Pi>, ()\<rparr>] \<^bold>= [\<^bold>\<lambda>x. \<lparr>\<Pi>', ()\<rparr>]]"
  hence "[v \<Turnstile> [\<^bold>\<lambda>x. \<lparr>\<Pi>, ()\<rparr>] \<^bold>= [\<^bold>\<lambda>x :: 'a. \<lparr>\<Pi>', ()\<rparr>]]" by AOT_meta_simp
  hence "[\<^bold>\<lambda>x :: 'a. \<lparr>\<Pi>, ()\<rparr>] = [\<^bold>\<lambda>x. \<lparr>\<Pi>', ()\<rparr>]"
    unfolding AOT_identity_relation_def using AOT_relation_identity
    by blast
  hence "\<And> x . Rep_relation [\<^bold>\<lambda>x :: 'a. \<lparr>\<Pi>, ()\<rparr>] x = Rep_relation [\<^bold>\<lambda>x. \<lparr>\<Pi>', ()\<rparr>] x"
    by auto
  hence "Rep_relation [\<^bold>\<lambda>x :: 'a. \<lparr>\<Pi>, ()\<rparr>] AOT_universal_encoder = Rep_relation [\<^bold>\<lambda>x :: 'a. \<lparr>\<Pi>', ()\<rparr>] AOT_universal_encoder"
    by simp
  hence 1: "\<And> s w . Rep_\<o> (Rep_relation [\<^bold>\<lambda>x :: 'a. \<lparr>\<Pi>, ()\<rparr>] AOT_universal_encoder) s w = Rep_\<o> (Rep_relation [\<^bold>\<lambda>x :: 'a. \<lparr>\<Pi>', ()\<rparr>] AOT_universal_encoder) s w"
    by simp
  {
    fix s w
    assume s_dj: "s = dj"
    have "Rep_\<o> (Rep_relation [\<^bold>\<lambda>x :: 'a. \<lparr>\<Pi>, ()\<rparr>] AOT_universal_encoder) s w = Rep_\<o> (Rep_relation [\<^bold>\<lambda>x :: 'a. \<lparr>\<Pi>', ()\<rparr>] AOT_universal_encoder) s w"
      using 1 by simp
    hence "Rep_\<o> \<lparr>\<Pi>, ()\<rparr> s w = Rep_\<o> \<lparr>\<Pi>', ()\<rparr> s w"
      unfolding AOT_lambda_def by (simp add: Abs_relation_inverse AOT_universal_encoder_exists Abs_\<o>_inverse s_dj) 
  }
  moreover {
    fix s w
    assume s_not_dj: "s \<noteq> dj"
    have "Rep_\<o> (Rep_relation [\<^bold>\<lambda>x :: 'a. \<lparr>\<Pi>, ()\<rparr>] AOT_universal_encoder) s w = Rep_\<o> (Rep_relation [\<^bold>\<lambda>x :: 'a. \<lparr>\<Pi>', ()\<rparr>] AOT_universal_encoder) s w"
      using 1 by simp
    moreover have "(\<exists>y :: 'a. [dw \<Turnstile> AOT_universal_encoder \<^bold>~ y])"
      using AOT_equiv_existsS AOT_universal_encoder_exists by blast
    ultimately have "Rep_\<o> \<lparr>\<Pi>, ()\<rparr> s w = Rep_\<o> \<lparr>\<Pi>', ()\<rparr> s w"
      unfolding AOT_lambda_def by (simp add: Abs_relation_inverse AOT_universal_encoder_exists Abs_\<o>_inverse s_not_dj) 
  }
  ultimately have "Rep_\<o> \<lparr>\<Pi>, ()\<rparr> = Rep_\<o> \<lparr>\<Pi>', ()\<rparr>" by blast 
  moreover have "AOT_meta_equiv \<Pi> \<Pi>"
    using "0" AOT_conjS AOT_logical_existsE by blast
  moreover have "AOT_meta_equiv \<Pi>' \<Pi>'"
    using "0" AOT_conjS AOT_logical_existsE by blast
  ultimately have "Rep_relation \<Pi> () = Rep_relation \<Pi>' ()" unfolding AOT_exe_def unfolding AOT_meta_equiv_unit_def
    by (simp add: Rep_\<o>_inject)
  hence "\<And> x . Rep_relation \<Pi> x = Rep_relation \<Pi>' x" by simp
  hence "\<Pi> = \<Pi>'" using Rep_relation_inject by blast
  thus "[v \<Turnstile> \<Pi> \<^bold>= \<Pi>']"
    unfolding AOT_identity_relation_def AOT_relation_identity_unit_def AOT_valid_in_def by (simp add: Abs_\<o>_inverse)
qed

end
