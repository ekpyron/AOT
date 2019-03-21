theory AOT_Instantiation
  imports AOT_Kappa
begin

typedecl \<omega>
typedecl \<sigma>

datatype \<upsilon> = \<omega>\<upsilon> \<omega> | \<sigma>\<upsilon> \<sigma>

type_synonym \<alpha> = "(\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool) set"

datatype \<nu> = \<omega>\<nu> \<omega> | \<alpha>\<nu> \<alpha>

axiomatization \<alpha>\<sigma> :: "\<alpha>\<Rightarrow>\<sigma>" where \<alpha>\<sigma>_surj: "surj \<alpha>\<sigma>"

primrec \<nu>\<upsilon> :: "\<nu>\<Rightarrow>\<upsilon>" where
  "\<nu>\<upsilon> (\<omega>\<nu> x) = \<omega>\<upsilon> x"
| "\<nu>\<upsilon> (\<alpha>\<nu> x) = \<sigma>\<upsilon> (\<alpha>\<sigma> x)"

typedef \<kappa> = "UNIV::(\<nu> option) set" ..

setup_lifting type_definition_\<kappa>

lift_definition \<kappa>\<upsilon> :: "\<kappa>\<Rightarrow>\<upsilon> option" is "\<lambda>x . map_option \<nu>\<upsilon> x" .

instantiation \<kappa> :: AOT_Term
begin
definition AOT_meta_equiv_\<kappa> :: "\<kappa> \<Rightarrow> \<kappa> \<Rightarrow> bool" where
  "AOT_meta_equiv_\<kappa> \<equiv> (\<lambda> x y . \<exists> o\<^sub>1 . \<kappa>\<upsilon> x = Some o\<^sub>1 \<and> \<kappa>\<upsilon> y = Some o\<^sub>1)"
instance proof
  show "part_equivp (AOT_meta_equiv :: \<kappa> \<Rightarrow> \<kappa> \<Rightarrow> bool)"
  proof (rule part_equivpI)
    show "\<exists>x :: \<kappa>. AOT_meta_equiv x x"
      apply (rule_tac x="Abs_\<kappa> (Some (\<omega>\<nu> x))" in exI)
      unfolding AOT_meta_equiv_\<kappa>_def apply transfer by simp
  next
    show "symp (AOT_meta_equiv :: \<kappa> \<Rightarrow> \<kappa> \<Rightarrow> bool)"
      apply (rule sympI) unfolding AOT_meta_equiv_\<kappa>_def by auto
  next
    show "transp (AOT_meta_equiv :: \<kappa> \<Rightarrow> \<kappa> \<Rightarrow> bool)"
      apply (rule transpI) unfolding AOT_meta_equiv_\<kappa>_def by auto
  qed
qed
end

axiomatization ConcreteInWorld :: "\<omega>\<Rightarrow>i\<Rightarrow>bool"
  where OrdinaryObjectsConcrete: "\<forall> x . \<exists> w . ConcreteInWorld x w"
    and PossiblyContingentObjectExists: "\<exists> x v . ConcreteInWorld x v \<and> \<not>ConcreteInWorld x dw"

lift_definition d\<Pi>' :: "\<kappa> relation \<Rightarrow> (\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool)" is
  "\<lambda> F u s w . \<exists> x . \<kappa>\<upsilon> x = Some u \<and> Rep_\<o> (Rep_relation (F) x) s w" .

lemma d\<Pi>'_prop_Aux: "\<exists>x. (\<exists>z. x = Some z \<and> \<nu>\<upsilon> z = u)"
  by (metis \<alpha>\<sigma>_surj \<nu>\<upsilon>.simps(1) \<nu>\<upsilon>.simps(2) \<upsilon>.exhaust surj_def)

lemma d\<Pi>'_prop: "\<exists> F . [dw \<Turnstile> F\<^bold>\<down>] \<and> r = d\<Pi>' F"
  unfolding d\<Pi>'_def apply (subst AOT_logical_existsS) unfolding AOT_logical_exists_def AOT_valid_in_def
  apply (simp add: Abs_\<o>_inverse)
  unfolding AOT_meta_equiv_relation_def
  apply simp unfolding AOT_meta_equiv_\<kappa>_def AOT_logical_exists_def AOT_valid_in_def
  apply (simp add: Abs_\<o>_inverse)
  unfolding \<kappa>\<upsilon>_def apply simp
  apply (rule_tac x="Abs_relation (\<lambda> x . Abs_\<o> (\<lambda> s w . (\<exists> u . \<kappa>\<upsilon> x = Some u) \<and> (\<forall> u . \<kappa>\<upsilon> x = Some u \<longrightarrow> r u s w)))" in exI)
  apply (simp add: Abs_relation_inverse Abs_\<o>_inverse)
  apply rule
  apply transfer
  apply auto[1]
  apply rule
  apply transfer
   apply auto[1]
  apply transfer apply simp apply (rule ext)+
  using d\<Pi>'_prop_Aux apply simp
  by fastforce

definition d\<Pi> :: "\<kappa> relation \<Rightarrow> (\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool) option" where
  "d\<Pi> \<equiv> (\<lambda> F . if [dw \<Turnstile> F\<^bold>\<down>] then Some (d\<Pi>' F) else None)"

lemma d\<Pi>_id:
  assumes "[v \<Turnstile> F\<^bold>\<down>]" and "[v \<Turnstile> G\<^bold>\<down>]" and "d\<Pi>' F = d\<Pi>' G"
  shows "F = G"
proof -
  {
    fix u :: \<upsilon> and s :: j and w :: i
    have "(\<exists>x. \<kappa>\<upsilon> x = Some u \<and> Rep_\<o> (Rep_relation F x) s w) = (\<exists>x. \<kappa>\<upsilon> x = Some u \<and> Rep_\<o> (Rep_relation G x) s w)"
      using assms(3) unfolding d\<Pi>'_def apply simp by meson
  } note 0=this

  {
    fix x y :: \<kappa>
    assume "[w \<Turnstile> x \<^bold>~ y]"
    hence "AOT_meta_equiv x y"
      using AOT_equivE by blast
    then obtain o\<^sub>1 where o\<^sub>1_prop: "\<kappa>\<upsilon> x = Some o\<^sub>1 \<and> \<kappa>\<upsilon> y = Some o\<^sub>1" unfolding AOT_meta_equiv_\<kappa>_def by auto
    have "Rep_\<o> (Rep_relation F x) = Rep_\<o> (Rep_relation G y)"
    proof ((rule ext)+, rule iffI) 
      fix s w
      assume "Rep_\<o> (Rep_relation F x) s w"
      hence "\<exists>x. \<kappa>\<upsilon> x = Some o\<^sub>1 \<and> Rep_\<o> (Rep_relation F x) s w" using o\<^sub>1_prop by blast
      hence "\<exists>x. \<kappa>\<upsilon> x = Some o\<^sub>1 \<and> Rep_\<o> (Rep_relation G x) s w" using 0 by blast
      thus "Rep_\<o> (Rep_relation G y) s w"
        by (metis AOT_logical_existsE AOT_meta_equiv_\<kappa>_def AOT_meta_equiv_relation.rep_eq assms(2) o\<^sub>1_prop)
    next
      fix s w
      assume "Rep_\<o> (Rep_relation G y) s w"
      hence "\<exists>x. \<kappa>\<upsilon> x = Some o\<^sub>1 \<and> Rep_\<o> (Rep_relation G x) s w" using o\<^sub>1_prop by blast
      hence "\<exists>x. \<kappa>\<upsilon> x = Some o\<^sub>1 \<and> Rep_\<o> (Rep_relation F x) s w" using 0 by blast
      thus "Rep_\<o> (Rep_relation F x) s w"
        by (metis AOT_logical_existsE AOT_meta_equiv_\<kappa>_def AOT_meta_equiv_relation.rep_eq assms(1) o\<^sub>1_prop)
    qed      
    hence "Rep_relation F x = Rep_relation G y"
      using Rep_\<o>_inject by blast
  } note 1=this

  show "F = G"
    apply (rule AOT_fun_equiv_equal[where v=w])
    apply (rule AOT_equiv_relI)
    using 1 apply simp
    using assms(1) apply (subst AOT_logical_existsS)
    using AOT_logical_existsE AOT_meta_equiv_relation.rep_eq apply blast
    using assms(2) apply (subst AOT_logical_existsS)
    using AOT_logical_existsE AOT_meta_equiv_relation.rep_eq by blast
qed

instantiation \<kappa> :: "AOT_Individual"
begin
lift_definition AOT_enc_\<kappa> :: "\<kappa> \<Rightarrow> (\<kappa> relation) \<Rightarrow> \<o>" is
  "\<lambda> x F s w . (\<exists> a r . x = Some (\<alpha>\<nu> a) \<and> (d\<Pi> F) = Some r \<and> r \<in> a)" .
lift_definition AOT_universal_encoder_\<kappa> :: "\<kappa>" is
  "Some (\<alpha>\<nu> UNIV)" .
definition AOT_relation_identity_\<kappa> :: "\<kappa> relation \<Rightarrow> \<kappa> relation \<Rightarrow> \<o>" where
  "AOT_relation_identity_\<kappa> \<equiv> (\<lambda> F G . F\<^bold>\<down> \<^bold>& G\<^bold>\<down> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>x. \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>x,G\<rbrace>))"
definition AOT_proj_enc_\<kappa> :: "\<kappa> \<Rightarrow> (\<kappa> \<Rightarrow> \<o>) \<Rightarrow> \<o>" where
  "AOT_proj_enc_\<kappa> \<equiv> \<lambda> x \<phi> . \<lbrace>x,[\<^bold>\<lambda>y . \<phi> y]\<rbrace>"

lemma \<kappa>\<upsilon>_ord: "\<kappa>\<upsilon> (Abs_\<kappa> (Some (\<omega>\<nu> x))) = Some (\<omega>\<upsilon> x)"
  by (simp add: \<kappa>\<upsilon>.abs_eq)

lemma universal_encoder_\<kappa>: "[v \<Turnstile> F\<^bold>\<down>] \<Longrightarrow> [v \<Turnstile> \<lbrace>AOT_universal_encoder :: \<kappa>, F\<rbrace>]"
 unfolding AOT_enc_\<kappa>_def AOT_universal_encoder_\<kappa>_def apply simp apply transfer
    apply (rule_tac x="UNIV" in exI) apply simp unfolding d\<Pi>_def
    apply (rule_tac x="d\<Pi>' F" in exI)
    by (simp add: AOT_logical_existsS) 
lemma enc_rigid_\<kappa>: "[v \<Turnstile> \<lbrace>x::\<kappa>, F\<rbrace>] = (\<forall>v. [v \<Turnstile> \<lbrace>x, F\<rbrace>])"
  unfolding AOT_enc_\<kappa>_def apply transfer by simp
lemma enc_\<kappa>_impl_exist:
  assumes "[v \<Turnstile> \<lbrace>x::\<kappa>,F\<rbrace>]"
  shows "[v \<Turnstile> x\<^bold>\<down>] \<and> [v \<Turnstile> F\<^bold>\<down>]"
  using assms apply - apply (subst AOT_logical_existsS)
  unfolding AOT_enc_\<kappa>_def d\<Pi>_def apply simp apply transfer
  by (metis AOT_logical_existsS AOT_meta_equiv_\<kappa>_def Rep_\<kappa>_inverse \<kappa>\<upsilon>.abs_eq option.simps(3) option.simps(9))

instance proof
  fix v
  show "[v \<Turnstile> (AOT_universal_encoder :: \<kappa>)\<^bold>\<down>]"
    apply (rule AOT_logical_existsI)
    unfolding AOT_universal_encoder_\<kappa>_def AOT_meta_equiv_\<kappa>_def
    apply transfer by simp
next
  fix v :: i and F :: "\<kappa> relation"
  assume "[v \<Turnstile> F\<^bold>\<down>]"
  thus "[v \<Turnstile> \<lbrace>AOT_universal_encoder, F\<rbrace>]"
    using universal_encoder_\<kappa> by auto
next
  fix v :: i and F G :: "\<kappa> relation"
  {
    obtain x where x_def: "x = Abs_\<kappa> (Some (\<alpha>\<nu> { H . H = d\<Pi>' F}))" by auto
    have x_ex: "[v \<Turnstile> x\<^bold>\<down>]" apply (rule AOT_logical_existsI) unfolding AOT_meta_equiv_\<kappa>_def x_def
      by (simp add: \<kappa>\<upsilon>.abs_eq)
    assume "[v \<Turnstile> F \<^bold>=\<^sub>r G]"
    hence id_def: "[v \<Turnstile> F\<^bold>\<down> \<^bold>& G\<^bold>\<down> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>x. \<lbrace>x, F\<rbrace> \<^bold>\<equiv> \<lbrace>x, G\<rbrace>)]" unfolding AOT_relation_identity_\<kappa>_def by auto
    hence "\<And> x . [v \<Turnstile> x\<^bold>\<down>] \<Longrightarrow> [v \<Turnstile> \<lbrace>x, F\<rbrace> \<^bold>\<equiv> \<lbrace>x, G\<rbrace>]" by AOT_meta_simp
    hence x_enc_F_is_x_enc_G: "[v \<Turnstile> \<lbrace>x, F\<rbrace>] = [v \<Turnstile> \<lbrace>x, G\<rbrace>]" using x_ex by AOT_meta_simp
    have G_ex: "[dw \<Turnstile> G\<^bold>\<down>]" using id_def
      by (simp add: AOT_conjS AOT_logical_existsS)
    have F_ex: "[dw \<Turnstile> F\<^bold>\<down>]" using id_def
      by (simp add: AOT_conjS AOT_logical_existsS)
    hence x_en_F: "[v \<Turnstile> \<lbrace>x,F\<rbrace>]"
      unfolding AOT_enc_\<kappa>_def x_def d\<Pi>_def
      by (simp add: Abs_\<kappa>_inverse AOT_valid_in.abs_eq)
    hence "[v \<Turnstile> \<lbrace>x,G\<rbrace>]" using x_enc_F_is_x_enc_G by auto
    hence "d\<Pi>' G = d\<Pi>' F"
      unfolding AOT_enc_\<kappa>_def x_def d\<Pi>_def
      by (simp add: G_ex Abs_\<kappa>_inverse AOT_valid_in.abs_eq)
    hence "G = F" using F_ex G_ex d\<Pi>_id by presburger
    hence "[v \<Turnstile> F\<^bold>\<down>] \<and> [v \<Turnstile> G\<^bold>\<down>] \<and> F = G" using id_def by AOT_meta_simp
  }
  moreover {
    assume "[v \<Turnstile> F\<^bold>\<down>] \<and> [v \<Turnstile> G\<^bold>\<down>] \<and> F = G"
    hence "[v \<Turnstile> F \<^bold>=\<^sub>r G]"
      unfolding AOT_relation_identity_\<kappa>_def by AOT_meta_auto
  }
  ultimately show "[v \<Turnstile> F \<^bold>=\<^sub>r G] = ([v \<Turnstile> F\<^bold>\<down>] \<and> [v \<Turnstile> G\<^bold>\<down>] \<and> F = G)" by auto
next
  fix v :: i and x :: \<kappa> and F :: "\<kappa> relation"
  show "[v \<Turnstile> \<lbrace>x, F\<rbrace>] = (\<forall>v. [v \<Turnstile> \<lbrace>x, F\<rbrace>])"
    unfolding AOT_enc_\<kappa>_def apply transfer by simp
next
  fix v :: i and x :: \<kappa> and F :: "\<kappa> relation"
  assume "[v \<Turnstile> \<lbrace>x,F\<rbrace>]"
  thus "[v \<Turnstile> x\<^bold>\<down>] \<and> [v \<Turnstile> F\<^bold>\<down>]"
   using enc_\<kappa>_impl_exist by auto
next
  fix \<phi> :: "\<kappa> \<Rightarrow> \<o>" and v :: i
  assume "\<And>v x y. [v \<Turnstile> x \<^bold>~ y] \<Longrightarrow> [v \<Turnstile> \<phi> x] = [v \<Turnstile> \<phi> y]"
  hence "[v \<Turnstile> [\<^bold>\<lambda>y . \<phi> y]\<^bold>\<down>]"
    by (rule AOT_lambda_existsI)
  thus "[v \<Turnstile> AOT_proj_enc (AOT_universal_encoder::\<kappa>) \<phi>]"
    unfolding AOT_proj_enc_\<kappa>_def 
    using  universal_encoder_\<kappa> by auto
next
  fix v va :: i and x :: \<kappa> and \<phi> :: "\<kappa>\<Rightarrow>\<o>"
  assume "[v \<Turnstile> AOT_proj_enc x \<phi>]"
  thus "[va \<Turnstile> AOT_proj_enc x \<phi>]"
    unfolding AOT_proj_enc_\<kappa>_def using enc_rigid_\<kappa>
    by blast
next
  fix v :: i and x :: \<kappa> and \<phi> :: "\<kappa>\<Rightarrow>\<o>"
  show "[v \<Turnstile> AOT_proj_enc x \<phi>] \<Longrightarrow> [v \<Turnstile> x\<^bold>\<down>]"
    unfolding AOT_proj_enc_\<kappa>_def
   using enc_\<kappa>_impl_exist by auto
qed
end

instantiation \<kappa> :: "AOT_UnaryIndividual"
begin
definition AOT_concrete_\<kappa> :: "\<kappa> relation" where
  "AOT_concrete_\<kappa> \<equiv> Abs_relation (\<lambda> x . Abs_\<o> (\<lambda>s w . \<exists> u . \<kappa>\<upsilon> x = Some (\<omega>\<upsilon> u) \<and> ConcreteInWorld u w))"
lemma \<kappa>_Concrete_exists: shows "[v \<Turnstile> (E! :: \<kappa> relation)\<^bold>\<down>]"
    apply (rule AOT_exists_relI)
    unfolding AOT_concrete_\<kappa>_def apply (simp add: Abs_relation_inverse)
    apply (drule AOT_equivE) unfolding AOT_meta_equiv_\<kappa>_def
    apply auto[1]
    apply (simp add: Abs_relation_inverse) apply (subst AOT_logical_existsS) unfolding AOT_meta_equiv_\<kappa>_def AOT_nec_false_def
    apply transfer apply simp
    by (meson AOT_meta_equiv_\<kappa>_def)
instance proof
  fix v
  show "[v \<Turnstile> (E! :: \<kappa> relation)\<^bold>\<down>]" using \<kappa>_Concrete_exists by auto
next
  fix v :: i and x :: \<kappa> and F :: "\<kappa> relation"
  assume "[v \<Turnstile> \<lparr>E!, x\<rparr>]"
  hence "\<exists>u. \<kappa>\<upsilon> x = Some (\<omega>\<upsilon> u) \<and> ConcreteInWorld u v"
    unfolding AOT_concrete_\<kappa>_def
    apply - apply (drule AOT_exeE3)
    apply (simp add: Abs_relation_inverse) apply transfer by simp
  thus "\<not> [v \<Turnstile> \<lbrace>x, F\<rbrace>]"
    unfolding AOT_enc_\<kappa>_def apply simp apply transfer
    by auto
next
  obtain u :: \<omega> and v :: i where "ConcreteInWorld u v"
    using OrdinaryObjectsConcrete by blast
  hence "[v \<Turnstile> \<lparr>E!, Abs_\<kappa> (Some (\<omega>\<nu> u))\<rparr>]"
    apply - apply (rule AOT_exeI)
    apply (simp add: \<kappa>_Concrete_exists)
    apply (simp add: AOT_logical_existsI AOT_meta_equiv_\<kappa>_def \<kappa>\<upsilon>.abs_eq)
    unfolding AOT_concrete_\<kappa>_def
    apply (simp add: Abs_relation_inverse) apply transfer by simp
  thus "\<exists> (x :: \<kappa>) v . [v \<Turnstile> \<lparr>E!, x\<rparr>]" by blast
next
  fix \<phi> :: "\<kappa> relation \<Rightarrow> \<o>" and v
  obtain a where a_def: "a = Abs_\<kappa> (Some (\<alpha>\<nu> { H . \<forall> F . d\<Pi> F = Some H \<longrightarrow> [v \<Turnstile> \<phi> F]}))" by auto
  have a_ex: "[v \<Turnstile> a\<^bold>\<down>]"
    apply (rule AOT_logical_existsI) unfolding a_def AOT_meta_equiv_\<kappa>_def
    apply transfer by simp
  have "[v \<Turnstile> [\<^bold>\<lambda>y :: \<kappa>. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!, y\<rparr>]\<^bold>\<down>]"
    by (fast intro: AOT_lambda_exists_intros \<kappa>_Concrete_exists)
  have "[v \<Turnstile> \<lparr>[\<^bold>\<lambda>y. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!, y\<rparr>], a\<rparr>]"
    apply (rule AOT_exeI)
    apply (fast intro: AOT_lambda_exists_intros \<kappa>_Concrete_exists)
    using a_ex apply simp
    apply (rule AOT_lambda_applyI)
    unfolding AOT_concrete_\<kappa>_def apply AOT_meta_simp
    apply (simp add: Abs_relation_inverse AOT_valid_in.abs_eq) unfolding a_def
     apply (simp add: \<kappa>\<upsilon>.abs_eq)
    using a_ex unfolding a_def by simp
  moreover have "[v \<Turnstile> (\<^bold>\<forall>F . \<lbrace>a,F\<rbrace> \<^bold>\<equiv> \<phi> F)]" apply AOT_meta_simp
    unfolding AOT_enc_\<kappa>_def a_def apply (simp add: Abs_\<kappa>_inverse AOT_valid_in.abs_eq)
    by (metis AOT_logical_existsS d\<Pi>_def d\<Pi>_id option.distinct(1) option.sel)
  ultimately show "[v \<Turnstile> \<^bold>\<exists>x. \<lparr>[\<^bold>\<lambda>y. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!, y\<rparr>], x\<rparr> \<^bold>& (\<^bold>\<forall>F. \<lbrace>x, F\<rbrace> \<^bold>\<equiv> \<phi> F)]" by AOT_meta_auto
next
  fix v :: i and F G :: "\<kappa> relation"
  show "(F \<^bold>=\<^sub>r G) = (F\<^bold>\<down> \<^bold>& G\<^bold>\<down> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>x. \<lbrace>x, F\<rbrace> \<^bold>\<equiv> \<lbrace>x, G\<rbrace>))"
    unfolding AOT_relation_identity_\<kappa>_def by blast
(*  show "[v \<Turnstile> F \<^bold>=\<^sub>r G] = [v \<Turnstile> F\<^bold>\<down> \<^bold>& G\<^bold>\<down> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>x. \<lbrace>x, F\<rbrace> \<^bold>\<equiv> \<lbrace>x, G\<rbrace>)]"
    unfolding AOT_relation_identity_\<kappa>_def by blast*)
next
  fix v
  obtain x :: \<omega> and w\<^sub>1 where prop1: "ConcreteInWorld x w\<^sub>1 \<and> \<not>ConcreteInWorld x dw"
    using PossiblyContingentObjectExists by blast
  have ord_concrete: "\<And> x v . [v \<Turnstile> Rep_relation E! (Abs_\<kappa> (Some (\<omega>\<nu> x)))] = ConcreteInWorld x v"
    unfolding AOT_concrete_\<kappa>_def AOT_valid_in_def by (simp add: Abs_relation_inverse Abs_\<o>_inverse \<kappa>\<upsilon>_ord)
  have ord_ex: "\<And> v x . [v \<Turnstile> Abs_\<kappa> (Some (\<omega>\<nu> x))\<^bold>\<down>]"
    by (simp add: AOT_logical_existsI AOT_meta_equiv_\<kappa>_def \<kappa>\<upsilon>_ord)
  show "[v \<Turnstile> \<^bold>\<diamond>(\<^bold>\<exists>x :: \<kappa>. \<lparr>E!, x\<rparr> \<^bold>& \<^bold>\<not>\<^bold>\<A>\<lparr>E!, x\<rparr>)]"
    apply AOT_meta_simp
    apply (rule_tac x=w\<^sub>1 in exI)
     apply (rule_tac x="Abs_\<kappa> (Some (\<omega>\<nu> x))" in exI)
    by (simp add: \<kappa>_Concrete_exists ord_concrete prop1 ord_ex)
next
  fix x :: \<kappa> and \<phi> :: "\<kappa>\<Rightarrow>\<o>"
  show "AOT_proj_enc x \<phi> = \<lbrace>x, AOT_lambda \<phi>\<rbrace>"
    unfolding AOT_proj_enc_\<kappa>_def by auto
qed
end

instantiation \<kappa> :: AOT_Identity
begin
definition AOT_identity_\<kappa> :: "\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<o>" where "AOT_identity_\<kappa> \<equiv> \<lambda> x y . x \<^bold>=\<^sub>E y \<^bold>\<or> \<lparr>A!,x\<rparr> \<^bold>& \<lparr>A!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F . \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>y,F\<rbrace>)"

lemma \<kappa>_abstract_\<alpha>:
  shows "[v \<Turnstile> \<lparr>A!,x\<rparr>] = (\<exists> a . x = Abs_\<kappa> (Some (\<alpha>\<nu> a)))"
proof -
  have 2: "[v \<Turnstile> \<lparr>A!,x\<rparr>] = ([v \<Turnstile> x\<^bold>\<down>] \<and> [v \<Turnstile> \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<rparr>])"
    apply (rule iffI) unfolding AOT_Abstract_def using AOT_beta1 using AOT_beta2 using AOT_exeS apply blast
    by (metis AOT_Abstract_def AOT_Abstract_exists AOT_exeS AOT_lambda_applyI)
  also have 5: "... = (\<forall> v . [v \<Turnstile> x\<^bold>\<down>] \<and> \<not> [v \<Turnstile> (\<lambda>x. Abs_\<o> (\<lambda>s w. \<exists>u. \<kappa>\<upsilon> x = Some (\<omega>\<upsilon> u) \<and> ConcreteInWorld u w)) x])"
    apply AOT_meta_simp using AOT_concrete_exists[where 'a=\<kappa>] unfolding AOT_concrete_\<kappa>_def
    apply (simp add: Abs_relation_inverse)
    using AOT_exists_necI by blast
  also have 6: "... = ((\<exists>o\<^sub>1. \<kappa>\<upsilon> x = Some o\<^sub>1 \<and> \<kappa>\<upsilon> x = Some o\<^sub>1) \<and> \<not>(\<exists> u . \<kappa>\<upsilon> x = Some (\<omega>\<upsilon> u)))"
    apply (subst AOT_logical_existsS)
    unfolding AOT_meta_equiv_\<kappa>_def
    apply transfer using OrdinaryObjectsConcrete by auto
  also have 8: "... = (\<exists> a . x = Abs_\<kappa> (Some (\<alpha>\<nu> a)))"
    apply transfer apply simp
    by (metis \<nu>.exhaust \<nu>\<upsilon>.simps(1) \<nu>\<upsilon>.simps(2) \<upsilon>.distinct(1) option.sel)
  finally show ?thesis by auto
qed

instance proof
  fix v :: i and x y :: \<kappa> and \<phi> :: "\<kappa>\<Rightarrow>\<o>"
  assume "[v \<Turnstile> x \<^bold>= y]"
  moreover {
    assume "[v \<Turnstile> x \<^bold>=\<^sub>E y]"
    hence "[v \<Turnstile> \<lparr>[\<^bold>\<lambda>(x, y). \<lparr>O!, x\<rparr> \<^bold>& \<lparr>O!, y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F. \<lparr>F, x\<rparr> \<^bold>\<equiv> \<lparr>F, y\<rparr>)], (x, y)\<rparr>]"
      unfolding AOT_identity\<^sub>E_infix_def AOT_identity\<^sub>E_def by auto
    hence 1: "[v \<Turnstile> \<lparr>O!, x\<rparr> \<^bold>& \<lparr>O!, y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F. \<lparr>F, x\<rparr> \<^bold>\<equiv> \<lparr>F, y\<rparr>)]" using AOT_beta1[where x="(x,y)"]
    proof -
      have "[v \<Turnstile> case (x, y) of (k, ka) \<Rightarrow> \<lparr>O!, k\<rparr> \<^bold>& \<lparr>O!, ka\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>r. \<lparr>r, k\<rparr> \<^bold>\<equiv> \<lparr>r, ka\<rparr>)]"
        using \<open>[v \<Turnstile> \<lparr>[\<^bold>\<lambda>(x, y) . \<lparr>O!, x\<rparr> \<^bold>& \<lparr>O!, y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F. \<lparr>F, x\<rparr> \<^bold>\<equiv> \<lparr>F, y\<rparr>)], (x, y)\<rparr>]\<close> \<open>\<And>v \<phi>. [v \<Turnstile> \<lparr>AOT_lambda \<phi>, (x, y)\<rparr>] \<Longrightarrow> [v \<Turnstile> \<phi> (x, y)]\<close> by blast
      then show ?thesis
        by fastforce
    qed
    have 2: "[v \<Turnstile> \<lparr>O!,x\<rparr>]" using 1 by AOT_meta_simp
    hence "[v \<Turnstile> \<^bold>\<diamond>\<lparr>E!,x\<rparr>]" unfolding AOT_Ordinary_def using AOT_beta1 by auto
    hence "\<exists> u . \<kappa>\<upsilon> x = Some (\<omega>\<upsilon> u)" apply AOT_meta_simp unfolding AOT_concrete_\<kappa>_def
      by (auto simp: Abs_relation_inverse AOT_valid_in.abs_eq)
    then obtain u\<^sub>1 where u\<^sub>1_prop: "\<kappa>\<upsilon> x = Some (\<omega>\<upsilon> u\<^sub>1)" by auto
    have "[v \<Turnstile> \<lparr>O!,y\<rparr>]" using 1 by AOT_meta_simp
    hence "[v \<Turnstile> \<^bold>\<diamond>\<lparr>E!,y\<rparr>]" unfolding AOT_Ordinary_def using AOT_beta1 by auto
    hence "\<exists> u . \<kappa>\<upsilon> y = Some (\<omega>\<upsilon> u)" apply AOT_meta_simp unfolding AOT_concrete_\<kappa>_def
      by (auto simp: Abs_relation_inverse AOT_valid_in.abs_eq)
    then obtain u\<^sub>2 where u\<^sub>2_prop: "\<kappa>\<upsilon> y = Some (\<omega>\<upsilon> u\<^sub>2)" by auto
    have "\<And> v F . [v \<Turnstile> F\<^bold>\<down>] \<Longrightarrow> [v \<Turnstile> \<lparr>F,x\<rparr>] = [v \<Turnstile> \<lparr>F,y\<rparr>]" using 1 by AOT_meta_auto
    moreover have 3: "[v \<Turnstile> (Abs_relation (\<lambda> x . Abs_\<o> (\<lambda> s w . \<kappa>\<upsilon> x = Some (\<omega>\<upsilon> u\<^sub>1))))\<^bold>\<down>]"
      apply (rule AOT_exists_relI)
       apply (simp add: Abs_relation_inverse)+
      apply (drule AOT_equivE)
      unfolding AOT_meta_equiv_\<kappa>_def
       apply auto[1]
      apply (simp add: Abs_relation_inverse) apply (subst AOT_logical_existsS)
      unfolding AOT_meta_equiv_\<kappa>_def AOT_logical_exists_def AOT_valid_in_def AOT_nec_false_def
      apply (simp add: Abs_\<o>_inverse)
      by (meson AOT_meta_equiv_\<kappa>_def)
    moreover have "[v \<Turnstile> \<lparr>Abs_relation (\<lambda> x . Abs_\<o> (\<lambda> s w . \<kappa>\<upsilon> x = Some (\<omega>\<upsilon> u\<^sub>1))), x\<rparr>]"
      apply (rule AOT_exeI) using 3 apply simp using 2[THEN AOT_exeE2] apply simp
      apply (simp add: Abs_relation_inverse) using u\<^sub>1_prop apply transfer by simp
    ultimately have "[v \<Turnstile> \<lparr>Abs_relation (\<lambda> x . Abs_\<o> (\<lambda> s w . \<kappa>\<upsilon> x = Some (\<omega>\<upsilon> u\<^sub>1))), y\<rparr>]" by blast
    hence "\<kappa>\<upsilon> y = Some (\<omega>\<upsilon> u\<^sub>1)"
      apply - apply (drule AOT_exeE3)
      apply (simp add: Abs_relation_inverse)
      apply transfer by simp
    hence "x = y" using u\<^sub>1_prop apply transfer apply simp
      by (metis \<nu>.exhaust \<nu>\<upsilon>.simps(1) \<nu>\<upsilon>.simps(2) \<upsilon>.distinct(2) \<upsilon>.inject(1))
  }
  moreover {
    assume 1: "[v \<Turnstile> \<lparr>A!,x\<rparr> \<^bold>& \<lparr>A!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F . \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>y,F\<rbrace>)]"
    have "[v \<Turnstile> \<lparr>A!,x\<rparr>]" using 1 by AOT_meta_auto
    then obtain a where x_def: "x = Abs_\<kappa> (Some (\<alpha>\<nu> a))" using \<kappa>_abstract_\<alpha> by auto
    have "[v \<Turnstile> \<lparr>A!,y\<rparr>]" using 1 by AOT_meta_auto
    then obtain b where y_def: "y = Abs_\<kappa> (Some (\<alpha>\<nu> b))" using \<kappa>_abstract_\<alpha> by auto
    hence "\<And> F . [dw \<Turnstile> F\<^bold>\<down>] \<Longrightarrow> [dw \<Turnstile> \<lbrace>x,F\<rbrace>] = [dw \<Turnstile> \<lbrace>y,F\<rbrace>]" using 1 by AOT_meta_auto
    hence "\<And>F. [dw \<Turnstile> F\<^bold>\<down>] \<Longrightarrow> (d\<Pi>' F \<in> a) = (d\<Pi>' F \<in> b)"
      unfolding x_def y_def AOT_enc_\<kappa>_def AOT_valid_in_def d\<Pi>_def
      by (simp add: Abs_\<o>_inverse Abs_\<kappa>_inverse)
    hence "\<And> r . (r \<in> a) = (r \<in> b)" using d\<Pi>'_prop
      by metis
    hence "a = b" by blast
    hence "x = y" unfolding x_def y_def apply transfer by auto
  }
  ultimately have "x = y" unfolding AOT_identity_\<kappa>_def by AOT_meta_auto
  moreover assume "[v \<Turnstile> \<phi> x]"
  ultimately show "[v \<Turnstile> \<phi> y]" by auto
next
  fix v :: i and x y :: \<kappa>
  assume "[v \<Turnstile> x \<^bold>= y]"
  moreover {
    assume "[v \<Turnstile> x \<^bold>=\<^sub>E y]"
    hence "[v \<Turnstile> \<lparr>[\<^bold>\<lambda>(x, y). \<lparr>O!, x\<rparr> \<^bold>& \<lparr>O!, y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F. \<lparr>F, x\<rparr> \<^bold>\<equiv> \<lparr>F, y\<rparr>)], (x, y)\<rparr>]"
      unfolding AOT_identity\<^sub>E_infix_def AOT_identity\<^sub>E_def by auto
    hence 1: "[v \<Turnstile> \<lparr>O!, x\<rparr> \<^bold>& \<lparr>O!, y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F. \<lparr>F, x\<rparr> \<^bold>\<equiv> \<lparr>F, y\<rparr>)]" using AOT_beta1[where x="(x,y)"]
    proof -
      have "[v \<Turnstile> case (x, y) of (k, ka) \<Rightarrow> \<lparr>O!, k\<rparr> \<^bold>& \<lparr>O!, ka\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>r. \<lparr>r, k\<rparr> \<^bold>\<equiv> \<lparr>r, ka\<rparr>)]"
        using \<open>[v \<Turnstile> \<lparr>[\<^bold>\<lambda>(x, y) . \<lparr>O!, x\<rparr> \<^bold>& \<lparr>O!, y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F. \<lparr>F, x\<rparr> \<^bold>\<equiv> \<lparr>F, y\<rparr>)], (x, y)\<rparr>]\<close> \<open>\<And>v \<phi>. [v \<Turnstile> \<lparr>AOT_lambda \<phi>, (x, y)\<rparr>] \<Longrightarrow> [v \<Turnstile> \<phi> (x, y)]\<close> by blast
      then show ?thesis
        by fastforce
    qed
    have "[v \<Turnstile> x\<^bold>\<down>] \<and> [v \<Turnstile> y\<^bold>\<down>]" using 1
      using AOT_exeE2 AOT_conjE by blast
  }
  moreover {
    assume 1: "[v \<Turnstile> \<lparr>A!,x\<rparr> \<^bold>& \<lparr>A!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F . \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>y,F\<rbrace>)]"
    have "[v \<Turnstile> x\<^bold>\<down>] \<and> [v \<Turnstile> y\<^bold>\<down>]" using 1
      using AOT_exeE2 AOT_conjE by blast
  }
  ultimately show "[v \<Turnstile> x\<^bold>\<down>] \<and> [v \<Turnstile> y\<^bold>\<down>]" unfolding AOT_identity_\<kappa>_def
    using AOT_disjE by blast
next
  fix v and x :: \<kappa>
  assume 1: "[v \<Turnstile> x\<^bold>\<down>]"
  {
    fix w
    have 2: "[w \<Turnstile> x\<^bold>\<down>]"
      using "1" AOT_exists_necI by auto
    hence "\<exists> u . \<kappa>\<upsilon> x = Some u"
      by (meson AOT_logical_existsE AOT_meta_equiv_\<kappa>_def)
    moreover {
      assume "\<exists> u . \<kappa>\<upsilon> x = Some (\<omega>\<upsilon> u)"
      hence "[w \<Turnstile> \<^bold>\<diamond>\<lparr>E!, x\<rparr>]" apply AOT_meta_simp
        apply (simp add: AOT_concrete_exists AOT_exists_necI[OF 1])
        unfolding AOT_concrete_\<kappa>_def
        apply (simp add: Abs_relation_inverse AOT_valid_in_def Abs_\<o>_inverse)
        using OrdinaryObjectsConcrete by blast
      hence "[w \<Turnstile> \<lparr>[\<^bold>\<lambda>y. \<^bold>\<diamond>\<lparr>E!, y\<rparr>],x\<rparr>]"
        by (metis "2" AOT_Ordinary_def AOT_Ordinary_exists AOT_beta2)
      hence "[w \<Turnstile> \<lparr>O!,x\<rparr>]"
        unfolding AOT_Ordinary_def
        using AOT_eta[symmetric, OF AOT_Ordinary_exists, unfolded AOT_Ordinary_def]
        by blast
      hence "[w \<Turnstile> \<lparr>O!, x\<rparr> \<^bold>& \<lparr>O!, x\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F. \<lparr>F, x\<rparr> \<^bold>\<equiv> \<lparr>F, x\<rparr>)]"
        by AOT_meta_simp
      moreover have id\<^sub>E_ex: "[w \<Turnstile> [\<^bold>\<lambda>(x, y). \<lparr>O!, x\<rparr> \<^bold>& \<lparr>O!, y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F. \<lparr>F, x\<rparr> \<^bold>\<equiv> \<lparr>F, y\<rparr>)]\<^bold>\<down>]"
        by (metis (mono_tags, lifting) AOT_identity\<^sub>E_def AOT_identity\<^sub>E_exists)
      ultimately have "[w \<Turnstile> \<lparr>AOT_identity\<^sub>E, (x, x)\<rparr>]" unfolding AOT_identity\<^sub>E_def
        using AOT_beta2[of w "(x,x)", OF AOT_exists_prodI[of w x x, OF 2, OF 2],
            where \<phi> = "(\<lambda> (x,y) . \<lparr>O!, x\<rparr> \<^bold>& \<lparr>O!, y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F. \<lparr>F, x\<rparr> \<^bold>\<equiv> \<lparr>F, y\<rparr>))"]
        apply simp
        by blast
      hence "[w \<Turnstile> x \<^bold>=\<^sub>E x]" unfolding AOT_identity\<^sub>E_infix_def by simp
      hence "[w \<Turnstile> x \<^bold>= x]" unfolding AOT_identity_\<kappa>_def by AOT_meta_simp
    }
    moreover {
      assume "\<exists> u . \<kappa>\<upsilon> x = Some (\<sigma>\<upsilon> u)"
      hence "\<exists> a . x = Abs_\<kappa> (Some (\<alpha>\<nu> a))"
        apply transfer apply simp
        by (metis \<nu>.exhaust \<nu>\<upsilon>.simps(1) \<upsilon>.distinct(1))
      hence "[w \<Turnstile> \<lparr>A!,x\<rparr>]"
        by (simp add: \<kappa>_abstract_\<alpha>)
      hence "[w \<Turnstile> \<lparr>A!, x\<rparr> \<^bold>& \<lparr>A!, x\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F. \<lbrace>x, F\<rbrace> \<^bold>\<equiv> \<lbrace>x, F\<rbrace>)]"
        by AOT_meta_simp
      hence "[w \<Turnstile> x \<^bold>= x]" unfolding AOT_identity_\<kappa>_def by AOT_meta_simp
    }
    ultimately have "[w \<Turnstile> x \<^bold>= x]"
      by (metis \<upsilon>.exhaust)
  }
  thus "[v \<Turnstile> \<^bold>\<box>(x \<^bold>= x)]"
    by (simp add: AOT_boxI)
qed
end

instantiation \<kappa> :: AOT_UnaryIndividualIdentity
begin
definition AOT_that_\<kappa> :: "(\<kappa> \<Rightarrow> \<o>) \<Rightarrow> \<kappa>" where
  "AOT_that_\<kappa> \<equiv> \<lambda> \<phi> . if (\<exists>! x . [dw \<Turnstile> x\<^bold>\<down>] \<and> [dw \<Turnstile> \<phi> x]) then (THE x . [dw \<Turnstile> x\<^bold>\<down>] \<and> [dw \<Turnstile> \<phi> x]) else (Abs_\<kappa> None)"
lemma \<kappa>_that_exists_unique: "[v \<Turnstile> (\<^bold>\<iota>x. \<phi> x)\<^bold>\<down>] = (\<exists>!x :: \<kappa>. [dw \<Turnstile> x\<^bold>\<down>] \<and> [dw \<Turnstile> \<phi> x])"
    unfolding AOT_that_\<kappa>_def apply (simp add: AOT_valid_in.abs_eq)
    apply rule
     apply transfer apply (subst AOT_logical_existsS)+
     apply simp
    apply (metis (no_types, lifting) theI2)
    by (metis AOT_logical_existsE AOT_meta_equiv_\<kappa>_def \<kappa>\<upsilon>.abs_eq option.distinct(1) option.simps(8))
instance proof
  fix v and x y :: \<kappa>
  show "(x \<^bold>= y) = (x \<^bold>=\<^sub>E y \<^bold>\<or> \<lparr>A!, x\<rparr> \<^bold>& \<lparr>A!, y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F. \<lbrace>x, F\<rbrace> \<^bold>\<equiv> \<lbrace>y, F\<rbrace>))"
    unfolding AOT_identity_\<kappa>_def by auto
(*  show "[v \<Turnstile> x \<^bold>= y] = [v \<Turnstile> x \<^bold>=\<^sub>E y \<^bold>\<or> \<lparr>A!, x\<rparr> \<^bold>& \<lparr>A!, y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F. \<lbrace>x, F\<rbrace> \<^bold>\<equiv> \<lbrace>y, F\<rbrace>)]"
    unfolding AOT_identity_\<kappa>_def by auto*)
next
  fix v :: i and x :: \<kappa> and \<phi> :: "\<kappa>\<Rightarrow>\<o>"
  assume x_ex: "[v \<Turnstile> x\<^bold>\<down>]"
  show "[v \<Turnstile> x \<^bold>= (\<^bold>\<iota>x. \<phi> x) \<^bold>\<equiv> (\<^bold>\<forall>z. \<^bold>\<A>\<phi> z \<^bold>\<equiv> z \<^bold>= x)]"
  proof (rule AOT_iffI)
    assume 1: "[v \<Turnstile> x \<^bold>= (\<^bold>\<iota>x. \<phi> x)]"
    have 2: "x = (\<^bold>\<iota>x. \<phi> x)" using AOT_l_identity[of v x "\<^bold>\<iota>x. \<phi> x" "\<lambda> y . Abs_\<o> (\<lambda>s w . x = y)", OF 1]
      apply transfer by simp
    moreover have "x \<noteq> Abs_\<kappa> None" using x_ex
      by (metis (mono_tags, hide_lams) AOT_non_exist_non_eq AOT_that_\<kappa>_def Abs_\<kappa>_inverse UNIV_I \<kappa>_that_exists_unique option.distinct(1))
    ultimately have x_def: "x = (THE x. [dw \<Turnstile> x\<^bold>\<down>] \<and> [dw \<Turnstile> \<phi> x])" and ex_unique: "\<exists>!x. [dw \<Turnstile> x\<^bold>\<down>] \<and> [dw \<Turnstile> \<phi> x]"
      unfolding AOT_that_\<kappa>_def by presburger+
    {
      fix z :: \<kappa>
      assume "[v \<Turnstile> z\<^bold>\<down>]"
      hence z_ex: "[dw \<Turnstile> z\<^bold>\<down>]"
        by (simp add: AOT_logical_existsS)
      {
        assume "[dw \<Turnstile> \<phi> z]"
        hence "z = x" using z_ex x_def ex_unique
          by (metis (no_types, lifting) the_equality)
        hence "[dw \<Turnstile> z \<^bold>= x]"
          using "1" AOT_eq_nec 2 by blast
      }
      moreover {
        assume "[dw \<Turnstile> z \<^bold>= x]"
        hence "[dw \<Turnstile> x \<^bold>= z]"
          using AOT_l_identity[of dw z x "\<lambda> y . y \<^bold>= z"]
          using AOT_boxE AOT_nec_selfeq z_ex by blast
        moreover have "[dw \<Turnstile> \<phi> x]"
          using x_def ex_unique theI'[of "\<lambda> x . [dw \<Turnstile> x \<^bold>\<down>] \<and> [dw \<Turnstile> \<phi> x]"] by fast
        ultimately have "[dw \<Turnstile> \<phi> z]" using AOT_l_identity[of dw x z \<phi>] by simp
      }
      ultimately have "[dw \<Turnstile> \<phi> z] = [dw \<Turnstile> z \<^bold>= x]" by auto
      hence "[dw \<Turnstile> \<phi> z] = [v \<Turnstile> z \<^bold>= x]"
        using AOT_eq_nec by blast
    }
    thus "[v \<Turnstile> \<^bold>\<forall>z. \<^bold>\<A>\<phi> z \<^bold>\<equiv> z \<^bold>= x]" by AOT_meta_auto
  next
    assume "[v \<Turnstile> \<^bold>\<forall>z. \<^bold>\<A>\<phi> z \<^bold>\<equiv> z \<^bold>= x]"
    hence 1: "\<And> z. [v \<Turnstile> z\<^bold>\<down>] \<Longrightarrow> [dw \<Turnstile> \<phi> z] = [v \<Turnstile> z \<^bold>= x]" by AOT_meta_auto
    hence 2: "[dw \<Turnstile> \<phi> x]"
      using AOT_boxE AOT_nec_selfeq x_ex by blast
    have 3: "\<And> z. [dw \<Turnstile> z\<^bold>\<down>] \<Longrightarrow> [dw \<Turnstile> \<phi> z] = [dw \<Turnstile> z \<^bold>= x]"
      using 1 AOT_eq_nec AOT_exists_necI by blast
    {
      fix z :: \<kappa>
      assume "[dw \<Turnstile> z\<^bold>\<down>]"
      moreover assume "[dw \<Turnstile> \<phi> z]"
      ultimately have "[dw \<Turnstile> z \<^bold>= x]" using 3 by blast
      hence "z = x" using AOT_l_identity[of dw z x "\<lambda> x . Abs_\<o> (\<lambda> s w . z = x)"]
        unfolding AOT_valid_in_def by (simp add: Abs_\<o>_inverse)
    } note 4=this
    have 5: "\<exists>! x . [dw \<Turnstile> x\<^bold>\<down>] \<and> [dw \<Turnstile> \<phi> x]"
      apply (rule_tac a=x in ex1I)
      using x_ex 2 AOT_exists_necI apply blast
      using 4 by blast
    hence "x = (THE x . [dw \<Turnstile> x\<^bold>\<down>] \<and> [dw \<Turnstile> \<phi> x])"
      by (metis (mono_tags, lifting) "4" the_equality)
    hence "x = (\<^bold>\<iota>x. \<phi> x)" unfolding AOT_that_\<kappa>_def
      by (simp add: 5)
    thus "[v \<Turnstile> x \<^bold>= (\<^bold>\<iota>x. \<phi> x)]"
      using "1" "2" x_ex by blast
  qed
qed
end

instance \<kappa> :: \<kappa> proof qed

lemma "True" nitpick[satisfy,user_axioms,card i=2,expect=genuine] by simp

end
