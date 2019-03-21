theory AOT_Relation
  imports AOT_Term
begin

typedef 'a relation = "UNIV::('a::AOT_Term\<Rightarrow>\<o>) set" ..
setup_lifting type_definition_relation

instantiation relation :: (AOT_Term) AOT_Term
begin
  lift_definition AOT_meta_equiv_relation :: "('a relation)\<Rightarrow>('a relation)\<Rightarrow>bool" is
    "\<lambda> F G . (\<forall> x y . AOT_meta_equiv x y \<longrightarrow> F x = G y)
           \<and> (\<forall> x . AOT_meta_equiv x x \<or> (F x = AOT_nec_false \<and> G x = AOT_nec_false))" .
instance proof
  show "part_equivp (AOT_meta_equiv :: ('a relation)\<Rightarrow>('a relation)\<Rightarrow>bool)"
  proof (rule part_equivpI)
    obtain F :: "'a relation" where F_def: "F = Abs_relation (\<lambda> x . AOT_nec_false)" by blast
    have "\<forall> x y . AOT_meta_equiv x y \<longrightarrow> (Rep_relation F) x = (Rep_relation F) y"
      unfolding F_def by (simp add: Abs_relation_inverse)
    moreover have "\<forall> x v . AOT_meta_equiv x x \<or> (Rep_relation F) x = AOT_nec_false"
      unfolding F_def by (simp add: Abs_relation_inverse)
    ultimately show "\<exists>x :: 'a relation. AOT_meta_equiv x x"
      unfolding AOT_meta_equiv_relation_def
      by auto
  next
    show "symp (AOT_meta_equiv :: ('a relation)\<Rightarrow>('a relation)\<Rightarrow>bool)"
      unfolding AOT_meta_equiv_relation_def symp_def
      using AOT_meta_equiv_part_equivp part_equivp_symp apply simp
      by fastforce
  next
    show "transp (AOT_meta_equiv :: ('a relation)\<Rightarrow>('a relation)\<Rightarrow>bool)"
      unfolding AOT_meta_equiv_relation_def transp_def apply simp
      by (meson AOT_meta_equiv_part_equivp part_equivp_symp part_equivp_transp)
  qed
qed
end

definition AOT_exe :: "('a::AOT_Term relation) \<Rightarrow> 'a \<Rightarrow> \<o>" where
  "AOT_exe \<equiv> (\<lambda> F x . if (AOT_meta_equiv F F \<and> AOT_meta_equiv x x) then (Rep_relation F) x else AOT_nec_false)"


nonterminal exe_args
syntax
  AOT_exe :: "('a::AOT_Term relation) \<Rightarrow> exe_args \<Rightarrow> 'b" ("\<lparr>_,/ _\<rparr>")
  "" :: "'a::AOT_Term \<Rightarrow> exe_args" ("_")
  Pair :: "'a::AOT_Term \<Rightarrow> exe_args \<Rightarrow> exe_args" ("_,/ _")
translations
  "\<lparr>F, x\<rparr>" \<rightleftharpoons> "CONST AOT_exe F x"

definition AOT_logical_exists :: "'a :: AOT_Term \<Rightarrow> \<o>" ("_\<^bold>\<down>" [70] 60) where
    "AOT_logical_exists \<equiv> (\<lambda> x . \<^bold>\<exists> \<Omega> . \<lparr>\<Omega>, x\<rparr>)"

lemma AOT_logical_existsE: "[v \<Turnstile> x\<^bold>\<down>] \<Longrightarrow> AOT_meta_equiv x x"
  unfolding AOT_logical_exists_def AOT_ex_def AOT_all_def AOT_not_def AOT_valid_in_def AOT_exe_def
  apply (simp add: Abs_\<o>_inverse)
  by (metis (mono_tags, lifting) AOT_nec_false.rep_eq)
lemma AOT_logical_existsI: "AOT_meta_equiv x x \<Longrightarrow> [v \<Turnstile> x\<^bold>\<down>]"
  unfolding AOT_logical_exists_def AOT_ex_def AOT_all_def AOT_not_def AOT_valid_in_def AOT_exe_def
  apply (simp add: Abs_\<o>_inverse)
  apply (rule_tac x="Abs_relation (\<lambda> x . if AOT_meta_equiv x x then AOT_nec_true else AOT_nec_false)" in exI)
  unfolding AOT_meta_equiv_relation_def  apply (simp add: Abs_relation_inverse) apply transfer
  by (meson AOT_meta_equiv_part_equivp part_equivp_def)
lemma AOT_logical_existsS: "[v \<Turnstile> x\<^bold>\<down>] = AOT_meta_equiv x x"
  using AOT_logical_existsE AOT_logical_existsI by blast
lemma AOT_exists_necI[AOT_meta_intro]: assumes "[v \<Turnstile> \<tau>\<^bold>\<down>]" shows "[w \<Turnstile> \<tau>\<^bold>\<down>]" using assms
  by (simp add: AOT_logical_existsS)


lemma AOT_allE[AOT_meta_elim]:
  assumes "[v \<Turnstile> \<^bold>\<forall> x . \<phi> x]"
      and "([v \<Turnstile> x\<^bold>\<down>] \<Longrightarrow> [v \<Turnstile> \<phi> x]) \<Longrightarrow> [v \<Turnstile> r]"
    shows "[v \<Turnstile> r]"
  using assms
  by (simp add: AOT_all.rep_eq AOT_logical_existsE AOT_valid_in.rep_eq)
lemma AOT_allI[AOT_meta_intro_safe]:
  assumes "\<And> x . [v \<Turnstile> x\<^bold>\<down>] \<Longrightarrow> [v \<Turnstile> \<phi> x]"
  shows "[v \<Turnstile> \<^bold>\<forall> x . \<phi> x]"
  using assms
  by (meson AOT_all.rep_eq AOT_logical_existsS AOT_valid_in.rep_eq)
lemma AOT_allS[AOT_meta_simp]:
  "[v \<Turnstile> \<^bold>\<forall> x . \<phi> x] = (\<forall> x . [v \<Turnstile> x\<^bold>\<down>] \<longrightarrow> [v \<Turnstile> \<phi> x])"
  by AOT_meta_auto

lemma AOT_exE[AOT_meta_elim_safe]:
  assumes "[v \<Turnstile> \<^bold>\<exists> x . \<phi> x]"
      and "\<And> x . [v \<Turnstile> x\<^bold>\<down>] \<Longrightarrow> ([v \<Turnstile> \<phi> x] \<Longrightarrow> [v \<Turnstile> q])"
  shows "[v \<Turnstile> q]"
  using assms unfolding AOT_ex_def
  by AOT_meta_auto
lemma AOT_exI[AOT_meta_intro]:
  assumes "[v \<Turnstile> x\<^bold>\<down>]" 
     and "[v \<Turnstile> \<phi> x]"
  shows "[v \<Turnstile> \<^bold>\<exists> x . \<phi> x]"
  using assms unfolding AOT_ex_def
  by AOT_meta_auto
lemma AOT_exS[AOT_meta_simp]: "[v \<Turnstile> \<^bold>\<exists> x . \<phi> x] = (\<exists> x . [v \<Turnstile> x\<^bold>\<down>] \<and> [v \<Turnstile> \<phi> x])"
  using AOT_exE AOT_exI AOT_notS by fastforce

lemma AOT_exists_prodI:
  assumes "[v \<Turnstile> xl\<^bold>\<down>]" and "[v \<Turnstile> xr\<^bold>\<down>]"
  shows "[v \<Turnstile> (xl,xr)\<^bold>\<down>]"
  apply (rule AOT_logical_existsI)
  using assms(1)[THEN AOT_logical_existsE]
  using assms(2)[THEN AOT_logical_existsE]
  by (simp add: AOT_meta_equiv_prod_def)
lemma AOT_exists_prodE1:
  assumes "[v \<Turnstile> (xl,xr)\<^bold>\<down>]"
  shows "[v \<Turnstile> xl\<^bold>\<down>]"
  apply (rule AOT_logical_existsI)
  using assms(1)[THEN AOT_logical_existsE]
  using assms apply transfer
  by (simp add: AOT_meta_equiv_prod_def)
lemma AOT_exists_prodE2:
  assumes "[v \<Turnstile> (xl,xr)\<^bold>\<down>]"
  shows "[v \<Turnstile> xr\<^bold>\<down>]"
  apply (rule AOT_logical_existsI)
  using assms(1)[THEN AOT_logical_existsE]
  using assms apply transfer
  by (simp add: AOT_meta_equiv_prod_def)


lemma AOT_exeE1[AOT_meta_elim]:
  assumes "[v \<Turnstile> \<lparr>F,x\<rparr>]"
  shows "[v \<Turnstile> F\<^bold>\<down>]"
  apply (rule AOT_logical_existsI)
  using assms unfolding AOT_exe_def AOT_nec_false_def AOT_valid_in_def apply simp
  by (metis (mono_tags, lifting) AOT_nec_false.rep_eq AOT_nec_false_def)
lemma AOT_exeE2[AOT_meta_elim]:
  assumes "[v \<Turnstile> \<lparr>F,x\<rparr>]"
  shows "[v \<Turnstile> x\<^bold>\<down>]"
  apply (rule AOT_logical_existsI)
  using assms unfolding AOT_exe_def AOT_nec_false_def AOT_valid_in_def apply simp
  by (metis (mono_tags, lifting) AOT_nec_false.rep_eq AOT_nec_false_def)
lemma AOT_exeE3[AOT_meta_elim]:
  assumes "[v \<Turnstile> \<lparr>F,x\<rparr>]"
  shows "[v \<Turnstile> (Rep_relation F) x]"
  by (metis AOT_exeE2 AOT_exe_def AOT_logical_existsE assms)
lemma AOT_exeI[AOT_meta_intro_safe]:
  assumes "[v \<Turnstile> F\<^bold>\<down>]"
      and "[v \<Turnstile> x\<^bold>\<down>]"
      and "[v \<Turnstile> (Rep_relation F) x]"
    shows "[v \<Turnstile> \<lparr>F,x\<rparr>]"
  by (metis AOT_exe_def AOT_logical_existsE assms(1) assms(2) assms(3))
lemma AOT_exeS[AOT_meta_simp]:
  "[v \<Turnstile> \<lparr>F,x\<rparr>] = ([v \<Turnstile> F\<^bold>\<down>] \<and> [v \<Turnstile> x\<^bold>\<down>] \<and> [v \<Turnstile> (Rep_relation F) x])"
  using AOT_exeI AOT_exeE1 AOT_exeE2 AOT_exeE3 by metis



definition AOT_equiv :: "'a::AOT_Term \<Rightarrow> 'a \<Rightarrow> \<o>" (infixl "\<^bold>~" 63) where
  "AOT_equiv \<equiv> (\<lambda> x y . x\<^bold>\<down> \<^bold>& y\<^bold>\<down> \<^bold>& (\<^bold>\<forall> F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>))"

lemma AOT_equivS: "AOT_meta_equiv x y = [v \<Turnstile> x \<^bold>~ y]"
proof
  assume 1: "AOT_meta_equiv x y"
  hence "[v \<Turnstile> \<^bold>\<forall> F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>]"
    apply AOT_meta_simp
    by (metis (full_types) AOT_exeS AOT_exe_def AOT_logical_existsI AOT_meta_equiv_relation.rep_eq)
  moreover have "AOT_meta_equiv x x" "AOT_meta_equiv y y" using 1
    by (meson AOT_meta_equiv_part_equivp part_equivp_def)+
  ultimately show "[v \<Turnstile> x \<^bold>~ y]" unfolding AOT_equiv_def
    by (simp add: AOT_conjI AOT_logical_existsI)
next
  assume "[v \<Turnstile> x \<^bold>~ y]"
  hence 1: "[v \<Turnstile> x\<^bold>\<down> \<^bold>& y\<^bold>\<down> \<^bold>& (\<^bold>\<forall> F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>)]" unfolding AOT_equiv_def by auto
  obtain F where F_def: "F = Abs_relation (\<lambda> y . Abs_\<o> (\<lambda> s w . AOT_meta_equiv x y))" by auto
  have 2: "AOT_meta_equiv F F" unfolding F_def unfolding AOT_meta_equiv_relation_def
    apply (simp add: Abs_relation_inverse) apply transfer
    by (meson AOT_meta_equiv_part_equivp part_equivp_symp part_equivp_transp)
  have 3: "AOT_meta_equiv x x" and 4: "AOT_meta_equiv y y" using 1
    using AOT_conjS AOT_logical_existsE apply blast
    using "1" AOT_conjS AOT_logical_existsS by blast
  have "(\<forall>F. [v \<Turnstile> F\<^bold>\<down>] \<longrightarrow>
         ([v \<Turnstile> x\<^bold>\<down>] \<and> [v \<Turnstile> Rep_relation F x]) = ([v \<Turnstile> y\<^bold>\<down>] \<and> [v \<Turnstile> Rep_relation F y]))"
    using 1 apply AOT_meta_simp by blast
  hence "[v \<Turnstile> Rep_relation F x] = [v \<Turnstile> Rep_relation F y]" using 2 3 4
    by (simp add: AOT_logical_existsI)
  thus "AOT_meta_equiv x y" unfolding F_def apply (simp add: Abs_relation_inverse) using 3 apply transfer by auto
qed

lemma AOT_equivI: "AOT_meta_equiv x y \<Longrightarrow> [v \<Turnstile> x \<^bold>~ y]"
  using AOT_equivS by auto
lemma AOT_equivE: "[v \<Turnstile> x \<^bold>~ y] \<Longrightarrow> AOT_meta_equiv x y"
  using AOT_equivS by auto

lemma AOT_equivE2: "[v \<Turnstile> x \<^bold>~ y] \<Longrightarrow> [v \<Turnstile> x\<^bold>\<down>]"
  by (metis AOT_conjE AOT_equiv_def)
lemma AOT_equivE3: "[v \<Turnstile> x \<^bold>~ y] \<Longrightarrow> [v \<Turnstile> y\<^bold>\<down>]"
  by (metis AOT_conjE AOT_equiv_def)

lemma AOT_equiv_relI[AOT_meta_intro_safe]:
  assumes "\<And> x y . [v \<Turnstile> x \<^bold>~ y] \<Longrightarrow> (Rep_relation F) x = (Rep_relation G) y"
      and "\<And> x . [v \<Turnstile> x\<^bold>\<down>] \<or> (Rep_relation F) x = AOT_nec_false"
      and "\<And> x . [v \<Turnstile> x\<^bold>\<down>] \<or> (Rep_relation G) x = AOT_nec_false"
    shows "[v \<Turnstile> F \<^bold>~ G]" apply (rule AOT_equivI)
  unfolding AOT_meta_equiv_relation_def apply simp
  using AOT_equivI AOT_logical_existsE AOT_logical_existsI assms(1) assms(2) assms(3)
  by blast

lemma AOT_equiv_existsS: "[v \<Turnstile> x \<^bold>~ x] = [v \<Turnstile> x\<^bold>\<down>]"
  using AOT_equivS AOT_logical_existsS by blast
lemma AOT_equiv_existsI: "[v \<Turnstile> x \<^bold>~ x] \<Longrightarrow> [v \<Turnstile> x\<^bold>\<down>]"
  using AOT_equiv_existsS by auto
lemma AOT_equiv_existsE: "[v \<Turnstile> x\<^bold>\<down>] \<Longrightarrow> [v \<Turnstile> x \<^bold>~ x]"
  using AOT_equiv_existsS by auto



lemma AOT_exe_trans:
  assumes "[v \<Turnstile> x \<^bold>~ y]"
      and "[v \<Turnstile> \<lparr>F,x\<rparr>]"
    shows "[v \<Turnstile> \<lparr>F,y\<rparr>]" using assms apply AOT_meta_simp
  by (metis (no_types, lifting) AOT_conjS AOT_equivE AOT_equiv_def AOT_logical_existsE AOT_meta_equiv_relation.rep_eq)

lemma AOT_exe_trans2:
  assumes "[v \<Turnstile> x \<^bold>~ y]"
    shows "\<lparr>F,x\<rparr> = \<lparr>F,y\<rparr>"
  by (metis AOT_equivE AOT_exe_def AOT_meta_equiv_relation.rep_eq assms)

lemma AOT_exists_relI[AOT_meta_intro_safe]:
  assumes "\<And> x y v . [v \<Turnstile> x \<^bold>~ y] \<Longrightarrow> (Rep_relation F) x = (Rep_relation F) y"
      and "\<And> x v . [v \<Turnstile> x\<^bold>\<down>] \<or> (Rep_relation F) x = AOT_nec_false"
    shows "[v \<Turnstile> F\<^bold>\<down>]"
  apply (rule AOT_equiv_existsI)
  apply (rule AOT_equiv_relI)
  using assms(1) apply blast
  by (simp add: assms(2))+

lemma AOT_equiv_relE1[AOT_meta_elim]:
  assumes "[v \<Turnstile> F \<^bold>~ G]"
      and "[v \<Turnstile> x \<^bold>~ y]"
  shows "(Rep_relation F) x = (Rep_relation G) y"
  using assms
  by (meson AOT_equivE AOT_meta_equiv_relation.rep_eq)

lemma AOT_equiv_relE2[AOT_meta_elim]:
  assumes "[v \<Turnstile> F \<^bold>~ G]"
      and "[v \<Turnstile> (Rep_relation F) x]"
  shows "[v \<Turnstile> x\<^bold>\<down>]"
  using assms AOT_equivE AOT_meta_equiv_relation.rep_eq
  by (metis (full_types) AOT_exeS AOT_exe_def AOT_logical_existsS)
lemma AOT_equiv_relE3[AOT_meta_elim]:
  assumes "[v \<Turnstile> F \<^bold>~ G]"
      and "[v \<Turnstile> (Rep_relation G) x]"
  shows "[v \<Turnstile> x\<^bold>\<down>]"
  using assms AOT_equivE AOT_meta_equiv_relation.rep_eq
  by (metis (full_types) AOT_exeS AOT_exe_def AOT_logical_existsS)

lemma AOT_fun_equiv_equal:
  assumes "[v \<Turnstile> (F::'a::AOT_Term relation) \<^bold>~ G]"
  shows "F = G"
proof -
  {
    fix x :: 'a
    {
      assume "[v \<Turnstile> x\<^bold>\<down>]"
      hence "(Rep_relation F) x = (Rep_relation G) x"
        using AOT_equiv_existsE AOT_equiv_relE1 assms by blast
    }
    moreover {
      assume "\<not>[v \<Turnstile> x\<^bold>\<down>]"
      hence "(Rep_relation F) x = (Rep_relation G) x"
        using AOT_equivE AOT_meta_equiv_relation.rep_eq assms by force
    }
    ultimately have "(Rep_relation F) x = (Rep_relation G) x" by auto
  }
  hence "Rep_relation F = Rep_relation G" by auto
  thus ?thesis
    using Rep_relation_inject by blast
qed


lift_definition AOT_lambda :: "('a::AOT_Term\<Rightarrow>\<o>) \<Rightarrow> 'a relation" is
  "\<lambda> \<phi> x . if (\<forall>v . [v \<Turnstile> x\<^bold>\<down>]) then Abs_\<o> (\<lambda> s w . s = dj \<and> Rep_\<o> (\<phi> x) s w \<or> (s \<noteq> dj \<and> (\<forall> y . [dw \<Turnstile> x \<^bold>~ y] \<longrightarrow> Rep_\<o> (\<phi> y) s w))) else AOT_nec_false" .

syntax
  AOT_lambda :: "[pttrn, \<o>]\<Rightarrow>'a::AOT_Term relation" ("(3[\<^bold>\<lambda>_/. _])")
translations
  "[\<^bold>\<lambda>x. b]" \<rightleftharpoons> "CONST AOT_lambda (\<lambda> x . b)"

lemma AOT_lambda_applyI[AOT_meta_intro_safe]:
  assumes "[v \<Turnstile> F x]"
      and "[v \<Turnstile> x\<^bold>\<down>]"
    shows "[v \<Turnstile> (Rep_relation [\<^bold>\<lambda>x. F x]) x]"
  using assms unfolding AOT_lambda_def
  apply (simp add: Abs_relation_inverse)
  using AOT_exists_necI AOT_valid_in.abs_eq AOT_valid_in.rep_eq by auto
lemma AOT_lambda_applyE1[AOT_meta_elim]:
  assumes "[v \<Turnstile> (Rep_relation [\<^bold>\<lambda>x. F x]) x]"
      and "[v \<Turnstile> x\<^bold>\<down>]"
    shows "[v \<Turnstile> F x]"
proof -
  have "Rep_\<o> (Rep_relation (AOT_lambda F) x) dj v"
    using assms(1) unfolding AOT_valid_in_def by (simp add: Abs_relation_inverse)
  thus "[v \<Turnstile> F x]"
    unfolding AOT_lambda_def apply (simp add: Abs_relation_inverse)
    using assms(2)[THEN AOT_exists_necI] apply transfer
    by auto
qed

lemma AOT_lambda_applyE2[AOT_meta_elim]:
  assumes "[v \<Turnstile> (Rep_relation [\<^bold>\<lambda>x. F x]) x]"
    shows "[v \<Turnstile> x\<^bold>\<down>]"
  using assms unfolding AOT_lambda_def
  apply (simp add: Abs_relation_inverse)
  by (metis (mono_tags, lifting) AOT_exeS AOT_exe_def AOT_logical_existsI)

lemma AOT_equiv_trans:
  assumes "[v \<Turnstile> x \<^bold>~ y]" and "[v \<Turnstile> y \<^bold>~ z]"
  shows "[v \<Turnstile> x \<^bold>~ z]"
  apply (rule AOT_equivI)
  using assms(1)[THEN AOT_equivE] assms(2)[THEN AOT_equivE]
  by (meson AOT_meta_equiv_part_equivp part_equivp_transp)

lemma AOT_equiv_sym:
  assumes "[v \<Turnstile> x \<^bold>~ y]"
  shows "[v \<Turnstile> y \<^bold>~ x]"
  apply (rule AOT_equivI)
  using assms(1)[THEN AOT_equivE]
  by (meson AOT_meta_equiv_part_equivp part_equivp_symp)

lemma AOT_lambda_existsI:
  assumes "\<And>x y v . [v \<Turnstile> x \<^bold>~ y] \<Longrightarrow> [v \<Turnstile> F x] = [v \<Turnstile> F y]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. F x]\<^bold>\<down>]"
proof (rule AOT_exists_relI)
  fix x y :: 'a and v :: i
  assume "[v \<Turnstile> x \<^bold>~ y]"
  hence 1: "\<And> v . [v \<Turnstile> x \<^bold>~ y]" and x_ex: "\<And> v . [v \<Turnstile> x\<^bold>\<down>]" and y_ex: "\<And> v . [v \<Turnstile> y\<^bold>\<down>]"
    using AOT_equivS AOT_equivE2 AOT_equivE3 AOT_logical_existsS by blast+
  {
    fix s :: j and v :: i
    have 3: "\<And> v . (\<forall>y. [dw \<Turnstile> x \<^bold>~ y] \<longrightarrow> Rep_\<o> (F y) s v) = (\<forall>ya. [dw \<Turnstile> y \<^bold>~ ya] \<longrightarrow> Rep_\<o> (F ya) s v)"
    proof(rule iffI; rule allI; rule impI)
      fix v :: i and ya :: 'a
      assume 2: "\<forall>y. [dw \<Turnstile> x \<^bold>~ y] \<longrightarrow> Rep_\<o> (F y) s v"
      assume "[dw \<Turnstile> y \<^bold>~ ya]"
      hence "[dw \<Turnstile> x \<^bold>~ ya]" using 1[of dw] AOT_equiv_trans by blast
      thus "Rep_\<o> (F ya) s v" using 2 by auto
    next
      fix v :: i and ya :: 'a
      assume 2: "\<forall>ya. [dw \<Turnstile> y \<^bold>~ ya] \<longrightarrow> Rep_\<o> (F ya) s v"
      assume "[dw \<Turnstile> x \<^bold>~ ya]"
      hence "[dw \<Turnstile> y \<^bold>~ ya]" using 1[of dw] AOT_equiv_trans AOT_equiv_sym by blast
      thus "Rep_\<o> (F ya) s v" using 2 by auto
    qed
    have "Rep_\<o> (Rep_relation (AOT_lambda F) x) s v  = Rep_\<o> (Rep_relation (AOT_lambda F) y) s v"
      unfolding AOT_lambda_def apply (simp add: Abs_relation_inverse Abs_\<o>_inverse)
      apply (cases "s = dj")
       apply simp using y_ex x_ex apply simp using assms(1)[OF 1] apply (simp add: AOT_valid_in_def)
      apply simp using x_ex y_ex apply simp using 1[of dw] using 3 by auto
  }
  hence "Rep_\<o> (Rep_relation (AOT_lambda F) x) = Rep_\<o> (Rep_relation (AOT_lambda F) y)" by auto
  thus "Rep_relation (AOT_lambda F) x = Rep_relation (AOT_lambda F) y"
    using Rep_\<o>_inject by blast
next
  fix x :: 'a and v :: i
  show "[v \<Turnstile> x\<^bold>\<down>] \<or> Rep_relation [\<^bold>\<lambda>x. F x] x = AOT_nec_false"
    by (simp add: AOT_lambda.rep_eq)
qed

lemma AOT_lambda_existsE:
  assumes "[v \<Turnstile> [\<^bold>\<lambda>x. F x]\<^bold>\<down>]"
      and "[v \<Turnstile> x \<^bold>~ y]"
    shows "[v \<Turnstile> F x] = [v \<Turnstile> F y]"
  by (smt AOT_equivE2 AOT_equivE3 AOT_equiv_existsE AOT_equiv_relE1 AOT_lambda_applyE1 AOT_lambda_applyI assms(1) assms(2)) (* TODO *)

lemma AOT_pre_eta:
  assumes "[v \<Turnstile> F\<^bold>\<down>]"
  shows "F = [\<^bold>\<lambda>x. (Rep_relation F) x]"
proof -
  {
    fix s :: j and v :: i and x :: 'a
    have "Rep_\<o> (Rep_relation F x) s v = Rep_\<o> (Rep_relation [\<^bold>\<lambda>x. (Rep_relation F) x] x) s v"
      unfolding AOT_lambda_def apply (simp add: Abs_relation_inverse Abs_\<o>_inverse)
      apply (cases "s = dj")
      apply simp
       apply (metis AOT_logical_existsE AOT_logical_existsI AOT_meta_equiv_relation.rep_eq assms)
      apply simp
      by (metis AOT_equivS AOT_equiv_existsE AOT_logical_existsI AOT_meta_equiv_relation.rep_eq assms)
  }
  hence "\<And> x . Rep_\<o> (Rep_relation F x) = Rep_\<o> (Rep_relation [\<^bold>\<lambda>x. (Rep_relation F) x] x)" by blast
  hence "Rep_relation F = Rep_relation [\<^bold>\<lambda>x. (Rep_relation F) x]" using Rep_\<o>_inject by blast
  thus ?thesis
    using Rep_relation_inject by blast
qed

lemma AOT_eta:
  assumes "[v \<Turnstile> F\<^bold>\<down>]"
  shows "F = [\<^bold>\<lambda>x. \<lparr>F,x\<rparr>]"
proof -
  {
    fix x :: 'a and s :: j and v :: i
    have "Rep_\<o> (Rep_relation F x) s v = Rep_\<o> (Rep_relation [\<^bold>\<lambda>x. \<lparr>F,x\<rparr>] x) s v"
      unfolding AOT_lambda_def
      apply (simp add: Abs_relation_inverse Abs_\<o>_inverse)
      apply (cases "s = dj")
      apply simp
       apply (metis (full_types) AOT_exeS AOT_exists_necI AOT_lambda_applyE2 AOT_nec_false.rep_eq AOT_pre_eta AOT_valid_in.rep_eq assms)
      apply simp
      by (metis (full_types, hide_lams) AOT_equivS AOT_exe_def AOT_exe_trans2 AOT_lambda.rep_eq AOT_logical_existsE AOT_pre_eta assms)
  }
  thus ?thesis using Rep_relation_inject Rep_\<o>_inject by blast
qed

named_theorems AOT_lambda_exists_intros

lemma AOT_lambda_exe_exists[AOT_lambda_exists_intros]: 
  assumes "[v \<Turnstile> F\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<lparr>F,x\<rparr>]\<^bold>\<down>]"
  using AOT_eta[OF assms] assms by auto

lemma AOT_lambda_const_exists[AOT_lambda_exists_intros]:
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<Theta>]\<^bold>\<down>]"
  apply (rule AOT_lambda_existsI) by auto

lemma AOT_lambda_not_exists[AOT_lambda_exists_intros]:
  assumes "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<^bold>\<not>(\<phi> x)]\<^bold>\<down>]"
  apply (rule AOT_lambda_existsI)
  using assms[THEN AOT_exists_necI, THEN AOT_lambda_existsE]
  by (meson AOT_notS)

lemma AOT_lambda_box_exists[AOT_lambda_exists_intros]:
  assumes "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<^bold>\<box>(\<phi> x)]\<^bold>\<down>]"
  apply (rule AOT_lambda_existsI)
  using assms[THEN AOT_exists_necI, THEN AOT_lambda_existsE]
  by (meson AOT_boxS AOT_equivS)

lemma AOT_lambda_actual_exists[AOT_lambda_exists_intros]:
  assumes "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<^bold>\<A>(\<phi> x)]\<^bold>\<down>]"
  apply (rule AOT_lambda_existsI)
  using assms[THEN AOT_exists_necI, THEN AOT_lambda_existsE]
  by (meson AOT_actualS AOT_equivS)

lemma AOT_lambda_impl_exists[AOT_lambda_exists_intros]:
  assumes "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x]\<^bold>\<down>]" and "[v \<Turnstile> [\<^bold>\<lambda>x. \<psi> x]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x \<^bold>\<rightarrow> \<psi> x]\<^bold>\<down>]"
  apply (rule AOT_lambda_existsI)
  using assms[THEN AOT_exists_necI, THEN AOT_lambda_existsE]
  by (simp add: AOT_implS)

lemma AOT_lambda_conj_exists[AOT_lambda_exists_intros]:
  assumes "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x]\<^bold>\<down>]" and "[v \<Turnstile> [\<^bold>\<lambda>x. \<psi> x]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x \<^bold>& \<psi> x]\<^bold>\<down>]"
  unfolding AOT_conj_def
  using assms by (fast intro: AOT_lambda_exists_intros)

lemma AOT_lambda_disj_exists[AOT_lambda_exists_intros]:
  assumes "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x]\<^bold>\<down>]" and "[v \<Turnstile> [\<^bold>\<lambda>x. \<psi> x]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x \<^bold>\<or> \<psi> x]\<^bold>\<down>]"
  unfolding AOT_disj_def
  using assms by (fast intro: AOT_lambda_exists_intros)

lemma AOT_lambda_iff_exists[AOT_lambda_exists_intros]:
  assumes "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x]\<^bold>\<down>]" and "[v \<Turnstile> [\<^bold>\<lambda>x. \<psi> x]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x \<^bold>\<equiv> \<psi> x]\<^bold>\<down>]"
  unfolding AOT_iff_def
  using assms by (fast intro: AOT_lambda_exists_intros)


lemma AOT_lambda_diamond_exists[AOT_lambda_exists_intros]:
  assumes "[v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<^bold>\<diamond>(\<phi> x)]\<^bold>\<down>]"
  unfolding AOT_diamond_def
  using assms by (fast intro: AOT_lambda_exists_intros)

lemma AOT_lambda_all_exists[AOT_lambda_exists_intros]:
  assumes "\<And> z . [v \<Turnstile> z\<^bold>\<down>] \<Longrightarrow> [v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x z]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<^bold>\<forall> y . \<phi> x y]\<^bold>\<down>]"
  apply (rule AOT_lambda_existsI)
  using assms[THEN AOT_exists_necI, THEN AOT_lambda_existsE]
  AOT_equivE2 AOT_equivE3 apply (subst AOT_allS)+
  by (simp add: AOT_exists_necI)

lemma AOT_lambda_ex_exists[AOT_lambda_exists_intros]:
  assumes "\<And> z . [v \<Turnstile> z\<^bold>\<down>] \<Longrightarrow> [v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x z]\<^bold>\<down>]"
  shows "[v \<Turnstile> [\<^bold>\<lambda>x. \<^bold>\<exists> y . \<phi> x y]\<^bold>\<down>]"
  unfolding AOT_ex_def
  using assms by (fast intro: AOT_lambda_exists_intros)

lemma AOT_lambda_equiv_exists:
  assumes "[v \<Turnstile> [\<^bold>\<lambda>y . \<phi> y]\<^bold>\<down>]"
      and "\<And> y v . [v \<Turnstile> y\<^bold>\<down>] \<Longrightarrow> [v \<Turnstile> \<phi> y] = [v \<Turnstile> \<psi> y]"
    shows "[v \<Turnstile> [\<^bold>\<lambda>y . \<psi> y]\<^bold>\<down>]"
  apply (rule AOT_lambda_existsI)
  using AOT_lambda_existsE[OF assms(1)] assms(2) AOT_equivE3
  by (metis AOT_equivE2 AOT_exists_necI AOT_lambda_existsE assms(1))

lemma AOT_equiv_prodI:
  assumes "[v \<Turnstile> (fst x) \<^bold>~ (fst y)]" and "[v \<Turnstile> (snd x) \<^bold>~ (snd y)]"
  shows "[v \<Turnstile> x \<^bold>~ y]"
  apply (rule AOT_equivI) using assms(1)[THEN AOT_equivE] assms(2)[THEN AOT_equivE]
  by (simp add: AOT_meta_equiv_prod_def)
lemma AOT_equiv_prodE1: assumes "[v \<Turnstile> x \<^bold>~ y]" shows "[v \<Turnstile> (fst x) \<^bold>~ (fst y)]"
  apply (rule AOT_equivI) using assms[THEN AOT_equivE]
  by (simp add: AOT_meta_equiv_prod_def)
lemma AOT_equiv_prodE2: assumes "[v \<Turnstile> x \<^bold>~ y]" shows "[v \<Turnstile> (snd x) \<^bold>~ (snd y)]"
  apply (rule AOT_equivI) using assms[THEN AOT_equivE]
  by (simp add: AOT_meta_equiv_prod_def)

lemma AOT_lambda_prod_exists[AOT_lambda_exists_intros]:
  assumes "\<And> y . [v \<Turnstile> [\<^bold>\<lambda>x. \<phi> x y]\<^bold>\<down>]"
      and "\<And> x . [v \<Turnstile> [\<^bold>\<lambda>y. \<phi> x y]\<^bold>\<down>]"
    shows "[v \<Turnstile> [\<^bold>\<lambda>(x,y). \<phi> x y]\<^bold>\<down>]"
  apply (rule AOT_lambda_existsI)
  using AOT_lambda_existsE[OF assms(1)[THEN AOT_exists_necI]]
        AOT_lambda_existsE[OF assms(2)[THEN AOT_exists_necI]]
  using AOT_equiv_prodE1 AOT_equiv_prodE2
  by (metis (full_types) case_prod_beta)

lemma AOT_beta1:
  assumes "[v \<Turnstile> \<lparr>[\<^bold>\<lambda>x . \<phi> x], x\<rparr>]"
  shows "[v \<Turnstile> \<phi> x]" using assms
  using AOT_exeE2 AOT_exeE3 AOT_lambda_applyE1 by blast

lemma AOT_beta2:
  assumes "[v \<Turnstile> x\<^bold>\<down>]" and "[v \<Turnstile> [\<^bold>\<lambda>x . \<phi> x]\<^bold>\<down>]" "[v \<Turnstile> \<phi> x]"
  shows "[v \<Turnstile> \<lparr>[\<^bold>\<lambda>x . \<phi> x], x\<rparr>]" using assms
  using AOT_exeI AOT_lambda_applyI by blast

abbreviation AOT_exe0 :: "unit relation \<Rightarrow> \<o>" ("\<lparr>_\<rparr>") where "\<lparr>p\<rparr> \<equiv> \<lparr>p,()\<rparr>"

end
