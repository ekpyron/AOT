theory AOT_Term
  imports AOT_Truth
begin

class AOT_Term =
  fixes AOT_equiv :: "['a, 'a] \<Rightarrow> bool" (infixl "\<approx>" 75)
  assumes AOT_equiv_part_equivp[AOT_meta]: "part_equivp (\<approx>)"

instantiation prod :: (AOT_Term, AOT_Term) AOT_Term
begin
definition AOT_equiv_prod :: "['a\<times>'b, 'a\<times>'b] \<Rightarrow> bool" where
  [AOT_meta, AOT_meta_simp]: "(\<approx>) \<equiv> \<lambda> (x\<^sub>1,x\<^sub>2) (y\<^sub>1,y\<^sub>2) . x\<^sub>1 \<approx> y\<^sub>1 \<and> x\<^sub>2 \<approx> y\<^sub>2"
instance proof(standard; rule part_equivpI; (rule sympI | rule transpI)?)
  obtain x :: 'a and y :: 'b where "x \<approx> x" and "y \<approx> y"
    using AOT_equiv_part_equivp part_equivpE by metis
  thus "\<exists> x :: 'a\<times>'b . x \<approx> x"
    by (rule_tac x="(x, y)" in exI) (simp add: AOT_meta_simp)
next
  show "x \<approx> y \<Longrightarrow> y \<approx> x" for x y :: "'a\<times>'b"
    by (induct x; induct y; simp add: AOT_meta_simp)
       (simp add: AOT_equiv_part_equivp part_equivp_symp)
next
  show "x \<approx> y \<Longrightarrow> y \<approx> z \<Longrightarrow> x \<approx> z" for x y z :: "'a\<times>'b"
    by (induct x; induct y; induct z; simp add: AOT_meta_simp)
       (meson AOT_equiv_part_equivp part_equivp_transp)
qed
end

instantiation \<o> :: AOT_Term
begin
definition AOT_equiv_\<o> :: "[\<o>, \<o>] \<Rightarrow> bool" where "AOT_equiv_\<o> \<equiv> (=)"
instance by standard (simp add: AOT_equiv_\<o>_def equivp_implies_part_equivp identity_equivp)
end


consts AOT_all :: "('a::AOT_Term \<Rightarrow> \<o>) \<Rightarrow> \<o>" (binder "\<^bold>\<forall>" [8] 9)
consts AOT_ex :: "('a::AOT_Term \<Rightarrow> \<o>) \<Rightarrow> \<o>" (binder "\<^bold>\<exists>" [8] 9)
consts AOT_denotes :: "'a::AOT_Term \<Rightarrow> \<o>" ("_\<^bold>\<down>" [70] 60)
consts AOT_id :: "['a::AOT_Term, 'a] \<Rightarrow> \<o>" (infixl "\<^bold>=" 63)

specification (AOT_all AOT_ex AOT_denotes AOT_id)
  AOT_allS[AOT_meta, AOT_meta_simp]: "[v \<Turnstile> \<^bold>\<forall> x . \<phi> x] = (\<forall> x . x \<approx> x \<longrightarrow> [v \<Turnstile> \<phi> x])"
  AOT_exS[AOT_meta, AOT_meta_simp]: "[v \<Turnstile> \<^bold>\<exists> x . \<phi> x] = (\<exists> x . x \<approx> x \<and> [v \<Turnstile> \<phi> x])"
  AOT_denotesS[AOT_meta, AOT_meta_simp]: "[v \<Turnstile> \<tau>\<^bold>\<down>] = (\<tau> \<approx> \<tau>)"
  AOT_idS[AOT_meta, AOT_meta_simp]: "[v \<Turnstile> \<tau>\<^sub>1 \<^bold>= \<tau>\<^sub>2] = (\<tau>\<^sub>1 \<approx> \<tau>\<^sub>1 \<and> \<tau>\<^sub>2 \<approx> \<tau>\<^sub>2 \<and> \<tau>\<^sub>1 = \<tau>\<^sub>2)"
  by (
      rule_tac x="\<lambda> \<phi> . \<epsilon>\<^sub>\<o> v . \<forall> x . x \<approx> x \<longrightarrow> [v \<Turnstile> \<phi> x]" in exI;
      rule_tac x="\<lambda> \<phi> . \<epsilon>\<^sub>\<o> v . \<exists> x . x \<approx> x \<and> [v \<Turnstile> \<phi> x]" in exI;
      rule_tac x="\<lambda> \<tau> . \<epsilon>\<^sub>\<o> v . \<tau> \<approx> \<tau> " in exI;
      rule_tac x="\<lambda> \<tau>\<^sub>1 \<tau>\<^sub>2 . \<epsilon>\<^sub>\<o> v . \<tau>\<^sub>1 \<approx> \<tau>\<^sub>1 \<and> \<tau>\<^sub>2 \<approx> \<tau>\<^sub>2 \<and> \<tau>\<^sub>1 = \<tau>\<^sub>2 " in exI
     ) (simp add: AOT_meta_simp)
declare AOT_all_def[AOT_meta] AOT_ex_def[AOT_meta] AOT_denotes_def[AOT_meta] AOT_id_def[AOT_meta]

lemma AOT_exI[AOT_meta]:
  assumes "[v \<Turnstile> \<tau>\<^bold>\<down>]" and "[v \<Turnstile> \<phi> \<tau>]"
  shows "[v \<Turnstile> \<^bold>\<exists> \<tau> . \<phi> \<tau>]"
  using assms by (auto simp: AOT_meta_simp)


declare[[typedef_overloaded]]

quotient_type 'a \<upsilon> = "'a::AOT_Term" / partial: "(\<approx>)" by (fact AOT_meta)
print_theorems
(* TODO: automatically collect these theorems *)
declare Quotient3_\<upsilon>[AOT_meta] Quotient_\<upsilon>[AOT_meta] Abs_\<upsilon>_cases[AOT_meta]
  Abs_\<upsilon>_induct[AOT_meta] Abs_\<upsilon>_inject[AOT_meta] Abs_\<upsilon>_inverse[AOT_meta]
  Rep_\<upsilon>[AOT_meta] Rep_\<upsilon>_cases[AOT_meta] Rep_\<upsilon>_induct[AOT_meta]
  Rep_\<upsilon>_inject[AOT_meta] Rep_\<upsilon>_inverse[AOT_meta] \<upsilon>.abs_induct[AOT_meta]
  \<upsilon>.domain[AOT_meta] \<upsilon>.domain_eq[AOT_meta] \<upsilon>.domain_par[AOT_meta] \<upsilon>.domain_par_left_total[AOT_meta]
  \<upsilon>.pcr_cr_eq[AOT_meta]
  \<upsilon>.rel_eq_transfer[AOT_meta] \<upsilon>.right_total[AOT_meta] \<upsilon>.right_unique[AOT_meta]
  type_definition_\<upsilon>[AOT_meta] \<upsilon>_equivp[AOT_meta] abs_\<upsilon>_def[AOT_meta]
  cr_\<upsilon>_def[AOT_meta] pcr_\<upsilon>_def[AOT_meta] rep_\<upsilon>_def[AOT_meta]
  typerep_\<upsilon>_def[AOT_meta]

typedef 'a var = "{ x :: 'a :: AOT_Term . x \<approx> x }" 
  using AOT_equiv_part_equivp part_equivp_def by auto
notation "Rep_var" ("\<langle>_\<rangle>")
declare typerep_var_def[AOT_meta] Abs_var_cases[AOT_meta] Abs_var_induct[AOT_meta]
        Abs_var_inject[AOT_meta] Abs_var_inverse[AOT_meta] Rep_var[AOT_meta]
        Rep_var_cases[AOT_meta] Rep_var_induct[AOT_meta] Rep_var_inject[AOT_meta]
        Rep_var_inverse[AOT_meta] type_definition_var[AOT_meta]

lemma AOT_var_denotes[AOT_meta]: "[v \<Turnstile> \<langle>x\<rangle>\<^bold>\<down>]"
  using AOT_denotesS Rep_var by blast

lemma AOT_var_equiv[AOT_meta]: "\<langle>x\<rangle> \<approx> \<langle>x\<rangle>"
  using Rep_var by blast

end
