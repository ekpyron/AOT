theory AOT_Term
  imports AOT_Truth
begin

class AOT_Term =
  fixes AOT_meta_equiv :: "'a\<Rightarrow>'a\<Rightarrow>bool"
  assumes AOT_meta_equiv_part_equivp: "part_equivp AOT_meta_equiv"
begin
end


lift_definition AOT_all :: "('a::AOT_Term\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>" [8] 9) is
  "\<lambda> \<phi> s w . (\<forall> x :: 'a . AOT_meta_equiv x x \<longrightarrow> \<phi> x s w)" .

definition AOT_ex :: "('a::AOT_Term\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<exists>" [8] 9) where
  "AOT_ex \<equiv> \<lambda> \<phi> . \<^bold>\<not>(\<^bold>\<forall> x . \<^bold>\<not>\<phi> x)"

instantiation prod :: (AOT_Term, AOT_Term) AOT_Term
begin
  definition AOT_meta_equiv_prod :: "'a\<times>'b\<Rightarrow>'a\<times>'b\<Rightarrow>bool" where
    "AOT_meta_equiv_prod \<equiv> (\<lambda> x y . AOT_meta_equiv (fst x) (fst y)
                                  \<and> AOT_meta_equiv (snd x) (snd y))"
instance proof
  show "part_equivp (AOT_meta_equiv :: 'a\<times>'b\<Rightarrow>'a\<times>'b\<Rightarrow>bool)"
  proof (rule part_equivpI)
    show "\<exists>x :: 'a\<times>'b. AOT_meta_equiv x x"
      unfolding AOT_meta_equiv_prod_def
      using AOT_meta_equiv_part_equivp[THEN part_equivpE]
      by (metis fst_conv snd_conv)
  next
    show "symp (AOT_meta_equiv :: 'a\<times>'b\<Rightarrow>'a\<times>'b\<Rightarrow>bool)"
      unfolding AOT_meta_equiv_prod_def
      using AOT_meta_equiv_part_equivp[THEN part_equivpE]
      by (metis (no_types, lifting) symp_def)
  next
    show "transp (AOT_meta_equiv :: 'a\<times>'b\<Rightarrow>'a\<times>'b\<Rightarrow>bool)"
      unfolding AOT_meta_equiv_prod_def transp_def
      using AOT_meta_equiv_part_equivp[THEN part_equivp_transp]
      by metis
  qed
qed
end

instantiation unit :: AOT_Term
begin
  definition AOT_meta_equiv_unit :: "unit\<Rightarrow>unit\<Rightarrow>bool" where "AOT_meta_equiv_unit \<equiv> (\<lambda> x y . True)" 
instance proof
  show "part_equivp (AOT_meta_equiv :: unit\<Rightarrow>unit\<Rightarrow>bool)"
    unfolding AOT_meta_equiv_unit_def
    by (simp add: part_equivp_def)
qed
end

lemma AOT_term_equiv_unitI:
    shows "AOT_meta_equiv (x::unit) (y::unit)"
  unfolding AOT_meta_equiv_unit_def by auto

end
