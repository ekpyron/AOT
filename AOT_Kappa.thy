theory AOT_Kappa
  imports AOT_Identity AOT_Individual
begin

class \<kappa> = AOT_UnaryIndividualIdentity

typedef (overloaded) ('a::AOT_Term) var = "{ x :: 'a . [dw \<Turnstile> x\<^bold>\<down>]}"
  apply simp apply (subst AOT_logical_existsS)
  using AOT_meta_equiv_part_equivp part_equivp_def by blast
notation Rep_var ("\<langle>_\<rangle>")
lemma vars_exist[AOT_meta_intro_safe]: "[v \<Turnstile> \<langle>x\<rangle>\<^bold>\<down>]"
  using AOT_exists_necI Rep_var by auto

lemma AOT_meta_var_allI: assumes "\<And> x :: ('a::AOT_Term) var. [v \<Turnstile> \<phi> \<langle>x\<rangle>]" shows "[v \<Turnstile> \<^bold>\<forall>x. \<phi> x]"
  using AOT_allI AOT_exists_necI Rep_var_cases assms by blast

end
