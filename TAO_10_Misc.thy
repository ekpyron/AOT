theory TAO_10_Misc
imports TAO_9_PLM
begin

locale Misc = PLM
begin
  definition Situation where "Situation x \<equiv> \<lparr>A!,x\<rparr> \<^bold>& (\<^bold>\<forall> F. \<lbrace>x,F\<rbrace> \<^bold>\<rightarrow> Propositional F)"

  definition EncodeProposition (infixl "\<^bold>\<Sigma>" 70) where "x\<^bold>\<Sigma>p \<equiv> \<lparr>A!,x\<rparr> \<^bold>& \<lbrace>x, \<^bold>\<lambda> x . p\<rbrace>"
  definition TrueInSituation (infixl "\<^bold>\<Turnstile>" 10) where "x \<^bold>\<Turnstile> p \<equiv> Situation x \<^bold>& x\<^bold>\<Sigma>p"
  definition PossibleWorld where "PossibleWorld x \<equiv> Situation x \<^bold>& \<^bold>\<diamond>(\<^bold>\<forall> p . x\<^bold>\<Sigma>p \<^bold>\<equiv> p)"

  lemma possit_sit_1: "[Situation (x\<^sup>P) \<^bold>\<equiv> \<^bold>\<box>(Situation (x\<^sup>P)) in v]"
  proof (rule "\<^bold>\<equiv>I"; rule CP)
    assume "[Situation (x\<^sup>P) in v]"
    hence 1: "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<rightarrow> Propositional F) in v]" unfolding Situation_def by auto
    have "[\<^bold>\<box>\<lparr>A!,x\<^sup>P\<rparr> in v]" using 1[conj1, THEN oa_facts_2[deduction]] .
    moreover have "[\<^bold>\<box>(\<^bold>\<forall> F. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<rightarrow> Propositional F) in v]"
       using 1[conj2] unfolding Propositional_def by (rule enc_prop_nec_2[deduction])
    ultimately show "[\<^bold>\<box>Situation (x\<^sup>P) in v]" unfolding Situation_def
    apply cut_tac apply (rule KBasic_3[equiv_rl]) by (rule intro_elim_1)
 next
    assume "[\<^bold>\<box>Situation (x\<^sup>P) in v]"
    thus "[Situation (x\<^sup>P) in v]" using qml_2[axiom_instance, deduction] by auto
 qed

  lemma possworld_nec: "[PossibleWorld (x\<^sup>P) \<^bold>\<equiv> \<^bold>\<box>(PossibleWorld (x\<^sup>P)) in v]" apply (rule "\<^bold>\<equiv>I"; rule CP)
     subgoal unfolding PossibleWorld_def apply (rule KBasic_3[equiv_rl]) apply (rule intro_elim_1)
      using possit_sit_1[equiv_lr] "\<^bold>&E"(1) apply blast
      using qml_3[axiom_instance, deduction] "\<^bold>&E"(2) by blast
    using qml_2[axiom_instance,deduction] by auto
end
end
