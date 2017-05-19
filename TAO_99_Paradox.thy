theory TAO_99_Paradox
imports TAO_9_PLM TAO_98_ArtificialTheorems
begin

section{* Paradox *}

(*<*)
locale Paradox = PLM
begin
(*>*)
  
  lemma exe_impl_exists:
    "[\<lparr>(\<^bold>\<lambda>x . \<^bold>\<forall> p . p \<^bold>\<rightarrow> p), \<^bold>\<iota>y . \<phi> y x\<rparr> \<^bold>\<equiv> (\<^bold>\<exists>!y . \<^bold>\<A>\<phi> y x) in v]"
    proof (rule "\<^bold>\<equiv>I"; rule CP)
      fix \<phi> :: "\<nu>\<Rightarrow>\<nu>\<Rightarrow>\<o>" and x :: \<nu> and v :: i
      assume "[\<lparr>(\<^bold>\<lambda>x . \<^bold>\<forall> p . p \<^bold>\<rightarrow> p),\<^bold>\<iota>y . \<phi> y x\<rparr> in v]"
      hence "[\<^bold>\<exists>y. \<^bold>\<A>\<phi> y x \<^bold>& (\<^bold>\<forall>z. \<^bold>\<A>\<phi> z x \<^bold>\<rightarrow> z \<^bold>= y)
              \<^bold>& \<lparr>(\<^bold>\<lambda>x . \<^bold>\<forall> p . p \<^bold>\<rightarrow> p), y\<^sup>P\<rparr> in v]"
        using nec_russell_axiom[equiv_lr] SimpleExOrEnc.intros by auto
      then obtain y where
        "[\<^bold>\<A>\<phi> y x \<^bold>& (\<^bold>\<forall>z. \<^bold>\<A>\<phi> z x \<^bold>\<rightarrow> z \<^bold>= y)
          \<^bold>& \<lparr>(\<^bold>\<lambda>x . \<^bold>\<forall> p . p \<^bold>\<rightarrow> p), y\<^sup>P\<rparr> in v]"
        by (rule Instantiate)
      hence "[\<^bold>\<A>\<phi> y x \<^bold>& (\<^bold>\<forall>z. \<^bold>\<A>\<phi> z x \<^bold>\<rightarrow> z \<^bold>= y) in v]"
        using "\<^bold>&E" by blast
      hence "[\<^bold>\<exists>y . \<^bold>\<A>\<phi> y x \<^bold>& (\<^bold>\<forall>z. \<^bold>\<A>\<phi> z x \<^bold>\<rightarrow> z \<^bold>= y) in v]"
        by (rule existential)
      thus "[\<^bold>\<exists>!y. \<^bold>\<A>\<phi> y x in v]"
        unfolding exists_unique_def by simp
    next
      fix \<phi> :: "\<nu>\<Rightarrow>\<nu>\<Rightarrow>\<o>" and x :: \<nu> and v :: i
      assume "[\<^bold>\<exists>!y. \<^bold>\<A>\<phi> y x in v]"
      hence "[\<^bold>\<exists>y. \<^bold>\<A>\<phi> y x \<^bold>& (\<^bold>\<forall>z. \<^bold>\<A>\<phi> z x \<^bold>\<rightarrow> z \<^bold>= y) in v]"
        unfolding exists_unique_def by simp
      then obtain y where
        "[\<^bold>\<A>\<phi> y x \<^bold>& (\<^bold>\<forall>z. \<^bold>\<A>\<phi> z x \<^bold>\<rightarrow> z \<^bold>= y) in v]"
        by (rule Instantiate)
      moreover have "[\<lparr>(\<^bold>\<lambda>x . \<^bold>\<forall> p . p \<^bold>\<rightarrow> p),y\<^sup>P\<rparr> in v]"
        apply (rule beta_C_meta_1[equiv_rl])
          apply show_proper
        by PLM_solver
      ultimately have "[\<^bold>\<A>\<phi> y x \<^bold>& (\<^bold>\<forall>z. \<^bold>\<A>\<phi> z x \<^bold>\<rightarrow> z \<^bold>= y)
                        \<^bold>& \<lparr>(\<^bold>\<lambda>x . \<^bold>\<forall> p . p \<^bold>\<rightarrow> p),y\<^sup>P\<rparr> in v]"
        using "\<^bold>&I" by blast
      hence "[\<^bold>\<exists> y . \<^bold>\<A>\<phi> y x \<^bold>& (\<^bold>\<forall>z. \<^bold>\<A>\<phi> z x \<^bold>\<rightarrow> z \<^bold>= y)
              \<^bold>& \<lparr>(\<^bold>\<lambda>x . \<^bold>\<forall> p . p \<^bold>\<rightarrow> p),y\<^sup>P\<rparr> in v]"
        by (rule existential)
      thus "[\<lparr>(\<^bold>\<lambda>x . \<^bold>\<forall> p . p \<^bold>\<rightarrow> p), \<^bold>\<iota>y. \<phi> y x\<rparr> in v]"
        using nec_russell_axiom[equiv_rl]
          SimpleExOrEnc.intros by auto
    qed

  lemma exists_unique_actual_equiv:
    "[(\<^bold>\<exists>!y . \<^bold>\<A>(y \<^bold>= x \<^bold>& \<psi> (x\<^sup>P))) \<^bold>\<equiv> \<^bold>\<A>\<psi> (x\<^sup>P) in v]"
  proof (rule "\<^bold>\<equiv>I"; rule CP)
    fix x v
    let ?\<phi> = "\<lambda> y x. y \<^bold>= x \<^bold>& \<psi> (x\<^sup>P)"
    assume "[\<^bold>\<exists>!y. \<^bold>\<A>?\<phi> y x in v]"
    hence "[\<^bold>\<exists>\<alpha>. \<^bold>\<A>?\<phi> \<alpha> x \<^bold>& (\<^bold>\<forall>\<beta>. \<^bold>\<A>?\<phi> \<beta> x \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
      unfolding exists_unique_def by simp
    then obtain \<alpha> where
      "[\<^bold>\<A>?\<phi> \<alpha> x \<^bold>& (\<^bold>\<forall>\<beta>. \<^bold>\<A>?\<phi> \<beta> x \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
      by (rule Instantiate)
    hence "[\<^bold>\<A>(\<alpha> \<^bold>= x \<^bold>& \<psi> (x\<^sup>P)) in v]"
      using "\<^bold>&E" by blast
    thus "[\<^bold>\<A>(\<psi> (x\<^sup>P)) in v]"
      using Act_Basic_2[equiv_lr] "\<^bold>&E" by blast
  next
    fix x v
    let ?\<phi> = "\<lambda> y x. y \<^bold>= x \<^bold>& \<psi> (x\<^sup>P)"
    assume 1: "[\<^bold>\<A>\<psi> (x\<^sup>P) in v]"
    have "[x \<^bold>= x in v]"
      using id_eq_1[where 'a=\<nu>] by simp
    hence "[\<^bold>\<A>(x \<^bold>= x) in v]"
      using id_act_3[equiv_lr] by fast
    hence "[\<^bold>\<A>(x \<^bold>= x \<^bold>& \<psi> (x\<^sup>P)) in v]"
      using 1 Act_Basic_2[equiv_rl] "\<^bold>&I" by blast
    hence "[\<^bold>\<A>?\<phi> x x in v]"
      by simp
    moreover have "[\<^bold>\<forall>\<beta>. \<^bold>\<A>?\<phi> \<beta> x \<^bold>\<rightarrow> \<beta> \<^bold>= x in v]"
    proof (rule "\<^bold>\<forall>I"; rule CP)
      fix \<beta>
      assume "[\<^bold>\<A>?\<phi> \<beta> x in v]"
      hence "[\<^bold>\<A>(\<beta> \<^bold>= x) in v]"
        using Act_Basic_2[equiv_lr] "\<^bold>&E" by fast
      thus "[\<beta> \<^bold>= x in v]" using id_act_3[equiv_rl] by fast
    qed      
    ultimately have "[\<^bold>\<A>?\<phi> x x \<^bold>& (\<^bold>\<forall>\<beta>. \<^bold>\<A>?\<phi> \<beta> x \<^bold>\<rightarrow> \<beta> \<^bold>= x) in v]"
      using "\<^bold>&I" by fast
    hence "[\<^bold>\<exists>\<alpha>. \<^bold>\<A>?\<phi> \<alpha> x \<^bold>& (\<^bold>\<forall>\<beta>. \<^bold>\<A>?\<phi> \<beta> x \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
      by (rule existential)
    thus "[\<^bold>\<exists>!y. \<^bold>\<A>?\<phi> y x in v]"
      unfolding exists_unique_def by simp
  qed
      
  definition backdoor where
    "backdoor \<equiv> \<lambda> \<psi> . \<^bold>\<lambda>x . \<lparr>(\<^bold>\<lambda>x . \<^bold>\<forall> p . p \<^bold>\<rightarrow> p), \<^bold>\<iota>y . y \<^bold>= x \<^bold>& \<psi> (x\<^sup>P)\<rparr>"
    
  lemma fake_beta:
    assumes "\<And> G \<phi>. IsProperInX (\<lambda>x . \<lparr>G,\<^bold>\<iota>y . \<phi> y x\<rparr>)"
    shows "[\<lparr>backdoor (\<lambda> x . \<psi> x), x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<A>\<psi> (x\<^sup>P) in v]"
  proof (rule "\<^bold>\<equiv>I"; rule CP)
    assume "[\<lparr>backdoor \<psi>,x\<^sup>P\<rparr> in v]"
    hence "[\<lparr>\<^bold>\<lambda>x. \<^bold>\<forall>p. p \<^bold>\<rightarrow> p,\<^bold>\<iota>y. y \<^bold>= x \<^bold>& \<psi> (x\<^sup>P)\<rparr> in v]"
      using beta_C_meta_1[equiv_lr, OF assms]
      unfolding backdoor_def identity_\<nu>_def by fast
    hence "[\<^bold>\<exists>!y. \<^bold>\<A> (y \<^bold>= x \<^bold>& \<psi> (x\<^sup>P)) in v]"
      using exe_impl_exists[equiv_lr] by fast
    thus "[\<^bold>\<A>\<psi> (x\<^sup>P) in v]"
      using exists_unique_actual_equiv[equiv_lr] by blast
  next
    assume "[\<^bold>\<A>\<psi> (x\<^sup>P) in v]"
    hence "[\<^bold>\<exists>!y. \<^bold>\<A> (y \<^bold>= x \<^bold>& \<psi> (x\<^sup>P)) in v]"
      using exists_unique_actual_equiv[equiv_rl] by blast
    hence "[\<lparr>\<^bold>\<lambda>x. \<^bold>\<forall>p. p \<^bold>\<rightarrow> p,\<^bold>\<iota>y. y \<^bold>= x \<^bold>& \<psi> (x\<^sup>P)\<rparr> in v]"
      using exe_impl_exists[equiv_rl] by fast
    thus "[\<lparr>backdoor \<psi>,x\<^sup>P\<rparr> in v]"
      using beta_C_meta_1[equiv_rl, OF assms]
      unfolding backdoor_def unfolding identity_\<nu>_def by fast
  qed

  lemma fake_beta_act:
    assumes "\<And> G \<phi>. IsProperInX (\<lambda>x . \<lparr>G,\<^bold>\<iota>y . \<phi> y x\<rparr>)"
    shows "[\<lparr>backdoor (\<lambda> x . \<psi> x), x\<^sup>P\<rparr> \<^bold>\<equiv> \<psi> (x\<^sup>P) in dw]"
    using fake_beta[OF assms]
      logic_actual[necessitation_averse_axiom_instance]
      intro_elim_6_e by blast
      
  lemma paradox:
    assumes "\<And> G \<phi>. IsProperInX (\<lambda>x . \<lparr>G,\<^bold>\<iota>y . \<phi> y x\<rparr>)"
    shows "False"
  proof -
    obtain K where K_def:
      "K = backdoor (\<lambda> x . \<^bold>\<exists> F . \<lbrace>x,F\<rbrace> \<^bold>& \<^bold>\<not>\<lparr>F,x\<rparr>)" by auto
    have "[\<^bold>\<exists>x. \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall>F. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> (F \<^bold>= K)) in dw]"
      using A_objects[axiom_instance] by fast
    then obtain x where x_prop:
      "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall>F. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> (F \<^bold>= K)) in dw]"
      by (rule Instantiate)
    {
      assume "[\<lparr>K,x\<^sup>P\<rparr> in dw]"
      hence "[\<^bold>\<exists> F . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>& \<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr> in dw]"
        unfolding K_def using fake_beta_act[OF assms, equiv_lr]
        by blast
      then obtain F where F_def:
        "[\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>& \<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr> in dw]" by (rule Instantiate)
      hence "[F \<^bold>= K in dw]"
        using x_prop[conj2, THEN "\<^bold>\<forall>E"[where \<beta>=F], equiv_lr]
          "\<^bold>&E" unfolding K_def by blast
      hence "[\<^bold>\<not>\<lparr>K,x\<^sup>P\<rparr> in dw]"
        using l_identity[axiom_instance,deduction,deduction]
             F_def[conj2] by fast
    }
    hence 1: "[\<^bold>\<not>\<lparr>K,x\<^sup>P\<rparr> in dw]"
      using reductio_aa_1 by blast
    hence "[\<^bold>\<not>(\<^bold>\<exists> F . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>& \<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>) in dw]"
      using fake_beta_act[OF assms,
            THEN oth_class_taut_5_d[equiv_lr],
            equiv_lr]
      unfolding K_def by blast
    hence "[\<^bold>\<forall> F . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<rightarrow> \<lparr>F,x\<^sup>P\<rparr> in dw]"
      apply - unfolding exists_def by PLM_solver
    moreover have "[\<lbrace>x\<^sup>P,K\<rbrace> in dw]"
      using x_prop[conj2, THEN "\<^bold>\<forall>E"[where \<beta>=K], equiv_rl]
            id_eq_1 by blast
    ultimately have "[\<lparr>K,x\<^sup>P\<rparr> in dw]"
      using "\<^bold>\<forall>E" vdash_properties_10 by blast
    hence "\<And>\<phi>. [\<phi> in dw]"
      using raa_cor_2 1 by blast
    thus "False" using Semantics.T4 by auto
  qed

(*<*)
end
(*>*)

end
