theory TAO_99_Sanity_Tests
imports TAO_7_Axioms
begin

section{* Sanity Tests *}

subsection{* Consistency *}

context
begin
  lemma "True" nitpick[expect=genuine, user_axioms, satisfy] by auto
end

subsection{* Intensionality *}

context
begin
    interpretation MetaSolver.

    lemma "[(\<^bold>\<lambda>y. (q \<^bold>\<or> \<^bold>\<not>q)) \<^bold>= (\<^bold>\<lambda>y. (p \<^bold>\<or> \<^bold>\<not>p)) in v]"
      unfolding identity_\<Pi>\<^sub>1_def
      apply (rule Eq\<^sub>1I) apply (simp add: meta_defs)
      nitpick[expect = genuine, user_axioms=true, sat_solver = MiniSat_JNI,
              card i = 2, card j = 2, card \<sigma> = 1, card \<omega> = 1, card "(i \<Rightarrow> bool) \<times> i" = 4,
              card "(i \<Rightarrow> bool) \<times> (i \<Rightarrow> bool) \<times> i" = 4, card \<upsilon> = 2, verbose, show_all, debug]
      oops --{* Countermodel by Nitpick *}
    lemma "[(\<^bold>\<lambda>y. (p \<^bold>\<or> q)) \<^bold>= (\<^bold>\<lambda>y. (q \<^bold>\<or> p)) in v]"
      unfolding identity_\<Pi>\<^sub>1_def
      apply (rule Eq\<^sub>1I) apply (simp add: meta_defs)
      nitpick[expect = genuine, user_axioms=true, sat_solver = MiniSat_JNI,
              card i = 2, card j = 2, card \<sigma> = 1, card \<omega> = 1, card "(i \<Rightarrow> bool) \<times> i" = 4,
              card "(i \<Rightarrow> bool) \<times> (i \<Rightarrow> bool) \<times> i" = 4, card \<upsilon> = 2, verbose, show_all, debug]
      oops --{* Countermodel by Nitpick *}
end

text{* Concreteness coindices with object domains. *}
context
begin
  private lemma OrdCheck: "[\<lparr>\<^bold>\<lambda> x . \<^bold>\<not>\<^bold>\<box>(\<^bold>\<not>\<lparr>E!, x\<^sup>P\<rparr>), x\<rparr> in v] \<longleftrightarrow> (meta_denotes x) \<and> (case (denotation x) of \<omega>\<nu> y \<Rightarrow> True | _ \<Rightarrow> False)"
    using OrdinaryObjectsPossiblyConcreteAxiom
    by (simp add: meta_defs meta_aux split: \<nu>.split \<upsilon>.split)
  private lemma AbsCheck: "[\<lparr>\<^bold>\<lambda> x . \<^bold>\<box>(\<^bold>\<not>\<lparr>E!, x\<^sup>P\<rparr>), x\<rparr> in v] \<longleftrightarrow> (meta_denotes x) \<and> (case (denotation x) of \<alpha>\<nu> y \<Rightarrow> True | _ \<Rightarrow> False)"
    using OrdinaryObjectsPossiblyConcreteAxiom
    by (simp add: meta_defs meta_aux split: \<nu>.split \<upsilon>.split)
end

text{* Justification for Axioms *}

context
begin
  text{* OrdinaryObjectsPossiblyConcreteAxiom is equivalent to "all ordinary objects are
         possibly concrete". *}
  private lemma OrdAxiomCheck: "OrdinaryObjectsPossiblyConcrete
    \<longleftrightarrow> (\<forall> x. ([\<lparr>\<^bold>\<lambda> x . \<^bold>\<not>\<^bold>\<box>(\<^bold>\<not>\<lparr>E!, x\<^sup>P\<rparr>), x\<^sup>P\<rparr> in v] \<longleftrightarrow> (case x of \<omega>\<nu> y \<Rightarrow> True | _ \<Rightarrow> False)))"
    unfolding Concrete_def by (auto simp: meta_defs meta_aux split: \<nu>.split \<upsilon>.split)
  text{* OrdinaryObjectsPossiblyConcreteAxiom is equivalent to "all abstract objects are
         necessarily not concrete". *}
  private lemma AbsAxiomCheck: "OrdinaryObjectsPossiblyConcrete
    \<longleftrightarrow> (\<forall> x. ([\<lparr>\<^bold>\<lambda> x . \<^bold>\<box>(\<^bold>\<not>\<lparr>E!, x\<^sup>P\<rparr>), x\<^sup>P\<rparr> in v] \<longleftrightarrow> (case x of \<alpha>\<nu> y \<Rightarrow> True | _ \<Rightarrow> False)))"
    by (auto simp: meta_defs meta_aux split: \<nu>.split \<upsilon>.split)
  
  text{* PossiblyContingentObjectExistsAxiom is equivalent to the corresponding statement
         in the embedded logic. *}
  private lemma PossiblyContingentObjectExistsCheck: "[\<^bold>\<not>(\<^bold>\<box>(\<^bold>\<forall> x. \<lparr>E!,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>E!,x\<^sup>P\<rparr>)) in v]"
     apply (simp add: meta_defs forall_\<nu>_def meta_aux split: \<nu>.split \<upsilon>.split)
     using PossiblyContingentObjectExistsAxiom
     by (metis \<nu>.simps(5) \<nu>\<upsilon>_def \<upsilon>.simps(1) no_\<sigma>\<omega>)
  private lemma "PossiblyContingentObjectExists"
    apply (auto simp: meta_defs)
    using PossiblyContingentObjectExistsCheck
    apply (auto simp: meta_defs forall_\<nu>_def meta_aux split: \<nu>.split \<upsilon>.split)
    by (metis \<upsilon>.exhaust \<upsilon>.simps(5) \<upsilon>.simps(6))

  text{* PossiblyNoContingentObjectExistsAxiom is equivalent to the corresponding statement
         in the embedded logic. *}
  private lemma PossiblyNoContingentObjectExistsCheck: "[\<^bold>\<not>(\<^bold>\<box>(\<^bold>\<not>(\<^bold>\<forall> x. \<lparr>E!,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>E!,x\<^sup>P\<rparr>))) in v]"
    apply (simp add: meta_defs forall_\<nu>_def meta_aux split: \<nu>.split \<upsilon>.split)
    using PossiblyNoContingentObjectExistsAxiom by blast  
  private lemma "PossiblyNoContingentObjectExists"
    using PossiblyNoContingentObjectExistsCheck
    apply (auto simp: meta_defs forall_\<nu>_def meta_aux split: \<nu>.split \<upsilon>.split)
    by (metis \<upsilon>.simps(5) \<nu>\<upsilon>_\<upsilon>\<nu>_id)
end

end
