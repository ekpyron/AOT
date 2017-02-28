(*<*)
theory TAO_99_Sanity_Tests
imports TAO_7_Axioms
begin
(*>*)

section{* Sanity Tests *}

subsection{* Consistency *}

context
begin
  lemma "True"
    nitpick[expect=genuine, user_axioms, satisfy]
    by auto
end

subsection{* Intensionality *}

context
begin
    interpretation MetaSolver.

    lemma "[(\<^bold>\<lambda>y. (q \<^bold>\<or> \<^bold>\<not>q)) \<^bold>= (\<^bold>\<lambda>y. (p \<^bold>\<or> \<^bold>\<not>p)) in v]"
      unfolding identity_\<Pi>\<^sub>1_def
      apply (rule Eq\<^sub>1I) apply (simp add: meta_defs)
      nitpick[expect = genuine, user_axioms=true,
              sat_solver = MiniSat_JNI,
              card i = 2, card j = 2, card \<sigma> = 1, card \<omega> = 1,
              card "(i \<Rightarrow> bool) \<times> i" = 4,
              card "(i \<Rightarrow> bool) \<times> (i \<Rightarrow> bool) \<times> i" = 4,
              card \<upsilon> = 2, verbose, show_all, debug]
      oops --{* Countermodel by Nitpick *}
    lemma "[(\<^bold>\<lambda>y. (p \<^bold>\<or> q)) \<^bold>= (\<^bold>\<lambda>y. (q \<^bold>\<or> p)) in v]"
      unfolding identity_\<Pi>\<^sub>1_def
      apply (rule Eq\<^sub>1I) apply (simp add: meta_defs)
      nitpick[expect = genuine, user_axioms=true,
              sat_solver = MiniSat_JNI,
              card i = 2, card j = 2, card \<sigma> = 1,
              card \<omega> = 1, card "(i \<Rightarrow> bool) \<times> i" = 4,
              card "(i \<Rightarrow> bool) \<times> (i \<Rightarrow> bool) \<times> i" = 4,
              card \<upsilon> = 2, verbose, show_all, debug]
      oops --{* Countermodel by Nitpick *}
end

subsection{* Concreteness coindices with Object Domains *}
context
begin
  private lemma OrdCheck:
    "[\<lparr>\<^bold>\<lambda> x . \<^bold>\<not>\<^bold>\<box>(\<^bold>\<not>\<lparr>E!, x\<^sup>P\<rparr>), x\<rparr> in v] \<longleftrightarrow>
     (denotes x) \<and> (case (denotation x) of \<omega>\<nu> y \<Rightarrow> True | _ \<Rightarrow> False)"
    using OrdinaryObjectsPossiblyConcreteAxiom
    by (simp add: meta_defs meta_aux split: \<nu>.split \<upsilon>.split)
  private lemma AbsCheck:
    "[\<lparr>\<^bold>\<lambda> x . \<^bold>\<box>(\<^bold>\<not>\<lparr>E!, x\<^sup>P\<rparr>), x\<rparr> in v] \<longleftrightarrow>
     (denotes x) \<and> (case (denotation x) of \<alpha>\<nu> y \<Rightarrow> True | _ \<Rightarrow> False)"
    using OrdinaryObjectsPossiblyConcreteAxiom
    by (simp add: meta_defs meta_aux split: \<nu>.split \<upsilon>.split)
end

subsection{* Justification for Meta-Logical Axioms *}

context
begin
text{*
\begin{remark}
  OrdinaryObjectsPossiblyConcreteAxiom is equivalent to "all ordinary objects are
   possibly concrete".
\end{remark}
*}
  private lemma OrdAxiomCheck:
    "OrdinaryObjectsPossiblyConcrete \<longleftrightarrow>
      (\<forall> x. ([\<lparr>\<^bold>\<lambda> x . \<^bold>\<not>\<^bold>\<box>(\<^bold>\<not>\<lparr>E!, x\<^sup>P\<rparr>), x\<^sup>P\<rparr> in v]
       \<longleftrightarrow> (case x of \<omega>\<nu> y \<Rightarrow> True | _ \<Rightarrow> False)))"
    unfolding Concrete_def by (auto simp: meta_defs meta_aux split: \<nu>.split \<upsilon>.split)

text{*
\begin{remark}
  OrdinaryObjectsPossiblyConcreteAxiom is equivalent to "all abstract objects are
  necessarily not concrete".
\end{remark}
*}
  private lemma AbsAxiomCheck:
    "OrdinaryObjectsPossiblyConcrete \<longleftrightarrow>
      (\<forall> x. ([\<lparr>\<^bold>\<lambda> x . \<^bold>\<box>(\<^bold>\<not>\<lparr>E!, x\<^sup>P\<rparr>), x\<^sup>P\<rparr> in v]
       \<longleftrightarrow> (case x of \<alpha>\<nu> y \<Rightarrow> True | _ \<Rightarrow> False)))"
    by (auto simp: meta_defs meta_aux split: \<nu>.split \<upsilon>.split)
  
text{*
\begin{remark}
  PossiblyContingentObjectExistsAxiom is equivalent to the corresponding statement
  in the embedded logic.
\end{remark}
*}
  private lemma PossiblyContingentObjectExistsCheck:
    "[\<^bold>\<not>(\<^bold>\<box>(\<^bold>\<forall> x. \<lparr>E!,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>E!,x\<^sup>P\<rparr>)) in v]"
     apply (simp add: meta_defs forall_\<nu>_def meta_aux split: \<nu>.split \<upsilon>.split)
     using PossiblyContingentObjectExistsAxiom
     by (metis \<nu>.simps(5) \<nu>\<upsilon>_def \<upsilon>.simps(1) no_\<sigma>\<omega>)
  private lemma "PossiblyContingentObjectExists"
    apply (auto simp: meta_defs)
    using PossiblyContingentObjectExistsCheck
    apply (auto simp: meta_defs forall_\<nu>_def meta_aux split: \<nu>.split \<upsilon>.split)
    by (metis \<upsilon>.exhaust \<upsilon>.simps(5) \<upsilon>.simps(6))

text{*
\begin{remark}
  PossiblyNoContingentObjectExistsAxiom is equivalent to the corresponding statement
  in the embedded logic.
\end{remark}
*}
  private lemma PossiblyNoContingentObjectExistsCheck:
    "[\<^bold>\<not>(\<^bold>\<box>(\<^bold>\<not>(\<^bold>\<forall> x. \<lparr>E!,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>E!,x\<^sup>P\<rparr>))) in v]"
    apply (simp add: meta_defs forall_\<nu>_def meta_aux split: \<nu>.split \<upsilon>.split)
    using PossiblyNoContingentObjectExistsAxiom by blast  
  private lemma "PossiblyNoContingentObjectExists"
    using PossiblyNoContingentObjectExistsCheck
    apply (auto simp: meta_defs forall_\<nu>_def meta_aux split: \<nu>.split \<upsilon>.split)
    by (metis \<upsilon>.simps(5) \<nu>\<upsilon>_\<upsilon>\<nu>_id)
end

subsection{* Relations in the Meta-Logic *}

context
begin
text{*
\begin{remark}
  Material equality in the embedded logic corresponds to
  equality in the actual state in the meta-logic.
\end{remark}
*}
  private lemma mat_eq_is_eq_dj:
    "[\<^bold>\<forall> x . \<^bold>\<box>(\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>G,x\<^sup>P\<rparr>) in v] \<longleftrightarrow>
     ((\<lambda> x . (eval\<Pi>\<^sub>1 F) x dj) = (\<lambda> x . (eval\<Pi>\<^sub>1 G) x dj))"
  proof
    interpret MetaSolver .
    interpret Semantics .
    assume 1: "[\<^bold>\<forall>x. \<^bold>\<box>(\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>G,x\<^sup>P\<rparr>) in v]"
    {
      fix v
      fix y
      obtain x where y_def: "y = \<nu>\<upsilon> x" by (metis \<nu>\<upsilon>_\<upsilon>\<nu>_id)
      have "(\<exists>r o\<^sub>1. Some r = d\<^sub>1 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> (x\<^sup>P) \<and> o\<^sub>1 \<in> ex1 r v) =
            (\<exists>r o\<^sub>1. Some r = d\<^sub>1 G \<and> Some o\<^sub>1 = d\<^sub>\<kappa> (x\<^sup>P) \<and> o\<^sub>1 \<in> ex1 r v)"
            using 1 apply cut_tac by meta_solver
      moreover obtain r where r_def: "Some r = d\<^sub>1 F"
        unfolding d\<^sub>1_def by auto
      moreover obtain s where s_def: "Some s = d\<^sub>1 G"
        unfolding d\<^sub>1_def by auto
      moreover have "Some x = d\<^sub>\<kappa> (x\<^sup>P)"
        using d\<^sub>\<kappa>_proper by simp
      ultimately have "(x \<in> ex1 r v) = (x \<in> ex1 s v)"
        by (metis option.inject)
      hence "(eval\<Pi>\<^sub>1 F) y dj v = (eval\<Pi>\<^sub>1 G) y dj v"
        using r_def s_def y_def by (simp add: d\<^sub>1.rep_eq ex1_def)
    }
    thus "(\<lambda>x. eval\<Pi>\<^sub>1 F x dj) = (\<lambda>x. eval\<Pi>\<^sub>1 G x dj)"
      by auto
  next
    interpret MetaSolver .
    interpret Semantics .
    assume 1: "(\<lambda>x. eval\<Pi>\<^sub>1 F x dj) = (\<lambda>x. eval\<Pi>\<^sub>1 G x dj)"
    {
      fix y v
      obtain x where x_def: "x = \<nu>\<upsilon> y"
        by simp
      hence "eval\<Pi>\<^sub>1 F x dj = eval\<Pi>\<^sub>1 G x dj"
        using 1 by metis
      moreover obtain r where r_def: "Some r = d\<^sub>1 F"
        unfolding d\<^sub>1_def by auto
      moreover obtain s where s_def: "Some s = d\<^sub>1 G"
        unfolding d\<^sub>1_def by auto
      ultimately have "(y \<in> ex1 r v) = (y \<in> ex1 s v)"
        by (simp add: d\<^sub>1.rep_eq ex1_def \<nu>\<upsilon>_\<upsilon>\<nu>_id x_def)
      hence "[\<lparr>F,y\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>G,y\<^sup>P\<rparr> in v]"
        apply cut_tac apply meta_solver
        using r_def s_def by (metis Semantics.d\<^sub>\<kappa>_proper option.inject)
    }
    thus "[\<^bold>\<forall>x. \<^bold>\<box>(\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>G,x\<^sup>P\<rparr>) in v]"
      using T6 T8 by fast
  qed

text{*
\begin{remark}
  Material equivalent relations are equal in the embedded logic
  if and only if they also coincide in all other states.
\end{remark}
*}
  private lemma mat_eq_is_eq_if_eq_forall_j:
    assumes "[\<^bold>\<forall> x . \<^bold>\<box>(\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>G,x\<^sup>P\<rparr>) in v]"
    shows "[F \<^bold>= G in v] \<longleftrightarrow>
           (\<forall> s . s \<noteq> dj \<longrightarrow> (\<forall> x . (eval\<Pi>\<^sub>1 F) x s = (eval\<Pi>\<^sub>1 G) x s))"
    proof
      interpret MetaSolver .
      assume "[F \<^bold>= G in v]"
      hence "F = G"
        apply cut_tac unfolding identity_\<Pi>\<^sub>1_def by meta_solver
      thus "\<forall>s. s \<noteq> dj \<longrightarrow> (\<forall>x. eval\<Pi>\<^sub>1 F x s = eval\<Pi>\<^sub>1 G x s)"
        by auto
    next
      interpret MetaSolver .
      assume "\<forall>s. s \<noteq> dj \<longrightarrow> (\<forall>x. eval\<Pi>\<^sub>1 F x s = eval\<Pi>\<^sub>1 G x s)"
      moreover have "((\<lambda> x . (eval\<Pi>\<^sub>1 F) x dj) = (\<lambda> x . (eval\<Pi>\<^sub>1 G) x dj))"
        using assms mat_eq_is_eq_dj by auto
      ultimately have "\<forall>s x. eval\<Pi>\<^sub>1 F x s = eval\<Pi>\<^sub>1 G x s"
        by metis
      hence "eval\<Pi>\<^sub>1 F = eval\<Pi>\<^sub>1 G"
        by blast
      hence "F = G"
        by (metis eval\<Pi>\<^sub>1_inverse)
      thus "[F \<^bold>= G in v]"
        unfolding identity_\<Pi>\<^sub>1_def using Eq\<^sub>1I by auto
    qed

text{*
\begin{remark}
  Under the assumption that all properties behave in all states like in the actual state
  the defined equality degenerates to material equality.
\end{remark}
*}
  lemma assumes "\<forall> F x s . (eval\<Pi>\<^sub>1 F) x s = (eval\<Pi>\<^sub>1 F) x dj"
    shows "[\<^bold>\<forall> x . \<^bold>\<box>(\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>G,x\<^sup>P\<rparr>) in v] \<longleftrightarrow> [F \<^bold>= G in v]"
    by (metis (no_types) MetaSolver.Eq\<^sub>1S assms identity_\<Pi>\<^sub>1_def
                         mat_eq_is_eq_dj mat_eq_is_eq_if_eq_forall_j)

end
(*<*)
end
(*>*)
