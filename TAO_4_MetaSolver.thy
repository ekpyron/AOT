(*<*)
theory TAO_4_MetaSolver
imports TAO_3_Semantics TAO_2_BasicDefinitions "~~/src/HOL/Eisbach/Eisbach"
begin
(*>*)

section{* MetaSolver *}
text{* \label{TAO_MetaSolver} *}

text{*
\begin{remark}
  @{text "meta_solver"} is a resolution prover that translates
  expressions in the embedded logic to expressions in the meta-logic,
  resp. semantic expressions as far as possible.
  The rules for connectives, quantifiers, exemplification
  and encoding are easy to prove.
  Futhermore rules for the defined identities are derived using more verbose proofs.
  By design the defined identities in the embedded logic coincide with the
  meta-logical equality.
\end{remark}
*}

locale MetaSolver
begin
  interpretation Semantics .

  named_theorems meta_intro
  named_theorems meta_elim
  named_theorems meta_subst
  named_theorems meta_cong

  method meta_solver = (assumption | rule meta_intro
      | erule meta_elim | drule meta_elim |  subst meta_subst
      | subst (asm) meta_subst | (erule notE; (meta_solver; fail))
      )+

subsection{* Rules for Implication *}
text{* \label{TAO_MetaSolver_Implication} *}

  lemma ImplI[meta_intro]: "([\<phi> in v] \<Longrightarrow> [\<psi> in v]) \<Longrightarrow> ([\<phi> \<^bold>\<rightarrow> \<psi> in v])"
    by (simp add: Semantics.T5)
  lemma ImplE[meta_elim]: "([\<phi> \<^bold>\<rightarrow> \<psi> in v]) \<Longrightarrow> ([\<phi> in v] \<longrightarrow> [\<psi> in v])"
    by (simp add: Semantics.T5)
  lemma ImplS[meta_subst]: "([\<phi> \<^bold>\<rightarrow> \<psi> in v]) = ([\<phi> in v] \<longrightarrow> [\<psi> in v])"
    by (simp add: Semantics.T5)

subsection{* Rules for Negation *}
text{* \label{TAO_MetaSolver_Negation} *}

  lemma NotI[meta_intro]: "\<not>[\<phi> in v] \<Longrightarrow> [\<^bold>\<not>\<phi> in v]"
    by (simp add: Semantics.T4)
  lemma NotE[meta_elim]: "[\<^bold>\<not>\<phi> in v] \<Longrightarrow> \<not>[\<phi> in v]"
    by (simp add: Semantics.T4)
  lemma NotS[meta_subst]: "[\<^bold>\<not>\<phi> in v] = (\<not>[\<phi> in v])"
    by (simp add: Semantics.T4)

subsection{* Rules for Conjunction *}
text{* \label{TAO_MetaSolver_Conjunction} *}

  lemma ConjI[meta_intro]: "([\<phi> in v] \<and> [\<psi> in v]) \<Longrightarrow> [\<phi> \<^bold>& \<psi> in v]"
    by (simp add: conj_def NotS ImplS)
  lemma ConjE[meta_elim]: "[\<phi> \<^bold>& \<psi> in v] \<Longrightarrow> ([\<phi> in v] \<and> [\<psi> in v])"
    by (simp add: conj_def NotS ImplS)
  lemma ConjS[meta_subst]: "[\<phi> \<^bold>& \<psi> in v] = ([\<phi> in v] \<and> [\<psi> in v])"
    by (simp add: conj_def NotS ImplS)

subsection{* Rules for Equivalence *}
text{* \label{TAO_MetaSolver_Equivalence} *}

  lemma EquivI[meta_intro]: "([\<phi> in v] \<longleftrightarrow> [\<psi> in v]) \<Longrightarrow> [\<phi> \<^bold>\<equiv> \<psi> in v]"
    by (simp add: equiv_def NotS ImplS ConjS)
  lemma EquivE[meta_elim]: "[\<phi> \<^bold>\<equiv> \<psi> in v] \<Longrightarrow> ([\<phi> in v] \<longleftrightarrow> [\<psi> in v])"
    by (auto simp: equiv_def NotS ImplS ConjS)
  lemma EquivS[meta_subst]: "[\<phi> \<^bold>\<equiv> \<psi> in v] = ([\<phi> in v] \<longleftrightarrow> [\<psi> in v])"
    by (auto simp: equiv_def NotS ImplS ConjS)

subsection{* Rules for Disjunction *}
text{* \label{TAO_MetaSolver_Disjunction} *}

  lemma DisjI[meta_intro]: "([\<phi> in v] \<or> [\<psi> in v]) \<Longrightarrow> [\<phi> \<^bold>\<or> \<psi> in v]"
    by (auto simp: disj_def NotS ImplS)
  lemma DisjE[meta_elim]: "[\<phi> \<^bold>\<or> \<psi> in v] \<Longrightarrow> ([\<phi> in v] \<or> [\<psi> in v])"
    by (auto simp: disj_def NotS ImplS)
  lemma DisjS[meta_subst]: "[\<phi> \<^bold>\<or> \<psi> in v] = ([\<phi> in v] \<or> [\<psi> in v])"
    by (auto simp: disj_def NotS ImplS)

subsection{* Rules for Necessity *}
text{* \label{TAO_MetaSolver_Necessity} *}

  lemma BoxI[meta_intro]: "(\<And>v.[\<phi> in v]) \<Longrightarrow> [\<^bold>\<box>\<phi> in v]"
    by (simp add: Semantics.T6)
  lemma BoxE[meta_elim]: "[\<^bold>\<box>\<phi> in v] \<Longrightarrow> (\<And>v.[\<phi> in v])"
    by (simp add: Semantics.T6)
  lemma BoxS[meta_subst]: "[\<^bold>\<box>\<phi> in v] = (\<forall> v.[\<phi> in v])"
    by (simp add: Semantics.T6)

subsection{* Rules for Possibility *}
text{* \label{TAO_MetaSolver_Possibility} *}

  lemma DiaI[meta_intro]: "(\<exists>v.[\<phi> in v]) \<Longrightarrow> [\<^bold>\<diamond>\<phi> in v]"
    by (metis BoxS NotS diamond_def)
  lemma DiaE[meta_elim]: "[\<^bold>\<diamond>\<phi> in v] \<Longrightarrow> (\<exists>v.[\<phi> in v])"
    by (metis BoxS NotS diamond_def)
  lemma DiaS[meta_subst]: "[\<^bold>\<diamond>\<phi> in v] = (\<exists> v.[\<phi> in v])"
    by (metis BoxS NotS diamond_def)

subsection{* Rules for Quantification *}
text{* \label{TAO_MetaSolver_Quantification} *}

  lemma All\<^sub>\<nu>I[meta_intro]: "(\<And>x::\<nu>. [\<phi> x in v]) \<Longrightarrow> [\<^bold>\<forall>\<^sub>\<nu> x. \<phi> x in v]"
    by (auto simp: Semantics.T8_\<nu>)
  lemma All\<^sub>\<nu>E[meta_elim]: "[\<^bold>\<forall>\<^sub>\<nu>x. \<phi> x in v] \<Longrightarrow> (\<And>x::\<nu>.[\<phi> x in v])"
    by (auto simp: Semantics.T8_\<nu>)
  lemma All\<^sub>\<nu>S[meta_subst]: "[\<^bold>\<forall>\<^sub>\<nu>x. \<phi> x in v] = (\<forall>x::\<nu>.[\<phi> x in v])"
    by (auto simp: Semantics.T8_\<nu>)

  lemma All\<^sub>0I[meta_intro]: "(\<And>x::\<Pi>\<^sub>0. [\<phi> x in v]) \<Longrightarrow> [\<^bold>\<forall>\<^sub>0 x. \<phi> x in v]"
    by (auto simp: Semantics.T8_0)
  lemma All\<^sub>0E[meta_elim]: "[\<^bold>\<forall>\<^sub>0 x. \<phi> x in v] \<Longrightarrow> (\<And>x::\<Pi>\<^sub>0 .[\<phi> x in v])"
    by (auto simp: Semantics.T8_0)
  lemma All\<^sub>0S[meta_subst]: "[\<^bold>\<forall>\<^sub>0 x. \<phi> x in v] = (\<forall>x::\<Pi>\<^sub>0.[\<phi> x in v])"
    by (auto simp: Semantics.T8_0)

  lemma All\<^sub>1I[meta_intro]: "(\<And>x::\<Pi>\<^sub>1. [\<phi> x in v]) \<Longrightarrow> [\<^bold>\<forall>\<^sub>1 x. \<phi> x in v]"
    by (auto simp: Semantics.T8_1)
  lemma All\<^sub>1E[meta_elim]: "[\<^bold>\<forall>\<^sub>1 x. \<phi> x in v] \<Longrightarrow> (\<And>x::\<Pi>\<^sub>1 .[\<phi> x in v])"
    by (auto simp: Semantics.T8_1)
  lemma All\<^sub>1S[meta_subst]: "[\<^bold>\<forall>\<^sub>1 x. \<phi> x in v] = (\<forall>x::\<Pi>\<^sub>1.[\<phi> x in v])"
    by (auto simp: Semantics.T8_1)

  lemma All\<^sub>2I[meta_intro]: "(\<And>x::\<Pi>\<^sub>2. [\<phi> x in v]) \<Longrightarrow> [\<^bold>\<forall>\<^sub>2 x. \<phi> x in v]"
    by (auto simp: Semantics.T8_2)
  lemma All\<^sub>2E[meta_elim]: "[\<^bold>\<forall>\<^sub>2 x. \<phi> x in v] \<Longrightarrow> (\<And>x::\<Pi>\<^sub>2 .[\<phi> x in v])"
    by (auto simp: Semantics.T8_2)
  lemma All\<^sub>2S[meta_subst]: "[\<^bold>\<forall>\<^sub>2 x. \<phi> x in v] = (\<forall>x::\<Pi>\<^sub>2.[\<phi> x in v])"
    by (auto simp: Semantics.T8_2)

  lemma All\<^sub>3I[meta_intro]: "(\<And>x::\<Pi>\<^sub>3. [\<phi> x in v]) \<Longrightarrow> [\<^bold>\<forall>\<^sub>3 x. \<phi> x in v]"
    by (auto simp: Semantics.T8_3)
  lemma All\<^sub>3E[meta_elim]: "[\<^bold>\<forall>\<^sub>3 x. \<phi> x in v] \<Longrightarrow> (\<And>x::\<Pi>\<^sub>3. [\<phi> x in v])"
    by (auto simp: Semantics.T8_3)
  lemma All\<^sub>3S[meta_subst]: "[\<^bold>\<forall>\<^sub>3 x. \<phi> x in v] = (\<forall>x::\<Pi>\<^sub>3. [\<phi> x in v])"
    by (auto simp: Semantics.T8_3)

subsection{* Rules for Actuality *}
text{* \label{TAO_MetaSolver_Actuality} *}

  lemma ActualI[meta_intro]: "[\<phi> in dw] \<Longrightarrow> [\<^bold>\<A>\<phi> in v]"
    by (auto simp: Semantics.T7)
  lemma ActualE[meta_elim]: "[\<^bold>\<A>\<phi> in v] \<Longrightarrow> [\<phi> in dw]"
    by (auto simp: Semantics.T7)
  lemma ActualS[meta_subst]: "[\<^bold>\<A>\<phi> in v] = [\<phi> in dw]"
    by (auto simp: Semantics.T7)

subsection {* Rules for Encoding *}
text{* \label{TAO_MetaSolver_Encoding} *}

  lemma EncI[meta_intro]:
    assumes "\<exists> r o\<^sub>1 . Some r = d\<^sub>1 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 \<in> en r"
    shows "[\<lbrace>x,F\<rbrace> in v]"
    using assms by (auto simp: Semantics.T2)
  lemma EncE[meta_elim]:
    assumes "[\<lbrace>x,F\<rbrace> in v]"
    shows "\<exists> r o\<^sub>1 . Some r = d\<^sub>1 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 \<in> en r"
    using assms by (auto simp: Semantics.T2)
  lemma EncS[meta_subst]:
    "[\<lbrace>x,F\<rbrace> in v] = (\<exists> r o\<^sub>1 . Some r = d\<^sub>1 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 \<in> en r)"
    by (auto simp: Semantics.T2)

subsection{* Rules for Exemplification *}
text{* \label{TAO_MetaSolver_Exemplification} *}

subsubsection{* Zero-place Relations *}

  lemma Exe0I[meta_intro]:
    assumes "\<exists> r . Some r = d\<^sub>0 p \<and> ex0 r v"
    shows "[\<lparr>p\<rparr> in v]"
    using assms by (auto simp: Semantics.T3)
  lemma Exe0E[meta_elim]:
    assumes "[\<lparr>p\<rparr> in v]"
    shows "\<exists> r . Some r = d\<^sub>0 p \<and> ex0 r v"
    using assms by (auto simp: Semantics.T3)
  lemma Exe0S[meta_subst]:
    "[\<lparr>p\<rparr> in v] = (\<exists> r . Some r = d\<^sub>0 p \<and> ex0 r v)"
    by (auto simp: Semantics.T3)

subsubsection{* One-Place Relations *}

  lemma Exe1I[meta_intro]:
    assumes "\<exists> r o\<^sub>1 . Some r = d\<^sub>1 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 \<in> ex1 r v"
    shows "[\<lparr>F,x\<rparr> in v]"
    using assms by (auto simp: Semantics.T1_1)
  lemma Exe1E[meta_elim]:
    assumes "[\<lparr>F,x\<rparr> in v]"
    shows "\<exists> r o\<^sub>1 . Some r = d\<^sub>1 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 \<in> ex1 r v"
    using assms by (auto simp: Semantics.T1_1)
  lemma Exe1S[meta_subst]:
    "[\<lparr>F,x\<rparr> in v] = (\<exists> r o\<^sub>1 . Some r = d\<^sub>1 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 \<in> ex1 r v)"
    by (auto simp: Semantics.T1_1)

subsubsection{* Two-Place Relations *}

  lemma Exe2I[meta_intro]:
    assumes "\<exists> r o\<^sub>1 o\<^sub>2 . Some r = d\<^sub>2 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x
                      \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> (o\<^sub>1, o\<^sub>2) \<in> ex2 r v"
    shows "[\<lparr>F,x,y\<rparr> in v]"
    using assms by (auto simp: Semantics.T1_2)
  lemma Exe2E[meta_elim]:
    assumes "[\<lparr>F,x,y\<rparr> in v]"
    shows "\<exists> r o\<^sub>1 o\<^sub>2 . Some r = d\<^sub>2 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x
                    \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> (o\<^sub>1, o\<^sub>2) \<in> ex2 r v"
    using assms by (auto simp: Semantics.T1_2)
  lemma Exe2S[meta_subst]:
    "[\<lparr>F,x,y\<rparr> in v] = (\<exists> r o\<^sub>1 o\<^sub>2 . Some r = d\<^sub>2 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x
                      \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> (o\<^sub>1, o\<^sub>2) \<in> ex2 r v)"
    by (auto simp: Semantics.T1_2)


subsubsection{* Three-Place Relations *}

  lemma Exe3I[meta_intro]:
    assumes "\<exists> r o\<^sub>1 o\<^sub>2 o\<^sub>3 . Some r = d\<^sub>3 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x
                         \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> Some o\<^sub>3 = d\<^sub>\<kappa> z
                         \<and> (o\<^sub>1, o\<^sub>2, o\<^sub>3) \<in> ex3 r v"
    shows "[\<lparr>F,x,y,z\<rparr> in v]"
    using assms by (auto simp: Semantics.T1_3)
  lemma Exe3E[meta_elim]:
    assumes "[\<lparr>F,x,y,z\<rparr> in v]"
    shows "\<exists> r o\<^sub>1 o\<^sub>2 o\<^sub>3 . Some r = d\<^sub>3 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x
                       \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> Some o\<^sub>3 = d\<^sub>\<kappa> z
                       \<and> (o\<^sub>1, o\<^sub>2, o\<^sub>3) \<in> ex3 r v"
    using assms by (auto simp: Semantics.T1_3)
  lemma Exe3S[meta_subst]:
    "[\<lparr>F,x,y,z\<rparr> in v] = (\<exists> r o\<^sub>1 o\<^sub>2 o\<^sub>3 . Some r = d\<^sub>3 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x
                                     \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> Some o\<^sub>3 = d\<^sub>\<kappa> z
                                     \<and> (o\<^sub>1, o\<^sub>2, o\<^sub>3) \<in> ex3 r v)"
    by (auto simp: Semantics.T1_3)

subsection{* Rules for Being Ordinary *}
text{* \label{TAO_MetaSolver_Ordinary} *}

  lemma OrdI[meta_intro]:
    assumes "\<exists> o\<^sub>1 y. Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 = \<omega>\<nu> y"
    shows "[\<lparr>O!,x\<rparr> in v]"
    proof -
      have "IsPropositionalInX (\<lambda>x. \<^bold>\<diamond>\<lparr>E!,x\<rparr>)"
        unfolding conn_defs
        by (simp add: IsPropositional_intros)
      moreover have "[\<^bold>\<diamond>\<lparr>E!,x\<rparr> in v]"
        apply meta_solver
        using ConcretenessSemantics1 propex\<^sub>1 assms by fast
      ultimately show "[\<lparr>O!,x\<rparr> in v]"
        unfolding Ordinary_def
        using D5_1 propex\<^sub>1 assms ConcretenessSemantics1 Exe1S
        by blast
    qed
  lemma OrdE[meta_elim]:
    assumes "[\<lparr>O!,x\<rparr> in v]"
    shows "\<exists> o\<^sub>1 y. Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 = \<omega>\<nu> y"
    proof -
      have "\<exists>r o\<^sub>1. Some r = d\<^sub>1 O! \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 \<in> ex1 r v"
        using assms Exe1E by simp
      moreover have "IsPropositionalInX (\<lambda>x. \<^bold>\<diamond>\<lparr>E!,x\<rparr>)"
        unfolding conn_defs
        by (simp add: IsPropositional_intros)
      ultimately have "[\<^bold>\<diamond>\<lparr>E!,x\<rparr> in v]"
        using D5_1 unfolding Ordinary_def by fast
      thus ?thesis
        apply - apply meta_solver
        using ConcretenessSemantics2 by blast
    qed
  lemma OrdS[meta_cong]:
    "[\<lparr>O!,x\<rparr> in v] = (\<exists> o\<^sub>1 y. Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 = \<omega>\<nu> y)"
    using OrdI OrdE by blast

subsection{* Rules for Being Abstract *}
text{* \label{TAO_MetaSolver_Abstract} *}

  lemma AbsI[meta_intro]:
    assumes "\<exists> o\<^sub>1 y. Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 = \<alpha>\<nu> y"
    shows "[\<lparr>A!,x\<rparr> in v]"
    proof -
      have "IsPropositionalInX (\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<rparr>)"
        unfolding conn_defs
        by (simp add: IsPropositional_intros)
      moreover have "[\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<rparr> in v]"
        apply meta_solver
        using ConcretenessSemantics2 propex\<^sub>1 assms
        by (metis \<nu>.distinct(1) option.sel)
      ultimately show "[\<lparr>A!,x\<rparr> in v]"
        unfolding Abstract_def
        using D5_1 propex\<^sub>1 assms ConcretenessSemantics1 Exe1S
        by blast
    qed
  lemma AbsE[meta_elim]:
    assumes "[\<lparr>A!,x\<rparr> in v]"
    shows "\<exists> o\<^sub>1 y. Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 = \<alpha>\<nu> y"
    proof -
      have 1: "IsPropositionalInX (\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<rparr>)"
        unfolding conn_defs
        by (simp add: IsPropositional_intros)
      have "\<exists>r o\<^sub>1. Some r = d\<^sub>1 A! \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 \<in> ex1 r v"
        using assms Exe1E by simp
      moreover hence "[\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<rparr> in v]"
        using D5_1[OF 1]
        unfolding Abstract_def by fast
      ultimately show ?thesis
        apply - apply meta_solver
        using ConcretenessSemantics1 propex\<^sub>1
        by (metis \<nu>.exhaust)
    qed
  lemma AbsS[meta_cong]:
    "[\<lparr>A!,x\<rparr> in v] = (\<exists> o\<^sub>1 y. Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 = \<alpha>\<nu> y)"
    using AbsI AbsE by blast

subsection{* Rules for Definite Descriptions *}
text{* \label{TAO_MetaSolver_DefiniteDescription} *}

  lemma TheEqI:
    assumes "\<And>x. [\<phi> x in dw] = [\<psi> x in dw]"
    shows "(\<^bold>\<iota>x. \<phi> x) = (\<^bold>\<iota>x. \<psi> x)"
    proof -
      have 1: "d\<^sub>\<kappa> (\<^bold>\<iota>x. \<phi> x) = d\<^sub>\<kappa> (\<^bold>\<iota>x. \<psi> x)"
        using assms D3 unfolding w\<^sub>0_def by simp
      {
        assume "\<exists> o\<^sub>1 . Some o\<^sub>1 = d\<^sub>\<kappa> (\<^bold>\<iota>x. \<phi> x)"
        hence ?thesis using 1 d\<^sub>\<kappa>_inject by force
      }
      moreover {
        assume "\<not>(\<exists> o\<^sub>1 . Some o\<^sub>1 = d\<^sub>\<kappa> (\<^bold>\<iota>x. \<phi> x))"
        hence ?thesis using 1 D3
        by (metis d\<^sub>\<kappa>.rep_eq eval\<kappa>_inverse)
      }
      ultimately show ?thesis by blast
    qed

subsection{* Rules for Identity *}
text{* \label{TAO_MetaSolver_Identity} *}

subsubsection{* Ordinary Objects *}
text{* \label{TAO_MetaSolver_Identity_Ordinary} *}

  lemma Eq\<^sub>EI[meta_intro]:
    assumes "\<exists> o\<^sub>1 X o\<^sub>2. Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> o\<^sub>1 = o\<^sub>2 \<and> o\<^sub>1 = \<omega>\<nu> X"
    shows "[x \<^bold>=\<^sub>E y in v]"
    proof -
      obtain o\<^sub>1 X o\<^sub>2 where 1:
        "Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> o\<^sub>1 = o\<^sub>2 \<and> o\<^sub>1 = \<omega>\<nu> X"
        using assms by auto
      obtain r where 2:
        "Some r = d\<^sub>2 basic_identity\<^sub>E"
        using propex\<^sub>2 by auto
      have "[\<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>\<^sub>1F. \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>) in v]"
        proof -
          have "[\<lparr>O!,x\<rparr> in v] \<and> [\<lparr>O!,y\<rparr> in v]"
            using OrdI 1 by blast
          moreover have "[\<^bold>\<box>(\<^bold>\<forall>\<^sub>1F. \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>) in v]"
            apply meta_solver using 1 by force
          ultimately show ?thesis using ConjI by simp
        qed
      moreover have "IsPropositionalInXY (\<lambda> x y . \<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>\<^sub>1F. \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>))"
        unfolding conn_defs
        by (simp add: IsPropositional_intros)
      ultimately have "(o\<^sub>1, o\<^sub>2) \<in> ex2 r v"
        using D5_2 1 2
        unfolding basic_identity\<^sub>E_def by fast
      thus "[x \<^bold>=\<^sub>E y in v]"
        using Exe2I 1 2
        unfolding basic_identity\<^sub>E_infix_def basic_identity\<^sub>E_def
        by blast
    qed
  lemma Eq\<^sub>EE[meta_elim]:
    assumes "[x \<^bold>=\<^sub>E y in v]"
    shows "\<exists> o\<^sub>1 X o\<^sub>2. Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> o\<^sub>1 = o\<^sub>2 \<and> o\<^sub>1 = \<omega>\<nu> X"
  proof -
    have "IsPropositionalInXY (\<lambda> x y . \<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>\<^sub>1F. \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>))"
        unfolding conn_defs
        by (simp add: IsPropositional_intros)
    hence 1: "[\<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>\<^sub>1 F. \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>) in v]"
      using assms unfolding basic_identity\<^sub>E_def basic_identity\<^sub>E_infix_def
      using D4_2 T1_2 D5_2 by meson
    hence 2: "\<exists> o\<^sub>1 o\<^sub>2 X Y . Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 = \<omega>\<nu> X
                         \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> o\<^sub>2 = \<omega>\<nu> Y"
      apply (subst (asm) ConjS)
      apply (subst (asm) ConjS)
      using OrdE by auto
    then obtain o\<^sub>1 o\<^sub>2 X Y where 3:
      "Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 = \<omega>\<nu> X \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> o\<^sub>2 = \<omega>\<nu> Y"
      by auto
    have "\<exists> r . Some r = d\<^sub>1 (\<^bold>\<lambda> z . make\<o> (\<lambda> w s . d\<^sub>\<kappa> (z\<^sup>P) = Some o\<^sub>1))"
      using propex\<^sub>1 by auto
    then obtain r where 4:
      "Some r = d\<^sub>1 (\<^bold>\<lambda> z . make\<o> (\<lambda> w s . d\<^sub>\<kappa> (z\<^sup>P) = Some o\<^sub>1))"
      by auto
    hence 5: "r = (\<lambda>u s w. Some (\<upsilon>\<nu> s u) = Some o\<^sub>1)"
      unfolding lambdabinder1_def d\<^sub>1_def d\<^sub>\<kappa>_proper
      apply transfer
      by simp
    have "[\<^bold>\<box>(\<^bold>\<forall>\<^sub>1 F. \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>) in v]"
      using 1 using ConjE by blast
    hence 6: "\<forall> v F . [\<lparr>F,x\<rparr> in v] \<longleftrightarrow> [\<lparr>F,y\<rparr> in v]"
      using BoxE EquivE All\<^sub>1E by fast
    hence 7: "\<forall> v . (o\<^sub>1 \<in> ex1 r v) = (o\<^sub>2 \<in> ex1 r v)"
      using 2 4 unfolding valid_in_def
      by (metis "3" "6" d\<^sub>1.rep_eq d\<^sub>\<kappa>_inject d\<^sub>\<kappa>_proper ex1_def eval\<o>_inverse exe1.rep_eq
          mem_Collect_eq option.sel rep_proper_id \<nu>\<kappa>_proper valid_in.abs_eq)
    have "o\<^sub>1 \<in> ex1 r v"
      using 5 3 unfolding ex1_def by (simp add: meta_aux)
    hence "o\<^sub>2 \<in> ex1 r v"
      using 7 by auto
    hence "o\<^sub>1 = o\<^sub>2"
      unfolding ex1_def 5 using 3 by (auto simp: meta_aux)
    thus ?thesis
      using 3 by auto
  qed
  lemma Eq\<^sub>ES[meta_subst]:
    "[x \<^bold>=\<^sub>E y in v] = (\<exists> o\<^sub>1 X o\<^sub>2. Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y
                                \<and> o\<^sub>1 = o\<^sub>2 \<and> o\<^sub>1 = \<omega>\<nu> X)"
    using Eq\<^sub>EI Eq\<^sub>EE by blast

subsubsection{* Individuals *}
text{* \label{TAO_MetaSolver_Identity_Individual} *}

  lemma Eq\<kappa>I[meta_intro]:
    assumes "\<exists> o\<^sub>1 o\<^sub>2. Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> o\<^sub>1 = o\<^sub>2"
    shows "[x \<^bold>=\<^sub>\<kappa> y in v]"
  proof -
    have "x = y" using assms d\<^sub>\<kappa>_inject by meson
    moreover have "[x \<^bold>=\<^sub>\<kappa> x in v]"
      unfolding basic_identity\<^sub>\<kappa>_def
      apply meta_solver
      by (metis (no_types, lifting) assms AbsI Exe1E \<nu>.exhaust)
    ultimately show ?thesis by auto
  qed
  lemma Eq\<kappa>_prop:
    assumes "[x \<^bold>=\<^sub>\<kappa> y in v]"
    shows "[\<phi> x in v] = [\<phi> y in v]"
  proof -
    have "[x \<^bold>=\<^sub>E y \<^bold>\<or> \<lparr>A!,x\<rparr> \<^bold>& \<lparr>A!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>\<^sub>1 F. \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>y,F\<rbrace>) in v]"
      using assms unfolding basic_identity\<^sub>\<kappa>_def by simp
    moreover {
      assume "[x \<^bold>=\<^sub>E y in v]"
      hence "(\<exists> o\<^sub>1 o\<^sub>2. Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> o\<^sub>1 = o\<^sub>2)"
        using Eq\<^sub>EE by fast
    }
    moreover {
      assume 1: "[\<lparr>A!,x\<rparr> \<^bold>& \<lparr>A!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>\<^sub>1 F. \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>y,F\<rbrace>) in v]"
      hence 2: "(\<exists> o\<^sub>1 o\<^sub>2 X Y. Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y
                              \<and> o\<^sub>1 = \<alpha>\<nu> X \<and> o\<^sub>2 = \<alpha>\<nu> Y)"
        using AbsE ConjE by meson
      moreover then obtain o\<^sub>1 o\<^sub>2 X Y where 3:
        "Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> o\<^sub>1 = \<alpha>\<nu> X \<and> o\<^sub>2 = \<alpha>\<nu> Y"
        by auto
      moreover have 4: "[\<^bold>\<box>(\<^bold>\<forall>\<^sub>1 F. \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>y,F\<rbrace>) in v]"
        using 1 ConjE by blast
      hence 6: "\<forall> v F . [\<lbrace>x,F\<rbrace> in v] \<longleftrightarrow> [\<lbrace>y,F\<rbrace> in v]"
        using BoxE All\<^sub>1E EquivE by fast
      hence 7: "\<forall>v r. (\<exists> o\<^sub>1. Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 \<in> en r)
                    = (\<exists> o\<^sub>1. Some o\<^sub>1 = d\<^sub>\<kappa> y \<and> o\<^sub>1 \<in> en r)"
        apply - apply meta_solver
        using propex\<^sub>1 d\<^sub>1_inject apply simp
        apply transfer by simp
      hence 8: "\<forall> r. (o\<^sub>1 \<in> en r) = (o\<^sub>2 \<in> en r)"
        using 3 d\<^sub>\<kappa>_inject d\<^sub>\<kappa>_proper apply simp
        by (metis option.inject)
      hence "\<forall>r. (o\<^sub>1 \<in> r) = (o\<^sub>2 \<in> r)"
        unfolding en_def using 3
        by (metis Collect_cong Collect_mem_eq \<nu>.simps(6)
                  mem_Collect_eq make\<Pi>\<^sub>1_cases)
      hence "(o\<^sub>1 \<in> { x . o\<^sub>1 = x }) = (o\<^sub>2 \<in> { x . o\<^sub>1 = x })"
        by metis
      hence "o\<^sub>1 = o\<^sub>2" by simp
      hence "(\<exists> o\<^sub>1 o\<^sub>2. Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> o\<^sub>1 = o\<^sub>2)"
        using 3 by auto
    }
    ultimately have "x = y"
      using DisjS using Semantics.d\<^sub>\<kappa>_inject by auto
    thus "(v \<Turnstile> (\<phi> x)) = (v \<Turnstile> (\<phi> y))" by simp
  qed
  lemma Eq\<kappa>E[meta_elim]:
    assumes "[x \<^bold>=\<^sub>\<kappa> y in v]"
    shows "\<exists> o\<^sub>1 o\<^sub>2. Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> o\<^sub>1 = o\<^sub>2"
  proof -
    have "\<forall> \<phi> . (v \<Turnstile> \<phi> x) = (v \<Turnstile> \<phi> y)"
      using assms Eq\<kappa>_prop by blast
    moreover obtain \<phi> where \<phi>_prop:
      "\<phi> = (\<lambda> \<alpha> . make\<o> (\<lambda> w s . (\<exists> o\<^sub>1 o\<^sub>2. Some o\<^sub>1 = d\<^sub>\<kappa> x
                            \<and> Some o\<^sub>2 = d\<^sub>\<kappa> \<alpha> \<and> o\<^sub>1 = o\<^sub>2)))"
      by auto
    ultimately have "(v \<Turnstile> \<phi> x) = (v \<Turnstile> \<phi> y)" by metis
    moreover have "(v \<Turnstile> \<phi> x)"
      using assms unfolding \<phi>_prop basic_identity\<^sub>\<kappa>_def
      by (metis (mono_tags, lifting) AbsS ConjE DisjS
                Eq\<^sub>ES valid_in.abs_eq)
    ultimately have "(v \<Turnstile> \<phi> y)" by auto
    thus ?thesis
      unfolding \<phi>_prop
      by (simp add: valid_in_def meta_aux)
  qed
  lemma Eq\<kappa>S[meta_subst]:
    "[x \<^bold>=\<^sub>\<kappa> y in v] = (\<exists> o\<^sub>1 o\<^sub>2. Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> o\<^sub>1 = o\<^sub>2)"
    using Eq\<kappa>I Eq\<kappa>E by blast

subsubsection{* One-Place Relations *}
text{* \label{TAO_MetaSolver_Identity_OnePlaceRelation} *}

  lemma Eq\<^sub>1I[meta_intro]: "F = G \<Longrightarrow> [F \<^bold>=\<^sub>1 G in v]"
    unfolding basic_identity\<^sub>1_def
    apply (rule BoxI, rule All\<^sub>\<nu>I, rule EquivI)
    by simp
  lemma Eq\<^sub>1E[meta_elim]: "[F \<^bold>=\<^sub>1 G in v] \<Longrightarrow> F = G"
    unfolding basic_identity\<^sub>1_def
    apply (drule BoxE, drule_tac x="(\<alpha>\<nu> { F })" in All\<^sub>\<nu>E, drule EquivE)
    apply (simp add: Semantics.T2)
    unfolding en_def d\<^sub>\<kappa>_def d\<^sub>1_def
    using \<nu>\<kappa>_proper rep_proper_id
    by (simp add: rep_def proper_def meta_aux \<nu>\<kappa>.rep_eq)
  lemma Eq\<^sub>1S[meta_subst]: "[F \<^bold>=\<^sub>1 G in v] = (F = G)"
    using Eq\<^sub>1I Eq\<^sub>1E by auto
  lemma Eq\<^sub>1_prop: "[F \<^bold>=\<^sub>1 G in v] \<Longrightarrow> [\<phi> F in v] = [\<phi> G in v]"
    using Eq\<^sub>1E by blast

subsubsection{* Two-Place Relations *}
text{* \label{TAO_MetaSolver_Identity_TwoPlaceRelation} *}

  lemma Eq\<^sub>2I[meta_intro]: "F = G \<Longrightarrow> [F \<^bold>=\<^sub>2 G in v]"
    unfolding basic_identity\<^sub>2_def
    apply (rule All\<^sub>\<nu>I, rule ConjI, (subst Eq\<^sub>1S)+)
    by simp
  lemma Eq\<^sub>2E[meta_elim]: "[F \<^bold>=\<^sub>2 G in v] \<Longrightarrow> F = G"
  proof -
    assume "[F \<^bold>=\<^sub>2 G in v]"
    hence "[\<^bold>\<forall>\<^sub>\<nu> x. (\<^bold>\<lambda>y. \<lparr>F,x\<^sup>P,y\<^sup>P\<rparr>) \<^bold>=\<^sub>1 (\<^bold>\<lambda>y. \<lparr>G,x\<^sup>P,y\<^sup>P\<rparr>) in v]"
      unfolding basic_identity\<^sub>2_def
      apply - apply meta_solver by auto
    hence "\<And>x . make\<Pi>\<^sub>1 (\<lambda>u s. eval\<Pi>\<^sub>2 F (\<nu>\<upsilon> s x) u s) = make\<Pi>\<^sub>1 (\<lambda>u s. eval\<Pi>\<^sub>2 G (\<nu>\<upsilon> s x) u s)"
     apply - apply meta_solver
     by (simp add: meta_defs meta_aux)
    hence "\<And>x . (\<lambda>u s. eval\<Pi>\<^sub>2 F (\<nu>\<upsilon> s x) u s) = (\<lambda>u s. eval\<Pi>\<^sub>2 G (\<nu>\<upsilon> s x) u s)"
      by (simp add: make\<Pi>\<^sub>1_inject)
    hence "\<And>x y . (\<lambda>u s. eval\<Pi>\<^sub>2 F y u s) = (\<lambda>u s. eval\<Pi>\<^sub>2 G y u s)"
      using \<nu>\<upsilon>_surj by (metis \<nu>\<upsilon>_\<upsilon>\<nu>_id)
    thus "F = G" using eval\<Pi>\<^sub>2_inject by blast
  qed
  lemma Eq\<^sub>2S[meta_subst]: "[F \<^bold>=\<^sub>2 G in v] = (F = G)"
    using Eq\<^sub>2I Eq\<^sub>2E by auto
  lemma Eq\<^sub>2_prop: "[F \<^bold>=\<^sub>2 G in v] \<Longrightarrow> [\<phi> F in v] = [\<phi> G in v]"
    using Eq\<^sub>2E by blast

subsubsection{* Three-Place Relations *}
text{* \label{TAO_MetaSolver_Identity_ThreePlaceRelation} *}

  lemma Eq\<^sub>3I[meta_intro]: "F = G \<Longrightarrow> [F \<^bold>=\<^sub>3 G in v]"
    apply (simp add: meta_defs meta_aux conn_defs basic_identity\<^sub>3_def)
    using MetaSolver.Eq\<^sub>1I valid_in.rep_eq by auto
  lemma Eq\<^sub>3E[meta_elim]: "[F \<^bold>=\<^sub>3 G in v] \<Longrightarrow> F = G"
  proof -
    assume "[F \<^bold>=\<^sub>3 G in v]"
    hence "[\<^bold>\<forall>\<^sub>\<nu> x y. (\<^bold>\<lambda>z. \<lparr>F,x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr>) \<^bold>=\<^sub>1 (\<^bold>\<lambda>z. \<lparr>G,x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr>) in v]"
      unfolding basic_identity\<^sub>3_def apply -
      apply meta_solver by auto
    hence "\<And>x y. (\<^bold>\<lambda>z. \<lparr>F,x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr>) = (\<^bold>\<lambda>z. \<lparr>G,x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr>)"
      using Eq\<^sub>1E All\<^sub>\<nu>S by (metis (mono_tags, lifting))
    hence "\<And>x y. make\<Pi>\<^sub>1 (\<lambda> u s . eval\<Pi>\<^sub>3 F (\<nu>\<upsilon> s x) (\<nu>\<upsilon> s y) u s)
               = make\<Pi>\<^sub>1 (\<lambda> u s . eval\<Pi>\<^sub>3 G (\<nu>\<upsilon> s x) (\<nu>\<upsilon> s y) u s)"
      by (auto simp: meta_defs meta_aux)
    hence "\<And>x y. (\<lambda> u s . eval\<Pi>\<^sub>3 F (\<nu>\<upsilon> s x) (\<nu>\<upsilon> s y) u s)
               = (\<lambda> u s . eval\<Pi>\<^sub>3 G (\<nu>\<upsilon> s x) (\<nu>\<upsilon> s y) u s)"
      by (simp add: make\<Pi>\<^sub>1_inject)
    hence "\<And>x y. (\<lambda> u s . eval\<Pi>\<^sub>3 F (\<nu>\<upsilon> s x) y u s)
               = (\<lambda> u s . eval\<Pi>\<^sub>3 G (\<nu>\<upsilon> s x) y u s)"
      using \<nu>\<upsilon>_surj by (metis \<nu>\<upsilon>_\<upsilon>\<nu>_id)
    hence "\<And>x y. (\<lambda> u s . eval\<Pi>\<^sub>3 F x y u s)
               = (\<lambda> u s . eval\<Pi>\<^sub>3 G x y u s)"
      using \<nu>\<upsilon>_surj by (metis \<nu>\<upsilon>_\<upsilon>\<nu>_id)
    thus "F = G" using eval\<Pi>\<^sub>3_inject by blast
  qed
  lemma Eq\<^sub>3S[meta_subst]: "[F \<^bold>=\<^sub>3 G in v] = (F = G)"
    using Eq\<^sub>3I Eq\<^sub>3E by auto
  lemma Eq\<^sub>3_prop: "[F \<^bold>=\<^sub>3 G in v] \<Longrightarrow> [\<phi> F in v] = [\<phi> G in v]"
    using Eq\<^sub>3E by blast

subsubsection{* Propositions *}
text{* \label{TAO_MetaSolver_Identity_Proposition} *}

  lemma Eq\<^sub>\<o>I[meta_intro]: "x = y \<Longrightarrow> [x \<^bold>=\<^sub>\<o> y in v]"
    unfolding basic_identity\<^sub>\<o>_def by (simp add: Eq\<^sub>1S)
  lemma Eq\<^sub>\<o>E[meta_elim]: "[F \<^bold>=\<^sub>\<o> G in v] \<Longrightarrow> F = G"
    unfolding basic_identity\<^sub>\<o>_def
    apply (drule Eq\<^sub>1E)
    apply (simp add: meta_defs)
    using eval\<o>_inject make\<Pi>\<^sub>1_inject
    by (metis UNIV_I)
  lemma Eq\<^sub>\<o>S[meta_subst]: "[F \<^bold>=\<^sub>\<o> G in v] = (F = G)"
    using Eq\<^sub>\<o>I Eq\<^sub>\<o>E by auto
  lemma Eq\<^sub>\<o>_prop: "[F \<^bold>=\<^sub>\<o> G in v] \<Longrightarrow> [\<phi> F in v] = [\<phi> G in v]"
    using Eq\<^sub>\<o>E by blast

end

(*<*)
end
(*>*)
