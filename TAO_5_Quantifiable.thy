(*<*)
theory TAO_5_Quantifiable
imports TAO_4_MetaSolver
begin
(*>*)

section{* General Quantification *}

text{*
\begin{remark}
  In order to define general quantifiers that can act
  on all variable types a type class is introduced
  which assumes the semantics of the all quantifier.
  This type class is then instantiated for all variable
  types.
\end{remark}
*}

subsection{* Type Class *}

text{* Datatype for types for which quantification is defined: *}

datatype var = \<kappa>var (var\<kappa>: \<kappa>) | \<o>var (var\<o>: \<o>) | \<Pi>\<^sub>1var (var\<Pi>\<^sub>1: \<Pi>\<^sub>1)
             | \<Pi>\<^sub>2var (var\<Pi>\<^sub>2: \<Pi>\<^sub>2) | \<Pi>\<^sub>3var (var\<Pi>\<^sub>3: \<Pi>\<^sub>3)

text{* Type class for quantifiable types: *}

class quantifiable = fixes forall :: "('a\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>" [8] 9)
                       and domain :: "'a set"
                       and qvar :: "'a\<Rightarrow>var"
                       and varq :: "var\<Rightarrow>'a"
  assumes quantifiable_T8: "(w \<Turnstile> (\<^bold>\<forall> x . \<psi> x)) = (\<forall> x . x \<in> domain \<longrightarrow> (w \<Turnstile> (\<psi> x)))"
      and varq_qvar_id: "varq (qvar x) = x"
      and nonempty: "\<exists> x . x \<in> domain"
begin
  definition exists :: "('a\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<exists>" [8] 9) where
    "exists \<equiv> \<lambda> \<phi> . \<^bold>\<not>(\<^bold>\<forall> x . \<^bold>\<not>\<phi> x)"
  declare exists_def[conn_defs]
end

text{* Semantics for the general all quantifier: *}

lemma (in Semantics) T8: shows "(w \<Turnstile> \<^bold>\<forall> x . \<psi> x) = (\<forall> x . x \<in> domain \<longrightarrow> (w \<Turnstile> \<psi> x))"
  using quantifiable_T8 .

subsection{* Instantiations *}

instantiation \<kappa> :: quantifiable
begin
  definition forall_\<kappa> :: "(\<kappa>\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<kappa> \<equiv> forall\<^sub>\<nu>"
  definition domain_\<kappa> :: "\<kappa> set" where "domain_\<kappa> \<equiv> { x . denotes (x)}"
  definition qvar_\<kappa> :: "\<kappa>\<Rightarrow>var" where "qvar \<equiv> \<kappa>var"
  definition varq_\<kappa> :: "var\<Rightarrow>\<kappa>" where "varq \<equiv> var\<kappa>"
  instance proof
    fix w :: i and \<psi> :: "\<kappa>\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. x \<in> domain \<longrightarrow> (w \<Turnstile> \<psi> x))"
      unfolding forall_\<kappa>_def domain_\<kappa>_def using Semantics.T8_\<nu> by auto
  next
    fix x :: \<kappa>
    show "varq (qvar x) = x"
      unfolding qvar_\<kappa>_def varq_\<kappa>_def by simp
  next
    show "\<exists>x :: \<kappa> . x \<in> domain" unfolding domain_\<kappa>_def unfolding denotes_def apply simp apply transfer by auto
  qed
end

instantiation \<o> :: quantifiable
begin
  definition forall_\<o> :: "(\<o>\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<o> \<equiv> forall\<^sub>\<o>"
  definition domain_\<o> :: "\<o> set" where "domain_\<o> \<equiv> UNIV"
  definition qvar_\<o> :: "\<o>\<Rightarrow>var" where "qvar \<equiv> \<o>var"
  definition varq_\<o> :: "var\<Rightarrow>\<o>" where "varq \<equiv> var\<o>"
  instance proof
    fix w :: i and \<psi> :: "\<o>\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. x \<in> domain \<longrightarrow> (w \<Turnstile> \<psi> x))"
      unfolding forall_\<o>_def domain_\<o>_def using Semantics.T8_\<o> by simp
  next
    fix x :: \<o>
    show "varq (qvar x) = x"
      unfolding qvar_\<o>_def varq_\<o>_def by simp
  next
    show "\<exists>x :: \<o> . x \<in> domain" unfolding domain_\<o>_def by auto
  qed
end

instantiation \<Pi>\<^sub>1 :: quantifiable
begin
  definition forall_\<Pi>\<^sub>1 :: "(\<Pi>\<^sub>1\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<Pi>\<^sub>1 \<equiv> forall\<^sub>1"
  definition domain_\<Pi>\<^sub>1 :: "\<Pi>\<^sub>1 set" where "domain_\<Pi>\<^sub>1 \<equiv> UNIV"
  definition qvar_\<Pi>\<^sub>1 :: "\<Pi>\<^sub>1\<Rightarrow>var" where "qvar \<equiv> \<Pi>\<^sub>1var"
  definition varq_\<Pi>\<^sub>1 :: "var\<Rightarrow>\<Pi>\<^sub>1" where "varq \<equiv> var\<Pi>\<^sub>1"
  instance proof
    fix w :: i and \<psi> :: "\<Pi>\<^sub>1\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. x \<in> domain \<longrightarrow> (w \<Turnstile> \<psi> x))"
      unfolding forall_\<Pi>\<^sub>1_def domain_\<Pi>\<^sub>1_def using Semantics.T8_1 by simp
  next
    fix x :: \<Pi>\<^sub>1
    show "varq (qvar x) = x"
      unfolding qvar_\<Pi>\<^sub>1_def varq_\<Pi>\<^sub>1_def by simp
  next
    show "\<exists>x :: \<Pi>\<^sub>1 . x \<in> domain" unfolding domain_\<Pi>\<^sub>1_def by auto
  qed
end

instantiation \<Pi>\<^sub>2 :: quantifiable
begin
  definition forall_\<Pi>\<^sub>2 :: "(\<Pi>\<^sub>2\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<Pi>\<^sub>2 \<equiv> forall\<^sub>2"
  definition domain_\<Pi>\<^sub>2 :: "\<Pi>\<^sub>2 set" where "domain_\<Pi>\<^sub>2 \<equiv> UNIV"
  definition qvar_\<Pi>\<^sub>2 :: "\<Pi>\<^sub>2\<Rightarrow>var" where "qvar \<equiv> \<Pi>\<^sub>2var"
  definition varq_\<Pi>\<^sub>2 :: "var\<Rightarrow>\<Pi>\<^sub>2" where "varq \<equiv> var\<Pi>\<^sub>2"
  instance proof
    fix w :: i and \<psi> :: "\<Pi>\<^sub>2\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. x \<in> domain \<longrightarrow> (w \<Turnstile> \<psi> x))"
      unfolding forall_\<Pi>\<^sub>2_def domain_\<Pi>\<^sub>2_def using Semantics.T8_2 by simp
  next
    fix x :: \<Pi>\<^sub>2
    show "varq (qvar x) = x"
      unfolding qvar_\<Pi>\<^sub>2_def varq_\<Pi>\<^sub>2_def by simp
  next
    show "\<exists>x :: \<Pi>\<^sub>2 . x \<in> domain" unfolding domain_\<Pi>\<^sub>2_def by auto
  qed
end

instantiation \<Pi>\<^sub>3 :: quantifiable
begin
  definition forall_\<Pi>\<^sub>3 :: "(\<Pi>\<^sub>3\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<Pi>\<^sub>3 \<equiv> forall\<^sub>3"
  definition domain_\<Pi>\<^sub>3 :: "\<Pi>\<^sub>3 set" where "domain_\<Pi>\<^sub>3 \<equiv> UNIV"
  definition qvar_\<Pi>\<^sub>3 :: "\<Pi>\<^sub>3\<Rightarrow>var" where "qvar \<equiv> \<Pi>\<^sub>3var"
  definition varq_\<Pi>\<^sub>3 :: "var\<Rightarrow>\<Pi>\<^sub>3" where "varq \<equiv> var\<Pi>\<^sub>3"
  instance proof
    fix w :: i and \<psi> :: "\<Pi>\<^sub>3\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. x \<in> domain \<longrightarrow> (w \<Turnstile> \<psi> x))"
      unfolding forall_\<Pi>\<^sub>3_def domain_\<Pi>\<^sub>3_def using Semantics.T8_3 by simp
  next
    fix x :: \<Pi>\<^sub>3
    show "varq (qvar x) = x"
      unfolding qvar_\<Pi>\<^sub>3_def varq_\<Pi>\<^sub>3_def by simp
  next
    show "\<exists>x :: \<Pi>\<^sub>3 . x \<in> domain" unfolding domain_\<Pi>\<^sub>3_def by auto
  qed
end

subsection{* MetaSolver Rules *}

text{*
\begin{remark}
  The @{text "meta_solver"} is extended by rules for
  general quantification.
\end{remark}
*}

context MetaSolver
begin
  subsubsection{* Rules for General All Quantification. *}
  lemma AllI[meta_intro]: "(\<And>x::'a::quantifiable. [\<phi> x in v]) \<Longrightarrow> [\<^bold>\<forall> x. \<phi> x in v]"
    by (auto simp: Semantics.T8)
  lemma AllE[meta_elim]: "[\<^bold>\<forall>x. \<phi> x in v] \<Longrightarrow> (\<And>x::'a::quantifiable. x \<in> domain \<longrightarrow> [\<phi> x in v])"
    by (auto simp: Semantics.T8)
  lemma AllS[meta_subst]: "[\<^bold>\<forall>x. \<phi> x in v] = (\<forall>x::'a::quantifiable. x \<in> domain \<longrightarrow> [\<phi> x in v])"
    by (auto simp: Semantics.T8)

  subsubsection{* Rules for Existence *}
  lemma ExIRule: "(y \<in> domain \<and> [\<phi> y in v]) \<Longrightarrow> [\<^bold>\<exists>x. \<phi> x in v]"
    by (auto simp: exists_def NotS AllS)
  lemma ExI[meta_intro]: "(\<exists> y . y \<in> domain \<and> [\<phi> y in v]) \<Longrightarrow> [\<^bold>\<exists>x. \<phi> x in v]"
    by (auto simp: exists_def NotS AllS)
  lemma ExE[meta_elim]: "[\<^bold>\<exists>x. \<phi> x in v] \<Longrightarrow> (\<exists> y .  y \<in> domain \<and>[\<phi> y in v])"
    by (auto simp: exists_def NotS AllS)
  lemma ExS[meta_subst]: "[\<^bold>\<exists>x. \<phi> x in v] = (\<exists> y .  y \<in> domain \<and>[\<phi> y in v])"
    by (auto simp: exists_def NotS AllS)
  lemma ExERule: assumes "[\<^bold>\<exists>x. \<phi> x in v]" obtains x where "[\<phi> x in v]" 
    using ExE assms by auto

end

(*<*)
end
(*>*)
