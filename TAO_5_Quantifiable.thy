(*<*)
theory TAO_5_Quantifiable
imports TAO_4_MetaSolver
begin
(*>*)

section{* General Quantification *}
text{* \label{TAO_Quantifiable} *}

text{*
\begin{remark}
  In order to define general quantifiers that can act
  on all individuals as well as relations a type class
  is introduced which assumes the semantics of the all quantifier.
  This type class is then instantiated for individuals and
  relations.
\end{remark}
*}

subsection{* Type Class *}
text{* \label{TAO_Quantifiable_Class} *}

text{* Type class for quantifiable types: *}

class quantifiable = fixes forall :: "('a\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>" [8] 9)
  assumes quantifiable_T8: "(w \<Turnstile> (\<^bold>\<forall> x . \<psi> x)) = (\<forall> x . (w \<Turnstile> (\<psi> x)))"
begin
  definition exists :: "('a\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<exists>" [8] 9) where
    "exists \<equiv> \<lambda> \<phi> . \<^bold>\<not>(\<^bold>\<forall> x . \<^bold>\<not>\<phi> x)"
  declare exists_def[conn_defs]
end

text{* Semantics for the general all quantifier: *}

lemma (in Semantics) T8: shows "(w \<Turnstile> \<^bold>\<forall> x . \<psi> x) = (\<forall> x . (w \<Turnstile> \<psi> x))"
  using quantifiable_T8 .

subsection{* Instantiations *}
text{* \label{TAO_Quantifiable_Instantiation} *}

instantiation \<nu> :: quantifiable
begin
  definition forall_\<nu> :: "(\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<nu> \<equiv> forall\<^sub>\<nu>"
  instance proof
    fix w :: i and \<psi> :: "\<nu>\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. (w \<Turnstile> \<psi> x))"
      unfolding forall_\<nu>_def using Semantics.T8_\<nu> .
  qed
end

instantiation \<o> :: quantifiable
begin
  definition forall_\<o> :: "(\<o>\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<o> \<equiv> forall\<^sub>\<o>"
  instance proof
    fix w :: i and \<psi> :: "\<o>\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. (w \<Turnstile> \<psi> x))"
      unfolding forall_\<o>_def using Semantics.T8_\<o> .
  qed
end

instantiation \<Pi>\<^sub>1 :: quantifiable
begin
  definition forall_\<Pi>\<^sub>1 :: "(\<Pi>\<^sub>1\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<Pi>\<^sub>1 \<equiv> forall\<^sub>1"
  instance proof
    fix w :: i and \<psi> :: "\<Pi>\<^sub>1\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. (w \<Turnstile> \<psi> x))"
      unfolding forall_\<Pi>\<^sub>1_def using Semantics.T8_1 .
  qed
end

instantiation \<Pi>\<^sub>2 :: quantifiable
begin
  definition forall_\<Pi>\<^sub>2 :: "(\<Pi>\<^sub>2\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<Pi>\<^sub>2 \<equiv> forall\<^sub>2"
  instance proof
    fix w :: i and \<psi> :: "\<Pi>\<^sub>2\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. (w \<Turnstile> \<psi> x))"
      unfolding forall_\<Pi>\<^sub>2_def using Semantics.T8_2 .
  qed
end

instantiation \<Pi>\<^sub>3 :: quantifiable
begin
  definition forall_\<Pi>\<^sub>3 :: "(\<Pi>\<^sub>3\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<Pi>\<^sub>3 \<equiv> forall\<^sub>3"
  instance proof
    fix w :: i and \<psi> :: "\<Pi>\<^sub>3\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. (w \<Turnstile> \<psi> x))"
      unfolding forall_\<Pi>\<^sub>3_def using Semantics.T8_3 .
  qed
end

subsection{* Rules *}
text{* \label{TAO_Quantifiable_Rules} *}

text{*
\begin{remark}
  Introduction rules for IsPropsositionalInX, IsPropsositionalInXY and IsPropsositionalInXYZ
  are derived for general quantification.
\end{remark}
*}

lemma IsPropositionalInX_forall[IsPropositional_intros]:
  assumes "\<And> a . IsPropositionalInX (\<phi> a)"
  shows "IsPropositionalInX (\<lambda> x . (\<^bold>\<forall> a . (\<phi> a) x))"
  using assms unfolding IsPropositionalInX_def
  by (simp add: quantifiable_T8)
lemma IsPropositionalInXY_forall[IsPropositional_intros]:
  assumes "\<And> a . IsPropositionalInXY (\<phi> a)"
  shows "IsPropositionalInXY (\<lambda> x y . (\<^bold>\<forall> a . (\<phi> a) x y))"
  using assms unfolding IsPropositionalInXY_def
  by (simp add: quantifiable_T8)
lemma IsPropositionalInXYZ_forall[IsPropositional_intros]:
  assumes "\<And> a . IsPropositionalInXYZ (\<phi> a)"
  shows "IsPropositionalInXYZ (\<lambda> x y z . (\<^bold>\<forall> a . (\<phi> a) x y z))"
  using assms unfolding IsPropositionalInXYZ_def
  by (simp add: quantifiable_T8)

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
  lemma AllE[meta_elim]: "[\<^bold>\<forall>x. \<phi> x in v] \<Longrightarrow> (\<And>x::'a::quantifiable.[\<phi> x in v])"
    by (auto simp: Semantics.T8)
  lemma AllS[meta_subst]: "[\<^bold>\<forall>x. \<phi> x in v] = (\<forall>x::'a::quantifiable.[\<phi> x in v])"
    by (auto simp: Semantics.T8)

  subsubsection{* Rules for Existence *}
  lemma ExIRule: "([\<phi> y in v]) \<Longrightarrow> [\<^bold>\<exists>x. \<phi> x in v]"
    by (auto simp: exists_def NotS AllS)
  lemma ExI[meta_intro]: "(\<exists> y . [\<phi> y in v]) \<Longrightarrow> [\<^bold>\<exists>x. \<phi> x in v]"
    by (auto simp: exists_def NotS AllS)
  lemma ExE[meta_elim]: "[\<^bold>\<exists>x. \<phi> x in v] \<Longrightarrow> (\<exists> y . [\<phi> y in v])"
    by (auto simp: exists_def NotS AllS)
  lemma ExS[meta_subst]: "[\<^bold>\<exists>x. \<phi> x in v] = (\<exists> y . [\<phi> y in v])"
    by (auto simp: exists_def NotS AllS)
  lemma ExERule: assumes "[\<^bold>\<exists>x. \<phi> x in v]" obtains x where "[\<phi> x in v]" 
    using ExE assms by auto

end

(*<*)
end
(*>*)
