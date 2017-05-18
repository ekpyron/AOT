(*<*)
theory TAO_4_TypeClass
imports TAO_2_Semantics TAO_3_BasicDefinitions
begin
(*>*)

section{* Type Class *}
text{* \label{TAO_TypeClass} *}

text{*
\begin{remark}
  In order to define general quantifiers that can act
  on individuals as well as relations a type class
  is introduced which assumes the semantics of the all quantifier.
  This type class is then instantiated for individuals and
  relations.
\end{remark}
*}

subsection{* Type Class *}
text{* \label{TAO_TypeClass_Class} *}

class TAO_type =
  fixes forall :: "('a\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>" [8] 9)
    and identity :: "'a trm\<Rightarrow>'a trm\<Rightarrow>\<o>" (infixl "\<^bold>=" 63)
  assumes TAO_type_T8: "(w \<Turnstile> (\<^bold>\<forall> x . \<psi> x)) = (\<forall> x . (w \<Turnstile> \<psi> x))"
      and TAO_type_identity: "(w \<Turnstile> (x \<^bold>= y)) = (proper x \<and> proper y \<and> x = y)"
begin
  definition exists :: "('a\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<exists>" [8] 9) where
      [conn_defs]: "exists \<equiv> \<lambda> \<phi> . \<^bold>\<not>(\<^bold>\<forall> x . \<^bold>\<not>\<phi> x)"
end
  
text{* Semantics for the general all quantifier: *}

lemma (in Semantics) T8: shows "(w \<Turnstile> \<^bold>\<forall> x . \<psi> x) = (\<forall> x . (w \<Turnstile> \<psi> x))"
  using TAO_type_T8 .

subsection{* Instantiations *}
text{* \label{TAO_Quantifiable_Instantiations} *}

instantiation \<nu> and \<o> and \<Omega>\<^sub>1 and \<Omega>\<^sub>2 and \<Omega>\<^sub>3 :: TAO_type
begin
  definition forall_\<nu> :: "(\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<o>" where
    "forall_\<nu> \<equiv> forall\<^sub>\<nu>"
  definition forall_\<o> :: "(\<o>\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<o> \<equiv> forall\<^sub>\<o>"
  definition forall_\<Omega>\<^sub>1 :: "(\<Omega>\<^sub>1\<Rightarrow>\<o>)\<Rightarrow>\<o>" where
    "forall_\<Omega>\<^sub>1 \<equiv> forall\<^sub>1"
  definition forall_\<Omega>\<^sub>2 :: "(\<Omega>\<^sub>2\<Rightarrow>\<o>)\<Rightarrow>\<o>" where
    "forall_\<Omega>\<^sub>2 \<equiv> forall\<^sub>2"
  definition forall_\<Omega>\<^sub>3 :: "(\<Omega>\<^sub>3\<Rightarrow>\<o>)\<Rightarrow>\<o>" where
    "forall_\<Omega>\<^sub>3 \<equiv> forall\<^sub>3"
  definition identity\<^sub>E::"\<Pi>\<^sub>2" where
    "identity\<^sub>E \<equiv> \<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<lparr>O!,x\<^sup>P\<rparr> \<^bold>& \<lparr>O!,y\<^sup>P\<rparr>
                     \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F. \<lparr>F\<^sup>P,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F\<^sup>P,y\<^sup>P\<rparr>))"
  definition identity\<^sub>E_infix::"\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<o>" (infixl "\<^bold>=\<^sub>E" 63) where
    "x \<^bold>=\<^sub>E y \<equiv> \<lparr>identity\<^sub>E, x, y\<rparr>"
  definition identity_\<nu> :: "\<kappa> \<Rightarrow> \<kappa> \<Rightarrow> \<o>" where
    "identity_\<nu> \<equiv> \<lambda> x y . (x \<^bold>=\<^sub>E y) \<^bold>\<or> \<lparr>A!,x\<rparr> \<^bold>& \<lparr>A!,y\<rparr>
                          \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F. \<lbrace>x,F\<^sup>P\<rbrace> \<^bold>\<equiv> \<lbrace>y,F\<^sup>P\<rbrace>)"
  definition identity_\<Omega>\<^sub>1 where
    "identity_\<Omega>\<^sub>1 \<equiv> \<lambda> F G . \<^bold>\<box>(\<^bold>\<forall> x. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>x\<^sup>P,G\<rbrace>)"
  definition identity_\<Omega>\<^sub>2 :: "\<Pi>\<^sub>2\<Rightarrow>\<Pi>\<^sub>2\<Rightarrow>\<o>" where
  "identity_\<Omega>\<^sub>2 \<equiv> \<lambda> F G .  \<^bold>\<forall> x. ((\<^bold>\<lambda>y. \<lparr>F,x\<^sup>P,y\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>y. \<lparr>G,x\<^sup>P,y\<^sup>P\<rparr>))
                                 \<^bold>& ((\<^bold>\<lambda>y. \<lparr>F,y\<^sup>P,x\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>y. \<lparr>G,y\<^sup>P,x\<^sup>P\<rparr>))"
  definition identity_\<Omega>\<^sub>3::"\<Pi>\<^sub>3\<Rightarrow>\<Pi>\<^sub>3\<Rightarrow>\<o>" where
    "identity_\<Omega>\<^sub>3 \<equiv> \<lambda> F G . \<^bold>\<forall> x y. (\<^bold>\<lambda>z. \<lparr>F,z\<^sup>P,x\<^sup>P,y\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>z. \<lparr>G,z\<^sup>P,x\<^sup>P,y\<^sup>P\<rparr>)
                                 \<^bold>& (\<^bold>\<lambda>z. \<lparr>F,x\<^sup>P,z\<^sup>P,y\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>z. \<lparr>G,x\<^sup>P,z\<^sup>P,y\<^sup>P\<rparr>)
                                 \<^bold>& (\<^bold>\<lambda>z. \<lparr>F,x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>z. \<lparr>G,x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr>)"
  definition identity_\<o>::"\<Pi>\<^sub>0\<Rightarrow>\<Pi>\<^sub>0\<Rightarrow>\<o>" where
    "identity_\<o> \<equiv> \<lambda> F G . (\<^bold>\<lambda>y. \<lparr>F\<rparr>) \<^bold>= (\<^bold>\<lambda>y. \<lparr>G\<rparr>)"

  instance proof
    fix w :: i and \<psi> :: "\<nu>\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. (w \<Turnstile> \<psi> x))"
      unfolding forall_\<nu>_def using Semantics.T8_\<nu> .
  next
    fix x y :: \<kappa> and w :: i
    show "[x \<^bold>= y in w] = (proper x \<and> proper y \<and> x = y)"
  qed
end


(*<*)
end
(*>*)
