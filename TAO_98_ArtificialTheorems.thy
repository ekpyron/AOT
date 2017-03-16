(*<*)
theory TAO_98_ArtificialTheorems
imports TAO_7_Axioms
begin
(*>*)

section{* Artificial Theorems *}

text{*
\begin{remark}
  Some examples of theorems that can be derived from the meta-logic, but which
  are (presumably) not derivable from the deductive system PLM itself.
\end{remark}
*}

locale ArtificialTheorems
begin

  lemma lambda_enc_1:
    "[\<lparr>\<^bold>\<lambda>x . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<lbrace>x\<^sup>P, F\<rbrace>, y\<^sup>P\<rparr> in v]"
    by (simp add: meta_defs meta_aux conn_defs forall_\<Pi>\<^sub>1_def)

  lemma lambda_enc_2:
    "[\<lparr>\<^bold>\<lambda> x . \<lbrace>y\<^sup>P, G\<rbrace>, x\<^sup>P\<rparr> \<^bold>\<equiv> \<lbrace>y\<^sup>P, G\<rbrace> in v]"
    by (simp add: meta_defs meta_aux conn_defs forall_\<Pi>\<^sub>1_def)

text{*
\begin{remark}
  The following is \emph{not} a theorem and nitpick can
  find a countermodel. This is expected and important because,
  if this were a theorem, the theory would become inconsistent.
\end{remark}
*}

  lemma lambda_enc_3:
    "[(\<lparr>\<^bold>\<lambda> x . \<lbrace>x\<^sup>P, F\<rbrace>, x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>P, F\<rbrace>) in v]"
    apply (simp add: meta_defs meta_aux conn_defs forall_\<Pi>\<^sub>1_def)
    nitpick[user_axioms, expect=genuine]
    oops --{* countermodel by nitpick *}

text{*
\begin{remark}
  Instead the following two statements hold.
\end{remark}
*}

  lemma lambda_enc_4:
    "[\<lparr>(\<^bold>\<lambda> x . \<lbrace>x\<^sup>P, F\<rbrace>), x\<^sup>P\<rparr> in v] \<longrightarrow> (\<exists> y . \<nu>\<upsilon> y = \<nu>\<upsilon> x \<and> [\<lbrace>y\<^sup>P, F\<rbrace> in v])"
    apply (simp add: meta_defs meta_aux)
    by (metis \<nu>\<upsilon>_\<upsilon>\<nu>_id id_apply)

  lemma lambda_enc_5:
    "(\<forall> y . \<nu>\<upsilon> y = \<nu>\<upsilon> x \<longrightarrow> [\<lbrace>y\<^sup>P, F\<rbrace> in v]) \<longrightarrow> [\<lparr>(\<^bold>\<lambda> x . \<lbrace>x\<^sup>P, F\<rbrace>), x\<^sup>P\<rparr> in v]"
    by (simp add: meta_defs meta_aux)

  lemma material_equivalence_implies_lambda_identity:
    assumes "[\<^bold>\<forall>F. \<^bold>\<box>(\<lparr>F,a\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,b\<^sup>P\<rparr>) in v]"
    shows "(\<^bold>\<lambda>x. \<lparr>R,x\<^sup>P,a\<^sup>P\<rparr>) = (\<^bold>\<lambda>x . \<lparr>R,x\<^sup>P, b\<^sup>P\<rparr>)"
    using assms
    apply (simp add: meta_defs meta_aux conn_defs forall_\<Pi>\<^sub>1_def)
    apply transfer
    by fast

end

(*<*)
end
(*>*)
