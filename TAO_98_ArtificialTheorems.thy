(*<*)
theory TAO_98_ArtificialTheorems
imports TAO_7_Axioms
begin
(*>*)

section{* Artificial Theorems *}
text{* \label{TAO_ArtificialTheorems} *}

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
    by (auto simp: meta_defs meta_aux conn_defs forall_\<Pi>\<^sub>1_def)

  lemma lambda_enc_2:
    "[\<lparr>\<^bold>\<lambda> x . \<lbrace>y\<^sup>P, G\<rbrace>, x\<^sup>P\<rparr> \<^bold>\<equiv> \<lbrace>y\<^sup>P, G\<rbrace> in v]"
    by (auto simp: meta_defs meta_aux conn_defs forall_\<Pi>\<^sub>1_def)

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
    "[\<lparr>(\<^bold>\<lambda> x . \<lbrace>x\<^sup>P, F\<rbrace>), x\<^sup>P\<rparr> in v] = (\<exists> y . \<nu>\<upsilon> dj y = \<nu>\<upsilon> dj x \<and> [\<lbrace>y\<^sup>P, F\<rbrace> in v])"
    by (simp add: meta_defs meta_aux)

  lemma lambda_ex:
    "[\<lparr>(\<^bold>\<lambda> x . \<phi> x), x\<^sup>P\<rparr> in v] = (\<exists> y . \<nu>\<upsilon> dj y = \<nu>\<upsilon> dj x \<and> [\<phi> y in v])"
    by (simp add: meta_defs meta_aux)

text{*
\begin{remark}
  These statements can also be translated to statements in the embedded logic.
\end{remark}
*}

  lemma lambda_ex_emb:
    "[\<lparr>(\<^bold>\<lambda> x . \<phi> x), x\<^sup>P\<rparr> \<^bold>\<equiv> (\<^bold>\<exists> y . (\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) \<^bold>& \<phi> y) in v]"
    proof(rule MetaSolver.EquivI)
      interpret MetaSolver .
      {
        assume "[\<lparr>(\<^bold>\<lambda> x . \<phi> x), x\<^sup>P\<rparr> in v]"
        then obtain y where "\<nu>\<upsilon> dj y = \<nu>\<upsilon> dj x \<and> [\<phi> y in v]"
          using lambda_ex by blast
        moreover hence "[(\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) in v]"
          apply - apply meta_solver
          by (simp add: Semantics.d\<^sub>\<kappa>_proper Semantics.ex1_def)
        ultimately have "[\<^bold>\<exists> y . (\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) \<^bold>& \<phi> y in v]"
          using ExIRule ConjI by fast
      }
      moreover {
        assume "[\<^bold>\<exists> y . (\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) \<^bold>& \<phi> y in v]"
        then obtain y where y_def: "[(\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) \<^bold>& \<phi> y in v]"
          by (rule ExERule)
        hence "\<And> F . [\<lparr>F,x\<^sup>P\<rparr> in v] = [\<lparr>F,y\<^sup>P\<rparr> in v]"
          apply - apply (drule ConjE) apply (drule conjunct1)
          apply (drule AllE) apply (drule EquivE) by simp
        hence "[\<lparr>make\<Pi>\<^sub>1 (\<lambda> u s w . \<nu>\<upsilon> dj y = u),x\<^sup>P\<rparr> in v]
             = [\<lparr>make\<Pi>\<^sub>1 (\<lambda> u s w . \<nu>\<upsilon> dj y = u),y\<^sup>P\<rparr> in v]" by auto
        hence "\<nu>\<upsilon> dj y = \<nu>\<upsilon> dj x" by (simp add: meta_defs meta_aux)
        moreover have "[\<phi> y in v]" using y_def ConjE by blast
        ultimately have "[\<lparr>(\<^bold>\<lambda> x . \<phi> x), x\<^sup>P\<rparr> in v]"
          using lambda_ex by blast
      }
      ultimately show "[\<lparr>\<^bold>\<lambda>x. \<phi> x,x\<^sup>P\<rparr> in v]
          = [\<^bold>\<exists>y. (\<^bold>\<forall>F. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) \<^bold>& \<phi> y in v]"
        by auto
    qed

  lemma lambda_enc_emb:
    "[\<lparr>(\<^bold>\<lambda> x . \<lbrace>x\<^sup>P, F\<rbrace>), x\<^sup>P\<rparr> \<^bold>\<equiv> (\<^bold>\<exists> y . (\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) \<^bold>& \<lbrace>y\<^sup>P, F\<rbrace>) in v]"
    using lambda_ex_emb by simp

  lemma lambda_desc:
    "[\<lparr>(\<^bold>\<lambda> x . \<lparr>F,\<^bold>\<iota>z . \<phi> z x\<rparr>), x\<^sup>P\<rparr> \<^bold>\<equiv> (\<^bold>\<exists> y . (\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) \<^bold>& \<lparr>F,\<^bold>\<iota>z . \<phi> z y\<rparr>) in v]"
    using lambda_ex_emb by simp

end

(*<*)
end
(*>*)
