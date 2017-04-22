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
    "[\<lparr>(\<^bold>\<lambda> x . \<lbrace>x\<^sup>P, F\<rbrace>), x\<^sup>P\<rparr> in v] \<longrightarrow> (\<exists> y . \<nu>\<upsilon> dj y = \<nu>\<upsilon> dj x \<and> [\<lbrace>y\<^sup>P, F\<rbrace> in v])"
    apply (simp add: meta_defs meta_aux)
    by (metis \<nu>\<upsilon>_\<upsilon>\<nu>_id id_apply)

  lemma lambda_enc_5:
    "(\<forall> y . \<nu>\<upsilon> dj y = \<nu>\<upsilon> dj x \<longrightarrow> [\<lbrace>y\<^sup>P, F\<rbrace> in v]) \<longrightarrow> [\<lparr>(\<^bold>\<lambda> x . \<lbrace>x\<^sup>P, F\<rbrace>), x\<^sup>P\<rparr> in v]"
    by (simp add: meta_defs meta_aux)

text{*
\begin{remark}
  These statements can also be translated to statements in the embedded logic.
\end{remark}
*}

  lemma lambda_enc_4b:
    "[\<lparr>(\<^bold>\<lambda> x . \<lbrace>x\<^sup>P, F\<rbrace>), x\<^sup>P\<rparr> \<^bold>\<rightarrow> (\<^bold>\<exists> y . (\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) \<^bold>& \<lbrace>y\<^sup>P, F\<rbrace>) in v]"
    proof(rule MetaSolver.ImplI)
      interpret MetaSolver .
      assume "[\<lparr>(\<^bold>\<lambda> x . \<lbrace>x\<^sup>P, F\<rbrace>), x\<^sup>P\<rparr> in v]"
      then obtain y where "\<nu>\<upsilon> dj y = \<nu>\<upsilon> dj x \<and> [\<lbrace>y\<^sup>P, F\<rbrace> in v]"
        using lambda_enc_4 by blast
      moreover hence "[(\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) in v]"
        apply - apply meta_solver
        by (simp add: Semantics.d\<^sub>\<kappa>_proper Semantics.ex1_def)
      ultimately show "[\<^bold>\<exists> y . (\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) \<^bold>& \<lbrace>y\<^sup>P, F\<rbrace> in v]"
        using ExIRule ConjI by fast
    qed

  lemma lambda_enc_5b:
    "[(\<^bold>\<forall> y . (\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) \<^bold>\<rightarrow> \<lbrace>y\<^sup>P, F\<rbrace>) \<^bold>\<rightarrow> \<lparr>(\<^bold>\<lambda> x . \<lbrace>x\<^sup>P, F\<rbrace>), x\<^sup>P\<rparr> in v]"
    proof(rule MetaSolver.ImplI)
      interpret MetaSolver .
      assume 1: "[\<^bold>\<forall> y . (\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) \<^bold>\<rightarrow> \<lbrace>y\<^sup>P, F\<rbrace> in v]"
      {
        fix y
        have y_prop: "[(\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) \<^bold>\<rightarrow> \<lbrace>y\<^sup>P, F\<rbrace> in v]"
          using AllE 1 by auto
        {
          assume "\<nu>\<upsilon> dj y = \<nu>\<upsilon> dj x"
          hence "[\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr> in v]"
            apply - apply meta_solver
            by (simp add: Semantics.d\<^sub>\<kappa>_proper Semantics.ex1_def)
          hence "[\<lbrace>y\<^sup>P, F\<rbrace> in v]" using y_prop ImplE by blast
        }
      }
      thus "[\<lparr>(\<^bold>\<lambda> x . \<lbrace>x\<^sup>P, F\<rbrace>), x\<^sup>P\<rparr> in v]"
        using lambda_enc_5 by auto
    qed

end

(*<*)
end
(*>*)
