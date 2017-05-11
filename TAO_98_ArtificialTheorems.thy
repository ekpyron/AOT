(*<*)
theory TAO_98_ArtificialTheorems
imports TAO_7_Axioms TAO_9_PLM
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

  lemma lambda_ex2:
    "[\<^bold>\<exists> x . \<lparr>(\<^bold>\<lambda> x . \<lbrace>x\<^sup>P,F\<rbrace>), x\<^sup>P\<rparr> in v]"
    apply (simp add: meta_defs meta_aux exists_def forall_\<nu>_def)
    using \<nu>.simps(6) by blast

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

  lemma lambda:
    "[\<^bold>\<exists> F x . \<lparr>(\<^bold>\<lambda> y . \<lbrace>y\<^sup>P,F\<rbrace>), x\<^sup>P\<rparr> \<^bold>& \<^bold>\<not>\<lbrace>x\<^sup>P,F\<rbrace> in v]"
  proof -
    interpret PLM .
    have "[\<^bold>\<exists>x y. \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& x \<^bold>\<noteq> y \<^bold>& (\<^bold>\<forall>F. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) in v]" using aclassical2 by auto
    then obtain x where "[\<^bold>\<exists> y. \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& x \<^bold>\<noteq> y \<^bold>& (\<^bold>\<forall>F. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) in v]" by (rule Instantiate)
    then obtain y where xy_def: "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& x \<^bold>\<noteq> y \<^bold>& (\<^bold>\<forall>F. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) in v]" by (rule Instantiate)
    have "[\<^bold>\<exists> F . \<^bold>\<not>(\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>y\<^sup>P,F\<rbrace>) in v]"
      using cqt_further_2[equiv_lr] reductio_aa_2[OF xy_def[conj1,conj2], where \<phi>="\<^bold>\<forall> F . (\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>y\<^sup>P,F\<rbrace>)", unfolded identity_\<nu>_def, OF ab_obey_1[deduction, OF xy_def[conj1,conj1], deduction]]
      by blast
    then obtain F where "[\<^bold>\<not>(\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>y\<^sup>P,F\<rbrace>) in v]" by (rule Instantiate)
    hence "[(\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>& \<^bold>\<not>\<lbrace>y\<^sup>P,F\<rbrace>) \<^bold>\<or> (\<^bold>\<not>\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>& \<lbrace>y\<^sup>P,F\<rbrace>) in v]" apply - by PLM_solver
    moreover {
      assume 1: "[\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>& \<^bold>\<not>\<lbrace>y\<^sup>P,F\<rbrace> in v]"
      hence "[(\<^bold>\<forall> F . \<lparr>F,y\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,x\<^sup>P\<rparr>) \<^bold>& \<lbrace>x\<^sup>P,F\<rbrace> in v]" using xy_def[conj2] apply - by PLM_solver
      hence "[\<^bold>\<exists> x . (\<^bold>\<forall> F . \<lparr>F,y\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,x\<^sup>P\<rparr>) \<^bold>& \<lbrace>x\<^sup>P,F\<rbrace> in v]" by (rule existential)
      hence "[\<lparr>(\<^bold>\<lambda> x . \<lbrace>x\<^sup>P,F\<rbrace>), y\<^sup>P\<rparr> in v]" using lambda_ex_emb[equiv_rl] by simp
      hence "[\<lparr>(\<^bold>\<lambda> x . \<lbrace>x\<^sup>P,F\<rbrace>), y\<^sup>P\<rparr> \<^bold>& \<^bold>\<not>\<lbrace>y\<^sup>P,F\<rbrace> in v]" using 1[conj2] "\<^bold>&I" by auto
      hence "[\<^bold>\<exists> y . \<lparr>(\<^bold>\<lambda> x . \<lbrace>x\<^sup>P,F\<rbrace>), y\<^sup>P\<rparr> \<^bold>& \<^bold>\<not>\<lbrace>y\<^sup>P,F\<rbrace> in v]" by (rule existential)
      hence ?thesis by (rule existential)
    }
    moreover {
      assume 1: "[\<^bold>\<not>\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>& \<lbrace>y\<^sup>P,F\<rbrace> in v]"
      hence "[(\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) \<^bold>& \<lbrace>y\<^sup>P,F\<rbrace> in v]" using xy_def[conj2] apply - by PLM_solver
      hence "[\<^bold>\<exists> y . (\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) \<^bold>& \<lbrace>y\<^sup>P,F\<rbrace> in v]" by (rule existential)
      hence "[\<lparr>(\<^bold>\<lambda> x . \<lbrace>x\<^sup>P,F\<rbrace>), x\<^sup>P\<rparr> in v]" using lambda_ex_emb[equiv_rl] by simp
      hence "[\<lparr>(\<^bold>\<lambda> x . \<lbrace>x\<^sup>P,F\<rbrace>), x\<^sup>P\<rparr> \<^bold>& \<^bold>\<not>\<lbrace>x\<^sup>P,F\<rbrace> in v]" using 1[conj1] "\<^bold>&I" by auto
      hence "[\<^bold>\<exists> y . \<lparr>(\<^bold>\<lambda> x . \<lbrace>x\<^sup>P,F\<rbrace>), y\<^sup>P\<rparr> \<^bold>& \<^bold>\<not>\<lbrace>y\<^sup>P,F\<rbrace> in v]" by (rule existential)
      hence ?thesis by (rule existential)
    }
    ultimately show ?thesis
      using PLM(67) PLM(81) by blast
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
