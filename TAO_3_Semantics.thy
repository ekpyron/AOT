(*<*)
theory TAO_3_Semantics
imports TAO_1_Embedding TAO_2_BasicDefinitions "~~/src/HOL/Eisbach/Eisbach"
begin
(*>*)

section{* Semantics *}
text{* \label{TAO_Semantics} *}

subsection{* Propositional Formulas *}
text{* \label{TAO_Semantics_Propositional} *}

text{*
\begin{remark}
  The embedding extends the notion of propositional formulas
  to functions that are propositional in the individual variables
  that are their parameters, i.e. their parameters only occur
  in exemplification and not in encoding subformulas. This weaker
  condition is enough to prove the semantics of propositional
  formulas.
  This condition can be represented by the property of a function in x
  that it only depends on the urelement corresponding to x under the actual
  state. The predicates IsPropositionalInX (resp. InXY, InXYZ) are defined
  accordingly and a set of introduction rules are proven which can be used
  to show that these predicates hold for any function from objects to truth
  values that do not contain encoding subformulas in their parameters.
\end{remark}
*}

named_theorems IsPropositional_intros

lift_definition IsPropositionalInX :: "(\<kappa>\<Rightarrow>\<o>)\<Rightarrow>bool" is
  "\<lambda> \<phi> . \<forall> x v . (v \<Turnstile> \<phi> (x\<^sup>P)) = (v \<Turnstile> \<phi> ((\<upsilon>\<nu> dj (\<nu>\<upsilon> dj x))\<^sup>P))" .
lift_definition IsPropositionalInXY :: "(\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<o>)\<Rightarrow>bool" is
  "\<lambda> \<phi> . \<forall> x y v . (v \<Turnstile> \<phi> (x\<^sup>P) (y\<^sup>P)) = (v \<Turnstile> \<phi> ((\<upsilon>\<nu> dj (\<nu>\<upsilon> dj x))\<^sup>P) ((\<upsilon>\<nu> dj (\<nu>\<upsilon> dj y))\<^sup>P))" .
lift_definition IsPropositionalInXYZ :: "(\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<o>)\<Rightarrow>bool" is
  "\<lambda> \<phi> . \<forall> x y z v . (v \<Turnstile> \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P)) = (v \<Turnstile> \<phi> ((\<upsilon>\<nu> dj (\<nu>\<upsilon> dj x))\<^sup>P) ((\<upsilon>\<nu> dj (\<nu>\<upsilon> dj y))\<^sup>P) ((\<upsilon>\<nu> dj (\<nu>\<upsilon> dj z))\<^sup>P))" .


named_theorems IsPropositionalIn_defs
declare IsPropositionalInX_def[IsPropositionalIn_defs]
        IsPropositionalInXY_def[IsPropositionalIn_defs]
        IsPropositionalInXYZ_def[IsPropositionalIn_defs]

lemma IsPropositionalInX_const[IsPropositional_intros]:
  "IsPropositionalInX (\<lambda> x . \<Theta>)"
  unfolding IsPropositionalInX_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInX_impl[IsPropositional_intros]:
  assumes "IsPropositionalInX \<phi>" and "IsPropositionalInX \<psi>"
  shows "IsPropositionalInX (\<lambda> x . \<phi> x \<^bold>\<rightarrow> \<psi> x)"
  using assms unfolding IsPropositionalInX_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInX_not[IsPropositional_intros]:
  assumes "IsPropositionalInX \<phi>"
  shows "IsPropositionalInX (\<lambda> x . \<^bold>\<not>\<phi> x)"
  using assms unfolding IsPropositionalInX_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInX_box[IsPropositional_intros]:
  assumes "IsPropositionalInX \<phi>"
  shows "IsPropositionalInX (\<lambda> x . \<^bold>\<box>\<phi> x)"
  using assms unfolding IsPropositionalInX_def
  by (auto simp: meta_defs meta_aux)
lemma IsPropositionalInX_actual[IsPropositional_intros]:
  assumes "IsPropositionalInX \<phi>"
  shows "IsPropositionalInX (\<lambda> x . \<^bold>\<A>\<phi> x)"
  using assms unfolding IsPropositionalInX_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInX_forall\<^sub>0[IsPropositional_intros]:
  assumes "\<And> a . IsPropositionalInX (\<phi> a)"
  shows "IsPropositionalInX (\<lambda> x . \<^bold>\<forall>\<^sub>0 a . \<phi> a x)"
  using assms unfolding IsPropositionalInX_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInX_forall\<^sub>1[IsPropositional_intros]:
  assumes "\<And> a . IsPropositionalInX (\<phi> a)"
  shows "IsPropositionalInX (\<lambda> x . \<^bold>\<forall>\<^sub>1 a . \<phi> a x)"
  using assms unfolding IsPropositionalInX_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInX_forall\<^sub>2[IsPropositional_intros]:
  assumes "\<And> a . IsPropositionalInX (\<phi> a)"
  shows "IsPropositionalInX (\<lambda> x . \<^bold>\<forall>\<^sub>2 a . \<phi> a x)"
  using assms unfolding IsPropositionalInX_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInX_forall\<^sub>3[IsPropositional_intros]:
  assumes "\<And> a . IsPropositionalInX (\<phi> a)"
  shows "IsPropositionalInX (\<lambda> x . \<^bold>\<forall>\<^sub>3 a . \<phi> a x)"
  using assms unfolding IsPropositionalInX_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInX_forall\<^sub>\<nu>[IsPropositional_intros]:
  assumes "\<And> a . IsPropositionalInX (\<phi> a)"
  shows "IsPropositionalInX (\<lambda> x . \<^bold>\<forall>\<^sub>\<nu> a . \<phi> a x)"
  using assms unfolding IsPropositionalInX_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInX_ex_x[IsPropositional_intros]:
  "IsPropositionalInX (\<lambda> x . \<lparr>F,x\<rparr>)"
  unfolding IsPropositionalInX_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInX_ex_xx[IsPropositional_intros]:
  "IsPropositionalInX (\<lambda> x . \<lparr>F,x,x\<rparr>)"
  unfolding IsPropositionalInX_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInX_ex_xb[IsPropositional_intros]:
  "IsPropositionalInX (\<lambda> x . \<lparr>F,x,b\<rparr>)"
  unfolding IsPropositionalInX_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInX_ex_ax[IsPropositional_intros]:
  "IsPropositionalInX (\<lambda> x . \<lparr>F,a,x\<rparr>)"
  unfolding IsPropositionalInX_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInX_ex_xxx[IsPropositional_intros]:
  "IsPropositionalInX (\<lambda> x . \<lparr>F,x,x,x\<rparr>)"
  unfolding IsPropositionalInX_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInX_ex_xxc[IsPropositional_intros]:
  "IsPropositionalInX (\<lambda> x . \<lparr>F,x,x,c\<rparr>)"
  unfolding IsPropositionalInX_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInX_ex_xbx[IsPropositional_intros]:
  "IsPropositionalInX (\<lambda> x . \<lparr>F,x,b,x\<rparr>)"
  unfolding IsPropositionalInX_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInX_ex_xbc[IsPropositional_intros]:
  "IsPropositionalInX (\<lambda> x . \<lparr>F,x,b,c\<rparr>)"
  unfolding IsPropositionalInX_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInX_ex_axx[IsPropositional_intros]:
  "IsPropositionalInX (\<lambda> x . \<lparr>F,a,x,x\<rparr>)"
  unfolding IsPropositionalInX_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInX_ex_axc[IsPropositional_intros]:
  "IsPropositionalInX (\<lambda> x . \<lparr>F,a,x,c\<rparr>)"
  unfolding IsPropositionalInX_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInX_ex_abx[IsPropositional_intros]:
  "IsPropositionalInX (\<lambda> x . \<lparr>F,a,b,x\<rparr>)"
  unfolding IsPropositionalInX_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_const[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<Theta>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_impl[IsPropositional_intros]:
  assumes "IsPropositionalInXY \<phi>" and "IsPropositionalInXY \<psi>"
  shows "IsPropositionalInXY (\<lambda> x y . \<phi> x y \<^bold>\<rightarrow> \<psi> x y)"
  using assms unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_not[IsPropositional_intros]:
  assumes "IsPropositionalInXY \<phi>"
  shows "IsPropositionalInXY (\<lambda> x y . \<^bold>\<not>\<phi> x y)"
  using assms unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_box[IsPropositional_intros]:
  assumes "IsPropositionalInXY \<phi>"
  shows "IsPropositionalInXY (\<lambda> x y . \<^bold>\<box>\<phi> x y)"
  using assms unfolding IsPropositionalInXY_def
  by (auto simp: meta_defs meta_aux)
lemma IsPropositionalInXY_actual[IsPropositional_intros]:
  assumes "IsPropositionalInXY \<phi>"
  shows "IsPropositionalInXY (\<lambda> x y . \<^bold>\<A>\<phi> x y)"
  using assms unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_forall\<^sub>0[IsPropositional_intros]:
  assumes "\<And> a . IsPropositionalInXY (\<phi> a)"
  shows "IsPropositionalInXY (\<lambda> x y . \<^bold>\<forall>\<^sub>0 a . \<phi> a x y)"
  using assms unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_forall\<^sub>1[IsPropositional_intros]:
  assumes "\<And> a . IsPropositionalInXY (\<phi> a)"
  shows "IsPropositionalInXY (\<lambda> x y . \<^bold>\<forall>\<^sub>1 a . \<phi> a x y)"
  using assms unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_forall\<^sub>2[IsPropositional_intros]:
  assumes "\<And> a . IsPropositionalInXY (\<phi> a)"
  shows "IsPropositionalInXY (\<lambda> x y . \<^bold>\<forall>\<^sub>2 a . \<phi> a x y)"
  using assms unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_forall\<^sub>3[IsPropositional_intros]:
  assumes "\<And> a . IsPropositionalInXY (\<phi> a)"
  shows "IsPropositionalInXY (\<lambda> x y . \<^bold>\<forall>\<^sub>3 a . \<phi> a x y)"
  using assms unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_forall\<^sub>\<nu>[IsPropositional_intros]:
  assumes "\<And> a . IsPropositionalInXY (\<phi> a)"
  shows "IsPropositionalInXY (\<lambda> x y . \<^bold>\<forall>\<^sub>\<nu> a . \<phi> a x y)"
  using assms unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_x[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,x\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_y[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,y\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_xx[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,x,x\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_xy[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,x,y\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_xb[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,x,b\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_yx[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,y,x\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_yy[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,y,y\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_yb[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,y,b\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_ax[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,a,x\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_ay[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,a,y\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_xxx[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,x,x,x\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_xxy[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,x,x,y\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_xxc[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,x,x,c\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_xyx[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,x,y,x\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_xyy[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,x,y,y\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_xyc[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,x,y,c\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_xbx[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,x,b,x\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_xby[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,x,b,y\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_xbc[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,x,b,c\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_yxx[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,y,x,x\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_yxy[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,y,x,y\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_yxc[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,y,x,c\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_yyx[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,y,y,x\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_yyy[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,y,y,y\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_yyc[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,y,y,c\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_ybx[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,y,b,x\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_yby[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,y,b,y\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_ybc[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,y,b,c\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_axx[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,a,x,x\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_axy[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,a,x,y\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_axc[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,a,x,c\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_ayx[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,a,y,x\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_ayy[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,a,y,y\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_ayc[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,a,y,c\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_abx[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,a,b,x\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXY_ex_aby[IsPropositional_intros]:
  "IsPropositionalInXY (\<lambda> x y . \<lparr>F,a,b,y\<rparr>)"
  unfolding IsPropositionalInXY_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_const[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<Theta>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_impl[IsPropositional_intros]:
  assumes "IsPropositionalInXYZ \<phi>" and "IsPropositionalInXYZ \<psi>"
  shows "IsPropositionalInXYZ (\<lambda> x y z . \<phi> x y z \<^bold>\<rightarrow> \<psi> x y z)"
  using assms unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_not[IsPropositional_intros]:
  assumes "IsPropositionalInXYZ \<phi>"
  shows "IsPropositionalInXYZ (\<lambda> x y z . \<^bold>\<not>\<phi> x y z)"
  using assms unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_box[IsPropositional_intros]:
  assumes "IsPropositionalInXYZ \<phi>"
  shows "IsPropositionalInXYZ (\<lambda> x y z . \<^bold>\<box>\<phi> x y z)"
  using assms unfolding IsPropositionalInXYZ_def
  by (auto simp: meta_defs meta_aux)
lemma IsPropositionalInXYZ_actual[IsPropositional_intros]:
  assumes "IsPropositionalInXYZ \<phi>"
  shows "IsPropositionalInXYZ (\<lambda> x y z . \<^bold>\<A>\<phi> x y z)"
  using assms unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_forall\<^sub>0[IsPropositional_intros]:
  assumes "\<And> a . IsPropositionalInXYZ (\<phi> a)"
  shows "IsPropositionalInXYZ (\<lambda> x y z . \<^bold>\<forall>\<^sub>0 a . \<phi> a x y z)"
  using assms unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_forall\<^sub>1[IsPropositional_intros]:
  assumes "\<And> a . IsPropositionalInXYZ (\<phi> a)"
  shows "IsPropositionalInXYZ (\<lambda> x y z . \<^bold>\<forall>\<^sub>1 a . \<phi> a x y z)"
  using assms unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_forall\<^sub>2[IsPropositional_intros]:
  assumes "\<And> a . IsPropositionalInXYZ (\<phi> a)"
  shows "IsPropositionalInXYZ (\<lambda> x y z . \<^bold>\<forall>\<^sub>2 a . \<phi> a x y z)"
  using assms unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_forall\<^sub>3[IsPropositional_intros]:
  assumes "\<And> a . IsPropositionalInXYZ (\<phi> a)"
  shows "IsPropositionalInXYZ (\<lambda> x y z . \<^bold>\<forall>\<^sub>3 a . \<phi> a x y z)"
  using assms unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_forall\<^sub>\<nu>[IsPropositional_intros]:
  assumes "\<And> a . IsPropositionalInXYZ (\<phi> a)"
  shows "IsPropositionalInXYZ (\<lambda> x y z . \<^bold>\<forall>\<^sub>\<nu> a . \<phi> a x y z)"
  using assms unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_x[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_y[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_z[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_xx[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_xy[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_xz[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_xb[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x,b\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_yx[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_yy[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_yz[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_yb[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y,b\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_zx[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_zy[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_zz[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_zb[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z,b\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_ax[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,a,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_ay[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,a,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_az[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,a,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_xxx[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x,x,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_xxy[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x,x,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_xxz[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x,x,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_xxc[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x,x,c\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_xyx[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x,y,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_xyy[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x,y,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_xyz[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x,y,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_xyc[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x,y,c\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_xzx[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x,z,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_xzy[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x,z,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_xzz[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x,z,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_xzc[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x,z,c\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_xbx[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x,b,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_xby[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x,b,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_xbz[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x,b,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_xbc[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,x,b,c\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_yxx[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y,x,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_yxy[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y,x,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_yxz[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y,x,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_yxc[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y,x,c\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_yyx[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y,y,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_yyy[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y,y,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_yyz[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y,y,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_yyc[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y,y,c\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_yzx[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y,z,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_yzy[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y,z,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_yzz[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y,z,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_yzc[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y,z,c\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_ybx[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y,b,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_yby[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y,b,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_ybz[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y,b,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_ybc[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,y,b,c\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_zxx[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z,x,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_zxy[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z,x,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_zxz[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z,x,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_zxc[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z,x,c\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_zyx[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z,y,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_zyy[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z,y,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_zyz[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z,y,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_zyc[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z,y,c\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_zzx[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z,z,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_zzy[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z,z,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_zzz[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z,z,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_zzc[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z,z,c\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_zbx[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z,b,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_zby[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z,b,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_zbz[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z,b,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_zbc[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,z,b,c\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_axx[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,a,x,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_axy[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,a,x,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_axz[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,a,x,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_axc[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,a,x,c\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_ayx[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,a,y,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_ayy[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,a,y,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_ayz[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,a,y,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_ayc[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,a,y,c\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_azx[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,a,z,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_azy[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,a,z,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_azz[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,a,z,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_azc[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,a,z,c\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_abx[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,a,b,x\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_aby[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,a,b,y\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)
lemma IsPropositionalInXYZ_ex_abz[IsPropositional_intros]:
  "IsPropositionalInXYZ (\<lambda> x y z . \<lparr>F,a,b,z\<rparr>)"
  unfolding IsPropositionalInXYZ_def
  by (simp add: meta_defs meta_aux)



lemma IsPropositionalInX_diamond[IsPropositional_intros]:
  assumes "IsPropositionalInX \<phi>"
  shows "IsPropositionalInX (\<lambda> x . \<^bold>\<diamond>\<phi> x)"
  unfolding conn_defs using assms
  by (simp add: IsPropositional_intros)


subsection{* Semantics *}
text{* \label{TAO_Semantics_Semantics} *}

locale Semantics
begin
  named_theorems semantics

  text{* The domains for the terms in the language. *}
  type_synonym R\<^sub>\<kappa> = "\<nu>"
  type_synonym R\<^sub>0 = "j\<Rightarrow>i\<Rightarrow>bool"
  type_synonym R\<^sub>1 = "\<upsilon>\<Rightarrow>R\<^sub>0"
  type_synonym R\<^sub>2 = "\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>R\<^sub>0"
  type_synonym R\<^sub>3 = "\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>R\<^sub>0"
  type_synonym W = i

  text{* Denotations of the terms in the language. *}
  lift_definition d\<^sub>\<kappa> :: "\<kappa>\<Rightarrow>R\<^sub>\<kappa> option" is id .
  lift_definition d\<^sub>0 :: "\<Pi>\<^sub>0\<Rightarrow>R\<^sub>0 option" is Some .
  lift_definition d\<^sub>1 :: "\<Pi>\<^sub>1\<Rightarrow>R\<^sub>1 option" is Some .
  lift_definition d\<^sub>2 :: "\<Pi>\<^sub>2\<Rightarrow>R\<^sub>2 option" is Some .
  lift_definition d\<^sub>3 :: "\<Pi>\<^sub>3\<Rightarrow>R\<^sub>3 option" is Some .

  text{* Designated actual world. *}
  definition w\<^sub>0 where "w\<^sub>0 \<equiv> dw"

  text{* Exemplification extensions. *}

  definition ex0 :: "R\<^sub>0\<Rightarrow>W\<Rightarrow>bool"
    where "ex0 \<equiv> \<lambda> F . F dj"
  definition ex1 :: "R\<^sub>1\<Rightarrow>W\<Rightarrow>(R\<^sub>\<kappa> set)"
    where "ex1 \<equiv> \<lambda> F w . { x . F (\<nu>\<upsilon> dj x) dj w }"
  definition ex2 :: "R\<^sub>2\<Rightarrow>W\<Rightarrow>((R\<^sub>\<kappa>\<times>R\<^sub>\<kappa>) set)"
    where "ex2 \<equiv> \<lambda> F w . { (x,y) . F (\<nu>\<upsilon> dj x) (\<nu>\<upsilon> dj y) dj w }"
  definition ex3 :: "R\<^sub>3\<Rightarrow>W\<Rightarrow>((R\<^sub>\<kappa>\<times>R\<^sub>\<kappa>\<times>R\<^sub>\<kappa>) set)"
    where "ex3 \<equiv> \<lambda> F w . { (x,y,z) . F (\<nu>\<upsilon> dj x) (\<nu>\<upsilon> dj y) (\<nu>\<upsilon> dj z) dj w }"

  text{* Encoding extensions. *}

  definition en :: "R\<^sub>1\<Rightarrow>(R\<^sub>\<kappa> set)"
    where "en \<equiv> \<lambda> F . { x . case x of \<alpha>\<nu> y \<Rightarrow> make\<Pi>\<^sub>1 (\<lambda> x . F x) \<in> y
                                       | _ \<Rightarrow> False }"

  text{* Collect definitions. *}
  named_theorems semantics_defs
  declare d\<^sub>0_def[semantics_defs] d\<^sub>1_def[semantics_defs]
          d\<^sub>2_def[semantics_defs] d\<^sub>3_def[semantics_defs]
          ex0_def[semantics_defs] ex1_def[semantics_defs]
          ex2_def[semantics_defs] ex3_def[semantics_defs]
          en_def[semantics_defs] d\<^sub>\<kappa>_def[semantics_defs]
          w\<^sub>0_def[semantics_defs]

  text{* Semantics for exemplification and encoding. *}

  lemma T1_1[semantics]:
    "(w \<Turnstile> \<lparr>F,x\<rparr>) = (\<exists> r o\<^sub>1 . Some r = d\<^sub>1 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 \<in> ex1 r w)"
    unfolding semantics_defs
    apply (simp add: meta_defs meta_aux rep_def proper_def)
    by (metis option.discI option.exhaust option.sel)

  lemma T1_2[semantics]:
    "(w \<Turnstile> \<lparr>F,x,y\<rparr>) = (\<exists> r o\<^sub>1 o\<^sub>2 . Some r = d\<^sub>2 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x
                               \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> (o\<^sub>1, o\<^sub>2) \<in> ex2 r w)"
    unfolding semantics_defs
    apply (simp add: meta_defs meta_aux rep_def proper_def)
    by (metis option.discI option.exhaust option.sel)

  lemma T1_3[semantics]:
    "(w \<Turnstile> \<lparr>F,x,y,z\<rparr>) = (\<exists> r o\<^sub>1 o\<^sub>2 o\<^sub>3 . Some r = d\<^sub>3 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x
                                    \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> Some o\<^sub>3 = d\<^sub>\<kappa> z
                                    \<and> (o\<^sub>1, o\<^sub>2, o\<^sub>3) \<in> ex3 r w)"
    unfolding semantics_defs
    apply (simp add: meta_defs meta_aux rep_def proper_def)
    by (metis option.discI option.exhaust option.sel)

  lemma T2[semantics]:
    "(w \<Turnstile> \<lbrace>x,F\<rbrace>) = (\<exists> r o\<^sub>1 . Some r = d\<^sub>1 F \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> o\<^sub>1 \<in> en r)"
    unfolding semantics_defs
    apply (simp add: meta_defs meta_aux rep_def proper_def split: \<nu>.split)
    by (metis \<nu>.exhaust \<nu>.inject(2) \<nu>.simps(4) \<nu>\<kappa>.rep_eq option.collapse
              option.discI rep.rep_eq rep_proper_id)

  lemma T3[semantics]:
    "(w \<Turnstile> \<lparr>F\<rparr>) = (\<exists> r . Some r = d\<^sub>0 F \<and> ex0 r w)"
    unfolding semantics_defs
    by (simp add: meta_defs meta_aux)

  text{* Semantics for connectives and quantifiers. *}

  lemma T4[semantics]: "(w \<Turnstile> \<^bold>\<not>\<psi>) = (\<not>(w \<Turnstile> \<psi>))"
    by (simp add: meta_defs meta_aux)

  lemma T5[semantics]: "(w \<Turnstile> \<psi> \<^bold>\<rightarrow> \<chi>) = (\<not>(w \<Turnstile> \<psi>) \<or> (w \<Turnstile> \<chi>))"
    by (simp add: meta_defs meta_aux)

  lemma T6[semantics]: "(w \<Turnstile> \<^bold>\<box>\<psi>) = (\<forall> v . (v \<Turnstile> \<psi>))"
    by (simp add: meta_defs meta_aux)

  lemma T7[semantics]: "(w \<Turnstile> \<^bold>\<A>\<psi>) = (dw \<Turnstile> \<psi>)"
    by (simp add: meta_defs meta_aux)

  lemma T8_\<nu>[semantics]: "(w \<Turnstile> \<^bold>\<forall>\<^sub>\<nu> x. \<psi> x) = (\<forall> x . (w \<Turnstile> \<psi> x))"
    by (simp add: meta_defs meta_aux)

  lemma T8_0[semantics]: "(w \<Turnstile> \<^bold>\<forall>\<^sub>0 x. \<psi> x) = (\<forall> x . (w \<Turnstile> \<psi> x))"
    by (simp add: meta_defs meta_aux)

  lemma T8_1[semantics]: "(w \<Turnstile> \<^bold>\<forall>\<^sub>1 x. \<psi> x) = (\<forall> x . (w \<Turnstile> \<psi> x))"
    by (simp add: meta_defs meta_aux)

  lemma T8_2[semantics]: "(w \<Turnstile> \<^bold>\<forall>\<^sub>2 x. \<psi> x) = (\<forall> x . (w \<Turnstile> \<psi> x))"
    by (simp add: meta_defs meta_aux)

  lemma T8_3[semantics]: "(w \<Turnstile> \<^bold>\<forall>\<^sub>3 x. \<psi> x) = (\<forall> x . (w \<Turnstile> \<psi> x))"
    by (simp add: meta_defs meta_aux)

  lemma T8_\<o>[semantics]: "(w \<Turnstile> \<^bold>\<forall>\<^sub>\<o> x. \<psi> x) = (\<forall> x . (w \<Turnstile> \<psi> x))"
    by (simp add: meta_defs meta_aux)

  text{* Semantics for descriptions and lambda expressions. *}

  lemma D3[semantics]:
    "d\<^sub>\<kappa> (\<^bold>\<iota>x . \<psi> x) = (if (\<exists>x . (w\<^sub>0 \<Turnstile> \<psi> x) \<and> (\<forall> y . (w\<^sub>0  \<Turnstile> \<psi> y) \<longrightarrow> y = x))
                      then (Some (THE x . (w\<^sub>0 \<Turnstile> \<psi> x))) else None)"
    unfolding semantics_defs
    by (auto simp: meta_defs meta_aux)

  lemma D4_1[semantics]: "d\<^sub>1 (\<^bold>\<lambda> x . \<lparr>F, x\<^sup>P\<rparr>) = d\<^sub>1 F"
    by (simp add: meta_defs meta_aux)

  lemma D4_2[semantics]: "d\<^sub>2 (\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<lparr>F, x\<^sup>P, y\<^sup>P\<rparr>)) = d\<^sub>2 F"
    by (simp add: meta_defs meta_aux)

  lemma D4_3[semantics]: "d\<^sub>3 (\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<lparr>F, x\<^sup>P, y\<^sup>P, z\<^sup>P\<rparr>)) = d\<^sub>3 F"
    by (simp add: meta_defs meta_aux)

  lemma D5_1[semantics]:
    assumes "IsPropositionalInX \<phi>"
    shows "\<And> w o\<^sub>1 r . Some r = d\<^sub>1 (\<^bold>\<lambda> x . (\<phi> (x\<^sup>P))) \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x
                      \<longrightarrow> (o\<^sub>1 \<in> ex1 r w) = (w \<Turnstile> \<phi> x)"
    using assms unfolding IsPropositionalIn_defs semantics_defs
    by (auto simp: meta_defs meta_aux rep_def proper_def \<nu>\<kappa>.abs_eq)

  lemma D5_2[semantics]:
    assumes "IsPropositionalInXY \<phi>"
    shows "\<And> w o\<^sub>1 o\<^sub>2 r . Some r = d\<^sub>2 (\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<phi> (x\<^sup>P) (y\<^sup>P)))
                       \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y
                       \<longrightarrow> ((o\<^sub>1,o\<^sub>2) \<in> ex2 r w) = (w \<Turnstile> \<phi> x y)"
    using assms unfolding IsPropositionalInXY_def semantics_defs
    by (auto simp: meta_defs meta_aux rep_def proper_def \<nu>\<kappa>.abs_eq)

  lemma D5_3[semantics]:
    assumes "IsPropositionalInXYZ \<phi>"
    shows "\<And> w o\<^sub>1 o\<^sub>2 o\<^sub>3 r . Some r = d\<^sub>3 (\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P)))
                          \<and> Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> Some o\<^sub>2 = d\<^sub>\<kappa> y \<and> Some o\<^sub>3 = d\<^sub>\<kappa> z
                          \<longrightarrow> ((o\<^sub>1,o\<^sub>2,o\<^sub>3) \<in> ex3 r w) = (w \<Turnstile> \<phi> x y z)"
    using assms unfolding IsPropositionalInXYZ_def semantics_defs
    by (auto simp: meta_defs meta_aux rep_def proper_def \<nu>\<kappa>.abs_eq)

  lemma D6[semantics]: "(\<And> w r . Some r = d\<^sub>0 (\<^bold>\<lambda>\<^sup>0 \<phi>) \<longrightarrow> ex0 r w = (w \<Turnstile> \<phi>))"
    by (auto simp: meta_defs meta_aux semantics_defs)

  text{* Auxiliary lemmata. *}

  lemma propex\<^sub>0: "\<exists> r . Some r = d\<^sub>0 F"
    unfolding d\<^sub>0_def by simp
  lemma propex\<^sub>1: "\<exists> r . Some r = d\<^sub>1 F"
    unfolding d\<^sub>1_def by simp
  lemma propex\<^sub>2: "\<exists> r . Some r = d\<^sub>2 F"
    unfolding d\<^sub>2_def by simp
  lemma propex\<^sub>3: "\<exists> r . Some r = d\<^sub>3 F"
    unfolding d\<^sub>3_def by simp
  lemma d\<^sub>0_inject: "\<And>x y. d\<^sub>0 x = d\<^sub>0 y \<Longrightarrow> x = y"
    unfolding d\<^sub>0_def by (simp add: eval\<o>_inject)
  lemma d\<^sub>1_inject: "\<And>x y. d\<^sub>1 x = d\<^sub>1 y \<Longrightarrow> x = y"
    unfolding d\<^sub>1_def by (simp add: eval\<Pi>\<^sub>1_inject)
  lemma d\<^sub>2_inject: "\<And>x y. d\<^sub>2 x = d\<^sub>2 y \<Longrightarrow> x = y"
    unfolding d\<^sub>2_def by (simp add: eval\<Pi>\<^sub>2_inject)
  lemma d\<^sub>3_inject: "\<And>x y. d\<^sub>3 x = d\<^sub>3 y \<Longrightarrow> x = y"
    unfolding d\<^sub>3_def by (simp add: eval\<Pi>\<^sub>3_inject)
  lemma d\<^sub>\<kappa>_inject: "\<And>x y o\<^sub>1. Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> Some o\<^sub>1 = d\<^sub>\<kappa> y \<Longrightarrow> x = y"
  proof -
    fix x :: \<kappa> and y :: \<kappa> and o\<^sub>1 :: \<nu>
    assume "Some o\<^sub>1 = d\<^sub>\<kappa> x \<and> Some o\<^sub>1 = d\<^sub>\<kappa> y"
    thus "x = y" apply transfer by auto
  qed
  lemma d\<^sub>\<kappa>_proper: "d\<^sub>\<kappa> (u\<^sup>P) = Some u"
    unfolding d\<^sub>\<kappa>_def by (simp add: \<nu>\<kappa>_def meta_aux)
  lemma ConcretenessSemantics1:
    "Some r = d\<^sub>1 E! \<Longrightarrow> (\<forall> x . \<exists> w . \<omega>\<nu> x \<in> ex1 r w)"
    unfolding semantics_defs apply transfer
    by (simp add: OrdinaryObjectsPossiblyConcreteAxiom \<nu>\<upsilon>_\<omega>\<nu>_is_\<omega>\<upsilon>)
  lemma ConcretenessSemantics2:
    "Some r = d\<^sub>1 E! \<Longrightarrow> (\<forall> x . x \<in> ex1 r w \<longrightarrow> (\<exists>y. x = \<omega>\<nu> y))"
    unfolding semantics_defs apply transfer apply simp
    by (metis \<nu>.exhaust \<upsilon>.exhaust \<upsilon>.simps(6) no_\<alpha>\<omega>)
end

subsection{* Validity Syntax *}
text{* \label{TAO_Semantics_Validity} *}

(* disable list syntax [] to replace it with truth evaluation *)
(*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
(*<*) no_syntax "__listcompr" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 

abbreviation validity_in :: "\<o>\<Rightarrow>i\<Rightarrow>bool" ("[_ in _]" [1]) where
  "validity_in \<equiv> \<lambda> \<phi> v . v \<Turnstile> \<phi>"
abbreviation actual_validity :: "\<o>\<Rightarrow>bool" ("[_]" [1]) where
  "actual_validity \<equiv> \<lambda> \<phi> . dw \<Turnstile> \<phi>"
abbreviation necessary_validity :: "\<o>\<Rightarrow>bool" ("\<box>[_]" [1]) where
  "necessary_validity \<equiv> \<lambda> \<phi> . \<forall> v . (v \<Turnstile> \<phi>)"

(*<*)
end
(*>*)
