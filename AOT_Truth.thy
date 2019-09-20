theory AOT_Truth
  imports Main
begin

named_theorems AOT_meta
named_theorems AOT_meta_simp

typedecl \<o>
typedecl i

axiomatization
  dw :: i and
  AOT_valid_in :: "[i, \<o>] \<Rightarrow> bool" ("[_ \<Turnstile> _]") and
  AOT_proposition_choice :: "(i \<Rightarrow> bool) \<Rightarrow> \<o>" (binder "\<epsilon>\<^sub>\<o>" 4)
  where AOT_proposition_choice[AOT_meta, AOT_meta_simp]: "[v \<Turnstile> \<epsilon>\<^sub>\<o> w. \<phi> w] \<longleftrightarrow> \<phi> v"
    and AOT_nonactual_world[AOT_meta]: "\<exists> v . v \<noteq> dw"

consts AOT_false_choice :: "'a \<Rightarrow> \<o>" ("\<bottom>'(_')")
specification (AOT_false_choice)
  [AOT_meta, AOT_meta_simp]: "[v \<Turnstile> \<bottom>(x)] = False"
  by (rule_tac x="\<lambda>_. \<epsilon>\<^sub>\<o> v . False" in exI) (simp add: AOT_meta_simp)

consts AOT_not :: "\<o> \<Rightarrow> \<o>" ("\<^bold>\<not>_" [54] 70)
consts AOT_imp :: "[\<o>, \<o>] \<Rightarrow> \<o>" (infixl "\<^bold>\<rightarrow>" 51)
consts AOT_box :: "\<o> \<Rightarrow> \<o>" ("\<^bold>\<box>_" [62] 63)
consts AOT_act :: "\<o> \<Rightarrow> \<o>" ("\<^bold>\<A>_" [64] 65)

specification (AOT_not AOT_imp AOT_box AOT_act)
  AOT_notS[AOT_meta, AOT_meta_simp]: "[v \<Turnstile> \<^bold>\<not>\<phi>] = (\<not>[v \<Turnstile> \<phi>])"
  AOT_impS[AOT_meta, AOT_meta_simp]: "[v \<Turnstile> \<phi> \<^bold>\<rightarrow> \<psi>] = ([v \<Turnstile> \<phi>] \<longrightarrow> [v \<Turnstile> \<psi>])"
  AOT_boxS[AOT_meta, AOT_meta_simp]: "[v \<Turnstile> \<^bold>\<box>\<phi>] = (\<forall> v . [v \<Turnstile> \<phi>])"
  AOT_actS[AOT_meta, AOT_meta_simp]: "[v \<Turnstile> \<^bold>\<A>\<phi>] = [dw \<Turnstile> \<phi>]"
  by (
      rule_tac x="\<lambda> \<phi> . \<epsilon>\<^sub>\<o> v . \<not>[v \<Turnstile> \<phi>]" in exI;
      rule_tac x="\<lambda> \<phi> \<psi> . \<epsilon>\<^sub>\<o> v . [v \<Turnstile> \<phi>] \<longrightarrow> [v \<Turnstile> \<psi>]" in exI;
      rule_tac x="\<lambda> \<phi> . \<epsilon>\<^sub>\<o> v . \<forall> w . [w \<Turnstile> \<phi>]" in exI;
      rule_tac x="\<lambda> \<phi> . \<epsilon>\<^sub>\<o> v . [dw \<Turnstile> \<phi>]" in exI
     ) (simp add: AOT_meta_simp)

declare AOT_not_def[AOT_meta] AOT_imp_def[AOT_meta] AOT_box_def[AOT_meta] AOT_act_def[AOT_meta]


consts AOT_dia :: "\<o> \<Rightarrow> \<o>" ("\<^bold>\<diamond>_" [62] 63)
consts AOT_conj :: "[\<o>, \<o>] \<Rightarrow> \<o>" (infixl "\<^bold>&" 53)
consts AOT_disj :: "[\<o>, \<o>] \<Rightarrow> \<o>" (infixl "\<^bold>\<or>" 52)
consts AOT_iff :: "[\<o>, \<o>] \<Rightarrow> \<o>" (infixl "\<^bold>\<equiv>" 51)

specification (AOT_dia AOT_conj AOT_disj AOT_iff)
  AOT_diaS[AOT_meta, AOT_meta_simp]: "[v \<Turnstile> \<^bold>\<diamond>\<phi>] = [v \<Turnstile> \<^bold>\<not>\<^bold>\<box>\<^bold>\<not>\<phi>]"
  AOT_conjS[AOT_meta, AOT_meta_simp]: "[v \<Turnstile> \<phi> \<^bold>& \<psi>] = ([v \<Turnstile> \<phi>] \<and> [v \<Turnstile> \<psi>])"
  AOT_disjS[AOT_meta, AOT_meta_simp]: "[v \<Turnstile> \<phi> \<^bold>\<or> \<psi>] = ([v \<Turnstile> \<phi>] \<or> [v \<Turnstile> \<psi>])"
  AOT_iffS[AOT_meta, AOT_meta_simp]: "[v \<Turnstile> \<phi> \<^bold>\<equiv> \<psi>] = ([v \<Turnstile> \<phi>] \<longleftrightarrow> [v \<Turnstile> \<psi>])"
  by (
      rule_tac x="\<lambda> \<phi> . \<epsilon>\<^sub>\<o> v . [v \<Turnstile> \<^bold>\<not>\<^bold>\<box>\<^bold>\<not>\<phi>]" in exI;
      rule_tac x="\<lambda> \<phi> \<psi> . \<epsilon>\<^sub>\<o> v . [v \<Turnstile> \<phi>] \<and> [v \<Turnstile> \<psi>]" in exI;
      rule_tac x="\<lambda> \<phi> \<psi> . \<epsilon>\<^sub>\<o> v . [v \<Turnstile> \<phi>] \<or> [v \<Turnstile> \<psi>]" in exI;
      rule_tac x="\<lambda> \<phi> \<psi> . \<epsilon>\<^sub>\<o> v . [v \<Turnstile> \<phi>] \<longleftrightarrow> [v \<Turnstile> \<psi>]" in exI
    ) (simp add: AOT_meta_simp)
declare AOT_dia_def[AOT_meta] AOT_conj_def[AOT_meta] AOT_disj_def[AOT_meta] AOT_iff_def[AOT_meta]

(* There are models. *)
lemma "True"
   nitpick[user_axioms, satisfy, expect=genuine] oops
(* There are extensional models. *)
lemma "\<forall> p q . (\<forall> v . [v \<Turnstile> p] \<longleftrightarrow> [v \<Turnstile> q]) \<longleftrightarrow> (p = q)"
  nitpick[user_axioms, satisfy, expect=genuine] oops
(* There are intensional models. *)
lemma "\<exists> p q . (\<forall> v . [v \<Turnstile> p] \<longleftrightarrow> [v \<Turnstile> q]) \<and> (p \<noteq> q)"
  nitpick[user_axioms, satisfy, expect=genuine] oops
(* Counterexample for extensional commutativity of conjunction. *)
lemma "p \<^bold>& q = q \<^bold>& p"
  nitpick[user_axioms, expect=genuine] oops

end
