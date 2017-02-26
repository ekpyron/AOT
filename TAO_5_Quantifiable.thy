theory TAO_5_Quantifiable
imports TAO_4_MetaSolver
begin

section{* General Quantification *}

text{* In order to define general quantifiers that can act
        on all variable types a type class is introduced
        which assumes the semantics of the all quantifier.
        This type class is then instantiated for all variable
        types. *}

subsection{* Type Class *}

text{* datatype for types for which quantification is defined *}
datatype var = \<nu>var (var\<nu>: \<nu>) | \<o>var (var\<o>: \<o>) | \<Pi>\<^sub>1var (var\<Pi>\<^sub>1: \<Pi>\<^sub>1)
             | \<Pi>\<^sub>2var (var\<Pi>\<^sub>2: \<Pi>\<^sub>2) | \<Pi>\<^sub>3var (var\<Pi>\<^sub>3: \<Pi>\<^sub>3)

text{* type class for quantifiable types *}
class quantifiable = fixes forall :: "('a\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>" [8] 9)
                       and qvar :: "'a\<Rightarrow>var"
                       and varq :: "var\<Rightarrow>'a"
  assumes quantifiable_T8: "\<And>w \<psi> . (w \<Turnstile> (\<^bold>\<forall> x . \<psi> x)) = (\<forall> x . (w \<Turnstile> (\<psi> x)))"
      and varq_qvar_id: "\<And>x. varq (qvar x) = x"
begin
  definition exists :: "('a\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<exists>" [8] 9) where
    "exists \<equiv> \<lambda> \<phi> . \<^bold>\<not>(\<^bold>\<forall> x . \<^bold>\<not>\<phi> x)"
  declare exists_def[conn_defs]
end

text{* semantics for general quantifier *}
lemma (in Semantics) T8: shows "(w \<Turnstile> \<^bold>\<forall> x . \<psi> x) = (\<forall> x . (w \<Turnstile> \<psi> x))"
  using quantifiable_T8 .

subsection{* Instantiations *}

instantiation \<nu> :: quantifiable
begin
  definition forall_\<nu> :: "(\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<nu> \<equiv> forall\<^sub>\<nu>"
  definition qvar_\<nu> :: "\<nu>\<Rightarrow>var" where "qvar \<equiv> \<nu>var"
  definition varq_\<nu> :: "var\<Rightarrow>\<nu>" where "varq \<equiv> var\<nu>"
  instance proof
    fix w :: i and \<psi> :: "\<nu>\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. (w \<Turnstile> \<psi> x))"
      unfolding forall_\<nu>_def using Semantics.T8_\<nu> .
  next
    fix x :: \<nu>
    show "varq (qvar x) = x"
      unfolding qvar_\<nu>_def varq_\<nu>_def by simp
  qed
end

instantiation \<o> :: quantifiable
begin
  definition forall_\<o> :: "(\<o>\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<o> \<equiv> forall\<^sub>\<o>"
  definition qvar_\<o> :: "\<o>\<Rightarrow>var" where "qvar \<equiv> \<o>var"
  definition varq_\<o> :: "var\<Rightarrow>\<o>" where "varq \<equiv> var\<o>"
  instance proof
    fix w :: i and \<psi> :: "\<o>\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. (w \<Turnstile> \<psi> x))"
      unfolding forall_\<o>_def using Semantics.T8_\<o> .
  next
    fix x :: \<o>
    show "varq (qvar x) = x"
      unfolding qvar_\<o>_def varq_\<o>_def by simp
  qed
end

instantiation \<Pi>\<^sub>1 :: quantifiable
begin
  definition forall_\<Pi>\<^sub>1 :: "(\<Pi>\<^sub>1\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<Pi>\<^sub>1 \<equiv> forall\<^sub>1"
  definition qvar_\<Pi>\<^sub>1 :: "\<Pi>\<^sub>1\<Rightarrow>var" where "qvar \<equiv> \<Pi>\<^sub>1var"
  definition varq_\<Pi>\<^sub>1 :: "var\<Rightarrow>\<Pi>\<^sub>1" where "varq \<equiv> var\<Pi>\<^sub>1"
  instance proof
    fix w :: i and \<psi> :: "\<Pi>\<^sub>1\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. (w \<Turnstile> \<psi> x))"
      unfolding forall_\<Pi>\<^sub>1_def using Semantics.T8_1 .
  next
    fix x :: \<Pi>\<^sub>1
    show "varq (qvar x) = x"
      unfolding qvar_\<Pi>\<^sub>1_def varq_\<Pi>\<^sub>1_def by simp
  qed
end

instantiation \<Pi>\<^sub>2 :: quantifiable
begin
  definition forall_\<Pi>\<^sub>2 :: "(\<Pi>\<^sub>2\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<Pi>\<^sub>2 \<equiv> forall\<^sub>2"
  definition qvar_\<Pi>\<^sub>2 :: "\<Pi>\<^sub>2\<Rightarrow>var" where "qvar \<equiv> \<Pi>\<^sub>2var"
  definition varq_\<Pi>\<^sub>2 :: "var\<Rightarrow>\<Pi>\<^sub>2" where "varq \<equiv> var\<Pi>\<^sub>2"
  instance proof
    fix w :: i and \<psi> :: "\<Pi>\<^sub>2\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. (w \<Turnstile> \<psi> x))"
      unfolding forall_\<Pi>\<^sub>2_def using Semantics.T8_2 .
  next
    fix x :: \<Pi>\<^sub>2
    show "varq (qvar x) = x"
      unfolding qvar_\<Pi>\<^sub>2_def varq_\<Pi>\<^sub>2_def by simp
  qed
end

instantiation \<Pi>\<^sub>3 :: quantifiable
begin
  definition forall_\<Pi>\<^sub>3 :: "(\<Pi>\<^sub>3\<Rightarrow>\<o>)\<Rightarrow>\<o>" where "forall_\<Pi>\<^sub>3 \<equiv> forall\<^sub>3"
  definition qvar_\<Pi>\<^sub>3 :: "\<Pi>\<^sub>3\<Rightarrow>var" where "qvar \<equiv> \<Pi>\<^sub>3var"
  definition varq_\<Pi>\<^sub>3 :: "var\<Rightarrow>\<Pi>\<^sub>3" where "varq \<equiv> var\<Pi>\<^sub>3"
  instance proof
    fix w :: i and \<psi> :: "\<Pi>\<^sub>3\<Rightarrow>\<o>"
    show "(w \<Turnstile> \<^bold>\<forall>x. \<psi> x) = (\<forall>x. (w \<Turnstile> \<psi> x))"
      unfolding forall_\<Pi>\<^sub>3_def using Semantics.T8_3 .
  next
    fix x :: \<Pi>\<^sub>3
    show "varq (qvar x) = x"
      unfolding qvar_\<Pi>\<^sub>3_def varq_\<Pi>\<^sub>3_def by simp
  qed
end

subsection{* MetaSolver Rules *}

text{* The @{text "meta_solver"} is extended by rules for
       general quantification. *}

context MetaSolver
begin
  text{* Rules for general all quantification. *}
  lemma AllI[meta_intro]: "(\<And>x::'a::quantifiable. [\<phi> x in v]) \<Longrightarrow> [\<^bold>\<forall> x. \<phi> x in v]"
    by (auto simp: Semantics.T8)
  lemma AllE[meta_elim]: "[\<^bold>\<forall>x. \<phi> x in v] \<Longrightarrow> (\<And>x::'a::quantifiable.[\<phi> x in v])"
    by (auto simp: Semantics.T8)
  lemma AllS[meta_subst]: "[\<^bold>\<forall>x. \<phi> x in v] = (\<forall>x::'a::quantifiable.[\<phi> x in v])"
    by (auto simp: Semantics.T8)

  text{* Rules for existence. *}
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

end
