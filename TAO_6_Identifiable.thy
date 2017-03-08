(*<*)
theory TAO_6_Identifiable
imports TAO_5_Quantifiable
begin
(*>*)

section{* General Identity *}

text{*
\begin{remark}
  In order to define a general identity symbol that can act
  on all types of terms a type class is introduced
  which assumes the substitution property of equality which
  is needed to state the axioms later.
  This type class is then instantiated for all applicable types.
\end{remark}
*}

subsection{* Type Classes *}

class identifiable =
fixes identity :: "'a\<Rightarrow>'a\<Rightarrow>\<o>" (infixl "\<^bold>=" 63)
assumes l_identity:
  "w \<Turnstile> x \<^bold>= y \<Longrightarrow> w \<Turnstile> \<phi> x \<Longrightarrow> w \<Turnstile> \<phi> y"
assumes meta_identity:
  "w \<Turnstile> x \<^bold>= y \<Longrightarrow> x = y"
begin
  abbreviation notequal (infixl "\<^bold>\<noteq>" 63) where
    "notequal \<equiv> \<lambda> x y . \<^bold>\<not>(x \<^bold>= y)"
end

class quantifiable_and_identifiable = quantifiable + identifiable
begin
  definition exists_unique::"('a\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<exists>!" [8] 9) where
    "exists_unique \<equiv> \<lambda> \<phi> . \<^bold>\<exists> \<alpha> . \<phi> \<alpha> \<^bold>& (\<^bold>\<forall>\<beta>. \<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>)"
  
  declare exists_unique_def[conn_defs]
end

subsection{* Instantiations *}

instantiation \<kappa> :: identifiable
begin
  definition identity_\<kappa> where "identity_\<kappa> \<equiv> basic_identity\<^sub>\<kappa>"
  instance proof
    fix x y :: \<kappa> and w \<phi>
    show "[x \<^bold>= y in w] \<Longrightarrow> [\<phi> x in w] \<Longrightarrow> [\<phi> y in w]"
      unfolding identity_\<kappa>_def
      using MetaSolver.Eq\<kappa>_prop ..
  next
    interpret MetaSolver .
    fix w :: i and x y :: \<kappa>
      show "[x \<^bold>= y in w] \<Longrightarrow> x = y" using Eq\<kappa>_prop
            unfolding identity_\<kappa>_def
            using MetaSolver.Eq\<kappa>E Semantics.d\<^sub>\<kappa>_inject by blast
  qed
end

instantiation \<Pi>\<^sub>1 :: identifiable
begin
  definition identity_\<Pi>\<^sub>1 where "identity_\<Pi>\<^sub>1 \<equiv> basic_identity\<^sub>1"
  instance proof
    fix F G :: \<Pi>\<^sub>1 and w \<phi>
    show "(w \<Turnstile> F \<^bold>= G) \<Longrightarrow> (w \<Turnstile> \<phi> F) \<Longrightarrow> (w \<Turnstile> \<phi> G)"
      unfolding identity_\<Pi>\<^sub>1_def using MetaSolver.Eq\<^sub>1_prop ..
  next
    interpret MetaSolver .
    fix w :: i and x y :: \<Pi>\<^sub>1
      show "[x \<^bold>= y in w] \<Longrightarrow> x = y" using Eq\<kappa>_prop
            unfolding identity_\<Pi>\<^sub>1_def
            using MetaSolver.Eq\<^sub>1E Semantics.d\<^sub>\<kappa>_inject by blast
  qed
end

instantiation \<Pi>\<^sub>2 :: identifiable
begin
  definition identity_\<Pi>\<^sub>2 where "identity_\<Pi>\<^sub>2 \<equiv> basic_identity\<^sub>2"
  instance proof
    fix F G :: \<Pi>\<^sub>2 and w \<phi>
    show "(w \<Turnstile> F \<^bold>= G) \<Longrightarrow> (w \<Turnstile> \<phi> F) \<Longrightarrow> (w \<Turnstile> \<phi> G)"
      unfolding identity_\<Pi>\<^sub>2_def using MetaSolver.Eq\<^sub>2_prop ..
  next
    interpret MetaSolver .
    fix w :: i and x y :: \<Pi>\<^sub>2
      show "[x \<^bold>= y in w] \<Longrightarrow> x = y" using Eq\<kappa>_prop
            unfolding identity_\<Pi>\<^sub>2_def
            using MetaSolver.Eq\<^sub>2E Semantics.d\<^sub>\<kappa>_inject by blast
  qed
end

instantiation \<Pi>\<^sub>3 :: identifiable
begin
  definition identity_\<Pi>\<^sub>3 where "identity_\<Pi>\<^sub>3 \<equiv> basic_identity\<^sub>3"
  instance proof
    fix F G :: \<Pi>\<^sub>3 and w \<phi>
    show "(w \<Turnstile> F \<^bold>= G) \<Longrightarrow> (w \<Turnstile> \<phi> F) \<Longrightarrow> (w \<Turnstile> \<phi> G)"
      unfolding identity_\<Pi>\<^sub>3_def using MetaSolver.Eq\<^sub>3_prop ..
  next
    interpret MetaSolver .
    fix w :: i and x y :: \<Pi>\<^sub>3
      show "[x \<^bold>= y in w] \<Longrightarrow> x = y" using Eq\<kappa>_prop
            unfolding identity_\<Pi>\<^sub>3_def
            using MetaSolver.Eq\<^sub>3E Semantics.d\<^sub>\<kappa>_inject by blast
  qed
end

instantiation \<o> :: identifiable
begin
  definition identity_\<o> where "identity_\<o> \<equiv> basic_identity\<^sub>\<o>"
  instance proof
    fix F G :: \<o> and w \<phi>
    show "(w \<Turnstile> F \<^bold>= G) \<Longrightarrow> (w \<Turnstile> \<phi> F) \<Longrightarrow> (w \<Turnstile> \<phi> G)"
      unfolding identity_\<o>_def using MetaSolver.Eq\<^sub>\<o>_prop ..
  next
    interpret MetaSolver .
    fix w :: i and x y :: \<o>
      show "[x \<^bold>= y in w] \<Longrightarrow> x = y" using Eq\<^sub>\<o>_prop
            unfolding identity_\<o>_def
            using MetaSolver.Eq\<^sub>\<o>E Semantics.d\<^sub>\<kappa>_inject by blast
  qed
end

instance \<kappa> :: quantifiable_and_identifiable ..
instance \<Pi>\<^sub>1 :: quantifiable_and_identifiable ..
instance \<Pi>\<^sub>2 :: quantifiable_and_identifiable ..
instance \<Pi>\<^sub>3 :: quantifiable_and_identifiable ..
instance \<o> :: quantifiable_and_identifiable ..

subsection{* New Identity Definitions *}

text{*
\begin{remark}
  The basic definitions of identity used the type specific quantifiers
  and identities. We now introduce equivalent alternative definitions that
  use the general identity and general quantifiers.
\end{remark}
*}

named_theorems identity_defs
lemma identity\<^sub>E_def[identity_defs]:
  "basic_identity\<^sub>E \<equiv> \<^bold>\<lambda>\<^sup>2 (\<lambda>x y. \<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F. \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>))"
  unfolding basic_identity\<^sub>E_def forall_\<Pi>\<^sub>1_def by simp
lemma identity\<^sub>E_infix_def[identity_defs]:
  "x \<^bold>=\<^sub>E y \<equiv> \<lparr>basic_identity\<^sub>E,x,y\<rparr>" using basic_identity\<^sub>E_infix_def .
lemma identity\<^sub>\<kappa>_def[identity_defs]:
  "op \<^bold>= \<equiv> \<lambda>x y. x \<^bold>=\<^sub>E y \<^bold>\<or> \<lparr>A!,x\<rparr> \<^bold>& \<lparr>A!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F. \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>y,F\<rbrace>)"
  unfolding identity_\<kappa>_def basic_identity\<^sub>\<kappa>_def forall_\<Pi>\<^sub>1_def by simp
lemma identity\<^sub>1_def[identity_defs]:
  "op \<^bold>= \<equiv> \<lambda>F G. \<^bold>\<box>(\<^bold>\<forall> x . \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>x,G\<rbrace>)"
  unfolding identity_\<Pi>\<^sub>1_def basic_identity\<^sub>1_def forall_\<kappa>_def by simp
lemma identity\<^sub>2_def[identity_defs]:
  "op \<^bold>= \<equiv> \<lambda>F G. \<^bold>\<forall> x. (\<^bold>\<lambda>y. \<lparr>F,x,y\<rparr>) \<^bold>= (\<^bold>\<lambda>y. \<lparr>G,x,y\<rparr>)
                    \<^bold>& (\<^bold>\<lambda>y. \<lparr>F,y,x\<rparr>) \<^bold>= (\<^bold>\<lambda>y. \<lparr>G,y,x\<rparr>)"
  unfolding identity_\<Pi>\<^sub>2_def identity_\<Pi>\<^sub>1_def basic_identity\<^sub>2_def forall_\<kappa>_def by simp
lemma identity\<^sub>3_def[identity_defs]:
  "op \<^bold>= \<equiv> \<lambda>F G. \<^bold>\<forall> x y. (\<^bold>\<lambda>z. \<lparr>F,z,x,y\<rparr>) \<^bold>= (\<^bold>\<lambda>z. \<lparr>G,z,x,y\<rparr>)
                      \<^bold>& (\<^bold>\<lambda>z. \<lparr>F,x,z,y\<rparr>) \<^bold>= (\<^bold>\<lambda>z. \<lparr>G,x,z,y\<rparr>)
                      \<^bold>& (\<^bold>\<lambda>z. \<lparr>F,x,y,z\<rparr>) \<^bold>= (\<^bold>\<lambda>z. \<lparr>G,x,y,z\<rparr>)"
  unfolding identity_\<Pi>\<^sub>3_def identity_\<Pi>\<^sub>1_def basic_identity\<^sub>3_def forall_\<kappa>_def by simp
lemma identity\<^sub>\<o>_def[identity_defs]: "op \<^bold>= \<equiv> \<lambda>F G. (\<^bold>\<lambda>y. F) \<^bold>= (\<^bold>\<lambda>y. G)"
  unfolding identity_\<o>_def identity_\<Pi>\<^sub>1_def basic_identity\<^sub>\<o>_def by simp

(*<*)
end
(*>*)
