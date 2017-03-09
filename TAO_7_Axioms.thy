(*<*)
theory TAO_7_Axioms
imports TAO_6_Identifiable
begin
(*>*)

section{* The Axioms of Principia Metaphysica *}

text{*
\begin{remark}
  The axioms of PM can now be derived from the Semantics
  and the meta-logic.
\end{remark}
*}

(* TODO: why is this needed again here? The syntax should already
         have been disabled in TAO_Semantics. *)
(* disable list syntax [] to replace it with truth evaluation *)
(*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
(*<*) no_syntax "__listcompr" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 

class AlwaysDenoting = quantifiable_and_identifiable +
  assumes cqt_2: "[\<^bold>\<exists> \<beta> . \<beta> \<^bold>= \<tau> in v]"

instantiation \<Pi>\<^sub>1 :: AlwaysDenoting
begin
  instance proof
    interpret MetaSolver .
    fix v :: i and \<tau> :: \<Pi>\<^sub>1
    show "[\<^bold>\<exists> \<beta> . \<beta> \<^bold>= \<tau> in v]"
      unfolding identity_\<Pi>\<^sub>1_def 
      by (metis Eq\<^sub>1S MetaSolver.All\<^sub>1E MetaSolver.NotS exists_def forall_\<Pi>\<^sub>1_def)
  qed
end

instantiation \<Pi>\<^sub>2 :: AlwaysDenoting
begin
  instance proof
    interpret MetaSolver .
    fix v :: i and \<tau> :: \<Pi>\<^sub>2
    show "[\<^bold>\<exists> \<beta> . \<beta> \<^bold>= \<tau> in v]"
      unfolding identity_\<Pi>\<^sub>2_def 
      by (metis Eq\<^sub>2S MetaSolver.All\<^sub>2E MetaSolver.NotS exists_def forall_\<Pi>\<^sub>2_def)
  qed
end

instantiation \<Pi>\<^sub>3 :: AlwaysDenoting
begin
  instance proof
    interpret MetaSolver .
    fix v :: i and \<tau> :: \<Pi>\<^sub>3
    show "[\<^bold>\<exists> \<beta> . \<beta> \<^bold>= \<tau> in v]"
      unfolding identity_\<Pi>\<^sub>3_def 
      by (metis Eq\<^sub>3S MetaSolver.All\<^sub>3E MetaSolver.NotS exists_def forall_\<Pi>\<^sub>3_def)
  qed
end

instantiation \<o> :: AlwaysDenoting
begin
  instance proof
    interpret MetaSolver .
    fix v :: i and \<tau> :: \<o>
    show "[\<^bold>\<exists> \<beta> . \<beta> \<^bold>= \<tau> in v]"
      unfolding identity_\<o>_def 
      using Eq\<^sub>\<o>S MetaSolver.All\<^sub>0E MetaSolver.NotS exists_def forall_\<o>_def
      by (metis Semantics.T8_\<o>)
  qed
end

locale Axioms
begin
  interpretation MetaSolver .
  interpretation Semantics .
  named_theorems axiom

subsection{* Closures *}

text{*
\begin{remark}
  The special syntax @{text "[[_]]"} is introduced for axioms. This allows to formulate
  special rules resembling the concepts of closures in PM. To simplify the instantiation
  of axioms later, special attributes are introduced to automatically resolve the
  special axiom syntax.
  Necessitation averse axioms are stated with the syntax for actual validity @{text "[_]"}.
\end{remark}
*}

  definition axiom :: "\<o>\<Rightarrow>bool" ("[[_]]") where "axiom \<equiv> \<lambda> \<phi> . \<forall> v . [\<phi> in v]"

  method axiom_meta_solver = ((unfold axiom_def)?, rule allI, meta_solver,
                              (simp | (auto; fail))?)

  lemma axiom_instance[axiom]: "[[\<phi>]] \<Longrightarrow> [\<phi> in v]"
    unfolding axiom_def by simp
  lemma closures_universal[axiom]: "(\<And>x.[[\<phi> x]]) \<Longrightarrow> [[\<^bold>\<forall> x. \<phi> x]]"
    by axiom_meta_solver
  lemma closures_actualization[axiom]: "[[\<phi>]] \<Longrightarrow> [[\<^bold>\<A> \<phi>]]"
    by axiom_meta_solver
  lemma closures_necessitation[axiom]: "[[\<phi>]] \<Longrightarrow> [[\<^bold>\<box> \<phi>]]"
    by axiom_meta_solver
  lemma necessitation_averse_axiom_instance[axiom]: "[\<phi>] \<Longrightarrow> [\<phi> in dw]"
    by meta_solver
  lemma necessitation_averse_closures_universal[axiom]: "(\<And>x.[\<phi> x]) \<Longrightarrow> [\<^bold>\<forall> x. \<phi> x]"
    by meta_solver

  attribute_setup axiom_instance = {*
    Scan.succeed (Thm.rule_attribute [] 
      (fn _ => fn thm => thm RS @{thm axiom_instance}))
  *}

  attribute_setup necessitation_averse_axiom_instance = {*
    Scan.succeed (Thm.rule_attribute [] 
      (fn _ => fn thm => thm RS @{thm necessitation_averse_axiom_instance}))
  *}

  attribute_setup axiom_necessitation = {*
    Scan.succeed (Thm.rule_attribute [] 
      (fn _ => fn thm => thm RS @{thm closures_necessitation}))
  *}

  attribute_setup axiom_actualization = {*
    Scan.succeed (Thm.rule_attribute [] 
      (fn _ => fn thm => thm RS @{thm closures_actualization}))
  *}

  attribute_setup axiom_universal = {*
    Scan.succeed (Thm.rule_attribute [] 
      (fn _ => fn thm => thm RS @{thm closures_universal}))
  *}

subsection{* Axioms for Negations and Conditionals *}

  lemma pl_1[axiom]:
    "[[\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<phi>)]]"
    by axiom_meta_solver
  lemma pl_2[axiom]:
    "[[(\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<chi>)) \<^bold>\<rightarrow> ((\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<chi>))]]"
    by axiom_meta_solver
  lemma pl_3[axiom]:
    "[[(\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi>) \<^bold>\<rightarrow> ((\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> \<phi>)]]"
    by axiom_meta_solver

subsection{* Axioms of Identity *}

  lemma l_identity[axiom]:
    "[[\<alpha> \<^bold>= \<beta> \<^bold>\<rightarrow> (\<phi> \<alpha> \<^bold>\<rightarrow> \<phi> \<beta>)]]"
    using l_identity apply cut_tac by axiom_meta_solver

subsection{* Axioms of Quantification *}

text{*
\begin{remark}
  The axioms of quantification differ slightly from the axioms in Principia Metaphysica.
  The differences can be justified, though.
  \begin{itemize}
    \item  
      Axiom @{text "cqt_2"} is omitted, as the embedding does not distinguish between terms
      and variables. Instead it is combined with @{text "cqt_1"}, in which the corresponding
      condition is omitted, and with @{text "cqt_5"} in its modified form @{text "cqt_5_mod"}.
    \item
      Note that the all quantifier for individuals only ranges over the datatype @{text "\<nu>"},
      which is always a denoting term and not a definite description in the embedding.
    \item
      The case of definite descriptions is handled separately in axiom @{text "cqt_1_\<kappa>"}:
      If a formula on datatype @{text "\<kappa>"} holds for all denoting terms (@{text "\<^bold>\<forall> \<alpha>. \<phi> (\<alpha>\<^sup>P)"})
      then the formula holds for an individual @{text "\<phi> \<alpha>"}, if @{text "\<alpha>"} denotes, i.e.
      @{text "\<^bold>\<exists> \<beta> . (\<beta>\<^sup>P) \<^bold>= \<alpha>"}.
    \item
      Although axiom @{text "cqt_5"} can be stated without modification, it is not a suitable
      formulation for the embedding. Therefore the seemingly stronger version @{text "cqt_5_mod"}
      is stated as well. On a closer look, though, @{text "cqt_5_mod"} immediately follows from
      the original @{text "cqt_5"} together with the omitted @{text "cqt_2"}.
  \end{itemize}
\end{remark}
*}

  lemma cqt_1[axiom]:
    "[[(\<^bold>\<forall> \<alpha> . \<phi> \<alpha>) \<^bold>\<rightarrow> ((\<^bold>\<exists> \<beta> . \<beta> \<^bold>= \<alpha>) \<^bold>\<rightarrow> \<phi> \<alpha>)]]"
    apply axiom_meta_solver apply auto using meta_identity by blast
  lemma cqt_2[axiom]:
    "[[(\<^bold>\<exists> \<beta> :: 'a::AlwaysDenoting. \<beta> \<^bold>= \<alpha>)]]"
      unfolding axiom_def using cqt_2 by blast
  lemma cqt_3[axiom]:
    "[[(\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<rightarrow> \<psi> \<alpha>) \<^bold>\<rightarrow> ((\<^bold>\<forall>\<alpha>. \<phi> \<alpha>) \<^bold>\<rightarrow> (\<^bold>\<forall>\<alpha>. \<psi> \<alpha>))]]" unfolding axiom_def
    using AllS ImplS by metis
  lemma cqt_4[axiom]:
    "[[\<phi> \<^bold>\<rightarrow> (\<^bold>\<forall>\<alpha>. \<phi>)]]"
    by axiom_meta_solver

  inductive SimpleExOrEnc
    where "SimpleExOrEnc (\<lambda> x . \<lparr>F,x\<rparr>)"
        | "SimpleExOrEnc (\<lambda> x . \<lparr>F,x,y\<rparr>)"
        | "SimpleExOrEnc (\<lambda> x . \<lparr>F,y,x\<rparr>)"
        | "SimpleExOrEnc (\<lambda> x . \<lparr>F,x,y,z\<rparr>)"
        | "SimpleExOrEnc (\<lambda> x . \<lparr>F,y,x,z\<rparr>)"
        | "SimpleExOrEnc (\<lambda> x . \<lparr>F,y,z,x\<rparr>)"
        | "SimpleExOrEnc (\<lambda> x . \<lbrace>x,F\<rbrace>)"

  lemma cqt_5[axiom]:
    assumes "SimpleExOrEnc \<psi>"
    shows "[[(\<psi> (\<^bold>\<iota>x . \<phi> x)) \<^bold>\<rightarrow> (\<^bold>\<exists> \<alpha>. \<alpha> \<^bold>= (\<^bold>\<iota>x . \<phi> x))]]"
    proof -
      have "\<forall> w . ([(\<psi> (\<^bold>\<iota>x . \<phi> x)) in w] \<longrightarrow> (\<exists> o\<^sub>1 . Some o\<^sub>1 = d\<^sub>\<kappa> (\<^bold>\<iota>x . \<phi> x)))"
        using assms apply induct by (meta_solver;metis)+
      moreover hence
        "\<forall> w . ([(\<psi> (\<^bold>\<iota>x . \<phi> x)) in w] \<longrightarrow> (that \<phi>) = (make\<kappa> (Some (denotation (that \<phi>)))))"
        apply transfer apply simp by force
     ultimately show ?thesis
      apply cut_tac unfolding identity_\<kappa>_def
      apply axiom_meta_solver
      by (metis domain_\<kappa>_def mem_Collect_eq proper_denotes)
    qed

  lemma cqt_5_mod[axiom]:
    assumes "SimpleExOrEnc \<psi>"
    shows "[[\<psi> x \<^bold>\<rightarrow> (\<^bold>\<exists>  \<alpha> . \<alpha> \<^bold>= x)]]"
    proof -
      have "\<forall> w . ([(\<psi> x) in w] \<longrightarrow> (\<exists> o\<^sub>1 . Some o\<^sub>1 = d\<^sub>\<kappa> x))"
        using assms apply induct by (meta_solver;metis)+
      moreover hence "\<forall> w . ([(\<psi> x) in w] \<longrightarrow> (x) = (make\<kappa> (Some (denotation (x)))))"
        apply transfer apply simp by force
      ultimately show ?thesis
        apply cut_tac unfolding identity_\<kappa>_def
        apply axiom_meta_solver
        by (metis domain_\<kappa>_def mem_Collect_eq proper_denotes)
    qed

subsection{* Axioms of Actuality *}

text{*
\begin{remark}
  The necessitation averse axiom of actuality is stated to be actually true;
  for the statement as a proper axiom (for which necessitation would be allowed)
  nitpick can find a counter-model as desired.
\end{remark}
*}

  lemma logic_actual[axiom]: "[(\<^bold>\<A>\<phi>) \<^bold>\<equiv> \<phi>]"
    apply meta_solver by auto
  lemma "[[(\<^bold>\<A>\<phi>) \<^bold>\<equiv> \<phi>]]"
    nitpick[user_axioms, expect = genuine, card = 1, card i = 2]
    oops --{* Counter-model by nitpick *}

  lemma logic_actual_nec_1[axiom]:
    "[[\<^bold>\<A>\<^bold>\<not>\<phi> \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<A>\<phi>]]"
    by axiom_meta_solver
  lemma logic_actual_nec_2[axiom]:
    "[[(\<^bold>\<A>(\<phi> \<^bold>\<rightarrow> \<psi>)) \<^bold>\<equiv> (\<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<^bold>\<A>\<psi>)]]"
    by axiom_meta_solver
  lemma logic_actual_nec_3[axiom]:
    "[[\<^bold>\<A>(\<^bold>\<forall>\<alpha>. \<phi> \<alpha>) \<^bold>\<equiv> (\<^bold>\<forall>\<alpha>. \<^bold>\<A>(\<phi> \<alpha>))]]"
    by axiom_meta_solver
  lemma logic_actual_nec_4[axiom]:
    "[[\<^bold>\<A>\<phi> \<^bold>\<equiv> \<^bold>\<A>\<^bold>\<A>\<phi>]]"
    by axiom_meta_solver

subsection{* Axioms of Necessity *}

  lemma qml_1[axiom]:
    "[[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>)]]"
    by axiom_meta_solver
  lemma qml_2[axiom]:
    "[[\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>]]"
    by axiom_meta_solver
  lemma qml_3[axiom]:
    "[[\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>]]"
    by axiom_meta_solver
  lemma qml_4[axiom]:
    "[[\<^bold>\<diamond>(\<^bold>\<exists>x. \<lparr>E!,x\<rparr> \<^bold>& \<^bold>\<diamond>\<^bold>\<not>\<lparr>E!,x\<rparr>) \<^bold>& \<^bold>\<diamond>\<^bold>\<not>(\<^bold>\<exists>x. \<lparr>E!,x\<rparr> \<^bold>& \<^bold>\<diamond>\<^bold>\<not>\<lparr>E!,x\<rparr>)]]"
     unfolding axiom_def
     using PossiblyContingentObjectExistsAxiom
           PossiblyNoContingentObjectExistsAxiom
     apply (simp add: meta_defs meta_aux conn_defs forall_\<kappa>_def
                 split: \<nu>.split \<upsilon>.split)
     by (metis \<nu>\<upsilon>_\<omega>\<nu>_is_\<omega>\<upsilon> \<upsilon>.distinct(1) \<upsilon>.inject(1) proper_denotation proper_denotes)

subsection{* Axioms of Necessity and Actuality *}
  lemma qml_act_1[axiom]:
    "[[\<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<A>\<phi>]]"
    by axiom_meta_solver
  lemma qml_act_2[axiom]:
    "[[\<^bold>\<box>\<phi> \<^bold>\<equiv> \<^bold>\<A>(\<^bold>\<box>\<phi>)]]"
    by axiom_meta_solver

subsection{* Axioms of Descriptions *}
  lemma descriptions[axiom]:
    "[[(x\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> x) \<^bold>\<equiv> (\<^bold>\<forall>z.(\<^bold>\<A>(\<phi> z) \<^bold>\<equiv> z \<^bold>= (x\<^sup>P)))]]"
    unfolding axiom_def
    proof (rule allI, rule EquivI; rule)
      fix v
      assume "[(x\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> x) in v]"
      moreover hence 1:
        "\<exists>o\<^sub>1 o\<^sub>2. Some o\<^sub>1 = d\<^sub>\<kappa> (x\<^sup>P) \<and> Some o\<^sub>2 = d\<^sub>\<kappa> (\<^bold>\<iota>x. \<phi> x) \<and> o\<^sub>1 = o\<^sub>2"
        apply cut_tac unfolding identity_\<kappa>_def by meta_solver
      then obtain o\<^sub>1 o\<^sub>2 where 2:
        "Some o\<^sub>1 = d\<^sub>\<kappa> (x\<^sup>P) \<and> Some o\<^sub>2 = d\<^sub>\<kappa> (\<^bold>\<iota>x. \<phi> x) \<and> o\<^sub>1 = o\<^sub>2"
        by auto
      have "\<forall> z . denotes z \<longrightarrow> [\<^bold>\<A>\<phi> z in v] = [z \<^bold>= (x\<^sup>P) in v]"
      proof
        fix z
        have "denotes z \<Longrightarrow> [\<^bold>\<A>\<phi> z in v] \<Longrightarrow> [z \<^bold>= (x\<^sup>P) in v]"
          unfolding identity_\<kappa>_def apply meta_solver
          unfolding d\<^sub>\<kappa>_def using 2 apply transfer
          apply simp
          by (metis (no_types, lifting) option.distinct(1) the1_equality)
        moreover have "[z \<^bold>= (x\<^sup>P) in v] \<Longrightarrow> [\<^bold>\<A>\<phi> z in v]"
          unfolding identity_\<kappa>_def apply meta_solver
          using 2 apply transfer apply simp
          by (metis (no_types, lifting) option.distinct(1) the1_equality)
        ultimately show "denotes z \<longrightarrow> [\<^bold>\<A>\<phi> z in v] = [z \<^bold>= (x\<^sup>P) in v]"
          by auto
      qed
      thus "[\<^bold>\<forall>z. \<^bold>\<A>\<phi> z \<^bold>\<equiv> z \<^bold>= (x\<^sup>P) in v]"
        unfolding identity_\<kappa>_def
        by (simp add: MetaSolver.EquivS domain_\<kappa>_def quantifiable_T8)
    next
      fix v
      assume "[\<^bold>\<forall>z. \<^bold>\<A>\<phi> z \<^bold>\<equiv> (z) \<^bold>= (x\<^sup>P) in v]"
      hence 1: "\<And>z. denotes z \<longrightarrow> ((dw \<Turnstile> \<phi> z) = (\<exists>o\<^sub>1 o\<^sub>2. Some o\<^sub>1 = d\<^sub>\<kappa> (z)
                \<and> Some o\<^sub>2 = d\<^sub>\<kappa> (x\<^sup>P) \<and> o\<^sub>1 = o\<^sub>2))"
        proof -
          fix z
          assume "[\<^bold>\<forall>z. \<^bold>\<A>\<phi> z \<^bold>\<equiv> z \<^bold>= (x\<^sup>P) in v]"
          hence "denotes z \<longrightarrow> [\<^bold>\<A>\<phi> z \<^bold>\<equiv> z \<^bold>= (x\<^sup>P) in v]" by (simp add: MetaSolver.All\<^sub>\<kappa>S forall_\<kappa>_def)
          thus "denotes z \<longrightarrow> ([\<phi> z in dw] = (\<exists>o\<^sub>1 o\<^sub>2. Some o\<^sub>1 = d\<^sub>\<kappa> z \<and> Some o\<^sub>2 = d\<^sub>\<kappa> (x\<^sup>P) \<and> o\<^sub>1 = o\<^sub>2))"
          using MetaSolver.Eq\<kappa>S MetaSolver.EquivE Semantics.T7 identity_\<kappa>_def by fastforce
        qed
      hence 2: "\<forall> z . denotes z \<longrightarrow> eval\<o> (\<phi> z) dj dw = (z = (x\<^sup>P))" apply transfer by auto 
      hence "((x\<^sup>P) = (\<^bold>\<iota>x. \<phi> x))" apply transfer by auto
      thus "[(x\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> x) in v]"  unfolding identity_\<kappa>_def 
      using 1 MetaSolver.Eq\<kappa>S 2 valid_in.rep_eq by (metis Semantics.D3 proper.rep_eq)
    qed

subsection{* Axioms for Complex Relation Terms *}

  lemma lambda_predicates_1[axiom]:
    "(\<^bold>\<lambda> x . \<phi> x) = (\<^bold>\<lambda> y . \<phi> y)" ..

  lemma lambda_predicates_2_1[axiom]:
    assumes "IsPropositionalInX \<phi>"
    shows "[[\<lparr>\<^bold>\<lambda> x . \<phi> x, x\<^sup>P\<rparr> \<^bold>\<equiv> \<phi> (x\<^sup>P)]]"
    apply axiom_meta_solver
    using D5_1[OF assms]
    apply transfer by auto 

  lemma lambda_predicates_2_2[axiom]:
    assumes "IsPropositionalInXY \<phi>"
    shows "[[\<lparr>(\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<phi> x y)), x\<^sup>P, y\<^sup>P\<rparr> \<^bold>\<equiv> \<phi> (x\<^sup>P) (y\<^sup>P)]]"
    apply axiom_meta_solver
    using D5_2[OF assms] apply transfer by auto

  lemma lambda_predicates_2_3[axiom]:
    assumes "IsPropositionalInXYZ \<phi>"
    shows "[[\<lparr>(\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<phi> x y z)),x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr> \<^bold>\<equiv> \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P)]]"
    proof -
      have "\<box>[\<lparr>(\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<phi> x y z)),x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr> \<^bold>\<rightarrow> \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P)]"
        apply meta_solver using D5_3[OF assms] by auto
      moreover have
        "\<box>[\<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P) \<^bold>\<rightarrow> \<lparr>(\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<phi> x y z)),x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr>]"
        apply axiom_meta_solver
        using D5_3[OF assms] unfolding d\<^sub>3_def ex3_def
        apply transfer by auto
      ultimately show ?thesis unfolding axiom_def equiv_def ConjS by blast
    qed

  lemma lambda_predicates_3_0[axiom]:
    "[[(\<^bold>\<lambda>\<^sup>0 \<phi>) \<^bold>= \<phi>]]"
    unfolding identity_defs
    apply axiom_meta_solver
    by (simp add: meta_defs meta_aux)

  lemma lambda_predicates_3_1[axiom]:
    "[[(\<^bold>\<lambda> x . \<lparr>F, x\<rparr>) \<^bold>= F]]"
    unfolding identity_defs
    apply axiom_meta_solver
    by (simp add: meta_defs meta_aux)

  lemma lambda_predicates_3_2[axiom]:
    "[[(\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<lparr>F, x, y\<rparr>)) \<^bold>= F]]"
    unfolding identity_defs
    apply axiom_meta_solver
    by (simp add: meta_defs meta_aux denotes_def denotation_def)

  lemma lambda_predicates_3_3[axiom]:
    "[[(\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<lparr>F, x, y, z\<rparr>)) \<^bold>= F]]"
    unfolding identity_defs
    apply axiom_meta_solver
    by (simp add: meta_defs meta_aux denotes_def denotation_def)

  lemma lambda_predicates_4_0[axiom]:
    assumes "\<And>x.[(\<^bold>\<A>(\<phi> x \<^bold>\<equiv> \<psi> x)) in v]"
    shows "[(\<^bold>\<lambda>\<^sup>0 (\<chi> (\<^bold>\<iota>x. \<phi> x)) \<^bold>= \<^bold>\<lambda>\<^sup>0 (\<chi> (\<^bold>\<iota>x. \<psi> x))) in v]"
    unfolding identity_defs using assms apply cut_tac
    apply meta_solver by (auto simp: meta_defs)

  lemma lambda_predicates_4_1[axiom]:
    assumes "\<And>x.[(\<^bold>\<A>(\<phi> x \<^bold>\<equiv> \<psi> x)) in v]"
    shows "[((\<^bold>\<lambda> x . \<chi> (\<^bold>\<iota>x. \<phi> x) x) \<^bold>= (\<^bold>\<lambda> x . \<chi> (\<^bold>\<iota>x. \<psi> x) x)) in v]"
    unfolding identity_defs using assms apply cut_tac
    apply meta_solver by (auto simp: meta_defs)

  lemma lambda_predicates_4_2[axiom]:
    assumes "\<And>x.[(\<^bold>\<A>(\<phi> x \<^bold>\<equiv> \<psi> x)) in v]"
    shows "[((\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<chi> (\<^bold>\<iota>x. \<phi> x) x y)) \<^bold>= (\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<chi> (\<^bold>\<iota>x. \<psi> x) x y))) in v]"
    unfolding identity_defs using assms apply cut_tac
    apply meta_solver by (auto simp: meta_defs)

  lemma lambda_predicates_4_3[axiom]:
    assumes "\<And>x.[(\<^bold>\<A>(\<phi> x \<^bold>\<equiv> \<psi> x)) in v]"
    shows "[(\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<chi> (\<^bold>\<iota>x. \<phi> x) x y z)) \<^bold>= (\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<chi> (\<^bold>\<iota>x. \<psi> x) x y z)) in v]"
    unfolding identity_defs using assms apply cut_tac
    apply meta_solver by (auto simp: meta_defs)

subsection{* Axioms of Encoding *}

  lemma encoding[axiom]:
    "[[\<lbrace>x,F\<rbrace> \<^bold>\<rightarrow> \<^bold>\<box>\<lbrace>x,F\<rbrace>]]"
    by axiom_meta_solver
  lemma nocoder[axiom]:
    "[[\<lparr>O!,x\<rparr> \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<exists> F . \<lbrace>x,F\<rbrace>)]]"
    unfolding axiom_def
    apply (rule allI, rule ImplI, subst (asm) OrdS)
    apply meta_solver unfolding en_def
    by (metis \<nu>.simps(5) mem_Collect_eq option.sel)
  lemma A_objects[axiom]:
    "[[\<^bold>\<exists>x. \<lparr>A!,x\<rparr> \<^bold>& (\<^bold>\<forall> F . (\<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<phi> F))]]"
    unfolding axiom_def
    proof (rule allI, rule ExIRule)
      fix v
      let ?x = "make\<kappa> (Some (\<alpha>\<nu> { F . [\<phi> F in v]}))"
      have "[\<lparr>A!,?x\<rparr> in v]" by (simp add: MetaSolver.AbsI Semantics.d\<^sub>\<kappa>.abs_eq)
      moreover have "[(\<^bold>\<forall>F. \<lbrace>?x,F\<rbrace> \<^bold>\<equiv> \<phi> F) in v]"
        apply meta_solver unfolding en_def
        using d\<^sub>1.rep_eq d\<^sub>\<kappa>_def d\<^sub>\<kappa>_proper eval\<Pi>\<^sub>1_inverse
        by (simp add: Semantics.d\<^sub>1.abs_eq Semantics.d\<^sub>1_inject)
      ultimately show "?x \<in> domain \<and> [\<lparr>A!,?x\<rparr> \<^bold>& (\<^bold>\<forall>F. \<lbrace>?x,F\<rbrace> \<^bold>\<equiv> \<phi> F) in v]"
        by (metis (no_types, lifting) MetaSolver.ConjI domain_\<kappa>_def mem_Collect_eq proper_denotes)
    qed
end

(*<*)
end
(*>*)
