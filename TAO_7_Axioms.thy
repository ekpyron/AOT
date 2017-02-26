theory TAO_7_Axioms
imports TAO_6_Identifiable
begin

section{* The Axioms of Principia Metaphysica *}

text{* The axioms of PM can now be derived from the Semantics
       and the meta-logic. *}

(* TODO: why is this needed again here? The syntax should already
         have been disabled in TAO_Semantics. *)
(* disable list syntax [] to replace it with truth evaluation *)
(*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
(*<*) no_syntax "__listcompr" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 

locale Axioms
begin
  interpretation MetaSolver .
  interpretation Semantics .
  named_theorems axiom

subsection{* Closures *}

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
    "[[\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<phi>)]]" by axiom_meta_solver
  lemma pl_2[axiom]:
    "[[(\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<chi>)) \<^bold>\<rightarrow> ((\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<chi>))]]" by axiom_meta_solver
  lemma pl_3[axiom]:
    "[[(\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi>) \<^bold>\<rightarrow> ((\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> \<phi>)]]" by axiom_meta_solver

subsection{* Axioms of Identity *}

  lemma l_identity[axiom]: "[[\<alpha> \<^bold>= \<beta> \<^bold>\<rightarrow> (\<phi> \<alpha> \<^bold>\<rightarrow> \<phi> \<beta>)]]" apply axiom_meta_solver
    using identifiable_identity by auto

subsection{* Axioms of Quantification *}

  text{*
         The axioms of quantification differ slightly from the axioms in Principia Metaphysica.
         The differences can be justified, though:

         Axiom @{text "cqt_2"} is omitted, as the embedding does not distinguish between terms
         and variables. Instead it is combined with @{text "cqt_1"}, in which the corresponding
         condition is omitted, and with @{text "cqt_5"} in its modified form @{text "cqt_5_mod"}.

         Note that the all quantifier for individuals only ranges over the datatype @{text "\<nu>"},
         which is always a denoting term and not a definite description in the embedding.

         The case of definite descriptions is handled separately in axiom @{text "cqt_1_\<kappa>"}:
         If a formula on datatype @{text "\<kappa>"} holds for all denoting terms (@{text "\<^bold>\<forall> \<alpha>. \<phi> (\<alpha>\<^sup>P)"})
         then the formula holds for an individual @{text "\<phi> \<alpha>"}, if @{text "\<alpha>"} denotes, i.e.
         @{text "\<^bold>\<exists> \<beta> . (\<beta>\<^sup>P) \<^bold>= \<alpha>"}.

         Although axiom @{text "cqt_5"} can be stated without modification, it is not a suitable
         formulation for the embedding. Therefore the seemingly stronger version @{text "cqt_5_mod"}
         is stated as well. On a closer look, though, @{text "cqt_5_mod"} immediately follows from
         the original @{text "cqt_5"} together with the omitted @{text "cqt_2"}.
       *}

  lemma cqt_1[axiom]: "[[(\<^bold>\<forall> \<alpha>. \<phi> \<alpha>) \<^bold>\<rightarrow> \<phi> \<alpha>]]" by axiom_meta_solver
  lemma cqt_1_\<kappa>[axiom]: "[[(\<^bold>\<forall> \<alpha>. \<phi> (\<alpha>\<^sup>P)) \<^bold>\<rightarrow> ((\<^bold>\<exists> \<beta> . (\<beta>\<^sup>P) \<^bold>= \<alpha>) \<^bold>\<rightarrow> \<phi> \<alpha>)]]" proof -
    {
      fix v
      assume 1: "[(\<^bold>\<forall> \<alpha>. \<phi> (\<alpha>\<^sup>P)) in v]"
      assume "[(\<^bold>\<exists> \<beta> . (\<beta>\<^sup>P) \<^bold>= \<alpha>) in v]"
      then obtain \<beta> where 2: "[(\<beta>\<^sup>P) \<^bold>= \<alpha> in v]" by (rule ExERule)
      hence "[\<phi> (\<beta>\<^sup>P) in v]" using 1 AllE by blast
      hence "[\<phi> \<alpha> in v]" using l_identity[where \<beta>="\<alpha>" and \<alpha>="\<beta>\<^sup>P" and \<phi>="\<lambda> x . \<phi> x", axiom_instance]
        ImplS 2 by simp
    }
    thus "[[(\<^bold>\<forall> \<alpha>. \<phi> (\<alpha>\<^sup>P)) \<^bold>\<rightarrow> ((\<^bold>\<exists> \<beta> . (\<beta>\<^sup>P) \<^bold>= \<alpha>) \<^bold>\<rightarrow> \<phi> \<alpha>)]]" unfolding axiom_def using ImplI by blast
  qed
  lemma cqt_3[axiom]: "[[(\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<rightarrow> \<psi> \<alpha>) \<^bold>\<rightarrow> ((\<^bold>\<forall>\<alpha>. \<phi> \<alpha>) \<^bold>\<rightarrow> (\<^bold>\<forall>\<alpha>. \<psi> \<alpha>))]]" by axiom_meta_solver
  lemma cqt_4[axiom]: "[[\<phi> \<^bold>\<rightarrow> (\<^bold>\<forall>\<alpha>. \<phi>)]]" by axiom_meta_solver

  inductive SimpleExOrEnc
    where "SimpleExOrEnc (\<lambda> x . \<lparr>F,x\<rparr>)"
        | "SimpleExOrEnc (\<lambda> x . \<lparr>F,x,y\<rparr>)"
        | "SimpleExOrEnc (\<lambda> x . \<lparr>F,y,x\<rparr>)"
        | "SimpleExOrEnc (\<lambda> x . \<lparr>F,x,y,z\<rparr>)"
        | "SimpleExOrEnc (\<lambda> x . \<lparr>F,y,x,z\<rparr>)"
        | "SimpleExOrEnc (\<lambda> x . \<lparr>F,y,z,x\<rparr>)"
        | "SimpleExOrEnc (\<lambda> x . \<lbrace>x,F\<rbrace>)"

  lemma cqt_5[axiom]: assumes "SimpleExOrEnc \<psi>"
    shows "[[(\<psi> (\<^bold>\<iota>x . \<phi> x)) \<^bold>\<rightarrow> (\<^bold>\<exists> \<alpha>. (\<alpha>\<^sup>P) \<^bold>= (\<^bold>\<iota>x . \<phi> x))]]" proof -
      have "\<forall> w . ([(\<psi> (\<^bold>\<iota>x . \<phi> x)) in w] \<longrightarrow> (\<exists> o\<^sub>1 . Some o\<^sub>1 = d\<^sub>\<kappa> (\<^bold>\<iota>x . \<phi> x)))"
        using assms apply induct by (meta_solver;metis)+
      moreover hence "\<forall> w . ([(\<psi> (\<^bold>\<iota>x . \<phi> x)) in w] \<longrightarrow> (that \<phi>) = (denotation (that \<phi>))\<^sup>P)"
        apply transfer by (metis (mono_tags, lifting) eq_snd_iff fst_conv option.simps(3))
     ultimately show ?thesis apply cut_tac unfolding identity_\<kappa>_def
      apply axiom_meta_solver by metis
  qed

  lemma cqt_5_mod[axiom]: assumes "SimpleExOrEnc \<psi>"
    shows "[[\<psi> x \<^bold>\<rightarrow> (\<^bold>\<exists>  \<alpha> . (\<alpha>\<^sup>P) \<^bold>= x)]]" proof -
      have "\<forall> w . ([(\<psi> x) in w] \<longrightarrow> (\<exists> o\<^sub>1 . Some o\<^sub>1 = d\<^sub>\<kappa> x))"
        using assms apply induct by (meta_solver;metis)+
      moreover hence "\<forall> w . ([(\<psi> x) in w] \<longrightarrow> (x) = (denotation (x))\<^sup>P)"
        apply transfer by (metis (mono_tags, lifting) eq_snd_iff fst_conv option.simps(3))
      ultimately show ?thesis apply cut_tac unfolding identity_\<kappa>_def apply axiom_meta_solver by metis
  qed

subsection{* Axioms of Actuality *}

  text{* The necessitation averse axiom of actuality is stated to be actually true;
         for the statement as a proper axiom (for which necessitation would be allowed)
         nitpick can find a counter-model as desired. *}
  lemma logic_actual[axiom]: "[(\<^bold>\<A>\<phi>) \<^bold>\<equiv> \<phi>]" apply meta_solver by auto
  lemma "[[(\<^bold>\<A>\<phi>) \<^bold>\<equiv> \<phi>]]" nitpick[user_axioms, expect = genuine, card = 1, card i = 2] oops

  lemma logic_actual_nec_1[axiom]: "[[\<^bold>\<A>\<^bold>\<not>\<phi> \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<A>\<phi>]]" by axiom_meta_solver
  lemma logic_actual_nec_2[axiom]: "[[(\<^bold>\<A>(\<phi> \<^bold>\<rightarrow> \<psi>)) \<^bold>\<equiv> (\<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<^bold>\<A>\<psi>)]]" by axiom_meta_solver
  lemma logic_actual_nec_3[axiom]: "[[\<^bold>\<A>(\<^bold>\<forall>\<alpha>. \<phi> \<alpha>) \<^bold>\<equiv> (\<^bold>\<forall>\<alpha>. \<^bold>\<A>(\<phi> \<alpha>))]]" by axiom_meta_solver
  lemma logic_actual_nec_4[axiom]: "[[\<^bold>\<A>\<phi> \<^bold>\<equiv> \<^bold>\<A>\<^bold>\<A>\<phi>]]" by axiom_meta_solver

subsection{* Axioms of Necessity *}

  lemma qml_1[axiom]: "[[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>)]]" by axiom_meta_solver
  lemma qml_2[axiom]: "[[\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>]]" by axiom_meta_solver
  lemma qml_3[axiom]: "[[\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>]]" by axiom_meta_solver
  lemma qml_4[axiom]: "[[\<^bold>\<diamond>(\<^bold>\<exists>x. \<lparr>E!,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<diamond>\<^bold>\<not>\<lparr>E!,x\<^sup>P\<rparr>) \<^bold>& \<^bold>\<diamond>\<^bold>\<not>(\<^bold>\<exists>x. \<lparr>E!,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<diamond>\<^bold>\<not>\<lparr>E!,x\<^sup>P\<rparr>)]]"
     unfolding axiom_def using PossiblyContingentObjectExistsAxiom PossiblyNoContingentObjectExistsAxiom
     apply (simp add: meta_defs meta_aux conn_defs forall_\<nu>_def split: \<nu>.split \<upsilon>.split)
     by (metis \<nu>\<upsilon>_\<omega>\<nu>_is_\<omega>\<upsilon> \<upsilon>.distinct(1) \<upsilon>.inject(1))

subsection{* Axioms of Necessity and Actuality *}
  lemma qml_act_1[axiom]: "[[\<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<A>\<phi>]]" by axiom_meta_solver
  lemma qml_act_2[axiom]: "[[\<^bold>\<box>\<phi> \<^bold>\<equiv> \<^bold>\<A>(\<^bold>\<box>\<phi>)]]" by axiom_meta_solver

subsection{* Axioms of Descriptions *}
  lemma descriptions[axiom]: "[[x\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) \<^bold>\<equiv> (\<^bold>\<forall>z.(\<^bold>\<A>(\<phi> z) \<^bold>\<equiv> z \<^bold>= x))]]"
    unfolding axiom_def apply (rule allI)
    proof (rule meta_intro)
      fix v
      {
        assume "[x\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in v]"
        moreover hence 1: "\<exists>o\<^sub>1 o\<^sub>2. Some o\<^sub>1 = d\<^sub>\<kappa> (x\<^sup>P) \<and> Some o\<^sub>2 = d\<^sub>\<kappa> (\<^bold>\<iota>x. \<phi> x) \<and> o\<^sub>1 = o\<^sub>2"
          apply cut_tac unfolding identity_\<kappa>_def by meta_solver
        then obtain o\<^sub>1 o\<^sub>2 where 2: "Some o\<^sub>1 = d\<^sub>\<kappa> (x\<^sup>P) \<and> Some o\<^sub>2 = d\<^sub>\<kappa> (\<^bold>\<iota>x. \<phi> x) \<and> o\<^sub>1 = o\<^sub>2" by auto
        hence 3: "(\<exists> x .((w\<^sub>0 \<Turnstile> \<phi> x) \<and> (\<forall>y. (w\<^sub>0 \<Turnstile> \<phi> y) \<longrightarrow> y = x))) \<and> d\<^sub>\<kappa> (\<^bold>\<iota>x. \<phi> x) = Some (THE x. (w\<^sub>0 \<Turnstile> \<phi> x))"
          using D3 by (metis option.distinct(1))
        then obtain X where 4: "((w\<^sub>0 \<Turnstile> \<phi> X) \<and> (\<forall>y. (w\<^sub>0 \<Turnstile> \<phi> y) \<longrightarrow> y = X))" by auto
        moreover have "o\<^sub>1 = (THE x. (w\<^sub>0 \<Turnstile> \<phi> x))" using 2 3 by auto
        ultimately have 5: "X = o\<^sub>1" by (metis (mono_tags) theI)
        have "\<forall> z . [\<^bold>\<A>\<phi> z in v] = [(z\<^sup>P) \<^bold>= (x\<^sup>P) in v]"
        proof
          fix z
          have "[\<^bold>\<A>\<phi> z in v] \<Longrightarrow> [(z\<^sup>P) \<^bold>= (x\<^sup>P) in v]"
            unfolding identity_\<kappa>_def apply meta_solver
            unfolding d\<^sub>\<kappa>_def using 4 5 2 apply transfer apply simp
            by (metis Semantics.w\<^sub>0_def)
          moreover have "[(z\<^sup>P) \<^bold>= (x\<^sup>P) in v] \<Longrightarrow> [\<^bold>\<A>\<phi> z in v]"
            unfolding identity_\<kappa>_def apply meta_solver using 2 4 5 apply transfer apply simp
            by (metis Semantics.w\<^sub>0_def)
          ultimately show "[\<^bold>\<A>\<phi> z in v] = [(z\<^sup>P) \<^bold>= (x\<^sup>P) in v]" by auto
        qed
        hence "[\<^bold>\<forall>z. \<^bold>\<A>\<phi> z \<^bold>\<equiv> (z\<^sup>P) \<^bold>= (x\<^sup>P) in v]" by (simp add: AllI EquivS)
      }
      moreover {
        assume "[\<^bold>\<forall>z. \<^bold>\<A>\<phi> z \<^bold>\<equiv> (z\<^sup>P) \<^bold>= (x\<^sup>P) in v]"
        hence "\<And>z. (dw \<Turnstile> \<phi> z) = (\<exists>o\<^sub>1 o\<^sub>2. Some o\<^sub>1 = d\<^sub>\<kappa> (z\<^sup>P) \<and> Some o\<^sub>2 = d\<^sub>\<kappa> (x\<^sup>P) \<and> o\<^sub>1 = o\<^sub>2)"
          apply cut_tac unfolding identity_\<kappa>_def  by meta_solver
        hence "\<forall> z . eval\<o> (\<phi> z) dj dw = (z = x)" apply transfer by simp
        moreover hence "\<exists>!x . eval\<o> (\<phi> x) dj dw" by metis
        ultimately have "x\<^sup>P = (\<^bold>\<iota>x. \<phi> x)" unfolding TheS by (simp add: \<nu>\<kappa>_def)
        hence "[x\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in v]"
          using Eq\<kappa>S unfolding identity_\<kappa>_def by (metis Semantics.d\<^sub>\<kappa>_proper)
      }
      ultimately show "[x\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in v] = [\<^bold>\<forall>z. \<^bold>\<A>\<phi> z \<^bold>\<equiv> z \<^bold>= x in v]"
        by (metis (mono_tags, lifting) AllI AllS identity_\<nu>_def)
    qed

subsection{* Axioms for Complex Relation Terms *}

  lemma lambda_predicates_1[axiom]: "(\<^bold>\<lambda> x . \<phi> x) = (\<^bold>\<lambda> y . \<phi> y)" ..

  lemma lambda_predicates_2_1[axiom]:
    assumes "IsPropositionalInX \<phi>"
    shows "[[\<lparr>\<^bold>\<lambda> x . \<phi> (x\<^sup>P), x\<^sup>P\<rparr> \<^bold>\<equiv> \<phi> (x\<^sup>P)]]"
    apply axiom_meta_solver
    using Semantics.D5_1[OF assms]
    apply transfer by simp

  lemma lambda_predicates_2_2[axiom]:
    assumes "IsPropositionalInXY \<phi>"
    shows "[[\<lparr>(\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<phi> (x\<^sup>P) (y\<^sup>P))), x\<^sup>P, y\<^sup>P\<rparr> \<^bold>\<equiv> \<phi> (x\<^sup>P) (y\<^sup>P)]]"
    apply axiom_meta_solver
    using Semantics.D5_2[OF assms] apply transfer by simp

  lemma lambda_predicates_2_3[axiom]:
    assumes "IsPropositionalInXYZ \<phi>"
    shows "[[\<lparr>(\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P))), x\<^sup>P, y\<^sup>P, z\<^sup>P\<rparr> \<^bold>\<equiv> \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P)]]" proof -
      have "\<box>[\<lparr>(\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P))), x\<^sup>P, y\<^sup>P, z\<^sup>P\<rparr> \<^bold>\<rightarrow> \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P)]"
        apply meta_solver using Semantics.D5_3[OF assms] by auto
      moreover have "\<box>[\<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P) \<^bold>\<rightarrow> \<lparr>(\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P))), x\<^sup>P, y\<^sup>P, z\<^sup>P\<rparr>]"
        apply axiom_meta_solver
        using Semantics.D5_3[OF assms] unfolding d\<^sub>3_def ex3_def
        apply transfer apply simp by fastforce
      ultimately show ?thesis unfolding axiom_def equiv_def ConjS by blast
    qed

  lemma lambda_predicates_3_0[axiom]: "[[(\<^bold>\<lambda>\<^sup>0 \<phi>) \<^bold>= \<phi>]]" unfolding identity_defs
    apply axiom_meta_solver by (simp add: meta_defs meta_aux)

  lemma lambda_predicates_3_1[axiom]: "[[(\<^bold>\<lambda> x . \<lparr>F, x\<^sup>P\<rparr>) \<^bold>= F]]" unfolding identity_defs
    apply axiom_meta_solver by (simp add: meta_defs meta_aux)

  lemma lambda_predicates_3_2[axiom]: "[[(\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<lparr>F, x\<^sup>P, y\<^sup>P\<rparr>)) \<^bold>= F]]" unfolding identity_defs
    apply axiom_meta_solver by (simp add: meta_defs meta_aux)

  lemma lambda_predicates_3_3[axiom]: "[[(\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<lparr>F, x\<^sup>P, y\<^sup>P, z\<^sup>P\<rparr>)) \<^bold>= F]]" unfolding identity_defs
    apply axiom_meta_solver by (simp add: meta_defs meta_aux)

  lemma lambda_predicates_4_0[axiom]: "(\<And>x.[(\<^bold>\<A>(\<phi> x \<^bold>\<equiv> \<psi> x)) in v]) \<Longrightarrow> [(\<^bold>\<lambda>\<^sup>0 (\<chi> (\<^bold>\<iota>x. \<phi> x)) \<^bold>= \<^bold>\<lambda>\<^sup>0 (\<chi> (\<^bold>\<iota>x. \<psi> x))) in v]"
    unfolding identity_defs
    apply meta_solver by (auto simp: meta_defs)

  lemma lambda_predicates_4_1[axiom]: "(\<And>x.[(\<^bold>\<A>(\<phi> x \<^bold>\<equiv> \<psi> x)) in v]) \<Longrightarrow> [((\<^bold>\<lambda> x . \<chi> (\<^bold>\<iota>x. \<phi> x) x) \<^bold>= (\<^bold>\<lambda> x . \<chi> (\<^bold>\<iota>x. \<psi> x) x)) in v]"
    unfolding identity_defs
    apply meta_solver by (auto simp: meta_defs)

  lemma lambda_predicates_4_2[axiom]: "(\<And>x.[(\<^bold>\<A>(\<phi> x \<^bold>\<equiv> \<psi> x)) in v]) \<Longrightarrow> [((\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<chi> (\<^bold>\<iota>x. \<phi> x) x y)) \<^bold>= (\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<chi> (\<^bold>\<iota>x. \<psi> x) x y))) in v]"
    unfolding identity_defs
    apply meta_solver by (auto simp: meta_defs)

  lemma lambda_predicates_4_3[axiom]: "(\<And>x.[(\<^bold>\<A>(\<phi> x \<^bold>\<equiv> \<psi> x)) in v]) \<Longrightarrow> [((\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<chi> (\<^bold>\<iota>x. \<phi> x) x y z)) \<^bold>= (\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<chi> (\<^bold>\<iota>x. \<psi> x) x y z))) in v]"
    unfolding identity_defs
    apply meta_solver by (auto simp: meta_defs)

subsection{* Axioms of Encoding *}

  lemma encoding[axiom]: "[[\<lbrace>x,F\<rbrace> \<^bold>\<rightarrow> \<^bold>\<box>\<lbrace>x,F\<rbrace>]]" by axiom_meta_solver
  lemma nocoder[axiom]: "[[\<lparr>O!,x\<rparr> \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<exists> F . \<lbrace>x,F\<rbrace>)]]"
    unfolding axiom_def apply (rule allI) apply (rule ImplI) apply (subst (asm) OrdS)
    apply meta_solver unfolding Semantics.en_def
    by (metis \<nu>.simps(5) mem_Collect_eq option.sel)
  lemma A_objects[axiom]: "[[\<^bold>\<exists>x. \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . (\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F))]]"
    proof -
      {
        fix v
        obtain x :: \<nu> where x_prop: "x = \<alpha>\<nu> { F . [\<phi> F in v]}" by auto
        hence "[\<lparr>A!,x\<^sup>P\<rparr> in v]" by (simp add: AbsS Semantics.d\<^sub>\<kappa>_proper)
        moreover have "[(\<^bold>\<forall>F. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F) in v]" apply meta_solver apply (subst x_prop)
          unfolding en_def using d\<^sub>1.rep_eq d\<^sub>\<kappa>_def d\<^sub>\<kappa>_proper eval\<Pi>\<^sub>1_inverse by auto
        ultimately have "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall>F. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F) in v]" by (simp add: ConjS)
        hence "[\<^bold>\<exists> x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall>F. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F) in v]" by (rule ExIRule)
      }
      thus ?thesis unfolding axiom_def by auto
    qed
end
end
