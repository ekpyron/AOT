theory AOT_model
  imports Main
begin

text\<open>We introduce a primitive type for (hyper)intensional propositions\<close>
typedecl \<o>

text\<open>Propositions need to cover all extensions possible in usual modal logic, so we
     axiomatize that there is a surjective function onto the boolean-valued functions
     acting on possible worlds.\<close>
typedecl w \<comment>\<open>The primtive type of possible worlds.\<close>
axiomatization AOT_model_d\<o> :: \<open>\<o>\<Rightarrow>(w\<Rightarrow>bool)\<close> where d\<o>_surj: \<open>surj AOT_model_d\<o>\<close>
consts w\<^sub>0 :: w \<comment>\<open>The designated actual world.\<close>
axiomatization where AOT_model_nonactual_world: \<open>\<exists>w . w \<noteq> w\<^sub>0\<close>

text\<open>Validity of a proposition in a world can now simply be defined by the means of the
     just axiomatized surjective extension function.\<close>
definition AOT_model_valid_in :: \<open>w\<Rightarrow>\<o>\<Rightarrow>bool\<close> where \<open>AOT_model_valid_in w \<phi> \<equiv> AOT_model_d\<o> \<phi> w\<close>

text\<open>The inverse of the extension function can be used to choose a proposition for a given extension.\<close>
definition AOT_model_proposition_choice :: \<open>(w\<Rightarrow>bool) \<Rightarrow> \<o>\<close> (binder \<open>\<epsilon>\<^sub>\<o> \<close> 8)
  where \<open>\<epsilon>\<^sub>\<o> w. \<phi> w \<equiv> (inv AOT_model_d\<o>) \<phi>\<close>
text\<open>By definition validity and proposition choice combine to the identity.\<close>
lemma AOT_model_proposition_choice_simp: \<open>AOT_model_valid_in w (\<epsilon>\<^sub>\<o> w. \<phi> w) = \<phi> w\<close>
  by (simp add: surj_f_inv_f[OF d\<o>_surj] AOT_model_valid_in_def AOT_model_proposition_choice_def)

text\<open>There are models for the axiom above.\<close>
lemma \<open>True\<close> nitpick[satisfy, user_axioms, expect = genuine] ..

declare[[typedef_overloaded]]

typedecl \<omega>
typedecl \<sigma>'
consts \<sigma>'\<^sub>V :: \<sigma>'
consts \<sigma>'\<^sub>0 :: \<sigma>'
definition \<sigma>cond :: \<open>(\<omega> \<Rightarrow> w \<Rightarrow> bool) set \<times> (\<omega> \<Rightarrow> w \<Rightarrow> bool) set \<times> \<sigma>' \<Rightarrow> bool\<close> where
  \<open>\<sigma>cond \<equiv> \<lambda> (ordext :: (\<omega> \<Rightarrow> w \<Rightarrow> bool) set, ordext' :: (\<omega> \<Rightarrow> w \<Rightarrow> bool) set, \<sigma>' :: \<sigma>') .
    (\<forall> x \<in> ordext . x \<in> ordext') \<and> (if ordext' = {} then \<sigma>' = \<sigma>'\<^sub>0 else if \<forall> x \<in> ordext' . x \<in> ordext then \<sigma>' = \<sigma>'\<^sub>V else True)\<close>
definition \<sigma>set where \<open>\<sigma>set \<equiv> Collect \<sigma>cond\<close>
abbreviation (input) ordext_intersection :: \<open>(\<omega> \<Rightarrow> w \<Rightarrow> bool) set \<times> (\<omega> \<Rightarrow> w \<Rightarrow> bool) set \<times> \<sigma>' \<Rightarrow> (\<omega> \<Rightarrow> w \<Rightarrow> bool) set\<close> where
  \<open>ordext_intersection \<equiv> \<lambda> set . fst set\<close>
abbreviation (input) ordext_union :: \<open>(\<omega> \<Rightarrow> w \<Rightarrow> bool) set \<times> (\<omega> \<Rightarrow> w \<Rightarrow> bool) set \<times> \<sigma>' \<Rightarrow> (\<omega> \<Rightarrow> w \<Rightarrow> bool) set\<close> where
  \<open>ordext_union \<equiv> \<lambda> set . fst (snd set)\<close>
abbreviation (input) \<sigma>\<sigma>' :: \<open>(\<omega> \<Rightarrow> w \<Rightarrow> bool) set \<times> (\<omega> \<Rightarrow> w \<Rightarrow> bool) set \<times> \<sigma>' \<Rightarrow> \<sigma>'\<close> where
  \<open>\<sigma>\<sigma>' \<equiv> \<lambda> set . snd (snd set)\<close>
lemma \<sigma>condI:
  assumes \<open>\<forall> x \<in> ordext_intersection \<sigma> . x \<in> ordext_union \<sigma>\<close>
  assumes \<open>ordext_union \<sigma> = {} \<Longrightarrow> \<sigma>\<sigma>' \<sigma> = \<sigma>'\<^sub>0\<close>
  assumes \<open>ordext_union \<sigma> \<noteq> {} \<Longrightarrow> ordext_intersection \<sigma> = ordext_union \<sigma> \<Longrightarrow> \<sigma>\<sigma>' \<sigma> = \<sigma>'\<^sub>V\<close>
  shows \<open>\<sigma>cond \<sigma>\<close>
  unfolding \<sigma>cond_def using assms by fastforce
typedef \<sigma> = \<open>\<sigma>set\<close> unfolding \<sigma>set_def \<sigma>cond_def by auto

typedecl null
datatype \<upsilon> = \<omega>\<upsilon> \<omega> | \<sigma>\<upsilon> \<sigma> | is_null\<upsilon>: null\<upsilon> null

consts AOT_model_concrete\<omega> :: \<open>\<omega> \<Rightarrow> w \<Rightarrow>  bool\<close>
specification (AOT_model_concrete\<omega>)
  AOT_model_\<omega>_concrete_in_some_world: \<open>\<exists> w . AOT_model_concrete\<omega> x w\<close>
  AOT_model_contingent_object: \<open>\<exists> x w . AOT_model_concrete\<omega> x w \<and> \<not>AOT_model_concrete\<omega> x w\<^sub>0\<close>
  by (rule_tac x=\<open>\<lambda>_ w. w \<noteq> w\<^sub>0\<close> in exI) (auto simp: AOT_model_nonactual_world)

typedef urrel = \<open>{ \<phi> . \<forall> x w . \<not>AOT_model_valid_in w (\<phi> (null\<upsilon> x)) }\<close>
  by (rule_tac x=\<open>\<lambda> x . (\<epsilon>\<^sub>\<o> w . \<not>is_null\<upsilon> x)\<close> in exI) (auto simp: AOT_model_proposition_choice_simp)

datatype \<kappa> = \<omega>\<kappa> \<omega> | \<alpha>\<kappa> \<open>urrel set\<close> | is_null\<kappa>: null\<kappa> null

section\<open>Extended model version\<close>

consts \<alpha>\<sigma>_ext :: \<open>urrel set \<Rightarrow> \<sigma>\<close>

definition urrel_to_\<omega>rel :: \<open>urrel \<Rightarrow> (\<omega> \<Rightarrow> w \<Rightarrow> bool)\<close> where
  \<open>urrel_to_\<omega>rel \<equiv> \<lambda> r u w . AOT_model_valid_in w (Rep_urrel r (\<omega>\<upsilon> u))\<close>
definition \<omega>rel_to_urrel :: \<open>(\<omega> \<Rightarrow> w \<Rightarrow> bool) \<Rightarrow> urrel\<close> where
  \<open>\<omega>rel_to_urrel \<equiv> \<lambda> \<phi> . Abs_urrel (\<lambda> u . \<epsilon>\<^sub>\<o> w . case u of \<omega>\<upsilon> x \<Rightarrow> \<phi> x w | _ \<Rightarrow> False)\<close>

definition AOT_urrel_\<omega>equiv :: \<open>urrel \<Rightarrow> urrel \<Rightarrow> bool\<close> where
  \<open>AOT_urrel_\<omega>equiv \<equiv> \<lambda> r s . \<forall> u v . AOT_model_valid_in v (Rep_urrel r (\<omega>\<upsilon> u)) = AOT_model_valid_in v (Rep_urrel s (\<omega>\<upsilon> u))\<close>

lemma urrel_\<omega>rel_quot: \<open>Quotient3 AOT_urrel_\<omega>equiv urrel_to_\<omega>rel \<omega>rel_to_urrel\<close>
proof(rule Quotient3I)
  show \<open>urrel_to_\<omega>rel (\<omega>rel_to_urrel a) = a\<close> for a
    unfolding \<omega>rel_to_urrel_def urrel_to_\<omega>rel_def
    apply (rule ext)
    apply (subst Abs_urrel_inverse)
    by (auto simp: AOT_model_proposition_choice_simp)
next
  show \<open>AOT_urrel_\<omega>equiv (\<omega>rel_to_urrel a) (\<omega>rel_to_urrel a)\<close> for a
    unfolding \<omega>rel_to_urrel_def AOT_urrel_\<omega>equiv_def
    apply (subst (1 2) Abs_urrel_inverse)
    by (auto simp: AOT_model_proposition_choice_simp)
next
  show \<open>AOT_urrel_\<omega>equiv r s = (AOT_urrel_\<omega>equiv r r \<and> AOT_urrel_\<omega>equiv s s \<and> urrel_to_\<omega>rel r = urrel_to_\<omega>rel s)\<close> for r s
  proof
    assume \<open>AOT_urrel_\<omega>equiv r s\<close>
    hence \<open>AOT_model_valid_in v (Rep_urrel r (\<omega>\<upsilon> u)) = AOT_model_valid_in v (Rep_urrel s (\<omega>\<upsilon> u))\<close> for u v
      using AOT_urrel_\<omega>equiv_def by metis
    hence \<open>urrel_to_\<omega>rel r = urrel_to_\<omega>rel s\<close>
      unfolding urrel_to_\<omega>rel_def
      by simp
    thus \<open>AOT_urrel_\<omega>equiv r r \<and> AOT_urrel_\<omega>equiv s s \<and> urrel_to_\<omega>rel r = urrel_to_\<omega>rel s\<close>
      unfolding AOT_urrel_\<omega>equiv_def
      by auto
  next
    assume \<open>AOT_urrel_\<omega>equiv r r \<and> AOT_urrel_\<omega>equiv s s \<and> urrel_to_\<omega>rel r = urrel_to_\<omega>rel s\<close>
    hence \<open>AOT_model_valid_in v (Rep_urrel r (\<omega>\<upsilon> u)) = AOT_model_valid_in v (Rep_urrel s (\<omega>\<upsilon> u))\<close> for u v
      by (metis urrel_to_\<omega>rel_def)
    thus \<open>AOT_urrel_\<omega>equiv r s\<close>
      using AOT_urrel_\<omega>equiv_def by presburger
  qed
qed

specification (\<alpha>\<sigma>_ext)
  \<alpha>\<sigma>_ext_surj: \<open>surj \<alpha>\<sigma>_ext\<close>
  \<alpha>\<sigma>_eq_ord_exts_all:
    \<open>\<alpha>\<sigma>_ext a = \<alpha>\<sigma>_ext b \<Longrightarrow> (\<And>s . urrel_to_\<omega>rel s = urrel_to_\<omega>rel r \<Longrightarrow> s \<in> a) \<Longrightarrow> (\<And> s . urrel_to_\<omega>rel s = urrel_to_\<omega>rel r \<Longrightarrow> s \<in> b)\<close>
  \<alpha>\<sigma>_eq_ord_exts_ex:
    \<open>\<alpha>\<sigma>_ext a = \<alpha>\<sigma>_ext b \<Longrightarrow> (\<exists> s . s \<in> a \<and> urrel_to_\<omega>rel s = urrel_to_\<omega>rel r) \<Longrightarrow> (\<exists>s . s \<in> b \<and> urrel_to_\<omega>rel s = urrel_to_\<omega>rel r)\<close>
proof -
  (* TODO: find better proof/strategy or simplify *)
  define \<alpha>\<sigma>_wit_intersection where \<open>\<alpha>\<sigma>_wit_intersection \<equiv> \<lambda> urrels . {ordext . \<forall>urrel . urrel_to_\<omega>rel urrel = ordext \<longrightarrow> urrel \<in> urrels}\<close>
  define \<alpha>\<sigma>_wit_union where \<open>\<alpha>\<sigma>_wit_union \<equiv> \<lambda> urrels . {ordext . \<exists>urrel\<in>urrels . urrel_to_\<omega>rel urrel = ordext}\<close>
  define \<alpha>\<sigma>_wit_\<sigma>' where \<open>\<alpha>\<sigma>_wit_\<sigma>' \<equiv> \<lambda> urrels . THE \<sigma>' . \<exists> urrel \<in> urrels .
          urrel_to_\<omega>rel urrel \<notin> \<alpha>\<sigma>_wit_intersection urrels \<and>
          ( \<forall> w \<sigma> . AOT_model_valid_in w (Rep_urrel urrel (\<sigma>\<upsilon> \<sigma>)) \<longrightarrow> \<sigma>\<sigma>' (Rep_\<sigma> \<sigma>) = \<sigma>')\<close>

  let ?\<alpha>\<sigma>_wit = \<open>\<lambda> urrels . 
        let ordexts = \<alpha>\<sigma>_wit_intersection urrels in
        let ordexts' = \<alpha>\<sigma>_wit_union urrels in
      (ordexts, ordexts', if ordexts' = {} then \<sigma>'\<^sub>0 else if \<forall> x \<in> ordexts' . x \<in> ordexts then \<sigma>'\<^sub>V else \<alpha>\<sigma>_wit_\<sigma>' urrels)\<close>
  define \<alpha>\<sigma>_wit :: \<open>urrel set \<Rightarrow> \<sigma>\<close> where
    \<open>\<alpha>\<sigma>_wit \<equiv> \<lambda> urrels . Abs_\<sigma> (?\<alpha>\<sigma>_wit urrels)\<close>
  have 1: \<open>\<forall>urrel. urrel_to_\<omega>rel urrel = y \<longrightarrow> urrel \<in> x \<Longrightarrow> \<exists>urrel\<in>x. urrel_to_\<omega>rel urrel = y\<close> for y x
    by (meson Quotient3_abs_rep urrel_\<omega>rel_quot)
  have wits_in_\<sigma>set: \<open>?\<alpha>\<sigma>_wit x \<in> \<sigma>set\<close> for x
    unfolding \<sigma>set_def
    apply simp
    apply (rule \<sigma>condI)
    by (auto simp: Let_def 1 \<alpha>\<sigma>_wit_intersection_def \<alpha>\<sigma>_wit_union_def)

  {
    fix \<sigma>
    have \<sigma>cond: \<open>\<sigma>cond (Rep_\<sigma> \<sigma>)\<close>
      using Rep_\<sigma> \<sigma>set_def by blast
    have \<sigma>cond_empty: \<open>fst (snd (Rep_\<sigma> \<sigma>)) = {} \<Longrightarrow> (fst (Rep_\<sigma> \<sigma>)) = {}\<close>
      by (metis (no_types, lifting) Product_Type.Collect_case_prodD Rep_\<sigma> \<sigma>cond_def \<sigma>set_def curryI curry_case_prod eq_fst_iff ex_in_conv) 
    have \<sigma>cond_univ: \<open>(fst (Rep_\<sigma> \<sigma>)) = UNIV \<Longrightarrow> fst (snd (Rep_\<sigma> \<sigma>)) = UNIV\<close>
      by (metis (mono_tags, lifting) UNIV_I UNIV_eq_I \<sigma>cond \<sigma>cond_def prod.case_eq_if)
    {
      assume \<open>ordext_union (Rep_\<sigma> \<sigma>) = {}\<close>
      moreover have \<open>ordext_intersection (Rep_\<sigma> \<sigma>) = {}\<close>
        by (simp add: \<sigma>cond_empty calculation)
      moreover have \<open>\<sigma>\<sigma>' (Rep_\<sigma> \<sigma>) = \<sigma>'\<^sub>0\<close>
        by (metis (mono_tags, lifting) \<sigma>cond \<sigma>cond_def calculation prod.case_eq_if)
      moreover have \<open>\<alpha>\<sigma>_wit {} = Abs_\<sigma> ({},{},\<sigma>'\<^sub>0)\<close>
        unfolding \<alpha>\<sigma>_wit_def
        apply (subst Abs_\<sigma>_inject)
        using wits_in_\<sigma>set apply blast
         apply (metis \<sigma>cond \<sigma>set_def calculation(1) calculation(2) calculation(3) mem_Collect_eq prod.exhaust_sel)
        apply (auto simp: Let_def \<alpha>\<sigma>_wit_intersection_def \<alpha>\<sigma>_wit_union_def)
        by (metis Quotient3_def urrel_\<omega>rel_quot)
      ultimately have \<open>\<alpha>\<sigma>_wit {} = \<sigma>\<close>
        unfolding \<alpha>\<sigma>_wit_def
        by (metis Rep_\<sigma>_inverse prod.collapse)
      hence \<open>\<exists>urrels . \<alpha>\<sigma>_wit urrels = \<sigma>\<close> by blast
    }
    moreover {
      assume 0: \<open>ordext_union (Rep_\<sigma> \<sigma>) \<noteq> {}\<close>
      moreover assume \<open>ordext_union (Rep_\<sigma> \<sigma>) = ordext_intersection (Rep_\<sigma> \<sigma>)\<close>
      moreover have \<open>snd (snd (Rep_\<sigma> \<sigma>)) = \<sigma>'\<^sub>V\<close>
        by (metis (mono_tags, lifting) Rep_\<sigma> \<sigma>cond_def \<sigma>set_def calculation(1) calculation(2) mem_Collect_eq prod.case_eq_if)
      moreover {
        have 2: \<open>{ordext. \<exists>urrel\<in>{urrel. urrel_to_\<omega>rel urrel \<in> fst (Rep_\<sigma> \<sigma>)}. urrel_to_\<omega>rel urrel = ordext} \<noteq> {}\<close>
          using "0" Quotient3_abs_rep calculation(2) urrel_\<omega>rel_quot by fastforce
        have \<open>\<alpha>\<sigma>_wit {urrel . urrel_to_\<omega>rel urrel \<in> ordext_intersection (Rep_\<sigma> \<sigma>)} = Abs_\<sigma> (ordext_intersection (Rep_\<sigma> \<sigma>), ordext_intersection (Rep_\<sigma> \<sigma>), \<sigma>'\<^sub>V)\<close>
        unfolding \<alpha>\<sigma>_wit_def
        apply (subst Abs_\<sigma>_inject)
        unfolding \<sigma>set_def
          apply simp
          apply (rule \<sigma>condI)
            apply (simp add: Let_def \<alpha>\<sigma>_wit_intersection_def \<alpha>\<sigma>_wit_union_def)
            apply (metis 1)
           apply (simp add: Let_def \<alpha>\<sigma>_wit_intersection_def \<alpha>\<sigma>_wit_union_def)
          apply (simp add: Let_def \<alpha>\<sigma>_wit_intersection_def \<alpha>\<sigma>_wit_union_def)
        apply blast
         apply (metis CollectI \<sigma>cond calculation(2) calculation(3) surjective_pairing)
        apply (simp only: Let_def 2 \<alpha>\<sigma>_wit_intersection_def \<alpha>\<sigma>_wit_union_def) apply simp
        using 1 by blast
      }
      moreover have \<open>\<sigma>cond (ordext_union (Rep_\<sigma> \<sigma>), ordext_union (Rep_\<sigma> \<sigma>), \<sigma>'\<^sub>V)\<close>
        by (metis \<sigma>cond calculation(2) calculation(3) surjective_pairing)
      ultimately have \<open>\<alpha>\<sigma>_wit {urrel . urrel_to_\<omega>rel urrel \<in> ordext_union (Rep_\<sigma> \<sigma>)} = \<sigma>\<close>
        by (metis Rep_\<sigma>_inverse prod.exhaust_sel)
      hence \<open>\<exists>urrels . \<alpha>\<sigma>_wit urrels = \<sigma>\<close> by blast
    }
    moreover {
      assume \<open>fst (Rep_\<sigma> \<sigma>) \<noteq> UNIV\<close>
      assume \<open>ordext_union (Rep_\<sigma> \<sigma>) \<noteq> ordext_intersection (Rep_\<sigma> \<sigma>)\<close>
      moreover have \<open>\<forall>x \<in> ordext_intersection (Rep_\<sigma> \<sigma>) . x \<in> ordext_union (Rep_\<sigma> \<sigma>)\<close>
        by (metis (no_types, lifting) \<sigma>cond \<sigma>cond_def case_prod_unfold)
      ultimately obtain r where r_notin_intersection: \<open>r \<notin> ordext_intersection (Rep_\<sigma> \<sigma>)\<close> and r_in_union: \<open>r \<in> ordext_union (Rep_\<sigma> \<sigma>)\<close>
        by blast
      have \<alpha>\<sigma>wit_eqI: \<open>\<alpha>\<sigma>_wit x = \<sigma>\<close> if
        \<open>\<alpha>\<sigma>_wit_intersection x = ordext_intersection (Rep_\<sigma> \<sigma>)\<close>
    and \<open>\<alpha>\<sigma>_wit_union x = ordext_union (Rep_\<sigma> \<sigma>)\<close>
    and \<open>\<alpha>\<sigma>_wit_\<sigma>' x = \<sigma>\<sigma>' (Rep_\<sigma> \<sigma>)\<close> for x
        using that unfolding \<alpha>\<sigma>_wit_def apply auto
        by (smt (z3) emptyE r_in_union r_notin_intersection surjective_pairing type_definition.Rep_inverse type_definition_\<sigma>)
      let ?intersection_part = \<open>{urrel . urrel_to_\<omega>rel urrel \<in> ordext_intersection (Rep_\<sigma> \<sigma>)}\<close>
      let ?union_part = \<open>{urrel . (urrel_to_\<omega>rel urrel \<in> ordext_union (Rep_\<sigma> \<sigma>)) \<and>
                             (\<forall> \<sigma>' w . AOT_model_valid_in w (Rep_urrel urrel (\<sigma>\<upsilon> \<sigma>')) \<longleftrightarrow> \<sigma>\<sigma>' (Rep_\<sigma> \<sigma>') = \<sigma>\<sigma>' (Rep_\<sigma> \<sigma>))}\<close>
      have simp0: \<open>urrel_to_\<omega>rel
           (Abs_urrel (\<lambda>u. \<epsilon>\<^sub>\<o> w. case u of \<omega>\<upsilon> x \<Rightarrow> r x w | \<sigma>\<upsilon> x \<Rightarrow> snd (snd (Rep_\<sigma> x)) = snd (snd (Rep_\<sigma> \<sigma>)) | null\<upsilon> null \<Rightarrow> False))
            = r\<close>
        unfolding urrel_to_\<omega>rel_def
        apply (subst Abs_urrel_inverse)
        by (auto simp: AOT_model_proposition_choice_simp)
      let ?\<sigma>_part = \<open>\<lambda> r . Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . case u of (\<omega>\<upsilon> x) \<Rightarrow> r x w | \<sigma>\<upsilon> x \<Rightarrow> \<sigma>\<sigma>' (Rep_\<sigma> x) = \<sigma>\<sigma>' (Rep_\<sigma> \<sigma>) | _ \<Rightarrow> False)\<close>
      have \<sigma>_part_in_union: \<open>?\<sigma>_part r \<in> ?union_part\<close>
        apply (auto simp: simp0 r_in_union)
         apply (subst (asm) Abs_urrel_inverse)
          apply (auto simp: AOT_model_proposition_choice_simp)
        apply (subst Abs_urrel_inverse)
        by (auto simp: AOT_model_proposition_choice_simp)
      have \<sigma>_part_not_in_intersection: \<open>?\<sigma>_part r \<notin> ?intersection_part\<close>
        apply (simp add: urrel_to_\<omega>rel_def)
        apply (subst Abs_urrel_inverse)
        by (auto simp: AOT_model_proposition_choice_simp r_notin_intersection)
      have \<open>\<alpha>\<sigma>_wit (?intersection_part \<union> ?union_part) = \<sigma>\<close> 
      proof (rule \<alpha>\<sigma>wit_eqI)
        show \<open>\<alpha>\<sigma>_wit_intersection (?intersection_part \<union> ?union_part) = ordext_intersection (Rep_\<sigma> \<sigma>)\<close>
          apply (auto simp: \<alpha>\<sigma>_wit_intersection_def)
          by (smt (z3) AOT_model_proposition_choice_simp Abs_urrel_inverse Quotient3_abs_rep \<omega>rel_to_urrel_def \<upsilon>.case(3) \<upsilon>.simps(11) mem_Collect_eq urrel_\<omega>rel_quot)
      next
        {
          fix ordext
          assume ordext_in_union: \<open>ordext \<in> ordext_union (Rep_\<sigma> \<sigma>)\<close>
          have ordext_simp: \<open>urrel_to_\<omega>rel
               (Abs_urrel (\<lambda>u. \<epsilon>\<^sub>\<o> w. case u of \<omega>\<upsilon> x \<Rightarrow> ordext x w | \<sigma>\<upsilon> x \<Rightarrow> snd (snd (Rep_\<sigma> x)) = snd (snd (Rep_\<sigma> \<sigma>)) | null\<upsilon> null \<Rightarrow> False))
              = ordext\<close>
            unfolding urrel_to_\<omega>rel_def
            apply (subst Abs_urrel_inverse)
            by (auto simp: AOT_model_proposition_choice_simp)
          have \<open>\<exists>urrel . (urrel
          \<in>{urrel. urrel_to_\<omega>rel urrel \<in> ordext_intersection (Rep_\<sigma> \<sigma>)} \<union>
            {urrel.
             urrel_to_\<omega>rel urrel \<in> ordext_union (Rep_\<sigma> \<sigma>) \<and>
             (\<forall>\<sigma>' w. AOT_model_valid_in w (Rep_urrel urrel (\<sigma>\<upsilon> \<sigma>')) = (snd (snd (Rep_\<sigma> \<sigma>')) = snd (snd (Rep_\<sigma> \<sigma>))))}) \<and>
            urrel_to_\<omega>rel urrel = ordext\<close>
            apply (rule_tac x=\<open>?\<sigma>_part ordext\<close> in exI)
            apply (auto simp: ordext_simp ordext_in_union)
             apply (subst (asm) Abs_urrel_inverse)
            apply (auto simp: AOT_model_proposition_choice_simp)
             apply (subst Abs_urrel_inverse)
            by (auto simp: AOT_model_proposition_choice_simp)
        } note 0 = this
        show \<open>\<alpha>\<sigma>_wit_union (?intersection_part \<union> ?union_part) = ordext_union (Rep_\<sigma> \<sigma>)\<close>
          apply (auto simp: \<alpha>\<sigma>_wit_union_def)
           apply (simp add: \<open>\<forall>x\<in>fst (Rep_\<sigma> \<sigma>). x \<in> fst (snd (Rep_\<sigma> \<sigma>))\<close>)
          using 0 by blast
      next
        have 1: \<open>\<exists>urrel . urrel \<in> ({urrel. urrel_to_\<omega>rel urrel \<in> fst (Rep_\<sigma> \<sigma>)} \<union>
       {urrel.
        urrel_to_\<omega>rel urrel \<in> fst (snd (Rep_\<sigma> \<sigma>)) \<and>
        (\<forall>\<sigma>' w. AOT_model_valid_in w (Rep_urrel urrel (\<sigma>\<upsilon> \<sigma>')) = (snd (snd (Rep_\<sigma> \<sigma>')) = snd (snd (Rep_\<sigma> \<sigma>))))}) \<and>
urrel_to_\<omega>rel urrel
       \<notin> \<alpha>\<sigma>_wit_intersection
           ({urrel. urrel_to_\<omega>rel urrel \<in> fst (Rep_\<sigma> \<sigma>)} \<union>
            {urrel.
             urrel_to_\<omega>rel urrel \<in> fst (snd (Rep_\<sigma> \<sigma>)) \<and>
             (\<forall>\<sigma>' w. AOT_model_valid_in w (Rep_urrel urrel (\<sigma>\<upsilon> \<sigma>')) = (snd (snd (Rep_\<sigma> \<sigma>')) = snd (snd (Rep_\<sigma> \<sigma>))))}) \<and>
           (\<forall>w \<sigma>'. AOT_model_valid_in w (Rep_urrel urrel (\<sigma>\<upsilon> \<sigma>')) \<longrightarrow> snd (snd (Rep_\<sigma> \<sigma>')) = snd (snd (Rep_\<sigma> \<sigma>)))\<close>
          apply (rule_tac x=\<open>?\<sigma>_part r\<close> in exI)
          using \<sigma>_part_in_union \<sigma>_part_not_in_intersection
          by (smt (verit, del_insts) AOT_model_proposition_choice_simp Abs_urrel_inverse Quotient3_abs_rep UnE UnI2 \<alpha>\<sigma>_wit_intersection_def \<omega>rel_to_urrel_def \<upsilon>.simps(11) \<upsilon>.simps(12) mem_Collect_eq r_notin_intersection simp0 urrel_\<omega>rel_quot)
        {
          fix \<sigma>'
          assume \<open>\<exists>urrel
           \<in>{urrel. urrel_to_\<omega>rel urrel \<in> fst (Rep_\<sigma> \<sigma>)} \<union>
             {urrel.
              urrel_to_\<omega>rel urrel \<in> fst (snd (Rep_\<sigma> \<sigma>)) \<and>
              (\<forall>\<sigma>' w. AOT_model_valid_in w (Rep_urrel urrel (\<sigma>\<upsilon> \<sigma>')) = (snd (snd (Rep_\<sigma> \<sigma>')) = snd (snd (Rep_\<sigma> \<sigma>))))}.
             urrel_to_\<omega>rel urrel
             \<notin> \<alpha>\<sigma>_wit_intersection
                 ({urrel. urrel_to_\<omega>rel urrel \<in> fst (Rep_\<sigma> \<sigma>)} \<union>
                  {urrel.
                   urrel_to_\<omega>rel urrel \<in> fst (snd (Rep_\<sigma> \<sigma>)) \<and>
                   (\<forall>\<sigma>' w. AOT_model_valid_in w (Rep_urrel urrel (\<sigma>\<upsilon> \<sigma>')) = (snd (snd (Rep_\<sigma> \<sigma>')) = snd (snd (Rep_\<sigma> \<sigma>))))}) \<and>
             (\<forall>w \<sigma>. AOT_model_valid_in w (Rep_urrel urrel (\<sigma>\<upsilon> \<sigma>)) \<longrightarrow> snd (snd (Rep_\<sigma> \<sigma>)) = \<sigma>')\<close>
          then obtain urrel where
              A: \<open>urrel \<in> {urrel. urrel_to_\<omega>rel urrel \<in> fst (Rep_\<sigma> \<sigma>)} \<union>
             {urrel.
              urrel_to_\<omega>rel urrel \<in> fst (snd (Rep_\<sigma> \<sigma>)) \<and>
              (\<forall>\<sigma>' w. AOT_model_valid_in w (Rep_urrel urrel (\<sigma>\<upsilon> \<sigma>')) = (snd (snd (Rep_\<sigma> \<sigma>')) = snd (snd (Rep_\<sigma> \<sigma>))))}\<close>
              and B: \<open>urrel_to_\<omega>rel urrel
                           \<notin> \<alpha>\<sigma>_wit_intersection
                               ({urrel. urrel_to_\<omega>rel urrel \<in> fst (Rep_\<sigma> \<sigma>)} \<union>
                                {urrel.
                                 urrel_to_\<omega>rel urrel \<in> fst (snd (Rep_\<sigma> \<sigma>)) \<and>
                                 (\<forall>\<sigma>' w. AOT_model_valid_in w (Rep_urrel urrel (\<sigma>\<upsilon> \<sigma>')) = (snd (snd (Rep_\<sigma> \<sigma>')) = snd (snd (Rep_\<sigma> \<sigma>))))})\<close>
              and C: \<open>\<forall>w \<sigma>. AOT_model_valid_in w (Rep_urrel urrel (\<sigma>\<upsilon> \<sigma>)) \<longrightarrow> snd (snd (Rep_\<sigma> \<sigma>)) = \<sigma>'\<close>
            by blast
          {
            assume \<open>urrel \<in> {urrel. urrel_to_\<omega>rel urrel \<in> fst (Rep_\<sigma> \<sigma>)}\<close>
            hence \<open>urrel_to_\<omega>rel urrel
                           \<in> \<alpha>\<sigma>_wit_intersection
                               ({urrel. urrel_to_\<omega>rel urrel \<in> fst (Rep_\<sigma> \<sigma>)} \<union>
                                {urrel.
                                 urrel_to_\<omega>rel urrel \<in> fst (snd (Rep_\<sigma> \<sigma>)) \<and>
                                 (\<forall>\<sigma>' w. AOT_model_valid_in w (Rep_urrel urrel (\<sigma>\<upsilon> \<sigma>')) = (snd (snd (Rep_\<sigma> \<sigma>')) = snd (snd (Rep_\<sigma> \<sigma>))))})\<close>
              by (simp add: \<alpha>\<sigma>_wit_intersection_def)
          }
          hence \<open>urrel \<in> {urrel.
              urrel_to_\<omega>rel urrel \<in> fst (snd (Rep_\<sigma> \<sigma>)) \<and>
              (\<forall>\<sigma>' w. AOT_model_valid_in w (Rep_urrel urrel (\<sigma>\<upsilon> \<sigma>')) = (snd (snd (Rep_\<sigma> \<sigma>')) = snd (snd (Rep_\<sigma> \<sigma>))))}\<close>
            using A B by fastforce
          moreover have \<open>AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel (\<sigma>\<upsilon> \<sigma>)) \<longrightarrow> snd (snd (Rep_\<sigma> \<sigma>)) = \<sigma>'\<close>
            using C calculation by blast
          ultimately have \<open>\<sigma>' = snd (snd (Rep_\<sigma> \<sigma>))\<close>
            by blast
        } note 2 = this
        show \<open>\<alpha>\<sigma>_wit_\<sigma>' (?intersection_part \<union> ?union_part) = \<sigma>\<sigma>' (Rep_\<sigma> \<sigma>)\<close>
          apply (auto simp: \<alpha>\<sigma>_wit_\<sigma>'_def)
          apply (rule the_equality)
          using 1 apply blast
          using 2 by blast
      qed
      hence \<open>\<exists>urrels . \<alpha>\<sigma>_wit urrels = \<sigma>\<close> by auto
    }
    ultimately have \<open>\<exists>urrels . \<alpha>\<sigma>_wit urrels = \<sigma>\<close>
      using \<sigma>cond_univ by blast
  }
  hence \<open>surj \<alpha>\<sigma>_wit\<close>
    using surjI by metis
  moreover {
    fix a b :: \<open>urrel set\<close> and r s
    assume \<open>\<alpha>\<sigma>_wit a = \<alpha>\<sigma>_wit b\<close>
    hence 0: \<open>{ordext::\<omega> \<Rightarrow> w \<Rightarrow> bool. \<forall>urrel::urrel. urrel_to_\<omega>rel urrel = ordext \<longrightarrow> urrel \<in> (a::urrel set)} = {ordext::\<omega> \<Rightarrow> w \<Rightarrow> bool. \<forall>urrel::urrel. urrel_to_\<omega>rel urrel = ordext \<longrightarrow> urrel \<in> (b::urrel set)}\<close>
      unfolding \<alpha>\<sigma>_wit_def Let_def
      apply (subst (asm) Abs_\<sigma>_inject)
        apply (metis wits_in_\<sigma>set)
       apply (metis wits_in_\<sigma>set)
      by (auto simp: \<alpha>\<sigma>_wit_intersection_def \<alpha>\<sigma>_wit_union_def)
    assume \<open>urrel_to_\<omega>rel s = urrel_to_\<omega>rel r \<Longrightarrow> s \<in> a\<close> for s
    hence \<open>urrel_to_\<omega>rel r \<in> {ordext::\<omega> \<Rightarrow> w \<Rightarrow> bool. \<forall>urrel::urrel. urrel_to_\<omega>rel urrel = ordext \<longrightarrow> urrel \<in> (a::urrel set)}\<close>
      by auto
    hence \<open>urrel_to_\<omega>rel r \<in> {ordext::\<omega> \<Rightarrow> w \<Rightarrow> bool. \<forall>urrel::urrel. urrel_to_\<omega>rel urrel = ordext \<longrightarrow> urrel \<in> (b::urrel set)}\<close>
      using 0 by blast
    moreover assume \<open>urrel_to_\<omega>rel s = urrel_to_\<omega>rel r\<close>
    ultimately have \<open>s \<in> b\<close>
      by blast
  }
  moreover {
    fix a b :: \<open>urrel set\<close> and s r
    assume \<open>\<alpha>\<sigma>_wit a = \<alpha>\<sigma>_wit b\<close>
    hence 0: \<open>{ordext::\<omega> \<Rightarrow> w \<Rightarrow> bool. \<exists>urrel \<in> (a::urrel set). urrel_to_\<omega>rel urrel = ordext} =
              {ordext::\<omega> \<Rightarrow> w \<Rightarrow> bool. \<exists>urrel \<in> (b::urrel set). urrel_to_\<omega>rel urrel = ordext}\<close>
      unfolding \<alpha>\<sigma>_wit_def
      apply (subst (asm) Abs_\<sigma>_inject)
        apply (metis wits_in_\<sigma>set)
       apply (metis wits_in_\<sigma>set)
      by (auto simp: Let_def \<alpha>\<sigma>_wit_intersection_def \<alpha>\<sigma>_wit_union_def)
    assume \<open>s \<in> a\<close>
    hence \<open>urrel_to_\<omega>rel s \<in> {ordext::\<omega> \<Rightarrow> w \<Rightarrow> bool. \<exists>urrel \<in> (a::urrel set). urrel_to_\<omega>rel urrel = ordext}\<close>
      by blast
    moreover assume \<open>urrel_to_\<omega>rel s = urrel_to_\<omega>rel r\<close>
    ultimately have \<open>urrel_to_\<omega>rel r \<in> {ordext::\<omega> \<Rightarrow> w \<Rightarrow> bool. \<exists>urrel \<in> (b::urrel set). urrel_to_\<omega>rel urrel = ordext}\<close>
      using "0" by argo
    hence \<open>\<exists>s. s \<in> b \<and> urrel_to_\<omega>rel s = urrel_to_\<omega>rel r\<close>
      by blast
  }
  ultimately show ?thesis
    by (rule_tac x=\<alpha>\<sigma>_wit in exI) metis
qed

section\<open>Restricted model version\<close>

consts \<alpha>\<sigma>_restr :: \<open>urrel set \<Rightarrow> \<sigma>\<close>

specification (\<alpha>\<sigma>_restr)
  \<alpha>\<sigma>_restr_surj: \<open>surj \<alpha>\<sigma>_restr\<close>
proof -
  obtain \<phi> where \<phi>_def: \<open>\<phi> = (\<lambda> \<sigma> u. \<epsilon>\<^sub>\<o> w. u = \<sigma>\<upsilon> \<sigma>)\<close> by auto
  show ?thesis
  proof (rule_tac x=\<open>\<lambda> x . THE \<sigma> . x = { Abs_urrel (\<phi> \<sigma>) }\<close> in exI;
         rule_tac f=\<open>\<lambda> \<sigma> . { Abs_urrel (\<phi> \<sigma>) }\<close> in surjI)
    have \<open>(\<lambda>u. \<epsilon>\<^sub>\<o> w. u = \<sigma>\<upsilon> x) = (\<lambda>u. \<epsilon>\<^sub>\<o> w. u = \<sigma>\<upsilon> \<sigma>) \<Longrightarrow> x = \<sigma>\<close> for x \<sigma>
      by (metis (mono_tags) \<upsilon>.inject(2) AOT_model_proposition_choice_simp)
    hence \<open>({Abs_urrel (\<phi> x)} = {Abs_urrel (\<phi> \<sigma>)}) = (x = \<sigma>)\<close> for x \<sigma>
      using Abs_urrel_inject[THEN iffD1, of \<open>\<phi> x\<close> \<open>\<phi> \<sigma>\<close>]
      by (simp add: \<phi>_def AOT_model_proposition_choice_simp) blast
    thus \<open>(THE \<sigma>. {Abs_urrel (\<phi> x)} = {Abs_urrel (\<phi> \<sigma>)}) = x\<close> for x
      by simp
  qed
qed

section\<open>Shared for both models\<close>

abbreviation (input) \<alpha>\<sigma> where \<open>\<alpha>\<sigma> \<equiv> \<alpha>\<sigma>_ext\<close> \<comment> \<open>Choose model kind.\<close>
lemmas \<alpha>\<sigma>_surj = \<alpha>\<sigma>_ext_surj

primrec \<kappa>\<upsilon> :: \<open>\<kappa>\<Rightarrow>\<upsilon>\<close> where
  \<open>\<kappa>\<upsilon> (\<omega>\<kappa> x) = \<omega>\<upsilon> x\<close>
| \<open>\<kappa>\<upsilon> (\<alpha>\<kappa> x) = \<sigma>\<upsilon> (\<alpha>\<sigma> x)\<close>
| \<open>\<kappa>\<upsilon> (null\<kappa> x) = null\<upsilon> x\<close>

lemma \<kappa>\<upsilon>_surj: \<open>surj \<kappa>\<upsilon>\<close>
  using \<alpha>\<sigma>_surj by (metis \<kappa>\<upsilon>.simps(1) \<kappa>\<upsilon>.simps(2) \<kappa>\<upsilon>.simps(3) \<upsilon>.exhaust surj_def)

lemma urrel_null_false: assumes \<open>AOT_model_valid_in w (Rep_urrel f (\<kappa>\<upsilon> x))\<close> shows \<open>\<not>is_null\<kappa> x\<close>
   by (metis (mono_tags, lifting) assms Rep_urrel \<kappa>.collapse(3) \<kappa>\<upsilon>.simps(3) mem_Collect_eq)


class AOT_Term =
  fixes AOT_model_denotes :: \<open>'a \<Rightarrow> bool\<close>
  assumes AOT_model_denoting_ex: \<open>\<exists> x . AOT_model_denotes x\<close>
class AOT_IncompleteTerm = AOT_Term +
  assumes AOT_model_nondenoting_ex: \<open>\<exists> x . \<not>AOT_model_denotes x\<close>

instantiation prod :: (AOT_Term, AOT_Term) AOT_Term
begin
definition AOT_model_denotes_prod :: \<open>'a\<times>'b \<Rightarrow> bool\<close> where
  \<open>AOT_model_denotes_prod \<equiv> \<lambda>(x,y) . AOT_model_denotes x \<and> AOT_model_denotes y\<close>
instance proof
  show \<open>\<exists>x::'a\<times>'b. AOT_model_denotes x\<close>
    by (simp add: AOT_model_denotes_prod_def AOT_model_denoting_ex)
qed
end

locale AOT_model_irregular_spec =
  fixes AOT_model_irregular :: \<open>('a \<Rightarrow> \<o>) \<Rightarrow> 'a \<Rightarrow> \<o>\<close>
    and AOT_model_regular :: \<open>'a \<Rightarrow> bool\<close>
    and AOT_model_term_equiv :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes AOT_model_irregular_false: \<open>\<not>AOT_model_valid_in w (AOT_model_irregular \<phi> x)\<close>
    and AOT_model_irregular_equiv:
      \<open>AOT_model_term_equiv x y \<Longrightarrow> AOT_model_irregular \<phi> x = AOT_model_irregular \<phi> y\<close>
    and AOT_model_irregular_eqI:
      \<open>(\<And> x . AOT_model_regular x \<Longrightarrow> \<phi> x = \<psi> x) \<Longrightarrow> AOT_model_irregular \<phi> x = AOT_model_irregular \<psi> x\<close>

class AOT_IndividualTerm = AOT_IncompleteTerm +
  fixes AOT_model_regular :: \<open>'a \<Rightarrow> bool\<close>
  fixes AOT_model_term_equiv :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  fixes AOT_model_irregular :: \<open>('a \<Rightarrow> \<o>) \<Rightarrow> 'a \<Rightarrow> \<o>\<close>
  assumes AOT_model_irregular_nondenoting: \<open>\<not>AOT_model_regular x \<Longrightarrow> \<not>AOT_model_denotes x\<close>
  assumes AOT_model_term_equiv_part_equivp: \<open>equivp AOT_model_term_equiv\<close>
  assumes AOT_model_term_equiv_denotes:
    \<open>AOT_model_term_equiv x y \<Longrightarrow> (AOT_model_denotes x = AOT_model_denotes y)\<close>
  assumes AOT_model_term_equiv_regular:
    \<open>AOT_model_term_equiv x y \<Longrightarrow> (AOT_model_regular x = AOT_model_regular y)\<close>
  assumes AOT_model_irregular:
    \<open>AOT_model_irregular_spec AOT_model_irregular AOT_model_regular AOT_model_term_equiv\<close>

interpretation AOT_model_irregular_spec AOT_model_irregular AOT_model_regular AOT_model_term_equiv
  using AOT_model_irregular .

lemma AOT_model_term_equiv_eps:
  shows "AOT_model_term_equiv (Eps (AOT_model_term_equiv \<kappa>)) \<kappa>"
    and "AOT_model_term_equiv \<kappa> (Eps (AOT_model_term_equiv \<kappa>))"
    and "AOT_model_term_equiv \<kappa> \<kappa>' \<Longrightarrow> (Eps (AOT_model_term_equiv \<kappa>)) = (Eps (AOT_model_term_equiv \<kappa>'))"
  apply (metis AOT_model_term_equiv_part_equivp equivp_def someI_ex)
  apply (metis AOT_model_term_equiv_part_equivp equivp_def someI_ex)
  by (metis AOT_model_term_equiv_part_equivp equivp_def)


typedef 'a rel (\<open><_>\<close>) = \<open>UNIV::('a::AOT_IndividualTerm \<Rightarrow> \<o>) set\<close> ..

setup_lifting type_definition_rel

definition fix_special :: \<open>('a::AOT_IndividualTerm \<Rightarrow> \<o>) \<Rightarrow> ('a \<Rightarrow> \<o>)\<close> where
  "fix_special \<equiv> \<lambda> \<phi> x . if AOT_model_regular x then \<phi> x else AOT_model_irregular \<phi> x"

lemma fix_special_denoting: \<open>AOT_model_denotes x \<Longrightarrow> fix_special \<phi> x = \<phi> x\<close>
  by (meson AOT_model_irregular_nondenoting fix_special_def)
lemma fix_special_non_special: \<open>AOT_model_regular x \<Longrightarrow> fix_special \<phi> x = \<phi> x\<close>
  by (meson AOT_model_irregular_nondenoting fix_special_def)
lemma fix_special_special: \<open>\<not>AOT_model_regular x \<Longrightarrow> fix_special \<phi> x = AOT_model_irregular \<phi> x\<close>
  by (simp add: fix_special_def)

instantiation rel :: (AOT_IndividualTerm) AOT_IncompleteTerm
begin
lift_definition AOT_model_denotes_rel :: \<open><'a> \<Rightarrow> bool\<close> is
  \<open>\<lambda> \<phi> . (\<forall> x y . AOT_model_term_equiv x y \<longrightarrow> \<phi> x = \<phi> y) \<and>
         (\<forall> w x . AOT_model_valid_in w (\<phi> x) \<longrightarrow> AOT_model_denotes x) \<and>
         (\<forall> x . \<not>AOT_model_regular x \<longrightarrow> \<phi> x = AOT_model_irregular \<phi> x)\<close> .
definition AOT_model_term_equiv_rel :: \<open><'a> \<Rightarrow> <'a> \<Rightarrow> bool\<close> where
  \<open>AOT_model_term_equiv_rel \<equiv> \<lambda> f g . AOT_model_denotes f \<and> AOT_model_denotes g \<and> f = g\<close>
definition AOT_model_regular_rel :: \<open><'a> \<Rightarrow> bool\<close> where
  \<open>AOT_model_regular_rel \<equiv> \<lambda> r . True\<close>
instance proof
  have \<open>AOT_model_irregular (fix_special \<phi>) x = AOT_model_irregular \<phi> x\<close> for \<phi> and x :: 'a
    by (rule AOT_model_irregular_eqI) (simp add: fix_special_def)
  thus \<open>\<exists> x :: <'a> . AOT_model_denotes x\<close>
    by (rule_tac x=\<open>Abs_rel (fix_special (\<lambda> x . \<epsilon>\<^sub>\<o> w . False))\<close> in exI; transfer)
       (auto simp: AOT_model_proposition_choice_simp fix_special_def AOT_model_irregular_equiv
                    AOT_model_term_equiv_regular AOT_model_irregular_false)
next
  show \<open>\<exists>x :: <'a> . \<not>AOT_model_denotes x\<close>
    by (rule_tac x=\<open>Abs_rel (\<lambda>x. \<epsilon>\<^sub>\<o> w . True)\<close> in exI)
       (simp add: AOT_model_denotes_rel.abs_eq AOT_model_nondenoting_ex AOT_model_proposition_choice_simp)
qed
end

lemma AOT_model_denotes_Abs_rel_fix_specialI:
  assumes \<open>\<And> x y . AOT_model_term_equiv x y \<Longrightarrow> \<phi> x = \<phi> y\<close>
      and \<open>\<And> w x . AOT_model_valid_in w (\<phi> x) \<Longrightarrow> AOT_model_denotes x\<close>
    shows \<open>AOT_model_denotes (Abs_rel (fix_special \<phi>))\<close>
proof -
  have \<open>\<not> AOT_model_regular x \<Longrightarrow>
         AOT_model_irregular \<phi> x = AOT_model_irregular (\<lambda>x. if AOT_model_regular x then \<phi> x else AOT_model_irregular \<phi> x) x\<close>
    for x
    by (rule AOT_model_irregular_eqI) auto
  thus ?thesis
  unfolding AOT_model_denotes_rel.rep_eq
  using assms by (auto simp: AOT_model_irregular_false Abs_rel_inverse AOT_model_irregular_equiv fix_special_def AOT_model_term_equiv_regular)
qed

lemma AOT_model_term_equiv_rel_equiv:
  assumes \<open>AOT_model_denotes x\<close>
      and \<open>AOT_model_denotes y\<close>
  shows \<open>AOT_model_term_equiv x y = (\<forall> \<Pi> w . AOT_model_denotes \<Pi> \<longrightarrow> AOT_model_valid_in w (Rep_rel \<Pi> x) = AOT_model_valid_in w (Rep_rel \<Pi> y))\<close>
proof
  assume \<open>AOT_model_term_equiv x y\<close>
  thus \<open>\<forall> \<Pi> w . AOT_model_denotes \<Pi> \<longrightarrow> AOT_model_valid_in w (Rep_rel \<Pi> x) = AOT_model_valid_in w (Rep_rel \<Pi> y)\<close>
    by (simp add: AOT_model_denotes_rel.rep_eq)
next
  have 0: \<open>AOT_model_term_equiv x' y' \<Longrightarrow> (AOT_model_denotes x' \<and> AOT_model_term_equiv x' y) = (AOT_model_denotes y' \<and> AOT_model_term_equiv y' y)\<close> for x' y'
    by (metis AOT_model_term_equiv_denotes AOT_model_term_equiv_part_equivp equivp_def)
  assume \<open>\<forall> \<Pi> w . AOT_model_denotes \<Pi> \<longrightarrow> AOT_model_valid_in w (Rep_rel \<Pi> x) = AOT_model_valid_in w (Rep_rel \<Pi> y)\<close>
  moreover have "AOT_model_denotes (Abs_rel (fix_special (\<lambda> x . \<epsilon>\<^sub>\<o> w . AOT_model_denotes x \<and> AOT_model_term_equiv x y)))" (is "AOT_model_denotes ?r")
    by (rule AOT_model_denotes_Abs_rel_fix_specialI)
       (auto simp: 0 AOT_model_denotes_rel.rep_eq Abs_rel_inverse fix_special_def
                   AOT_model_proposition_choice_simp AOT_model_irregular_false)
  ultimately have \<open>AOT_model_valid_in w (Rep_rel ?r x) = AOT_model_valid_in w (Rep_rel ?r y)\<close> for w
    by blast
  thus \<open>AOT_model_term_equiv x y\<close>
    by (simp add: Abs_rel_inverse AOT_model_proposition_choice_simp fix_special_denoting[OF assms(1)] fix_special_denoting[OF assms(2)] assms AOT_model_term_equiv_part_equivp equivp_reflp)
qed

class AOT_UnaryIndividualTerm =
  fixes AOT_model_enc :: \<open>'a \<Rightarrow> <'a::AOT_IndividualTerm> \<Rightarrow> bool\<close>
    and AOT_model_concrete :: \<open>w \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes AOT_model_no_special_nondenoting:
      \<open>AOT_model_regular x\<close>
      and AOT_model_enc_relid:
        \<open>AOT_model_denotes F \<Longrightarrow>
         AOT_model_denotes G \<Longrightarrow>
         (\<And> x . AOT_model_enc x F \<longleftrightarrow> AOT_model_enc x G)
         \<Longrightarrow> F = G\<close>
      and AOT_model_a_objects:
        \<open>\<exists>x . AOT_model_denotes x \<and>
              (\<forall>w. \<not> AOT_model_concrete w x) \<and>
              (\<forall>F. AOT_model_denotes F \<longrightarrow> AOT_model_enc x F = \<phi> F)\<close>
      and AOT_model_contingent:
        \<open>\<exists> x w. AOT_model_concrete w x \<and> \<not> AOT_model_concrete w\<^sub>0 x\<close>
      and AOT_model_nocoder:
        \<open>AOT_model_concrete w x \<Longrightarrow> \<not>AOT_model_enc x F\<close>
      and AOT_model_concrete_equiv:
        \<open>AOT_model_term_equiv x y \<Longrightarrow> AOT_model_concrete w x = AOT_model_concrete w y\<close>
      and AOT_model_concrete_denotes:
        \<open>AOT_model_concrete w x \<Longrightarrow> AOT_model_denotes x\<close>
(* only extended models *)
      and AOT_model_enc_indistinguishable_all:
       \<open>AOT_model_denotes a \<Longrightarrow> \<not>(\<exists> w . AOT_model_concrete w a) \<Longrightarrow>
        AOT_model_denotes b \<Longrightarrow> \<not>(\<exists> w . AOT_model_concrete w b) \<Longrightarrow>
        AOT_model_denotes \<Pi> \<Longrightarrow>
        (\<And> \<Pi>' . AOT_model_denotes \<Pi>' \<Longrightarrow> (\<And> v . AOT_model_valid_in v (Rep_rel \<Pi>' a) = AOT_model_valid_in v (Rep_rel \<Pi>' b))) \<Longrightarrow>
        (\<And> \<Pi>' . AOT_model_denotes \<Pi>' \<Longrightarrow> (\<And> v x . \<exists> w . AOT_model_concrete w x \<Longrightarrow> AOT_model_valid_in v (Rep_rel \<Pi>' x) = AOT_model_valid_in v (Rep_rel \<Pi> x)) \<Longrightarrow> AOT_model_enc a \<Pi>') \<Longrightarrow>
        (\<And> \<Pi>' . AOT_model_denotes \<Pi>' \<Longrightarrow> (\<And> v x . \<exists> w . AOT_model_concrete w x \<Longrightarrow> AOT_model_valid_in v (Rep_rel \<Pi>' x) = AOT_model_valid_in v (Rep_rel \<Pi> x)) \<Longrightarrow> AOT_model_enc b \<Pi>')\<close>
      and AOT_model_enc_indistinguishable_ex:
       \<open>AOT_model_denotes a \<Longrightarrow> \<not>(\<exists> w . AOT_model_concrete w a) \<Longrightarrow>
        AOT_model_denotes b \<Longrightarrow> \<not>(\<exists> w . AOT_model_concrete w b) \<Longrightarrow>
        AOT_model_denotes \<Pi> \<Longrightarrow>
        (\<And> \<Pi>' . AOT_model_denotes \<Pi>' \<Longrightarrow> (\<And> v . AOT_model_valid_in v (Rep_rel \<Pi>' a) = AOT_model_valid_in v (Rep_rel \<Pi>' b))) \<Longrightarrow>
        (\<exists> \<Pi>' . AOT_model_denotes \<Pi>' \<and> AOT_model_enc a \<Pi>' \<and> (\<forall> v x . (\<exists> w . AOT_model_concrete w x) \<longrightarrow> AOT_model_valid_in v (Rep_rel \<Pi>' x) = AOT_model_valid_in v (Rep_rel \<Pi> x))) \<Longrightarrow>
        (\<exists> \<Pi>' . AOT_model_denotes \<Pi>' \<and> AOT_model_enc b \<Pi>' \<and> (\<forall> v x . (\<exists> w . AOT_model_concrete w x) \<longrightarrow> AOT_model_valid_in v (Rep_rel \<Pi>' x) = AOT_model_valid_in v (Rep_rel \<Pi> x)))\<close>
instantiation \<kappa> :: AOT_IndividualTerm
begin
definition AOT_model_term_equiv_\<kappa> :: \<open>\<kappa> \<Rightarrow> \<kappa> \<Rightarrow> bool\<close> where
  \<open>AOT_model_term_equiv_\<kappa> \<equiv> \<lambda> x y . \<kappa>\<upsilon> x = \<kappa>\<upsilon> y\<close>
definition AOT_model_denotes_\<kappa> :: \<open>\<kappa> \<Rightarrow> bool\<close> where
  \<open>AOT_model_denotes_\<kappa> \<equiv> \<lambda> x . \<not>is_null\<kappa> x\<close>
definition AOT_model_regular_\<kappa> :: \<open>\<kappa> \<Rightarrow> bool\<close> where
  \<open>AOT_model_regular_\<kappa> \<equiv> \<lambda> x . True\<close>
definition AOT_model_irregular_\<kappa> :: \<open>(\<kappa> \<Rightarrow> \<o>) \<Rightarrow> \<kappa> \<Rightarrow> \<o>\<close> where
  \<open>AOT_model_irregular_\<kappa> \<equiv> SOME \<phi> . AOT_model_irregular_spec \<phi> AOT_model_regular AOT_model_term_equiv\<close>
instance proof
  show \<open>\<exists>x :: \<kappa>. AOT_model_denotes x\<close>
    by (rule_tac x=\<open>\<omega>\<kappa> undefined\<close> in exI)
       (simp add: AOT_model_denotes_\<kappa>_def)
next
  show \<open>\<exists>x :: \<kappa>. \<not>AOT_model_denotes x\<close>
    by (rule_tac x=\<open>null\<kappa> undefined\<close> in exI)
       (simp add: AOT_model_denotes_\<kappa>_def AOT_model_regular_\<kappa>_def)
next
  show "\<not>AOT_model_regular x \<Longrightarrow> \<not> AOT_model_denotes x" for x :: \<kappa>
    by (simp add: AOT_model_regular_\<kappa>_def)
next
  show \<open>equivp (AOT_model_term_equiv :: \<kappa> \<Rightarrow> \<kappa> \<Rightarrow> bool)\<close>
    by (rule equivpI; rule reflpI exI sympI transpI)
       (simp_all add: AOT_model_term_equiv_\<kappa>_def)
next
  show \<open>AOT_model_term_equiv x y \<Longrightarrow> AOT_model_denotes x = AOT_model_denotes y\<close> for x y :: \<kappa>
    by (metis AOT_model_denotes_\<kappa>_def AOT_model_term_equiv_\<kappa>_def \<kappa>.exhaust_disc \<kappa>\<upsilon>.simps
              \<upsilon>.disc(1) \<upsilon>.disc(3) \<upsilon>.disc(5) \<upsilon>.disc(6) is_\<alpha>\<kappa>_def is_\<omega>\<kappa>_def is_null\<kappa>_def)
next
  show \<open>AOT_model_term_equiv x y \<Longrightarrow> AOT_model_regular x = AOT_model_regular y\<close> for x y :: \<kappa>
    by (simp add: AOT_model_regular_\<kappa>_def)
next
  have "AOT_model_irregular_spec (\<lambda> \<phi> (x :: \<kappa>) .  \<epsilon>\<^sub>\<o> w . False) AOT_model_regular AOT_model_term_equiv"
    by standard (auto simp: AOT_model_proposition_choice_simp)
  thus \<open>AOT_model_irregular_spec (AOT_model_irregular::(\<kappa>\<Rightarrow>\<o>) \<Rightarrow> \<kappa> \<Rightarrow> \<o>) AOT_model_regular AOT_model_term_equiv\<close>
    unfolding AOT_model_irregular_\<kappa>_def by (metis (no_types, lifting) someI_ex)
qed
end


definition rel_to_urrel :: \<open><\<kappa>> \<Rightarrow> urrel\<close> where
  \<open>rel_to_urrel \<equiv> \<lambda> \<Pi> . Abs_urrel (\<lambda> u . Rep_rel \<Pi> (SOME x . \<kappa>\<upsilon> x = u))\<close>
definition urrel_to_rel :: \<open>urrel \<Rightarrow> <\<kappa>>\<close> where
  \<open>urrel_to_rel \<equiv> \<lambda> \<phi> . Abs_rel (\<lambda> x . Rep_urrel \<phi> (\<kappa>\<upsilon> x))\<close>

definition AOT_rel_equiv :: \<open><'a::AOT_IndividualTerm> \<Rightarrow> <'a> \<Rightarrow> bool\<close> where
  "AOT_rel_equiv \<equiv> (\<lambda> x y . AOT_model_denotes x \<and> AOT_model_denotes y \<and> x = y)"

lemma urrel_quotient3: \<open>Quotient3 AOT_rel_equiv rel_to_urrel urrel_to_rel\<close>
proof (rule Quotient3I)
  have \<open>(\<lambda>u. Rep_urrel a (\<kappa>\<upsilon> (SOME x. \<kappa>\<upsilon> x = u))) = (\<lambda>u. Rep_urrel a u)\<close> for a
    by (rule ext) (metis (mono_tags, lifting) \<kappa>\<upsilon>_surj surj_f_inv_f verit_sko_ex')
  thus \<open>rel_to_urrel (urrel_to_rel a) = a\<close> for a
    by (simp add: Abs_rel_inverse rel_to_urrel_def urrel_to_rel_def Rep_urrel_inverse)
next
  show \<open>AOT_rel_equiv (urrel_to_rel a) (urrel_to_rel a)\<close> for a
    unfolding AOT_rel_equiv_def urrel_to_rel_def
    by transfer (simp add: AOT_model_regular_\<kappa>_def AOT_model_denotes_\<kappa>_def
                           AOT_model_term_equiv_\<kappa>_def urrel_null_false)
next
  {
    fix a
    assume \<open>\<forall>w x. AOT_model_valid_in w (a x) \<longrightarrow> \<not> is_null\<kappa> x\<close>
    hence \<open>(\<lambda>u. a (SOME x. \<kappa>\<upsilon> x = u)) \<in> {\<phi>. \<forall>x w. \<not> AOT_model_valid_in w (\<phi> (null\<upsilon> x))}\<close>
      by (simp; metis (mono_tags, lifting) \<kappa>.exhaust_disc \<kappa>\<upsilon>.simps \<upsilon>.disc(1) \<upsilon>.disc(3) \<upsilon>.disc(5)
                                           \<upsilon>.disc(6) is_\<alpha>\<kappa>_def is_\<omega>\<kappa>_def someI_ex)
  } note 1 = this
  {
    fix r s :: \<open>\<kappa> \<Rightarrow> \<o>\<close>
    assume A: \<open>\<forall>x y. AOT_model_term_equiv x y \<longrightarrow> r x = r y\<close>
    assume \<open>\<forall>w x. AOT_model_valid_in w (r x) \<longrightarrow> AOT_model_denotes x\<close>
    hence 2: \<open>(\<lambda>u. r (SOME x. \<kappa>\<upsilon> x = u)) \<in> {\<phi>. \<forall>x w. \<not> AOT_model_valid_in w (\<phi> (null\<upsilon> x))}\<close>
      using 1 AOT_model_denotes_\<kappa>_def by meson
    assume B: \<open>\<forall>x y. AOT_model_term_equiv x y \<longrightarrow> s x = s y\<close>
    assume \<open>\<forall>w x. AOT_model_valid_in w (s x) \<longrightarrow> AOT_model_denotes x\<close>
    hence 3: \<open>(\<lambda>u. s (SOME x. \<kappa>\<upsilon> x = u)) \<in> {\<phi>. \<forall>x w. \<not> AOT_model_valid_in w (\<phi> (null\<upsilon> x))}\<close>
      using 1 AOT_model_denotes_\<kappa>_def by meson
    assume \<open>Abs_urrel (\<lambda>u. r (SOME x. \<kappa>\<upsilon> x = u)) = Abs_urrel (\<lambda>u. s (SOME x. \<kappa>\<upsilon> x = u))\<close>
    hence 4: \<open>r (SOME x. \<kappa>\<upsilon> x = u) = s (SOME x::\<kappa>. \<kappa>\<upsilon> x = u)\<close> for u
      unfolding Abs_urrel_inject[OF 2 3] by metis
    have \<open>r x = s x\<close> for x
      using 4[of \<open>\<kappa>\<upsilon> x\<close>]
      by (metis (mono_tags, lifting) A B AOT_model_term_equiv_\<kappa>_def someI_ex)
    hence \<open>r = s\<close> by auto
  } 
  thus \<open>AOT_rel_equiv r s = (AOT_rel_equiv r r \<and> AOT_rel_equiv s s \<and> rel_to_urrel r = rel_to_urrel s)\<close> for r s
    unfolding AOT_rel_equiv_def rel_to_urrel_def
    by transfer auto
qed

lemma urrel_quotient: \<open>Quotient AOT_rel_equiv rel_to_urrel urrel_to_rel (\<lambda>x y. AOT_rel_equiv x x \<and> rel_to_urrel x = y)\<close>
  using Quotient3_to_Quotient[OF urrel_quotient3] by auto

instantiation \<kappa> :: AOT_UnaryIndividualTerm
begin                          

definition AOT_model_enc_\<kappa> :: \<open>\<kappa> \<Rightarrow> <\<kappa>> \<Rightarrow> bool\<close> where
  \<open>AOT_model_enc_\<kappa> \<equiv> \<lambda> x F . case x of \<alpha>\<kappa> a \<Rightarrow> AOT_model_denotes F \<and> rel_to_urrel F \<in> a | _ \<Rightarrow> False\<close>
primrec AOT_model_concrete_\<kappa> :: \<open>w \<Rightarrow> \<kappa> \<Rightarrow> bool\<close> where
  \<open>AOT_model_concrete_\<kappa> w (\<omega>\<kappa> x) = AOT_model_concrete\<omega> x w\<close>
| \<open>AOT_model_concrete_\<kappa> w (\<alpha>\<kappa> x) = False\<close>
| \<open>AOT_model_concrete_\<kappa> w (null\<kappa> x) = False\<close>

lemma AOT_meta_a_objects_\<kappa>:
  \<open>\<exists>x :: \<kappa>. AOT_model_denotes x \<and>
            (\<forall>w. \<not> AOT_model_concrete w x) \<and>
            (\<forall>F. AOT_model_denotes F \<longrightarrow> AOT_model_enc x F = \<phi> F)\<close> for \<phi>
  apply (rule_tac x=\<open>\<alpha>\<kappa> {f . \<phi> (urrel_to_rel f)}\<close> in exI)
  apply (simp add: AOT_model_enc_\<kappa>_def AOT_model_denotes_\<kappa>_def)
  by (metis (no_types, lifting) AOT_rel_equiv_def Quotient_rep_abs_fold_unmap urrel_quotient)

instance proof
  show \<open>AOT_model_regular x\<close> for x :: \<kappa>
    by (simp add: AOT_model_regular_\<kappa>_def)
next
  fix F G :: \<open><\<kappa>>\<close>
  assume \<open>AOT_model_denotes F\<close>
  moreover assume \<open>AOT_model_denotes G\<close>
  moreover assume \<open>\<And>x. AOT_model_enc x F = AOT_model_enc x G\<close>
  moreover obtain x where \<open>\<forall>G. AOT_model_denotes G \<longrightarrow> AOT_model_enc x G = (F = G)\<close>
    using AOT_meta_a_objects_\<kappa> by blast
  ultimately show \<open>F = G\<close> by blast
next
  show \<open>\<exists>x :: \<kappa>. AOT_model_denotes x \<and>
                 (\<forall>w. \<not> AOT_model_concrete w x) \<and>
                 (\<forall>F. AOT_model_denotes F \<longrightarrow> AOT_model_enc x F = \<phi> F)\<close> for \<phi>
    using AOT_meta_a_objects_\<kappa> .
next
  show \<open>\<exists> (x::\<kappa>) w. AOT_model_concrete w x \<and> \<not> AOT_model_concrete w\<^sub>0 x\<close>
    using AOT_model_concrete_\<kappa>.simps(1) AOT_model_contingent_object by blast
next
  show \<open>AOT_model_concrete w x \<Longrightarrow> \<not> AOT_model_enc x F\<close> for w and x :: \<kappa> and F
    by (metis AOT_model_concrete_\<kappa>.simps(2) AOT_model_enc_\<kappa>_def \<kappa>.case_eq_if \<kappa>.collapse(2))
next
  show \<open>AOT_model_term_equiv x y \<Longrightarrow> AOT_model_concrete w x = AOT_model_concrete w y\<close>
    for x y :: \<kappa> and w
    by (induct x; induct y; auto simp: AOT_model_term_equiv_\<kappa>_def)
next
  show \<open>AOT_model_concrete w x \<Longrightarrow> AOT_model_denotes x\<close> for w and x :: \<kappa>
    by (metis AOT_model_concrete_\<kappa>.simps(3) AOT_model_denotes_\<kappa>_def \<kappa>.collapse(3))
(* Extended models only *)
(* TODO: brush up proof *)
next
  fix \<kappa> \<kappa>' :: \<kappa> and \<Pi> \<Pi>' :: \<open><\<kappa>>\<close> and w :: w
  assume \<open>AOT_model_denotes \<kappa>\<close>
  moreover assume \<open>\<nexists>w. AOT_model_concrete w \<kappa>\<close>
  ultimately obtain a where a_def: \<open>\<alpha>\<kappa> a = \<kappa>\<close>
    by (metis AOT_model_\<omega>_concrete_in_some_world AOT_model_concrete_\<kappa>.simps(1) AOT_model_denotes_\<kappa>_def \<kappa>.discI(3) \<kappa>.exhaust_sel)
  assume \<open>AOT_model_denotes \<kappa>'\<close>
  moreover assume \<open>\<nexists>w. AOT_model_concrete w \<kappa>'\<close>
  ultimately obtain b where b_def: \<open>\<alpha>\<kappa> b = \<kappa>'\<close>
    by (metis AOT_model_\<omega>_concrete_in_some_world AOT_model_concrete_\<kappa>.simps(1) AOT_model_denotes_\<kappa>_def \<kappa>.discI(3) \<kappa>.exhaust_sel)
  assume \<open>AOT_model_denotes \<Pi>' \<Longrightarrow> AOT_model_valid_in w (Rep_rel \<Pi>' \<kappa>) = AOT_model_valid_in w (Rep_rel \<Pi>' \<kappa>')\<close> for \<Pi>' w
  hence \<open>AOT_model_valid_in w (Rep_urrel r (\<kappa>\<upsilon> \<kappa>)) = AOT_model_valid_in w (Rep_urrel r (\<kappa>\<upsilon> \<kappa>'))\<close> for r
    by (metis AOT_rel_equiv_def Abs_rel_inverse Quotient3_rel_rep iso_tuple_UNIV_I urrel_quotient3 urrel_to_rel_def)
  hence \<open>let r = (Abs_urrel (\<lambda> u . \<epsilon>\<^sub>\<o> w . u = \<kappa>\<upsilon> \<kappa>)) in AOT_model_valid_in w (Rep_urrel r (\<kappa>\<upsilon> \<kappa>)) = AOT_model_valid_in w (Rep_urrel r (\<kappa>\<upsilon> \<kappa>'))\<close>
    by presburger
  hence \<alpha>\<sigma>_eq: \<open>\<alpha>\<sigma> a = \<alpha>\<sigma> b\<close>
    unfolding Let_def
    apply (subst (asm) (1 2) Abs_urrel_inverse)
    using AOT_model_proposition_choice_simp a_def b_def by force+
  assume \<Pi>_den: \<open>AOT_model_denotes \<Pi>\<close>
  have \<open>\<exists>r . \<forall> x . Rep_rel \<Pi> (\<omega>\<kappa> x) = Rep_urrel r (\<omega>\<upsilon> x)\<close>
    apply (rule_tac x=\<open>rel_to_urrel \<Pi>\<close> in exI)
    apply auto
    unfolding rel_to_urrel_def
    apply (subst Abs_urrel_inverse)
    apply auto
     apply (metis (mono_tags, lifting) AOT_model_denotes_\<kappa>_def AOT_model_denotes_rel.rep_eq \<kappa>.exhaust_disc \<kappa>\<upsilon>.simps(1) \<kappa>\<upsilon>.simps(2) \<kappa>\<upsilon>.simps(3) \<open>AOT_model_denotes \<Pi>\<close> \<upsilon>.disc(8) \<upsilon>.disc(9) \<upsilon>.distinct(3) is_\<alpha>\<kappa>_def is_\<omega>\<kappa>_def verit_sko_ex')
      by (metis (mono_tags, lifting) AOT_model_denotes_rel.rep_eq AOT_model_term_equiv_\<kappa>_def \<kappa>\<upsilon>.simps(1) \<Pi>_den verit_sko_ex')
  then obtain r where r_prop: \<open>Rep_rel \<Pi> (\<omega>\<kappa> x) = Rep_urrel r (\<omega>\<upsilon> x)\<close> for x by blast
  assume \<open>AOT_model_denotes \<Pi>' \<Longrightarrow>
              (\<And>v x. \<exists>w. AOT_model_concrete w x \<Longrightarrow> AOT_model_valid_in v (Rep_rel \<Pi>' x) = AOT_model_valid_in v (Rep_rel \<Pi> x)) \<Longrightarrow>
              AOT_model_enc \<kappa> \<Pi>'\<close> for \<Pi>'
  hence \<open>AOT_model_denotes \<Pi>' \<Longrightarrow>
              (\<And>v x. AOT_model_valid_in v (Rep_rel \<Pi>' (\<omega>\<kappa> x)) = AOT_model_valid_in v (Rep_rel \<Pi> (\<omega>\<kappa> x))) \<Longrightarrow>
              AOT_model_enc \<kappa> \<Pi>'\<close> for \<Pi>'
    by (metis AOT_model_concrete_\<kappa>.simps(2) AOT_model_concrete_\<kappa>.simps(3) \<kappa>.exhaust_disc is_\<alpha>\<kappa>_def is_\<omega>\<kappa>_def is_null\<kappa>_def)
  hence \<open>(\<And>v x. AOT_model_valid_in v (Rep_urrel r (\<omega>\<upsilon> x)) = AOT_model_valid_in v (Rep_rel \<Pi> (\<omega>\<kappa> x))) \<Longrightarrow>
              r \<in> a\<close> for r
    unfolding a_def[symmetric] AOT_model_enc_\<kappa>_def apply simp
    by (smt (verit, best) AOT_rel_equiv_def Abs_rel_inverse Quotient3_def \<kappa>\<upsilon>.simps(1) iso_tuple_UNIV_I urrel_quotient3 urrel_to_rel_def)
  hence \<open>(\<And>v x. AOT_model_valid_in v (Rep_urrel r' (\<omega>\<upsilon> x)) = AOT_model_valid_in v (Rep_urrel r (\<omega>\<upsilon> x))) \<Longrightarrow>
              r' \<in> a\<close> for r'
    unfolding r_prop.
  hence \<open>\<And>s. urrel_to_\<omega>rel s = urrel_to_\<omega>rel r \<Longrightarrow> s \<in> a\<close>
    by (metis urrel_to_\<omega>rel_def)
  hence 0: \<open>\<And>s. urrel_to_\<omega>rel s = urrel_to_\<omega>rel r \<Longrightarrow> s \<in> b\<close>
    using \<alpha>\<sigma>_eq_ord_exts_all[OF \<alpha>\<sigma>_eq] by blast

  assume \<Pi>'_den: \<open>AOT_model_denotes \<Pi>'\<close>
  assume \<open>\<exists>w. AOT_model_concrete w x \<Longrightarrow> AOT_model_valid_in v (Rep_rel \<Pi>' x) = AOT_model_valid_in v (Rep_rel \<Pi> x)\<close> for v x
  hence \<open>AOT_model_valid_in v (Rep_rel \<Pi>' (\<omega>\<kappa> x)) = AOT_model_valid_in v (Rep_rel \<Pi> (\<omega>\<kappa> x))\<close> for v x
    using AOT_model_\<omega>_concrete_in_some_world AOT_model_concrete_\<kappa>.simps(1) by presburger
  hence \<open>AOT_model_valid_in v (Rep_urrel (rel_to_urrel \<Pi>') (\<omega>\<upsilon> x)) = AOT_model_valid_in v (Rep_urrel r (\<omega>\<upsilon> x))\<close> for v x
    by (smt (verit, best) AOT_rel_equiv_def Abs_rel_inverse Quotient3_def \<Pi>'_den \<kappa>\<upsilon>.simps(1) iso_tuple_UNIV_I r_prop urrel_quotient3 urrel_to_rel_def)
  hence \<open>urrel_to_\<omega>rel (rel_to_urrel \<Pi>') = urrel_to_\<omega>rel r\<close>
    by (metis (full_types) AOT_urrel_\<omega>equiv_def Quotient3_def urrel_\<omega>rel_quot)
  hence \<open>rel_to_urrel \<Pi>' \<in> b\<close> using 0 by blast
  thus \<open>AOT_model_enc \<kappa>' \<Pi>'\<close>
    unfolding b_def[symmetric] AOT_model_enc_\<kappa>_def by (auto simp: \<Pi>'_den)
next
  fix \<kappa> \<kappa>' :: \<kappa> and \<Pi> \<Pi>' :: \<open><\<kappa>>\<close> and w :: w
  assume \<open>AOT_model_denotes \<kappa>\<close>
  moreover assume \<open>\<nexists>w. AOT_model_concrete w \<kappa>\<close>
  ultimately obtain a where a_def: \<open>\<alpha>\<kappa> a = \<kappa>\<close>
    by (metis AOT_model_\<omega>_concrete_in_some_world AOT_model_concrete_\<kappa>.simps(1) AOT_model_denotes_\<kappa>_def \<kappa>.discI(3) \<kappa>.exhaust_sel)
  assume \<open>AOT_model_denotes \<kappa>'\<close>
  moreover assume \<open>\<nexists>w. AOT_model_concrete w \<kappa>'\<close>
  ultimately obtain b where b_def: \<open>\<alpha>\<kappa> b = \<kappa>'\<close>
    by (metis AOT_model_\<omega>_concrete_in_some_world AOT_model_concrete_\<kappa>.simps(1) AOT_model_denotes_\<kappa>_def \<kappa>.discI(3) \<kappa>.exhaust_sel)
  assume \<open>AOT_model_denotes \<Pi>' \<Longrightarrow> AOT_model_valid_in w (Rep_rel \<Pi>' \<kappa>) = AOT_model_valid_in w (Rep_rel \<Pi>' \<kappa>')\<close> for \<Pi>' w
  hence \<open>AOT_model_valid_in w (Rep_urrel r (\<kappa>\<upsilon> \<kappa>)) = AOT_model_valid_in w (Rep_urrel r (\<kappa>\<upsilon> \<kappa>'))\<close> for r
    by (metis AOT_rel_equiv_def Abs_rel_inverse Quotient3_rel_rep iso_tuple_UNIV_I urrel_quotient3 urrel_to_rel_def)
  hence \<open>let r = (Abs_urrel (\<lambda> u . \<epsilon>\<^sub>\<o> w . u = \<kappa>\<upsilon> \<kappa>)) in AOT_model_valid_in w (Rep_urrel r (\<kappa>\<upsilon> \<kappa>)) = AOT_model_valid_in w (Rep_urrel r (\<kappa>\<upsilon> \<kappa>'))\<close>
    by presburger
  hence \<alpha>\<sigma>_eq: \<open>\<alpha>\<sigma> a = \<alpha>\<sigma> b\<close>
    unfolding Let_def
    apply (subst (asm) (1 2) Abs_urrel_inverse)
    using AOT_model_proposition_choice_simp a_def b_def by force+
  assume \<Pi>_den: \<open>AOT_model_denotes \<Pi>\<close>
  have \<open>\<exists>r . \<forall> x . Rep_rel \<Pi> (\<omega>\<kappa> x) = Rep_urrel r (\<omega>\<upsilon> x)\<close>
    apply (rule_tac x=\<open>rel_to_urrel \<Pi>\<close> in exI)
    apply auto
    unfolding rel_to_urrel_def
    apply (subst Abs_urrel_inverse)
    apply auto
     apply (metis (mono_tags, lifting) AOT_model_denotes_\<kappa>_def AOT_model_denotes_rel.rep_eq \<kappa>.exhaust_disc \<kappa>\<upsilon>.simps(1) \<kappa>\<upsilon>.simps(2) \<kappa>\<upsilon>.simps(3) \<open>AOT_model_denotes \<Pi>\<close> \<upsilon>.disc(8) \<upsilon>.disc(9) \<upsilon>.distinct(3) is_\<alpha>\<kappa>_def is_\<omega>\<kappa>_def verit_sko_ex')
    by (metis (mono_tags, lifting) AOT_model_denotes_rel.rep_eq AOT_model_term_equiv_\<kappa>_def \<kappa>\<upsilon>.simps(1) \<Pi>_den verit_sko_ex')
  then obtain r where r_prop: \<open>Rep_rel \<Pi> (\<omega>\<kappa> x) = Rep_urrel r (\<omega>\<upsilon> x)\<close> for x by blast

  assume \<open>\<exists>\<Pi>'. AOT_model_denotes \<Pi>' \<and>
             AOT_model_enc \<kappa> \<Pi>' \<and>
             (\<forall>v x. (\<exists>w. AOT_model_concrete w x) \<longrightarrow> AOT_model_valid_in v (Rep_rel \<Pi>' x) = AOT_model_valid_in v (Rep_rel \<Pi> x))\<close>
  then obtain \<Pi>' where
      \<Pi>'_den: \<open>AOT_model_denotes \<Pi>'\<close> and
      \<kappa>_enc_\<Pi>': \<open>AOT_model_enc \<kappa> \<Pi>'\<close> and
      \<Pi>'_prop: \<open>\<exists>w. AOT_model_concrete w x \<Longrightarrow> AOT_model_valid_in v (Rep_rel \<Pi>' x) = AOT_model_valid_in v (Rep_rel \<Pi> x)\<close> for v x
    by blast
  have \<open>AOT_model_valid_in v (Rep_rel \<Pi>' (\<omega>\<kappa> x)) = AOT_model_valid_in v (Rep_rel \<Pi> (\<omega>\<kappa> x))\<close> for x v
    by (simp add: AOT_model_\<omega>_concrete_in_some_world \<Pi>'_prop)
  hence \<open>AOT_urrel_\<omega>equiv (rel_to_urrel \<Pi>') (rel_to_urrel \<Pi>)\<close>
    unfolding AOT_urrel_\<omega>equiv_def
    by (smt (verit) AOT_rel_equiv_def Abs_rel_inverse Quotient3_def \<Pi>'_den \<Pi>_den \<kappa>\<upsilon>.simps(1) iso_tuple_UNIV_I urrel_quotient3 urrel_to_rel_def)
  have \<open>rel_to_urrel \<Pi>' \<in> a\<close> and \<open>urrel_to_\<omega>rel (rel_to_urrel \<Pi>') = urrel_to_\<omega>rel (rel_to_urrel \<Pi>)\<close>
    apply (metis AOT_model_enc_\<kappa>_def \<kappa>.simps(11) \<kappa>_enc_\<Pi>' a_def)
    by (metis Quotient3_rel \<open>AOT_urrel_\<omega>equiv (rel_to_urrel \<Pi>') (rel_to_urrel \<Pi>)\<close> urrel_\<omega>rel_quot)
  hence \<open>\<exists>s. s \<in> b \<and> urrel_to_\<omega>rel s = urrel_to_\<omega>rel (rel_to_urrel \<Pi>)\<close>
    using \<alpha>\<sigma>_eq_ord_exts_ex[OF \<alpha>\<sigma>_eq] by blast
  then obtain s where s_prop: \<open>s \<in> b \<and> urrel_to_\<omega>rel s = urrel_to_\<omega>rel (rel_to_urrel \<Pi>)\<close>
    by blast
  then obtain \<Pi>'' where \<Pi>''_prop: \<open>rel_to_urrel \<Pi>'' = s\<close> and \<Pi>''_den: \<open>AOT_model_denotes \<Pi>''\<close>
    by (metis AOT_rel_equiv_def Quotient3_def urrel_quotient3)
  moreover have \<open>AOT_model_enc \<kappa>' \<Pi>''\<close>
    by (metis AOT_model_enc_\<kappa>_def \<Pi>''_den \<Pi>''_prop \<kappa>.simps(11) b_def s_prop)
  moreover have \<open>(\<exists>w. AOT_model_concrete w x) \<Longrightarrow> AOT_model_valid_in v (Rep_rel \<Pi>'' x) = AOT_model_valid_in v (Rep_rel \<Pi> x)\<close> for v x
  proof -
    assume \<open>\<exists>w. AOT_model_concrete w x\<close>
    then obtain u where x_def: \<open>x = \<omega>\<kappa> u\<close>
      by (metis AOT_model_concrete_\<kappa>.simps(2) AOT_model_concrete_\<kappa>.simps(3) \<kappa>.exhaust)
    show \<open>AOT_model_valid_in v (Rep_rel \<Pi>'' x) = AOT_model_valid_in v (Rep_rel \<Pi> x)\<close>
      unfolding x_def
      by (smt (verit, best) AOT_rel_equiv_def Abs_rel_inverse Quotient3_def \<Pi>''_den \<Pi>''_prop \<Pi>_den \<kappa>\<upsilon>.simps(1) iso_tuple_UNIV_I s_prop urrel_quotient3 urrel_to_\<omega>rel_def urrel_to_rel_def)
  qed
  ultimately show \<open>\<exists>\<Pi>'. AOT_model_denotes \<Pi>' \<and>
             AOT_model_enc \<kappa>' \<Pi>' \<and>
             (\<forall>v x. (\<exists>w. AOT_model_concrete w x) \<longrightarrow> AOT_model_valid_in v (Rep_rel \<Pi>' x) = AOT_model_valid_in v (Rep_rel \<Pi> x))\<close>
    apply (rule_tac x=\<Pi>'' in exI)
    by auto
qed
end

instantiation prod :: (AOT_UnaryIndividualTerm, AOT_IndividualTerm) AOT_IndividualTerm
begin
definition AOT_model_regular_prod :: \<open>'a\<times>'b \<Rightarrow> bool\<close> where
  \<open>AOT_model_regular_prod \<equiv> \<lambda> (x,y) . (AOT_model_regular x \<and> AOT_model_regular y \<and> (AOT_model_denotes x \<or> AOT_model_denotes y))\<close>
definition AOT_model_term_equiv_prod :: \<open>'a\<times>'b \<Rightarrow> 'a\<times>'b \<Rightarrow> bool\<close> where
  \<open>AOT_model_term_equiv_prod \<equiv>  \<lambda> (x\<^sub>1,y\<^sub>1) (x\<^sub>2,y\<^sub>2) . (AOT_model_term_equiv x\<^sub>1 x\<^sub>2 \<and> AOT_model_term_equiv y\<^sub>1 y\<^sub>2)\<close>
function AOT_model_irregular_prod :: \<open>('a\<times>'b \<Rightarrow> \<o>) \<Rightarrow> 'a\<times>'b \<Rightarrow> \<o>\<close> where
  AOT_model_irregular_proj2: "AOT_model_denotes x \<and> \<not>AOT_model_denotes y \<Longrightarrow>
    AOT_model_irregular \<phi> (x,y) = AOT_model_irregular (\<lambda>y. \<phi> (SOME x' . AOT_model_term_equiv x x', y)) y"
| AOT_model_irregular_proj1: "\<not>AOT_model_denotes x \<and> AOT_model_denotes y \<Longrightarrow>
    AOT_model_irregular \<phi> (x,y) = AOT_model_irregular (\<lambda>x. \<phi> (x, SOME y' . AOT_model_term_equiv y y')) x"
| AOT_model_irregular_prod_generic: "AOT_model_denotes x = AOT_model_denotes y \<Longrightarrow>
    AOT_model_irregular \<phi> (x,y) = (SOME \<Phi> . AOT_model_irregular_spec \<Phi> AOT_model_regular AOT_model_term_equiv) \<phi> (x,y)"
  by auto blast
termination using "termination" by blast

instance proof
  obtain x :: 'a and y :: 'b where \<open>\<not>AOT_model_denotes x\<close> and \<open>\<not>AOT_model_denotes y\<close>
    by (meson AOT_model_nondenoting_ex AOT_model_denoting_ex)
  thus \<open>\<exists>x::'a\<times>'b. \<not>AOT_model_denotes x\<close>
    by (auto simp: AOT_model_denotes_prod_def AOT_model_regular_prod_def)
next
  show \<open>equivp (AOT_model_term_equiv :: 'a\<times>'b \<Rightarrow> 'a\<times>'b \<Rightarrow> bool)\<close>
    by (rule equivpI; rule reflpI sympI transpI;
        simp add: AOT_model_term_equiv_prod_def AOT_model_term_equiv_part_equivp
                  equivp_reflp prod.case_eq_if case_prod_unfold equivp_symp)
       (metis equivp_transp[OF AOT_model_term_equiv_part_equivp])
next
  show \<open>\<not>AOT_model_regular x \<Longrightarrow> \<not> AOT_model_denotes x\<close> for x :: \<open>'a\<times>'b\<close>
    by (metis (mono_tags, lifting) AOT_model_denotes_prod_def AOT_model_irregular_nondenoting
                                   AOT_model_regular_prod_def case_prod_unfold)
next
  show \<open>AOT_model_term_equiv x y \<Longrightarrow> AOT_model_denotes x = AOT_model_denotes y\<close> for x y :: \<open>'a\<times>'b\<close>
    by (metis (mono_tags, lifting) AOT_model_denotes_prod_def AOT_model_term_equiv_denotes
                                   AOT_model_term_equiv_prod_def case_prod_beta)
next
  show \<open>AOT_model_term_equiv x y \<Longrightarrow> AOT_model_regular x = AOT_model_regular y\<close> for x y :: \<open>'a\<times>'b\<close>
    by (induct x; induct y; simp add: AOT_model_term_equiv_prod_def AOT_model_regular_prod_def)
       (meson AOT_model_term_equiv_denotes AOT_model_term_equiv_regular)
next
  interpret sp: AOT_model_irregular_spec \<open>\<lambda>\<phi> (x::'a\<times>'b) . \<epsilon>\<^sub>\<o> w . False\<close> AOT_model_regular AOT_model_term_equiv
    by (simp add: AOT_model_irregular_spec_def AOT_model_proposition_choice_simp)
  have ex_spec: "\<exists> \<phi> :: ('a\<times>'b \<Rightarrow> \<o>) \<Rightarrow> 'a\<times>'b \<Rightarrow> \<o> . AOT_model_irregular_spec \<phi> AOT_model_regular AOT_model_term_equiv"
    using sp.AOT_model_irregular_spec_axioms by blast
  have some_spec: \<open>AOT_model_irregular_spec
    (SOME \<phi> :: ('a\<times>'b \<Rightarrow> \<o>) \<Rightarrow> 'a\<times>'b \<Rightarrow> \<o> . AOT_model_irregular_spec \<phi> AOT_model_regular AOT_model_term_equiv)
    AOT_model_regular AOT_model_term_equiv\<close>
    using someI_ex[OF ex_spec] by argo
  interpret sp_some: AOT_model_irregular_spec
    \<open>SOME \<phi> :: ('a\<times>'b \<Rightarrow> \<o>) \<Rightarrow> 'a\<times>'b \<Rightarrow> \<o> . AOT_model_irregular_spec \<phi> AOT_model_regular AOT_model_term_equiv\<close>
    AOT_model_regular AOT_model_term_equiv
    using some_spec by blast
  show \<open>AOT_model_irregular_spec (AOT_model_irregular :: ('a\<times>'b \<Rightarrow> \<o>) \<Rightarrow> 'a\<times>'b \<Rightarrow> \<o>) AOT_model_regular AOT_model_term_equiv\<close>
  proof
    have \<open>\<not>AOT_model_valid_in w (AOT_model_irregular \<phi> (a, b))\<close> for w \<phi> and a :: 'a and b :: 'b
      by (induct arbitrary: \<phi> rule: AOT_model_irregular_prod.induct)
         (auto simp: AOT_model_irregular_false sp_some.AOT_model_irregular_false)
    thus "\<not>AOT_model_valid_in w (AOT_model_irregular \<phi> x)" for w \<phi> and x :: \<open>'a\<times>'b\<close>
      by (induct x)
  next
    {
      fix x\<^sub>1 y\<^sub>1 :: 'a and x\<^sub>2 y\<^sub>2 :: 'b and \<phi> :: \<open>'a\<times>'b\<Rightarrow>\<o>\<close>
      assume x\<^sub>1y\<^sub>1_equiv: \<open>AOT_model_term_equiv x\<^sub>1 y\<^sub>1\<close>
      moreover assume x\<^sub>2y\<^sub>2_equiv: \<open>AOT_model_term_equiv x\<^sub>2 y\<^sub>2\<close>
      ultimately have xy_equiv: \<open>AOT_model_term_equiv (x\<^sub>1,x\<^sub>2) (y\<^sub>1,y\<^sub>2)\<close>
        by (simp add: AOT_model_term_equiv_prod_def)
      {
        assume \<open>AOT_model_denotes x\<^sub>1 \<and> AOT_model_denotes x\<^sub>2\<close>
        moreover hence \<open>AOT_model_denotes y\<^sub>1 \<and> AOT_model_denotes y\<^sub>2\<close>
          by (meson AOT_model_term_equiv_denotes x\<^sub>1y\<^sub>1_equiv x\<^sub>2y\<^sub>2_equiv)
        ultimately have \<open>AOT_model_irregular \<phi> (x\<^sub>1,x\<^sub>2) = AOT_model_irregular \<phi> (y\<^sub>1,y\<^sub>2)\<close>
          by (simp add: sp_some.AOT_model_irregular_equiv xy_equiv)
      }
      moreover {
        assume \<open>~AOT_model_denotes x\<^sub>1 \<and> ~AOT_model_denotes x\<^sub>2\<close>
        moreover hence \<open>~AOT_model_denotes y\<^sub>1 \<and> ~AOT_model_denotes y\<^sub>2\<close>
          by (meson AOT_model_term_equiv_denotes x\<^sub>1y\<^sub>1_equiv x\<^sub>2y\<^sub>2_equiv)
        ultimately have \<open>AOT_model_irregular \<phi> (x\<^sub>1,x\<^sub>2) = AOT_model_irregular \<phi> (y\<^sub>1,y\<^sub>2)\<close>
          by (simp add: sp_some.AOT_model_irregular_equiv xy_equiv)
      }
      moreover {
        assume denotes_x: \<open>AOT_model_denotes x\<^sub>1 \<and> \<not>AOT_model_denotes x\<^sub>2\<close>
        hence denotes_y: \<open>AOT_model_denotes y\<^sub>1 \<and> \<not>AOT_model_denotes y\<^sub>2\<close>
          by (meson AOT_model_term_equiv_denotes x\<^sub>1y\<^sub>1_equiv x\<^sub>2y\<^sub>2_equiv)
        have eps_eq: \<open>Eps (AOT_model_term_equiv x\<^sub>1) = Eps (AOT_model_term_equiv y\<^sub>1)\<close>
          by (simp add: AOT_model_term_equiv_eps(3) x\<^sub>1y\<^sub>1_equiv)
        have \<open>AOT_model_irregular \<phi> (x\<^sub>1,x\<^sub>2) = AOT_model_irregular \<phi> (y\<^sub>1,y\<^sub>2)\<close>
          using denotes_x denotes_y by (auto simp: x\<^sub>2y\<^sub>2_equiv eps_eq AOT_model_irregular_equiv)
      }
      moreover {
        assume denotes_x: \<open>\<not>AOT_model_denotes x\<^sub>1 \<and> AOT_model_denotes x\<^sub>2\<close>
        hence denotes_y: \<open>\<not>AOT_model_denotes y\<^sub>1 \<and> AOT_model_denotes y\<^sub>2\<close>
          by (meson AOT_model_term_equiv_denotes x\<^sub>1y\<^sub>1_equiv x\<^sub>2y\<^sub>2_equiv)
        have eps_eq: \<open>Eps (AOT_model_term_equiv x\<^sub>2) = Eps (AOT_model_term_equiv y\<^sub>2)\<close>
          by (simp add: AOT_model_term_equiv_eps(3) x\<^sub>2y\<^sub>2_equiv)
        have \<open>AOT_model_irregular \<phi> (x\<^sub>1,x\<^sub>2) = AOT_model_irregular \<phi> (y\<^sub>1,y\<^sub>2)\<close>
          using denotes_x denotes_y
          by (auto simp: x\<^sub>1y\<^sub>1_equiv eps_eq AOT_model_irregular_equiv)
      }
      ultimately have \<open>AOT_model_irregular \<phi> (x\<^sub>1,x\<^sub>2) = AOT_model_irregular \<phi> (y\<^sub>1,y\<^sub>2)\<close> by blast
    } note 0 = this
    show \<open>AOT_model_term_equiv x y \<Longrightarrow> AOT_model_irregular \<phi> x = AOT_model_irregular \<phi> y\<close>
      for x y :: \<open>'a\<times>'b\<close> and \<phi>
      by (induct x; induct y; simp add: AOT_model_term_equiv_prod_def 0)
  next
    fix \<phi> \<psi> :: \<open>'a\<times>'b \<Rightarrow> \<o>\<close>
    assume \<open>AOT_model_regular x \<Longrightarrow> \<phi> x = \<psi> x\<close> for x
    hence \<open>AOT_model_regular x \<and> AOT_model_regular y \<and> (AOT_model_denotes x \<or> AOT_model_denotes y) \<Longrightarrow> \<phi> (x, y) = \<psi> (x, y)\<close> for x y
      unfolding AOT_model_regular_prod_def by simp
    hence \<open>AOT_model_irregular \<phi> (x,y) = AOT_model_irregular \<psi> (x,y)\<close> for x :: 'a and y :: 'b
    proof (induct arbitrary: \<psi> \<phi> rule: AOT_model_irregular_prod.induct)
      case (1 x y \<phi>)
      thus ?case
        apply simp
        by (meson AOT_model_irregular_eqI AOT_model_irregular_nondenoting AOT_model_term_equiv_denotes AOT_model_term_equiv_eps(1))
    next
      case (2 x y \<phi>)
      thus ?case
        apply simp
        by (meson AOT_model_irregular_nondenoting AOT_model_no_special_nondenoting AOT_model_term_equiv_denotes AOT_model_term_equiv_eps(2))
    next
      case (3 x y \<phi>)
      thus ?case
        apply simp
        by (metis (mono_tags, lifting) AOT_model_regular_prod_def case_prod_conv sp_some.AOT_model_irregular_eqI surj_pair)
    qed
    thus \<open>AOT_model_irregular \<phi> x = AOT_model_irregular \<psi> x\<close> for  x :: \<open>'a\<times>'b\<close>
      by (metis surjective_pairing)
  qed
qed
end

lemma AOT_meta_prod_equivI:
  shows "\<And> (a::'a::AOT_UnaryIndividualTerm) x (y :: 'b::AOT_IndividualTerm) . AOT_model_term_equiv x y \<Longrightarrow> AOT_model_term_equiv (a,x) (a,y)"
    and "\<And> (x::'a::AOT_UnaryIndividualTerm) y (b :: 'b::AOT_IndividualTerm) . AOT_model_term_equiv x y \<Longrightarrow> AOT_model_term_equiv (x,b) (y,b)"
    unfolding AOT_model_term_equiv_prod_def
    by (simp add: AOT_model_term_equiv_part_equivp equivp_reflp)+


instantiation unit :: AOT_Term
begin
definition AOT_model_denotes_unit :: \<open>unit \<Rightarrow> bool\<close> where \<open>AOT_model_denotes_unit \<equiv> \<lambda>_. True\<close>
instance proof
  show \<open>\<exists>x::unit. AOT_model_denotes x\<close>
    by (simp add: AOT_model_denotes_unit_def)
qed
end

instantiation \<o> :: AOT_Term
begin
definition AOT_model_denotes_\<o> :: \<open>\<o> \<Rightarrow> bool\<close> where \<open>AOT_model_denotes_\<o> \<equiv> \<lambda>_. True\<close>
instance proof
  show \<open>\<exists>x::\<o>. AOT_model_denotes x\<close>
    by (simp add: AOT_model_denotes_\<o>_def)
qed
end

typedef (overloaded) 'a AOT_var = \<open>{ x :: 'a::AOT_Term . AOT_model_denotes x }\<close>
  morphisms AOT_term_of_var AOT_var_of_term
  by (simp add: AOT_model_denoting_ex)

declare AOT_var_of_term_induct[induct del]
        AOT_var_of_term_cases[cases del]
        AOT_term_of_var_induct[induct del]
        AOT_term_of_var_cases[cases del]

lemmas AOT_var_of_term_inverse = AOT_var_of_term_inverse[simplified]
   and AOT_var_of_term_inject = AOT_var_of_term_inject[simplified]
   and AOT_var_of_term_induct = AOT_var_of_term_induct[simplified, induct type: AOT_var]
   and AOT_var_of_term_cases = AOT_var_of_term_cases[simplified, cases type: AOT_var]
   and AOT_term_of_var = AOT_term_of_var[simplified]
   and AOT_term_of_var_cases = AOT_term_of_var_cases[simplified, induct pred: AOT_term_of_var]
   and AOT_term_of_var_induct = AOT_term_of_var_induct[simplified, induct pred: AOT_term_of_var]
   and AOT_term_of_var_inverse = AOT_term_of_var_inverse[simplified]
   and AOT_term_of_var_inject = AOT_term_of_var_inject[simplified]

consts AOT_model_equiv_def :: \<open>\<o> \<Rightarrow> \<o> \<Rightarrow> bool\<close>
specification(AOT_model_equiv_def)
  AOT_model_equiv_def: \<open>AOT_model_equiv_def \<phi> \<psi> = (\<forall> v . AOT_model_valid_in v \<phi> = AOT_model_valid_in v \<psi>)\<close>
  by (rule_tac x=\<open>\<lambda> \<phi> \<psi> . \<forall> v . AOT_model_valid_in v \<phi> = AOT_model_valid_in v \<psi>\<close> in exI) simp

consts AOT_model_id_def :: \<open>('b \<Rightarrow> 'a::AOT_Term) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool\<close>
specification(AOT_model_id_def)
  AOT_model_id_def: \<open>(AOT_model_id_def \<tau> \<sigma>) = (\<forall> \<alpha> . if AOT_model_denotes (\<sigma> \<alpha>) then \<tau> \<alpha> = \<sigma> \<alpha> else \<not>AOT_model_denotes (\<tau> \<alpha>))\<close>
  by (rule_tac x="\<lambda> \<tau> \<sigma> . \<forall> \<alpha> . if AOT_model_denotes (\<sigma> \<alpha>) then \<tau> \<alpha> = \<sigma> \<alpha> else \<not>AOT_model_denotes (\<tau> \<alpha>)" in exI)
     blast

definition AOT_model_nondenoting :: \<open>'a::AOT_IncompleteTerm\<close> where
  \<open>AOT_model_nondenoting \<equiv> SOME \<tau> . \<not>AOT_model_denotes \<tau>\<close>
lemma AOT_model_nondenoing: \<open>\<not>AOT_model_denotes (AOT_model_nondenoting)\<close>
  using someI_ex[OF AOT_model_nondenoting_ex] unfolding AOT_model_nondenoting_def by blast

definition AOT_model_axiom where "AOT_model_axiom \<equiv> \<lambda> \<phi> . \<forall> v . AOT_model_valid_in v \<phi>"
definition AOT_model_act_axiom where "AOT_model_act_axiom \<equiv> \<lambda> \<phi> . AOT_model_valid_in w\<^sub>0 \<phi>"

lemma AOT_model_axiomI: assumes \<open>\<And>v . AOT_model_valid_in v \<phi>\<close> shows \<open>AOT_model_axiom \<phi>\<close>
  unfolding AOT_model_axiom_def using assms ..

lemma AOT_model_act_axiomI: assumes \<open>AOT_model_valid_in w\<^sub>0 \<phi>\<close> shows \<open>AOT_model_act_axiom \<phi>\<close>
  unfolding AOT_model_act_axiom_def using assms .

end
