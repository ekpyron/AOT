(*<*)
theory AOT_model               
  imports Main "HOL-Cardinals.Bounded_Set"
begin                           

declare[[typedef_overloaded]]
(*>*)

section\<open>Model for the Logic of AOT\<close>

text\<open>We introduce a primitive type for hyperintensional propositions.\<close>
typedecl \<o>

text\<open>To be able to model modal operators following Kripke semantics,
     we introduce a primitive type for possible worlds and assert, by axiom,
     that there is a surjective function mapping propositions to the
     boolean-valued functions acting on possible worlds. We call the result
     of applying this function to a proposition the Kripke-extension
     of the proposition.\<close>
typedecl w \<comment>\<open>The primtive type of possible worlds.\<close>
axiomatization AOT_model_d\<o> :: \<open>\<o>\<Rightarrow>(w\<Rightarrow>bool)\<close> where
  d\<o>_surj: \<open>surj AOT_model_d\<o>\<close>

text\<open>The axioms of PLM require the existence of a non-actual world.\<close>
consts w\<^sub>0 :: w \<comment>\<open>The designated actual world.\<close>
axiomatization where AOT_model_nonactual_world: \<open>\<exists>w . w \<noteq> w\<^sub>0\<close>

text\<open>Validity of a proposition in a given world can now be modelled as the result
     of applying that world to the Kripke-extension of the proposition.\<close>
definition AOT_model_valid_in :: \<open>w\<Rightarrow>\<o>\<Rightarrow>bool\<close> where
  \<open>AOT_model_valid_in w \<phi> \<equiv> AOT_model_d\<o> \<phi> w\<close>

text\<open>By construction, we can choose a proposition for any given Kripke-extension,
     s.t. the proposition is valid in a possible world iff the Kripke-extension
     evaluates to true at that world.\<close>
definition AOT_model_proposition_choice :: \<open>(w\<Rightarrow>bool) \<Rightarrow> \<o>\<close> (binder \<open>\<epsilon>\<^sub>\<o> \<close> 8)
  where \<open>\<epsilon>\<^sub>\<o> w. \<phi> w \<equiv> (inv AOT_model_d\<o>) \<phi>\<close>
lemma AOT_model_proposition_choice_simp: \<open>AOT_model_valid_in w (\<epsilon>\<^sub>\<o> w. \<phi> w) = \<phi> w\<close>
  by (simp add: surj_f_inv_f[OF d\<o>_surj] AOT_model_valid_in_def
                AOT_model_proposition_choice_def)

text\<open>Nitpick can trivially show that there are models for the axioms above.\<close>
lemma \<open>True\<close> nitpick[satisfy, user_axioms, expect = genuine] ..

typedecl \<omega> \<comment>\<open>The primtive type of ordinary objects/urelements.\<close>

typedecl \<sigma>'
datatype \<sigma> = \<sigma>'\<sigma> \<sigma>' | number\<sigma> nat

typedecl null \<comment> \<open>Null-Urelements representing non-denoting terms.\<close>

datatype \<upsilon> = \<omega>\<upsilon> \<omega> | \<sigma>\<upsilon> \<sigma> | is_null\<upsilon>: null\<upsilon> null \<comment> \<open>Type of Urelements\<close>

text\<open>Urrelations are proposition-valued functions on Urelements.
     Urrelations are required to evaluate to necessarily false propositions for
     Null-Urelements (note that there may be several distinct necessarily false
     propositions).\<close>
typedef urrel = \<open>{ \<phi> . \<forall> x w . \<not>AOT_model_valid_in w (\<phi> (null\<upsilon> x)) }\<close>
  by (rule exI[where x=\<open>\<lambda> x . (\<epsilon>\<^sub>\<o> w . \<not>is_null\<upsilon> x)\<close>])
     (auto simp: AOT_model_proposition_choice_simp)

definition finite_card :: \<open>'a set \<Rightarrow> nat option\<close> where
  \<open>finite_card \<equiv> \<lambda> set . if finite set then Some (card set) else None\<close>

definition relcount :: \<open>urrel set \<Rightarrow> nat option\<close> where
  \<open>relcount \<equiv> \<lambda> rels .
    if \<exists>n . \<forall> rel \<in> rels . finite_card { u . AOT_model_valid_in w\<^sub>0 (Rep_urrel rel u)} = Some n
    then Some (THE n . \<forall> rel \<in> rels . finite_card { u . AOT_model_valid_in w\<^sub>0 (Rep_urrel rel u)} = Some n)
    else None\<close>

definition model_number :: \<open>nat \<Rightarrow> urrel set\<close> where
  \<open>model_number \<equiv> \<lambda> n . { rel . finite_card {u . AOT_model_valid_in w\<^sub>0 (Rep_urrel rel u)} = Some n}\<close>

text\<open>For simple models that do not validate extended relation comprehension,
     the mapping from abstract objects to urelements is merely required to be
     surjective and a suitable such mapping can be constructed for any choice of
     a type @{typ \<sigma>}.\<close>
consts \<alpha>\<sigma> :: \<open>urrel set \<Rightarrow> \<sigma>\<close>

lemma Aux1:
  assumes \<open>{x} = {rel. finite_card {u. AOT_model_valid_in w\<^sub>0 (Rep_urrel rel u)} = Some n}\<close>
  shows \<open>False\<close>
proof -
  have bij1: \<open>bij_betw (\<lambda>n . \<sigma>\<upsilon> (number\<sigma> n)) {0..<n}
    {u. AOT_model_valid_in w\<^sub>0 (\<epsilon>\<^sub>\<o> w. if w = w\<^sub>0 then case u of \<sigma>\<upsilon> (\<sigma>'\<sigma> \<sigma>') \<Rightarrow> False | \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False else False)}\<close>
    unfolding bij_betw_def
    apply auto
    apply (meson \<sigma>.inject(2) \<upsilon>.inject(2) inj_onI)
     apply (simp add: AOT_model_proposition_choice_simp)
    apply (simp add: image_def AOT_model_proposition_choice_simp)
    by (metis \<sigma>.exhaust \<sigma>.simps(5) \<sigma>.simps(6) \<upsilon>.case_eq_if \<upsilon>.sel(2) atLeastLessThan_iff is_\<sigma>\<upsilon>_def zero_le)

  have bij2: \<open>bij_betw (\<lambda>n . \<sigma>\<upsilon> (number\<sigma> n)) {0..<n}
    {u. AOT_model_valid_in w\<^sub>0 (\<epsilon>\<^sub>\<o> w. if w = w\<^sub>0 then case u of \<sigma>\<upsilon> (\<sigma>'\<sigma> \<sigma>') \<Rightarrow> False | \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False else \<not>is_null\<upsilon> u)}\<close>
    unfolding bij_betw_def
    apply auto
    apply (meson \<sigma>.inject(2) \<upsilon>.inject(2) inj_onI)
     apply (simp add: AOT_model_proposition_choice_simp)
    apply (simp add: image_def AOT_model_proposition_choice_simp)
    by (metis \<sigma>.exhaust \<sigma>.simps(5) \<sigma>.simps(6) \<upsilon>.case_eq_if \<upsilon>.sel(2) atLeastLessThan_iff is_\<sigma>\<upsilon>_def zero_le)

  have \<open>card {u. AOT_model_valid_in w\<^sub>0 (\<epsilon>\<^sub>\<o> w. if w = w\<^sub>0 then case u of \<sigma>\<upsilon> (\<sigma>'\<sigma> \<sigma>') \<Rightarrow> False | \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False else False)} = n\<close>
    by (metis (no_types, lifting) atLeast0LessThan bij1 bij_betw_same_card card_lessThan)
  moreover have \<open>finite {u. AOT_model_valid_in w\<^sub>0 (\<epsilon>\<^sub>\<o> w. if w = w\<^sub>0 then case u of \<sigma>\<upsilon> (\<sigma>'\<sigma> \<sigma>') \<Rightarrow> False | \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False else False)}\<close>
    using bij_betw_finite bij1 by blast
  ultimately have 1: \<open>finite_card {u. AOT_model_valid_in w\<^sub>0 (Rep_urrel (Abs_urrel (\<lambda> u . \<epsilon>\<^sub>\<o> w . if w = w\<^sub>0 then case u of \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False else False)) u)} = Some n\<close>
    by (auto simp: Abs_urrel_inverse AOT_model_proposition_choice_simp finite_card_def)
  hence 1: \<open>(Abs_urrel (\<lambda> u . \<epsilon>\<^sub>\<o> w . if w = w\<^sub>0 then case u of \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False else False)) = x\<close>
    using assms by blast

  have \<open>card {u. AOT_model_valid_in w\<^sub>0 (\<epsilon>\<^sub>\<o> w. if w = w\<^sub>0 then case u of \<sigma>\<upsilon> (\<sigma>'\<sigma> \<sigma>') \<Rightarrow> False | \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False else \<not>is_null\<upsilon> u)} = n\<close>
    by (metis (no_types, lifting) atLeast0LessThan bij2 bij_betw_same_card card_lessThan)
  moreover have \<open>finite {u. AOT_model_valid_in w\<^sub>0 (\<epsilon>\<^sub>\<o> w. if w = w\<^sub>0 then case u of \<sigma>\<upsilon> (\<sigma>'\<sigma> \<sigma>') \<Rightarrow> False | \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False else \<not>is_null\<upsilon> u)}\<close>
    using bij_betw_finite bij2 by blast
  ultimately have \<open>finite_card {u. AOT_model_valid_in w\<^sub>0 (Rep_urrel (Abs_urrel (\<lambda> u . \<epsilon>\<^sub>\<o> w . if w = w\<^sub>0 then case u of \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False else \<not>is_null\<upsilon> u)) u)} = Some n\<close>
    by (auto simp: Abs_urrel_inverse AOT_model_proposition_choice_simp finite_card_def)
  hence 2: \<open>(Abs_urrel (\<lambda> u . \<epsilon>\<^sub>\<o> w . if w = w\<^sub>0 then case u of \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False else \<not>is_null\<upsilon> u)) = x\<close>
    using assms by blast
  hence \<open>(Abs_urrel (\<lambda> u . \<epsilon>\<^sub>\<o> w . if w = w\<^sub>0 then case u of \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False else False)) = 
          (Abs_urrel (\<lambda> u . \<epsilon>\<^sub>\<o> w . if w = w\<^sub>0 then case u of \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False else \<not>is_null\<upsilon> u))\<close>
    using 1 by blast
  hence \<open>Rep_urrel (Abs_urrel (\<lambda> u . \<epsilon>\<^sub>\<o> w . if w = w\<^sub>0 then case u of \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False else False)) =
  Rep_urrel (Abs_urrel (\<lambda> u . \<epsilon>\<^sub>\<o> w . if w = w\<^sub>0 then case u of \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False else \<not>is_null\<upsilon> u))\<close>
    by auto
  hence \<open>(\<lambda> u . \<epsilon>\<^sub>\<o> w . if w = w\<^sub>0 then case u of \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False else False) =
         (\<lambda> u . \<epsilon>\<^sub>\<o> w . if w = w\<^sub>0 then case u of \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False else \<not>is_null\<upsilon> u)\<close>
    by (auto simp: Abs_urrel_inverse AOT_model_proposition_choice_simp)
  thus \<open>False\<close>
    by (smt (z3) AOT_model_nonactual_world AOT_model_proposition_choice_simp \<upsilon>.case_eq_if \<upsilon>.disc_eq_case(3) is_\<sigma>\<upsilon>_def)
qed

lemma n_eq: \<open>(THE m. model_number n = model_number m) = n\<close> for n
proof -
  have bij: \<open>bij_betw (\<lambda>n . \<sigma>\<upsilon> (number\<sigma> n)) {0..<n}
    {u. AOT_model_valid_in w\<^sub>0 (\<epsilon>\<^sub>\<o> w. case u of \<sigma>\<upsilon> (\<sigma>'\<sigma> \<sigma>') \<Rightarrow> False | \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False)}\<close>
    unfolding bij_betw_def
    apply auto
    apply (meson \<sigma>.inject(2) \<upsilon>.inject(2) inj_onI)
     apply (simp add: AOT_model_proposition_choice_simp)
    apply (simp add: image_def AOT_model_proposition_choice_simp)
    by (metis \<sigma>.exhaust \<sigma>.simps(5) \<sigma>.simps(6) \<upsilon>.case_eq_if \<upsilon>.sel(2) atLeastLessThan_iff is_\<sigma>\<upsilon>_def zero_le)

  {
    fix x
    assume \<open>model_number n = model_number x\<close>
    hence \<open>{rel. finite_card {u. AOT_model_valid_in w\<^sub>0 (Rep_urrel rel u)} = Some n} =
           {rel. finite_card {u. AOT_model_valid_in w\<^sub>0 (Rep_urrel rel u)} = Some x}\<close>
      unfolding model_number_def by blast
    moreover have \<open>(Abs_urrel (\<lambda> u . \<epsilon>\<^sub>\<o> w . case u of \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False)) \<in> 
          {rel. finite_card {u. AOT_model_valid_in w\<^sub>0 (Rep_urrel rel u)} = Some n}\<close>
      apply (auto simp: finite_card_def)
      apply (subst Abs_urrel_inverse)
        apply (simp add: AOT_model_proposition_choice_simp)
       apply (metis atLeast0LessThan bij bij_betw_same_card card_lessThan)
      apply (subst Abs_urrel_inverse)
        apply (simp add: AOT_model_proposition_choice_simp)
      using bij bij_betw_finite by blast
    ultimately have \<open>(Abs_urrel (\<lambda> u . \<epsilon>\<^sub>\<o> w . case u of \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False)) \<in> 
          {rel. finite_card {u. AOT_model_valid_in w\<^sub>0 (Rep_urrel rel u)} = Some x}\<close>
      by blast
    hence \<open>finite_card
     {u. AOT_model_valid_in w\<^sub>0
          (\<epsilon>\<^sub>\<o> w. case u of \<sigma>\<upsilon> (\<sigma>'\<sigma> \<sigma>') \<Rightarrow> False | \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False)} =
    Some x\<close> apply auto
      apply (subst (asm) Abs_urrel_inverse)
       apply (simp add: AOT_model_proposition_choice_simp)
      by meson
    hence \<open>card {u. AOT_model_valid_in w\<^sub>0
          (\<epsilon>\<^sub>\<o> w. case u of \<sigma>\<upsilon> (\<sigma>'\<sigma> \<sigma>') \<Rightarrow> False | \<sigma>\<upsilon> (number\<sigma> m) \<Rightarrow> m < n | _ \<Rightarrow> False)} = x\<close>
      by (metis (no_types, lifting) bij bij_betw_finite finite_atLeastLessThan finite_card_def option.inject)
    hence \<open>x = n\<close>
      using bij bij_betw_same_card by force
  }
  thus ?thesis
    by (auto intro!: the1_equality ex1I[where a=n])
qed

text\<open>Individual terms are either ordinary objects, represented by ordinary urelements,
     abstract objects, modelled as sets of Urrelations, or null objects, used to
     represent non-denoting definite descriptions.\<close>
datatype \<kappa> = \<omega>\<kappa> \<omega> | \<alpha>\<kappa> \<open>urrel set\<close> | is_null\<kappa>: null\<kappa> null

locale \<alpha>\<sigma>_props =
  fixes \<alpha>\<sigma> :: \<open>urrel set \<Rightarrow> \<sigma>\<close>
  assumes \<alpha>\<sigma>_surj: \<open>surj \<alpha>\<sigma>\<close>
  assumes \<alpha>\<sigma>_disc_pre: \<open>\<alpha>\<sigma> x = \<alpha>\<sigma> y \<Longrightarrow> x = { urrel. finite_card { \<kappa> . (\<forall> y . (case (y,\<kappa>) of (\<omega>\<kappa> a, \<omega>\<kappa> b) \<Rightarrow> a=b | (null\<kappa> a, null\<kappa> b) \<Rightarrow> a=b | (\<alpha>\<kappa> a, \<alpha>\<kappa> b) \<Rightarrow> \<alpha>\<sigma> a = \<alpha>\<sigma> b | _ \<Rightarrow> False)  \<longrightarrow> \<kappa> = y) \<and>
            AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel (case \<kappa> of \<omega>\<kappa> x \<Rightarrow> \<omega>\<upsilon> x | \<alpha>\<kappa> x \<Rightarrow> \<sigma>\<upsilon> (\<alpha>\<sigma> x) | null\<kappa> x \<Rightarrow> null\<upsilon> x))} = Some n} \<Longrightarrow> x = y\<close>
begin
end

lemma Aux: \<open>finite_card {u. case u of \<sigma>\<upsilon> (number\<sigma> \<sigma>') \<Rightarrow> \<sigma>' < n | _ \<Rightarrow> False} = Some n\<close>
proof -
  have bij: \<open>bij_betw (\<lambda>n . \<sigma>\<upsilon> (number\<sigma> n)) {0..<n}
    {u. case u of \<sigma>\<upsilon> (number\<sigma> \<sigma>') \<Rightarrow> \<sigma>' < n | _ \<Rightarrow> False}\<close>
    unfolding bij_betw_def
    apply auto
    apply (meson \<sigma>.inject(2) \<upsilon>.inject(2) inj_onI)
    apply (simp add: image_def AOT_model_proposition_choice_simp)
    by (metis \<sigma>.exhaust \<sigma>.simps(5) \<sigma>.simps(6) \<upsilon>.case_eq_if \<upsilon>.sel(2) atLeastLessThan_iff is_\<sigma>\<upsilon>_def zero_le)
  thus ?thesis
    by (metis atLeast0LessThan bij_betw_finite bij_betw_same_card card_lessThan finite_card_def finite_lessThan)
qed

fun \<upsilon>disc :: \<open>\<upsilon> \<Rightarrow> bool\<close> where
  \<open>\<upsilon>disc (\<omega>\<upsilon> x) = True\<close>
| \<open>\<upsilon>disc (\<sigma>\<upsilon> (number\<sigma> x)) = True\<close>
| \<open>\<upsilon>disc _ = False\<close>

definition urrel_number :: \<open>urrel \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>urrel_number \<equiv> \<lambda> urrel n . finite_card
              {u. \<upsilon>disc u \<and> AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel u)} =
             Some n\<close>

lemma urrel_number_eq:
  assumes \<open>urrel_number urrel n\<close>
      and \<open>urrel_number urrel m\<close>
    shows \<open>n = m\<close>
  by (metis assms(1) assms(2) option.inject urrel_number_def)

lemma urrel_number_zeroI:
  assumes \<open>\<nexists>x . AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel x)\<close>
  shows \<open>urrel_number urrel 0\<close>
proof -
  have 0: \<open>{u. \<upsilon>disc u \<and> AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel u)} = {}\<close>
    using assms by blast
  show \<open>urrel_number urrel 0\<close>
    unfolding urrel_number_def 0
    by (simp add: finite_card_def)
qed

lemma urrel_number_oneI:
  assumes \<open>\<exists>!x . \<upsilon>disc x \<and> AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel x)\<close>
  shows \<open>urrel_number urrel 1\<close>
proof -
  obtain x where A: \<open>AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel x)\<close> and B: \<open>\<upsilon>disc x\<close> and
                 C: \<open>\<forall>y . \<upsilon>disc y \<and> AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel y) \<longrightarrow> y = x\<close>
    using assms by blast
  have 0: \<open>{u. \<upsilon>disc u \<and> AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel u)} = {x}\<close> (is \<open>?lhs = ?rhs\<close>)
  proof(rule; rule)
    fix y
    assume \<open>y \<in> ?lhs\<close>
    hence \<open>\<upsilon>disc y\<close> and \<open>AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel y)\<close>
      by blast+
    hence \<open>y = x\<close> using C by blast
    thus \<open>y \<in> {x}\<close> by blast
  next
    fix y
    assume \<open>y \<in> {x}\<close>
    hence \<open>y = x\<close> by blast
    hence \<open>\<upsilon>disc y\<close> and \<open>AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel y)\<close> using A B by blast+
    thus \<open>y \<in> {u. \<upsilon>disc u \<and> AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel u)}\<close>
      by blast
  qed
  show \<open>urrel_number urrel 1\<close>
    unfolding urrel_number_def 0
    by (simp add: finite_card_def)
qed


lemma urrel_number_ex: \<open>\<exists> urrel . urrel_number urrel n\<close>
proof
  have 0: \<open>{u. \<upsilon>disc u \<and>
     (case u of \<sigma>\<upsilon> (\<sigma>'\<sigma> \<sigma>'') \<Rightarrow> False | \<sigma>\<upsilon> (number\<sigma> \<sigma>') \<Rightarrow> \<sigma>' < n | _ \<Rightarrow> False)} =
      {u. case u of \<sigma>\<upsilon> (number\<sigma> \<sigma>') \<Rightarrow> \<sigma>' < n | _ \<Rightarrow> False}\<close> for n apply auto
    by (metis \<sigma>.simps(5) \<upsilon>.case_eq_if \<upsilon>.disc(6) \<upsilon>.sel(2) \<upsilon>disc.elims(1))
  thus \<open>urrel_number (Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w. case u of \<sigma>\<upsilon> (number\<sigma> \<sigma>') \<Rightarrow> \<sigma>' < n | _ \<Rightarrow> False)) n\<close>
    unfolding urrel_number_def
    apply (subst Abs_urrel_inverse)
    by (auto simp add: AOT_model_proposition_choice_simp 0 Aux)
qed

definition urrel_set_is_number :: \<open>urrel set \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>urrel_set_is_number \<equiv> \<lambda> urrels n . urrels = { urrel .  urrel_number urrel n }\<close>

lemma urrel_is_number_eq:
  assumes \<open>urrel_set_is_number urrel n\<close>
      and \<open>urrel_set_is_number urrel m\<close>
    shows \<open>n = m\<close>
  by (metis assms(1) assms(2) mem_Collect_eq urrel_number_eq urrel_number_ex urrel_set_is_number_def)

specification (\<alpha>\<sigma>)
  \<alpha>\<sigma>_props: \<open>\<alpha>\<sigma>_props \<alpha>\<sigma>\<close>
proof
  define \<alpha>\<sigma> :: \<open>urrel set \<Rightarrow> \<sigma>\<close> where \<open>\<alpha>\<sigma> \<equiv> \<lambda> urrels .
        if \<exists>n . urrel_set_is_number urrels n then number\<sigma> (THE n . urrel_set_is_number urrels n)
        else \<sigma>'\<sigma> (THE \<sigma>' . \<exists>urrel \<in> urrels . \<exists>v . v \<noteq> w\<^sub>0 \<and> AOT_model_valid_in v (Rep_urrel urrel (\<sigma>\<upsilon> (\<sigma>'\<sigma> \<sigma>'))))
  \<close>
  define \<kappa>\<upsilon> where \<open>\<kappa>\<upsilon> \<equiv> (\<lambda>\<kappa> . case \<kappa> of \<omega>\<kappa> x \<Rightarrow> \<omega>\<upsilon> x | \<alpha>\<kappa> x \<Rightarrow> \<sigma>\<upsilon> (\<alpha>\<sigma> x) | null\<kappa> x \<Rightarrow> null\<upsilon> x)\<close>
  fix someord :: \<omega>
  obtain w\<^sub>1 where w\<^sub>1: \<open>w\<^sub>1 \<noteq> w\<^sub>0\<close>
    using AOT_model_nonactual_world by blast
    have surj_\<alpha>\<sigma>: \<open>surj \<alpha>\<sigma>\<close>
    proof -
      have 1: \<open>\<nexists>n. \<forall>urrel\<in>{Abs_urrel (\<lambda>u. \<epsilon>\<^sub>\<o> w. case u of \<omega>\<upsilon> x \<Rightarrow> x = someord | _ \<Rightarrow> False), Abs_urrel (\<lambda>u. \<epsilon>\<^sub>\<o> w. u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s'))}.
                   urrel_number urrel n\<close> for s'
      proof
        assume \<open>\<exists>n. \<forall>urrel\<in>{Abs_urrel (\<lambda>u. \<epsilon>\<^sub>\<o> w. case u of \<omega>\<upsilon> x \<Rightarrow> x = someord | _ \<Rightarrow> False), Abs_urrel (\<lambda>u. \<epsilon>\<^sub>\<o> w. u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s'))}.
                urrel_number urrel n\<close>
        then obtain n where \<open>\<forall>urrel\<in>{Abs_urrel (\<lambda>u. \<epsilon>\<^sub>\<o> w. case u of \<omega>\<upsilon> x \<Rightarrow> x = someord | _ \<Rightarrow> False), Abs_urrel (\<lambda>u. \<epsilon>\<^sub>\<o> w. u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s'))}.
                             urrel_number urrel n\<close>
          by blast
        hence 0: \<open>urrel_number (Abs_urrel (\<lambda>u. \<epsilon>\<^sub>\<o> w. case u of \<omega>\<upsilon> x \<Rightarrow> x = someord | _ \<Rightarrow> False)) n\<close>
          and
          1: \<open>urrel_number (Abs_urrel (\<lambda>u. \<epsilon>\<^sub>\<o> w. u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s'))) n\<close>
          by blast+
        have 2: \<open>{u. \<upsilon>disc u \<and>
                AOT_model_valid_in w\<^sub>0 (Rep_urrel (Abs_urrel (\<lambda>u. \<epsilon>\<^sub>\<o> w. u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s'))) u)} =
          {}\<close>
          apply auto
          apply (subst (asm) Abs_urrel_inverse)
          by (auto simp: AOT_model_proposition_choice_simp)
        have 3: \<open>{u. \<upsilon>disc u \<and>
                AOT_model_valid_in w\<^sub>0 (Rep_urrel (Abs_urrel (\<lambda>u. \<epsilon>\<^sub>\<o> w. case u of \<omega>\<upsilon> x \<Rightarrow> x = someord | _ \<Rightarrow> False)) u)} =
                { \<omega>\<upsilon> someord }\<close>
          apply auto
          apply (subst (asm) Abs_urrel_inverse)
            apply (auto simp: AOT_model_proposition_choice_simp)
           apply (metis (full_types) \<upsilon>.case_eq_if \<upsilon>.collapse(1))
          apply (subst Abs_urrel_inverse)
          by (auto simp: AOT_model_proposition_choice_simp)
        have \<open>n = 0\<close> using 1 unfolding urrel_number_def unfolding 2 finite_card_def by auto
        moreover have \<open>n = 1\<close> using 0 unfolding 3 urrel_number_def finite_card_def by auto
        ultimately show \<open>False\<close>
          by auto
      qed
      have 2: \<open>finite_card
          {u. \<upsilon>disc u \<and>
              AOT_model_valid_in w\<^sub>0 (Rep_urrel (Abs_urrel (\<lambda>u. \<epsilon>\<^sub>\<o> w. u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s'))) u)} \<noteq>
         finite_card
          {u. \<upsilon>disc u \<and>
              AOT_model_valid_in w\<^sub>0 (Rep_urrel (Abs_urrel (\<lambda>u. \<epsilon>\<^sub>\<o> w. case u of \<omega>\<upsilon> x \<Rightarrow> x = someord | _ \<Rightarrow> False)) u)}\<close>
        for s'
      proof
        assume 1: \<open>finite_card
          {u. \<upsilon>disc u \<and>
              AOT_model_valid_in w\<^sub>0 (Rep_urrel (Abs_urrel (\<lambda>u. \<epsilon>\<^sub>\<o> w. u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s'))) u)} =
         finite_card
          {u. \<upsilon>disc u \<and>
              AOT_model_valid_in w\<^sub>0 (Rep_urrel (Abs_urrel (\<lambda>u. \<epsilon>\<^sub>\<o> w. case u of \<omega>\<upsilon> x \<Rightarrow> x = someord | _ \<Rightarrow> False)) u)}\<close>
          (* TODO: unify with above *)
        have 2: \<open>{u. \<upsilon>disc u \<and>
                AOT_model_valid_in w\<^sub>0 (Rep_urrel (Abs_urrel (\<lambda>u. \<epsilon>\<^sub>\<o> w. u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s'))) u)} =
          {}\<close>
          apply auto
          apply (subst (asm) Abs_urrel_inverse)
          by (auto simp: AOT_model_proposition_choice_simp)
        have 3: \<open>{u. \<upsilon>disc u \<and>
                AOT_model_valid_in w\<^sub>0 (Rep_urrel (Abs_urrel (\<lambda>u. \<epsilon>\<^sub>\<o> w. case u of \<omega>\<upsilon> x \<Rightarrow> x = someord | _ \<Rightarrow> False)) u)} =
                { \<omega>\<upsilon> someord }\<close>
          apply auto
          apply (subst (asm) Abs_urrel_inverse)
            apply (auto simp: AOT_model_proposition_choice_simp)
           apply (metis (full_types) \<upsilon>.case_eq_if \<upsilon>.collapse(1))
          apply (subst Abs_urrel_inverse)
          by (auto simp: AOT_model_proposition_choice_simp)
        show False
          using 1 unfolding 2 3
          by (simp add: finite_card_def)
      qed
      {
        fix s
        {
          assume \<open>\<exists> n . s = number\<sigma> n\<close>
          then obtain n where s_def: \<open>s = number\<sigma> n\<close> by blast
          have \<open>\<alpha>\<sigma> { urrel . finite_card { u . \<upsilon>disc u \<and> AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel u) } = Some n} = s\<close>
            unfolding \<alpha>\<sigma>_def s_def urrel_set_is_number_def
            apply (auto simp add: Let_def)
            apply (rule the1_equality)
             apply (rule_tac a=n in ex1I)
              apply rule apply rule
                apply (simp_all)
            using urrel_number_ex
                apply (metis (mono_tags, lifting) mem_Collect_eq urrel_number_def)
               apply rule
            apply simp
            using urrel_number_ex
               apply (metis (mono_tags, lifting) mem_Collect_eq urrel_number_def)
            apply (smt (z3) mem_Collect_eq option.inject urrel_number_def urrel_number_ex)
            using urrel_number_def apply presburger
            by (smt (verit, best) Collect_cong urrel_number_def)
          hence \<open>\<exists>f . \<alpha>\<sigma> (f s) = s\<close> by fast
        }
        moreover {
          assume \<open>\<exists>s' . s = \<sigma>'\<sigma> s'\<close>
          then obtain s' where s_def: \<open>s = \<sigma>'\<sigma> s'\<close> by blast
          have 3: \<open>\<sigma>'\<sigma> (THE \<sigma>'.
             (\<exists>v. v \<noteq> w\<^sub>0 \<and>
                  AOT_model_valid_in v
                   (Rep_urrel (Abs_urrel (\<lambda>u. \<epsilon>\<^sub>\<o> w. case u of \<omega>\<upsilon> x \<Rightarrow> x = someord | _ \<Rightarrow> False)) (\<sigma>\<upsilon> (\<sigma>'\<sigma> \<sigma>')))) \<or>
             (\<exists>v. v \<noteq> w\<^sub>0 \<and> AOT_model_valid_in v (Rep_urrel (Abs_urrel (\<lambda>u. \<epsilon>\<^sub>\<o> w. u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s'))) (\<sigma>\<upsilon> (\<sigma>'\<sigma> \<sigma>'))))) =
            s\<close>
            unfolding s_def
            apply simp
            apply (rule the1_equality)
             apply (rule_tac a="s'" in ex1I)
            by ((subst Abs_urrel_inverse | subst (asm) Abs_urrel_inverse); simp add: AOT_model_proposition_choice_simp AOT_model_nonactual_world)+
          have \<open>\<alpha>\<sigma> ({ Abs_urrel (\<lambda> u . \<epsilon>\<^sub>\<o> w.  case u of \<omega>\<upsilon> x \<Rightarrow> x = someord | _ \<Rightarrow> False),
                      Abs_urrel (\<lambda> u . \<epsilon>\<^sub>\<o> w.  u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s')) }) = s\<close>
            unfolding \<alpha>\<sigma>_def Let_def s_def urrel_set_is_number_def
            apply (auto simp add: 1 2 3)
            using "1" apply auto[1]
            using s_def by blast

          hence \<open>\<exists>f . \<alpha>\<sigma> (f s) = s\<close> by fast
        }
        ultimately have \<open>\<exists>f . \<alpha>\<sigma> (f s) = s\<close>
          by (meson \<sigma>.exhaust)
      }
      thus ?thesis
        by (metis surj_def)
    qed
  have \<kappa>\<upsilon>_surj: \<open>surj \<kappa>\<upsilon>\<close>
    by (metis \<kappa>.simps(10) \<kappa>.simps(11) \<kappa>.simps(12) \<kappa>\<upsilon>_def \<upsilon>.exhaust surj_\<alpha>\<sigma> surj_def)
  show \<open>\<alpha>\<sigma>_props \<alpha>\<sigma>\<close>
  proof
    show \<open>surj \<alpha>\<sigma>\<close> using surj_\<alpha>\<sigma> by blast
  next
    fix x y and n
    assume \<alpha>\<sigma>_eq: \<open>\<alpha>\<sigma> x = \<alpha>\<sigma> y\<close>
    hence is_num_eq: \<open>(\<exists>n . urrel_set_is_number x n) = (\<exists>n . urrel_set_is_number y n)\<close>
      unfolding \<alpha>\<sigma>_def
      by (metis \<sigma>.distinct(2))
    assume A: \<open>x =
       {urrel.
        finite_card
         {\<kappa>. (\<forall>y. (case (y, \<kappa>) of (\<omega>\<kappa> a, \<omega>\<kappa> b) \<Rightarrow> a = b | (\<alpha>\<kappa> a, \<alpha>\<kappa> b) \<Rightarrow> \<alpha>\<sigma> a = \<alpha>\<sigma> b | (null\<kappa> a, null\<kappa> b) \<Rightarrow> a = b | _ \<Rightarrow> False) \<longrightarrow> \<kappa> = y) \<and>
              AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel (case \<kappa> of \<omega>\<kappa> x \<Rightarrow> \<omega>\<upsilon> x | \<alpha>\<kappa> x \<Rightarrow> \<sigma>\<upsilon> (\<alpha>\<sigma> x) | null\<kappa> x \<Rightarrow> null\<upsilon> x))} =
        Some n}\<close>
    {
      fix a
      assume 0: \<open>\<forall>y. (case (y,\<alpha>\<kappa> a) of (\<omega>\<kappa> a, \<omega>\<kappa> b) \<Rightarrow> a = b | (\<alpha>\<kappa> a, \<alpha>\<kappa> b) \<Rightarrow> \<alpha>\<sigma> a = \<alpha>\<sigma> b | (null\<kappa> a, null\<kappa> b) \<Rightarrow> a = b | _ \<Rightarrow> False) \<longrightarrow> \<alpha>\<kappa> a = y\<close>
      {
        fix b
        have \<open>\<alpha>\<sigma> a = \<alpha>\<sigma> b \<longrightarrow> \<alpha>\<kappa> a = \<alpha>\<kappa> b\<close>
          using 0 by force
      } note 1 = this
      {
        assume \<open>\<exists>s . \<alpha>\<sigma> a = \<sigma>'\<sigma> s\<close>
        then obtain s where \<open>\<alpha>\<sigma> a = \<sigma>'\<sigma> s\<close> by blast
        define b where \<open>b = { Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . w = w\<^sub>0 \<and> u = \<omega>\<upsilon> someord), Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . w \<noteq> w\<^sub>0 \<and> u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s))}\<close>
        define c where \<open>c = { Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . w \<noteq> w\<^sub>0 \<and> u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s))}\<close>
        have \<open>Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . w = w\<^sub>0 \<and> u = \<omega>\<upsilon> someord) \<noteq> Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . w \<noteq> w\<^sub>0 \<and> u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s))\<close>
        proof
          assume \<open>Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . w = w\<^sub>0 \<and> u = \<omega>\<upsilon> someord) = Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . w \<noteq> w\<^sub>0 \<and> u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s))\<close>
          hence \<open>(\<lambda>u . \<epsilon>\<^sub>\<o> w . w = w\<^sub>0 \<and> u = \<omega>\<upsilon> someord) = (\<lambda>u . \<epsilon>\<^sub>\<o> w . w \<noteq> w\<^sub>0 \<and> u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s))\<close>
            apply (subst (asm) Abs_urrel_inject)
            by (auto simp: AOT_model_proposition_choice_simp)
          thus \<open>False\<close>
            by (metis (mono_tags, lifting) AOT_model_proposition_choice_simp)
        qed
        hence \<open>b \<noteq> c\<close> unfolding b_def c_def by auto
        have b_not_num: \<open>\<nexists>n . urrel_set_is_number b n\<close>
        proof
          assume \<open>\<exists>n . urrel_set_is_number b n\<close>
          then obtain n where 0: \<open>urrel_set_is_number b n\<close> by blast
          hence \<open>urrel_number (Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . w = w\<^sub>0 \<and> u = \<omega>\<upsilon> someord)) n\<close>
            by (metis (no_types, lifting) b_def insertI1 mem_Collect_eq urrel_set_is_number_def)
          moreover have \<open>urrel_number (Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . w \<noteq> w\<^sub>0 \<and> u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s))) n\<close>
            using 0
            by (metis (mono_tags, lifting) b_def insertI1 insert_commute mem_Collect_eq urrel_set_is_number_def)
          moreover have \<open>urrel_number (Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . w = w\<^sub>0 \<and> u = \<omega>\<upsilon> someord)) 1\<close>
            apply (rule urrel_number_oneI)
            apply (rule_tac a = \<open>\<omega>\<upsilon> someord\<close> in ex1I)
             apply (subst Abs_urrel_inverse)
            apply (auto simp: AOT_model_proposition_choice_simp)
             apply (subst (asm) Abs_urrel_inverse)
            by (auto simp: AOT_model_proposition_choice_simp)
          moreover have \<open>urrel_number (Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . w \<noteq> w\<^sub>0 \<and> u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s))) 0\<close>
            apply (rule urrel_number_zeroI)
            apply (subst Abs_urrel_inverse)
            by (auto simp: AOT_model_proposition_choice_simp)
          ultimately show \<open>False\<close> using urrel_number_eq
            using zero_neq_one by blast
        qed
        have \<open>\<alpha>\<sigma> b = \<sigma>'\<sigma> s\<close>
          unfolding \<alpha>\<sigma>_def apply (simp add: b_not_num)
          apply (rule the1_equality)
           apply (rule_tac a=\<open>s\<close> in ex1I)
            apply (rule_tac x=\<open>Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . w \<noteq> w\<^sub>0 \<and> u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s))\<close> in bexI)
             apply (rule_tac x=\<open>w\<^sub>1\<close> in exI)
             apply (subst Abs_urrel_inverse)
              apply (auto simp: AOT_model_proposition_choice_simp w\<^sub>1)
          unfolding b_def apply simp
           apply simp
          using AOT_model_proposition_choice_simp Abs_urrel_inverse apply force
            apply (rule_tac x=\<open>Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . w \<noteq> w\<^sub>0 \<and> u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s))\<close> in bexI)
           apply (rule_tac x=\<open>w\<^sub>1\<close> in exI)
           apply (auto simp: AOT_model_proposition_choice_simp w\<^sub>1)
          apply (subst Abs_urrel_inverse)
          by (auto simp: AOT_model_proposition_choice_simp w\<^sub>1)
        have c_not_num: \<open>\<nexists>n . urrel_set_is_number c n\<close>
        proof
          assume \<open>\<exists>n . urrel_set_is_number c n\<close>
          then obtain n where 0: \<open>urrel_set_is_number c n\<close> by blast
          hence \<open>urrel_number (Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . w \<noteq> w\<^sub>0 \<and> u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s))) n\<close>
            by (metis c_def mem_Collect_eq singletonI urrel_set_is_number_def)
          moreover have \<open>urrel_number (Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . w \<noteq> w\<^sub>0 \<and> u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s))) 0\<close>
            apply (rule urrel_number_zeroI)
            apply (subst Abs_urrel_inverse)
            by (auto simp: AOT_model_proposition_choice_simp)
          ultimately have n0: \<open>n = 0\<close>
            using urrel_number_eq by blast
          have \<open>urrel_number (Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . False)) 0\<close>
            apply (rule urrel_number_zeroI)
            apply (subst Abs_urrel_inverse)
            by (auto simp: AOT_model_proposition_choice_simp)
          hence \<open>Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . False) \<in> c\<close>
            by (metis "0" mem_Collect_eq n0 urrel_set_is_number_def)
          hence \<open>Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . False) = Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . w \<noteq> w\<^sub>0 \<and> u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s))\<close>
            using c_def by blast
          thus \<open>False\<close>
            apply (subst (asm) Abs_urrel_inject)
              apply (auto simp: AOT_model_proposition_choice_simp)
            by (smt (z3) AOT_model_proposition_choice_simp w\<^sub>1)
        qed
        have \<open>\<alpha>\<sigma> c = \<sigma>'\<sigma> s\<close>
          unfolding \<alpha>\<sigma>_def apply (simp add: c_not_num)
          apply (rule the1_equality)
           apply (rule_tac a=\<open>s\<close> in ex1I)
            apply (rule_tac x=\<open>Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . w \<noteq> w\<^sub>0 \<and> u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s))\<close> in bexI)
             apply (rule_tac x=\<open>w\<^sub>1\<close> in exI)
             apply (subst Abs_urrel_inverse)
              apply (auto simp: AOT_model_proposition_choice_simp w\<^sub>1)
          unfolding c_def apply simp
           apply simp
          using AOT_model_proposition_choice_simp Abs_urrel_inverse apply force
            apply (rule_tac x=\<open>Abs_urrel (\<lambda>u . \<epsilon>\<^sub>\<o> w . w \<noteq> w\<^sub>0 \<and> u = \<sigma>\<upsilon> (\<sigma>'\<sigma> s))\<close> in bexI)
           apply (rule_tac x=\<open>w\<^sub>1\<close> in exI)
           apply (auto simp: AOT_model_proposition_choice_simp w\<^sub>1)
          apply (subst Abs_urrel_inverse)
          by (auto simp: AOT_model_proposition_choice_simp w\<^sub>1)
        have \<open>\<alpha>\<sigma> b = \<alpha>\<sigma> c\<close>
          using \<open>\<alpha>\<sigma> b = \<sigma>'\<sigma> s\<close> \<open>\<alpha>\<sigma> c = \<sigma>'\<sigma> s\<close> by auto
        have \<open>False\<close>
          by (metis "1" \<kappa>.sel(2) \<open>\<alpha>\<sigma> a = \<sigma>'\<sigma> s\<close> \<open>\<alpha>\<sigma> b = \<sigma>'\<sigma> s\<close> \<open>\<alpha>\<sigma> c = \<sigma>'\<sigma> s\<close> \<open>b \<noteq> c\<close>)
      }
      hence \<open>\<exists> n. \<alpha>\<sigma> a = number\<sigma> n\<close>
        by (meson \<sigma>.exhaust)
    }
    moreover {
      fix a
      assume \<open>\<exists> n. \<alpha>\<sigma> a = number\<sigma> n\<close>
      then obtain n where a_num_n: \<open>\<alpha>\<sigma> a = number\<sigma> n\<close> by blast
      hence a_num_n': \<open>urrel_set_is_number a n\<close>
        unfolding \<alpha>\<sigma>_def
        by (metis (mono_tags, lifting) \<sigma>.distinct(1) \<sigma>.inject(2) mem_Collect_eq theI urrel_number_eq urrel_number_ex urrel_set_is_number_def)
      {
        fix b
        assume \<open>\<alpha>\<sigma> b = \<alpha>\<sigma> a\<close>
        hence b_num_n: \<open>\<alpha>\<sigma> b = number\<sigma> n\<close> using a_num_n by auto
        hence b_num_n': \<open>urrel_set_is_number b n\<close>
          unfolding \<alpha>\<sigma>_def
          by (metis (mono_tags, lifting) \<sigma>.distinct(1) \<sigma>.inject(2) mem_Collect_eq theI urrel_number_eq urrel_number_ex urrel_set_is_number_def)
        have \<open>a = b\<close>
          by (metis a_num_n' b_num_n' urrel_set_is_number_def)
      } note 0 = this
      have \<open>\<forall>y. (case (y,\<alpha>\<kappa> a) of (\<omega>\<kappa> a, \<omega>\<kappa> b) \<Rightarrow> a = b | (\<alpha>\<kappa> a, \<alpha>\<kappa> b) \<Rightarrow> \<alpha>\<sigma> a = \<alpha>\<sigma> b | (null\<kappa> a, null\<kappa> b) \<Rightarrow> a = b | _ \<Rightarrow> False) \<longrightarrow> \<alpha>\<kappa> a = y\<close>
      proof -
        {
          fix y
          assume \<open>(case (y,\<alpha>\<kappa> a) of (\<omega>\<kappa> a, \<omega>\<kappa> b) \<Rightarrow> a = b | (\<alpha>\<kappa> a, \<alpha>\<kappa> b) \<Rightarrow> \<alpha>\<sigma> a = \<alpha>\<sigma> b | (null\<kappa> a, null\<kappa> b) \<Rightarrow> a = b | _ \<Rightarrow> False)\<close>
          hence \<open>\<alpha>\<kappa> a = y\<close>
            apply (induct y)
              apply simp
             apply simp
            using 0 apply simp
            by simp
        }
        thus ?thesis by auto
      qed
    }
    ultimately have simp1: \<open>(\<forall>y. (case (y, \<kappa>) of (\<omega>\<kappa> a, \<omega>\<kappa> b) \<Rightarrow> a = b | (\<omega>\<kappa> a, _) \<Rightarrow> False | (\<alpha>\<kappa> a, \<alpha>\<kappa> b) \<Rightarrow> \<alpha>\<sigma> a = \<alpha>\<sigma> b | (\<alpha>\<kappa> a, _) \<Rightarrow> False
         | (null\<kappa> a, null\<kappa> b) \<Rightarrow> a = b | (null\<kappa> a, _) \<Rightarrow> False) \<longrightarrow>
        \<kappa> = y) = (\<upsilon>disc (\<kappa>\<upsilon> \<kappa>))\<close> if \<open>\<not>is_null\<kappa> \<kappa>\<close> for \<kappa>
      using that
      apply (induct \<kappa>)
        apply (simp_all add: \<kappa>\<upsilon>_def)
      apply (smt (verit, best) \<kappa>.case_eq_if \<kappa>.disc(4) \<kappa>.disc(7) \<kappa>.distinct_disc(1) \<kappa>.expand)
      by (metis \<upsilon>.sel(2) \<upsilon>.simps(5) \<upsilon>disc.elims(2) \<upsilon>disc.simps(2))

    have simp2: \<open>AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel (case \<kappa> of \<omega>\<kappa> x \<Rightarrow> \<omega>\<upsilon> x | \<alpha>\<kappa> x \<Rightarrow> \<sigma>\<upsilon> (\<alpha>\<sigma> x) | null\<kappa> x \<Rightarrow> null\<upsilon> x)) \<Longrightarrow> \<not>is_null\<kappa> \<kappa>\<close>
      for urrel \<kappa> using Rep_urrel
      by (metis (mono_tags, lifting) \<kappa>.case_eq_if \<kappa>.distinct_disc(3) \<kappa>.distinct_disc(6) mem_Collect_eq)

    have \<open>{\<kappa>. (\<forall>y. (case (y, \<kappa>) of (\<omega>\<kappa> a, \<omega>\<kappa> b) \<Rightarrow> a = b | (\<alpha>\<kappa> a, \<alpha>\<kappa> b) \<Rightarrow> \<alpha>\<sigma> a = \<alpha>\<sigma> b | (null\<kappa> a, null\<kappa> b) \<Rightarrow> a = b | _ \<Rightarrow> False) \<longrightarrow> \<kappa> = y) \<and>
              AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel (case \<kappa> of \<omega>\<kappa> x \<Rightarrow> \<omega>\<upsilon> x | \<alpha>\<kappa> x \<Rightarrow> \<sigma>\<upsilon> (\<alpha>\<sigma> x) | null\<kappa> x \<Rightarrow> null\<upsilon> x))} =
          {\<kappa> . \<upsilon>disc (\<kappa>\<upsilon> \<kappa>) \<and> AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel (case \<kappa> of \<omega>\<kappa> x \<Rightarrow> \<omega>\<upsilon> x | \<alpha>\<kappa> x \<Rightarrow> \<sigma>\<upsilon> (\<alpha>\<sigma> x) | null\<kappa> x \<Rightarrow> null\<upsilon> x))}\<close>
        (is \<open>?lhs = ?rhs\<close>)
      for urrel
    proof(rule; rule)
      fix \<kappa>
      assume 0: \<open>\<kappa> \<in> ?lhs\<close>
      hence 1: \<open>\<not>is_null\<kappa> \<kappa>\<close>
        using simp2 by blast
      thus \<open>\<kappa> \<in> ?rhs\<close>
        using 0[simplified] simp1[OF simp2]
        by auto
    next
      fix \<kappa>
      assume 0: \<open>\<kappa> \<in> ?rhs\<close>
      hence 1: \<open>\<not>is_null\<kappa> \<kappa>\<close>
        using simp2 by force
      thus \<open>\<kappa> \<in> ?lhs\<close>
        using 0[simplified] simp1[OF simp2]
        by auto
    qed
    hence B: \<open>x =
    {urrel.
     finite_card
      {\<kappa>. \<upsilon>disc (\<kappa>\<upsilon> \<kappa>) \<and> AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel (case \<kappa> of \<omega>\<kappa> x \<Rightarrow> \<omega>\<upsilon> x | \<alpha>\<kappa> x \<Rightarrow> \<sigma>\<upsilon> (\<alpha>\<sigma> x) | null\<kappa> x \<Rightarrow> null\<upsilon> x))} =
     Some n}\<close> using A by auto

    {
      fix urrel
      fix x
      obtain y where y_def: \<open>\<kappa>\<upsilon> y = x\<close>
        by (meson \<kappa>\<upsilon>_surj surj_f_inv_f)
      have \<open>\<upsilon>disc x \<Longrightarrow>
         AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel x) \<Longrightarrow>
         \<exists>xa. \<upsilon>disc (\<kappa>\<upsilon> xa) \<and> AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel (case xa of \<omega>\<kappa> x \<Rightarrow> \<omega>\<upsilon> x | \<alpha>\<kappa> x \<Rightarrow> \<sigma>\<upsilon> (\<alpha>\<sigma> x) | null\<kappa> x \<Rightarrow> null\<upsilon> x)) \<and> x = \<kappa>\<upsilon> xa\<close>
        apply (rule_tac x=y in exI)
        apply (auto simp add: y_def)
        using \<kappa>\<upsilon>_def y_def by blast
    } note aux = this
    have \<open>bij_betw \<kappa>\<upsilon>
        {\<kappa>. \<upsilon>disc (\<kappa>\<upsilon> \<kappa>) \<and> AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel (case \<kappa> of \<omega>\<kappa> x \<Rightarrow> \<omega>\<upsilon> x | \<alpha>\<kappa> x \<Rightarrow> \<sigma>\<upsilon> (\<alpha>\<sigma> x) | null\<kappa> x \<Rightarrow> null\<upsilon> x))}
        {u. \<upsilon>disc u \<and> AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel u)}\<close> for urrel
      unfolding bij_betw_def
      apply auto
        apply (rule inj_onI)
        apply auto
      apply (smt (verit, ccfv_threshold) \<kappa>.collapse(1) \<kappa>.disc(5) \<kappa>.disc(6) \<kappa>.disc(9) \<kappa>.distinct(1) \<kappa>.distinct(3) \<kappa>.distinct(5) \<kappa>.distinct_disc(2) \<kappa>.exhaust_disc \<kappa>.exhaust_sel \<kappa>.inject(1) \<kappa>.sel(2) \<kappa>.simps(10) \<kappa>.simps(11) \<kappa>.split_sel_asm \<kappa>\<upsilon>_def \<open>\<And>urrel. {\<kappa>. (\<forall>y. (case (y, \<kappa>) of (\<omega>\<kappa> a, \<omega>\<kappa> b) \<Rightarrow> a = b | (\<omega>\<kappa> a, _) \<Rightarrow> False | (\<alpha>\<kappa> a, \<alpha>\<kappa> b) \<Rightarrow> \<alpha>\<sigma> a = \<alpha>\<sigma> b | (\<alpha>\<kappa> a, _) \<Rightarrow> False | (null\<kappa> a, null\<kappa> b) \<Rightarrow> a = b | (null\<kappa> a, _) \<Rightarrow> False) \<longrightarrow> \<kappa> = y) \<and> AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel (case \<kappa> of \<omega>\<kappa> x \<Rightarrow> \<omega>\<upsilon> x | \<alpha>\<kappa> x \<Rightarrow> \<sigma>\<upsilon> (\<alpha>\<sigma> x) | null\<kappa> x \<Rightarrow> null\<upsilon> x))} = {\<kappa>. \<upsilon>disc (\<kappa>\<upsilon> \<kappa>) \<and> AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel (case \<kappa> of \<omega>\<kappa> x \<Rightarrow> \<omega>\<upsilon> x | \<alpha>\<kappa> x \<Rightarrow> \<sigma>\<upsilon> (\<alpha>\<sigma> x) | null\<kappa> x \<Rightarrow> null\<upsilon> x))}\<close> \<upsilon>.distinct(1) \<upsilon>.distinct(3) \<upsilon>.distinct(5) \<upsilon>.exhaust \<upsilon>.inject(1) \<upsilon>.inject(2) \<upsilon>disc.cases \<upsilon>disc.elims(2) accp.simps accp_induct_rule case_prodI empty_def is_\<alpha>\<kappa>_def mem_Collect_eq not_accp_down simp2)
      using \<kappa>\<upsilon>_def apply blast
      unfolding image_def
      apply auto
      using aux by blast

    hence x_num_n: \<open>urrel_set_is_number x n\<close>
      unfolding urrel_set_is_number_def urrel_number_def
      by (smt (verit, best) B Collect_cong bij_betw_finite bij_betw_same_card finite_card_def)
    hence x_num_ex: \<open>\<exists>n . urrel_set_is_number x n\<close>
      by auto
    have \<open>\<alpha>\<sigma> x = number\<sigma> n\<close>
      unfolding \<alpha>\<sigma>_def apply (simp add: x_num_n x_num_ex)
      apply (rule the1_equality)
       apply (rule_tac a=n in ex1I)
      apply (auto simp: x_num_n)
      by (simp add: urrel_is_number_eq x_num_n)
    {
      have \<open>\<exists> n . urrel_set_is_number y n\<close>
        using is_num_eq x_num_n by blast
      hence \<open>urrel_set_is_number y n\<close>
        using x_num_n
        by (metis \<alpha>\<sigma>_def \<alpha>\<sigma>_eq \<sigma>.inject(2) theI urrel_is_number_eq)
    }
    thus \<open>x = y\<close> using x_num_n
      by (simp add: urrel_set_is_number_def)
  qed
qed

interpretation \<alpha>\<sigma>_props \<alpha>\<sigma>
  using \<alpha>\<sigma>_props by simp

text\<open>We use the extended model version.\<close>
abbreviation (input) AOT_ExtendedModel where \<open>AOT_ExtendedModel \<equiv> False\<close>
(*
abbreviation (input) \<alpha>\<sigma> where \<open>\<alpha>\<sigma> \<equiv> \<alpha>\<sigma>_restr\<close>
lemmas \<alpha>\<sigma>_surj = \<alpha>\<sigma>_restr_surj
abbreviation (input) AOT_ExtendedModel where \<open>AOT_ExtendedModel \<equiv> False\<close>
*)

text\<open>The mapping from abstract objects to urelements can be naturally
     lifted to a surjective mapping from individual terms to urelements.\<close>
primrec \<kappa>\<upsilon> :: \<open>\<kappa>\<Rightarrow>\<upsilon>\<close> where
  \<open>\<kappa>\<upsilon> (\<omega>\<kappa> x) = \<omega>\<upsilon> x\<close>
| \<open>\<kappa>\<upsilon> (\<alpha>\<kappa> x) = \<sigma>\<upsilon> (\<alpha>\<sigma> x)\<close>
| \<open>\<kappa>\<upsilon> (null\<kappa> x) = null\<upsilon> x\<close>

lemma \<kappa>\<upsilon>_surj: \<open>surj \<kappa>\<upsilon>\<close>
  using \<alpha>\<sigma>_surj by (metis \<kappa>\<upsilon>.simps(1) \<kappa>\<upsilon>.simps(2) \<kappa>\<upsilon>.simps(3) \<upsilon>.exhaust surj_def)

text\<open>By construction if the urelement of an individual term is exemplified by
     an (ur-)relation, it cannot be a null-object.\<close>
lemma urrel_null_false:
  assumes \<open>AOT_model_valid_in w (Rep_urrel f (\<kappa>\<upsilon> x))\<close>
  shows \<open>\<not>is_null\<kappa> x\<close>
  by (metis (mono_tags, lifting) assms Rep_urrel \<kappa>.collapse(3) \<kappa>\<upsilon>.simps(3)
        mem_Collect_eq)

thm \<alpha>\<sigma>_disc_pre

lemma \<alpha>\<sigma>_disc:
  assumes \<open>\<alpha>\<sigma> x = \<alpha>\<sigma> y\<close>
  assumes \<open>\<And> r . (r \<in> x) = (finite_card {\<kappa> . (\<forall>\<kappa>' . \<kappa>\<upsilon> \<kappa> = \<kappa>\<upsilon> \<kappa>' \<longrightarrow> \<kappa> = \<kappa>') \<and> AOT_model_valid_in w\<^sub>0 (Rep_urrel r (\<kappa>\<upsilon> \<kappa>))} = Some n)\<close>
  shows \<open>x = y\<close>
proof -
  show \<open>x = y\<close>
  proof (rule \<alpha>\<sigma>_disc_pre[OF assms(1)])
    have 0: \<open>(\<forall>y. (case (y, \<kappa>) of (\<omega>\<kappa> a, \<omega>\<kappa> b) \<Rightarrow> a = b | (\<omega>\<kappa> a, _) \<Rightarrow> False | (\<alpha>\<kappa> a, \<alpha>\<kappa> b) \<Rightarrow> \<alpha>\<sigma> a = \<alpha>\<sigma> b | (\<alpha>\<kappa> a, _) \<Rightarrow> False
                 | (null\<kappa> a, null\<kappa> b) \<Rightarrow> a = b | (null\<kappa> a, _) \<Rightarrow> False) \<longrightarrow>
                \<kappa> = y) = (\<forall>\<kappa>' . \<kappa>\<upsilon> \<kappa> = \<kappa>\<upsilon> \<kappa>' \<longrightarrow> \<kappa> = \<kappa>')\<close> for \<kappa>
      apply (induct \<kappa>)
        apply auto
      apply (metis \<kappa>.collapse(1) \<kappa>.exhaust_disc \<kappa>\<upsilon>.simps(1) \<kappa>\<upsilon>.simps(2) \<kappa>\<upsilon>.simps(3) \<upsilon>.disc(4) \<upsilon>.disc(5) \<upsilon>.distinct(3) \<upsilon>.sel(1) is_\<alpha>\<kappa>_def is_null\<kappa>_def)
      apply (smt (z3) \<kappa>.case_eq_if \<kappa>.collapse(1) \<kappa>.disc(1))
      apply (smt (z3) \<kappa>.collapse(2) \<kappa>.exhaust_disc \<kappa>.simps(11) \<kappa>\<upsilon>.simps(1) \<kappa>\<upsilon>.simps(2) \<kappa>\<upsilon>.simps(3) \<upsilon>.disc(8) \<upsilon>.disc(9) \<upsilon>.inject(2) \<upsilon>.simps(5) is_\<omega>\<kappa>_def is_null\<kappa>_def)
      apply (smt (z3) \<kappa>.case_eq_if \<kappa>.collapse(2) \<kappa>.disc(2) \<kappa>.disc(5) \<kappa>\<upsilon>.simps(2))
      apply (metis \<kappa>.exhaust_disc \<kappa>\<upsilon>.simps(1) \<kappa>\<upsilon>.simps(2) \<kappa>\<upsilon>.simps(3) \<upsilon>.disc(7) \<upsilon>.disc(8) \<upsilon>.disc(9) \<upsilon>.inject(3) is_\<alpha>\<kappa>_def is_\<omega>\<kappa>_def is_null\<kappa>_def)
      by (smt (verit, best) \<kappa>.case_eq_if \<kappa>.disc(3) \<kappa>.disc(6) \<kappa>.expand)
    have 1: \<open>(case \<kappa> of \<omega>\<kappa> x \<Rightarrow> \<omega>\<upsilon> x | \<alpha>\<kappa> x \<Rightarrow> \<sigma>\<upsilon> (\<alpha>\<sigma> x) | null\<kappa> x \<Rightarrow> null\<upsilon> x) = \<kappa>\<upsilon> \<kappa>\<close> for \<kappa>
      by (metis \<kappa>.case_eq_if \<kappa>.collapse(1) \<kappa>.collapse(2) \<kappa>.collapse(3) \<kappa>.exhaust_disc \<kappa>\<upsilon>.simps(1) \<kappa>\<upsilon>.simps(2) \<kappa>\<upsilon>.simps(3))
    show \<open>x =
    {urrel.
     finite_card
      {\<kappa>. (\<forall>y. (case (y, \<kappa>) of (\<omega>\<kappa> a, \<omega>\<kappa> b) \<Rightarrow> a = b | (\<omega>\<kappa> a, _) \<Rightarrow> False | (\<alpha>\<kappa> a, \<alpha>\<kappa> b) \<Rightarrow> \<alpha>\<sigma> a = \<alpha>\<sigma> b | (\<alpha>\<kappa> a, _) \<Rightarrow> False
                 | (null\<kappa> a, null\<kappa> b) \<Rightarrow> a = b | (null\<kappa> a, _) \<Rightarrow> False) \<longrightarrow>
                \<kappa> = y) \<and>
           AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel (case \<kappa> of \<omega>\<kappa> x \<Rightarrow> \<omega>\<upsilon> x | \<alpha>\<kappa> x \<Rightarrow> \<sigma>\<upsilon> (\<alpha>\<sigma> x) | null\<kappa> x \<Rightarrow> null\<upsilon> x))} =
       Some n}\<close>
      unfolding 0 1
      using assms(2) by auto
  qed
qed

text\<open>AOT requires any ordinary object to be @{emph \<open>possibly concrete\<close>} and that
     there is an object that is not actually, but possibly concrete.\<close>
consts AOT_model_concrete\<omega> :: \<open>\<omega> \<Rightarrow> w \<Rightarrow>  bool\<close>
specification (AOT_model_concrete\<omega>)
  AOT_model_\<omega>_concrete_in_some_world:
  \<open>\<exists> w . AOT_model_concrete\<omega> x w\<close>
  AOT_model_contingent_object:
  \<open>\<exists> x w . AOT_model_concrete\<omega> x w \<and> \<not>AOT_model_concrete\<omega> x w\<^sub>0\<close>
  by (rule exI[where x=\<open>\<lambda>_ w. w \<noteq> w\<^sub>0\<close>]) (auto simp: AOT_model_nonactual_world)

text\<open>We define a type class for AOT's terms specifying the conditions under which
     objects of that type denote and require the set of denoting terms to be
     non-empty.\<close>
class AOT_Term =
  fixes AOT_model_denotes :: \<open>'a \<Rightarrow> bool\<close>
  assumes AOT_model_denoting_ex: \<open>\<exists> x . AOT_model_denotes x\<close>

text\<open>All types except the type of propositions involve non-denoting terms. We
     define a refined type class for those.\<close>
class AOT_IncompleteTerm = AOT_Term +
  assumes AOT_model_nondenoting_ex: \<open>\<exists> x . \<not>AOT_model_denotes x\<close>

text\<open>Generic non-denoting term.\<close>
definition AOT_model_nondenoting :: \<open>'a::AOT_IncompleteTerm\<close> where
  \<open>AOT_model_nondenoting \<equiv> SOME \<tau> . \<not>AOT_model_denotes \<tau>\<close>
lemma AOT_model_nondenoing: \<open>\<not>AOT_model_denotes (AOT_model_nondenoting)\<close>
  using someI_ex[OF AOT_model_nondenoting_ex]
  unfolding AOT_model_nondenoting_def by blast

text\<open>@{const AOT_model_denotes} can trivially be extended to products of types.\<close>
instantiation prod :: (AOT_Term, AOT_Term) AOT_Term
begin
definition AOT_model_denotes_prod :: \<open>'a\<times>'b \<Rightarrow> bool\<close> where
  \<open>AOT_model_denotes_prod \<equiv> \<lambda>(x,y) . AOT_model_denotes x \<and> AOT_model_denotes y\<close>
instance proof
  show \<open>\<exists>x::'a\<times>'b. AOT_model_denotes x\<close>
    by (simp add: AOT_model_denotes_prod_def AOT_model_denoting_ex)
qed
end

text\<open>We specify a transformation of proposition-valued functions on terms, s.t.
     the result is fully determined by @{emph \<open>regular\<close>} terms. This will be required
     for modelling n-ary relations as functions on tuples while preserving AOT's
     definition of n-ary relation identity.\<close>
locale AOT_model_irregular_spec =
  fixes AOT_model_irregular :: \<open>('a \<Rightarrow> \<o>) \<Rightarrow> 'a \<Rightarrow> \<o>\<close>
    and AOT_model_regular :: \<open>'a \<Rightarrow> bool\<close>
    and AOT_model_term_equiv :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes AOT_model_irregular_false:
    \<open>\<not>AOT_model_valid_in w (AOT_model_irregular \<phi> x)\<close>
  assumes AOT_model_irregular_equiv:
    \<open>AOT_model_term_equiv x y \<Longrightarrow>
     AOT_model_irregular \<phi> x = AOT_model_irregular \<phi> y\<close>
  assumes AOT_model_irregular_eqI:
    \<open>(\<And> x . AOT_model_regular x \<Longrightarrow> \<phi> x = \<psi> x) \<Longrightarrow>
     AOT_model_irregular \<phi> x = AOT_model_irregular \<psi> x\<close>

text\<open>We introduce a type class for individual terms that specifies being regular,
     being equivalent (i.e. conceptually @{emph \<open>sharing urelements\<close>}) and the
     transformation on proposition-valued functions as specified above.\<close>
class AOT_IndividualTerm = AOT_IncompleteTerm +
  fixes AOT_model_regular :: \<open>'a \<Rightarrow> bool\<close>
  fixes AOT_model_term_equiv :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  fixes AOT_model_irregular :: \<open>('a \<Rightarrow> \<o>) \<Rightarrow> 'a \<Rightarrow> \<o>\<close>
  assumes AOT_model_irregular_nondenoting:
    \<open>\<not>AOT_model_regular x \<Longrightarrow> \<not>AOT_model_denotes x\<close>
  assumes AOT_model_term_equiv_part_equivp:
    \<open>equivp AOT_model_term_equiv\<close>
  assumes AOT_model_term_equiv_denotes:
    \<open>AOT_model_term_equiv x y \<Longrightarrow> (AOT_model_denotes x = AOT_model_denotes y)\<close>
  assumes AOT_model_term_equiv_regular:
    \<open>AOT_model_term_equiv x y \<Longrightarrow> (AOT_model_regular x = AOT_model_regular y)\<close>
  assumes AOT_model_irregular:
    \<open>AOT_model_irregular_spec AOT_model_irregular AOT_model_regular
                              AOT_model_term_equiv\<close>

interpretation AOT_model_irregular_spec AOT_model_irregular AOT_model_regular
                                        AOT_model_term_equiv
  using AOT_model_irregular .

text\<open>Our concrete type for individual terms satisfies the type class of
     individual terms.
     Note that all unary individuals are regular. In general an individual term
     may be a tuple and is regular, if at most one tuple element does not denote.\<close>
instantiation \<kappa> :: AOT_IndividualTerm
begin
definition AOT_model_term_equiv_\<kappa> :: \<open>\<kappa> \<Rightarrow> \<kappa> \<Rightarrow> bool\<close> where
  \<open>AOT_model_term_equiv_\<kappa> \<equiv> \<lambda> x y . \<kappa>\<upsilon> x = \<kappa>\<upsilon> y\<close>
definition AOT_model_denotes_\<kappa> :: \<open>\<kappa> \<Rightarrow> bool\<close> where
  \<open>AOT_model_denotes_\<kappa> \<equiv> \<lambda> x . \<not>is_null\<kappa> x\<close>
definition AOT_model_regular_\<kappa> :: \<open>\<kappa> \<Rightarrow> bool\<close> where
  \<open>AOT_model_regular_\<kappa> \<equiv> \<lambda> x . True\<close>
definition AOT_model_irregular_\<kappa> :: \<open>(\<kappa> \<Rightarrow> \<o>) \<Rightarrow> \<kappa> \<Rightarrow> \<o>\<close> where
  \<open>AOT_model_irregular_\<kappa> \<equiv> SOME \<phi> . AOT_model_irregular_spec \<phi>
                                        AOT_model_regular AOT_model_term_equiv\<close>
instance proof
  show \<open>\<exists>x :: \<kappa>. AOT_model_denotes x\<close>
    by (rule exI[where x=\<open>\<omega>\<kappa> undefined\<close>])
       (simp add: AOT_model_denotes_\<kappa>_def)
next
  show \<open>\<exists>x :: \<kappa>. \<not>AOT_model_denotes x\<close>
    by (rule exI[where x=\<open>null\<kappa> undefined\<close>])
       (simp add: AOT_model_denotes_\<kappa>_def AOT_model_regular_\<kappa>_def)
next
  show "\<not>AOT_model_regular x \<Longrightarrow> \<not> AOT_model_denotes x" for x :: \<kappa>
    by (simp add: AOT_model_regular_\<kappa>_def)
next
  show \<open>equivp (AOT_model_term_equiv :: \<kappa> \<Rightarrow> \<kappa> \<Rightarrow> bool)\<close>
    by (rule equivpI; rule reflpI exI sympI transpI)
       (simp_all add: AOT_model_term_equiv_\<kappa>_def)
next
  fix x y :: \<kappa>
  show \<open>AOT_model_term_equiv x y \<Longrightarrow> AOT_model_denotes x = AOT_model_denotes y\<close>
    by (metis AOT_model_denotes_\<kappa>_def AOT_model_term_equiv_\<kappa>_def \<kappa>.exhaust_disc
              \<kappa>\<upsilon>.simps \<upsilon>.disc(1,3,5,6) is_\<alpha>\<kappa>_def is_\<omega>\<kappa>_def is_null\<kappa>_def)
next
  fix x y :: \<kappa>
  show \<open>AOT_model_term_equiv x y \<Longrightarrow> AOT_model_regular x = AOT_model_regular y\<close>
    by (simp add: AOT_model_regular_\<kappa>_def)
next
  have "AOT_model_irregular_spec (\<lambda> \<phi> (x::\<kappa>) .  \<epsilon>\<^sub>\<o> w . False)
          AOT_model_regular AOT_model_term_equiv"
    by standard (auto simp: AOT_model_proposition_choice_simp)
  thus \<open>AOT_model_irregular_spec (AOT_model_irregular::(\<kappa>\<Rightarrow>\<o>) \<Rightarrow> \<kappa> \<Rightarrow> \<o>)
          AOT_model_regular AOT_model_term_equiv\<close>
    unfolding AOT_model_irregular_\<kappa>_def by (metis (no_types, lifting) someI_ex)
qed
end

text\<open>We define relations among individuals as proposition valued functions.
     @{emph \<open>Denoting\<close>} relations among single individuals will match the
     urrelations introduced above.\<close>
typedef 'a rel (\<open><_>\<close>) = \<open>UNIV::('a::AOT_IndividualTerm \<Rightarrow> \<o>) set\<close> ..
setup_lifting type_definition_rel

text\<open>We use the transformation specified above to "fix" the behaviour of
     functions on irregular terms.\<close>
definition fix_special :: \<open>('a::AOT_IndividualTerm \<Rightarrow> \<o>) \<Rightarrow> ('a \<Rightarrow> \<o>)\<close> where
  \<open>fix_special \<equiv> \<lambda> \<phi> x . if AOT_model_regular x
                          then \<phi> x else AOT_model_irregular \<phi> x\<close>
lemma fix_special_denoting:
  \<open>AOT_model_denotes x \<Longrightarrow> fix_special \<phi> x = \<phi> x\<close>
  by (meson AOT_model_irregular_nondenoting fix_special_def)
lemma fix_special_non_special:
  \<open>AOT_model_regular x \<Longrightarrow> fix_special \<phi> x = \<phi> x\<close>
  by (meson AOT_model_irregular_nondenoting fix_special_def)
lemma fix_special_special:
  \<open>\<not>AOT_model_regular x \<Longrightarrow> fix_special \<phi> x = AOT_model_irregular \<phi> x\<close>
  by (simp add: fix_special_def)

text\<open>Relations among individual terms are (potentially non-denoting) terms.
     A relation denotes, if it agrees on all equivalent terms (i.e. terms sharing
     urelements), is necessarily false on all non-denoting terms and is
     well-behaved on irregular terms.\<close>
instantiation rel :: (AOT_IndividualTerm) AOT_IncompleteTerm
begin
lift_definition AOT_model_denotes_rel :: \<open><'a> \<Rightarrow> bool\<close> is
  \<open>\<lambda> \<phi> . (\<forall> x y . AOT_model_term_equiv x y \<longrightarrow> \<phi> x = \<phi> y) \<and>
         (\<forall> w x . AOT_model_valid_in w (\<phi> x) \<longrightarrow> AOT_model_denotes x) \<and>
         (\<forall> x . \<not>AOT_model_regular x \<longrightarrow> \<phi> x = AOT_model_irregular \<phi> x)\<close> .
definition AOT_model_term_equiv_rel :: \<open><'a> \<Rightarrow> <'a> \<Rightarrow> bool\<close> where
  \<open>AOT_model_term_equiv_rel \<equiv> \<lambda> f g . AOT_model_denotes f \<and> AOT_model_denotes g \<and>
                                      f = g\<close>
instance proof
  have \<open>AOT_model_irregular (fix_special \<phi>) x = AOT_model_irregular \<phi> x\<close>
    for \<phi> and x :: 'a
    by (rule AOT_model_irregular_eqI) (simp add: fix_special_def)
  thus \<open>\<exists> x :: <'a> . AOT_model_denotes x\<close>
    by (safe intro!: exI[where x=\<open>Abs_rel (fix_special (\<lambda>x. \<epsilon>\<^sub>\<o> w . False))\<close>])
       (transfer; auto simp: AOT_model_proposition_choice_simp fix_special_def
                             AOT_model_irregular_equiv AOT_model_term_equiv_regular
                             AOT_model_irregular_false)
next
  show \<open>\<exists>f :: <'a> . \<not>AOT_model_denotes f\<close>
    by (rule exI[where x=\<open>Abs_rel (\<lambda>x. \<epsilon>\<^sub>\<o> w . True)\<close>];
        auto simp: AOT_model_denotes_rel.abs_eq AOT_model_nondenoting_ex
                   AOT_model_proposition_choice_simp)
qed
end

text\<open>Auxiliary lemmata.\<close>

lemma AOT_model_term_equiv_eps:
  shows \<open>AOT_model_term_equiv (Eps (AOT_model_term_equiv \<kappa>)) \<kappa>\<close>
    and \<open>AOT_model_term_equiv \<kappa> (Eps (AOT_model_term_equiv \<kappa>))\<close>
    and \<open>AOT_model_term_equiv \<kappa> \<kappa>' \<Longrightarrow>
         (Eps (AOT_model_term_equiv \<kappa>)) = (Eps (AOT_model_term_equiv \<kappa>'))\<close>
  apply (metis AOT_model_term_equiv_part_equivp equivp_def someI_ex)
  apply (metis AOT_model_term_equiv_part_equivp equivp_def someI_ex)
  by (metis AOT_model_term_equiv_part_equivp equivp_def)

lemma AOT_model_denotes_Abs_rel_fix_specialI:
  assumes \<open>\<And> x y . AOT_model_term_equiv x y \<Longrightarrow> \<phi> x = \<phi> y\<close>
      and \<open>\<And> w x . AOT_model_valid_in w (\<phi> x) \<Longrightarrow> AOT_model_denotes x\<close>
    shows \<open>AOT_model_denotes (Abs_rel (fix_special \<phi>))\<close>
proof -
  have \<open>AOT_model_irregular \<phi> x = AOT_model_irregular
          (\<lambda>x. if AOT_model_regular x then \<phi> x else AOT_model_irregular \<phi> x) x\<close>
    if \<open>\<not> AOT_model_regular x\<close>
    for x
    by (rule AOT_model_irregular_eqI) auto
  thus ?thesis
  unfolding AOT_model_denotes_rel.rep_eq
  using assms by (auto simp: AOT_model_irregular_false Abs_rel_inverse
                             AOT_model_irregular_equiv fix_special_def
                             AOT_model_term_equiv_regular)
qed

lemma AOT_model_term_equiv_rel_equiv:
  assumes \<open>AOT_model_denotes x\<close>
      and \<open>AOT_model_denotes y\<close>
    shows \<open>AOT_model_term_equiv x y = (\<forall> \<Pi> w . AOT_model_denotes \<Pi> \<longrightarrow>
            AOT_model_valid_in w (Rep_rel \<Pi> x) = AOT_model_valid_in w (Rep_rel \<Pi> y))\<close>
proof
  assume \<open>AOT_model_term_equiv x y\<close>
  thus \<open>\<forall> \<Pi> w . AOT_model_denotes \<Pi> \<longrightarrow> AOT_model_valid_in w (Rep_rel \<Pi> x) =
                                         AOT_model_valid_in w (Rep_rel \<Pi> y)\<close>
    by (simp add: AOT_model_denotes_rel.rep_eq)
next
  have 0: \<open>(AOT_model_denotes x' \<and> AOT_model_term_equiv x' y) =
           (AOT_model_denotes y' \<and> AOT_model_term_equiv y' y)\<close>
    if \<open>AOT_model_term_equiv x' y'\<close> for x' y'
    by (metis that AOT_model_term_equiv_denotes AOT_model_term_equiv_part_equivp
              equivp_def)
  assume \<open>\<forall> \<Pi> w . AOT_model_denotes \<Pi> \<longrightarrow> AOT_model_valid_in w (Rep_rel \<Pi> x) =
                                           AOT_model_valid_in w (Rep_rel \<Pi> y)\<close>
  moreover have \<open>AOT_model_denotes (Abs_rel (fix_special
    (\<lambda> x . \<epsilon>\<^sub>\<o> w . AOT_model_denotes x \<and> AOT_model_term_equiv x y)))\<close>
    (is "AOT_model_denotes ?r")
    by (rule AOT_model_denotes_Abs_rel_fix_specialI)
       (auto simp: 0 AOT_model_denotes_rel.rep_eq Abs_rel_inverse fix_special_def
                   AOT_model_proposition_choice_simp AOT_model_irregular_false)
  ultimately have \<open>AOT_model_valid_in w (Rep_rel ?r x) =
                   AOT_model_valid_in w (Rep_rel ?r y)\<close> for w
    by blast
  thus \<open>AOT_model_term_equiv x y\<close>
    by (simp add: Abs_rel_inverse AOT_model_proposition_choice_simp
                  fix_special_denoting[OF assms(1)] AOT_model_term_equiv_part_equivp
                  fix_special_denoting[OF assms(2)] assms equivp_reflp)
qed


text\<open>Denoting relations among terms of type @{typ \<kappa>} correspond to urrelations.\<close>

definition rel_to_urrel :: \<open><\<kappa>> \<Rightarrow> urrel\<close> where
  \<open>rel_to_urrel \<equiv> \<lambda> \<Pi> . Abs_urrel (\<lambda> u . Rep_rel \<Pi> (SOME x . \<kappa>\<upsilon> x = u))\<close>
definition urrel_to_rel :: \<open>urrel \<Rightarrow> <\<kappa>>\<close> where
  \<open>urrel_to_rel \<equiv> \<lambda> \<phi> . Abs_rel (\<lambda> x . Rep_urrel \<phi> (\<kappa>\<upsilon> x))\<close>

lemma urrel_quotient3: \<open>Quotient3 AOT_model_term_equiv_rel rel_to_urrel urrel_to_rel\<close>
proof (rule Quotient3I)
  have \<open>(\<lambda>u. Rep_urrel a (\<kappa>\<upsilon> (SOME x. \<kappa>\<upsilon> x = u))) = (\<lambda>u. Rep_urrel a u)\<close> for a
    by (rule ext) (metis (mono_tags, lifting) \<kappa>\<upsilon>_surj surj_f_inv_f verit_sko_ex')
  thus \<open>rel_to_urrel (urrel_to_rel a) = a\<close> for a
    by (simp add: Abs_rel_inverse rel_to_urrel_def urrel_to_rel_def
                  Rep_urrel_inverse)
next
  show \<open>AOT_model_term_equiv_rel (urrel_to_rel a) (urrel_to_rel a)\<close> for a
    unfolding AOT_model_term_equiv_rel_def urrel_to_rel_def
    by transfer (simp add: AOT_model_regular_\<kappa>_def AOT_model_denotes_\<kappa>_def
                           AOT_model_term_equiv_\<kappa>_def urrel_null_false)
next
  {
    fix a
    assume \<open>\<forall>w x. AOT_model_valid_in w (a x) \<longrightarrow> \<not> is_null\<kappa> x\<close>
    hence \<open>(\<lambda>u. a (SOME x. \<kappa>\<upsilon> x = u)) \<in>
           {\<phi>. \<forall>x w. \<not> AOT_model_valid_in w (\<phi> (null\<upsilon> x))}\<close>
      by (simp; metis (mono_tags, lifting) \<kappa>.exhaust_disc \<kappa>\<upsilon>.simps \<upsilon>.disc(1,3,5)
                                           \<upsilon>.disc(6) is_\<alpha>\<kappa>_def is_\<omega>\<kappa>_def someI_ex)
  } note 1 = this
  {
    fix r s :: \<open>\<kappa> \<Rightarrow> \<o>\<close>
    assume A: \<open>\<forall>x y. AOT_model_term_equiv x y \<longrightarrow> r x = r y\<close>
    assume \<open>\<forall>w x. AOT_model_valid_in w (r x) \<longrightarrow> AOT_model_denotes x\<close>
    hence 2: \<open>(\<lambda>u. r (SOME x. \<kappa>\<upsilon> x = u)) \<in>
              {\<phi>. \<forall>x w. \<not> AOT_model_valid_in w (\<phi> (null\<upsilon> x))}\<close>
      using 1 AOT_model_denotes_\<kappa>_def by meson
    assume B: \<open>\<forall>x y. AOT_model_term_equiv x y \<longrightarrow> s x = s y\<close>
    assume \<open>\<forall>w x. AOT_model_valid_in w (s x) \<longrightarrow> AOT_model_denotes x\<close>
    hence 3: \<open>(\<lambda>u. s (SOME x. \<kappa>\<upsilon> x = u)) \<in>
              {\<phi>. \<forall>x w. \<not> AOT_model_valid_in w (\<phi> (null\<upsilon> x))}\<close>
      using 1 AOT_model_denotes_\<kappa>_def by meson
    assume \<open>Abs_urrel (\<lambda>u. r (SOME x. \<kappa>\<upsilon> x = u)) =
            Abs_urrel (\<lambda>u. s (SOME x. \<kappa>\<upsilon> x = u))\<close>
    hence 4: \<open>r (SOME x. \<kappa>\<upsilon> x = u) = s (SOME x::\<kappa>. \<kappa>\<upsilon> x = u)\<close> for u
      unfolding Abs_urrel_inject[OF 2 3] by metis
    have \<open>r x = s x\<close> for x
      using 4[of \<open>\<kappa>\<upsilon> x\<close>]
      by (metis (mono_tags, lifting) A B AOT_model_term_equiv_\<kappa>_def someI_ex)
    hence \<open>r = s\<close> by auto
  } 
  thus \<open>AOT_model_term_equiv_rel r s =
        (AOT_model_term_equiv_rel r r \<and> AOT_model_term_equiv_rel s s \<and>
         rel_to_urrel r = rel_to_urrel s)\<close> for r s
    unfolding AOT_model_term_equiv_rel_def rel_to_urrel_def
    by transfer auto
qed

lemma urrel_quotient:
  \<open>Quotient AOT_model_term_equiv_rel rel_to_urrel urrel_to_rel
            (\<lambda>x y. AOT_model_term_equiv_rel x x \<and> rel_to_urrel x = y)\<close>
  using Quotient3_to_Quotient[OF urrel_quotient3] by auto


text\<open>Unary individual terms are always regular and equipped with encoding and
     concreteness. The specification of the type class anticipates the required
     properties for deriving the axiom system.\<close>
class AOT_UnaryIndividualTerm =
  fixes AOT_model_enc :: \<open>'a \<Rightarrow> <'a::AOT_IndividualTerm> \<Rightarrow> bool\<close>
    and AOT_model_concrete :: \<open>w \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes AOT_model_no_special_nondenoting:
      \<open>AOT_model_regular x\<close> \<comment> \<open>All unary individual terms are regular.\<close>
      and AOT_model_enc_relid:
        \<open>AOT_model_denotes F \<Longrightarrow>
         AOT_model_denotes G \<Longrightarrow>
         (\<And> x . AOT_model_enc x F \<longleftrightarrow> AOT_model_enc x G)
         \<Longrightarrow> F = G\<close>
      and AOT_model_A_objects:
        \<open>\<exists>x . AOT_model_denotes x \<and>
              (\<forall>w. \<not> AOT_model_concrete w x) \<and>
              (\<forall>F. AOT_model_denotes F \<longrightarrow> AOT_model_enc x F = \<phi> F)\<close>
      and AOT_model_contingent:
        \<open>\<exists> x w. AOT_model_concrete w x \<and> \<not> AOT_model_concrete w\<^sub>0 x\<close>
      and AOT_model_nocoder:
        \<open>AOT_model_concrete w x \<Longrightarrow> \<not>AOT_model_enc x F\<close>
      and AOT_model_concrete_equiv:
        \<open>AOT_model_term_equiv x y \<Longrightarrow>
          AOT_model_concrete w x = AOT_model_concrete w y\<close>
      and AOT_model_concrete_denotes:
        \<open>AOT_model_concrete w x \<Longrightarrow> AOT_model_denotes x\<close>


text\<open>Instantiate the class of unary individual terms for our concrete type of
     individual terms @{typ \<kappa>}.\<close>
instantiation \<kappa> :: AOT_UnaryIndividualTerm
begin                          

definition AOT_model_enc_\<kappa> :: \<open>\<kappa> \<Rightarrow> <\<kappa>> \<Rightarrow> bool\<close> where
  \<open>AOT_model_enc_\<kappa> \<equiv> \<lambda> x F .
      case x of \<alpha>\<kappa> a \<Rightarrow> AOT_model_denotes F \<and> rel_to_urrel F \<in> a
              | _ \<Rightarrow> False\<close>
primrec AOT_model_concrete_\<kappa> :: \<open>w \<Rightarrow> \<kappa> \<Rightarrow> bool\<close> where
  \<open>AOT_model_concrete_\<kappa> w (\<omega>\<kappa> x) = AOT_model_concrete\<omega> x w\<close>
| \<open>AOT_model_concrete_\<kappa> w (\<alpha>\<kappa> x) = False\<close>
| \<open>AOT_model_concrete_\<kappa> w (null\<kappa> x) = False\<close>

lemma AOT_meta_A_objects_\<kappa>:
  \<open>\<exists>x :: \<kappa>. AOT_model_denotes x \<and>
            (\<forall>w. \<not> AOT_model_concrete w x) \<and>
            (\<forall>F. AOT_model_denotes F \<longrightarrow> AOT_model_enc x F = \<phi> F)\<close> for \<phi>
  apply (rule exI[where x=\<open>\<alpha>\<kappa> {f . \<phi> (urrel_to_rel f)}\<close>])
  apply (simp add: AOT_model_enc_\<kappa>_def AOT_model_denotes_\<kappa>_def)
  by (metis (no_types, lifting) AOT_model_term_equiv_rel_def urrel_quotient
                                Quotient_rep_abs_fold_unmap)

instance proof
  show \<open>AOT_model_regular x\<close> for x :: \<kappa>
    by (simp add: AOT_model_regular_\<kappa>_def)
next
  fix F G :: \<open><\<kappa>>\<close>
  assume \<open>AOT_model_denotes F\<close>
  moreover assume \<open>AOT_model_denotes G\<close>
  moreover assume \<open>\<And>x. AOT_model_enc x F = AOT_model_enc x G\<close>
  moreover obtain x where \<open>\<forall>G. AOT_model_denotes G \<longrightarrow> AOT_model_enc x G = (F = G)\<close>
    using AOT_meta_A_objects_\<kappa> by blast
  ultimately show \<open>F = G\<close> by blast
next
  show \<open>\<exists>x :: \<kappa>. AOT_model_denotes x \<and>
                 (\<forall>w. \<not> AOT_model_concrete w x) \<and>
                 (\<forall>F. AOT_model_denotes F \<longrightarrow> AOT_model_enc x F = \<phi> F)\<close> for \<phi>
    using AOT_meta_A_objects_\<kappa> .
next
  show \<open>\<exists> (x::\<kappa>) w. AOT_model_concrete w x \<and> \<not> AOT_model_concrete w\<^sub>0 x\<close>
    using AOT_model_concrete_\<kappa>.simps(1) AOT_model_contingent_object by blast
next
  show \<open>AOT_model_concrete w x \<Longrightarrow> \<not> AOT_model_enc x F\<close> for w and x :: \<kappa> and F
    by (metis AOT_model_concrete_\<kappa>.simps(2) AOT_model_enc_\<kappa>_def \<kappa>.case_eq_if
              \<kappa>.collapse(2))
next
  show \<open>AOT_model_concrete w x = AOT_model_concrete w y\<close>
    if \<open>AOT_model_term_equiv x y\<close>
    for x y :: \<kappa> and w
    using that by (induct x; induct y; auto simp: AOT_model_term_equiv_\<kappa>_def)
next
  show \<open>AOT_model_concrete w x \<Longrightarrow> AOT_model_denotes x\<close> for w and x :: \<kappa>
    by (metis AOT_model_concrete_\<kappa>.simps(3) AOT_model_denotes_\<kappa>_def \<kappa>.collapse(3))
qed
end

text\<open>Products of unary individual terms and individual terms are individual terms.
     A tuple is regular, if at most one element does not denote. I.e. a pair is
     regular, if the first (unary) element denotes and the second is regular (i.e.
     at most one of its recursive tuple elements does not denote), or the first does
     not denote, but the second denotes (i.e. all its recursive tuple elements
     denote).\<close>
instantiation prod :: (AOT_UnaryIndividualTerm, AOT_IndividualTerm) AOT_IndividualTerm
begin
definition AOT_model_regular_prod :: \<open>'a\<times>'b \<Rightarrow> bool\<close> where
  \<open>AOT_model_regular_prod \<equiv> \<lambda> (x,y) . AOT_model_denotes x \<and> AOT_model_regular y \<or>
                                      \<not>AOT_model_denotes x \<and> AOT_model_denotes y\<close>
definition AOT_model_term_equiv_prod :: \<open>'a\<times>'b \<Rightarrow> 'a\<times>'b \<Rightarrow> bool\<close> where
  \<open>AOT_model_term_equiv_prod \<equiv>  \<lambda> (x\<^sub>1,y\<^sub>1) (x\<^sub>2,y\<^sub>2) .
    AOT_model_term_equiv x\<^sub>1 x\<^sub>2 \<and> AOT_model_term_equiv y\<^sub>1 y\<^sub>2\<close>
function AOT_model_irregular_prod :: \<open>('a\<times>'b \<Rightarrow> \<o>) \<Rightarrow> 'a\<times>'b \<Rightarrow> \<o>\<close> where
  AOT_model_irregular_proj2: \<open>AOT_model_denotes x \<Longrightarrow>
    AOT_model_irregular \<phi> (x,y) =
    AOT_model_irregular (\<lambda>y. \<phi> (SOME x' . AOT_model_term_equiv x x', y)) y\<close>
| AOT_model_irregular_proj1: \<open>\<not>AOT_model_denotes x \<and> AOT_model_denotes y \<Longrightarrow>
    AOT_model_irregular \<phi> (x,y) =
    AOT_model_irregular (\<lambda>x. \<phi> (x, SOME y' . AOT_model_term_equiv y y')) x\<close>
| AOT_model_irregular_prod_generic: \<open>\<not>AOT_model_denotes x \<and> \<not>AOT_model_denotes y \<Longrightarrow>
    AOT_model_irregular \<phi> (x,y) =
    (SOME \<Phi> . AOT_model_irregular_spec \<Phi> AOT_model_regular AOT_model_term_equiv)
      \<phi> (x,y)\<close>
  by auto blast
termination using "termination" by blast

instance proof
  obtain x :: 'a and y :: 'b where
    \<open>\<not>AOT_model_denotes x\<close> and \<open>\<not>AOT_model_denotes y\<close>
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
    by (metis (mono_tags, lifting) AOT_model_denotes_prod_def case_prod_unfold
          AOT_model_irregular_nondenoting AOT_model_regular_prod_def)
next
  fix x y :: \<open>'a\<times>'b\<close>
  show \<open>AOT_model_term_equiv x y \<Longrightarrow> AOT_model_denotes x = AOT_model_denotes y\<close>
    by (metis (mono_tags, lifting) AOT_model_denotes_prod_def case_prod_beta
        AOT_model_term_equiv_denotes AOT_model_term_equiv_prod_def )
next
  fix x y :: \<open>'a\<times>'b\<close>
  show \<open>AOT_model_term_equiv x y \<Longrightarrow> AOT_model_regular x = AOT_model_regular y\<close>
    by (induct x; induct y;
        simp add: AOT_model_term_equiv_prod_def AOT_model_regular_prod_def)
       (meson AOT_model_term_equiv_denotes AOT_model_term_equiv_regular)
next
  interpret sp: AOT_model_irregular_spec \<open>\<lambda>\<phi> (x::'a\<times>'b) . \<epsilon>\<^sub>\<o> w . False\<close>
                    AOT_model_regular AOT_model_term_equiv
    by (simp add: AOT_model_irregular_spec_def AOT_model_proposition_choice_simp)
  have ex_spec: \<open>\<exists> \<phi> :: ('a\<times>'b \<Rightarrow> \<o>) \<Rightarrow> 'a\<times>'b \<Rightarrow> \<o> .
    AOT_model_irregular_spec \<phi> AOT_model_regular AOT_model_term_equiv\<close>
    using sp.AOT_model_irregular_spec_axioms by blast
  have some_spec: \<open>AOT_model_irregular_spec
    (SOME \<phi> :: ('a\<times>'b \<Rightarrow> \<o>) \<Rightarrow> 'a\<times>'b \<Rightarrow> \<o> .
        AOT_model_irregular_spec \<phi> AOT_model_regular AOT_model_term_equiv)
    AOT_model_regular AOT_model_term_equiv\<close>
    using someI_ex[OF ex_spec] by argo
  interpret sp_some: AOT_model_irregular_spec
    \<open>SOME \<phi> :: ('a\<times>'b \<Rightarrow> \<o>) \<Rightarrow> 'a\<times>'b \<Rightarrow> \<o> .
        AOT_model_irregular_spec \<phi> AOT_model_regular AOT_model_term_equiv\<close>
    AOT_model_regular AOT_model_term_equiv
    using some_spec by blast
  show \<open>AOT_model_irregular_spec (AOT_model_irregular :: ('a\<times>'b \<Rightarrow> \<o>) \<Rightarrow> 'a\<times>'b \<Rightarrow> \<o>)
          AOT_model_regular AOT_model_term_equiv\<close>
  proof
    have \<open>\<not>AOT_model_valid_in w (AOT_model_irregular \<phi> (a, b))\<close>
      for w \<phi> and a :: 'a and b :: 'b
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
        assume \<open>AOT_model_denotes x\<^sub>1\<close>
        moreover hence \<open>AOT_model_denotes y\<^sub>1\<close>
          using AOT_model_term_equiv_denotes AOT_model_term_equiv_regular
                x\<^sub>1y\<^sub>1_equiv x\<^sub>2y\<^sub>2_equiv by blast
        ultimately have \<open>AOT_model_irregular \<phi> (x\<^sub>1,x\<^sub>2) =
                         AOT_model_irregular \<phi> (y\<^sub>1,y\<^sub>2)\<close>
          using AOT_model_irregular_equiv AOT_model_term_equiv_eps(3)
                x\<^sub>1y\<^sub>1_equiv x\<^sub>2y\<^sub>2_equiv by fastforce
      }
      moreover {
        assume \<open>~AOT_model_denotes x\<^sub>1 \<and> AOT_model_denotes x\<^sub>2\<close>
        moreover hence \<open>~AOT_model_denotes y\<^sub>1 \<and> AOT_model_denotes y\<^sub>2\<close>
          by (meson AOT_model_term_equiv_denotes x\<^sub>1y\<^sub>1_equiv x\<^sub>2y\<^sub>2_equiv)
        ultimately have \<open>AOT_model_irregular \<phi> (x\<^sub>1,x\<^sub>2) =
                         AOT_model_irregular \<phi> (y\<^sub>1,y\<^sub>2)\<close>
          using AOT_model_irregular_equiv AOT_model_term_equiv_eps(3)
                x\<^sub>1y\<^sub>1_equiv x\<^sub>2y\<^sub>2_equiv by fastforce
      }
      moreover {
        assume denotes_x: \<open>(\<not>AOT_model_denotes x\<^sub>1 \<and> \<not>AOT_model_denotes x\<^sub>2)\<close>
        hence denotes_y: \<open>(\<not>AOT_model_denotes y\<^sub>1 \<and> \<not>AOT_model_denotes y\<^sub>2)\<close>
          by (meson AOT_model_term_equiv_denotes AOT_model_term_equiv_regular
                    x\<^sub>1y\<^sub>1_equiv x\<^sub>2y\<^sub>2_equiv)
        have eps_eq: \<open>Eps (AOT_model_term_equiv x\<^sub>1) = Eps (AOT_model_term_equiv y\<^sub>1)\<close>
          by (simp add: AOT_model_term_equiv_eps(3) x\<^sub>1y\<^sub>1_equiv)
        have \<open>AOT_model_irregular \<phi> (x\<^sub>1,x\<^sub>2) = AOT_model_irregular \<phi> (y\<^sub>1,y\<^sub>2)\<close>
          using denotes_x denotes_y
          using sp_some.AOT_model_irregular_equiv xy_equiv by auto
      }
      moreover {
        assume denotes_x: \<open>\<not>AOT_model_denotes x\<^sub>1 \<and> AOT_model_denotes x\<^sub>2\<close>
        hence denotes_y: \<open>\<not>AOT_model_denotes y\<^sub>1 \<and> AOT_model_denotes y\<^sub>2\<close>
          by (meson AOT_model_term_equiv_denotes x\<^sub>1y\<^sub>1_equiv x\<^sub>2y\<^sub>2_equiv)
        have eps_eq: \<open>Eps (AOT_model_term_equiv x\<^sub>2) = Eps (AOT_model_term_equiv y\<^sub>2)\<close>
          by (simp add: AOT_model_term_equiv_eps(3) x\<^sub>2y\<^sub>2_equiv)
        have \<open>AOT_model_irregular \<phi> (x\<^sub>1,x\<^sub>2) = AOT_model_irregular \<phi> (y\<^sub>1,y\<^sub>2)\<close>
          using denotes_x denotes_y
          using AOT_model_irregular_nondenoting calculation(2) by blast
      }
      ultimately have \<open>AOT_model_irregular \<phi> (x\<^sub>1,x\<^sub>2) = AOT_model_irregular \<phi> (y\<^sub>1,y\<^sub>2)\<close>
        using AOT_model_term_equiv_denotes AOT_model_term_equiv_regular
              sp_some.AOT_model_irregular_equiv x\<^sub>1y\<^sub>1_equiv x\<^sub>2y\<^sub>2_equiv xy_equiv
        by blast
    } note 0 = this
    show \<open>AOT_model_term_equiv x y \<Longrightarrow>
          AOT_model_irregular \<phi> x = AOT_model_irregular \<phi> y\<close>
      for x y :: \<open>'a\<times>'b\<close> and \<phi>
      by (induct x; induct y; simp add: AOT_model_term_equiv_prod_def 0)
  next
    fix \<phi> \<psi> :: \<open>'a\<times>'b \<Rightarrow> \<o>\<close>
    assume \<open>AOT_model_regular x \<Longrightarrow> \<phi> x = \<psi> x\<close> for x
    hence \<open>\<phi> (x, y) = \<psi> (x, y)\<close>
      if \<open>AOT_model_denotes x \<and> AOT_model_regular y \<or>
          \<not>AOT_model_denotes x \<and> AOT_model_denotes y\<close> for x y
      using that unfolding AOT_model_regular_prod_def by simp
    hence \<open>AOT_model_irregular \<phi> (x,y) = AOT_model_irregular \<psi> (x,y)\<close>
      for x :: 'a and y :: 'b
    proof (induct arbitrary: \<psi> \<phi> rule: AOT_model_irregular_prod.induct)
      case (1 x y \<phi>)
      thus ?case
        apply simp
        by (meson AOT_model_irregular_eqI AOT_model_irregular_nondenoting
                  AOT_model_term_equiv_denotes AOT_model_term_equiv_eps(1))
    next
      case (2 x y \<phi>)
      thus ?case
        apply simp
        by (meson AOT_model_irregular_nondenoting AOT_model_term_equiv_denotes
                  AOT_model_term_equiv_eps(1))
    next
      case (3 x y \<phi>)
      thus ?case
        apply simp
        by (metis (mono_tags, lifting) AOT_model_regular_prod_def case_prod_conv
                                       sp_some.AOT_model_irregular_eqI surj_pair)
    qed
    thus \<open>AOT_model_irregular \<phi> x = AOT_model_irregular \<psi> x\<close> for  x :: \<open>'a\<times>'b\<close>
      by (metis surjective_pairing)
  qed
qed
end

text\<open>Introduction rules for term equivalence on tuple terms.\<close>
lemma AOT_meta_prod_equivI:
  shows "\<And> (a::'a::AOT_UnaryIndividualTerm) x (y :: 'b::AOT_IndividualTerm) .
            AOT_model_term_equiv x y \<Longrightarrow> AOT_model_term_equiv (a,x) (a,y)"
    and "\<And> (x::'a::AOT_UnaryIndividualTerm) y (b :: 'b::AOT_IndividualTerm) .
            AOT_model_term_equiv x y \<Longrightarrow> AOT_model_term_equiv (x,b) (y,b)"
    unfolding AOT_model_term_equiv_prod_def
    by (simp add: AOT_model_term_equiv_part_equivp equivp_reflp)+

text\<open>The unit type and the type of propositions are trivial instances of terms.\<close>

instantiation unit :: AOT_Term
begin
definition AOT_model_denotes_unit :: \<open>unit \<Rightarrow> bool\<close> where
  \<open>AOT_model_denotes_unit \<equiv> \<lambda>_. True\<close>
instance proof
  show \<open>\<exists>x::unit. AOT_model_denotes x\<close>
    by (simp add: AOT_model_denotes_unit_def)
qed
end

instantiation \<o> :: AOT_Term
begin
definition AOT_model_denotes_\<o> :: \<open>\<o> \<Rightarrow> bool\<close> where
  \<open>AOT_model_denotes_\<o> \<equiv> \<lambda>_. True\<close>
instance proof
  show \<open>\<exists>x::\<o>. AOT_model_denotes x\<close>
    by (simp add: AOT_model_denotes_\<o>_def)
qed
end

text\<open>AOT's variables are modelled by restricting the type of terms to those terms
     that denote.\<close>
typedef 'a AOT_var = \<open>{ x :: 'a::AOT_Term . AOT_model_denotes x }\<close>
  morphisms AOT_term_of_var AOT_var_of_term
  by (simp add: AOT_model_denoting_ex)

text\<open>Simplify automatically generated theorems and rules.\<close>
declare AOT_var_of_term_induct[induct del]
        AOT_var_of_term_cases[cases del]
        AOT_term_of_var_induct[induct del]
        AOT_term_of_var_cases[cases del]
lemmas AOT_var_of_term_inverse = AOT_var_of_term_inverse[simplified]
   and AOT_var_of_term_inject = AOT_var_of_term_inject[simplified]
   and AOT_var_of_term_induct =
          AOT_var_of_term_induct[simplified, induct type: AOT_var]
   and AOT_var_of_term_cases =
          AOT_var_of_term_cases[simplified, cases type: AOT_var]
   and AOT_term_of_var = AOT_term_of_var[simplified]
   and AOT_term_of_var_cases =
          AOT_term_of_var_cases[simplified, induct pred: AOT_term_of_var]
   and AOT_term_of_var_induct =
          AOT_term_of_var_induct[simplified, induct pred: AOT_term_of_var]
   and AOT_term_of_var_inverse = AOT_term_of_var_inverse[simplified]
   and AOT_term_of_var_inject = AOT_term_of_var_inject[simplified]

text\<open>Equivalence by definition is modelled as necessary equivalence.\<close>
consts AOT_model_equiv_def :: \<open>\<o> \<Rightarrow> \<o> \<Rightarrow> bool\<close>
specification(AOT_model_equiv_def)
  AOT_model_equiv_def: \<open>AOT_model_equiv_def \<phi> \<psi> = (\<forall> v . AOT_model_valid_in v \<phi> =
                                                         AOT_model_valid_in v \<psi>)\<close>
  by (rule exI[where x=\<open>\<lambda> \<phi> \<psi> . \<forall> v . AOT_model_valid_in v \<phi> =
                                       AOT_model_valid_in v \<psi>\<close>]) simp

text\<open>Identity by definition is modelled as identity for denoting terms plus
     co-denoting.\<close>
consts AOT_model_id_def :: \<open>('b \<Rightarrow> 'a::AOT_Term) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool\<close>
specification(AOT_model_id_def)
  AOT_model_id_def: \<open>(AOT_model_id_def \<tau> \<sigma>) = (\<forall> \<alpha> . if AOT_model_denotes (\<sigma> \<alpha>)
                                                     then \<tau> \<alpha> = \<sigma> \<alpha>
                                                     else \<not>AOT_model_denotes (\<tau> \<alpha>))\<close>
  by (rule exI[where x="\<lambda> \<tau> \<sigma> . \<forall> \<alpha> . if AOT_model_denotes (\<sigma> \<alpha>)
                                      then \<tau> \<alpha> = \<sigma> \<alpha>
                                      else \<not>AOT_model_denotes (\<tau> \<alpha>)"])
     blast

text\<open>Models for modally-strict and modally-fragile axioms as necessary,
     resp. actually valid propositions.\<close>
definition AOT_model_axiom where
  \<open>AOT_model_axiom \<equiv> \<lambda> \<phi> . \<forall> v . AOT_model_valid_in v \<phi>\<close>
definition AOT_model_act_axiom where
  \<open>AOT_model_act_axiom \<equiv> \<lambda> \<phi> . AOT_model_valid_in w\<^sub>0 \<phi>\<close>

lemma AOT_model_axiomI:
  assumes \<open>\<And>v . AOT_model_valid_in v \<phi>\<close>
  shows \<open>AOT_model_axiom \<phi>\<close>
  unfolding AOT_model_axiom_def using assms ..

lemma AOT_model_act_axiomI:
  assumes \<open>AOT_model_valid_in w\<^sub>0 \<phi>\<close>
  shows \<open>AOT_model_act_axiom \<phi>\<close>
  unfolding AOT_model_act_axiom_def using assms .

(*<*)
end
(*>*)