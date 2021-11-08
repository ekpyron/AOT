(*<*)
theory AOT_model
  imports Main "HOL-Cardinals.Cardinals" "HOL-Library.Countable"
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
typedef \<sigma> = \<open>UNIV::(nat\<times>\<sigma>') set\<close>..

lemma \<sigma>_inf: \<open>Cinfinite |UNIV::\<sigma> set|\<close>
proof -
  have \<open>\<exists>f :: nat \<Rightarrow> \<sigma> . inj f\<close>
    by (auto intro!: exI[where x=\<open>\<lambda>n . Abs_\<sigma> (n,undefined)\<close>] injI simp: Abs_\<sigma>_inject)
  thus ?thesis
    by (metis Cnotzero_UNIV Field_card_of card_of_image cinfinite_def cinfinite_mono
              infinite_UNIV_char_0 inj_imp_surj_inv)
qed


typedecl null \<comment> \<open>Null-Urelements representing non-denoting terms.\<close>

datatype \<upsilon> = \<omega>\<upsilon> \<omega> | \<sigma>\<upsilon> \<sigma> | is_null\<upsilon>: null\<upsilon> null \<comment> \<open>Type of Urelements\<close>

text\<open>Urrelations are proposition-valued functions on Urelements.
     Urrelations are required to evaluate to necessarily false propositions for
     Null-Urelements (note that there may be several distinct necessarily false
     propositions).\<close>
typedef urrel = \<open>{ \<phi> . \<forall> x w . \<not>AOT_model_valid_in w (\<phi> (null\<upsilon> x)) }\<close>
  by (rule exI[where x=\<open>\<lambda> x . (\<epsilon>\<^sub>\<o> w . \<not>is_null\<upsilon> x)\<close>])
     (auto simp: AOT_model_proposition_choice_simp)

text\<open>Individual terms are either ordinary objects, represented by ordinary urelements,
     abstract objects, modelled as sets of Urrelations, or null objects, used to
     represent non-denoting definite descriptions.\<close>
datatype \<kappa> = \<omega>\<kappa> \<omega> | \<alpha>\<kappa> \<open>urrel set\<close> | is_null\<kappa>: null\<kappa> null

text\<open>Abstract objects will be modelled as sets of urrelations and will
     have to be mapped back surjectively into the set of special urelements.
     We show that any mapping from abstract objects to special urelements
     has to involve at least one large set of collapsed abstract objects.
     We will use this fact to extend arbitrary mappings from abstract objects
     to special urelements to surjective mappings.\<close>
lemma \<alpha>\<sigma>_pigeonhole:
  \<comment> \<open>For any arbitrary mapping @{term \<alpha>\<sigma>} from sets of urrelations to special
     urelements, there exists an abstract object x, s.t. the cardinal of the set
     of special urelements is strictly smaller than the cardinal of the set of
     abstract objects that are mapped to the same urelement as x under @{term \<alpha>\<sigma>}.\<close>
  \<open>\<exists>x . |UNIV::\<sigma> set| <o |{y . \<alpha>\<sigma> x = \<alpha>\<sigma> y}|\<close>
  for \<alpha>\<sigma> :: \<open>urrel set \<Rightarrow> \<sigma>\<close>
proof(rule ccontr)
  have card_\<sigma>_set_set_bound: \<open>|UNIV::\<sigma> set set| \<le>o |UNIV::urrel set|\<close>
  proof -
    let ?pick = \<open>\<lambda>u s . \<epsilon>\<^sub>\<o> w . case u of (\<sigma>\<upsilon> s') \<Rightarrow> s' \<in> s | _ \<Rightarrow> False\<close>
    have \<open>\<exists>f :: \<sigma> set \<Rightarrow> urrel . inj f\<close>
    proof
      show \<open>inj (\<lambda>s . Abs_urrel (\<lambda>u . ?pick u s))\<close>
      proof(rule injI)
        fix x y
        assume \<open>Abs_urrel (\<lambda>u. ?pick u x) = Abs_urrel (\<lambda>u. ?pick u y)\<close>
        hence \<open>(\<lambda>u. ?pick u x) = (\<lambda>u. ?pick u y)\<close>
          by (auto intro!: Abs_urrel_inject[THEN iffD1]
                     simp: AOT_model_proposition_choice_simp)
        hence \<open>AOT_model_valid_in w\<^sub>0 (?pick (\<sigma>\<upsilon> s) x) =
               AOT_model_valid_in w\<^sub>0 (?pick (\<sigma>\<upsilon> s) y)\<close>
          for s by metis
        hence \<open>(s \<in> x) = (s \<in> y)\<close> for s
          by (auto simp: AOT_model_proposition_choice_simp)
        thus \<open>x = y\<close>
          by blast
      qed
    qed
    thus ?thesis
      by (metis card_of_image inj_imp_surj_inv)
  qed

  text\<open>Assume, for a proof by contradiction, that there is no large collapsed set.\<close>
  assume \<open>\<nexists>x . |UNIV::\<sigma> set| <o |{y . \<alpha>\<sigma> x = \<alpha>\<sigma> y}|\<close>
  hence A: \<open>\<forall>x . |{y . \<alpha>\<sigma> x = \<alpha>\<sigma> y}| \<le>o |UNIV::\<sigma> set|\<close>
    by auto
  have union_univ: \<open>(\<Union>x \<in> range(inv \<alpha>\<sigma>) . {y . \<alpha>\<sigma> x = \<alpha>\<sigma> y}) = UNIV\<close>
    by auto (meson f_inv_into_f range_eqI)

  text\<open>We prove by case distinction: there is either finitely many or
       infinitely many special urelements.\<close>
  {
    text\<open>Finite case.\<close>
    assume finite_\<sigma>_set: \<open>finite (UNIV::\<sigma> set)\<close>
    hence finite_collapsed: \<open>finite {y . \<alpha>\<sigma> x = \<alpha>\<sigma> y}\<close> for x
      using A card_of_ordLeq_infinite by blast
    hence 0: \<open>\<forall>x . card {y . \<alpha>\<sigma> x = \<alpha>\<sigma> y} \<le> card (UNIV::\<sigma> set)\<close>
      by (metis A \<open>finite UNIV\<close> card_of_ordLeq inj_on_iff_card_le)
    have 1: \<open>card (range (inv \<alpha>\<sigma>)) \<le> card (UNIV::\<sigma> set)\<close>
      using \<open>finite UNIV\<close> card_image_le by blast
    hence 2: \<open>finite (range (inv \<alpha>\<sigma>))\<close>
      using \<open>finite UNIV\<close> by blast

    define n where \<open>n = card (UNIV::urrel set set)\<close>
    define m where \<open>m = card (UNIV::\<sigma> set)\<close>

    have \<open>n = card (\<Union>x \<in> range(inv \<alpha>\<sigma>) . {y . \<alpha>\<sigma> x = \<alpha>\<sigma> y})\<close>
      unfolding n_def using union_univ by argo
    also have \<open>\<dots> \<le> (\<Sum>i\<in>range (inv \<alpha>\<sigma>). card {y. \<alpha>\<sigma> i = \<alpha>\<sigma> y})\<close>
      using card_UN_le 2 by blast
    also have \<open>\<dots> \<le> (\<Sum>i\<in>range (inv \<alpha>\<sigma>). card (UNIV::\<sigma> set))\<close>
      by (metis (no_types, lifting) 0 sum_mono)
    also have \<open>\<dots> \<le> card (range (inv \<alpha>\<sigma>)) * card (UNIV::\<sigma> set)\<close>
      using sum_bounded_above by auto
    also have \<open>\<dots> \<le> card (UNIV::\<sigma> set) * card (UNIV::\<sigma> set)\<close>
      using 1 by force
    also have \<open>\<dots> = m*m\<close>
      unfolding m_def by blast
    finally have n_upper: \<open>n \<le> m*m\<close>.

    have \<open>finite (\<Union>x \<in> range(inv \<alpha>\<sigma>) . {y . \<alpha>\<sigma> x = \<alpha>\<sigma> y})\<close>
      using 2 finite_collapsed by blast
    hence finite_\<alpha>set: \<open>finite (UNIV::urrel set set)\<close>
      using union_univ by argo

    have \<open>2^2^m = (2::nat)^(card (UNIV::\<sigma> set set))\<close>
      by (metis Pow_UNIV card_Pow finite_\<sigma>_set m_def)
    moreover have \<open>card (UNIV::\<sigma> set set) \<le> (card (UNIV::urrel set))\<close>
      using card_\<sigma>_set_set_bound
      by (meson Finite_Set.finite_set card_of_ordLeq finite_\<alpha>set
                finite_\<sigma>_set inj_on_iff_card_le)
    ultimately have \<open>2^2^m \<le> (2::nat)^(card (UNIV:: urrel set))\<close>
      by simp
    also have \<open>\<dots> = n\<close>
      unfolding n_def
      by (metis Finite_Set.finite_set Pow_UNIV card_Pow finite_\<alpha>set)
    finally have \<open>2^2^m \<le> n\<close> by blast
    hence \<open>2^2^m \<le> m*m\<close> using n_upper by linarith
    moreover {
      have \<open>(2::nat)^(2^m) \<ge> (2^(m + 1))\<close>
        by (metis Suc_eq_plus1 Suc_leI less_exp one_le_numeral power_increasing)
      also have \<open>(2^(m + 1)) = (2::nat) * 2^m\<close>
        by auto
      have \<open>m < 2^m\<close>
        by (simp add: less_exp)
      hence \<open>m*m < (2^m)*(2^m)\<close>
        by (simp add: mult_strict_mono)
      moreover have \<open>\<dots> = 2^(m+m)\<close>
        by (simp add: power_add)
      ultimately have \<open>m*m < 2 ^ (m + m)\<close> by presburger
      moreover have \<open>m+m \<le> 2^m\<close>
      proof (induct m)
        case 0
        thus ?case by auto
      next
        case (Suc m)
        thus ?case
          by (metis Suc_leI less_exp mult_2 mult_le_mono2 power_Suc)
      qed
      ultimately have \<open>m*m < 2^2^m\<close>
        by (meson less_le_trans one_le_numeral power_increasing)
    }
    ultimately have False by auto
  }
  moreover {
    text\<open>Infinite case.\<close>
    assume \<open>infinite (UNIV::\<sigma> set)\<close>
    hence \<open>natLeq <=o |UNIV::\<sigma> set|\<close>
      by (meson card_of_UNIV card_of_ordLeq_infinite finite_prod
                infinite_iff_natLeq_ordLeq)
    hence \<open>cinfinite |UNIV::\<sigma> set|\<close>
      using cinfinite_mono natLeq_cinfinite by blast
    hence Cinf\<sigma>: \<open>Cinfinite |UNIV::\<sigma> set|\<close>
      using Cnotzero_UNIV by blast
    have 1: \<open>|range (inv \<alpha>\<sigma>)| \<le>o |UNIV::\<sigma> set|\<close>
      by auto
    have 2: \<open>\<forall>i\<in>range (inv \<alpha>\<sigma>). |{y . \<alpha>\<sigma> i = \<alpha>\<sigma> y}| \<le>o |UNIV::\<sigma> set|\<close>
    proof
      fix i :: \<open>urrel set\<close>
      assume \<open>i \<in> range (inv \<alpha>\<sigma>)\<close>
      show \<open>|{y . \<alpha>\<sigma> i = \<alpha>\<sigma> y}| \<le>o |UNIV::\<sigma> set|\<close>
        using A by blast
    qed
    have \<open>|\<Union> ((\<lambda>i. {y. \<alpha>\<sigma> i = \<alpha>\<sigma> y}) ` (range (inv \<alpha>\<sigma>)))| \<le>o
                   |Sigma (range (inv \<alpha>\<sigma>)) (\<lambda>i. {y. \<alpha>\<sigma> i = \<alpha>\<sigma> y})|\<close>
      using card_of_UNION_Sigma by blast
    hence \<open>|UNIV::urrel set set| \<le>o
           |Sigma (range (inv \<alpha>\<sigma>)) (\<lambda>i. {y. \<alpha>\<sigma> i = \<alpha>\<sigma> y})|\<close>
      using union_univ by argo
    moreover have \<open>|Sigma (range (inv \<alpha>\<sigma>)) (\<lambda>i. {y. \<alpha>\<sigma> i = \<alpha>\<sigma> y})| \<le>o |UNIV::\<sigma> set|\<close>
      using card_of_Sigma_ordLeq_Cinfinite[OF Cinf\<sigma>, OF 1, OF 2] by blast
    ultimately have \<open>|UNIV::urrel set set| \<le>o |UNIV::\<sigma> set|\<close>
      using ordLeq_transitive by blast
    moreover {
      have \<open>|UNIV::\<sigma> set| <o |UNIV::\<sigma> set set|\<close>
        by auto
      moreover have \<open>|UNIV::\<sigma> set set| \<le>o |UNIV::urrel set|\<close>
        using card_\<sigma>_set_set_bound by blast
      moreover have \<open>|UNIV::urrel set| <o |UNIV::urrel set set|\<close>
        by auto
      ultimately have \<open>|UNIV::\<sigma> set| <o |UNIV::urrel set set|\<close>
        by (metis ordLess_imp_ordLeq ordLess_ordLeq_trans)
    }
    ultimately have False
      using not_ordLeq_ordLess by blast
  }
  ultimately show False by blast
qed

text\<open>We introduce a mapping from abstract objects (i.e. sets of urrelations) to
     special urelements @{text \<open>\<alpha>\<sigma>\<close>} that is surjective and distinguishes all
     abstract objects that are distinguished by a (not necessarily surjective)
     mapping @{text \<open>\<alpha>\<sigma>'\<close>}. @{text \<open>\<alpha>\<sigma>'\<close>} will be used to model extended relation
     comprehension.\<close>
consts \<alpha>\<sigma>' :: \<open>urrel set \<Rightarrow> \<sigma>\<close>
consts \<alpha>\<sigma> :: \<open>urrel set \<Rightarrow> \<sigma>\<close>
specification(\<alpha>\<sigma>)
  \<alpha>\<sigma>_surj: \<open>surj \<alpha>\<sigma>\<close>
  \<alpha>\<sigma>_\<alpha>\<sigma>': \<open>\<alpha>\<sigma> x = \<alpha>\<sigma> y \<Longrightarrow> \<alpha>\<sigma>' x = \<alpha>\<sigma>' y\<close>
proof -
  obtain x where x_prop: \<open>|UNIV::\<sigma> set| <o |{y. \<alpha>\<sigma>' x = \<alpha>\<sigma>' y}|\<close>
    using \<alpha>\<sigma>_pigeonhole by blast
  have \<open>\<exists>f :: urrel set \<Rightarrow> \<sigma> . f ` {y. \<alpha>\<sigma>' x = \<alpha>\<sigma>' y} = UNIV \<and> f x = \<alpha>\<sigma>' x\<close>
  proof -
    have \<open>\<exists>f :: urrel set \<Rightarrow> \<sigma> . f ` {y. \<alpha>\<sigma>' x = \<alpha>\<sigma>' y} = UNIV\<close>
      by (simp add: x_prop card_of_ordLeq2 ordLess_imp_ordLeq)
    then obtain f :: \<open>urrel set \<Rightarrow> \<sigma>\<close> where \<open>f ` {y. \<alpha>\<sigma>' x = \<alpha>\<sigma>' y} = UNIV\<close>
      by presburger
    moreover obtain a where \<open>f a = \<alpha>\<sigma>' x\<close> and \<open>\<alpha>\<sigma>' a = \<alpha>\<sigma>' x\<close>
      by (smt (verit, best) calculation UNIV_I image_iff mem_Collect_eq)
    ultimately show ?thesis
      by (auto intro!: exI[where x=\<open>Fun.swap x a f\<close>])
  qed
  then obtain f where fimage: \<open>f ` {y. \<alpha>\<sigma>' x = \<alpha>\<sigma>' y} = UNIV\<close>
                  and fx: \<open>f x = \<alpha>\<sigma>' x\<close>
    by blast

  define \<alpha>\<sigma> :: \<open>urrel set \<Rightarrow> \<sigma>\<close> where
    \<open>\<alpha>\<sigma> \<equiv> \<lambda> urrels . if \<alpha>\<sigma>' urrels = \<alpha>\<sigma>' x \<and> f urrels \<notin> range \<alpha>\<sigma>'
                      then f urrels
                      else \<alpha>\<sigma>' urrels\<close>
  have \<open>surj \<alpha>\<sigma>\<close>
  proof -
    {
    fix s :: \<sigma>
    {
      assume \<open>s \<in> range \<alpha>\<sigma>'\<close>
      hence 0: \<open>\<alpha>\<sigma>' (inv \<alpha>\<sigma>' s) = s\<close>
        by (meson f_inv_into_f)
      {
        assume \<open>s = \<alpha>\<sigma>' x\<close>
        hence \<open>\<alpha>\<sigma> x = s\<close>
          using \<alpha>\<sigma>_def fx by presburger
        hence \<open>\<exists>f . \<alpha>\<sigma> (f s) = s\<close>
          by auto
      }
      moreover {
        assume \<open>s \<noteq> \<alpha>\<sigma>' x\<close>
        hence \<open>\<alpha>\<sigma> (inv \<alpha>\<sigma>' s) = s\<close>
          unfolding \<alpha>\<sigma>_def 0 by presburger
        hence \<open>\<exists>f . \<alpha>\<sigma> (f s) = s\<close>
          by blast
      }
      ultimately have \<open>\<exists>f . \<alpha>\<sigma> (f s) = s\<close>
        by blast
    }
    moreover {
      assume \<open>s \<notin> range \<alpha>\<sigma>'\<close>
      moreover obtain urrels where \<open>f urrels = s\<close> and \<open>\<alpha>\<sigma>' x = \<alpha>\<sigma>' urrels\<close>
        by (smt (verit, best) UNIV_I fimage image_iff mem_Collect_eq)
      ultimately have \<open>\<alpha>\<sigma> urrels = s\<close>
        using \<alpha>\<sigma>_def by presburger
      hence \<open>\<exists>f . \<alpha>\<sigma> (f s) = s\<close>
        by (meson f_inv_into_f range_eqI)
    }
    ultimately have \<open>\<exists>f . \<alpha>\<sigma> (f s) = s\<close>
      by blast
    }
    thus ?thesis
      by (metis surj_def)
  qed
  moreover have \<open>\<forall>x y. \<alpha>\<sigma> x = \<alpha>\<sigma> y \<longrightarrow> \<alpha>\<sigma>' x = \<alpha>\<sigma>' y\<close>
    by (metis \<alpha>\<sigma>_def rangeI)
  ultimately show ?thesis
    by blast
qed

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

lemma disc_ex: \<open>\<exists>\<alpha>\<sigma>'::urrel set \<Rightarrow> \<sigma>. \<forall>x y. \<alpha>\<sigma>' x = \<alpha>\<sigma>' y \<longrightarrow> \<alpha>disc x = \<alpha>disc y\<close>
  for \<alpha>disc :: \<open>urrel set \<Rightarrow> 'a::countable\<close>
proof -
  obtain f :: \<open>'a \<Rightarrow> nat\<close> where \<open>inj f\<close> using ex_inj by blast
  moreover obtain g :: \<open>nat \<Rightarrow> \<sigma>\<close> where \<open>inj g\<close>
    using \<sigma>_inf by (meson cinfinite_def infinite_iff_countable_subset)
  term \<open>g o f o \<alpha>disc\<close>
  ultimately show ?thesis
    by (auto intro!: exI[where x=\<open>g o f o \<alpha>disc\<close>] simp: injD)
qed

datatype disc = Number nat | InfiniteCardinal | Other nat

instance disc :: countable
  by countable_datatype

(*
definition is_number :: \<open>urrel set \<Rightarrow> bool\<close> where
  \<open>is_number \<equiv> \<lambda> urrels . \<exists> r :: ((\<upsilon>\<times>\<upsilon>) set) . card_order_on (Field r) r \<and>
               urrels \<noteq> {} \<and>
               urrels = { urrel . r =o |{ x . AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel x)}|}\<close>
*)

definition urrel_act_ext :: \<open>urrel \<Rightarrow> \<upsilon> set\<close> where
  \<open>urrel_act_ext \<equiv> \<lambda> urrel . { x . AOT_model_valid_in w\<^sub>0 (Rep_urrel urrel x)}\<close>

definition is_number :: \<open>urrel set \<Rightarrow> bool\<close> where
  \<open>is_number \<equiv> \<lambda> urrels . \<exists> urrel . urrel \<in> urrels \<and>
        (\<forall> urrel' . urrel' \<in> urrels \<longleftrightarrow> (\<exists>f . bij_betw f (urrel_act_ext urrel') (urrel_act_ext urrel)))\<close>

definition is_natural_number :: \<open>urrel set \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>is_natural_number \<equiv> \<lambda> urrels n . is_number urrels \<and>
    (\<forall> urrel \<in> urrels . finite (urrel_act_ext urrel) \<and> card (urrel_act_ext urrel) = n)\<close>

lemma is_natural_number_inject:
  assumes \<open>is_natural_number x n\<close>
      and \<open>is_natural_number y n\<close>
  shows \<open>x = y\<close>
proof -
  have \<open>is_number x\<close>
    using assms unfolding is_natural_number_def by blast
  then obtain urrelx where x: \<open>urrelx \<in> x \<and> (\<forall> urrel' . urrel' \<in> x \<longleftrightarrow> (\<exists>f . bij_betw f (urrel_act_ext urrel') (urrel_act_ext urrelx)))\<close>
    unfolding is_number_def by blast
  hence x': \<open>finite (urrel_act_ext urrelx) \<and> card (urrel_act_ext urrelx) = n\<close>
    using assms unfolding is_natural_number_def by blast

  have \<open>is_number y\<close>
    using assms unfolding is_natural_number_def by blast
  then obtain urrely where y: \<open>urrely \<in> y \<and> (\<forall> urrel' . urrel' \<in> y \<longleftrightarrow> (\<exists>f . bij_betw f (urrel_act_ext urrel') (urrel_act_ext urrely)))\<close>
    unfolding is_number_def by blast
  hence y': \<open>finite (urrel_act_ext urrely) \<and> card (urrel_act_ext urrely) = n\<close>
    using assms unfolding is_natural_number_def by blast
  {
    fix r
    assume \<open>r \<in> x\<close>
    hence \<open>finite (urrel_act_ext r) \<and> card (urrel_act_ext r) = n\<close>
      by (meson assms(1) is_natural_number_def)
    hence \<open>r \<in> y\<close>
      by (simp add: y' finite_same_card_bij y)
  }
  moreover {
    fix r
    assume \<open>r \<in> y\<close>
    hence \<open>finite (urrel_act_ext r) \<and> card (urrel_act_ext r) = n\<close>
      by (meson assms(2) is_natural_number_def)
    hence \<open>r \<in> x\<close>
      by (simp add: x' finite_same_card_bij x)
  }
  ultimately show \<open>x = y\<close>
    by blast
qed

lemma the_natural_number_eq:
  assumes \<open>\<exists>n . is_natural_number x n\<close>
  assumes \<open>\<exists>n . is_natural_number y n\<close>
  shows \<open>((THE n . is_natural_number x n) = (THE n . is_natural_number y n)) = (x = y)\<close>
  by (metis assms(1) assms(2) is_natural_number_def is_natural_number_inject theI)

definition \<alpha>disc :: \<open>urrel set \<Rightarrow> disc\<close> where
  \<open>\<alpha>disc \<equiv> \<lambda> urrels . if is_number urrels
          then (if \<exists>n . is_natural_number urrels n
                then Number (THE n . is_natural_number urrels n)
                else InfiniteCardinal)
          else Other (undefined urrels)\<close>

specification (\<alpha>\<sigma>')
  \<alpha>\<sigma>_disc: \<open>\<alpha>\<sigma>' x = \<alpha>\<sigma>' y \<Longrightarrow> \<alpha>disc x = \<alpha>disc y\<close>
  using disc_ex by blast

(*<*)
end
(*>*)
