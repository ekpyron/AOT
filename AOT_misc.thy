theory AOT_misc
  imports AOT_NaturalNumbers
begin

section\<open>Miscellaneous Theorems\<close>

AOT_theorem \<open>\<forall>F([F]x \<equiv> [F]y) \<equiv> \<forall>F(([F]x) = ([F]y))\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I"; rule GEN)
  fix F
  AOT_assume 1: \<open>\<forall>F([F]x \<equiv> [F]y)\<close>
  AOT_show \<open>(([F]x) = ([F]y))\<close>
  proof (rule "raa-cor:1")
    AOT_assume 2: \<open>\<not>(([F]x) = ([F]y))\<close>
    AOT_have 3: \<open>\<not>([\<lambda>z [F]x] = [\<lambda>z [F]y])\<close>
    proof (rule "raa-cor:2")
      AOT_assume \<open>[\<lambda>z [F]x] = [\<lambda>z [F]y]\<close>
      AOT_hence \<open>([F]x) = ([F]y)\<close>
        using "\<equiv>\<^sub>d\<^sub>fI" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "identity:4" "log-prop-prop:2" by blast
      AOT_thus \<open>([F]x) = ([F]y) & \<not>(([F]x) = ([F]y))\<close>
        using 2 "&I" by blast
    qed
    AOT_have \<open>\<exists>z \<not>(z[\<lambda>z [F]x] \<equiv> z[\<lambda>z [F]y])\<close>
    proof(rule "raa-cor:1")
      AOT_assume \<open>\<not>\<exists>z \<not>(z[\<lambda>z [F]x] \<equiv> z[\<lambda>z [F]y])\<close>
      AOT_hence \<open>\<forall>z(z[\<lambda>z [F]x] \<equiv> z[\<lambda>z [F]y])\<close>
        by (metis (no_types, lifting) "existential:2[const_var]" "raa-cor:3" "universal-cor")
      AOT_hence \<open>\<forall>z\<box>(z[\<lambda>z [F]x] \<equiv> z[\<lambda>z [F]y])\<close>
        using "3" "prop-equiv.unvarify_F.unvarify_G.\<forall>E(1).\<forall>E(1).\<equiv>E(2).rule=E'" "prop-prop2:2" "raa-cor:3" "rule=I:1" by blast
      AOT_hence \<open>\<box>\<forall>z(z[\<lambda>z [F]x] \<equiv> z[\<lambda>z [F]y])\<close>
        by (simp add: "BFs:1.\<rightarrow>E")
      AOT_hence \<open>[\<lambda>z [F]x] = [\<lambda>z [F]y]\<close>
        using "p-identity-thm2:1"[unvarify F, OF "prop-prop2:2", unvarify G, OF "prop-prop2:2", THEN "\<equiv>E"(2)]
        by auto
      AOT_thus \<open>[\<lambda>z [F]x] = [\<lambda>z [F]y] & \<not>[\<lambda>z [F]x] = [\<lambda>z [F]y]\<close>
        using 3 "&I" by auto
    qed
    then AOT_obtain z where 4: \<open>\<not>(z[\<lambda>z [F]x] \<equiv> z[\<lambda>z [F]y])\<close>
      using "\<exists>E"[rotated] by blast
    AOT_have 5: \<open>[\<lambda>y z[\<lambda>z [F]y]]\<down>\<close>
      by "cqt:2"
    AOT_have \<open>\<not>([\<lambda>y z[\<lambda>z [F]y]]x \<equiv> [\<lambda>y z[\<lambda>z [F]y]]y)\<close>
      by (metis (no_types, lifting) ext "1" "5" "S5Basic:4.\<rightarrow>E" "T-S5-fund:1.\<rightarrow>E" "cqt:2"(1) "kirchner-thm-cor:1.\<rightarrow>E.\<forall>E(1).\<forall>E(1).\<rightarrow>E" "local.4"
          "raa-cor:3")
    moreover AOT_have \<open>([\<lambda>y z[\<lambda>z [F]y]]x \<equiv> [\<lambda>y z[\<lambda>z [F]y]]y)\<close>
      using "1" "5" "rule-ui:1" by blast
    ultimately AOT_show \<open>p & \<not>p\<close>
      using "raa-cor:3" by blast
  qed
next
  fix F
  AOT_assume \<open>\<forall>F(([F]x) = ([F]y))\<close>
  AOT_hence \<open>([F]x) = ([F]y)\<close>
    using "rule-ui:3" by blast
  AOT_thus \<open>([F]x) \<equiv> ([F]y)\<close>
    using "oth-class-taut:3:a" "rule=E" by blast
qed

text\<open>Fragments of PLM's theory of Concepts.\<close>

AOT_define FimpG :: \<open>\<Pi> \<Rightarrow> \<Pi> \<Rightarrow> \<phi>\<close> (infixl \<open>\<Rightarrow>\<close> 50)
  "F-imp-G": \<open>[G] \<Rightarrow> [F] \<equiv>\<^sub>d\<^sub>f F\<down> & G\<down> & \<box>\<forall>x ([G]x \<rightarrow> [F]x)\<close>

AOT_define concept :: \<open>\<Pi>\<close> (\<open>C!\<close>)
  concepts: \<open>C! =\<^sub>d\<^sub>f A!\<close>

AOT_register_rigid_restricted_type
  Concept: \<open>C!\<kappa>\<close>
proof
  AOT_modally_strict {
    AOT_have \<open>\<exists>x A!x\<close>
      using "o-objects-exist:2" "qml:2"[axiom_inst] "\<rightarrow>E" by blast
    AOT_thus \<open>\<exists>x C!x\<close>
      using "rule-id-df:1[zero]"[OF concepts, OF "oa-exist:2"] "rule=E" id_sym
      by fast
  }
next
  AOT_modally_strict {
    AOT_show \<open>C!\<kappa> \<rightarrow> \<kappa>\<down>\<close> for \<kappa>
      using "cqt:5:a"[axiom_inst, THEN "\<rightarrow>E", THEN "&E"(2)] "\<rightarrow>I"
      by blast
  }
next
  AOT_modally_strict {
    AOT_have \<open>\<forall>x(A!x \<rightarrow> \<box>A!x)\<close>
      by (simp add: "oa-facts:2" GEN)
    AOT_thus \<open>\<forall>x(C!x \<rightarrow> \<box>C!x)\<close>
      using "rule-id-df:1[zero]"[OF concepts, OF "oa-exist:2"] "rule=E" id_sym
      by fast
  }
qed

AOT_register_variable_names
  Concept: c d e

AOT_theorem "concept-comp:1": \<open>\<exists>x(C!x & \<forall>F(x[F] \<equiv> \<phi>{F}))\<close>
    using concepts[THEN "rule-id-df:1[zero]", OF "oa-exist:2", symmetric]
          "A-objects"[axiom_inst]
          "rule=E" by fast

AOT_theorem "concept-comp:2": \<open>\<exists>!x(C!x & \<forall>F(x[F] \<equiv> \<phi>{F}))\<close>
    using concepts[THEN "rule-id-df:1[zero]", OF "oa-exist:2", symmetric]
          "A-objects!"
          "rule=E" by fast

AOT_theorem "concept-comp:3": \<open>\<^bold>\<iota>x(C!x & \<forall>F(x[F] \<equiv> \<phi>{F}))\<down>\<close>
  using "concept-comp:2" "A-Exists:2"[THEN "\<equiv>E"(2)] "RA[2]" by blast

AOT_theorem "concept-comp:4":
  \<open>\<^bold>\<iota>x(C!x & \<forall>F(x[F] \<equiv> \<phi>{F})) = \<^bold>\<iota>x(A!x & \<forall>F(x[F] \<equiv> \<phi>{F}))\<close>
    using "=I"(1)[OF "concept-comp:3"]
          "rule=E"[rotated]
          concepts[THEN "rule-id-df:1[zero]", OF "oa-exist:2"]
          by fast

AOT_define conceptInclusion :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl \<open>\<preceq>\<close> 100)
  "con:1": \<open>c \<preceq> d \<equiv>\<^sub>d\<^sub>f \<forall>F(c[F] \<rightarrow> d[F])\<close>


AOT_define conceptOf :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>ConceptOf'(_,_')\<close>)
  "concept-of-G": \<open>ConceptOf(c,G) \<equiv>\<^sub>d\<^sub>f G\<down> & \<forall>F (c[F] \<equiv> [G] \<Rightarrow> [F])\<close>

AOT_theorem "con-exists:1": \<open>\<exists>c ConceptOf(c,G)\<close>
proof -
  AOT_obtain c where \<open>\<forall>F (c[F] \<equiv> [G] \<Rightarrow> [F])\<close>
    using "concept-comp:1" "Concept.\<exists>E"[rotated] by meson
  AOT_hence \<open>ConceptOf(c,G)\<close>
    by (auto intro!: "concept-of-G"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" Concept.\<psi>)
  thus ?thesis by (rule "Concept.\<exists>I")
qed

AOT_theorem "con-exists:2": \<open>\<exists>!c ConceptOf(c,G)\<close>
proof -
  AOT_have \<open>\<exists>!c \<forall>F (c[F] \<equiv> [G] \<Rightarrow> [F])\<close>
    using "concept-comp:2" by simp
  moreover {
    AOT_modally_strict {
      fix x
      AOT_assume \<open>\<forall>F (x[F] \<equiv> [G] \<Rightarrow> [F])\<close>
      moreover AOT_have \<open>[G] \<Rightarrow> [G]\<close>
        by (safe intro!: "F-imp-G"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" RN GEN "\<rightarrow>I")
      ultimately AOT_have \<open>x[G]\<close>
        using "\<forall>E"(2) "\<equiv>E" by blast
      AOT_hence \<open>A!x\<close>
        using "encoders-are-abstract"[THEN "\<rightarrow>E", OF "\<exists>I"(2)] by simp
      AOT_hence \<open>C!x\<close>
        using concepts[THEN "rule-id-df:1[zero]", OF "oa-exist:2", symmetric]
              "rule=E"[rotated]
        by fast
    }
  }
  ultimately show ?thesis
    by (AOT_subst \<open>ConceptOf(c,G)\<close> \<open>\<forall>F (c[F] \<equiv> [G] \<Rightarrow> [F])\<close> for: c;
           AOT_subst_def "concept-of-G")
       (auto intro!: "\<equiv>I" "\<rightarrow>I" "&I" "cqt:2" Concept.\<psi> dest: "&E")
qed

AOT_theorem "con-exists:3": \<open>\<^bold>\<iota>c ConceptOf(c,G)\<down>\<close>
  by (safe intro!: "A-Exists:2"[THEN "\<equiv>E"(2)] "con-exists:2"[THEN "RA[2]"])


AOT_define theConceptOfG :: \<open>\<tau> \<Rightarrow> \<kappa>\<^sub>s\<close> (\<open>\<^bold>c\<^sub>_\<close>)
  "concept-G": \<open>\<^bold>c\<^sub>G =\<^sub>d\<^sub>f \<^bold>\<iota>c ConceptOf(c, G)\<close>

AOT_theorem "concept-G[den]": \<open>\<^bold>c\<^sub>G\<down>\<close>
  by (auto intro!: "rule-id-df:1"[OF "concept-G"]
                   "t=t-proper:1"[THEN "\<rightarrow>E"]
                   "con-exists:3")


AOT_theorem "concept-G[concept]": \<open>C!\<^bold>c\<^sub>G\<close>
proof -
  AOT_have \<open>\<^bold>\<A>(C!\<^bold>c\<^sub>G & ConceptOf(\<^bold>c\<^sub>G, G))\<close>
    by (auto intro!: "actual-desc:2"[unvarify x, THEN "\<rightarrow>E"]
                     "rule-id-df:1"[OF "concept-G"]
                     "concept-G[den]"
                     "con-exists:3")
  AOT_hence \<open>\<^bold>\<A>C!\<^bold>c\<^sub>G\<close>
    by (metis "Act-Basic:2" "con-dis-i-e:2:a" "intro-elim:3:a")
  AOT_hence \<open>\<^bold>\<A>A!\<^bold>c\<^sub>G\<close>
    using "rule-id-df:1[zero]"[OF concepts, OF "oa-exist:2"]
          "rule=E" by fast
  AOT_hence \<open>A!\<^bold>c\<^sub>G\<close>
    using "oa-facts:8"[unvarify x, THEN "\<equiv>E"(2)] "concept-G[den]" by blast
  thus ?thesis
    using "rule-id-df:1[zero]"[OF concepts, OF "oa-exist:2", symmetric]
          "rule=E" by fast
qed

AOT_theorem "conG-strict": \<open>\<^bold>c\<^sub>G = \<^bold>\<iota>c \<forall>F(c[F] \<equiv> [G] \<Rightarrow> [F])\<close>
proof (rule "id-eq:3"[unvarify \<alpha> \<beta> \<gamma>, THEN "\<rightarrow>E"])
  AOT_have \<open>\<box>\<forall>x (C!x & ConceptOf(x,G) \<equiv> C!x & \<forall>F (x[F] \<equiv> [G] \<Rightarrow> [F]))\<close>
    by (auto intro!: "concept-of-G"[THEN "\<equiv>\<^sub>d\<^sub>fI"] RN GEN "\<equiv>I" "\<rightarrow>I" "&I" "cqt:2"
               dest: "&E";
        auto dest: "\<forall>E"(2) "\<equiv>E"(1,2) dest!: "&E"(2) "concept-of-G"[THEN "\<equiv>\<^sub>d\<^sub>fE"])
  AOT_thus \<open>\<^bold>c\<^sub>G = \<^bold>\<iota>c ConceptOf(c, G) & \<^bold>\<iota>c ConceptOf(c, G) = \<^bold>\<iota>c \<forall>F(c[F] \<equiv> [G] \<Rightarrow> [F])\<close>
    by (auto intro!: "&I" "rule-id-df:1"[OF "concept-G"] "con-exists:3"
                      "equiv-desc-eq:3"[THEN "\<rightarrow>E"])
qed(auto simp: "concept-G[den]" "con-exists:3" "concept-comp:3")


AOT_theorem "conG-lemma:1": \<open>\<forall>F(\<^bold>c\<^sub>G[F] \<equiv> [G] \<Rightarrow> [F])\<close>
proof(safe intro!: GEN "\<equiv>I" "\<rightarrow>I")
  fix F
  AOT_have \<open>\<^bold>\<A>\<forall>F(\<^bold>c\<^sub>G[F] \<equiv> [G] \<Rightarrow> [F])\<close>
    using "actual-desc:4"[THEN "\<rightarrow>E", OF "concept-comp:3",
                          THEN "Act-Basic:2"[THEN "\<equiv>E"(1)],
                          THEN "&E"(2)]
          "conG-strict"[symmetric] "rule=E" by fast
  AOT_hence \<open>\<^bold>\<A>(\<^bold>c\<^sub>G[F] \<equiv> [G] \<Rightarrow> [F])\<close>
    using "logic-actual-nec:3"[axiom_inst, THEN "\<equiv>E"(1)] "\<forall>E"(2)
    by blast
  AOT_hence 0: \<open>\<^bold>\<A>\<^bold>c\<^sub>G[F] \<equiv> \<^bold>\<A>[G] \<Rightarrow> [F]\<close>
    using "Act-Basic:5"[THEN "\<equiv>E"(1)] by blast
  {
    AOT_assume \<open>\<^bold>c\<^sub>G[F]\<close>
    AOT_hence \<open>\<^bold>\<A>\<^bold>c\<^sub>G[F]\<close>
      by(safe intro!: "en-eq:10[1]"[unvarify x\<^sub>1, THEN "\<equiv>E"(2)]
                      "concept-G[den]")
    AOT_hence \<open>\<^bold>\<A>[G] \<Rightarrow> [F]\<close>
      using 0[THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>\<^bold>\<A>(F\<down> & G\<down> & \<box>\<forall>x([G]x \<rightarrow> [F]x))\<close>
      by (AOT_subst_def (reverse) "F-imp-G")
    AOT_hence \<open>\<^bold>\<A>\<box>\<forall>x([G]x \<rightarrow> [F]x)\<close>
      using "Act-Basic:2"[THEN "\<equiv>E"(1)] "&E" by blast
    AOT_hence \<open>\<box>\<forall>x([G]x \<rightarrow> [F]x)\<close>
      using "qml-act:2"[axiom_inst, THEN "\<equiv>E"(2)] by simp
    AOT_thus \<open>[G] \<Rightarrow> [F]\<close>
      by (AOT_subst_def "F-imp-G"; auto intro!: "&I" "cqt:2")
  }
  {
    AOT_assume \<open>[G] \<Rightarrow> [F]\<close>
    AOT_hence \<open>\<box>\<forall>x([G]x \<rightarrow> [F]x)\<close>
      by (safe dest!: "F-imp-G"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E"(2))
    AOT_hence \<open>\<^bold>\<A>\<box>\<forall>x([G]x \<rightarrow> [F]x)\<close>
      using "qml-act:2"[axiom_inst, THEN "\<equiv>E"(1)] by simp
    AOT_hence \<open>\<^bold>\<A>(F\<down> & G\<down> & \<box>\<forall>x([G]x \<rightarrow> [F]x))\<close>
      by (auto intro!: "Act-Basic:2"[THEN "\<equiv>E"(2)] "&I" "cqt:2"
               intro: "RA[2]")
    AOT_hence \<open>\<^bold>\<A>([G] \<Rightarrow> [F])\<close>
      by (AOT_subst_def "F-imp-G")
    AOT_hence \<open>\<^bold>\<A>\<^bold>c\<^sub>G[F]\<close>
      using 0[THEN "\<equiv>E"(2)] by blast
    AOT_thus \<open>\<^bold>c\<^sub>G[F]\<close>
      by(safe intro!: "en-eq:10[1]"[unvarify x\<^sub>1, THEN "\<equiv>E"(1)]
                      "concept-G[den]")
  }
qed

AOT_define ThickForm :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>FormOf'(_,_')\<close>)
  "tform-of": \<open>FormOf(x,G) \<equiv>\<^sub>d\<^sub>f A!x & G\<down> & \<forall>F(x[F] \<equiv> [G] \<Rightarrow> [F])\<close>

AOT_theorem shared_urelement_projection_identity:
  assumes \<open>\<forall>y [\<lambda>x (y[\<lambda>z [R]zx])]\<down>\<close>
  shows \<open>\<forall>F([F]a \<equiv> [F]b) \<rightarrow> [\<lambda>z [R]za] = [\<lambda>z [R]zb]\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<forall>F([F]a \<equiv> [F]b)\<close>
  {
    fix z
    AOT_have \<open>[\<lambda>x (z[\<lambda>z [R]zx])]\<down>\<close>
      using assms[THEN "\<forall>E"(2)].
    AOT_hence 1: \<open>\<forall>x \<forall>y (\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> \<box>(z[\<lambda>z [R]zx] \<equiv> z[\<lambda>z [R]zy]))\<close>
      using "kirchner-thm-cor:1"[THEN "\<rightarrow>E"]
      by blast
    AOT_have \<open>\<box>(z[\<lambda>z [R]za] \<equiv> z[\<lambda>z [R]zb])\<close>
      using 1[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF 0] by blast
  }
  AOT_hence \<open>\<forall>z \<box>(z[\<lambda>z [R]za] \<equiv> z[\<lambda>z [R]zb])\<close>
    by (rule GEN)
  AOT_hence \<open>\<box>\<forall>z(z[\<lambda>z [R]za] \<equiv> z[\<lambda>z [R]zb])\<close>
    by (rule BF[THEN "\<rightarrow>E"])
  AOT_thus \<open>[\<lambda>z [R]za] = [\<lambda>z [R]zb]\<close>
    by (AOT_subst_def "identity:2")
       (auto intro!: "&I" "cqt:2")
qed

AOT_theorem shared_urelement_exemplification_identity:
  assumes \<open>\<forall>y [\<lambda>x (y[\<lambda>z [G]x])]\<down>\<close>
  shows \<open>\<forall>F([F]a \<equiv> [F]b) \<rightarrow> ([G]a) = ([G]b)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<forall>F([F]a \<equiv> [F]b)\<close>
  {
    fix z
    AOT_have \<open>[\<lambda>x (z[\<lambda>z [G]x])]\<down>\<close>
      using assms[THEN "\<forall>E"(2)].
    AOT_hence 1: \<open>\<forall>x \<forall>y (\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> \<box>(z[\<lambda>z [G]x] \<equiv> z[\<lambda>z [G]y]))\<close>
      using "kirchner-thm-cor:1"[THEN "\<rightarrow>E"]
      by blast
    AOT_have \<open>\<box>(z[\<lambda>z [G]a] \<equiv> z[\<lambda>z [G]b])\<close>
      using 1[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF 0] by blast
  }
  AOT_hence \<open>\<forall>z \<box>(z[\<lambda>z [G]a] \<equiv> z[\<lambda>z [G]b])\<close>
    by (rule GEN)
  AOT_hence \<open>\<box>\<forall>z(z[\<lambda>z [G]a] \<equiv> z[\<lambda>z [G]b])\<close>
    by (rule BF[THEN "\<rightarrow>E"])
  AOT_hence \<open>[\<lambda>z [G]a] = [\<lambda>z [G]b]\<close>
    by (AOT_subst_def "identity:2")
       (auto intro!: "&I" "cqt:2")
  AOT_thus \<open>([G]a) = ([G]b)\<close>
    by (safe intro!: "identity:4"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "log-prop-prop:2")
qed

text\<open>The assumptions of the theorems above are derivable, if the additional
     introduction rules for the upcoming extension of @{thm "cqt:2[lambda]"}
     are explicitly allowed (while they are currently not part of the
     abstraction layer).\<close>
notepad
begin
  AOT_modally_strict {
    AOT_have \<open>\<forall>R\<forall>y [\<lambda>x (y[\<lambda>z [R]zx])]\<down>\<close>
      by (safe intro!: GEN "cqt:2" AOT_instance_of_cqt_2_intro_next)
    AOT_have \<open>\<forall>G\<forall>y [\<lambda>x (y[\<lambda>z [G]x])]\<down>\<close>
      by (safe intro!: GEN "cqt:2" AOT_instance_of_cqt_2_intro_next)
  }
end

end
