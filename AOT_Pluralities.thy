theory AOT_Pluralities
  imports AOT_NaturalNumbers
begin

AOT_define PluralityOf :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>PluralityOf'(_,_')\<close>)
  "pluralq:1": \<open>PluralityOf(x,G) \<equiv>\<^sub>d\<^sub>f \<exists>u ([G]u & A!x & \<forall>F(x[F] \<equiv> \<exists>u([G]u & F = [\<lambda>y y = u])))\<close>

AOT_theorem "pluralq:2": \<open>\<forall>G(\<exists>u[G]u \<rightarrow> \<exists>!x PluralityOf(x,G))\<close>
proof(safe intro!: GEN "\<rightarrow>I")
  fix G
  AOT_assume \<open>\<exists>u [G]u\<close>
  then AOT_obtain u where \<open>[G]u\<close>
    using "Discernible.\<exists>E"[rotated] by meson
  moreover AOT_obtain a where a: \<open>A!a & \<forall>F(a[F] \<equiv> \<exists>u([G]u & F = [\<lambda>y y = u]))\<close>
    using "\<exists>E"[rotated] "A-objects"[axiom_inst] by meson
  ultimately AOT_have 1: \<open>PluralityOf(a,G)\<close>
    using "&I" "Discernible.\<exists>I" "pluralq:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"]
    by (meson "con-dis-i-e:2:b" "con-dis-taut:1.\<rightarrow>E")
  AOT_show \<open>\<exists>!x PluralityOf(x,G)\<close>
  proof(safe intro!: "uniqueness:2.\<equiv>E(2)" "\<exists>I"(2)[where \<beta>=a] GEN "\<equiv>I" "\<rightarrow>I" "ab-obey:1"[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "&I")
    fix y
    {
      AOT_assume \<open>PluralityOf(y,G)\<close>
      then AOT_obtain v where v: \<open>[G]v & A!y & \<forall>F(y[F] \<equiv> \<exists>u([G]u & F = [\<lambda>y y = u]))\<close>
        using "\<equiv>\<^sub>d\<^sub>fE"[OF "pluralq:1"] "Discernible.\<exists>E"[rotated] by meson
      AOT_thus \<open>A!y\<close>
        using "&E" by blast
      {
        fix F
        AOT_assume \<open>y[F]\<close>
        AOT_thus \<open>a[F]\<close>
          by (metis (no_types, lifting) "con-dis-i-e:2:b" "intro-elim:3:a" "intro-elim:3:b" "rule-ui:3" a v)
      }
      {
        fix F
        AOT_assume \<open>a[F]\<close>
        AOT_thus \<open>y[F]\<close>
          by (metis (lifting) "con-dis-i-e:2:b" "intro-elim:3:a" "intro-elim:3:b" "rule-ui:3" a v)
      }
    }
    {
      AOT_assume \<open>y = a\<close>
      AOT_thus \<open>PluralityOf(y,G)\<close>
        using "rule=E" 1 id_sym by fast
    }
    AOT_show \<open>A!a\<close> using a "&E" by blast
  qed
qed

AOT_define Plurality :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>Plurality'(_')\<close>)
  "pluralq:3": \<open>Plurality(x) \<equiv>\<^sub>d\<^sub>f \<exists>G PluralityOf(x,G)\<close>

AOT_theorem
  rigid_enc:
  assumes \<open>RIGID_CONDITION(\<phi>)\<close>
  shows \<open>\<forall>F(x[F] \<equiv> \<phi>{F}) \<rightarrow> \<box>\<forall>F(x[F] \<equiv> \<phi>{F})\<close>
proof(safe intro!: "\<rightarrow>I" BF[THEN "\<rightarrow>E"] GEN)
  fix F
  AOT_assume \<open>\<forall>F(x[F] \<equiv> \<phi>{F})\<close>
  AOT_hence \<open>x[F] \<equiv> \<phi>{F}\<close>
    using "rule-ui:3" by blast
  moreover AOT_have \<open>\<box>(x[F] \<rightarrow> \<box>x[F])\<close>
    using "pre-en-eq:1[1]" RN by auto
  moreover AOT_have \<open>\<box>(\<phi>{F} \<rightarrow> \<box>\<phi>{F})\<close>
    by (simp add: "cqt:2"(1) "deduction-theorem" "strict-can:1[E].\<forall>E(1).\<rightarrow>E" RN assms)
  ultimately AOT_show \<open>\<box>(x[F] \<equiv> \<phi>{F})\<close>
    by (metis "S5Basic:2.\<equiv>E(1)" "S5Basic:4.\<rightarrow>E" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "deduction-theorem" "intro-elim:2"
        "intro-elim:3:a" "intro-elim:3:b" "sc-eq-box-box:4.\<rightarrow>E.\<rightarrow>E")
qed

AOT_theorem
  rigid_ex:
  assumes \<open>RIGID_CONDITION(\<phi>)\<close>
  shows \<open>\<exists>x \<phi>{x} \<rightarrow> \<box>\<exists>x \<phi>{x}\<close>
  by (metis "\<exists>E'" "cqt:2"(1) "deduction-theorem" "existential:2[const_var]" "sign-S5-thm:1.\<rightarrow>E"
      "strict-can:1[E].\<forall>E(1).\<rightarrow>E" assms)

AOT_theorem
  rigid_ex':
  assumes \<open>RIGID_CONDITION(\<phi>)\<close>
  shows \<open>\<exists>x \<phi>{x} \<equiv> \<box>\<exists>x \<phi>{x}\<close>
  by (simp add: "intro-elim:2" "qml:2" "vdash-properties:1[2]" assms rigid_ex)

lemma AOT_subst_world_box[AOT_substI]:
    \<open>AOT_subst \<Theta> \<Longrightarrow> AOT_subst (\<lambda> \<phi>. \<guillemotleft>w \<Turnstile> \<guillemotleft>\<Theta> \<phi>\<guillemotright>\<guillemotright>)\<close>
  sorry

AOT_register_variable_names
  PossibleWorld: v

AOT_theorem "pluralq:4''": \<open>\<box>\<forall>x(Plurality(x) \<rightarrow> \<box>Plurality(x))\<close>
proof(rule RN; safe intro!: GEN "\<rightarrow>I")
  AOT_modally_strict {
    fix x
    AOT_assume \<open>Plurality(x)\<close>
    then AOT_obtain G where \<open>PluralityOf(x,G)\<close>
      using "pluralq:3.\<equiv>\<^sub>d\<^sub>fE.\<exists>E'" by blast
    then AOT_obtain u where u: \<open>[G]u & A!x & \<forall>F(x[F] \<equiv> \<exists>u([G]u & F = [\<lambda>y y = u]))\<close>
      using "pluralq:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "Discernible.\<exists>E"[rotated] by meson
    AOT_obtain v where v: \<open>\<forall>p (v \<Turnstile> p \<equiv> p)\<close>
      using "act-world:1" "PossibleWorld.\<exists>E"[rotated] by meson
    AOT_have \<open>[[G]\<^sub>v]u\<close>
      by (metis (no_types, lifting) "con-dis-i-e:2:a" "intro-elim:3:b" "log-prop-prop:2" "rigid-der:1" "rule-ui:1"
          u v)
    AOT_have \<open>\<forall>w w \<Turnstile> Plurality(x)\<close>
    proof(safe intro!: PossibleWorld.GEN)
      fix w
      AOT_have 0: \<open>w \<Turnstile> (D!u & ([[G]\<^sub>v]u & A!x & \<forall>F (x[F] \<equiv> \<exists>u ([[G]\<^sub>v]u & F = [\<lambda>y y = u]))))\<close>
      proof(safe intro!: "conj-dist-w:1"[unvarify p q, OF "log-prop-prop:2", OF "log-prop-prop:2", THEN "\<equiv>E"(2)] "&I" "conj-dist-w:5"[THEN "\<equiv>E"(2)] GEN "conj-dist-w:4"[unvarify p q, OF "log-prop-prop:2", OF "log-prop-prop:2", THEN "\<equiv>E"(2)])
        AOT_show \<open>w \<Turnstile> D!u\<close>
          by (simp add: "cqt:2"(1) "discern-obj:8.unvarify_x.\<forall>E(1).\<rightarrow>E" "fund:2.unvarify_p.\<forall>E(1).\<equiv>E(1).\<forall>E(1).\<rightarrow>E"
              "log-prop-prop:2" Discernible.restricted_var_condition PossibleWorld.restricted_var_condition)
      next
        AOT_show \<open>w \<Turnstile> [[G]\<^sub>v]u\<close>
           sorry
      next
        AOT_show \<open>w \<Turnstile> A!x\<close>
          using "con-dis-i-e:2:a" "con-dis-i-e:2:b" "fund:2.unvarify_p.\<forall>E(1).\<equiv>E(1).\<forall>E(1).\<rightarrow>E" "log-prop-prop:2"
            "oa-facts:2.unvarify_x.\<forall>E(1).\<rightarrow>E" "russell-axiom[exe,1].\<psi>_denotes_asm" "world:3.\<rightarrow>E"
            PossibleWorld.restricted_var_condition u by blast
      next
        fix F
        AOT_have \<open>(w \<Turnstile> x[F]) \<equiv> (\<exists>u((w \<Turnstile> [[G]\<^sub>v]u) & (w \<Turnstile> F = [\<lambda>y y = u])))\<close>
          sorry
        AOT_show \<open>(w \<Turnstile> x[F]) \<equiv> (w \<Turnstile> \<exists>u([[G]\<^sub>v]u & F = [\<lambda>y y = u]))\<close>
          sorry
      qed
      AOT_hence \<open>w \<Turnstile> \<exists>u ([[G]\<^sub>v]u & A!x & \<forall>F (x[F] \<equiv> \<exists>u ([[G]\<^sub>v]u & F = [\<lambda>y y = u])))\<close>
        by (safe intro!: "conj-dist-w:6"[THEN "\<equiv>E"(2)] "\<exists>I"(2)[where \<beta>=\<open>Discernible.Rep u\<close>])
      thm "conj-dist-w:1"[unvarify p q, OF "log-prop-prop:2", OF "log-prop-prop:2", THEN "\<equiv>E"(2)]
      AOT_hence 0: \<open>\<exists>G (w \<Turnstile> \<exists>u ([G]u & A!x & \<forall>F (x[F] \<equiv> \<exists>u ([G]u & F = [\<lambda>y y = u]))))\<close>
        by (simp add: "df-rigid-rel:1.\<equiv>\<^sub>d\<^sub>fE.&E(1)" "existential:1" "rigid-der:2")
      AOT_hence 0: \<open>w \<Turnstile> \<exists>G \<exists>u ([G]u & A!x & \<forall>F (x[F] \<equiv> \<exists>u ([G]u & F = [\<lambda>y y = u])))\<close>
        by (safe intro!: "conj-dist-w:6"[THEN "\<equiv>E"(2)])
      AOT_show \<open>w \<Turnstile> Plurality(x)\<close>
        apply (AOT_subst_def "pluralq:3")
        apply (AOT_subst \<open>PluralityOf(x,G)\<close> \<open>\<exists>u ([G]u & A!x & \<forall>F(x[F] \<equiv> \<exists>u([G]u & F = [\<lambda>y y = u])))\<close> for: G)
         apply (simp add: "pluralq:1" "rule-eq-df:1")
        using "0" by blast
    qed
    AOT_thus \<open>\<box>Plurality(x)\<close>
      using "fund:2.unvarify_p.\<forall>E(1).\<equiv>E(2)" "log-prop-prop:2" by blast
  }
qed

AOT_theorem "pluralq:4'": \<open>\<box>\<forall>x(Plurality(x) \<rightarrow> \<box>Plurality(x))\<close>
proof(rule RN; safe intro!: GEN "\<rightarrow>I")
  AOT_modally_strict {
    fix x
    AOT_assume \<open>Plurality(x)\<close>
    then AOT_obtain G where \<open>PluralityOf(x,G)\<close>
      using "pluralq:3.\<equiv>\<^sub>d\<^sub>fE.\<exists>E'" by blast
    then AOT_obtain u where u: \<open>[G]u & A!x & \<forall>F(x[F] \<equiv> \<exists>u([G]u & F = [\<lambda>y y = u]))\<close>
      using "pluralq:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "Discernible.\<exists>E"[rotated] by meson
    AOT_obtain w where w: \<open>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
      using "act-world:1" "PossibleWorld.\<exists>E"[rotated] by meson
    AOT_hence 1: \<open>[[G]\<^sub>w]u \<equiv> [G]u\<close> for u
      using "intro-elim:3:e" "log-prop-prop:2" "rigid-der:1" "rule-ui:1" by blast
    AOT_have \<open>\<box>PluralityOf(x,[G]\<^sub>w)\<close>
    proof (AOT_subst_def "pluralq:1"; safe intro!: "sign-S5-thm:1.\<rightarrow>E" "\<exists>I" "KBasic:3.\<equiv>E(2)" "&I")
      AOT_show \<open>\<box>D!u\<close>
        by (simp add: Discernible.\<psi> RN)
      AOT_have \<open>[[G]\<^sub>w]u\<close>
        using "1" "con-dis-i-e:2:a" "intro-elim:3:b" u by blast
      AOT_thus \<open>\<box>[[G]\<^sub>w]u\<close>
        using "rigid-der:2"[THEN "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2), THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"]]
        using "rule-ui:3" "vdash-properties:10" by blast
      AOT_show \<open>\<box>A!x\<close>
        using "con-dis-i-e:2:a" "con-dis-i-e:2:b" "oa-facts:2" "vdash-properties:10" u by blast
      AOT_modally_strict {
        fix F
        AOT_have \<open>\<exists>u([[G]\<^sub>w]u & F = [\<lambda>y y = u]) \<equiv> \<box>\<exists>u([[G]\<^sub>w]u & F = [\<lambda>y y = u])\<close>
        proof(safe intro!: rigid_ex' "strict-can:1[I]" "\<rightarrow>I" GEN "KBasic:3.\<equiv>E(2)" "&I")
          AOT_modally_strict {
            fix x
            AOT_assume 0: \<open>D!x & ([[G]\<^sub>w]x & F = [\<lambda>y y = x])\<close>
            AOT_show \<open>\<box>D!x\<close>
              using "0" "con-dis-i-e:2:a" "discern-obj:8.unvarify_x.\<forall>E(1).\<rightarrow>E" "russell-axiom[exe,1].\<psi>_denotes_asm"
              by blast
            AOT_show \<open>\<box>[[G]\<^sub>w]x\<close>
              by (meson "0" "T-S5-fund:1.\<rightarrow>E" "con-dis-i-e:2:a" "con-dis-i-e:2:b" "cqt:2"(1) "df-rigid-rel:1.\<equiv>\<^sub>d\<^sub>fE.&E(1)"
                  "df-rigid-rel:1.\<equiv>\<^sub>d\<^sub>fE.&E(2)" "rigid-der:2" "rigid-rel-thms:1.unvarify_F.\<forall>E(1).\<equiv>E(1).\<forall>E(1).\<rightarrow>E")
            AOT_show \<open>\<box>F = [\<lambda>y y = x]\<close>
              using "0" "con-dis-i-e:2:b" "id-nec:2.\<rightarrow>E" by blast
          }
        qed
      } note 2 = this
      AOT_show \<open>\<box>\<forall>F(x[F] \<equiv> \<exists>u([[G]\<^sub>w]u & F = [\<lambda>y y = u]))\<close>
      proof(safe intro!: rigid_enc[THEN "\<rightarrow>E"] "strict-can:1[I]" GEN "\<rightarrow>I")
        AOT_modally_strict {
          fix F
          AOT_assume \<open>\<exists>u([[G]\<^sub>w]u & F = [\<lambda>y y = u])\<close>
          AOT_thus \<open>\<box>\<exists>u([[G]\<^sub>w]u & F = [\<lambda>y y = u])\<close>
            using "2" "intro-elim:3:a" by blast
        }
      next
        fix F
        AOT_show \<open>x[F] \<equiv> \<exists>u([[G]\<^sub>w]u & F = [\<lambda>y y = u])\<close>
          sorry
      qed
    qed
    AOT_hence \<open>\<exists>G \<box>PluralityOf(x,G)\<close>
      using "\<exists>I"(1) by (metis "df-rigid-rel:1.\<equiv>\<^sub>d\<^sub>fE.&E(1)" "rigid-der:2")
    AOT_thus \<open>\<box>Plurality(x)\<close>
      by (AOT_subst_def "pluralq:3") (auto simp: "sign-S5-thm:1.\<rightarrow>E")
  }
qed


AOT_theorem "pluralq:4": \<open>\<box>\<forall>x(Plurality(x) \<rightarrow> \<box>Plurality(x))\<close>
proof(rule RN; safe intro!: GEN "\<rightarrow>I")
  AOT_modally_strict {
    fix x
    AOT_assume \<open>Plurality(x)\<close>
    then AOT_obtain G where \<open>PluralityOf(x,G)\<close>
      using "pluralq:3.\<equiv>\<^sub>d\<^sub>fE.\<exists>E'" by blast
    then AOT_obtain u where u: \<open>[G]u & A!x & \<forall>F(x[F] \<equiv> \<exists>u([G]u & F = [\<lambda>y y = u]))\<close>
      using "pluralq:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "Discernible.\<exists>E"[rotated] by meson
    AOT_obtain w where w: \<open>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
      using "act-world:1" "PossibleWorld.\<exists>E"[rotated] by meson
    AOT_hence 1: \<open>[[G]\<^sub>w]u \<equiv> [G]u\<close> for u
      using "intro-elim:3:e" "log-prop-prop:2" "rigid-der:1" "rule-ui:1" by blast
    AOT_have \<open>\<box>PluralityOf(x,[G]\<^sub>w)\<close>
    proof (AOT_subst_def "pluralq:1"; safe intro!: "sign-S5-thm:1.\<rightarrow>E" "\<exists>I" "KBasic:3.\<equiv>E(2)" "&I")
      AOT_show \<open>\<box>D!u\<close>
        by (simp add: Discernible.\<psi> RN)
      AOT_have \<open>[[G]\<^sub>w]u\<close>
        using "1" "con-dis-i-e:2:a" "intro-elim:3:b" u by blast
      AOT_thus \<open>\<box>[[G]\<^sub>w]u\<close>
        using "rigid-der:2"[THEN "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2), THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"]]
        using "rule-ui:3" "vdash-properties:10" by blast
      AOT_show \<open>\<box>A!x\<close>
        using "con-dis-i-e:2:a" "con-dis-i-e:2:b" "oa-facts:2" "vdash-properties:10" u by blast
      AOT_modally_strict {
        fix F
        AOT_have \<open>\<exists>u([[G]\<^sub>w]u & F = [\<lambda>y y = u]) \<equiv> \<box>\<exists>u([[G]\<^sub>w]u & F = [\<lambda>y y = u])\<close>
        proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
          AOT_assume \<open>\<exists>u([[G]\<^sub>w]u & F = [\<lambda>y y = u])\<close>
          then AOT_obtain u where \<open>[[G]\<^sub>w]u & F = [\<lambda>y y = u]\<close>
            using "Discernible.\<exists>E"[rotated] by meson
          AOT_hence \<open>\<box>([[G]\<^sub>w]u & F = [\<lambda>y y = u])\<close>
            by (metis (lifting) "KBasic:3" "T-S5-fund:1.\<rightarrow>E" "con-dis-i-e:2:b" "con-dis-taut:1.\<rightarrow>E"
                "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "cqt:2"(1) "df-rigid-rel:1.\<equiv>\<^sub>d\<^sub>fE.&E(1)" "df-rigid-rel:1.\<equiv>\<^sub>d\<^sub>fE.&E(2)"
                "id-nec:2.\<rightarrow>E" "intro-elim:3:b" "rigid-der:2" "rigid-rel-thms:1.unvarify_F.\<forall>E(1).\<equiv>E(1).\<forall>E(1).\<rightarrow>E")
          AOT_hence \<open>\<exists>u \<box>([[G]\<^sub>w]u & F = [\<lambda>y y = u])\<close>
            using "Discernible.\<exists>I" by simp
          AOT_thus \<open>\<box>\<exists>u ([[G]\<^sub>w]u & F = [\<lambda>y y = u])\<close>
            using "Discernible.res-var-bound-reas[Buridan]" "vdash-properties:10" by fastforce
        next
          AOT_assume \<open>\<box>\<exists>u ([[G]\<^sub>w]u & F = [\<lambda>y y = u])\<close>
          AOT_thus \<open>\<exists>u ([[G]\<^sub>w]u & F = [\<lambda>y y = u])\<close>
            using "S5Basic:2.\<equiv>E(1)" "S5Basic:4.\<rightarrow>E" by blast
        qed
      } note 2 = this
      AOT_show \<open>\<box>\<forall>F(x[F] \<equiv> \<exists>u([[G]\<^sub>w]u & F = [\<lambda>y y = u]))\<close>
      proof (safe intro!: "BFs:1.\<rightarrow>E" GEN "sc-eq-box-box:4"[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "&I")
        fix F
        AOT_show \<open>\<box>(x[F] \<rightarrow> \<box>x[F])\<close>
          by (simp add: "vdash-properties:1[2]" RN encoding)
        AOT_show \<open>\<box>(\<exists>u([[G]\<^sub>w]u & F = [\<lambda>y y = u]) \<rightarrow> \<box>\<exists>u([[G]\<^sub>w]u & F = [\<lambda>y y = u]))\<close>
          using 2 "KBasic:4.\<equiv>E(1).&E(1)" RN by blast
        AOT_show \<open>\<box>x[F] \<equiv> \<box>\<exists>u([[G]\<^sub>w]u & F = [\<lambda>y y = u])\<close>
        proof (AOT_subst (reverse) \<open>\<box>x[F]\<close> \<open>x[F]\<close>, simp add: "en-eq:2[1]",
               AOT_subst (reverse) \<open>\<box>\<exists>u([[G]\<^sub>w]u & F = [\<lambda>y y = u])\<close> \<open>\<exists>u([[G]\<^sub>w]u & F = [\<lambda>y y = u])\<close>, simp add: 2;
               safe intro!: "\<equiv>I" "\<rightarrow>I")
          AOT_assume \<open>x[F]\<close>
          then AOT_obtain u where \<open>[G]u & F = [\<lambda>y y = u]\<close>
            using "Discernible.\<exists>E"[rotated] u[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<equiv>E"(1)] by fastforce
          AOT_hence \<open>[[G]\<^sub>w]u & F = [\<lambda>y y = u]\<close>
            using "1" "intro-elim:3:b" "oth-class-taut:4:e.\<rightarrow>E" by blast
          AOT_thus \<open>\<exists>u ([[G]\<^sub>w]u & F = [\<lambda>y y = u])\<close>
            using "Discernible.\<exists>I" by fast
        next
          AOT_assume \<open>\<exists>u ([[G]\<^sub>w]u & F = [\<lambda>y y = u])\<close>
          then AOT_obtain u where \<open>[[G]\<^sub>w]u & F = [\<lambda>y y = u]\<close>
            using "Discernible.\<exists>E"[rotated] by meson
          AOT_hence \<open>[G]u & F = [\<lambda>y y = u]\<close>
            by (metis "1" "con-dis-i-e:2:a" "con-dis-i-e:2:b" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "intro-elim:3:a")
          AOT_hence \<open>\<exists>u ([G]u & F = [\<lambda>y y = u])\<close>
            using "Discernible.\<exists>I" by simp
          AOT_thus \<open>x[F]\<close>
            using "con-dis-i-e:2:b" "intro-elim:3:b" "rule-ui:3" u by blast
        qed
      qed
    qed
    AOT_hence \<open>\<exists>G \<box>PluralityOf(x,G)\<close>
      using "\<exists>I"(1) by (metis "df-rigid-rel:1.\<equiv>\<^sub>d\<^sub>fE.&E(1)" "rigid-der:2")
    AOT_thus \<open>\<box>Plurality(x)\<close>
      by (AOT_subst_def "pluralq:3") (auto simp: "sign-S5-thm:1.\<rightarrow>E")
  }
qed

AOT_theorem \<open>\<exists>x\<exists>G(PluralityOf(x,G) & \<not>\<box>PluralityOf(x,G))\<close>
proof -
  AOT_obtain p where p: \<open>p & \<diamond>\<not>p\<close>
    using "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "cont-tf-thm:1.\<exists>E'" "cont-tf:1.\<equiv>\<^sub>d\<^sub>fE.&E(1)" "cont-tf:1.\<equiv>\<^sub>d\<^sub>fE.&E(2)" by blast
  AOT_obtain a where a: \<open>A!a & \<forall>F(a[F] \<equiv> \<exists>u([\<lambda>u p]u & F = [\<lambda>y y = u]))\<close>
    using "\<exists>E"[rotated] "A-objects"[axiom_inst] by meson
  AOT_have \<open>[\<lambda>u p]\<down>\<close> by "cqt:2"
  moreover AOT_have \<open>PluralityOf(a,[\<lambda>u p])\<close>
    by(rule "\<equiv>\<^sub>d\<^sub>fI"[OF "pluralq:1"]; auto intro!: "cqt:2" Discernible.\<psi> p[THEN "&E"(1)] "betaC:2:a"
        "\<exists>I" "&I" a[THEN "&E"(1)]  a[THEN "&E"(2)])
  moreover AOT_have \<open>\<not>\<box>PluralityOf(a,[\<lambda>u p])\<close>
  proof(rule "raa-cor:2")
    AOT_assume \<open>\<box>PluralityOf(a,[\<lambda>u p])\<close>
    AOT_hence \<open>\<box>p\<close>
      by(rule RM[THEN "\<rightarrow>E", rotated]; metis (no_types, lifting) "betaC:1:a" "con-dis-i-e:2:a"
              "con-dis-i-e:2:b" "deduction-theorem" "pluralq:1.\<equiv>\<^sub>d\<^sub>fE.\<exists>E'")
    AOT_thus \<open>\<box>p & \<not>\<box>p\<close>
      using "KBasic:11.\<equiv>E(2)" "con-dis-i-e:2:b" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" p by blast
  qed
  ultimately show ?thesis
    by (metis (no_types, lifting) "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "existential:1" "existential:2[const_var]")
qed


end
