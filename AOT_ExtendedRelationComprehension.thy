theory AOT_ExtendedRelationComprehension
  imports AOT_RestrictedVariables
begin

section\<open>Extended Relation Comprehension\<close>

text\<open>This theory depends choosing extended models.\<close>
interpretation AOT_ExtendedModel by (standard; auto)

text\<open>Auxiliary lemma: negations of denoting relations denote.\<close>
AOT_theorem negation_denotes: \<open>[\<lambda>x \<phi>{x}]\<down> \<rightarrow> [\<lambda>x \<not>\<phi>{x}]\<down>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>[\<lambda>x \<phi>{x}]\<down>\<close>
  AOT_show \<open>[\<lambda>x \<not>\<phi>{x}]\<down>\<close>
  proof (rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E", OF "&I"])
    AOT_show \<open>[\<lambda>x \<not>[\<lambda>x \<phi>{x}]x]\<down>\<close> by "cqt:2"
  next
    AOT_have \<open>\<box>[\<lambda>x \<phi>{x}]\<down>\<close>
      using 0 "exist-nec"[THEN "\<rightarrow>E"] by blast
    moreover AOT_have \<open>\<box>[\<lambda>x \<phi>{x}]\<down> \<rightarrow> \<box>\<forall>x (\<not>[\<lambda>x \<phi>{x}]x \<equiv> \<not>\<phi>{x})\<close>
      by(rule RM; safe intro!: GEN "\<equiv>I" "\<rightarrow>I" "\<beta>\<rightarrow>C"(2) "\<beta>\<leftarrow>C"(2) "cqt:2")
    ultimately AOT_show \<open>\<box>\<forall>x (\<not>[\<lambda>x \<phi>{x}]x \<equiv> \<not>\<phi>{x})\<close>
      using "\<rightarrow>E" by blast
  qed
qed

text\<open>Auxiliary lemma: conjunctions of denoting relations denote.\<close>
AOT_theorem conjunction_denotes: \<open>[\<lambda>x \<phi>{x}]\<down> & [\<lambda>x \<psi>{x}]\<down> \<rightarrow> [\<lambda>x \<phi>{x} & \<psi>{x}]\<down>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>[\<lambda>x \<phi>{x}]\<down> & [\<lambda>x \<psi>{x}]\<down>\<close>
  AOT_show \<open>[\<lambda>x \<phi>{x} & \<psi>{x}]\<down>\<close>
  proof (rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E", OF "&I"])
    AOT_show \<open>[\<lambda>x [\<lambda>x \<phi>{x}]x & [\<lambda>x \<psi>{x}]x]\<down>\<close> by "cqt:2"
  next
    AOT_have \<open>\<box>([\<lambda>x \<phi>{x}]\<down> & [\<lambda>x \<psi>{x}]\<down>)\<close>
      using 0 "exist-nec"[THEN "\<rightarrow>E"] "&E"
            "KBasic:3" "df-simplify:2" "intro-elim:3:b" by blast
    moreover AOT_have
      \<open>\<box>([\<lambda>x \<phi>{x}]\<down> & [\<lambda>x \<psi>{x}]\<down>) \<rightarrow> \<box>\<forall>x ([\<lambda>x \<phi>{x}]x & [\<lambda>x \<psi>{x}]x \<equiv> \<phi>{x} & \<psi>{x})\<close>
      by(rule RM; auto intro!: GEN "\<equiv>I" "\<rightarrow>I" "cqt:2" "&I"
                        intro: "\<beta>\<leftarrow>C"
                         dest: "&E" "\<beta>\<rightarrow>C")
    ultimately AOT_show \<open>\<box>\<forall>x ([\<lambda>x \<phi>{x}]x & [\<lambda>x \<psi>{x}]x \<equiv> \<phi>{x} & \<psi>{x})\<close>
      using "\<rightarrow>E" by blast
  qed
qed

AOT_register_rigid_restricted_type
  Ordinary: \<open>O!\<kappa>\<close>
proof
  AOT_modally_strict {
    AOT_show \<open>\<exists>x O!x\<close>
      by (meson "B\<diamond>" "T\<diamond>" "o-objects-exist:1" "\<rightarrow>E")
  }
next
  AOT_modally_strict {
    AOT_show \<open>O!\<kappa> \<rightarrow> \<kappa>\<down>\<close> for \<kappa>
      by (simp add: "\<rightarrow>I" "cqt:5:a[1]"[axiom_inst, THEN "\<rightarrow>E", THEN "&E"(2)])
  }
next
  AOT_modally_strict {
    AOT_show \<open>\<box>(O!\<alpha> \<rightarrow> \<box>O!\<alpha>)\<close> for \<alpha>
      by (simp add: RN "oa-facts:1")
  }
qed

AOT_register_variable_names
  Ordinary: u v r t s

text\<open>In PLM this is defined in the Natural Numbers chapter,
     but since it is helpful for stating the comprehension principles,
     we already define it here.\<close>
AOT_define eqE :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl \<open>\<equiv>\<^sub>E\<close> 50)
  eqE: \<open>F \<equiv>\<^sub>E G \<equiv>\<^sub>d\<^sub>f F\<down> & G\<down> & \<forall>u ([F]u \<equiv> [G]u)\<close>

text\<open>Derive existence claims about relations from the axioms.\<close>
AOT_theorem denotes_all: \<open>[\<lambda>x \<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> x[G])]\<down>\<close>
    and denotes_all_neg: \<open>[\<lambda>x \<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>x[G])]\<down>\<close>
proof -
  AOT_have Aux: \<open>\<forall>F (\<box>F \<equiv>\<^sub>E G \<rightarrow> (x[F] \<equiv> x[G])), \<not>(x[G] \<equiv> y[G])
    \<^bold>\<turnstile>\<^sub>\<box> \<exists>F([F]x & \<not>[F]y)\<close> for x y G
  proof -
    AOT_modally_strict {
    AOT_assume 0: \<open>\<forall>F (\<box>F \<equiv>\<^sub>E G \<rightarrow> (x[F] \<equiv> x[G]))\<close>
    AOT_assume G_prop: \<open>\<not>(x[G] \<equiv> y[G])\<close>
    {
      AOT_assume \<open>\<not>\<exists>F([F]x & \<not>[F]y)\<close>
      AOT_hence 0: \<open>\<forall>F \<not>([F]x & \<not>[F]y)\<close>
        by (metis "cqt-further:4" "\<rightarrow>E")
      AOT_have \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
      proof (rule GEN; rule "\<equiv>I"; rule "\<rightarrow>I")
        fix F
        AOT_assume \<open>[F]x\<close>
        moreover AOT_have \<open>\<not>([F]x & \<not>[F]y)\<close>
          using 0[THEN "\<forall>E"(2)] by blast
        ultimately AOT_show \<open>[F]y\<close>
          by (metis "&I" "raa-cor:1") 
      next
        fix F
        AOT_assume \<open>[F]y\<close>
        AOT_hence \<open>\<not>[\<lambda>x \<not>[F]x]y\<close>
          by (metis "\<not>\<not>I" "\<beta>\<rightarrow>C"(2))
        moreover AOT_have \<open>\<not>([\<lambda>x \<not>[F]x]x & \<not>[\<lambda>x \<not>[F]x]y)\<close>
          apply (rule 0[THEN "\<forall>E"(1)]) by "cqt:2[lambda]"
        ultimately AOT_have 1: \<open>\<not>[\<lambda>x \<not>[F]x]x\<close>
          by (metis "&I" "raa-cor:3")
        {
          AOT_assume \<open>\<not>[F]x\<close>
          AOT_hence \<open>[\<lambda>x \<not>[F]x]x\<close>
            by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2")
          AOT_hence \<open>p & \<not>p\<close> for p
            using 1 by (metis "raa-cor:3")
        }
        AOT_thus \<open>[F]x\<close> by (metis "raa-cor:1")
      qed
      AOT_hence \<open>\<box>\<forall>F ([F]x \<equiv> [F]y)\<close>
        using "ind-nec"[THEN "\<rightarrow>E"] by blast
      AOT_hence \<open>\<forall>F \<box>([F]x \<equiv> [F]y)\<close>
        by (metis "CBF" "\<rightarrow>E")
    } note indistI = this
    {
      AOT_assume G_prop: \<open>x[G] & \<not>y[G]\<close>
      AOT_hence Ax: \<open>A!x\<close>
        using "&E"(1) "\<exists>I"(2) "\<rightarrow>E" "encoders-are-abstract" by blast
  
      {
        AOT_assume Ay: \<open>A!y\<close>
        {
          fix F
          {
            AOT_assume \<open>\<forall>u\<box>([F]u \<equiv> [G]u)\<close>
            AOT_hence \<open>\<box>\<forall>u([F]u \<equiv> [G]u)\<close>
              using "Ordinary.res-var-bound-reas[BF]"[THEN "\<rightarrow>E"] by simp
            AOT_hence \<open>\<box>F \<equiv>\<^sub>E G\<close>
              by (AOT_subst \<open>F \<equiv>\<^sub>E G\<close> \<open>\<forall>u ([F]u \<equiv> [G]u)\<close>)
                 (auto intro!: "eqE"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I"] "cqt:2")
            AOT_hence \<open>x[F] \<equiv> x[G]\<close>
              using 0[THEN "\<forall>E"(2)] "\<equiv>E" "\<rightarrow>E" by meson
            AOT_hence \<open>x[F]\<close>
              using G_prop "&E" "\<equiv>E" by blast
          }
          AOT_hence \<open>\<forall>u\<box>([F]u \<equiv> [G]u) \<rightarrow> x[F]\<close>
            by (rule "\<rightarrow>I")
        }
        AOT_hence xprop: \<open>\<forall>F(\<forall>u\<box>([F]u \<equiv> [G]u) \<rightarrow> x[F])\<close>
          by (rule GEN)
        moreover AOT_have yprop: \<open>\<not>\<forall>F(\<forall>u\<box>([F]u \<equiv> [G]u) \<rightarrow> y[F])\<close>
        proof (rule "raa-cor:2")
          AOT_assume \<open>\<forall>F(\<forall>u\<box>([F]u \<equiv> [G]u) \<rightarrow> y[F])\<close>
          AOT_hence \<open>\<forall>F(\<box>\<forall>u([F]u \<equiv> [G]u) \<rightarrow> y[F])\<close>
            apply (AOT_subst \<open>\<box>\<forall>u([F]u \<equiv> [G]u)\<close> \<open>\<forall>u\<box>([F]u \<equiv> [G]u)\<close> for: F)
            using "Ordinary.res-var-bound-reas[BF]"
                  "Ordinary.res-var-bound-reas[CBF]"
                  "intro-elim:2" apply presburger
            by simp
          AOT_hence A: \<open>\<forall>F(\<box>F \<equiv>\<^sub>E G \<rightarrow> y[F])\<close>
            by (AOT_subst \<open>F \<equiv>\<^sub>E G\<close> \<open>\<forall>u ([F]u \<equiv> [G]u)\<close> for: F)
               (auto intro!: "eqE"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I"] "cqt:2")
          moreover AOT_have \<open>\<box>G \<equiv>\<^sub>E G\<close>
            by (auto intro!: "eqE"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "cqt:2" RN "&I" GEN "\<rightarrow>I" "\<equiv>I")
          ultimately AOT_have \<open>y[G]\<close> using "\<forall>E"(2) "\<rightarrow>E" by blast
          AOT_thus \<open>p & \<not>p\<close> for p using G_prop "&E" by (metis "raa-cor:3")
        qed
        AOT_have \<open>\<exists>F([F]x & \<not>[F]y)\<close>
        proof(rule "raa-cor:1")
          AOT_assume \<open>\<not>\<exists>F([F]x & \<not>[F]y)\<close>
          AOT_hence indist: \<open>\<forall>F \<box>([F]x \<equiv> [F]y)\<close> using indistI by blast
          AOT_have \<open>\<forall>F(\<forall>u\<box>([F]u \<equiv> [G]u) \<rightarrow> y[F])\<close>
            using indistinguishable_ord_enc_all[axiom_inst, THEN "\<rightarrow>E", OF "&I",
                      OF "&I", OF "&I", OF "cqt:2[const_var]"[axiom_inst],
                      OF Ax, OF Ay, OF indist, THEN "\<equiv>E"(1), OF xprop].
          AOT_thus \<open>\<forall>F(\<forall>u\<box>([F]u \<equiv> [G]u) \<rightarrow> y[F]) & \<not>\<forall>F(\<forall>u\<box>([F]u \<equiv> [G]u) \<rightarrow> y[F])\<close>
            using yprop "&I" by blast
        qed
      }
      moreover {
        AOT_assume notAy: \<open>\<not>A!y\<close>
        AOT_have \<open>\<exists>F([F]x & \<not>[F]y)\<close>
          apply (rule "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>A!\<guillemotright>\<close>])
          using Ax notAy "&I" apply blast
          by (simp add: "oa-exist:2")
      }
      ultimately AOT_have \<open>\<exists>F([F]x & \<not>[F]y)\<close>
        by (metis "raa-cor:1")
    }
    moreover {
      AOT_assume G_prop: \<open>\<not>x[G] & y[G]\<close>
      AOT_hence Ay: \<open>A!y\<close>
        by (meson "&E"(2) "encoders-are-abstract" "existential:2[const_var]" "\<rightarrow>E")
      AOT_hence notOy: \<open>\<not>O!y\<close>
        using "\<equiv>E"(1) "oa-contingent:3" by blast
      {
        AOT_assume Ax: \<open>A!x\<close>
        {
          fix F
          {
            AOT_assume \<open>\<box>\<forall>u([F]u \<equiv> [G]u)\<close>
            AOT_hence \<open>\<box>F \<equiv>\<^sub>E G\<close>
              by (AOT_subst \<open>F \<equiv>\<^sub>E G\<close> \<open>\<forall>u([F]u \<equiv> [G]u)\<close>)
                 (auto intro!: "eqE"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I"] "cqt:2")
            AOT_hence \<open>x[F] \<equiv> x[G]\<close>
              using 0[THEN "\<forall>E"(2)] "\<equiv>E" "\<rightarrow>E" by meson
            AOT_hence \<open>\<not>x[F]\<close>
              using G_prop "&E" "\<equiv>E" by blast
          }
          AOT_hence \<open>\<box>\<forall>u([F]u \<equiv> [G]u) \<rightarrow> \<not>x[F]\<close>
            by (rule "\<rightarrow>I")
        }
        AOT_hence x_prop: \<open>\<forall>F(\<box>\<forall>u([F]u \<equiv> [G]u) \<rightarrow> \<not>x[F])\<close>
          by (rule GEN)
        AOT_have x_prop: \<open>\<not>\<exists>F(\<forall>u\<box>([F]u \<equiv> [G]u) & x[F])\<close> 
        proof (rule "raa-cor:2")
          AOT_assume \<open>\<exists>F(\<forall>u \<box>([F]u \<equiv> [G]u) & x[F])\<close>
          then AOT_obtain F where F_prop: \<open>\<forall>u \<box>([F]u \<equiv> [G]u) & x[F]\<close>
            using "\<exists>E"[rotated] by blast
          AOT_have \<open>\<box>([F]u \<equiv> [G]u)\<close> for u
            using F_prop[THEN "&E"(1), THEN "Ordinary.\<forall>E"].
          AOT_hence \<open>\<forall>u \<box>([F]u \<equiv> [G]u)\<close>
            by (rule Ordinary.GEN)
          AOT_hence \<open>\<box>\<forall>u([F]u \<equiv> [G]u)\<close>
            by (metis "Ordinary.res-var-bound-reas[BF]" "\<rightarrow>E")
          AOT_hence \<open>\<not>x[F]\<close>
            using x_prop[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
          AOT_thus \<open>p & \<not>p\<close> for p
            using F_prop[THEN "&E"(2)] by (metis "raa-cor:3")
        qed
        AOT_have y_prop: \<open>\<exists>F(\<forall>u \<box>([F]u \<equiv> [G]u) & y[F])\<close>
        proof (rule "raa-cor:1")
          AOT_assume \<open>\<not>\<exists>F (\<forall>u \<box>([F]u \<equiv> [G]u) & y[F])\<close>
          AOT_hence 0: \<open>\<forall>F \<not>(\<forall>u \<box>([F]u \<equiv> [G]u) & y[F])\<close>
            using "cqt-further:4"[THEN "\<rightarrow>E"] by blast
          {
            fix F
            {
              AOT_assume \<open>\<forall>u \<box>([F]u \<equiv> [G]u)\<close>
              AOT_hence \<open>\<not>y[F]\<close>
                using 0[THEN "\<forall>E"(2)] "&I" "raa-cor:1" by meson
            }
            AOT_hence \<open>(\<forall>u \<box>([F]u \<equiv> [G]u) \<rightarrow> \<not>y[F])\<close>
              by (rule "\<rightarrow>I")
          }
          AOT_hence A: \<open>\<forall>F(\<forall>u \<box>([F]u \<equiv> [G]u) \<rightarrow> \<not>y[F])\<close>
            by (rule GEN)
          moreover AOT_have \<open>\<forall>u \<box>([G]u \<equiv> [G]u)\<close>
            by (simp add: RN "oth-class-taut:3:a" "universal-cor" "\<rightarrow>I")
          ultimately AOT_have \<open>\<not>y[G]\<close>
            using "\<forall>E"(2) "\<rightarrow>E" by blast
          AOT_thus \<open>p & \<not>p\<close> for p
            using G_prop "&E" by (metis "raa-cor:3")
        qed
    
        AOT_have \<open>\<exists>F([F]x & \<not>[F]y)\<close>
        proof(rule "raa-cor:1")
          AOT_assume \<open>\<not>\<exists>F([F]x & \<not>[F]y)\<close>
          AOT_hence indist: \<open>\<forall>F \<box>([F]x \<equiv> [F]y)\<close>
            using indistI by blast
          AOT_thus \<open>\<exists>F(\<forall>u \<box>([F]u \<equiv> [G]u) & x[F]) & \<not>\<exists>F(\<forall>u \<box>([F]u \<equiv> [G]u) & x[F])\<close>
            using indistinguishable_ord_enc_ex[axiom_inst, THEN "\<rightarrow>E", OF "&I",
                    OF "&I", OF "&I", OF "cqt:2[const_var]"[axiom_inst],
                    OF Ax, OF Ay, OF indist, THEN "\<equiv>E"(2), OF y_prop]
                x_prop "&I" by blast
        qed
      }
      moreover {
        AOT_assume notAx: \<open>\<not>A!x\<close>
        AOT_hence Ox: \<open>O!x\<close>
          using "\<or>E"(3) "oa-exist:3" by blast
        AOT_have \<open>\<exists>F([F]x & \<not>[F]y)\<close>
          apply (rule "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>O!\<guillemotright>\<close>])
          using Ox notOy "&I" apply blast
          by (simp add: "oa-exist:1")
      }
      ultimately AOT_have \<open>\<exists>F([F]x & \<not>[F]y)\<close>
        by (metis "raa-cor:1")
    }
    ultimately AOT_show \<open>\<exists>F([F]x & \<not>[F]y)\<close>
      using G_prop by (metis "&I" "\<rightarrow>I" "\<equiv>I" "raa-cor:1")
  }
  qed

  AOT_modally_strict {
    fix x y
    AOT_assume indist: \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
    AOT_hence nec_indist: \<open>\<box>\<forall>F ([F]x \<equiv> [F]y)\<close> 
      using "ind-nec" "vdash-properties:10" by blast
    AOT_hence indist_nec: \<open>\<forall>F \<box>([F]x \<equiv> [F]y)\<close>
      using "CBF" "vdash-properties:10" by blast
    AOT_assume 0: \<open>\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> x[G])\<close>
    AOT_hence 1: \<open>\<forall>G (\<box>\<forall>u ([G]u \<equiv> [F]u) \<rightarrow> x[G])\<close>
      by (AOT_subst (reverse) \<open>\<forall>u ([G]u \<equiv> [F]u)\<close> \<open>G \<equiv>\<^sub>E F\<close> for: G)
         (auto intro!: "eqE"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I"] "cqt:2")
    AOT_have \<open>x[F]\<close>
      by (safe intro!: 1[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] GEN "\<rightarrow>I" RN "\<equiv>I")
    AOT_have \<open>\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> y[G])\<close>
    proof(rule "raa-cor:1")
      AOT_assume \<open>\<not>\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> y[G])\<close>
      AOT_hence \<open>\<exists>G \<not>(\<box>G \<equiv>\<^sub>E F \<rightarrow> y[G])\<close>
        using "cqt-further:2" "\<rightarrow>E" by blast
      then AOT_obtain G where G_prop: \<open>\<not>(\<box>G \<equiv>\<^sub>E F \<rightarrow> y[G])\<close>
        using "\<exists>E"[rotated] by blast
      AOT_hence 1: \<open>\<box>G \<equiv>\<^sub>E F & \<not>y[G]\<close>
        by (metis "\<equiv>E"(1) "oth-class-taut:1:b")
      AOT_have xG: \<open>x[G]\<close>
        using 0[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] 1[THEN "&E"(1)] by blast
      AOT_hence \<open>x[G] & \<not>y[G]\<close>
        using 1[THEN "&E"(2)] "&I" by blast
      AOT_hence B: \<open>\<not>(x[G] \<equiv> y[G])\<close>
        using "&E"(2) "\<equiv>E"(1) "reductio-aa:1" xG by blast
      {
        fix H
        {
          AOT_assume \<open>\<box>H \<equiv>\<^sub>E G\<close>
          AOT_hence \<open>\<box>(H \<equiv>\<^sub>E G & G \<equiv>\<^sub>E F)\<close>
            using 1 by (metis "KBasic:3" "con-dis-i-e:1" "con-dis-i-e:2:a"
                              "intro-elim:3:b")
          moreover AOT_have \<open>\<box>(H \<equiv>\<^sub>E G & G \<equiv>\<^sub>E F) \<rightarrow> \<box>(H \<equiv>\<^sub>E F)\<close>
          proof(rule RM)
            AOT_modally_strict {
              AOT_show \<open>H \<equiv>\<^sub>E G & G \<equiv>\<^sub>E F \<rightarrow> H \<equiv>\<^sub>E F\<close>
              proof (safe intro!: "\<rightarrow>I" "eqE"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" Ordinary.GEN)
                fix u
                AOT_assume \<open>H \<equiv>\<^sub>E G & G \<equiv>\<^sub>E F\<close>
                AOT_hence \<open>\<forall>u ([H]u \<equiv> [G]u)\<close> and \<open>\<forall>u ([G]u \<equiv> [F]u)\<close>
                  using "eqE"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
                AOT_thus \<open>[H]u \<equiv> [F]u\<close>
                  by (auto dest!: "Ordinary.\<forall>E" dest: "\<equiv>E")
              qed
            }
          qed
          ultimately AOT_have \<open>\<box>(H \<equiv>\<^sub>E F)\<close>
            using "\<rightarrow>E" by blast
          AOT_hence \<open>x[H]\<close>
            using 0[THEN "\<forall>E"(2)] "\<rightarrow>E" by blast
          AOT_hence \<open>x[H] \<equiv> x[G]\<close>
            using xG "\<equiv>I" "\<rightarrow>I" by blast
        }
        AOT_hence \<open>\<box>H \<equiv>\<^sub>E G \<rightarrow> (x[H] \<equiv> x[G])\<close> by (rule "\<rightarrow>I")
      }
      AOT_hence A: \<open>\<forall>H(\<box>H \<equiv>\<^sub>E G \<rightarrow> (x[H] \<equiv> x[G]))\<close>
        by (rule GEN)
      then AOT_obtain F where F_prop: \<open>[F]x & \<not>[F]y\<close>
        using Aux[OF A, OF B] "\<exists>E"[rotated] by blast
      moreover AOT_have \<open>[F]y\<close>
        using indist[THEN "\<forall>E"(2), THEN "\<equiv>E"(1), OF F_prop[THEN "&E"(1)]].
      AOT_thus \<open>p & \<not>p\<close> for p
        using F_prop[THEN "&E"(2)] by (metis "raa-cor:3")
    qed
  } note 0 = this
  AOT_modally_strict {
    fix x y
    AOT_assume \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
    moreover AOT_have \<open>\<forall>F ([F]y \<equiv> [F]x)\<close>
      by (metis calculation "cqt-basic:11" "\<equiv>E"(2))
    ultimately AOT_have \<open>\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> x[G]) \<equiv> \<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> y[G])\<close>
      using 0 "\<equiv>I" "\<rightarrow>I" by auto
  } note 1 = this
  AOT_show \<open>[\<lambda>x \<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> x[G])]\<down>\<close>
    by (safe intro!: RN GEN "\<rightarrow>I" 1 "kirchner-thm:2"[THEN "\<equiv>E"(2)])

  AOT_modally_strict {
    fix x y
    AOT_assume indist: \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
    AOT_hence nec_indist: \<open>\<box>\<forall>F ([F]x \<equiv> [F]y)\<close> 
      using "ind-nec" "vdash-properties:10" by blast
    AOT_hence indist_nec: \<open>\<forall>F \<box>([F]x \<equiv> [F]y)\<close>
      using "CBF" "vdash-properties:10" by blast
    AOT_assume 0: \<open>\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>x[G])\<close>
    AOT_hence 1: \<open>\<forall>G (\<box>\<forall>u ([G]u \<equiv> [F]u) \<rightarrow> \<not>x[G])\<close>
      by (AOT_subst (reverse) \<open>\<forall>u ([G]u \<equiv> [F]u)\<close> \<open>G \<equiv>\<^sub>E F\<close> for: G)
         (auto intro!: "eqE"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I"] "cqt:2")
    AOT_have \<open>\<not>x[F]\<close>
      by (safe intro!: 1[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] GEN "\<rightarrow>I" RN "\<equiv>I")
    AOT_have \<open>\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>y[G])\<close>
    proof(rule "raa-cor:1")
      AOT_assume \<open>\<not>\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>y[G])\<close>
      AOT_hence \<open>\<exists>G \<not>(\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>y[G])\<close>
        using "cqt-further:2" "\<rightarrow>E" by blast
      then AOT_obtain G where G_prop: \<open>\<not>(\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>y[G])\<close>
        using "\<exists>E"[rotated] by blast
      AOT_hence 1: \<open>\<box>G \<equiv>\<^sub>E F & \<not>\<not>y[G]\<close>
        by (metis "\<equiv>E"(1) "oth-class-taut:1:b")
      AOT_hence yG: \<open>y[G]\<close>
        using G_prop "\<rightarrow>I" "raa-cor:3" by blast
      moreover AOT_hence 12: \<open>\<not>x[G]\<close>
        using 0[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] 1[THEN "&E"(1)] by blast
      ultimately AOT_have \<open>\<not>x[G] & y[G]\<close>
        using "&I" by blast
      AOT_hence B: \<open>\<not>(x[G] \<equiv> y[G])\<close>
        by (metis "12" "\<equiv>E"(3) "raa-cor:3" yG)
      {
        fix H
        {
          AOT_assume 3: \<open>\<box>H \<equiv>\<^sub>E G\<close>
          AOT_hence \<open>\<box>(H \<equiv>\<^sub>E G & G \<equiv>\<^sub>E F)\<close>
            using 1
            by (metis "KBasic:3" "con-dis-i-e:1" "\<rightarrow>I" "intro-elim:3:b"
                      "reductio-aa:1" G_prop)
          moreover AOT_have \<open>\<box>(H \<equiv>\<^sub>E G & G \<equiv>\<^sub>E F) \<rightarrow> \<box>(H \<equiv>\<^sub>E F)\<close>
          proof (rule RM)
            AOT_modally_strict {
              AOT_show \<open>H \<equiv>\<^sub>E G & G \<equiv>\<^sub>E F \<rightarrow> H \<equiv>\<^sub>E F\<close>
              proof (safe intro!: "\<rightarrow>I" "eqE"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" Ordinary.GEN)
                fix u
                AOT_assume \<open>H \<equiv>\<^sub>E G & G \<equiv>\<^sub>E F\<close>
                AOT_hence \<open>\<forall>u ([H]u \<equiv> [G]u)\<close> and \<open>\<forall>u ([G]u \<equiv> [F]u)\<close>
                  using "eqE"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
                AOT_thus \<open>[H]u \<equiv> [F]u\<close>
                  by (auto dest!: "Ordinary.\<forall>E" dest: "\<equiv>E")
              qed
            }
          qed
          ultimately AOT_have \<open>\<box>(H \<equiv>\<^sub>E F)\<close>
            using "\<rightarrow>E" by blast
          AOT_hence \<open>\<not>x[H]\<close>
            using 0[THEN "\<forall>E"(2)] "\<rightarrow>E" by blast
          AOT_hence \<open>x[H] \<equiv> x[G]\<close>
            using 12 "\<equiv>I" "\<rightarrow>I" by (metis "raa-cor:3")
        }
        AOT_hence \<open>\<box>H \<equiv>\<^sub>E G \<rightarrow> (x[H] \<equiv> x[G])\<close>
          by (rule "\<rightarrow>I")
      }
      AOT_hence A: \<open>\<forall>H(\<box>H \<equiv>\<^sub>E G \<rightarrow> (x[H] \<equiv> x[G]))\<close>
        by (rule GEN)
      then AOT_obtain F where F_prop: \<open>[F]x & \<not>[F]y\<close>
        using Aux[OF A, OF B] "\<exists>E"[rotated] by blast
      moreover AOT_have \<open>[F]y\<close>
        using indist[THEN "\<forall>E"(2), THEN "\<equiv>E"(1), OF F_prop[THEN "&E"(1)]].
      AOT_thus \<open>p & \<not>p\<close> for p
        using F_prop[THEN "&E"(2)] by (metis "raa-cor:3")
    qed
  } note 0 = this
  AOT_modally_strict {
    fix x y
    AOT_assume \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
    moreover AOT_have \<open>\<forall>F ([F]y \<equiv> [F]x)\<close>
      by (metis calculation "cqt-basic:11" "\<equiv>E"(2))
    ultimately AOT_have \<open>\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>x[G]) \<equiv> \<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>y[G])\<close>
      using 0 "\<equiv>I" "\<rightarrow>I" by auto
  } note 1 = this
  AOT_show \<open>[\<lambda>x \<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>x[G])]\<down>\<close>
    by (safe intro!: RN GEN "\<rightarrow>I" 1 "kirchner-thm:2"[THEN "\<equiv>E"(2)])
qed

text\<open>Reformulate the existence claims in terms of their negations.\<close>

AOT_theorem denotes_ex: \<open>[\<lambda>x \<exists>G (\<box>G \<equiv>\<^sub>E F & x[G])]\<down>\<close>
proof (rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E", OF "&I"])
  AOT_show \<open>[\<lambda>x \<not>\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>x[G])]\<down>\<close>
    using denotes_all_neg[THEN negation_denotes[THEN "\<rightarrow>E"]].
next
  AOT_show \<open>\<box>\<forall>x (\<not>\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>x[G]) \<equiv> \<exists>G (\<box>G \<equiv>\<^sub>E F & x[G]))\<close>
    by (AOT_subst  \<open>\<box>G \<equiv>\<^sub>E F & x[G]\<close> \<open>\<not>(\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>x[G])\<close> for: G x)
       (auto simp: "conventions:1" "rule-eq-df:1"
             intro: "oth-class-taut:4:b"[THEN "\<equiv>E"(2)]
                    "intro-elim:3:f"[OF "cqt-further:3", OF "oth-class-taut:3:b"]
             intro!: RN GEN)
qed


AOT_theorem denotes_ex_neg: \<open>[\<lambda>x \<exists>G (\<box>G \<equiv>\<^sub>E F & \<not>x[G])]\<down>\<close>
proof (rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E", OF "&I"])
  AOT_show \<open>[\<lambda>x \<not>\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> x[G])]\<down>\<close>
    using denotes_all[THEN negation_denotes[THEN "\<rightarrow>E"]].
next
  AOT_show \<open>\<box>\<forall>x (\<not>\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> x[G]) \<equiv> \<exists>G (\<box>G \<equiv>\<^sub>E F & \<not>x[G]))\<close>
    by (AOT_subst (reverse) \<open>\<box>G \<equiv>\<^sub>E F & \<not>x[G]\<close> \<open>\<not>(\<box>G \<equiv>\<^sub>E F \<rightarrow> x[G])\<close> for: G x)
       (auto simp: "oth-class-taut:1:b"
             intro: "oth-class-taut:4:b"[THEN "\<equiv>E"(2)]
                    "intro-elim:3:f"[OF "cqt-further:3", OF "oth-class-taut:3:b"]
             intro!: RN GEN)
qed

text\<open>Derive comprehension principles.\<close>

AOT_theorem Comprehension_1:
  shows \<open>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G})) \<rightarrow> [\<lambda>x \<exists>F (\<phi>{F} & x[F])]\<down>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume assm: \<open>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G}))\<close>
  AOT_modally_strict {
    fix x y
    AOT_assume 0: \<open>\<forall>F\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G}))\<close>
    AOT_assume indist: \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
    AOT_assume x_prop: \<open>\<exists>F (\<phi>{F} & x[F])\<close>
    then AOT_obtain F where F_prop: \<open>\<phi>{F} & x[F]\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>\<box>F \<equiv>\<^sub>E F & x[F]\<close>
      by (auto intro!: RN eqE[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" GEN "\<equiv>I" "\<rightarrow>I" dest: "&E")
    AOT_hence \<open>\<exists>G(\<box>G \<equiv>\<^sub>E F & x[G])\<close>
      by (rule "\<exists>I")
    AOT_hence \<open>[\<lambda>x \<exists>G(\<box>G \<equiv>\<^sub>E F & x[G])]x\<close>
      by (safe intro!: "\<beta>\<leftarrow>C" denotes_ex "cqt:2")
    AOT_hence \<open>[\<lambda>x \<exists>G(\<box>G \<equiv>\<^sub>E F & x[G])]y\<close>
      using indist[THEN "\<forall>E"(1), OF denotes_ex, THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>\<exists>G(\<box>G \<equiv>\<^sub>E F & y[G])\<close>
      using "\<beta>\<rightarrow>C" by blast
    then AOT_obtain G where \<open>\<box>G \<equiv>\<^sub>E F & y[G]\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>\<phi>{G} & y[G]\<close>
      using 0[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<equiv>E"(1)]
            F_prop[THEN "&E"(1)] "&E" "&I" by blast
    AOT_hence \<open>\<exists>F (\<phi>{F} & y[F])\<close>
      by (rule "\<exists>I")
  } note 1 = this
  AOT_modally_strict {
    AOT_assume 0: \<open>\<forall>F\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G}))\<close>
    {
      fix x y
      {
        AOT_assume \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
        moreover AOT_have \<open>\<forall>F ([F]y \<equiv> [F]x)\<close>
          by (metis calculation "cqt-basic:11" "\<equiv>E"(1))
        ultimately AOT_have \<open>\<exists>F (\<phi>{F} & x[F]) \<equiv> \<exists>F (\<phi>{F} & y[F])\<close>
          using 0 1[OF 0] "\<equiv>I" "\<rightarrow>I" by simp
      }
      AOT_hence \<open>\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<exists>F (\<phi>{F} & x[F]) \<equiv> \<exists>F (\<phi>{F} & y[F]))\<close>
        using "\<rightarrow>I" by blast
    }
    AOT_hence \<open>\<forall>x\<forall>y(\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<exists>F (\<phi>{F} & x[F]) \<equiv>  \<exists>F (\<phi>{F} & y[F])))\<close>
      by (auto intro!: GEN)
  } note 1 = this
  AOT_hence \<open>\<^bold>\<turnstile>\<^sub>\<box> \<forall>F\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G})) \<rightarrow>
                \<forall>x\<forall>y(\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<exists>F (\<phi>{F} & x[F]) \<equiv> \<exists>F (\<phi>{F} & y[F])))\<close>
    by (rule "\<rightarrow>I")
  AOT_hence \<open>\<box>\<forall>F\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G})) \<rightarrow>
             \<box>\<forall>x\<forall>y(\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<exists>F (\<phi>{F} & x[F]) \<equiv> \<exists>F (\<phi>{F} & y[F])))\<close>
    by (rule RM)
  AOT_hence \<open>\<box>\<forall>x\<forall>y(\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<exists>F (\<phi>{F} & x[F]) \<equiv> \<exists>F (\<phi>{F} & y[F])))\<close>
    using "\<rightarrow>E" assm by blast
  AOT_thus \<open>[\<lambda>x \<exists>F (\<phi>{F} & x[F])]\<down>\<close>
    by (safe intro!: "kirchner-thm:2"[THEN "\<equiv>E"(2)])
qed

AOT_theorem Comprehension_2:
  shows \<open>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G})) \<rightarrow> [\<lambda>x \<exists>F (\<phi>{F} & \<not>x[F])]\<down>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume assm: \<open>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G}))\<close>
  AOT_modally_strict {
    fix x y
    AOT_assume 0: \<open>\<forall>F\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G}))\<close>
    AOT_assume indist: \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
    AOT_assume x_prop: \<open>\<exists>F (\<phi>{F} & \<not>x[F])\<close>
    then AOT_obtain F where F_prop: \<open>\<phi>{F} & \<not>x[F]\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>\<box>F \<equiv>\<^sub>E F & \<not>x[F]\<close>
      by (auto intro!: RN eqE[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" GEN "\<equiv>I" "\<rightarrow>I" dest: "&E")
    AOT_hence \<open>\<exists>G(\<box>G \<equiv>\<^sub>E F & \<not>x[G])\<close>
      by (rule "\<exists>I")
    AOT_hence \<open>[\<lambda>x \<exists>G(\<box>G \<equiv>\<^sub>E F & \<not>x[G])]x\<close>
      by (safe intro!: "\<beta>\<leftarrow>C" denotes_ex_neg "cqt:2")
    AOT_hence \<open>[\<lambda>x \<exists>G(\<box>G \<equiv>\<^sub>E F & \<not>x[G])]y\<close>
      using indist[THEN "\<forall>E"(1), OF denotes_ex_neg, THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>\<exists>G(\<box>G \<equiv>\<^sub>E F & \<not>y[G])\<close>
      using "\<beta>\<rightarrow>C" by blast
    then AOT_obtain G where \<open>\<box>G \<equiv>\<^sub>E F & \<not>y[G]\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>\<phi>{G} & \<not>y[G]\<close>
      using 0[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<equiv>E"(1)]
            F_prop[THEN "&E"(1)] "&E" "&I" by blast
    AOT_hence \<open>\<exists>F (\<phi>{F} & \<not>y[F])\<close>
      by (rule "\<exists>I")
  } note 1 = this
  AOT_modally_strict {
    AOT_assume 0: \<open>\<forall>F\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G}))\<close>
    {
      fix x y
      {
        AOT_assume \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
        moreover AOT_have \<open>\<forall>F ([F]y \<equiv> [F]x)\<close>
          by (metis calculation "cqt-basic:11" "\<equiv>E"(1))
        ultimately AOT_have \<open>\<exists>F (\<phi>{F} & \<not>x[F]) \<equiv> \<exists>F (\<phi>{F} & \<not>y[F])\<close>
          using 0 1[OF 0] "\<equiv>I" "\<rightarrow>I" by simp
      }
      AOT_hence \<open>\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<exists>F (\<phi>{F} & \<not>x[F]) \<equiv> \<exists>F (\<phi>{F} & \<not>y[F]))\<close>
        using "\<rightarrow>I" by blast
    }
    AOT_hence \<open>\<forall>x\<forall>y(\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<exists>F (\<phi>{F} & \<not>x[F]) \<equiv>  \<exists>F (\<phi>{F} & \<not>y[F])))\<close>
      by (auto intro!: GEN)
  } note 1 = this
  AOT_hence \<open>\<^bold>\<turnstile>\<^sub>\<box> \<forall>F\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G})) \<rightarrow>
                \<forall>x\<forall>y(\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<exists>F (\<phi>{F} & \<not>x[F]) \<equiv> \<exists>F (\<phi>{F} & \<not>y[F])))\<close>
    by (rule "\<rightarrow>I")
  AOT_hence \<open>\<box>\<forall>F\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G})) \<rightarrow>
             \<box>\<forall>x\<forall>y(\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<exists>F (\<phi>{F} & \<not>x[F]) \<equiv> \<exists>F (\<phi>{F} & \<not>y[F])))\<close>
    by (rule RM)
  AOT_hence \<open>\<box>\<forall>x\<forall>y(\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<exists>F (\<phi>{F} & \<not>x[F]) \<equiv> \<exists>F (\<phi>{F} & \<not>y[F])))\<close>
    using "\<rightarrow>E" assm by blast
  AOT_thus \<open>[\<lambda>x \<exists>F (\<phi>{F} & \<not>x[F])]\<down>\<close>
    by (safe intro!: "kirchner-thm:2"[THEN "\<equiv>E"(2)])
qed

text\<open>Derived variants of the comprehension principles above.\<close>

AOT_theorem Comprehension_1':
  shows \<open>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G})) \<rightarrow> [\<lambda>x \<forall>F (x[F] \<rightarrow> \<phi>{F})]\<down>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G}))\<close>
  AOT_hence 0: \<open>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<not>\<phi>{F} \<equiv> \<not>\<phi>{G}))\<close>
    by (AOT_subst (reverse) \<open>\<not>\<phi>{F} \<equiv> \<not>\<phi>{G}\<close> \<open>\<phi>{F} \<equiv> \<phi>{G}\<close> for: F G)
       (auto simp: "oth-class-taut:4:b")
  AOT_show \<open>[\<lambda>x \<forall>F (x[F] \<rightarrow> \<phi>{F})]\<down>\<close>
  proof(rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E", OF "&I"])
    AOT_show \<open>[\<lambda>x \<not>\<exists>F(\<not>\<phi>{F} & x[F])]\<down>\<close>
      using Comprehension_1[THEN "\<rightarrow>E", OF 0, THEN negation_denotes[THEN "\<rightarrow>E"]].
  next
    AOT_show \<open>\<box>\<forall>x (\<not>\<exists>F (\<not>\<phi>{F} & x[F]) \<equiv> \<forall>F (x[F] \<rightarrow> \<phi>{F}))\<close>
      by (AOT_subst (reverse) \<open>\<not>\<phi>{F} & x[F]\<close> \<open>\<not>(x[F] \<rightarrow> \<phi>{F})\<close> for: F x)
         (auto simp: "oth-class-taut:1:b"[THEN "intro-elim:3:e",
                                          OF "oth-class-taut:2:a"]
             intro: "intro-elim:3:f"[OF "cqt-further:3", OF "oth-class-taut:3:a",
                                     symmetric]
             intro!: RN GEN)
  qed
qed

AOT_theorem Comprehension_2':
  shows \<open>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G})) \<rightarrow> [\<lambda>x \<forall>F (\<phi>{F} \<rightarrow> x[F])]\<down>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G}))\<close>
  AOT_show \<open>[\<lambda>x \<forall>F (\<phi>{F} \<rightarrow> x[F])]\<down>\<close>
  proof(rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E", OF "&I"])
    AOT_show \<open>[\<lambda>x \<not>\<exists>F(\<phi>{F} & \<not>x[F])]\<down>\<close>
      using Comprehension_2[THEN "\<rightarrow>E", OF 0, THEN negation_denotes[THEN "\<rightarrow>E"]].
  next
    AOT_show \<open>\<box>\<forall>x (\<not>\<exists>F (\<phi>{F} & \<not>x[F]) \<equiv> \<forall>F (\<phi>{F} \<rightarrow> x[F]))\<close>
      by (AOT_subst (reverse) \<open>\<phi>{F} & \<not>x[F]\<close> \<open>\<not>(\<phi>{F} \<rightarrow> x[F])\<close> for: F x)
         (auto simp: "oth-class-taut:1:b"
             intro: "intro-elim:3:f"[OF "cqt-further:3", OF "oth-class-taut:3:a",
                                     symmetric]
             intro!: RN GEN)
  qed
qed

text\<open>Derive a combined comprehension principles.\<close>

AOT_theorem Comprehension_3:
  \<open>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G})) \<rightarrow> [\<lambda>x \<forall>F (x[F] \<equiv> \<phi>{F})]\<down>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G}))\<close>
  AOT_show \<open>[\<lambda>x \<forall>F (x[F] \<equiv> \<phi>{F})]\<down>\<close>
  proof(rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E", OF "&I"])
    AOT_show \<open>[\<lambda>x \<forall>F (x[F] \<rightarrow> \<phi>{F}) & \<forall>F (\<phi>{F} \<rightarrow> x[F])]\<down>\<close>
      by (safe intro!: conjunction_denotes[THEN "\<rightarrow>E", OF "&I"]
                       Comprehension_1'[THEN "\<rightarrow>E"]
                       Comprehension_2'[THEN "\<rightarrow>E"] 0)
  next
    AOT_show \<open>\<box>\<forall>x (\<forall>F (x[F] \<rightarrow> \<phi>{F}) & \<forall>F (\<phi>{F} \<rightarrow> x[F]) \<equiv> \<forall>F (x[F] \<equiv> \<phi>{F}))\<close>
      by (auto intro!: RN GEN "\<equiv>I" "\<rightarrow>I" "&I" dest: "&E" "\<forall>E"(2) "\<rightarrow>E" "\<equiv>E"(1,2))
  qed
qed

notepad
begin
text\<open>Verify that the original axioms are equivalent to @{thm denotes_ex}
     and @{thm denotes_ex_neg}.\<close>
AOT_modally_strict {
  fix x y H
  AOT_have \<open>A!x & A!y & \<forall>F \<box>([F]x \<equiv> [F]y) \<rightarrow>
  (\<forall>G (\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [H]z)) \<rightarrow> x[G]) \<equiv>
   \<forall>G (\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [H]z)) \<rightarrow> y[G]))\<close>
  proof(rule "\<rightarrow>I")
    {
      fix x y
      AOT_assume \<open>A!x\<close>
      AOT_assume \<open>A!y\<close>
      AOT_assume indist: \<open>\<forall>F \<box>([F]x \<equiv> [F]y)\<close>
      AOT_assume \<open>\<forall>G (\<forall>u \<box>([G]u \<equiv> [H]u) \<rightarrow> x[G])\<close>
      AOT_hence \<open>\<forall>G (\<box>\<forall>u ([G]u \<equiv> [H]u) \<rightarrow> x[G])\<close>
        using "Ordinary.res-var-bound-reas[BF]" "Ordinary.res-var-bound-reas[CBF]"
              "intro-elim:2"
        by (AOT_subst \<open>\<box>\<forall>u ([G]u \<equiv> [H]u)\<close> \<open>\<forall>u \<box>([G]u \<equiv> [H]u)\<close> for: G) auto
      AOT_hence \<open>\<forall>G (\<box>G \<equiv>\<^sub>E H \<rightarrow> x[G])\<close>
        by (AOT_subst \<open>G \<equiv>\<^sub>E H\<close> \<open>\<forall>u ([G]u \<equiv> [H]u)\<close> for: G)
            (safe intro!: "eqE"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I"] "cqt:2")
      AOT_hence \<open>\<not>\<exists>G (\<box>G \<equiv>\<^sub>E H & \<not>x[G])\<close>
        by (AOT_subst (reverse) \<open>(\<box>G \<equiv>\<^sub>E H & \<not>x[G])\<close> \<open>\<not>(\<box>G \<equiv>\<^sub>E H \<rightarrow> x[G])\<close> for: G)
           (auto simp: "oth-class-taut:1:b" "cqt-further:3"[THEN "\<equiv>E"(1)])
      AOT_hence \<open>\<not>[\<lambda>x \<exists>G (\<box>G \<equiv>\<^sub>E H & \<not>x[G])]x\<close>
        by (auto intro: "\<beta>\<rightarrow>C")
      AOT_hence \<open>\<not>[\<lambda>x \<exists>G (\<box>G \<equiv>\<^sub>E H & \<not>x[G])]y\<close>
        using indist[THEN "\<forall>E"(1), OF denotes_ex_neg,
                     THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"],
                     THEN "\<equiv>E"(3)] by blast
      AOT_hence \<open>\<not>\<exists>G (\<box>G \<equiv>\<^sub>E H & \<not>y[G])\<close>
        by (safe intro!: "\<beta>\<leftarrow>C" denotes_ex_neg "cqt:2")
      AOT_hence \<open>\<forall>G \<not>(\<box>G \<equiv>\<^sub>E H & \<not>y[G])\<close>
        using "cqt-further:4"[THEN "\<rightarrow>E"] by blast
      AOT_hence \<open>\<forall>G(\<box>G \<equiv>\<^sub>E H \<rightarrow> y[G])\<close>
        by (AOT_subst \<open>\<box>G \<equiv>\<^sub>E H \<rightarrow> y[G]\<close> \<open>\<not>(\<box>G \<equiv>\<^sub>E H & \<not>y[G])\<close> for: G)
           (auto simp: "oth-class-taut:1:a")
      AOT_hence \<open>\<forall>G (\<box>\<forall>u([G]u \<equiv> [H]u) \<rightarrow> y[G])\<close>
        by (AOT_subst (reverse) \<open>\<forall>u ([G]u \<equiv> [H]u)\<close> \<open>G \<equiv>\<^sub>E H\<close> for: G)
           (safe intro!: "eqE"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I"] "cqt:2") 
      AOT_hence \<open>\<forall>G (\<forall>u \<box>([G]u \<equiv> [H]u) \<rightarrow> y[G])\<close>
        using "Ordinary.res-var-bound-reas[BF]" "Ordinary.res-var-bound-reas[CBF]"
              "intro-elim:2"
        by (AOT_subst \<open>\<forall>u \<box>([G]u \<equiv> [H]u)\<close> \<open>\<box>\<forall>u ([G]u \<equiv> [H]u)\<close> for: G) auto
    } note 0 = this
    AOT_assume \<open>A!x & A!y & \<forall>F \<box>([F]x \<equiv> [F]y)\<close>
    AOT_hence \<open>A!x\<close> and \<open>A!y\<close> and \<open>\<forall>F \<box>([F]x \<equiv> [F]y)\<close>
      using "&E" by blast+
    moreover AOT_have \<open>\<forall>F \<box>([F]y \<equiv> [F]x)\<close>
      using calculation(3)
      apply (safe intro!: CBF[THEN "\<rightarrow>E"] dest!: BF[THEN "\<rightarrow>E"])
      using "RM:3" "cqt-basic:11" "intro-elim:3:b" by fast
    ultimately AOT_show \<open>\<forall>G (\<forall>u \<box>([G]u \<equiv> [H]u) \<rightarrow> x[G]) \<equiv>
                         \<forall>G (\<forall>u \<box>([G]u \<equiv> [H]u) \<rightarrow> y[G])\<close>
      using 0 by (auto intro!: "\<equiv>I" "\<rightarrow>I")
  qed
  
  AOT_have \<open>A!x & A!y & \<forall>F \<box>([F]x \<equiv> [F]y) \<rightarrow>
  (\<exists>G (\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [H]z)) & x[G]) \<equiv> \<exists>G (\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [H]z)) & y[G]))\<close>
  proof(rule "\<rightarrow>I")
    {
      fix x y
      AOT_assume \<open>A!x\<close>
      AOT_assume \<open>A!y\<close>
      AOT_assume indist: \<open>\<forall>F \<box>([F]x \<equiv> [F]y)\<close>
      AOT_assume x_prop: \<open>\<exists>G (\<forall>u \<box>([G]u \<equiv> [H]u) & x[G])\<close>
      AOT_hence \<open>\<exists>G (\<box>\<forall>u ([G]u \<equiv> [H]u) & x[G])\<close>
        using "Ordinary.res-var-bound-reas[BF]" "Ordinary.res-var-bound-reas[CBF]"
              "intro-elim:2"
        by (AOT_subst \<open>\<box>\<forall>u ([G]u \<equiv> [H]u)\<close> \<open>\<forall>u \<box>([G]u \<equiv> [H]u)\<close> for: G) auto
      AOT_hence \<open>\<exists>G (\<box>G \<equiv>\<^sub>E H & x[G])\<close>
        by (AOT_subst \<open>G \<equiv>\<^sub>E H\<close> \<open>\<forall>u ([G]u \<equiv> [H]u)\<close> for: G)
           (safe intro!: "eqE"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I"] "cqt:2") 
      AOT_hence \<open>[\<lambda>x \<exists>G (\<box>G \<equiv>\<^sub>E H & x[G])]x\<close>
        by (safe intro!: "\<beta>\<leftarrow>C" denotes_ex "cqt:2")
      AOT_hence \<open>[\<lambda>x \<exists>G (\<box>G \<equiv>\<^sub>E H & x[G])]y\<close>
        using indist[THEN "\<forall>E"(1), OF denotes_ex,
                     THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"],
                     THEN "\<equiv>E"(1)] by blast
      AOT_hence \<open>\<exists>G (\<box>G \<equiv>\<^sub>E H & y[G])\<close>
        by (rule "\<beta>\<rightarrow>C")
      AOT_hence \<open>\<exists>G (\<box>\<forall>u ([G]u \<equiv> [H]u) & y[G])\<close>
        by (AOT_subst (reverse) \<open>\<forall>u ([G]u \<equiv> [H]u)\<close> \<open>G \<equiv>\<^sub>E H\<close> for: G)
           (safe intro!: "eqE"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I"] "cqt:2") 
      AOT_hence \<open>\<exists>G (\<forall>u \<box>([G]u \<equiv> [H]u) & y[G])\<close>
        using "Ordinary.res-var-bound-reas[BF]"
              "Ordinary.res-var-bound-reas[CBF]"
              "intro-elim:2"
        by (AOT_subst \<open>\<forall>u \<box>([G]u \<equiv> [H]u)\<close> \<open>\<box>\<forall>u ([G]u \<equiv> [H]u)\<close> for: G) auto 
    } note 0 = this
    AOT_assume \<open>A!x & A!y & \<forall>F \<box>([F]x \<equiv> [F]y)\<close>
    AOT_hence \<open>A!x\<close> and \<open>A!y\<close> and \<open>\<forall>F \<box>([F]x \<equiv> [F]y)\<close>
      using "&E" by blast+
    moreover AOT_have \<open>\<forall>F \<box>([F]y \<equiv> [F]x)\<close>
      using calculation(3)
      apply (safe intro!: CBF[THEN "\<rightarrow>E"] dest!: BF[THEN "\<rightarrow>E"])
      using "RM:3" "cqt-basic:11" "intro-elim:3:b" by fast
    ultimately AOT_show \<open>\<exists>G (\<forall>u \<box>([G]u \<equiv> [H]u) & x[G]) \<equiv>
                         \<exists>G (\<forall>u \<box>([G]u \<equiv> [H]u) & y[G])\<close>
      using 0 by (auto intro!: "\<equiv>I" "\<rightarrow>I")
  qed
}
end

end