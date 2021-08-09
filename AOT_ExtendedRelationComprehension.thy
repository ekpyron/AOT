theory AOT_ExtendedRelationComprehension
  imports AOT_RestrictedVariables
begin

section\<open>Extended Relation Comprehension\<close>

AOT_register_rigid_restricted_type
  Ordinary: \<open>O!\<kappa>\<close>
proof
  AOT_modally_strict {
    AOT_show \<open>\<exists>x O!x\<close>
      by (meson "B\<diamond>" "T\<diamond>" "o-objects-exist:1" "vdash-properties:10")
  }
next
  AOT_modally_strict {
    AOT_show \<open>O!\<kappa> \<rightarrow> \<kappa>\<down>\<close> for \<kappa>
      by (simp add: "deduction-theorem" "russell-axiom[exe,1].\<psi>_denotes_asm")
  }
next
  AOT_modally_strict {
    AOT_show \<open>\<box>(O!\<alpha> \<rightarrow> \<box>O!\<alpha>)\<close> for \<alpha>
      by (simp add: RN "oa-facts:1")
  }
qed

AOT_register_variable_names
  Ordinary: u v r t s

text\<open>In PLM this is defined in the Natural Numbers chapter, but since it is helpful for stating
     the comprehension principles, we already define it here.\<close>
AOT_define eqE :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl \<open>\<equiv>\<^sub>E\<close> 50)
  eqE: \<open>F \<equiv>\<^sub>E G \<equiv>\<^sub>d\<^sub>f F\<down> & G\<down> & \<forall>u ([F]u \<equiv> [G]u)\<close>

AOT_theorem denotes_all: \<open>[\<lambda>x \<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> x[G])]\<down>\<close>
    and denotes_all_neg: \<open>[\<lambda>x \<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>x[G])]\<down>\<close>
proof -
  AOT_have Aux: \<open>\<forall>F (\<box>F \<equiv>\<^sub>E G \<rightarrow> (x[F] \<equiv> x[G])), \<not>(x[G] \<equiv> y[G]) \<^bold>\<turnstile>\<^sub>\<box> \<exists>F([F]x & \<not>[F]y)\<close> for x y G
  proof -
    AOT_modally_strict {
    AOT_assume 0: \<open>\<forall>F (\<box>F \<equiv>\<^sub>E G \<rightarrow> (x[F] \<equiv> x[G]))\<close>
    AOT_assume G_prop: \<open>\<not>(x[G] \<equiv> y[G])\<close>
    {
      AOT_assume \<open>\<not>\<exists>F([F]x & \<not>[F]y)\<close>
      AOT_hence 0: \<open>\<forall>F \<not>([F]x & \<not>[F]y)\<close> by (metis "cqt-further:4" "vdash-properties:10")
      AOT_have \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
      proof (rule GEN; rule "\<equiv>I"; rule "\<rightarrow>I")
        fix F
        AOT_assume \<open>[F]x\<close>
        moreover AOT_have \<open>\<not>([F]x & \<not>[F]y)\<close> using 0[THEN "\<forall>E"(2)] by blast
        ultimately AOT_show \<open>[F]y\<close> by (metis "&I" "raa-cor:1") 
      next
        fix F
        AOT_assume \<open>[F]y\<close>
        AOT_hence \<open>\<not>[\<lambda>x \<not>[F]x]y\<close> by (metis "\<not>\<not>I" "\<beta>\<rightarrow>C"(2))
        moreover AOT_have \<open>\<not>([\<lambda>x \<not>[F]x]x & \<not>[\<lambda>x \<not>[F]x]y)\<close>
          apply (rule 0[THEN "\<forall>E"(1)]) by "cqt:2[lambda]"
        ultimately AOT_have 1: \<open>\<not>[\<lambda>x \<not>[F]x]x\<close> by (metis "&I" "raa-cor:3")
        {
          AOT_assume \<open>\<not>[F]x\<close>
          AOT_hence \<open>[\<lambda>x \<not>[F]x]x\<close>
            by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2")
          AOT_hence \<open>p & \<not>p\<close> for p using 1 by (metis "raa-cor:3")
        }
        AOT_thus \<open>[F]x\<close> by (metis "raa-cor:1")
      qed
      AOT_hence \<open>\<box>\<forall>F ([F]x \<equiv> [F]y)\<close> using "ind-nec"[THEN "\<rightarrow>E"] by blast
      AOT_hence \<open>\<forall>F \<box>([F]x \<equiv> [F]y)\<close> by (metis "CBF" "vdash-properties:10")
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
            AOT_hence \<open>x[F] \<equiv> x[G]\<close> using 0[THEN "\<forall>E"(2)] "\<equiv>E" "\<rightarrow>E" by meson
            AOT_hence \<open>x[F]\<close> using G_prop "&E" "\<equiv>E" by blast
          }
          AOT_hence \<open>\<forall>u\<box>([F]u \<equiv> [G]u) \<rightarrow> x[F]\<close> by (rule "\<rightarrow>I")
        }
        AOT_hence xprop: \<open>\<forall>F(\<forall>u\<box>([F]u \<equiv> [G]u) \<rightarrow> x[F])\<close> by (rule GEN)
        moreover AOT_have yprop: \<open>\<not>\<forall>F(\<forall>u\<box>([F]u \<equiv> [G]u) \<rightarrow> y[F])\<close>
        proof (rule "raa-cor:2")
          AOT_assume \<open>\<forall>F(\<forall>u\<box>([F]u \<equiv> [G]u) \<rightarrow> y[F])\<close>
          AOT_hence \<open>\<forall>F(\<box>\<forall>u([F]u \<equiv> [G]u) \<rightarrow> y[F])\<close>
            apply (AOT_subst \<open>\<box>\<forall>u([F]u \<equiv> [G]u)\<close> \<open>\<forall>u\<box>([F]u \<equiv> [G]u)\<close> for: F)
            using "Ordinary.res-var-bound-reas[BF]" "Ordinary.res-var-bound-reas[CBF]" "intro-elim:2" apply presburger
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
            using indistinguishable_ord_enc_all[axiom_inst, THEN "\<rightarrow>E", OF "&I", OF "&I", OF "&I", OF "cqt:2[const_var]"[axiom_inst], OF Ax, OF Ay, OF indist, THEN "\<equiv>E"(1), OF xprop].
          AOT_thus \<open>\<forall>F(\<forall>u\<box>([F]u \<equiv> [G]u) \<rightarrow> y[F]) & \<not>\<forall>F(\<forall>u\<box>([F]u \<equiv> [G]u) \<rightarrow> y[F])\<close> using yprop "&I" by blast
        qed
      }
      moreover {
        AOT_assume notAy: \<open>\<not>A!y\<close>
        AOT_have \<open>\<exists>F([F]x & \<not>[F]y)\<close>
          apply (rule "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>A!\<guillemotright>\<close>])
          using Ax notAy "&I" apply blast
          by (simp add: "oa-exist:2")
      }
      ultimately AOT_have \<open>\<exists>F([F]x & \<not>[F]y)\<close>  by (metis "raa-cor:1")
    }
    moreover {
      AOT_assume G_prop: \<open>\<not>x[G] & y[G]\<close>
      AOT_hence Ay: \<open>A!y\<close>
        by (meson "&E"(2) "encoders-are-abstract" "existential:2[const_var]" "vdash-properties:10")
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
            AOT_hence \<open>x[F] \<equiv> x[G]\<close> using 0[THEN "\<forall>E"(2)] "\<equiv>E" "\<rightarrow>E" by meson
            AOT_hence \<open>\<not>x[F]\<close> using G_prop "&E" "\<equiv>E" by blast
          }
          AOT_hence \<open>\<box>\<forall>u([F]u \<equiv> [G]u) \<rightarrow> \<not>x[F]\<close> by (rule "\<rightarrow>I")
        }
        AOT_hence x_prop: \<open>\<forall>F(\<box>\<forall>u([F]u \<equiv> [G]u) \<rightarrow> \<not>x[F])\<close> by (rule GEN)
        AOT_have x_prop: \<open>\<not>\<exists>F(\<forall>u\<box>([F]u \<equiv> [G]u) & x[F])\<close> 
        proof (rule "raa-cor:2")
          AOT_assume \<open>\<exists>F(\<forall>u \<box>([F]u \<equiv> [G]u) & x[F])\<close>
          then AOT_obtain F where F_prop: \<open>\<forall>u \<box>([F]u \<equiv> [G]u) & x[F]\<close> using "\<exists>E"[rotated] by blast
          AOT_have \<open>\<box>([F]u \<equiv> [G]u)\<close> for u using F_prop[THEN "&E"(1), THEN "Ordinary.\<forall>E"].
          AOT_hence \<open>\<forall>u \<box>([F]u \<equiv> [G]u)\<close> by (rule Ordinary.GEN)
          AOT_hence \<open>\<box>\<forall>u([F]u \<equiv> [G]u)\<close> by (metis "Ordinary.res-var-bound-reas[BF]" "vdash-properties:10")
          AOT_hence \<open>\<not>x[F]\<close> using x_prop[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
          AOT_thus \<open>p & \<not>p\<close> for p using F_prop[THEN "&E"(2)] by (metis "raa-cor:3")
        qed
        AOT_have y_prop: \<open>\<exists>F(\<forall>u \<box>([F]u \<equiv> [G]u) & y[F])\<close>
        proof (rule "raa-cor:1")
          AOT_assume \<open>\<not>\<exists>F (\<forall>u \<box>([F]u \<equiv> [G]u) & y[F])\<close>
          AOT_hence 0: \<open>\<forall>F \<not>(\<forall>u \<box>([F]u \<equiv> [G]u) & y[F])\<close> using "cqt-further:4"[THEN "\<rightarrow>E"] by blast
          {
            fix F
            {
              AOT_assume \<open>\<forall>u \<box>([F]u \<equiv> [G]u)\<close>
              AOT_hence \<open>\<not>y[F]\<close> using 0[THEN "\<forall>E"(2)] using "&I" "raa-cor:1" by meson
            }
            AOT_hence \<open>(\<forall>u \<box>([F]u \<equiv> [G]u) \<rightarrow> \<not>y[F])\<close> by (rule "\<rightarrow>I")
          }
          AOT_hence A: \<open>\<forall>F(\<forall>u \<box>([F]u \<equiv> [G]u) \<rightarrow> \<not>y[F])\<close> by (rule GEN)
          moreover AOT_have \<open>\<forall>u \<box>([G]u \<equiv> [G]u)\<close>
            by (simp add: RN "oth-class-taut:3:a" "universal-cor" "vdash-properties:9")
          ultimately AOT_have \<open>\<not>y[G]\<close> using "\<forall>E"(2) "\<rightarrow>E" by blast
          AOT_thus \<open>p & \<not>p\<close> for p using G_prop "&E" by (metis "raa-cor:3")
        qed
    
        AOT_have \<open>\<exists>F([F]x & \<not>[F]y)\<close>
        proof(rule "raa-cor:1")
          AOT_assume \<open>\<not>\<exists>F([F]x & \<not>[F]y)\<close>
          AOT_hence indist: \<open>\<forall>F \<box>([F]x \<equiv> [F]y)\<close>
            using indistI by blast
          AOT_thus \<open>\<exists>F(\<forall>u \<box>([F]u \<equiv> [G]u) & x[F]) & \<not>\<exists>F(\<forall>u \<box>([F]u \<equiv> [G]u) & x[F])\<close>
            using indistinguishable_ord_enc_ex[axiom_inst, THEN "\<rightarrow>E", OF "&I", OF "&I", OF "&I",
                OF "cqt:2[const_var]"[axiom_inst], OF Ax, OF Ay, OF indist, THEN "\<equiv>E"(2), OF y_prop]
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
      ultimately AOT_have \<open>\<exists>F([F]x & \<not>[F]y)\<close> by (metis "raa-cor:1")
    }
    ultimately AOT_show \<open>\<exists>F([F]x & \<not>[F]y)\<close>
      using G_prop by (metis "&I" "deduction-theorem" "\<equiv>I" "raa-cor:1")
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
      AOT_hence \<open>\<exists>G \<not>(\<box>G \<equiv>\<^sub>E F \<rightarrow> y[G])\<close> using "cqt-further:2" "vdash-properties:10" by blast
      then AOT_obtain G where G_prop: \<open>\<not>(\<box>G \<equiv>\<^sub>E F \<rightarrow> y[G])\<close> using "\<exists>E"[rotated] by blast
      AOT_hence 1: \<open>\<box>G \<equiv>\<^sub>E F & \<not>y[G]\<close> by (metis "\<equiv>E"(1) "oth-class-taut:1:b")
      AOT_have xG: \<open>x[G]\<close> using 0[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] 1[THEN "&E"(1)] by blast
      AOT_hence \<open>x[G] & \<not>y[G]\<close> using 1[THEN "&E"(2)] "&I" by blast
      AOT_hence B: \<open>\<not>(x[G] \<equiv> y[G])\<close>
        using "&E"(2) "\<equiv>E"(1) "reductio-aa:1" xG by blast
      {
        fix H
        {
          AOT_assume \<open>\<box>H \<equiv>\<^sub>E G\<close>
          AOT_hence \<open>\<box>(H \<equiv>\<^sub>E G & G \<equiv>\<^sub>E F)\<close>
            using 1 by (metis "KBasic:3" "con-dis-i-e:1" "con-dis-i-e:2:a" "intro-elim:3:b")
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
          ultimately AOT_have \<open>\<box>(H \<equiv>\<^sub>E F)\<close> using "\<rightarrow>E" by blast
          AOT_hence \<open>x[H]\<close> using 0[THEN "\<forall>E"(2)] "\<rightarrow>E" by blast
          AOT_hence \<open>x[H] \<equiv> x[G]\<close> using xG "\<equiv>I" "\<rightarrow>I" by blast
        }
        AOT_hence \<open>\<box>H \<equiv>\<^sub>E G \<rightarrow> (x[H] \<equiv> x[G])\<close> by (rule "\<rightarrow>I")
      }
      AOT_hence A: \<open>\<forall>H(\<box>H \<equiv>\<^sub>E G \<rightarrow> (x[H] \<equiv> x[G]))\<close> by (rule GEN)
      then AOT_obtain F where F_prop: \<open>[F]x & \<not>[F]y\<close> using Aux[OF A, OF B] "\<exists>E"[rotated] by blast
      moreover AOT_have \<open>[F]y\<close> using indist[THEN "\<forall>E"(2), THEN "\<equiv>E"(1), OF F_prop[THEN "&E"(1)]].
      AOT_thus \<open>p & \<not>p\<close> for p using F_prop[THEN "&E"(2)] by (metis "raa-cor:3")
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
      AOT_hence \<open>\<exists>G \<not>(\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>y[G])\<close> using "cqt-further:2" "vdash-properties:10" by blast
      then AOT_obtain G where G_prop: \<open>\<not>(\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>y[G])\<close> using "\<exists>E"[rotated] by blast
      AOT_hence 1: \<open>\<box>G \<equiv>\<^sub>E F & \<not>\<not>y[G]\<close> by (metis "\<equiv>E"(1) "oth-class-taut:1:b")
      AOT_hence yG: \<open>y[G]\<close>
        using G_prop "deduction-theorem" "raa-cor:3" by blast
      moreover AOT_hence 12: \<open>\<not>x[G]\<close> using 0[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] 1[THEN "&E"(1)] by blast
      ultimately AOT_have \<open>\<not>x[G] & y[G]\<close> using "&I" by blast
      AOT_hence B: \<open>\<not>(x[G] \<equiv> y[G])\<close> by (metis "12" "\<equiv>E"(3) "raa-cor:3" yG)
      {
        fix H
        {
          AOT_assume 3: \<open>\<box>H \<equiv>\<^sub>E G\<close>
          AOT_hence \<open>\<box>(H \<equiv>\<^sub>E G & G \<equiv>\<^sub>E F)\<close> using 1
            by (metis "KBasic:3" "con-dis-i-e:1" "deduction-theorem" "intro-elim:3:b" "reductio-aa:1" G_prop)
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
          ultimately AOT_have \<open>\<box>(H \<equiv>\<^sub>E F)\<close> using "\<rightarrow>E" by blast
          AOT_hence \<open>\<not>x[H]\<close> using 0[THEN "\<forall>E"(2)] "\<rightarrow>E" by blast
          AOT_hence \<open>x[H] \<equiv> x[G]\<close> using 12 "\<equiv>I" "\<rightarrow>I" by (metis "raa-cor:3")
        }
        AOT_hence \<open>\<box>H \<equiv>\<^sub>E G \<rightarrow> (x[H] \<equiv> x[G])\<close> by (rule "\<rightarrow>I")
      }
      AOT_hence A: \<open>\<forall>H(\<box>H \<equiv>\<^sub>E G \<rightarrow> (x[H] \<equiv> x[G]))\<close> by (rule GEN)
      then AOT_obtain F where F_prop: \<open>[F]x & \<not>[F]y\<close> using Aux[OF A, OF B] "\<exists>E"[rotated] by blast
      moreover AOT_have \<open>[F]y\<close> using indist[THEN "\<forall>E"(2), THEN "\<equiv>E"(1), OF F_prop[THEN "&E"(1)]].
      AOT_thus \<open>p & \<not>p\<close> for p using F_prop[THEN "&E"(2)] by (metis "raa-cor:3")
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

AOT_theorem denotes_ex: \<open>[\<lambda>x \<exists>G (\<box>G \<equiv>\<^sub>E F & x[G])]\<down>\<close>
proof (rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E", OF "&I"])
  AOT_show \<open>[\<lambda>x \<not>[\<lambda>x \<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>x[G])]x]\<down>\<close>
    by "cqt:2"
next
  AOT_show \<open>\<box>\<forall>x (\<not>[\<lambda>x \<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>x[G])]x \<equiv> \<exists>G (\<box>G \<equiv>\<^sub>E F & x[G]))\<close>
  proof(safe intro!: RN "\<equiv>I" "\<rightarrow>I" GEN)
    AOT_modally_strict {
      fix x
      AOT_assume \<open>\<not>[\<lambda>x \<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>x[G])]x\<close>
      AOT_hence \<open>\<not>\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>x[G])\<close>
        by (safe intro!: "\<beta>\<leftarrow>C"(2) denotes_all_neg "cqt:2")
      AOT_hence \<open>\<exists>G \<not>(\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>x[G])\<close>
        using "cqt-further:2"[THEN "\<rightarrow>E"] by blast
      AOT_thus \<open>\<exists>G (\<box>G \<equiv>\<^sub>E F & x[G])\<close>
        apply (AOT_subst \<open>\<box>G \<equiv>\<^sub>E F & x[G]\<close> \<open>\<not>(\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>x[G])\<close> for: G)
        using "conventions:1" "rule-eq-df:1" apply presburger
        by blast
    }
  next
    AOT_modally_strict {
      fix x
      AOT_assume \<open>\<exists>G (\<box>G \<equiv>\<^sub>E F & x[G])\<close>
      AOT_hence \<open>\<exists>G \<not>(\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>x[G])\<close>
        apply (AOT_subst (reverse) \<open>\<not>(\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>x[G])\<close> \<open>\<box>G \<equiv>\<^sub>E F & x[G]\<close> for: G)
        using "conventions:1" "rule-eq-df:1" apply presburger
        by blast
      AOT_hence \<open>\<not>\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>x[G])\<close>
        using "\<not>\<not>I" "cqt-further:3" "intro-elim:3:d" by fast
      AOT_thus \<open>\<not>[\<lambda>x \<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> \<not>x[G])]x\<close>
        by (safe intro!: "\<beta>\<rightarrow>C"(2))
    }
  qed
qed

AOT_theorem denotes_ex_neg: \<open>[\<lambda>x \<not>\<exists>G (\<box>G \<equiv>\<^sub>E F & x[G])]\<down>\<close>
proof (rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E", OF "&I"])
  AOT_show \<open>[\<lambda>x \<not>[\<lambda>x \<exists>G (\<box>G \<equiv>\<^sub>E F & x[G])]x]\<down>\<close>
    by "cqt:2"
next
  AOT_show \<open>\<box>\<forall>x (\<not>[\<lambda>x \<exists>G (\<box>G \<equiv>\<^sub>E F & x[G])]x \<equiv> \<not>\<exists>G (\<box>G \<equiv>\<^sub>E F & x[G]))\<close>
    by (AOT_subst \<open>[\<lambda>x \<exists>G (\<box>G \<equiv>\<^sub>E F & x[G])]x\<close> \<open>\<exists>G (\<box>G \<equiv>\<^sub>E F & x[G])\<close> for: x)
       (safe intro!: GEN RN "beta-C-meta"[THEN "\<rightarrow>E"] denotes_ex "\<equiv>I" "\<rightarrow>I")
qed


AOT_theorem Comprehension_1:
  shows \<open>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G})) \<rightarrow> [\<lambda>x \<forall>F (\<phi>{F} \<rightarrow> x[F])]\<down>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume assm: \<open>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G}))\<close>
  AOT_modally_strict {
    fix x y
    AOT_assume 0: \<open>\<forall>F\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G}))\<close>
    AOT_assume indist: \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
    AOT_assume x_prop: \<open>\<forall>F (\<phi>{F} \<rightarrow> x[F])\<close>
    AOT_have \<open>\<forall>F (\<phi>{F} \<rightarrow> y[F])\<close>
    proof(safe intro!: GEN "\<rightarrow>I")
      fix F
      AOT_assume \<phi>F: \<open>\<phi>{F}\<close>
      AOT_hence \<open>x[F]\<close> using x_prop "\<forall>E"(2) "\<rightarrow>E" by blast
      {
        fix G
        {
          AOT_assume \<open>\<box>G \<equiv>\<^sub>E F\<close>
          AOT_hence \<open>\<phi>{G}\<close>
            using 0[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<equiv>E"(1)] \<phi>F by blast
          AOT_hence \<open>x[G]\<close> using x_prop[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
        }
        AOT_hence \<open>\<box>G \<equiv>\<^sub>E F \<rightarrow> x[G]\<close> using "\<rightarrow>I" by blast
      }
      AOT_hence \<open>\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> x[G])\<close> by (rule GEN)
      AOT_hence \<open>[\<lambda>x \<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> x[G])]x\<close>
        by (safe intro!: "\<beta>\<leftarrow>C" denotes_all "cqt:2")
      AOT_hence \<open>[\<lambda>x \<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> x[G])]y\<close>
        using indist[THEN "\<forall>E"(1), OF denotes_all, THEN "\<equiv>E"(1)] by blast
      AOT_hence \<open>\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> y[G])\<close>
        using "\<beta>\<rightarrow>C" by blast
      AOT_hence \<open>\<box>F \<equiv>\<^sub>E F \<rightarrow> y[F]\<close>
        using "\<forall>E"(2) by blast
      moreover AOT_have \<open>\<box>F \<equiv>\<^sub>E F\<close>
        by(safe intro!: RN "\<equiv>I" "\<rightarrow>I" GEN "eqE"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2")
      ultimately AOT_show \<open>y[F]\<close>
        using "\<rightarrow>E" by blast
    qed
  } note 1 = this
  AOT_modally_strict {
    AOT_assume 0: \<open>\<forall>F\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G}))\<close>
    {
      fix x y
      {
        AOT_assume \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
        moreover AOT_have \<open>\<forall>F ([F]y \<equiv> [F]x)\<close>
          by (metis calculation "cqt-basic:11" "\<equiv>E"(1))
        ultimately AOT_have \<open>\<forall>F (\<phi>{F} \<rightarrow> x[F]) \<equiv> \<forall>F (\<phi>{F} \<rightarrow> y[F])\<close>
          using 0 1[OF 0] "\<equiv>I" "\<rightarrow>I" by simp
      }
      AOT_hence \<open>\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<forall>F (\<phi>{F} \<rightarrow> x[F]) \<equiv> \<forall>F (\<phi>{F} \<rightarrow> y[F]))\<close> using "\<rightarrow>I" by blast
    }
    AOT_hence \<open>\<forall>y(\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<forall>F (\<phi>{F} \<rightarrow> x[F]) \<equiv> \<forall>F (\<phi>{F} \<rightarrow> y[F])))\<close> for x
      by (rule GEN)
    AOT_hence \<open>\<forall>x\<forall>y(\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<forall>F (\<phi>{F} \<rightarrow> x[F]) \<equiv> \<forall>F (\<phi>{F} \<rightarrow> y[F])))\<close>
      by (rule GEN)
  } note 1 = this
  AOT_hence \<open>\<^bold>\<turnstile>\<^sub>\<box> \<forall>F\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G})) \<rightarrow> \<forall>x\<forall>y(\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<forall>F (\<phi>{F} \<rightarrow> x[F]) \<equiv> \<forall>F (\<phi>{F} \<rightarrow> y[F])))\<close>
    by (rule "\<rightarrow>I")
  AOT_hence \<open>\<box>\<forall>F\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G})) \<rightarrow> \<box>\<forall>x\<forall>y(\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<forall>F (\<phi>{F} \<rightarrow> x[F]) \<equiv> \<forall>F (\<phi>{F} \<rightarrow> y[F])))\<close>
    by (rule RM)
  AOT_hence \<open>\<box>\<forall>x\<forall>y(\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<forall>F (\<phi>{F} \<rightarrow> x[F]) \<equiv> \<forall>F (\<phi>{F} \<rightarrow> y[F])))\<close>
    using "\<rightarrow>E" assm by blast
  AOT_thus \<open>[\<lambda>x \<forall>F (\<phi>{F} \<rightarrow> x[F])]\<down>\<close>
    by (safe intro!: "kirchner-thm:2"[THEN "\<equiv>E"(2)])
qed

AOT_theorem Comprehension_2:
  \<open>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G})) \<rightarrow> [\<lambda>x \<forall>F (x[F] \<rightarrow> \<phi>{F})]\<down>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume assm: \<open>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G}))\<close>
  AOT_modally_strict {
    fix x y
    AOT_assume 0: \<open>\<forall>F\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G}))\<close>
    AOT_assume indist: \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
    AOT_assume x_prop: \<open>\<forall>F (x[F] \<rightarrow> \<phi>{F})\<close>
    AOT_have \<open>\<forall>F (y[F] \<rightarrow> \<phi>{F})\<close>
    proof(safe intro!: GEN "\<rightarrow>I")
      fix F
      AOT_assume \<open>y[F]\<close>
      AOT_hence \<open>\<box>F \<equiv>\<^sub>E F & y[F]\<close>
        by (safe intro!: RN "&I" GEN "\<rightarrow>I" "\<equiv>I" "eqE"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "cqt:2")
      AOT_hence \<open>\<exists>G (\<box>G \<equiv>\<^sub>E F & y[G])\<close> by (rule "\<exists>I")
      AOT_hence \<open>[\<lambda>y \<exists>G (\<box>G \<equiv>\<^sub>E F & y[G])]y\<close>
        by (safe intro!: "\<beta>\<leftarrow>C" denotes_ex "cqt:2")
      AOT_hence \<open>[\<lambda>y \<exists>G (\<box>G \<equiv>\<^sub>E F & y[G])]x\<close>
        using indist[THEN "\<forall>E"(1), OF denotes_ex, THEN "\<equiv>E"(2)] by blast
      AOT_hence \<open>\<exists>G (\<box>G \<equiv>\<^sub>E F & x[G])\<close>
        using "\<beta>\<rightarrow>C" by blast
      then AOT_obtain G where \<open>\<box>G \<equiv>\<^sub>E F & x[G]\<close> using "\<exists>E"[rotated] by blast
      moreover AOT_have \<open>\<phi>{G}\<close> using calculation x_prop[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] "&E" by blast
      ultimately AOT_show \<open>\<phi>{F}\<close> using 0[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<equiv>E"(2)] "&E" by blast
    qed
  } note 1 = this
  AOT_modally_strict {
    AOT_assume 0: \<open>\<forall>F\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G}))\<close>
    {
      fix x y
      {
        AOT_assume \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
        moreover AOT_have \<open>\<forall>F ([F]y \<equiv> [F]x)\<close>
          by (metis calculation "cqt-basic:11" "\<equiv>E"(1))
        ultimately AOT_have \<open>\<forall>F (x[F] \<rightarrow> \<phi>{F}) \<equiv> \<forall>F (y[F] \<rightarrow> \<phi>{F})\<close>
          using 0 1[OF 0] "\<equiv>I" "\<rightarrow>I" by simp
      }
      AOT_hence \<open>\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<forall>F (x[F] \<rightarrow> \<phi>{F}) \<equiv> \<forall>F (y[F] \<rightarrow> \<phi>{F}))\<close> using "\<rightarrow>I" by blast
    }
    AOT_hence \<open>\<forall>y(\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<forall>F (x[F] \<rightarrow> \<phi>{F}) \<equiv> \<forall>F (y[F] \<rightarrow> \<phi>{F})))\<close> for x
      by (rule GEN)
    AOT_hence \<open>\<forall>x\<forall>y(\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<forall>F (x[F] \<rightarrow> \<phi>{F}) \<equiv> \<forall>F (y[F] \<rightarrow> \<phi>{F})))\<close>
      by (rule GEN)
  } note 1 = this
  AOT_hence \<open>\<^bold>\<turnstile>\<^sub>\<box> \<forall>F\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G})) \<rightarrow> \<forall>x\<forall>y(\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<forall>F (x[F] \<rightarrow> \<phi>{F}) \<equiv> \<forall>F (y[F] \<rightarrow> \<phi>{F})))\<close>
    by (rule "\<rightarrow>I")
  AOT_hence \<open>\<box>\<forall>F\<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G})) \<rightarrow> \<box>\<forall>x\<forall>y(\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<forall>F (x[F] \<rightarrow> \<phi>{F}) \<equiv> \<forall>F (y[F] \<rightarrow> \<phi>{F})))\<close>
    by (rule RM)
  AOT_hence \<open>\<box>\<forall>x\<forall>y(\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> (\<forall>F (x[F] \<rightarrow> \<phi>{F}) \<equiv> \<forall>F (y[F] \<rightarrow> \<phi>{F})))\<close>
    using "\<rightarrow>E" assm by blast
  AOT_thus \<open>[\<lambda>x \<forall>F (x[F] \<rightarrow> \<phi>{F})]\<down>\<close>
    by (safe intro!: "kirchner-thm:2"[THEN "\<equiv>E"(2)])
qed

AOT_theorem Comprehension_3: \<open>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G})) \<rightarrow> [\<lambda>x \<forall>F (x[F] \<equiv> \<phi>{F})]\<down>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G}))\<close>
  AOT_hence \<open>\<box>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G}))\<close>
    using "S5Basic:5"[THEN "\<rightarrow>E"] by blast
  moreover AOT_have \<open>\<box>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G})) \<rightarrow> \<box>\<forall>x
                     ([\<lambda>x \<forall>F (x[F] \<rightarrow> \<phi>{F})]x & [\<lambda>x \<forall>F (\<phi>{F} \<rightarrow> x[F])]x \<equiv> \<forall>F (x[F] \<equiv> \<phi>{F}))\<close>
  proof(rule RM; rule "\<rightarrow>I")
    AOT_modally_strict {
      AOT_assume \<open>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G}))\<close>
      AOT_hence \<open>[\<lambda>x \<forall>F (x[F] \<rightarrow> \<phi>{F})]\<down>\<close> and \<open>[\<lambda>x \<forall>F (\<phi>{F} \<rightarrow> x[F])]\<down>\<close>
        using Comprehension_1[THEN "\<rightarrow>E"] Comprehension_2[THEN "\<rightarrow>E"] by auto
      AOT_thus \<open>\<forall>x ([\<lambda>x \<forall>F (x[F] \<rightarrow> \<phi>{F})]x & [\<lambda>x \<forall>F (\<phi>{F} \<rightarrow> x[F])]x \<equiv> \<forall>F (x[F] \<equiv> \<phi>{F}))\<close>
        by(auto intro!: GEN "\<equiv>I" "\<rightarrow>I" "&I" "\<beta>\<leftarrow>C" "cqt:2[const_var]"[axiom_inst]
                dest!: "\<beta>\<rightarrow>C" dest: "&E" "\<forall>E"(2) "\<rightarrow>E" "\<equiv>E")
    }
  qed
  ultimately AOT_have \<open>\<box>\<forall>x ([\<lambda>x \<forall>F (x[F] \<rightarrow> \<phi>{F})]x & [\<lambda>x \<forall>F (\<phi>{F} \<rightarrow> x[F])]x \<equiv> \<forall>F (x[F] \<equiv> \<phi>{F}))\<close>
    using "\<rightarrow>E" by blast
  AOT_thus \<open>[\<lambda>x \<forall>F (x[F] \<equiv> \<phi>{F})]\<down>\<close>
  proof (safe_step intro!: "safe-ext"[axiom_inst, THEN "\<rightarrow>E", OF "&I"])
    AOT_show \<open>[\<lambda>x [\<lambda>x \<forall>F (x[F] \<rightarrow> \<phi>{F})]x & [\<lambda>x \<forall>F (\<phi>{F} \<rightarrow> x[F])]x]\<down>\<close>
      by "cqt:2"
  qed(auto)
qed

notepad
begin
text\<open>Verify that the axioms are equivalent to @{text \<open>denotes_all\<close>} and @{text \<open>denotes_ex\<close>}.\<close>
AOT_modally_strict {
  fix x y H
  AOT_have \<open>A!x & A!y & \<forall>F \<box>([F]x \<equiv> [F]y) \<rightarrow>
  (\<forall>G (\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [H]z)) \<rightarrow> x[G]) \<equiv> \<forall>G (\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [H]z)) \<rightarrow> y[G]))\<close>
  proof(rule "\<rightarrow>I")
    {
      fix x y
      AOT_assume \<open>A!x\<close>
      AOT_assume \<open>A!y\<close>
      AOT_assume indist: \<open>\<forall>F \<box>([F]x \<equiv> [F]y)\<close>
      AOT_assume \<open>\<forall>G (\<forall>u \<box>([G]u \<equiv> [H]u) \<rightarrow> x[G])\<close>
      AOT_hence \<open>\<forall>G (\<box>\<forall>u ([G]u \<equiv> [H]u) \<rightarrow> x[G])\<close>
        using "Ordinary.res-var-bound-reas[BF]" "Ordinary.res-var-bound-reas[CBF]" "intro-elim:2"
        by (AOT_subst \<open>\<box>\<forall>u ([G]u \<equiv> [H]u)\<close> \<open>\<forall>u \<box>([G]u \<equiv> [H]u)\<close> for: G) auto
      AOT_hence \<open>\<forall>G (\<box>G \<equiv>\<^sub>E H \<rightarrow> x[G])\<close>
        by (AOT_subst \<open>G \<equiv>\<^sub>E H\<close> \<open>\<forall>u ([G]u \<equiv> [H]u)\<close> for: G)
            (safe intro!: "eqE"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I"] "cqt:2") 
      AOT_hence \<open>[\<lambda>x \<forall>G (\<box>G \<equiv>\<^sub>E H \<rightarrow> x[G])]x\<close>
        by (safe intro!: "\<beta>\<leftarrow>C" denotes_all "cqt:2")
      AOT_hence \<open>[\<lambda>x \<forall>G (\<box>G \<equiv>\<^sub>E H \<rightarrow> x[G])]y\<close>
        using indist[THEN "\<forall>E"(1), OF denotes_all, THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"], THEN "\<equiv>E"(1)] by blast
      AOT_hence \<open>\<forall>G (\<box>G \<equiv>\<^sub>E H \<rightarrow> y[G])\<close>
        using "\<beta>\<rightarrow>C" by blast
      AOT_hence \<open>\<forall>G (\<box>\<forall>u([G]u \<equiv> [H]u) \<rightarrow> y[G])\<close>
        by (AOT_subst (reverse) \<open>\<forall>u ([G]u \<equiv> [H]u)\<close> \<open>G \<equiv>\<^sub>E H\<close> for: G)
           (safe intro!: "eqE"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I"] "cqt:2") 
      AOT_hence \<open>\<forall>G (\<forall>u \<box>([G]u \<equiv> [H]u) \<rightarrow> y[G])\<close>
        using "Ordinary.res-var-bound-reas[BF]" "Ordinary.res-var-bound-reas[CBF]" "intro-elim:2"
        by (AOT_subst \<open>\<forall>u \<box>([G]u \<equiv> [H]u)\<close> \<open>\<box>\<forall>u ([G]u \<equiv> [H]u)\<close> for: G) auto
    } note 0 = this
    AOT_assume \<open>A!x & A!y & \<forall>F \<box>([F]x \<equiv> [F]y)\<close>
    AOT_hence \<open>A!x\<close> and \<open>A!y\<close> and \<open>\<forall>F \<box>([F]x \<equiv> [F]y)\<close>
      using "&E" by blast+
    moreover AOT_have \<open>\<forall>F \<box>([F]y \<equiv> [F]x)\<close>
      using calculation(3)
      apply (safe intro!: CBF[THEN "\<rightarrow>E"] dest!: BF[THEN "\<rightarrow>E"])
      using "RM:3" "cqt-basic:11" "intro-elim:3:b" by fast
    ultimately AOT_show \<open>\<forall>G (\<forall>u \<box>([G]u \<equiv> [H]u) \<rightarrow> x[G]) \<equiv> \<forall>G (\<forall>u \<box>([G]u \<equiv> [H]u) \<rightarrow> y[G])\<close>
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
        using "Ordinary.res-var-bound-reas[BF]" "Ordinary.res-var-bound-reas[CBF]" "intro-elim:2"
        by (AOT_subst \<open>\<box>\<forall>u ([G]u \<equiv> [H]u)\<close> \<open>\<forall>u \<box>([G]u \<equiv> [H]u)\<close> for: G) auto
      AOT_hence \<open>\<exists>G (\<box>G \<equiv>\<^sub>E H & x[G])\<close>
        by (AOT_subst \<open>G \<equiv>\<^sub>E H\<close> \<open>\<forall>u ([G]u \<equiv> [H]u)\<close> for: G)
           (safe intro!: "eqE"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I"] "cqt:2") 
      AOT_hence \<open>[\<lambda>x \<exists>G (\<box>G \<equiv>\<^sub>E H & x[G])]x\<close>
        by (safe intro!: "\<beta>\<leftarrow>C" denotes_ex "cqt:2")
      AOT_hence \<open>[\<lambda>x \<exists>G (\<box>G \<equiv>\<^sub>E H & x[G])]y\<close>
        using indist[THEN "\<forall>E"(1), OF denotes_ex, THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"], THEN "\<equiv>E"(1)] by blast
      AOT_hence \<open>\<exists>G (\<box>G \<equiv>\<^sub>E H & y[G])\<close>
        by (rule "\<beta>\<rightarrow>C")
      AOT_hence \<open>\<exists>G (\<box>\<forall>u ([G]u \<equiv> [H]u) & y[G])\<close>
        by (AOT_subst (reverse) \<open>\<forall>u ([G]u \<equiv> [H]u)\<close> \<open>G \<equiv>\<^sub>E H\<close> for: G)
           (safe intro!: "eqE"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I"] "cqt:2") 
      AOT_hence \<open>\<exists>G (\<forall>u \<box>([G]u \<equiv> [H]u) & y[G])\<close>
        using "Ordinary.res-var-bound-reas[BF]" "Ordinary.res-var-bound-reas[CBF]" "intro-elim:2"
        by (AOT_subst \<open>\<forall>u \<box>([G]u \<equiv> [H]u)\<close> \<open>\<box>\<forall>u ([G]u \<equiv> [H]u)\<close> for: G) auto 
    } note 0 = this
    AOT_assume \<open>A!x & A!y & \<forall>F \<box>([F]x \<equiv> [F]y)\<close>
    AOT_hence \<open>A!x\<close> and \<open>A!y\<close> and \<open>\<forall>F \<box>([F]x \<equiv> [F]y)\<close>
      using "&E" by blast+
    moreover AOT_have \<open>\<forall>F \<box>([F]y \<equiv> [F]x)\<close>
      using calculation(3)
      apply (safe intro!: CBF[THEN "\<rightarrow>E"] dest!: BF[THEN "\<rightarrow>E"])
      using "RM:3" "cqt-basic:11" "intro-elim:3:b" by fast
    ultimately AOT_show \<open>\<exists>G (\<forall>u \<box>([G]u \<equiv> [H]u) & x[G]) \<equiv> \<exists>G (\<forall>u \<box>([G]u \<equiv> [H]u) & y[G])\<close>
      using 0 by (auto intro!: "\<equiv>I" "\<rightarrow>I")
  qed
}
end

end