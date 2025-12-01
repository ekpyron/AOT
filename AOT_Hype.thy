theory AOT_Hype
  imports AOT_PossibleWorlds
begin

(* TODO: improve property negation syntax *)

AOT_define hype :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>Hype'(_')\<close>)
  "hype:1": \<open>Hype(p) \<equiv>\<^sub>d\<^sub>f ((((p)\<^sup>-))\<^sup>-) = p\<close>

AOT_theorem "hype:2": \<open>Hype(p) \<rightarrow> Hype(((p)\<^sup>-))\<close>
  by (metis "deduction-theorem" "hype:1.\<equiv>\<^sub>d\<^sub>fE.rule=E'" "hype:1.\<equiv>\<^sub>d\<^sub>fI" "log-prop-prop:2" "rule=I:1"
      "thm-relation-negation:9.unvarify_p.unvarify_q.\<forall>E(1).\<forall>E(1).\<rightarrow>E.rule=E'")

axiomatization where "hype:3": \<open>\<And> v . [v \<Turnstile> \<exists>p Hype(p)]\<close>

AOT_define hypestate :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>HypeState'(_')\<close>)
  "hype:4": \<open>HypeState(x) \<equiv>\<^sub>d\<^sub>f Situation(x) & \<forall>p(x \<Turnstile> p \<rightarrow> Hype(p))\<close>

AOT_theorem "hype:1[nec]": \<open>Hype(p) \<rightarrow> \<box>Hype(p)\<close>
proof(safe intro!: "\<rightarrow>I")
  fix p
  AOT_assume \<open>Hype(p)\<close>
  AOT_hence \<open>((((p)\<^sup>-))\<^sup>-) = p\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" "hype:1" by blast
  AOT_hence \<open>\<box>(((((p)\<^sup>-))\<^sup>-) = p)\<close>
    by (simp add: "id-nec:2.\<rightarrow>E")
  AOT_thus \<open>\<box>Hype(p)\<close>
    by (AOT_subst_def "hype:1")
qed

AOT_register_rigid_restricted_type
  Hype: \<open>Hype(\<phi>)\<close>
proof
  AOT_modally_strict {
    AOT_show \<open>\<exists>p Hype(p)\<close>
      using "hype:3".
  }
next
  AOT_modally_strict {
    AOT_show \<open>Hype(\<tau>) \<rightarrow> \<tau>\<down>\<close> for \<tau>
      by (simp add: "deduction-theorem" "log-prop-prop:2")
  }
next
  AOT_modally_strict {
    AOT_show \<open>\<forall>p(Hype(p) \<rightarrow> \<box>Hype(p))\<close>
      by(safe intro!: GEN "\<rightarrow>I" "hype:1[nec]")
  }
qed

AOT_theorem "hype:4[nec]": \<open>HypeState(x) \<rightarrow> \<box>HypeState(x)\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_assume \<open>HypeState(x)\<close>
  AOT_hence 1: \<open>Situation(x) & \<forall>p(x \<Turnstile> p \<rightarrow> Hype(p))\<close>
    by (simp add: "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "deduction-theorem" "hype:4.\<equiv>\<^sub>d\<^sub>fE.&E(1)"
        "hype:4.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E" "log-prop-prop:2" "universal-cor")
  AOT_have \<open>\<box>Situation(x)\<close>
    using "1" "con-dis-taut:1.\<rightarrow>E" "possit-sit:1.unvarify_x.\<forall>E(1).\<equiv>E(1)" "situations:3.\<rightarrow>E"
    by blast
  moreover AOT_have \<open>\<box>\<forall>p(x \<Turnstile> p \<rightarrow> Hype(p))\<close>
  proof(safe intro!: "BFs:1.\<rightarrow>E" GEN; rule "sc-eq-box-box:6.\<rightarrow>E.\<rightarrow>E")
    fix p
    AOT_show \<open>\<box>(x \<Turnstile> p \<rightarrow> \<box>x \<Turnstile> p)\<close>
      by (metis "KBasic:1.\<rightarrow>E" "KBasic:2.\<rightarrow>E" "S5Basic:4.\<rightarrow>E" "S5Basic:5.\<rightarrow>E" "T-S5-fund:1.\<rightarrow>E"
          "lem2:1.unconstrain_s.unvarify_p.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<equiv>E(1)"
          "lem2:5.unconstrain_s.unvarify_p.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<equiv>E(1)" "log-prop-prop:2" "raa-cor:2"
          "situations:3.\<rightarrow>E" calculation)
    AOT_show \<open>x \<Turnstile> p \<rightarrow> \<box>Hype(p)\<close>
    proof(rule "\<rightarrow>I")
      AOT_assume \<open>x \<Turnstile> p\<close>
      AOT_hence \<open>Hype(p)\<close>
        using 1[THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=p], THEN "\<rightarrow>E"] by simp
      AOT_hence \<open>((((p)\<^sup>-))\<^sup>-) = p\<close>
        using "\<equiv>\<^sub>d\<^sub>fE" "hype:1" by blast
      AOT_hence \<open>\<box>(((((p)\<^sup>-))\<^sup>-) = p)\<close>
        by (simp add: "id-nec:2.\<rightarrow>E")
      AOT_thus \<open>\<box>Hype(p)\<close>
        by (AOT_subst_def "hype:1")
    qed
  qed
  ultimately AOT_have \<open>\<box>(Situation(x) & \<forall>p(x \<Turnstile> p \<rightarrow> Hype(p)))\<close>
    using "KBasic:3.\<equiv>E(2)" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" by blast
  AOT_thus \<open>\<box>HypeState(x)\<close>
    by (AOT_subst_def "hype:4")
qed

AOT_register_rigid_restricted_type
  HypeState: \<open>HypeState(\<kappa>)\<close>
proof
  AOT_modally_strict {
    AOT_have \<open>\<exists>s \<forall>p(s \<Turnstile> p \<equiv> Hype(p))\<close>
      by (simp add: "sit-comp-simp:1")
    then AOT_obtain s where \<open>\<forall>p(s \<Turnstile> p \<equiv> Hype(p))\<close>
      using "Situation.\<exists>E"[rotated] by meson
    AOT_hence \<open>\<forall>p(s \<Turnstile> p \<rightarrow> Hype(p))\<close>
      by (metis (lifting) "deduction-theorem" "intro-elim:3:a" "rule-ui:3" "universal-cor")
    AOT_hence \<open>HypeState(s)\<close>
      by (simp add: "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "hype:4.\<equiv>\<^sub>d\<^sub>fI" Situation.restricted_var_condition)
    AOT_thus \<open>\<exists> x HypeState(x)\<close>
      by (rule "\<exists>I")
  }
next
  AOT_modally_strict {
    fix \<tau>
    AOT_show \<open>HypeState(\<tau>) \<rightarrow> \<tau>\<down>\<close>
      by (simp add: "deduction-theorem" "hype:4.\<equiv>\<^sub>d\<^sub>fE.&E(1)" "situations:3.\<rightarrow>E")
  }
next
  AOT_modally_strict {
    AOT_show \<open>\<forall>x(HypeState(x) \<rightarrow> \<box>HypeState(x))\<close>
      by(safe intro!: GEN "\<rightarrow>I" "hype:4[nec]")
  }
qed

AOT_register_variable_names
  Hype: \<p> \<q>

AOT_register_variable_names
  HypeState: \<s>

AOT_theorem "hype:5": \<open>\<exists>\<s>\<forall>\<p>(\<s> \<Turnstile> \<p> \<equiv> \<phi>{\<p>})\<close>
proof -
  AOT_have \<open>\<exists>s\<forall>p(s \<Turnstile> p \<equiv> Hype(p) & \<phi>{p})\<close>
    by (simp add: "sit-comp-simp:1")
  then AOT_obtain s where s: \<open>\<forall>p(s \<Turnstile> p \<equiv> Hype(p) & \<phi>{p})\<close>
    using "Situation.\<exists>E"[rotated] by meson
  AOT_hence \<open>\<forall>\<p>(s \<Turnstile> \<p> \<equiv> \<phi>{\<p>})\<close>
    by (metis (no_types, lifting) "log-prop-prop:2" "oth-class-taut:8:i" "rule-ui:1" "universal-cor"
        "vdash-properties:10")
  moreover AOT_have \<open>HypeState(s)\<close>
    by (metis (no_types, lifting) "con-dis-i-e:2:a" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "deduction-theorem"
        "hype:4.\<equiv>\<^sub>d\<^sub>fI" "intro-elim:3:a" "rule-ui:3" "universal-cor" Situation.\<psi> s)
  ultimately AOT_show \<open>\<exists>\<s>\<forall>\<p>(\<s> \<Turnstile> \<p> \<equiv> \<phi>{\<p>})\<close>
    by (meson "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "existential:2[const_var]")
qed

AOT_theorem hype_state_situation: \<open>Situation(\<s>)\<close>
  using "hype:4.\<equiv>\<^sub>d\<^sub>fE.&E(1)" HypeState.restricted_var_condition by presburger

AOT_theorem "hype:6":
  assumes \<open>for arbitrary p: \<phi>{p} \<rightarrow> Hype(p)\<close>
  shows \<open>\<exists>!\<s>\<forall>\<p>(\<s> \<Turnstile> \<p> \<equiv> \<phi>{\<p>})\<close>
proof -
  AOT_obtain \<s> where 1: \<open>\<forall>\<p>(\<s> \<Turnstile> \<p> \<equiv> \<phi>{\<p>})\<close>
    using "hype:5" "HypeState.\<exists>E"[rotated] by meson
  moreover {
    fix \<s>'
    AOT_assume 2: \<open>\<forall>\<p>(\<s>' \<Turnstile> \<p> \<equiv> \<phi>{\<p>})\<close>
    AOT_have \<open>\<s>' = \<s>\<close>
    proof (safe intro!: GEN "\<equiv>I" "\<rightarrow>I" "sit-identity"[unconstrain s, unconstrain s', THEN "\<rightarrow>E", OF hype_state_situation, THEN "\<rightarrow>E", OF hype_state_situation, THEN "\<equiv>E"(2)])
      fix p
      AOT_assume \<open>\<s> \<Turnstile> p\<close>
      AOT_hence \<open>\<phi>{p}\<close>
        by (metis "cqt-basic:12.\<rightarrow>E.\<forall>E(1).\<rightarrow>E" "hype:4.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E" "intro-elim:3:a"
            "log-prop-prop:2" "vdash-properties:10" AOT_restricted_type.restricted_var_condition
            HypeState.AOT_restricted_type_axioms 1)
      AOT_thus \<open>\<s>' \<Turnstile> p\<close>
        using "2" "intro-elim:3:b" "oth-class-taut:4:a.\<rightarrow>E.\<rightarrow>E.\<rightarrow>E" "rule-ui:2[const_var]" assms
        by blast
    next
      fix p
      AOT_assume \<open>\<s>' \<Turnstile> p\<close>
      AOT_hence \<open>\<phi>{p}\<close>
        by (metis "2" "cqt-basic:12.\<rightarrow>E.\<forall>E(1).\<rightarrow>E" "hype:4.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E" "intro-elim:3:a"
            "log-prop-prop:2" "vdash-properties:10" AOT_restricted_type.restricted_var_condition
            HypeState.AOT_restricted_type_axioms)
      AOT_thus \<open>\<s> \<Turnstile> p\<close>
        by (metis "intro-elim:3:b" "log-prop-prop:2" "rule-ui:1" "vdash-properties:10" assms
            1)
    qed
  }
  ultimately AOT_have \<open>HypeState(\<s>) & \<forall>\<p> (\<s> \<Turnstile> \<p> \<equiv> \<phi>{\<p>}) & \<forall>\<beta> (HypeState(\<beta>) & \<forall>\<p> (\<beta> \<Turnstile> \<p> \<equiv> \<phi>{\<p>}) \<rightarrow> \<beta> = \<s>)\<close>
    by (metis (no_types, lifting) "HypeState.\<forall>I" "con-dis-i-e:1" "con-dis-i-e:2:b" "con-dis-taut:1.\<rightarrow>E"
        "deduction-theorem" "rule-ui:2[const_var]" "universal-cor" "vdash-properties:6"
        HypeState.restricted_var_condition)
  AOT_thus \<open>\<exists>!\<s>\<forall>\<p>(\<s> \<Turnstile> \<p> \<equiv> \<phi>{\<p>})\<close>
    apply (AOT_subst_def "uniqueness:1")
    using "\<exists>I" by fast
qed

AOT_theorem "hype:7": \<open>(\<s> \<Turnstile> \<p> & \<s>' \<Turnstile> ((\<p>)\<^sup>-)) \<rightarrow> \<s>!\<s>'\<close>
  by (metis (no_types, lifting) "\<equiv>\<^sub>d\<^sub>fI" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "deduction-theorem" "existential:1"
      "incomp-sit:1" "log-prop-prop:2" hype_state_situation)

AOT_theorem "hype:8": \<open>\<s>!\<s>' \<rightarrow> (\<s> \<oplus> \<s>'')!(\<s>'\<oplus>\<s>'')\<close>
  by (simp add: "cqt:2"(1) "deduction-theorem"
      "incomp-sit:10.unconstrain_s.unconstrain_s'.unconstrain_s''.unconstrain_s'''.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<rightarrow>E"
      hype_state_situation)

AOT_define RoutleyStarHype :: \<open>\<tau> \<Rightarrow> \<tau>\<close> (\<open>_\<^sup>\<star>\<close>)
"routley-star-hype:1": \<open>\<s>\<^sup>\<star> =\<^sub>d\<^sub>f \<^bold>\<iota>\<s>' \<forall>\<p>(\<s>' \<Turnstile> \<p> \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-)))\<close>

AOT_theorem 
  "routley-star-hype:1[denotes']": \<open>\<^bold>\<iota>\<s>' \<forall>\<p>(\<s>' \<Turnstile> \<p> \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-)))\<down>\<close>
  and 
  "routley-star-hype:1[denotes]": \<open>\<s>\<^sup>\<star>\<down>\<close>
  and
  "routley-star-hype:1[HypeState]": \<open>HypeState(\<s>\<^sup>\<star>)\<close>
proof -
  AOT_have \<open>\<^bold>\<A>\<exists>!\<s>' \<forall>\<p>(\<s>' \<Turnstile> \<p> \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-)))\<close>
  proof(safe intro!: "RA[2]" "hype:6" "\<rightarrow>I")
    AOT_modally_strict {
    fix p
    AOT_assume \<open>\<exists>\<q> (\<not>\<s> \<Turnstile> \<q> & p = ((\<q>)\<^sup>-))\<close>
    then AOT_obtain \<q> where \<open>(\<not>\<s> \<Turnstile> \<q> & p = ((\<q>)\<^sup>-))\<close>
      using "Hype.\<exists>E"[rotated] by meson
    AOT_thus \<open>Hype(p)\<close>
      using "con-dis-i-e:2:b" "hype:2.unvarify_p.\<forall>E(1).\<rightarrow>E" "log-prop-prop:2" "rule=E'"
        Hype.restricted_var_condition id_sym by blast
  }
  qed
  AOT_thus 0: \<open>\<^bold>\<iota>\<s>' \<forall>\<p>(\<s>' \<Turnstile> \<p> \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-)))\<down>\<close>
    by (simp add: "A-Exists:2.\<equiv>E(2)")
  AOT_thus \<open>\<s>\<^sup>\<star>\<down>\<close>
    using "rule-id-df:2:b"[OF "routley-star-hype:1"] by blast
  AOT_have \<open>\<^bold>\<A>HypeState(\<s>\<^sup>\<star>)\<close>
    using "rule-id-df:2:b"[OF "routley-star-hype:1", OF 0]
    using "0" "RA[2]" "act-cond.\<rightarrow>E.\<rightarrow>E" "con-dis-taut:1"
      "nec-hintikka-scheme.unvarify_x.\<forall>E(1).\<equiv>E(1).&E(1)" "rule=I:1" id_sym by blast
  AOT_thus \<open>HypeState(\<s>\<^sup>\<star>)\<close>
    by (metis "HypeState.res-var:3" "deduction-theorem" "hype:4[nec].unvarify_x.\<forall>E(1).\<rightarrow>E"
        "sc-eq-fur:2.\<rightarrow>E.\<equiv>E(1)" "vdash-properties:10" RN)
qed

AOT_theorem "routley-star-hype:2": \<open>\<forall>\<p>(\<s>\<^sup>\<star> \<Turnstile> \<p> \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-)))\<close>
proof(rule "Hype.\<forall>I")
  fix \<p>
  AOT_have \<open>\<^bold>\<A>(HypeState(\<^bold>\<iota>\<s>' \<forall>\<p>(\<s>' \<Turnstile> \<p> \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-)))) & \<forall>\<p>(\<^bold>\<iota>\<s>' \<forall>\<p>(\<s>' \<Turnstile> \<p> \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-))) \<Turnstile> \<p> \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-))))\<close>
    using "routley-star-hype:1[denotes']"
    using "actual-desc:4.\<rightarrow>E" by blast
  AOT_hence \<open>\<^bold>\<A>\<forall>\<p>(\<^bold>\<iota>\<s>' \<forall>\<p>(\<s>' \<Turnstile> \<p> \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-))) \<Turnstile> \<p> \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-)))\<close>
    using "Act-Basic:2.\<equiv>E(1).&E(2)" by blast
  AOT_hence \<open>\<forall>p\<^bold>\<A>(Hype(p) \<rightarrow> (\<^bold>\<iota>\<s>' \<forall>\<p>(\<s>' \<Turnstile> \<p> \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-))) \<Turnstile> p \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & p = ((\<q>)\<^sup>-))))\<close>
    by (meson "RA[2]" "act-cond.\<rightarrow>E.\<rightarrow>E" "cqt-orig:3" "universal-cor")
  AOT_hence \<open>\<forall>p(\<^bold>\<A>Hype(p) \<rightarrow> \<^bold>\<A>(\<^bold>\<iota>\<s>' \<forall>\<p>(\<s>' \<Turnstile> \<p> \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-))) \<Turnstile> p \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & p = ((\<q>)\<^sup>-))))\<close>
    by (metis (no_types, lifting) "act-cond.\<rightarrow>E.\<rightarrow>E" "deduction-theorem" "rule-ui:3"
        "universal-cor")
  AOT_hence \<open>\<forall>p(Hype(p) \<rightarrow> \<^bold>\<A>(\<^bold>\<iota>\<s>' \<forall>\<p>(\<s>' \<Turnstile> \<p> \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-))) \<Turnstile> p \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & p = ((\<q>)\<^sup>-))))\<close>
    by (metis (no_types, lifting) "deduction-theorem" "hype:1[nec]" "log-prop-prop:2" "nec-imp-act.\<rightarrow>E"
        "rule-ui:1" "universal-cor" "vdash-properties:6")
  AOT_hence \<open>\<^bold>\<A>(\<^bold>\<iota>\<s>' \<forall>\<p>(\<s>' \<Turnstile> \<p> \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-))) \<Turnstile> \<p> \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-)))\<close>
    using "Hype.\<forall>E" by fast
  AOT_hence 1: \<open>\<^bold>\<A>(\<^bold>\<iota>\<s>' \<forall>\<p>(\<s>' \<Turnstile> \<p> \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-))) \<Turnstile> \<p>) \<equiv> \<^bold>\<A>\<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-))\<close>
    using "Act-Basic:5" "intro-elim:3:a" by blast
  AOT_hence 2: \<open>\<^bold>\<A>(\<s>\<^sup>\<star> \<Turnstile> \<p>) \<equiv> \<^bold>\<A>\<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-))\<close>
    using "rule-id-df:2:b"[where \<tau>\<^sub>1\<tau>\<^sub>n="(AOT_term_of_var (HypeState.Rep \<s>))", OF "routley-star-hype:1", OF "routley-star-hype:1[denotes']"]
    by fast
  AOT_show \<open>\<s>\<^sup>\<star> \<Turnstile> \<p> \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-))\<close>
  proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
    AOT_assume \<open>\<s>\<^sup>\<star> \<Turnstile> \<p>\<close>
    AOT_hence \<open>\<^bold>\<A>\<s>\<^sup>\<star> \<Turnstile> \<p>\<close>
      by (simp add: "cqt:2"(1) "hype_state_situation.unconstrain_\<s>.\<forall>E(1).\<rightarrow>E"
          "lem2:4.unconstrain_s.unvarify_p.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<equiv>E(2)" "routley-star-hype:1[HypeState]"
          "routley-star-hype:1[denotes]")
    AOT_hence \<open>\<^bold>\<A>\<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-))\<close>
      using "2" "intro-elim:3:a" by blast
    AOT_hence \<open>\<exists>q \<^bold>\<A>(Hype(q) & (\<not>\<s> \<Turnstile> q & \<p> = ((q)\<^sup>-)))\<close>
      by (meson "Act-Basic:10.\<equiv>E(1).\<exists>E'" "existential:2[const_var]")
    then AOT_obtain q where \<open>\<^bold>\<A>(Hype(q) & (\<not>\<s> \<Turnstile> q & \<p> = ((q)\<^sup>-)))\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>\<^bold>\<A>Hype(q) & \<^bold>\<A>(\<not>\<s> \<Turnstile> q) & \<^bold>\<A>(\<p> = ((q)\<^sup>-))\<close>
      by (meson "Act-Basic:2.\<equiv>E(1).&E(1)" "Act-Basic:2.\<equiv>E(1).&E(2)" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E")
    AOT_hence \<open>Hype(q) & ((\<not>\<s> \<Turnstile> q) & (\<p> = ((q)\<^sup>-)))\<close>
      by (metis "Act-Sub:1.\<equiv>E(1)" "con-dis-i-e:2:b" "con-dis-taut:1.\<rightarrow>E" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E"
          "cqt:2"(1) "id-act:1.unvarify_\<alpha>.unvarify_\<beta>.\<forall>E(1).\<forall>E(1).\<equiv>E(2).rule=E'" "id-eq:1"
          "lem2:4.unconstrain_s.unvarify_p.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<equiv>E(2)" "log-prop-prop:2" "raa-cor:4"
          "sc-eq-fur:2.\<rightarrow>E.\<equiv>E(1)" "true-in-s.\<equiv>\<^sub>d\<^sub>fE.&E(1)" Hype.rigid_condition)
    AOT_thus \<open>\<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-))\<close>
      by (simp add: "existential:2[const_var]")
  next
    AOT_assume \<open>\<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-))\<close>
    then AOT_obtain q where \<open>Hype(q) & ((\<not>\<s> \<Turnstile> q) & (\<p> = ((q)\<^sup>-)))\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>\<^bold>\<A>Hype(q) & \<^bold>\<A>(\<not>\<s> \<Turnstile> q) & \<^bold>\<A>(\<p> = ((q)\<^sup>-))\<close>
      by (metis "con-dis-i-e:2:b" "con-dis-taut:1.\<rightarrow>E" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "id-nec:2.\<rightarrow>E"
          "lem2:5.unconstrain_s.unvarify_p.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<equiv>E(1)" "log-prop-prop:2" "nec-imp-act.\<rightarrow>E"
          "sc-eq-fur:2.\<rightarrow>E.\<equiv>E(2)" "situations:3.\<rightarrow>E" Hype.rigid_condition hype_state_situation)
    AOT_hence \<open>\<^bold>\<A>(Hype(q) & (\<not>\<s> \<Turnstile> q & \<p> = ((q)\<^sup>-)))\<close>
      by (metis "act-conj-act:3.\<rightarrow>E" "con-dis-i-e:2:b" "con-dis-taut:1.\<rightarrow>E"
          "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E")
    AOT_hence \<open>\<exists>q \<^bold>\<A>(Hype(q) & (\<not>\<s> \<Turnstile> q & \<p> = ((q)\<^sup>-)))\<close>
      using "\<exists>I" by fast
    AOT_hence \<open>\<^bold>\<A>\<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-))\<close>
      by (simp add: "Act-Basic:10.\<equiv>E(2)")
    AOT_hence \<open>\<^bold>\<A>(\<s>\<^sup>\<star> \<Turnstile> \<p>)\<close>
      using "2" "intro-elim:3:b" by blast
    AOT_thus \<open>\<s>\<^sup>\<star> \<Turnstile> \<p>\<close>
      by (simp add: "hype:4.\<equiv>\<^sub>d\<^sub>fE.&E(1)" "lem2:4.unconstrain_s.unvarify_p.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<equiv>E(1)"
          "log-prop-prop:2" "routley-star-hype:1[HypeState]" "situations:3.\<rightarrow>E")
  qed
qed

AOT_theorem "routley-star-hype:3": \<open>\<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-)) \<equiv> \<not>\<s> \<Turnstile> ((\<p>)\<^sup>-)\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>\<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-))\<close>
  then AOT_obtain \<q> where q: \<open>\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-)\<close>
    by (metis (no_types, lifting) "con-dis-i-e:2:b" "con-dis-taut:1.\<rightarrow>E" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E"
        "existential:2[const_var]" "instantiation" Hype.instantiation)
  AOT_hence \<open>\<not>\<s> \<Turnstile> ((((\<q>)\<^sup>-))\<^sup>-)\<close>
    by (metis "con-dis-i-e:2:a" "hype:1.\<equiv>\<^sub>d\<^sub>fE.rule=E'" "raa-cor:6"
        AOT_restricted_type.restricted_var_condition Hype.AOT_restricted_type_axioms)
  AOT_thus \<open>\<not>\<s> \<Turnstile> ((\<p>)\<^sup>-)\<close>
    by (meson "con-dis-i-e:2:b" "id_sym.rule=E'" q)
next
  AOT_assume \<open>\<not>\<s> \<Turnstile> ((\<p>)\<^sup>-)\<close>
  AOT_hence \<open>\<not>\<s> \<Turnstile> ((((((\<p>)\<^sup>-))\<^sup>-))\<^sup>-)\<close>
    by (meson "hype:1.\<equiv>\<^sub>d\<^sub>fE.rule=E'" "raa-cor:4" AOT_restricted_type.restricted_var_condition
        Hype.AOT_restricted_type_axioms)
  moreover AOT_have \<open>\<p> = ((((((((\<p>)\<^sup>-))\<^sup>-))\<^sup>-))\<^sup>-)\<close>
    by (meson "\<equiv>\<^sub>d\<^sub>fE" "hype:1" "hype:2.unvarify_p.\<forall>E(1).\<rightarrow>E" "log-prop-prop:2" AOT_restricted_type.\<psi>
        Hype.AOT_restricted_type_axioms id_sym id_trans)
  moreover AOT_have \<open>Hype(((((((((\<p>)\<^sup>-))\<^sup>-))\<^sup>-))))\<close>
    by (simp add: "hype:2.unvarify_p.\<forall>E(1).\<rightarrow>E" "log-prop-prop:2" Hype.restricted_var_condition)
  ultimately AOT_show \<open>\<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-))\<close>
    by (meson "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "existential:1" "log-prop-prop:2")
qed

AOT_theorem "routley-star-hype:4": \<open>\<forall>\<p>(\<s>\<^sup>\<star> \<Turnstile> \<p> \<equiv> \<not>\<s> \<Turnstile> ((\<p>)\<^sup>-))\<close>
proof(rule "Hype.GEN")
  fix \<p>
  AOT_have \<open>\<s>\<^sup>\<star> \<Turnstile> \<p> \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & \<p> = ((\<q>)\<^sup>-))\<close>
    by (metis (lifting) ext "HypeState.res-var:3" "deduction-theorem" "existential:1" "intro-elim:2"
        "log-prop-prop:2" "routley-star-hype:2.unconstrain_\<s>.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<equiv>E(1).\<exists>E'"
        "routley-star-hype:2.unconstrain_\<s>.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<equiv>E(2)" "vdash-properties:10"
        Hype.restricted_var_condition HypeState.restricted_var_condition)
  also AOT_have \<open>\<dots> \<equiv> \<not>\<s> \<Turnstile> ((\<p>)\<^sup>-)\<close>
    using "routley-star-hype:3" by auto
  finally AOT_show \<open>\<s>\<^sup>\<star> \<Turnstile> \<p> \<equiv> \<not>\<s> \<Turnstile> ((\<p>)\<^sup>-)\<close>.
qed

AOT_theorem "routley-star-hype:5": \<open>\<forall>\<p>(\<s>\<^sup>\<star> \<Turnstile> ((\<p>)\<^sup>-) \<equiv> \<not>\<s> \<Turnstile> \<p>)\<close>
proof(rule "Hype.GEN")
  fix \<p>
  AOT_have \<open>\<s>\<^sup>\<star> \<Turnstile> ((\<p>)\<^sup>-) \<equiv> \<exists>\<q>(\<not>\<s> \<Turnstile> \<q> & ((\<p>)\<^sup>-) = ((\<q>)\<^sup>-))\<close>
    using "hype:2.unvarify_p.\<forall>E(1).\<rightarrow>E" "log-prop-prop:2" "routley-star-hype:2" "rule-ui:1"
      "vdash-properties:10" Hype.restricted_var_condition by blast
  also AOT_have \<open>\<dots> \<equiv> \<not>\<s> \<Turnstile> ((((\<p>)\<^sup>-))\<^sup>-)\<close>
    by (metis (lifting) "HypeState.res-var:3" "deduction-theorem" "hype:2.unvarify_p.\<forall>E(1).\<rightarrow>E"
        "intro-elim:2" "intro-elim:3:a" "intro-elim:3:b" "log-prop-prop:2"
        "routley-star-hype:4.unconstrain_\<s>.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<equiv>E(1)"
        "routley-star-hype:4.unconstrain_\<s>.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<equiv>E(2)" Hype.restricted_var_condition
        HypeState.restricted_var_condition calculation)
  also AOT_have \<open>\<dots> \<equiv> \<not>\<s> \<Turnstile> \<p>\<close>
    by (meson "deduction-theorem" "hype:1.\<equiv>\<^sub>d\<^sub>fE.rule=E'" "intro-elim:2" "intro-elim:3:f" "raa-cor:3"
        "reductio-aa:1" Hype.restricted_var_condition)
  finally AOT_show \<open>\<s>\<^sup>\<star> \<Turnstile> ((\<p>)\<^sup>-) \<equiv> \<not>\<s> \<Turnstile> \<p>\<close>.
qed

AOT_theorem "routley-star-hype:6": \<open>GlutOn(\<s>,\<p>) \<rightarrow> GapOn(\<s>\<^sup>\<star>, \<p>)\<close>
  by (metis "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "cqt:2"(1) "deduction-theorem" "hype:4.\<equiv>\<^sub>d\<^sub>fE.&E(1)" "raa-cor:1"
      "routley-star-hype:1[denotes'].2.unconstrain_\<s>.\<forall>E(1).\<rightarrow>E"
      "routley-star-hype:4.unconstrain_\<s>.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<equiv>E(1)"
      "routley-star-hype:5.unconstrain_\<s>.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<equiv>E(1)" "routley-star:4.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(2)"
      "routley-star:4[not].unconstrain_s.unvarify_p.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<equiv>E(1).&E(1)"
      "routley-star:5.\<equiv>\<^sub>d\<^sub>fI" Hype.restricted_var_condition
      HypeState.restricted_var_condition)

AOT_theorem "routley-star-hype:7": \<open>GapOn(\<s>,\<p>) \<rightarrow> GlutOn(\<s>\<^sup>\<star>, \<p>)\<close>
  by (simp add: "con-dis-i-e:1" "cqt:2"(1) "deduction-theorem"
      "hype_state_situation.unconstrain_\<s>.\<forall>E(1).\<rightarrow>E" "routley-star-hype:1[HypeState]"
      "routley-star-hype:1[denotes]" "routley-star-hype:4.unconstrain_\<s>.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<equiv>E(2)"
      "routley-star-hype:5.unconstrain_\<s>.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<equiv>E(2)"
      "routley-star:4[not].unconstrain_s.unvarify_p.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<equiv>E(2)"
      "routley-star:5.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(2)"
      "routley-star:5[not].unconstrain_s.unvarify_p.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<equiv>E(1).&E(1)"
      "thm-relation-negation:7.unvarify_p.\<forall>E(1).rule=E'" Hype.restricted_var_condition
      HypeState.restricted_var_condition)

AOT_theorem "routley-star-hype:8": \<open>(\<not>GapOn(\<s>,\<p>) & \<not>GlutOn(\<s>, \<p>)) \<rightarrow> (\<s>\<^sup>\<star> \<Turnstile> \<p> \<equiv> \<s> \<Turnstile> \<p>)\<close>
  sorry

AOT_theorem "routley-star-hype:9": \<open>\<s>\<^sup>\<star>\<^sup>\<star> = \<s>\<close>
  sorry

AOT_theorem "routley-star-hype:10": \<open>\<not>\<s>!\<s>\<^sup>\<star>\<close>
  by (metis "con-dis-i-e:2:a" "con-dis-i-e:2:b" "cqt:2"(1) "hype:4.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E"
      "incomp-sit:1.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<exists>E'" "reductio-aa:1"
      "routley-star-hype:5.unconstrain_\<s>.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<equiv>E(1)"
      HypeState.\<psi>)

AOT_theorem \<open>\<not>\<s>!\<s>' \<rightarrow> (\<s>' \<oplus> (\<s>\<^sup>\<star>))\<down> & (\<s>' \<oplus> (\<s>\<^sup>\<star>)) = \<s>\<^sup>\<star>\<close>
  sorry

AOT_theorem \<open>\<s>\<unlhd>\<s>' \<rightarrow> \<s>'\<^sup>\<star> \<unlhd> \<s>\<^sup>\<star>\<close>
   sorry

end
