(*<*)
theory AOT_PossibleWorlds
  imports AOT_PLM AOT_BasicLogicalObjects AOT_RestrictedVariables
begin
(*>*)

section\<open>Possible Worlds\<close>

AOT_define Situation :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>Situation'(_')\<close>)
  situations: \<open>Situation(x) \<equiv>\<^sub>d\<^sub>f A!x & \<forall>F (x[F] \<rightarrow> Propositional([F]))\<close>

AOT_theorem "T-sit": \<open>TruthValue(x) \<rightarrow> Situation(x)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>TruthValue(x)\<close>
  AOT_hence \<open>\<exists>p TruthValueOf(x,p)\<close>
    using "T-value"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain p where \<open>TruthValueOf(x,p)\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<theta>: \<open>A!x & \<forall>F (x[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q]))\<close>
    using "tv-p"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_show \<open>Situation(x)\<close>
  proof(rule situations[THEN "\<equiv>\<^sub>d\<^sub>fI"]; safe intro!: "&I" GEN "\<rightarrow>I" \<theta>[THEN "&E"(1)])
    fix F
    AOT_assume \<open>x[F]\<close>
    AOT_hence \<open>\<exists>q((q \<equiv> p) & F = [\<lambda>y q])\<close>
      using \<theta>[THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=F], THEN "\<equiv>E"(1)] by argo
    then AOT_obtain q where \<open>(q \<equiv> p) & F = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
    AOT_hence \<open>\<exists>p F = [\<lambda>y p]\<close> using "&E"(2) "\<exists>I"(2) by metis
    AOT_thus \<open>Propositional([F])\<close>
      by (metis "\<equiv>\<^sub>d\<^sub>fI" "prop-prop1")
  qed
qed

AOT_theorem "possit-sit:1": \<open>Situation(x) \<equiv> \<box>Situation(x)\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>Situation(x)\<close>
  AOT_hence 0: \<open>A!x & \<forall>F (x[F] \<rightarrow> Propositional([F]))\<close>
    using situations[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_have 1: \<open>\<box>(A!x & \<forall>F (x[F] \<rightarrow> Propositional([F])))\<close>
  proof(rule "KBasic:3"[THEN "\<equiv>E"(2)]; rule "&I")
    AOT_show \<open>\<box>A!x\<close> using 0[THEN "&E"(1)] by (metis "oa-facts:2"[THEN "\<rightarrow>E"])
  next
    AOT_have \<open>\<forall>F (x[F] \<rightarrow> Propositional([F])) \<rightarrow> \<box>\<forall>F (x[F] \<rightarrow> Propositional([F]))\<close>
      by (AOT_subst \<open>\<lambda> \<Pi> . \<guillemotleft>Propositional([\<Pi>])\<guillemotright>\<close> \<open>\<lambda> \<Pi> . \<guillemotleft>\<exists>p (\<Pi> = [\<lambda>y p])\<guillemotright>\<close>)
         (auto simp: "prop-prop1" "\<equiv>Df" "enc-prop-nec:2")
    AOT_thus \<open>\<box>\<forall>F (x[F] \<rightarrow> Propositional([F]))\<close>
      using 0[THEN "&E"(2)] "\<rightarrow>E" by blast
  qed
  AOT_show \<open>\<box>Situation(x)\<close>
    by (AOT_subst \<open>\<guillemotleft>Situation(x)\<guillemotright>\<close> \<open>\<guillemotleft>A!x & \<forall>F (x[F] \<rightarrow> Propositional([F]))\<guillemotright>\<close>)
       (auto simp: 1 "\<equiv>Df" situations)
next
  AOT_show \<open>Situation(x)\<close> if \<open>\<box>Situation(x)\<close>
    using "qml:2"[axiom_inst, THEN "\<rightarrow>E", OF that].
qed

AOT_theorem "possit-sit:2": \<open>\<diamond>Situation(x) \<equiv> Situation(x)\<close>
  using "possit-sit:1"
  by (metis "RE\<diamond>" "S5Basic:2" "\<equiv>E"(1) "\<equiv>E"(5) "Commutativity of \<equiv>")

AOT_theorem "possit-sit:3": \<open>\<diamond>Situation(x) \<equiv> \<box>Situation(x)\<close>
  using "possit-sit:1" "possit-sit:2" by (meson "\<equiv>E"(5))

AOT_theorem "possit-sit:4": \<open>\<^bold>\<A>Situation(x) \<equiv> Situation(x)\<close>
  by (meson "Act-Basic:5" "Act-Sub:2" "RA[2]" "\<equiv>E"(1) "\<equiv>E"(6) "possit-sit:2")


AOT_register_rigid_restricted_type
  Situation: \<open>Situation(\<kappa>)\<close>
proof
  AOT_modally_strict {
    fix p
    AOT_obtain x where \<open>TruthValueOf(x,p)\<close> by (metis "instantiation" "p-has-!tv:1")
    AOT_hence \<open>\<exists>p TruthValueOf(x,p)\<close> by (rule "\<exists>I")
    AOT_hence \<open>TruthValue(x)\<close> by (metis "\<equiv>\<^sub>d\<^sub>fI" "T-value")
    AOT_hence \<open>Situation(x)\<close> using "T-sit"[THEN "\<rightarrow>E"] by blast
    AOT_thus \<open>\<exists>x Situation(x)\<close> by (rule "\<exists>I")
  }
next
  AOT_modally_strict {
    AOT_show \<open>Situation(\<kappa>) \<rightarrow> \<kappa>\<down>\<close> for \<kappa>
    proof (rule "\<rightarrow>I")
      AOT_assume \<open>Situation(\<kappa>)\<close>
      AOT_hence \<open>A!\<kappa>\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "&E"(1) situations)
      AOT_thus \<open>\<kappa>\<down>\<close> by (metis "russell-axiom[exe,1].\<psi>_denotes_asm")
    qed
  }
next
  AOT_modally_strict {
    fix \<alpha>
    AOT_show \<open>\<box>(Situation(\<alpha>) \<rightarrow> \<box>Situation(\<alpha>))\<close>
      using "possit-sit:1"[THEN "conventions:3"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(1), THEN RN]
      by blast
  }
qed

AOT_register_variable_names
  Situation: s

AOT_define TruthInSituation :: \<open>\<tau> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> ("(_ \<Turnstile>/ _)" [100, 40] 100)
  "true-in-s": \<open>s \<Turnstile> p \<equiv>\<^sub>d\<^sub>f s\<^bold>\<Sigma>p\<close>

notepad
begin
  (* Verify precedence. *)
  fix x p q
  have \<open>\<guillemotleft>x \<Turnstile> p \<rightarrow> q\<guillemotright> = \<guillemotleft>(x \<Turnstile> p) \<rightarrow> q\<guillemotright>\<close>
    by simp
  have \<open>\<guillemotleft>x \<Turnstile> p & q\<guillemotright> = \<guillemotleft>(x \<Turnstile> p) & q\<guillemotright>\<close>
    by simp
  have \<open>\<guillemotleft>x \<Turnstile> \<not>p\<guillemotright> = \<guillemotleft>x \<Turnstile> (\<not>p)\<guillemotright>\<close>
    by simp
  have \<open>\<guillemotleft>x \<Turnstile> \<box>p\<guillemotright> = \<guillemotleft>x \<Turnstile> (\<box>p)\<guillemotright>\<close>
    by simp
  have \<open>\<guillemotleft>x \<Turnstile> \<^bold>\<A>p\<guillemotright> = \<guillemotleft>x \<Turnstile> (\<^bold>\<A>p)\<guillemotright>\<close>
    by simp
  have \<open>\<guillemotleft>\<box>x \<Turnstile> p\<guillemotright> = \<guillemotleft>\<box>(x \<Turnstile> p)\<guillemotright>\<close>
    by simp
  have \<open>\<guillemotleft>\<not>x \<Turnstile> p\<guillemotright> = \<guillemotleft>\<not>(x \<Turnstile> p)\<guillemotright>\<close>
    by simp
end


AOT_theorem lem1: \<open>Situation(x) \<rightarrow> (x \<Turnstile> p \<equiv> x[\<lambda>y p])\<close>
proof (rule "\<rightarrow>I"; rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>Situation(x)\<close>
  AOT_assume \<open>x \<Turnstile> p\<close>
  AOT_hence \<open>x\<^bold>\<Sigma>p\<close>
    using "true-in-s"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_thus \<open>x[\<lambda>y p]\<close> using "prop-enc"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
next
  AOT_assume 1: \<open>Situation(x)\<close>
  AOT_assume \<open>x[\<lambda>y p]\<close>
  AOT_hence \<open>x\<^bold>\<Sigma>p\<close>
    using "prop-enc"[THEN "\<equiv>\<^sub>d\<^sub>fI", OF "&I", OF "cqt:2[const_var]"[axiom_inst]] by blast
  AOT_thus \<open>x \<Turnstile> p\<close>
    using "true-in-s"[THEN "\<equiv>\<^sub>d\<^sub>fI"] 1 "&I" by blast
qed

AOT_theorem "lem2:1": \<open>s \<Turnstile> p \<equiv> \<box>s \<Turnstile> p\<close>
proof -
  AOT_have sit: \<open>Situation(s)\<close>
    by (simp add: Situation.\<psi>)
  AOT_have \<open>s \<Turnstile> p \<equiv> s[\<lambda>y p]\<close>
    using lem1[THEN "\<rightarrow>E", OF sit] by blast
  also AOT_have \<open>\<dots> \<equiv> \<box>s[\<lambda>y p]\<close>
    by (rule "en-eq:2[1]"[unvarify F]) "cqt:2[lambda]"
  also AOT_have \<open>\<dots> \<equiv> \<box>s \<Turnstile> p\<close>
    using lem1[THEN RM, THEN "\<rightarrow>E", OF "possit-sit:1"[THEN "\<equiv>E"(1), OF sit]]
    by (metis "KBasic:6" "\<equiv>E"(2) "Commutativity of \<equiv>" "vdash-properties:10")
  finally show ?thesis.
qed

AOT_theorem "lem2:2": \<open>\<diamond>s \<Turnstile> p \<equiv> s \<Turnstile> p\<close>
proof -
  AOT_have \<open>\<box>(s \<Turnstile> p \<rightarrow> \<box>s \<Turnstile> p)\<close>
    using "possit-sit:1"[THEN "\<equiv>E"(1), OF Situation.\<psi>] "lem2:1"[THEN "conventions:3"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(1)]] RM[OF "\<rightarrow>I", THEN "\<rightarrow>E"] by blast
  thus ?thesis by (metis "B\<diamond>" "S5Basic:13" "T\<diamond>" "\<equiv>I" "\<equiv>E"(1) "vdash-properties:10")
qed

AOT_theorem "lem2:3": \<open>\<diamond>s \<Turnstile> p \<equiv> \<box>s \<Turnstile> p\<close>
  using "lem2:1" "lem2:2" by (metis "\<equiv>E"(5))

AOT_theorem "lem2:4": \<open>\<^bold>\<A>(s \<Turnstile> p) \<equiv> s \<Turnstile> p\<close>
proof -
  AOT_have \<open>\<box>(s \<Turnstile> p \<rightarrow> \<box>s \<Turnstile> p)\<close>
    using "possit-sit:1"[THEN "\<equiv>E"(1), OF Situation.\<psi>]
      "lem2:1"[THEN "conventions:3"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(1)]] RM[OF "\<rightarrow>I", THEN "\<rightarrow>E"] by blast
  thus ?thesis
    using "sc-eq-fur:2"[THEN "\<rightarrow>E"] by blast
qed

AOT_theorem "lem2:5": \<open>\<not>s \<Turnstile> p \<equiv> \<box>\<not>s \<Turnstile> p\<close>
  by (metis "KBasic2:1" "contraposition:1[2]" "deduction-theorem" "\<equiv>I" "\<equiv>E"(3) "\<equiv>E"(4) "lem2:2")

AOT_theorem "sit-identity": \<open>s = s' \<equiv> \<forall>p(s \<Turnstile> p \<equiv> s' \<Turnstile> p)\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>s = s'\<close>
  moreover AOT_have \<open>\<forall>p(s \<Turnstile> p \<equiv> s \<Turnstile> p)\<close>
    by (simp add: "oth-class-taut:3:a" "universal-cor")
  ultimately AOT_show \<open>\<forall>p(s \<Turnstile> p \<equiv> s' \<Turnstile> p)\<close>
    using "rule=E" by fast
next
  AOT_assume a: \<open>\<forall>p (s \<Turnstile> p \<equiv> s' \<Turnstile> p)\<close>
  AOT_show \<open>s = s'\<close>
  proof(safe intro!: "ab-obey:1"[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "&I" GEN "\<equiv>I" "\<rightarrow>I")
    AOT_show \<open>A!s\<close> using Situation.\<psi> "\<equiv>\<^sub>d\<^sub>fE" "&E"(1) situations by blast
  next
    AOT_show \<open>A!s'\<close> using Situation.\<psi> "\<equiv>\<^sub>d\<^sub>fE" "&E"(1) situations by blast
  next
    fix F
    AOT_assume 0: \<open>s[F]\<close>
    AOT_hence \<open>\<exists>p (F = [\<lambda>y p])\<close>
      using Situation.\<psi>[THEN situations[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=F], THEN "\<rightarrow>E"]
            "prop-prop1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
    then AOT_obtain p where F_def: \<open>F = [\<lambda>y p]\<close>
      using "\<exists>E" by metis
    AOT_hence \<open>s[\<lambda>y p]\<close> using 0 "rule=E" by blast
    AOT_hence \<open>s \<Turnstile> p\<close> using lem1[THEN "\<rightarrow>E", OF Situation.\<psi>, THEN "\<equiv>E"(2)] by blast
    AOT_hence \<open>s' \<Turnstile> p\<close> using a[THEN "\<forall>E"(2)[where \<beta>=p], THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>s'[\<lambda>y p]\<close> using lem1[THEN "\<rightarrow>E", OF Situation.\<psi>, THEN "\<equiv>E"(1)] by blast
    AOT_thus \<open>s'[F]\<close> using F_def[symmetric] "rule=E" by blast
  next
    fix F
    AOT_assume 0: \<open>s'[F]\<close>
    AOT_hence \<open>\<exists>p (F = [\<lambda>y p])\<close>
      using Situation.\<psi>[THEN situations[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=F], THEN "\<rightarrow>E"]
            "prop-prop1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
    then AOT_obtain p where F_def: \<open>F = [\<lambda>y p]\<close>
      using "\<exists>E" by metis
    AOT_hence \<open>s'[\<lambda>y p]\<close> using 0 "rule=E" by blast
    AOT_hence \<open>s' \<Turnstile> p\<close> using lem1[THEN "\<rightarrow>E", OF Situation.\<psi>, THEN "\<equiv>E"(2)] by blast
    AOT_hence \<open>s \<Turnstile> p\<close> using a[THEN "\<forall>E"(2)[where \<beta>=p], THEN "\<equiv>E"(2)] by blast
    AOT_hence \<open>s[\<lambda>y p]\<close> using lem1[THEN "\<rightarrow>E", OF Situation.\<psi>, THEN "\<equiv>E"(1)] by blast
    AOT_thus \<open>s[F]\<close> using F_def[symmetric] "rule=E" by blast
  qed
qed

AOT_define PartOfSituation :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl \<open>\<unlhd>\<close> 80)
  "sit-part-whole": \<open>s \<unlhd> s' \<equiv>\<^sub>d\<^sub>f \<forall>p (s \<Turnstile> p \<rightarrow> s' \<Turnstile> p)\<close>

AOT_theorem "part:1": \<open>s \<unlhd> s\<close>
  by (rule "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
     (safe intro!: "&I" Situation.\<psi> GEN "\<rightarrow>I")

AOT_theorem "part:2": \<open>s \<unlhd> s' & s \<noteq> s' \<rightarrow> \<not>(s' \<unlhd> s)\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2); rule "raa-cor:2")
  AOT_assume 0: \<open>s \<unlhd> s'\<close>
  AOT_hence a: \<open>s \<Turnstile> p \<rightarrow> s' \<Turnstile> p\<close> for p using "\<forall>E"(2) "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_assume \<open>s' \<unlhd> s\<close>
  AOT_hence b: \<open>s' \<Turnstile> p \<rightarrow> s \<Turnstile> p\<close> for p using "\<forall>E"(2) "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_have \<open>\<forall>p (s \<Turnstile> p \<equiv> s' \<Turnstile> p)\<close> using a b by (simp add: "\<equiv>I" "universal-cor")
  AOT_hence 1: \<open>s = s'\<close> using "sit-identity"[THEN "\<equiv>E"(2)] by metis
  AOT_assume \<open>s \<noteq> s'\<close>
  AOT_hence \<open>\<not>(s = s')\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "=-infix")
  AOT_thus \<open>s = s' & \<not>(s = s')\<close> using 1 "&I" by blast
qed

AOT_theorem "part:3": \<open>s \<unlhd> s' & s' \<unlhd> s'' \<rightarrow> s \<unlhd> s''\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2); safe intro!: "&I" GEN "\<rightarrow>I" "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fI"] Situation.\<psi>)
  fix p
  AOT_assume \<open>s \<Turnstile> p\<close>
  moreover AOT_assume \<open>s \<unlhd> s'\<close>
  ultimately AOT_have \<open>s' \<Turnstile> p\<close>
    using "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=p], THEN "\<rightarrow>E"] by blast
  moreover AOT_assume \<open>s' \<unlhd> s''\<close>
  ultimately AOT_show \<open>s'' \<Turnstile> p\<close>
    using "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=p], THEN "\<rightarrow>E"] by blast
qed

AOT_theorem "sit-identity2:1": \<open>s = s' \<equiv> s \<unlhd> s' & s' \<unlhd> s\<close>
proof (safe intro!: "\<equiv>I" "&I" "\<rightarrow>I")
  AOT_show \<open>s \<unlhd> s'\<close> if \<open>s = s'\<close>
    using "rule=E" "part:1" that by blast
next
  AOT_show \<open>s' \<unlhd> s\<close> if \<open>s = s'\<close>
    using "rule=E" "part:1" that[symmetric] by blast
next
  AOT_assume \<open>s \<unlhd> s' & s' \<unlhd> s\<close>
  AOT_thus \<open>s = s'\<close> using "part:2"[THEN "\<rightarrow>E", OF "&I"]
    by (metis "\<equiv>\<^sub>d\<^sub>fI" "&E"(1) "&E"(2) "=-infix" "raa-cor:3")
qed

AOT_theorem "sit-identity2:2": \<open>s = s' \<equiv> \<forall>s'' (s'' \<unlhd> s \<equiv> s'' \<unlhd> s')\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I" Situation.GEN "sit-identity"[THEN "\<equiv>E"(2)] GEN[where 'a=\<o>])
  AOT_show \<open>s'' \<unlhd> s'\<close> if \<open>s'' \<unlhd> s\<close> and \<open>s = s'\<close> for s''
    using "rule=E" that by blast
next
  AOT_show \<open>s'' \<unlhd> s\<close> if \<open>s'' \<unlhd> s'\<close> and \<open>s = s'\<close> for s''
    using "rule=E" id_sym that by blast
next
  AOT_show \<open>s' \<Turnstile> p\<close> if \<open>s \<Turnstile> p\<close> and \<open>\<forall>s'' (s'' \<unlhd> s \<equiv> s'' \<unlhd> s')\<close> for p
    using "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), OF that(2)[THEN "Situation.\<forall>E", THEN "\<equiv>E"(1), OF "part:1"], THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF that(1)].
next
  AOT_show \<open>s \<Turnstile> p\<close> if \<open>s' \<Turnstile> p\<close> and \<open>\<forall>s'' (s'' \<unlhd> s \<equiv> s'' \<unlhd> s')\<close> for p
    using "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), OF that(2)[THEN "Situation.\<forall>E",
          THEN "\<equiv>E"(2), OF "part:1"], THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF that(1)].
qed

AOT_define Persistent :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>Persistent'(_')\<close>)
  persistent: \<open>Persistent(p) \<equiv>\<^sub>d\<^sub>f \<forall>s (s \<Turnstile> p \<rightarrow> \<forall>s' (s \<unlhd> s' \<rightarrow> s' \<Turnstile> p))\<close>

AOT_theorem "pers-prop": \<open>\<forall>p Persistent(p)\<close>
  by (safe intro!: GEN[where 'a=\<o>] Situation.GEN persistent[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<rightarrow>I")
     (simp add: "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"])

AOT_define NullSituation :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>NullSituation'(_')\<close>)
  "df-null-trivial:1": \<open>NullSituation(s) \<equiv>\<^sub>d\<^sub>f \<not>\<exists>p s \<Turnstile> p\<close>

AOT_define TrivialSituation :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>TrivialSituation'(_')\<close>)
  "df-null-trivial:2": \<open>TrivialSituation(s) \<equiv>\<^sub>d\<^sub>f \<forall>p s \<Turnstile> p\<close>

AOT_theorem "thm-null-trivial:1": \<open>\<exists>!x NullSituation(x)\<close>
proof (AOT_subst \<open>\<lambda> \<kappa> . \<guillemotleft>NullSituation(\<kappa>)\<guillemotright>\<close> \<open>\<lambda> \<kappa> . \<guillemotleft>A!\<kappa> & \<forall>F (\<kappa>[F] \<equiv> F \<noteq> F)\<guillemotright>\<close>)
  AOT_modally_strict {
    AOT_show \<open>NullSituation(x) \<equiv> A!x & \<forall>F (x[F] \<equiv> F \<noteq> F)\<close> for x
    proof (safe intro!: "\<equiv>I" "\<rightarrow>I" "df-null-trivial:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] dest!: "df-null-trivial:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"])
      AOT_assume 0: \<open>Situation(x) & \<not>\<exists>p x \<Turnstile> p\<close>
      AOT_have 1: \<open>A!x\<close> using 0[THEN "&E"(1), THEN situations[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(1)].
      AOT_have 2: \<open>x[F] \<rightarrow> \<exists>p F = [\<lambda>y p]\<close> for F
        using 0[THEN "&E"(1), THEN situations[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2), THEN "\<forall>E"(2)]
        by (metis "\<equiv>\<^sub>d\<^sub>fE" "deduction-theorem" "prop-prop1" "\<rightarrow>E")
      AOT_show \<open>A!x & \<forall>F (x[F] \<equiv> F \<noteq> F)\<close>
      proof (safe intro!: "&I" 1 GEN "\<equiv>I" "\<rightarrow>I")
        fix F
        AOT_assume \<open>x[F]\<close>
        moreover AOT_obtain p where \<open>F = [\<lambda>y p]\<close>
          using calculation 2[THEN "\<rightarrow>E"] "\<exists>E"[rotated] by blast
        ultimately AOT_have \<open>x[\<lambda>y p]\<close> by (metis "rule=E")
        AOT_hence \<open>x \<Turnstile> p\<close> using lem1[THEN "\<rightarrow>E", OF 0[THEN "&E"(1)], THEN "\<equiv>E"(2)] by blast
        AOT_hence \<open>\<exists>p (x \<Turnstile> p)\<close> by (rule "\<exists>I")
        AOT_thus \<open>F \<noteq> F\<close> using 0[THEN "&E"(2)] "raa-cor:1" "&I" by blast
      next
        fix F :: \<open><\<kappa>> AOT_var\<close>
        AOT_assume \<open>F \<noteq> F\<close>
        AOT_hence \<open>\<not>(F = F)\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "=-infix")
        moreover AOT_have \<open>F = F\<close>
          by (simp add: "id-eq:1")
        ultimately AOT_show \<open>x[F]\<close> using "&I" "raa-cor:1" by blast
      qed
    next
      AOT_assume 0: \<open>A!x & \<forall>F (x[F] \<equiv> F \<noteq> F)\<close>
      AOT_hence \<open>x[F] \<equiv> F \<noteq> F\<close> for F using "\<forall>E" "&E" by blast
      AOT_hence 1: \<open>\<not>x[F]\<close> for F
        using "\<equiv>\<^sub>d\<^sub>fE" "id-eq:1" "=-infix" "reductio-aa:1" "\<equiv>E"(1) by blast
      AOT_show \<open>Situation(x) & \<not>\<exists>p x \<Turnstile> p\<close>
      proof (safe intro!: "&I" situations[THEN "\<equiv>\<^sub>d\<^sub>fI"] 0[THEN "&E"(1)] GEN "\<rightarrow>I")
        AOT_show \<open>Propositional([F])\<close> if \<open>x[F]\<close> for F using that 1 "&I" "raa-cor:1" by fast
      next
        AOT_show \<open>\<not>\<exists>p x \<Turnstile> p\<close>
        proof(rule "raa-cor:2")
          AOT_assume \<open>\<exists>p x \<Turnstile> p\<close>
          then AOT_obtain p where \<open>x \<Turnstile> p\<close> using "\<exists>E"[rotated] by blast
          AOT_hence \<open>x[\<lambda>y p]\<close>
            using "\<equiv>\<^sub>d\<^sub>fE" "&E"(1) "\<equiv>E"(1) lem1 "modus-tollens:1" "raa-cor:3" "true-in-s" by fast
          moreover AOT_have \<open>\<not>x[\<lambda>y p]\<close>
            by (rule 1[unvarify F]) "cqt:2[lambda]"
          ultimately AOT_show \<open>p & \<not>p\<close> for p using "&I" "raa-cor:1" by blast
        qed
      qed
    qed
  }
next
  AOT_show \<open>\<exists>!x ([A!]x & \<forall>F (x[F] \<equiv> F \<noteq> F))\<close>
    by (simp add: "A-objects!")
qed


AOT_theorem "thm-null-trivial:2": \<open>\<exists>!x TrivialSituation(x)\<close>
proof (AOT_subst \<open>\<lambda> \<kappa> . \<guillemotleft>TrivialSituation(\<kappa>)\<guillemotright>\<close> \<open>\<lambda> \<kappa> . \<guillemotleft>A!\<kappa> & \<forall>F (\<kappa>[F] \<equiv> \<exists>p F = [\<lambda>y p])\<guillemotright>\<close>)
  AOT_modally_strict {
    AOT_show \<open>TrivialSituation(x) \<equiv> A!x & \<forall>F (x[F] \<equiv> \<exists>p F = [\<lambda>y p])\<close> for x
    proof (safe intro!: "\<equiv>I" "\<rightarrow>I" "df-null-trivial:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] dest!: "df-null-trivial:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"])
      AOT_assume 0: \<open>Situation(x) & \<forall>p x \<Turnstile> p\<close>
      AOT_have 1: \<open>A!x\<close> using 0[THEN "&E"(1), THEN situations[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(1)].
      AOT_have 2: \<open>x[F] \<rightarrow> \<exists>p F = [\<lambda>y p]\<close> for F
        using 0[THEN "&E"(1), THEN situations[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2), THEN "\<forall>E"(2)]
        by (metis "\<equiv>\<^sub>d\<^sub>fE" "deduction-theorem" "prop-prop1" "\<rightarrow>E")
      AOT_show \<open>A!x & \<forall>F (x[F] \<equiv> \<exists>p F = [\<lambda>y p])\<close>
      proof (safe intro!: "&I" 1 GEN "\<equiv>I" "\<rightarrow>I" 2)
        fix F
        AOT_assume \<open>\<exists>p F = [\<lambda>y p]\<close>
        then AOT_obtain p where \<open>F = [\<lambda>y p]\<close> using "\<exists>E"[rotated] by blast
        moreover AOT_have \<open>x \<Turnstile> p\<close> using 0[THEN "&E"(2)] "\<forall>E" by blast
        ultimately AOT_show \<open>x[F]\<close>
          by (metis 0 "rule=E" "&E"(1) id_sym "\<equiv>E"(2) lem1 "Commutativity of \<equiv>" "\<rightarrow>E")
      qed
    next
      AOT_assume 0: \<open>A!x & \<forall>F (x[F] \<equiv> \<exists>p F = [\<lambda>y p])\<close>
      AOT_hence 1: \<open>x[F] \<equiv> \<exists>p F = [\<lambda>y p]\<close> for F using "\<forall>E" "&E" by blast
      AOT_have 2: \<open>Situation(x)\<close>
      proof (safe intro!: "&I" situations[THEN "\<equiv>\<^sub>d\<^sub>fI"] 0[THEN "&E"(1)] GEN "\<rightarrow>I")
        AOT_show \<open>Propositional([F])\<close> if \<open>x[F]\<close> for F
          using 1[THEN "\<equiv>E"(1), OF that]
          by (metis "\<equiv>\<^sub>d\<^sub>fI" "prop-prop1")
      qed
      AOT_show \<open>Situation(x) & \<forall>p (x \<Turnstile> p)\<close>
      proof (safe intro!: "&I" 2 0[THEN "&E"(1)] GEN "\<rightarrow>I")
        AOT_have \<open>x[\<lambda>y p] \<equiv> \<exists>q [\<lambda>y p] = [\<lambda>y q]\<close> for p
          by (rule 1[unvarify F, where \<tau>="\<guillemotleft>[\<lambda>y p]\<guillemotright>"]) "cqt:2[lambda]"
        moreover AOT_have \<open>\<exists>q [\<lambda>y p] = [\<lambda>y q]\<close> for p
          by (rule "\<exists>I"(2)[where \<beta>=p])
             (simp add: "rule=I:1" "prop-prop2:2")
        ultimately AOT_have \<open>x[\<lambda>y p]\<close> for p by (metis "\<equiv>E"(2))
        AOT_thus \<open>x \<Turnstile> p\<close> for p
          by (metis "2" "\<equiv>E"(2) lem1 "\<rightarrow>E")
      qed
    qed
  }
next
  AOT_show \<open>\<exists>!x ([A!]x & \<forall>F (x[F] \<equiv> \<exists>p F = [\<lambda>y p]))\<close>
    by (simp add: "A-objects!")
qed

AOT_theorem "thm-null-trivial:3": \<open>\<^bold>\<iota>x NullSituation(x)\<down>\<close>
  by (meson "A-Exists:2" "RA[2]" "\<equiv>E"(2) "thm-null-trivial:1")

AOT_theorem "thm-null-trivial:4": \<open>\<^bold>\<iota>x TrivialSituation(x)\<down>\<close>
  using "A-Exists:2" "RA[2]" "\<equiv>E"(2) "thm-null-trivial:2" by blast

AOT_define TheNullSituation :: \<open>\<kappa>\<^sub>s\<close> (\<open>\<^bold>s\<^sub>\<emptyset>\<close>)
  "df-the-null-sit:1": \<open>\<^bold>s\<^sub>\<emptyset> =\<^sub>d\<^sub>f \<^bold>\<iota>x NullSituation(x)\<close>

AOT_define TheTrivialSituation :: \<open>\<kappa>\<^sub>s\<close> (\<open>\<^bold>s\<^sub>V\<close>)
  "df-the-null-sit:2": \<open>\<^bold>s\<^sub>V =\<^sub>d\<^sub>f \<^bold>\<iota>x TrivialSituation(x)\<close>

AOT_theorem "null-triv-sc:1": \<open>NullSituation(x) \<rightarrow> \<box>NullSituation(x)\<close>
proof(safe intro!: "\<rightarrow>I" dest!: "df-null-trivial:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"]; frule "&E"(1); drule "&E"(2))
  AOT_assume 1: \<open>\<not>\<exists>p (x \<Turnstile> p)\<close>
  AOT_assume 0: \<open>Situation(x)\<close>
  AOT_hence \<open>\<box>Situation(x)\<close> by (metis "\<equiv>E"(1) "possit-sit:1")
  moreover AOT_have \<open>\<box>\<not>\<exists>p (x \<Turnstile> p)\<close>
  proof(rule "raa-cor:1")
    AOT_assume \<open>\<not>\<box>\<not>\<exists>p (x \<Turnstile> p)\<close>
    AOT_hence \<open>\<diamond>\<exists>p (x \<Turnstile> p)\<close>
      by (metis "\<equiv>\<^sub>d\<^sub>fI" "conventions:5")
    AOT_hence \<open>\<exists>p \<diamond>(x \<Turnstile> p)\<close> by (metis "BF\<diamond>" "\<rightarrow>E")
    then AOT_obtain p where \<open>\<diamond>(x \<Turnstile> p)\<close> using "\<exists>E"[rotated] by blast
    AOT_hence \<open>x \<Turnstile> p\<close>
      by (metis "\<equiv>E"(1) "lem2:2"[unconstrain s, THEN "\<rightarrow>E", OF 0])
    AOT_hence \<open>\<exists>p x \<Turnstile> p\<close> using "\<exists>I" by fast
    AOT_thus \<open>\<exists>p x \<Turnstile> p & \<not>\<exists>p x \<Turnstile> p\<close> using 1 "&I" by blast
  qed
  ultimately AOT_have 2: \<open>\<box>(Situation(x) & \<not>\<exists>p x \<Turnstile> p)\<close>
    by (metis "KBasic:3" "&I" "\<equiv>E"(2))
  AOT_show \<open>\<box>NullSituation(x)\<close>
    by (AOT_subst \<open>\<guillemotleft>NullSituation(x)\<guillemotright>\<close> \<open>\<guillemotleft>Situation(x) & \<not>\<exists>p x \<Turnstile> p\<guillemotright>\<close>)
       (auto simp: "df-null-trivial:1" "\<equiv>Df" 2)
qed


AOT_theorem "null-triv-sc:2": \<open>TrivialSituation(x) \<rightarrow> \<box>TrivialSituation(x)\<close>
proof(safe intro!: "\<rightarrow>I" dest!: "df-null-trivial:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"]; frule "&E"(1); drule "&E"(2))
  AOT_assume 0: \<open>Situation(x)\<close>
  AOT_hence 1: \<open>\<box>Situation(x)\<close> by (metis "\<equiv>E"(1) "possit-sit:1")
  AOT_assume \<open>\<forall>p x \<Turnstile> p\<close>
  AOT_hence \<open>x \<Turnstile> p\<close> for p using "\<forall>E" by blast
  AOT_hence \<open>\<box>x \<Turnstile> p\<close> for p using  0 "\<equiv>E"(1) "lem2:1"[unconstrain s, THEN "\<rightarrow>E"] by blast
  AOT_hence \<open>\<forall>p \<box>x \<Turnstile> p\<close> by (rule GEN)
  AOT_hence \<open>\<box>\<forall>p x \<Turnstile> p\<close> by (rule BF[THEN "\<rightarrow>E"])
  AOT_hence 2: \<open>\<box>(Situation(x) & \<forall>p x \<Turnstile> p)\<close>
    using 1 by (metis "KBasic:3" "&I" "\<equiv>E"(2))
  AOT_show \<open>\<box>TrivialSituation(x)\<close>
    by (AOT_subst \<open>\<guillemotleft>TrivialSituation(x)\<guillemotright>\<close> \<open>\<guillemotleft>Situation(x) & \<forall>p x \<Turnstile> p\<guillemotright>\<close>)
       (auto simp: "df-null-trivial:2" "\<equiv>Df" 2)
qed

AOT_theorem "null-triv-sc:3": \<open>NullSituation(\<^bold>s\<^sub>\<emptyset>)\<close>
  by (safe intro!: "df-the-null-sit:1"[THEN "=\<^sub>d\<^sub>fI"(2)] "thm-null-trivial:3"
                   "rule=I:1"[OF "thm-null-trivial:3"]
                   "!box-desc:2"[THEN "\<rightarrow>E", THEN "\<rightarrow>E", rotated, OF "thm-null-trivial:1",
                                 OF "\<forall>I", OF "null-triv-sc:1", THEN "\<forall>E"(1), THEN "\<rightarrow>E"])

AOT_theorem "null-triv-sc:4": \<open>TrivialSituation(\<^bold>s\<^sub>V)\<close>
  by (safe intro!: "df-the-null-sit:2"[THEN "=\<^sub>d\<^sub>fI"(2)] "thm-null-trivial:4"
                   "rule=I:1"[OF "thm-null-trivial:4"]
                   "!box-desc:2"[THEN "\<rightarrow>E", THEN "\<rightarrow>E", rotated, OF "thm-null-trivial:2",
                                 OF "\<forall>I", OF "null-triv-sc:2", THEN "\<forall>E"(1), THEN "\<rightarrow>E"])

AOT_theorem "null-triv-facts:1": \<open>NullSituation(x) \<equiv> Null(x)\<close>
proof (safe intro!: "\<equiv>I" "\<rightarrow>I" "df-null-uni:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "df-null-trivial:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"]
            dest!: "df-null-uni:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "df-null-trivial:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"])
  AOT_assume 0: \<open>Situation(x) & \<not>\<exists>p x \<Turnstile> p\<close>
  AOT_have 1: \<open>x[F] \<rightarrow> \<exists>p F = [\<lambda>y p]\<close> for F
    using 0[THEN "&E"(1), THEN situations[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2), THEN "\<forall>E"(2)]
    by (metis "\<equiv>\<^sub>d\<^sub>fE" "deduction-theorem" "prop-prop1" "\<rightarrow>E")
  AOT_show \<open>A!x & \<not>\<exists>F x[F]\<close>
  proof (safe intro!: "&I" 0[THEN "&E"(1), THEN situations[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(1)]; rule "raa-cor:2")
    AOT_assume \<open>\<exists>F x[F]\<close>
    then AOT_obtain F where F_prop: \<open>x[F]\<close> using "\<exists>E"[rotated] by blast
    AOT_hence \<open>\<exists>p F = [\<lambda>y p]\<close> using 1[THEN "\<rightarrow>E"] by blast
    then AOT_obtain p where \<open>F = [\<lambda>y p]\<close> using "\<exists>E"[rotated] by blast
    AOT_hence \<open>x[\<lambda>y p]\<close> by (metis "rule=E" F_prop)
    AOT_hence \<open>x \<Turnstile> p\<close> using lem1[THEN "\<rightarrow>E", OF 0[THEN "&E"(1)], THEN "\<equiv>E"(2)] by blast
    AOT_hence \<open>\<exists>p x \<Turnstile> p\<close> by (rule "\<exists>I")
    AOT_thus \<open>\<exists>p x \<Turnstile> p & \<not>\<exists>p x \<Turnstile> p\<close> using 0[THEN "&E"(2)] "&I" by blast
  qed
next
  AOT_assume 0: \<open>A!x & \<not>\<exists>F x[F]\<close>
  AOT_have \<open>Situation(x)\<close>
    apply (rule situations[THEN "\<equiv>\<^sub>d\<^sub>fI", OF "&I", OF 0[THEN "&E"(1)]]; rule GEN)
    using 0[THEN "&E"(2)] by (metis "deduction-theorem" "existential:2[const_var]" "raa-cor:3") 
  moreover AOT_have \<open>\<not>\<exists>p x \<Turnstile> p\<close>
  proof (rule "raa-cor:2")
    AOT_assume \<open>\<exists>p x \<Turnstile> p\<close>
    then AOT_obtain p where \<open>x \<Turnstile> p\<close> by (metis "instantiation")
    AOT_hence \<open>x[\<lambda>y p]\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "&E"(2) "prop-enc" "true-in-s")
    AOT_hence \<open>\<exists>F x[F]\<close> by (rule "\<exists>I") "cqt:2[lambda]"
    AOT_thus \<open>\<exists>F x[F] & \<not>\<exists>F x[F]\<close> using 0[THEN "&E"(2)] "&I" by blast
  qed
  ultimately AOT_show \<open>Situation(x) & \<not>\<exists>p x \<Turnstile> p\<close> using "&I" by blast
qed

AOT_theorem "null-triv-facts:2": \<open>\<^bold>s\<^sub>\<emptyset> = a\<^sub>\<emptyset>\<close>
  apply (rule "=\<^sub>d\<^sub>fI"(2)[OF "df-the-null-sit:1"])
   apply (fact "thm-null-trivial:3")
  apply (rule "=\<^sub>d\<^sub>fI"(2)[OF "df-null-uni-terms:1"])
   apply (fact "null-uni-uniq:3")
  apply (rule "equiv-desc-eq:3"[THEN "\<rightarrow>E"])
  apply (rule "&I")
   apply (fact "thm-null-trivial:3")
  by (rule RN; rule GEN; rule "null-triv-facts:1")

AOT_theorem "null-triv-facts:3": \<open>\<^bold>s\<^sub>V \<noteq> a\<^sub>V\<close>
proof(rule "=-infix"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_have \<open>Universal(a\<^sub>V)\<close>
    by (simp add: "null-uni-facts:4")
  AOT_hence 0: \<open>a\<^sub>V[A!]\<close>
    using "df-null-uni:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" "\<forall>E"(1)
    by (metis "cqt:5:a" "vdash-properties:10" "vdash-properties:1[2]")
  moreover AOT_have 1: \<open>\<not>\<^bold>s\<^sub>V[A!]\<close>
  proof(rule "raa-cor:2")
    AOT_have \<open>Situation(\<^bold>s\<^sub>V)\<close>
      using "\<equiv>\<^sub>d\<^sub>fE" "&E"(1) "df-null-trivial:2" "null-triv-sc:4" by blast
    AOT_hence \<open>\<forall>F (\<^bold>s\<^sub>V[F] \<rightarrow> Propositional([F]))\<close>
      by (metis "\<equiv>\<^sub>d\<^sub>fE" "&E"(2) situations)
    moreover AOT_assume \<open>\<^bold>s\<^sub>V[A!]\<close>
    ultimately AOT_have \<open>Propositional(A!)\<close> using "\<forall>E"(1)[rotated, OF "oa-exist:2"] "\<rightarrow>E" by blast
    AOT_thus \<open>Propositional(A!) & \<not>Propositional(A!)\<close> using "prop-in-f:4:d" "&I" by blast
  qed
  AOT_show \<open>\<not>(\<^bold>s\<^sub>V = a\<^sub>V)\<close>
  proof (rule "raa-cor:2")
    AOT_assume \<open>\<^bold>s\<^sub>V = a\<^sub>V\<close>
    AOT_hence \<open>\<^bold>s\<^sub>V[A!]\<close> using 0 "rule=E" id_sym by fast
    AOT_thus \<open>\<^bold>s\<^sub>V[A!] & \<not>\<^bold>s\<^sub>V[A!]\<close> using 1 "&I" by blast
  qed
qed

definition ConditionOnPropositionalProperties :: \<open>(<\<kappa>> \<Rightarrow> \<o>) \<Rightarrow> bool\<close> where
  "cond-prop": \<open>ConditionOnPropositionalProperties \<equiv> \<lambda> \<phi> . \<forall> v . [v \<Turnstile> \<forall>F (\<phi>{F} \<rightarrow> Propositional([F]))]\<close>

syntax ConditionOnPropositionalProperties :: \<open>id_position \<Rightarrow> AOT_prop\<close> ("CONDITION'_ON'_PROPOSITIONAL'_PROPERTIES'(_')")

AOT_theorem "cond-prop[E]":
  assumes \<open>CONDITION_ON_PROPOSITIONAL_PROPERTIES(\<phi>)\<close>
  shows \<open>\<forall>F (\<phi>{F} \<rightarrow> Propositional([F]))\<close>
  using assms[unfolded "cond-prop"] by auto

AOT_theorem "cond-prop[I]":
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<forall>F (\<phi>{F} \<rightarrow> Propositional([F]))\<close>
  shows \<open>CONDITION_ON_PROPOSITIONAL_PROPERTIES(\<phi>)\<close>
  using assms "cond-prop" by metis

AOT_theorem "pre-comp-sit":
  assumes \<open>CONDITION_ON_PROPOSITIONAL_PROPERTIES(\<phi>)\<close>
  shows \<open>(Situation(x) & \<forall>F (x[F] \<equiv> \<phi>{F})) \<equiv> (A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>Situation(x) & \<forall>F (x[F] \<equiv> \<phi>{F})\<close>
  AOT_thus \<open>A!x & \<forall>F (x[F] \<equiv> \<phi>{F})\<close>
    using "&E" situations[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&I" by blast
next
  AOT_assume 0: \<open>A!x & \<forall>F (x[F] \<equiv> \<phi>{F})\<close>
  AOT_show \<open>Situation(x) & \<forall>F (x[F] \<equiv> \<phi>{F})\<close>
  proof (safe intro!: situations[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I")
    AOT_show \<open>A!x\<close> using 0[THEN "&E"(1)].
  next
    AOT_show \<open>\<forall>F (x[F] \<rightarrow> Propositional([F]))\<close>
    proof(rule GEN; rule "\<rightarrow>I")
      fix F
      AOT_assume \<open>x[F]\<close>
      AOT_hence \<open>\<phi>{F}\<close> using 0[THEN "&E"(2)] "\<forall>E" "\<equiv>E" by blast
      AOT_thus \<open>Propositional([F])\<close> using "cond-prop[E]"[OF assms] "\<forall>E" "\<rightarrow>E" by blast
    qed
  next
    AOT_show \<open>\<forall>F (x[F] \<equiv> \<phi>{F})\<close> using 0 "&E" by blast
  qed
qed

AOT_theorem "comp-sit:1":
  assumes \<open>CONDITION_ON_PROPOSITIONAL_PROPERTIES(\<phi>)\<close>
  shows \<open>\<exists>s \<forall>F(s[F] \<equiv> \<phi>{F})\<close>
  by (AOT_subst \<open>\<lambda>\<kappa> . \<guillemotleft>Situation(\<kappa>) & \<forall>F(\<kappa>[F] \<equiv> \<phi>{F})\<guillemotright>\<close> \<open>\<lambda>\<kappa>. \<guillemotleft>A!\<kappa> & \<forall>F (\<kappa>[F] \<equiv> \<phi>{F})\<guillemotright>\<close>)
     (auto simp: "pre-comp-sit"[OF assms] "A-objects"[where \<phi>=\<phi>, axiom_inst])

AOT_theorem "comp-sit:2":
  assumes \<open>CONDITION_ON_PROPOSITIONAL_PROPERTIES(\<phi>)\<close>
  shows \<open>\<exists>!s \<forall>F(s[F] \<equiv> \<phi>{F})\<close>
  by (AOT_subst \<open>\<lambda>\<kappa> . \<guillemotleft>Situation(\<kappa>) & \<forall>F(\<kappa>[F] \<equiv> \<phi>{F})\<guillemotright>\<close> \<open>\<lambda>\<kappa>. \<guillemotleft>A!\<kappa> & \<forall>F (\<kappa>[F] \<equiv> \<phi>{F})\<guillemotright>\<close>)
     (auto simp: assms "pre-comp-sit"  "pre-comp-sit"[OF assms] "A-objects!")

AOT_theorem "can-sit-desc:1":
  assumes \<open>CONDITION_ON_PROPOSITIONAL_PROPERTIES(\<phi>)\<close>
  shows \<open>\<^bold>\<iota>s(\<forall>F (s[F] \<equiv> \<phi>{F}))\<down>\<close>
  using "comp-sit:2"[OF assms] "A-Exists:2" "RA[2]" "\<equiv>E"(2) by blast

AOT_theorem "can-sit-desc:2":
  assumes \<open>CONDITION_ON_PROPOSITIONAL_PROPERTIES(\<phi>)\<close>
  shows \<open>\<^bold>\<iota>s(\<forall>F (s[F] \<equiv> \<phi>{F})) = \<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))\<close>
  by (auto intro!: "equiv-desc-eq:2"[THEN "\<rightarrow>E", OF "&I", OF "can-sit-desc:1"[OF assms]]
                   "RA[2]" GEN "pre-comp-sit"[OF assms])

AOT_theorem "strict-sit":
  assumes \<open>RIGID_CONDITION(\<phi>)\<close>
      and \<open>CONDITION_ON_PROPOSITIONAL_PROPERTIES(\<phi>)\<close>
    shows \<open>y = \<^bold>\<iota>s(\<forall>F (s[F] \<equiv> \<phi>{F})) \<rightarrow> \<forall>F (y[F] \<equiv> \<phi>{F})\<close>
  using "rule=E"[rotated, OF "can-sit-desc:2"[OF assms(2), symmetric]]
        "box-phi-a:2"[OF assms(1)] "\<rightarrow>E" "\<rightarrow>I" "&E" by fast

(* TODO: exercise (479) sit-lit *)

AOT_define actual :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>Actual'(_')\<close>)
  \<open>Actual(s) \<equiv>\<^sub>d\<^sub>f \<forall>p (s \<Turnstile> p \<rightarrow> p)\<close>

AOT_theorem "act-and-not-pos": \<open>\<exists>s (Actual(s) & \<diamond>\<not>Actual(s))\<close>
proof -
  AOT_obtain q\<^sub>1 where q\<^sub>1_prop: \<open>q\<^sub>1 & \<diamond>\<not>q\<^sub>1\<close>
    by (metis "\<equiv>\<^sub>d\<^sub>fE" "instantiation" "cont-tf:1" "cont-tf-thm:1")
  AOT_have \<open>\<exists>s (\<forall>F (s[F] \<equiv> F = [\<lambda>y q\<^sub>1]))\<close>
  proof (safe intro!: "comp-sit:1" "cond-prop[I]" GEN "\<rightarrow>I")
    AOT_modally_strict {
      AOT_show \<open>Propositional([F])\<close> if \<open>F = [\<lambda>y q\<^sub>1]\<close> for F
        using "\<equiv>\<^sub>d\<^sub>fI" "existential:2[const_var]" "prop-prop1" that by fastforce
    }
  qed
  then AOT_obtain s\<^sub>1 where s_prop: \<open>\<forall>F (s\<^sub>1[F] \<equiv> F = [\<lambda>y q\<^sub>1])\<close>
    using "Situation.\<exists>E"[rotated] by meson
  AOT_have \<open>Actual(s\<^sub>1)\<close>
  proof(safe intro!: actual[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" GEN "\<rightarrow>I" s_prop Situation.\<psi>)
    fix p
    AOT_assume \<open>s\<^sub>1 \<Turnstile> p\<close>
    AOT_hence \<open>s\<^sub>1[\<lambda>y p]\<close>
      by (metis "\<equiv>\<^sub>d\<^sub>fE" "&E"(2) "prop-enc" "true-in-s")
    AOT_hence \<open>[\<lambda>y p] = [\<lambda>y q\<^sub>1]\<close>
      by (rule s_prop[THEN "\<forall>E"(1), THEN "\<equiv>E"(1), rotated]) "cqt:2[lambda]"
    AOT_hence \<open>p = q\<^sub>1\<close> by (metis "\<equiv>E"(2) "p-identity-thm2:3")
    AOT_thus \<open>p\<close> using q\<^sub>1_prop[THEN "&E"(1)] "rule=E" id_sym by fast
  qed
  moreover AOT_have \<open>\<diamond>\<not>Actual(s\<^sub>1)\<close>
  proof(rule "raa-cor:1"; drule "KBasic:12"[THEN "\<equiv>E"(2)])
    AOT_assume \<open>\<box>Actual(s\<^sub>1)\<close>
    AOT_hence \<open>\<box>(Situation(s\<^sub>1) & \<forall>p (s\<^sub>1 \<Turnstile> p \<rightarrow> p))\<close>
      using actual[THEN "\<equiv>Df", THEN "conventions:3"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(1), THEN RM, THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>\<box>\<forall>p (s\<^sub>1 \<Turnstile> p \<rightarrow> p)\<close> by (metis "RM:1" "Conjunction Simplification"(2) "vdash-properties:10")
    AOT_hence \<open>\<forall>p \<box>(s\<^sub>1 \<Turnstile> p \<rightarrow> p)\<close> by (metis "CBF" "vdash-properties:10")
    AOT_hence \<open>\<box>(s\<^sub>1 \<Turnstile> q\<^sub>1 \<rightarrow> q\<^sub>1)\<close> using "\<forall>E" by blast
    AOT_hence \<open>\<box>s\<^sub>1 \<Turnstile> q\<^sub>1 \<rightarrow> \<box>q\<^sub>1\<close> by (metis "\<rightarrow>E" "qml:1" "vdash-properties:1[2]")
    moreover AOT_have \<open>s\<^sub>1 \<Turnstile> q\<^sub>1\<close>
      using s_prop[THEN "\<forall>E"(1), THEN "\<equiv>E"(2), THEN lem1[THEN "\<rightarrow>E", OF Situation.\<psi>, THEN "\<equiv>E"(2)]]
            "rule=I:1" "prop-prop2:2" by blast
    ultimately AOT_have \<open>\<box>q\<^sub>1\<close>
      using "\<equiv>\<^sub>d\<^sub>fE" "&E"(1) "\<equiv>E"(1) "lem2:1" "true-in-s" "vdash-properties:10" by fast
    AOT_thus \<open>\<diamond>\<not>q\<^sub>1 & \<not>\<diamond>\<not>q\<^sub>1\<close> using "KBasic:12"[THEN "\<equiv>E"(1)] q\<^sub>1_prop[THEN "&E"(2)] "&I" by blast
  qed
  ultimately AOT_have \<open>(Actual(s\<^sub>1) & \<diamond>\<not>Actual(s\<^sub>1))\<close> using s_prop "&I" by blast
  thus ?thesis by (rule "Situation.\<exists>I")
qed

AOT_theorem "actual-s:1": \<open>\<exists>s Actual(s)\<close>
proof -
  AOT_obtain s where \<open>(Actual(s) & \<diamond>\<not>Actual(s))\<close>
    using "act-and-not-pos" "Situation.\<exists>E"[rotated] by meson
  AOT_hence \<open>Actual(s)\<close> using "&E" "&I" by metis
  thus ?thesis by (rule "Situation.\<exists>I")
qed

AOT_theorem "actual-s:2": \<open>\<exists>s \<not>Actual(s)\<close>
proof(rule "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>\<^bold>s\<^sub>V\<guillemotright>\<close>]; (rule "&I")?)
  AOT_show \<open>Situation(\<^bold>s\<^sub>V)\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" "&E"(1) "df-null-trivial:2" "null-triv-sc:4" by blast
next
  AOT_show \<open>\<not>Actual(\<^bold>s\<^sub>V)\<close>
  proof(rule "raa-cor:2")
    AOT_assume 0: \<open>Actual(\<^bold>s\<^sub>V)\<close>
    AOT_obtain p\<^sub>1 where notp\<^sub>1: \<open>\<not>p\<^sub>1\<close>
      by (metis "instantiation" "existential:1" "log-prop-prop:2" "non-contradiction")
    AOT_have \<open>\<^bold>s\<^sub>V \<Turnstile> p\<^sub>1\<close>
      using "null-triv-sc:4"[THEN "\<equiv>\<^sub>d\<^sub>fE"[OF "df-null-trivial:2"], THEN "&E"(2)] "\<forall>E" by blast
    AOT_hence \<open>p\<^sub>1\<close> using 0[THEN actual[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"]
      by blast
    AOT_thus \<open>p & \<not>p\<close> for p using notp\<^sub>1 by (metis "raa-cor:3")
  qed
next
  AOT_show \<open>\<^bold>s\<^sub>V\<down>\<close>
    using "df-the-null-sit:2" "rule-id-def:2:b[zero]" "thm-null-trivial:4" by blast
qed

AOT_theorem "actual-s:3": \<open>\<exists>p\<forall>s(Actual(s) \<rightarrow> \<not>s \<Turnstile> p)\<close>
proof -
  AOT_obtain p\<^sub>1 where notp\<^sub>1: \<open>\<not>p\<^sub>1\<close>
    by (metis "instantiation" "existential:1" "log-prop-prop:2" "non-contradiction")
  AOT_have \<open>\<forall>s (Actual(s) \<rightarrow> \<not>(s \<Turnstile> p\<^sub>1))\<close>
  proof (rule Situation.GEN; rule "\<rightarrow>I"; rule "raa-cor:2")
    fix s
    AOT_assume \<open>Actual(s)\<close>
    moreover AOT_assume \<open>s \<Turnstile> p\<^sub>1\<close>
    ultimately AOT_have \<open>p\<^sub>1\<close> using actual[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
    AOT_thus \<open>p\<^sub>1 & \<not>p\<^sub>1\<close> using notp\<^sub>1 "&I" by simp
  qed
  thus ?thesis by (rule "\<exists>I")
qed

AOT_theorem comp: \<open>\<exists>s (s' \<unlhd> s & s'' \<unlhd> s & \<forall>s''' (s' \<unlhd> s''' & s'' \<unlhd> s''' \<rightarrow> s \<unlhd> s'''))\<close>
proof -
  have cond_prop: \<open>ConditionOnPropositionalProperties (\<lambda> \<Pi> . \<guillemotleft>s'[\<Pi>] \<or> s''[\<Pi>]\<guillemotright>)\<close>
  proof(safe intro!: "cond-prop[I]" GEN "oth-class-taut:8:c"[THEN "\<rightarrow>E", THEN "\<rightarrow>E"]; rule "\<rightarrow>I")
    AOT_modally_strict {
      fix F
      AOT_have \<open>Situation(s')\<close>
        by (simp add: Situation.restricted_var_condition)
      AOT_hence \<open>s'[F] \<rightarrow> Propositional([F])\<close>
        using "situations"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), THEN "\<forall>E"(2)] by blast
      moreover AOT_assume \<open>s'[F]\<close>
      ultimately AOT_show \<open>Propositional([F])\<close>
        using "\<rightarrow>E" by blast
    }
  next
    AOT_modally_strict {
      fix F
      AOT_have \<open>Situation(s'')\<close>
        by (simp add: Situation.restricted_var_condition)
      AOT_hence \<open>s''[F] \<rightarrow> Propositional([F])\<close>
        using "situations"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), THEN "\<forall>E"(2)] by blast
      moreover AOT_assume \<open>s''[F]\<close>
      ultimately AOT_show \<open>Propositional([F])\<close>
        using "\<rightarrow>E" by blast
    }
  qed
  AOT_obtain s\<^sub>3 where \<theta>: \<open>\<forall>F (s\<^sub>3[F] \<equiv> s'[F] \<or> s''[F])\<close>
    using "comp-sit:1"[OF cond_prop] "Situation.\<exists>E"[rotated] by meson
  AOT_have \<open>s' \<unlhd> s\<^sub>3 & s'' \<unlhd> s\<^sub>3 & \<forall>s''' (s' \<unlhd> s''' & s'' \<unlhd> s''' \<rightarrow> s\<^sub>3 \<unlhd> s''')\<close>
  proof(safe intro!: "&I" "\<equiv>\<^sub>d\<^sub>fI"[OF "true-in-s"] "\<equiv>\<^sub>d\<^sub>fI"[OF "prop-enc"]
                     "Situation.GEN" "GEN"[where 'a=\<o>] "\<rightarrow>I" "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fI"]
                     Situation.restricted_var_condition "cqt:2[const_var]"[axiom_inst])
    fix p
    AOT_assume \<open>s' \<Turnstile> p\<close>
    AOT_hence \<open>s'[\<lambda>x p]\<close>
      by (metis "&E"(2) "prop-enc" "\<equiv>\<^sub>d\<^sub>fE" "true-in-s")
    AOT_thus \<open>s\<^sub>3[\<lambda>x p]\<close>
      using \<theta>[THEN "\<forall>E"(1),OF "prop-prop2:2", THEN "\<equiv>E"(2), OF "\<or>I"(1)] by blast
  next
    fix p
    AOT_assume \<open>s'' \<Turnstile> p\<close>
    AOT_hence \<open>s''[\<lambda>x p]\<close>
      by (metis "&E"(2) "prop-enc" "\<equiv>\<^sub>d\<^sub>fE" "true-in-s")
    AOT_thus \<open>s\<^sub>3[\<lambda>x p]\<close>
      using \<theta>[THEN "\<forall>E"(1),OF "prop-prop2:2", THEN "\<equiv>E"(2), OF "\<or>I"(2)] by blast
  next
    fix s p
    AOT_assume 0: \<open>s' \<unlhd> s & s'' \<unlhd> s\<close>
    AOT_assume \<open>s\<^sub>3 \<Turnstile> p\<close>
    AOT_hence \<open>s\<^sub>3[\<lambda>x p]\<close>
      by (metis "&E"(2) "prop-enc" "\<equiv>\<^sub>d\<^sub>fE" "true-in-s")
    AOT_hence \<open>s'[\<lambda>x p] \<or> s''[\<lambda>x p]\<close>
      using \<theta>[THEN "\<forall>E"(1),OF "prop-prop2:2", THEN "\<equiv>E"(1)] by blast
    moreover {
      AOT_assume \<open>s'[\<lambda>x p]\<close>
      AOT_hence \<open>s' \<Turnstile> p\<close>
        by (safe intro!: "prop-enc"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "true-in-s"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I"
                         Situation.\<psi> "cqt:2[const_var]"[axiom_inst])
      moreover AOT_have \<open>s' \<Turnstile> p \<rightarrow> s \<Turnstile> p\<close>
        using "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2)] 0[THEN "&E"(1)] "\<forall>E"(2) by blast
      ultimately AOT_have \<open>s \<Turnstile> p\<close>
        using "\<rightarrow>E" by blast
      AOT_hence \<open>s[\<lambda>x p]\<close>
        using "true-in-s"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "prop-enc"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
    }
    moreover {
      AOT_assume \<open>s''[\<lambda>x p]\<close>
      AOT_hence \<open>s'' \<Turnstile> p\<close>
        by (safe intro!: "prop-enc"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "true-in-s"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I"
                         Situation.\<psi> "cqt:2[const_var]"[axiom_inst])
      moreover AOT_have \<open>s'' \<Turnstile> p \<rightarrow> s \<Turnstile> p\<close>
        using "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2)] 0[THEN "&E"(2)] "\<forall>E"(2) by blast
      ultimately AOT_have \<open>s \<Turnstile> p\<close>
        using "\<rightarrow>E" by blast
      AOT_hence \<open>s[\<lambda>x p]\<close>
        using "true-in-s"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "prop-enc"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
    }
    ultimately AOT_show \<open>s[\<lambda>x p]\<close>
      by (metis "\<or>E"(1) "\<rightarrow>I")
  qed
  thus ?thesis
    using "Situation.\<exists>I" by fast
qed

AOT_theorem "act-sit:1": \<open>Actual(s) \<rightarrow> (s \<Turnstile> p \<rightarrow> [\<lambda>y p]s)\<close>
proof (safe intro!: "\<rightarrow>I")
  AOT_assume \<open>Actual(s)\<close>
  AOT_hence p if \<open>s \<Turnstile> p\<close> using actual[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"] that by blast
  moreover AOT_assume \<open>s \<Turnstile> p\<close>
  ultimately AOT_have p: p by blast
  AOT_show \<open>[\<lambda>y p]s\<close>
    by (rule "\<beta>\<leftarrow>C"(1); "cqt:2[lambda]")
       (auto simp: p "ex:1:a" "rule-ui:2[const_var]")
qed

AOT_theorem "act-sit:2": \<open>(Actual(s') & Actual(s'')) \<rightarrow> \<exists>x (Actual(x) & s' \<unlhd> x & s'' \<unlhd> x)\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume act_s': \<open>Actual(s')\<close>
  AOT_assume act_s'': \<open>Actual(s'')\<close>
  have "cond-prop": \<open>ConditionOnPropositionalProperties (\<lambda> \<Pi> . \<guillemotleft>\<exists>p (\<Pi> = [\<lambda>y p] & (s' \<Turnstile> p \<or> s'' \<Turnstile> p))\<guillemotright>)\<close>
  proof (safe intro!: "cond-prop[I]"  "\<forall>I" "\<rightarrow>I" "prop-prop1"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
    AOT_modally_strict {
      fix \<beta>
      AOT_assume \<open>\<exists>p (\<beta> = [\<lambda>y p] & (s' \<Turnstile> p \<or> s'' \<Turnstile> p))\<close>
      then AOT_obtain p where \<open>\<beta> = [\<lambda>y p]\<close> using "\<exists>E"[rotated] "&E" by blast
      AOT_thus \<open>\<exists>p \<beta> = [\<lambda>y p]\<close> by (rule "\<exists>I")
    }
  qed
  have rigid: \<open>rigid_condition (\<lambda> \<Pi> . \<guillemotleft>\<exists>p (\<Pi> = [\<lambda>y p] & (s' \<Turnstile> p \<or> s'' \<Turnstile> p))\<guillemotright>)\<close>
  proof(safe intro!: "strict-can:1[I]" "\<rightarrow>I" GEN)
    AOT_modally_strict {
      fix F
      AOT_assume \<open>\<exists>p (F = [\<lambda>y p] & (s' \<Turnstile> p \<or> s'' \<Turnstile> p))\<close>
      then AOT_obtain p\<^sub>1 where p\<^sub>1_prop: \<open>F = [\<lambda>y p\<^sub>1] & (s' \<Turnstile> p\<^sub>1 \<or> s'' \<Turnstile> p\<^sub>1)\<close>
        using "\<exists>E"[rotated] by blast
      AOT_hence \<open>\<box>(F = [\<lambda>y p\<^sub>1])\<close>
        using "&E"(1) "id-nec:2" "vdash-properties:10" by blast
      moreover AOT_have \<open>\<box>(s' \<Turnstile> p\<^sub>1 \<or> s'' \<Turnstile> p\<^sub>1)\<close>
      proof(rule "\<or>E"; (rule "\<rightarrow>I"; rule "KBasic:15"[THEN "\<rightarrow>E"])?)
        AOT_show \<open>s' \<Turnstile> p\<^sub>1 \<or> s'' \<Turnstile> p\<^sub>1\<close> using p\<^sub>1_prop "&E" by blast
      next
        AOT_show \<open>\<box>s' \<Turnstile> p\<^sub>1 \<or> \<box>s'' \<Turnstile> p\<^sub>1\<close> if \<open>s' \<Turnstile> p\<^sub>1\<close>
          apply (rule "\<or>I"(1))
          using "\<equiv>\<^sub>d\<^sub>fE" "&E"(1) "\<equiv>E"(1) "lem2:1" that "true-in-s" by blast
      next
        AOT_show \<open>\<box>s' \<Turnstile> p\<^sub>1 \<or> \<box>s'' \<Turnstile> p\<^sub>1\<close> if \<open>s'' \<Turnstile> p\<^sub>1\<close>
          apply (rule "\<or>I"(2))
          using "\<equiv>\<^sub>d\<^sub>fE" "&E"(1) "\<equiv>E"(1) "lem2:1" that "true-in-s" by blast
      qed
      ultimately AOT_have \<open>\<box>(F = [\<lambda>y p\<^sub>1] & (s' \<Turnstile> p\<^sub>1 \<or> s'' \<Turnstile> p\<^sub>1))\<close>
        by (metis "KBasic:3" "&I" "\<equiv>E"(2))
      AOT_hence \<open>\<exists>p \<box>(F = [\<lambda>y p] & (s' \<Turnstile> p \<or> s'' \<Turnstile> p))\<close> by (rule "\<exists>I")
      AOT_thus \<open>\<box>\<exists>p (F = [\<lambda>y p] & (s' \<Turnstile> p \<or> s'' \<Turnstile> p))\<close>
        using Buridan[THEN "\<rightarrow>E"] by fast
    }
  qed

  AOT_have desc_den: \<open>\<^bold>\<iota>s(\<forall>F (s[F] \<equiv> \<exists>p (F = [\<lambda>y p] & (s' \<Turnstile> p \<or> s'' \<Turnstile> p))))\<down>\<close>
    by (rule "can-sit-desc:1"[OF "cond-prop"])
  AOT_obtain x\<^sub>0 where x\<^sub>0_prop1: \<open>x\<^sub>0 = \<^bold>\<iota>s(\<forall>F (s[F] \<equiv> \<exists>p (F = [\<lambda>y p] & (s' \<Turnstile> p \<or> s'' \<Turnstile> p))))\<close>
    by (metis (no_types, lifting) "instantiation" "rule=I:1" desc_den "existential:1" id_sym)
  AOT_hence x\<^sub>0_sit: \<open>Situation(x\<^sub>0)\<close>
    using "actual-desc:3"[THEN "\<rightarrow>E"] "Act-Basic:2" "&E"(1) "\<equiv>E"(1) "possit-sit:4" by blast

  AOT_have 1: \<open>\<forall>F (x\<^sub>0[F] \<equiv> \<exists>p (F = [\<lambda>y p] & (s' \<Turnstile> p \<or> s'' \<Turnstile> p)))\<close>
    using "strict-sit"[OF rigid, OF "cond-prop", THEN "\<rightarrow>E", OF x\<^sub>0_prop1].
  AOT_have 2: \<open>(x\<^sub>0 \<Turnstile> p) \<equiv> (s' \<Turnstile> p \<or> s'' \<Turnstile> p)\<close> for p
  proof (rule "\<equiv>I"; rule "\<rightarrow>I")
    AOT_assume \<open>x\<^sub>0 \<Turnstile> p\<close>
    AOT_hence \<open>x\<^sub>0[\<lambda>y p]\<close> using lem1[THEN "\<rightarrow>E", OF x\<^sub>0_sit, THEN "\<equiv>E"(1)] by blast
    then AOT_obtain q where \<open>[\<lambda>y p] = [\<lambda>y q] & (s' \<Turnstile> q \<or> s'' \<Turnstile> q)\<close>
      using 1[THEN "\<forall>E"(1)[where \<tau>="\<guillemotleft>[\<lambda>y p]\<guillemotright>"], OF "prop-prop2:2", THEN "\<equiv>E"(1)]
            "\<exists>E"[rotated] by blast
    AOT_thus \<open>s' \<Turnstile> p \<or> s'' \<Turnstile> p\<close>
      by (metis "rule=E" "&E"(1) "&E"(2) "\<or>I"(1) "\<or>I"(2)
                "\<or>E"(1) "deduction-theorem" id_sym "\<equiv>E"(2) "p-identity-thm2:3")
  next
    AOT_assume \<open>s' \<Turnstile> p \<or> s'' \<Turnstile> p\<close>
    AOT_hence \<open>[\<lambda>y p] = [\<lambda>y p] & (s' \<Turnstile> p \<or> s'' \<Turnstile> p)\<close>
      by (metis "rule=I:1" "&I" "prop-prop2:2") 
    AOT_hence \<open>\<exists>q ([\<lambda>y p] = [\<lambda>y q] & (s' \<Turnstile> q \<or> s'' \<Turnstile> q))\<close>
      by (rule "\<exists>I")
    AOT_hence \<open>x\<^sub>0[\<lambda>y p]\<close>
      using 1[THEN "\<forall>E"(1), OF "prop-prop2:2", THEN "\<equiv>E"(2)] by blast
    AOT_thus \<open>x\<^sub>0 \<Turnstile> p\<close> by (metis "\<equiv>\<^sub>d\<^sub>fI" "&I" "ex:1:a" "prop-enc" "rule-ui:2[const_var]" x\<^sub>0_sit "true-in-s")
  qed

  AOT_have \<open>Actual(x\<^sub>0) & s' \<unlhd> x\<^sub>0 & s'' \<unlhd> x\<^sub>0\<close>
  proof(safe intro!: "\<rightarrow>I" "&I" "\<exists>I"(1) actual[THEN "\<equiv>\<^sub>d\<^sub>fI"] x\<^sub>0_sit GEN "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
    fix p
    AOT_assume \<open>x\<^sub>0 \<Turnstile> p\<close>
    AOT_hence \<open>s' \<Turnstile> p \<or> s'' \<Turnstile> p\<close>
      using 2 "\<equiv>E"(1) by metis
    AOT_thus \<open>p\<close> using act_s' act_s'' actual[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"]
      by (metis "\<or>E"(3) "reductio-aa:1")
  next
    AOT_show \<open>x\<^sub>0 \<Turnstile> p\<close> if \<open>s' \<Turnstile> p\<close> for p using 2[THEN "\<equiv>E"(2), OF "\<or>I"(1), OF that].
  next
    AOT_show \<open>x\<^sub>0 \<Turnstile> p\<close> if \<open>s'' \<Turnstile> p\<close> for p using 2[THEN "\<equiv>E"(2), OF "\<or>I"(2), OF that].
  next
    AOT_show \<open>Situation(s')\<close> using act_s'[THEN actual[THEN "\<equiv>\<^sub>d\<^sub>fE"]] "&E" by blast
  next
    AOT_show \<open>Situation(s'')\<close> using act_s''[THEN actual[THEN "\<equiv>\<^sub>d\<^sub>fE"]] "&E" by blast
  qed
  AOT_thus \<open>\<exists>x (Actual(x) & s' \<unlhd> x & s'' \<unlhd> x)\<close>
    by (rule "\<exists>I")
qed

AOT_define Consistent :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>Consistent'(_')\<close>)
  cons: \<open>Consistent(s) \<equiv>\<^sub>d\<^sub>f \<not>\<exists>p (s \<Turnstile> p & s \<Turnstile> \<not>p)\<close>

AOT_theorem "sit-cons": \<open>Actual(s) \<rightarrow> Consistent(s)\<close>
proof(safe intro!: "\<rightarrow>I" cons[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" Situation.\<psi> dest!: actual[THEN "\<equiv>\<^sub>d\<^sub>fE"]; frule "&E"(1); drule "&E"(2))
  AOT_assume 0: \<open>\<forall>p (s \<Turnstile> p \<rightarrow> p)\<close>
  AOT_show \<open>\<not>\<exists>p (s \<Turnstile> p & s \<Turnstile> \<not>p)\<close>
  proof (rule "raa-cor:2")
    AOT_assume \<open>\<exists>p (s \<Turnstile> p & s \<Turnstile> \<not>p)\<close>
    then AOT_obtain p where \<open>s \<Turnstile> p & s \<Turnstile> \<not>p\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>p & \<not>p\<close>
      using 0[THEN "\<forall>E"(1)[where \<tau>=\<open>\<guillemotleft>\<not>p\<guillemotright>\<close>, THEN "\<rightarrow>E"], OF "log-prop-prop:2"]
            0[THEN "\<forall>E"(2)[where \<beta>=p], THEN "\<rightarrow>E"] "&E" "&I" by blast
    AOT_thus \<open>p & \<not>p\<close> for p by (metis "raa-cor:1") 
  qed
qed

(* TODO: PLM: recheck use of substitution with restricted variables *)
AOT_theorem "cons-rigid:1": \<open>\<not>Consistent(s) \<equiv> \<box>\<not>Consistent(s)\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<not>Consistent(s)\<close>
  AOT_hence \<open>\<exists>p (s \<Turnstile> p & s \<Turnstile> \<not>p)\<close>
    using cons[THEN "\<equiv>\<^sub>d\<^sub>fI", OF "&I", OF Situation.\<psi>] by (metis "raa-cor:3")
  then AOT_obtain p where p_prop: \<open>s \<Turnstile> p & s \<Turnstile> \<not>p\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<open>\<box>s \<Turnstile> p\<close>
    using "&E"(1) "\<equiv>E"(1) "lem2:1" by blast
  moreover AOT_have \<open>\<box>s \<Turnstile> \<not>p\<close>
    using p_prop "T\<diamond>" "&E" "\<equiv>E"(1)
      "modus-tollens:1" "raa-cor:3" "lem2:3"[unvarify p]
      "log-prop-prop:2" by metis
  ultimately AOT_have \<open>\<box>(s \<Turnstile> p & s \<Turnstile> \<not>p)\<close>
    by (metis "KBasic:3" "&I" "\<equiv>E"(2))
  AOT_hence \<open>\<exists>p \<box>(s \<Turnstile> p & s \<Turnstile> \<not>p)\<close>
    by (rule "\<exists>I")
  AOT_hence \<open>\<box>\<exists>p(s \<Turnstile> p & s \<Turnstile> \<not>p)\<close>
    by (metis Buridan "vdash-properties:10") 
  AOT_thus \<open>\<box>\<not>Consistent(s)\<close>
    apply (rule "qml:1"[axiom_inst, THEN "\<rightarrow>E", THEN "\<rightarrow>E", rotated])
    apply (rule RN)
    using "\<equiv>\<^sub>d\<^sub>fE" "&E"(2) cons "deduction-theorem" "raa-cor:3" by blast
next
  AOT_assume \<open>\<box>\<not>Consistent(s)\<close>
  AOT_thus \<open>\<not>Consistent(s)\<close> using "qml:2"[axiom_inst, THEN "\<rightarrow>E"] by auto
qed

AOT_theorem "cons-rigid:2": \<open>\<diamond>Consistent(x) \<equiv> Consistent(x)\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<diamond>Consistent(x)\<close>
  AOT_have \<open>\<diamond>(Situation(x) & \<not>\<exists>p (x \<Turnstile> p & x \<Turnstile> \<not>p))\<close>
    apply (AOT_subst \<open>\<guillemotleft>Situation(x) & \<not>\<exists>p (x \<Turnstile> p & x \<Turnstile> \<not>p)\<guillemotright>\<close> \<open>\<guillemotleft>Consistent(x)\<guillemotright>\<close>)
     using cons "\<equiv>E"(2) "Commutativity of \<equiv>" "\<equiv>Df" apply blast
    by (simp add: 0)
  AOT_hence \<open>\<diamond>Situation(x)\<close> and 1: \<open>\<diamond>\<not>\<exists>p (x \<Turnstile> p & x \<Turnstile> \<not>p)\<close>
    using "RM\<diamond>" "Conjunction Simplification"(1) "Conjunction Simplification"(2) "modus-tollens:1" "raa-cor:3" by blast+
  AOT_hence 2: \<open>Situation(x)\<close> by (metis "\<equiv>E"(1) "possit-sit:2")
  AOT_have 3: \<open>\<not>\<box>\<exists>p (x \<Turnstile> p & x \<Turnstile> \<not>p)\<close>
    using 2 using 1 "KBasic:11" "\<equiv>E"(2) by blast
  AOT_show \<open>Consistent(x)\<close>
  proof (rule "raa-cor:1")
    AOT_assume \<open>\<not>Consistent(x)\<close>
    AOT_hence \<open>\<exists>p (x \<Turnstile> p & x \<Turnstile> \<not>p)\<close>
      using 0 "\<equiv>\<^sub>d\<^sub>fE" "conventions:5" 2 "cons-rigid:1"[unconstrain s, THEN "\<rightarrow>E"] "modus-tollens:1" "raa-cor:3" "\<equiv>E"(4) by meson
    then AOT_obtain p where \<open>x \<Turnstile> p\<close> and 4: \<open>x \<Turnstile> \<not>p\<close> using "\<exists>E"[rotated] "&E" by blast
    AOT_hence \<open>\<box>x \<Turnstile> p\<close> by (metis "2" "\<equiv>E"(1) "lem2:1"[unconstrain s, THEN "\<rightarrow>E"])
    moreover AOT_have \<open>\<box>x \<Turnstile> \<not>p\<close> using 4 "lem2:1"[unconstrain s, unvarify p, THEN "\<rightarrow>E"]  by (metis 2 "\<equiv>E"(1) "log-prop-prop:2")
    ultimately AOT_have \<open>\<box>(x \<Turnstile> p & x \<Turnstile> \<not>p)\<close> by (metis "KBasic:3" "&I" "\<equiv>E"(3) "raa-cor:3")
    AOT_hence \<open>\<exists>p \<box>(x \<Turnstile> p & x \<Turnstile> \<not>p)\<close> by (metis "existential:1" "log-prop-prop:2")
    AOT_hence \<open>\<box>\<exists>p (x \<Turnstile> p & x \<Turnstile> \<not>p)\<close> by (metis Buridan "vdash-properties:10")
    AOT_thus \<open>p & \<not>p\<close> for p using 3 "&I"  by (metis "raa-cor:3")
  qed
next
  AOT_show \<open>\<diamond>Consistent(x)\<close> if \<open>Consistent(x)\<close>
    using "T\<diamond>" that "vdash-properties:10" by blast
qed

AOT_define possible :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>Possible'(_')\<close>)
  pos: \<open>Possible(s) \<equiv>\<^sub>d\<^sub>f \<diamond>Actual(s)\<close>

AOT_theorem "sit-pos:1": \<open>Actual(s) \<rightarrow> Possible(s)\<close>
  apply(rule "\<rightarrow>I"; rule pos[THEN "\<equiv>\<^sub>d\<^sub>fI"]; rule "&I")
  apply (meson "\<equiv>\<^sub>d\<^sub>fE" actual "&E"(1))
  using "T\<diamond>" "vdash-properties:10" by blast

AOT_theorem "sit-pos:2": \<open>\<exists>p ((s \<Turnstile> p) & \<not>\<diamond>p) \<rightarrow> \<not>Possible(s)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<exists>p ((s \<Turnstile> p) & \<not>\<diamond>p)\<close>
  then AOT_obtain p where a: \<open>(s \<Turnstile> p) & \<not>\<diamond>p\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<open>\<box>(s \<Turnstile> p)\<close> using "&E" by (metis "T\<diamond>" "\<equiv>E"(1) "lem2:3" "vdash-properties:10")
  moreover AOT_have \<open>\<box>\<not>p\<close> using a[THEN "&E"(2)] by (metis "KBasic2:1" "\<equiv>E"(2))
  ultimately AOT_have \<open>\<box>(s \<Turnstile> p & \<not>p)\<close> by (metis "KBasic:3" "&I" "\<equiv>E"(3) "raa-cor:3")
  AOT_hence \<open>\<exists>p \<box>(s \<Turnstile> p & \<not>p)\<close> by (rule "\<exists>I")
  AOT_hence 1: \<open>\<box>\<exists>q (s \<Turnstile> q & \<not>q)\<close> by (metis Buridan "vdash-properties:10")
  AOT_have \<open>\<box>\<not>\<forall>q (s \<Turnstile> q \<rightarrow> q)\<close>
    apply (AOT_subst \<open>\<lambda>\<phi> . \<guillemotleft>s \<Turnstile> \<phi> \<rightarrow> \<phi>\<guillemotright>\<close> \<open>\<lambda> \<phi> . \<guillemotleft>\<not>(s \<Turnstile> \<phi> & \<not>\<phi>)\<guillemotright>\<close>)
     apply (simp add: "oth-class-taut:1:a")
    apply (AOT_subst \<open>\<guillemotleft>\<not>\<forall>q \<not>(s \<Turnstile> q & \<not>q)\<guillemotright>\<close> \<open>\<guillemotleft>\<exists>q (s \<Turnstile> q & \<not>q)\<guillemotright>\<close>)
    by (auto simp: "conventions:4" "df-rules-formulas[3]" "df-rules-formulas[4]" "\<equiv>I" 1)
  AOT_hence 0: \<open>\<not>\<diamond>\<forall>q (s \<Turnstile> q \<rightarrow> q)\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "conventions:5" "raa-cor:3")
  AOT_show \<open>\<not>Possible(s)\<close>
    apply (AOT_subst \<open>\<guillemotleft>Possible(s)\<guillemotright>\<close> \<open>\<guillemotleft>Situation(s) & \<diamond>Actual(s)\<guillemotright>\<close>)
     apply (simp add: pos "\<equiv>Df")
    apply (AOT_subst \<open>\<guillemotleft>Actual(s)\<guillemotright>\<close> \<open>\<guillemotleft>Situation(s) & \<forall>q (s \<Turnstile> q \<rightarrow> q)\<guillemotright>\<close>)
     using actual "\<equiv>Df" apply presburger
    by (metis "0" "KBasic2:3" "&E"(2) "raa-cor:3" "vdash-properties:10")
qed

AOT_theorem "pos-cons-sit:1": \<open>Possible(s) \<rightarrow> Consistent(s)\<close>
  by (auto simp: "sit-cons"[THEN "RM\<diamond>", THEN "\<rightarrow>E", THEN "cons-rigid:2"[THEN "\<equiv>E"(1)]]
           intro!: "\<rightarrow>I" dest!: pos[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E"(2))

AOT_theorem "pos-cons-sit:2": \<open>\<exists>s (Consistent(s) & \<not>Possible(s))\<close>
proof -
  AOT_obtain q\<^sub>1 where \<open>q\<^sub>1 & \<diamond>\<not>q\<^sub>1\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" "instantiation" "cont-tf:1" "cont-tf-thm:1" by blast
  have "cond-prop": \<open>ConditionOnPropositionalProperties (\<lambda> \<Pi> . \<guillemotleft>\<Pi> = [\<lambda>y q\<^sub>1 & \<not>q\<^sub>1]\<guillemotright>)\<close>
    by (auto intro!: "cond-prop[I]" GEN "\<rightarrow>I" "prop-prop1"[THEN "\<equiv>\<^sub>d\<^sub>fI"]
                     "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>q\<^sub>1 & \<not>q\<^sub>1\<guillemotright>\<close>, rotated, OF "log-prop-prop:2"])
  have rigid: \<open>rigid_condition (\<lambda> \<Pi> . \<guillemotleft>\<Pi> = [\<lambda>y q\<^sub>1 & \<not>q\<^sub>1]\<guillemotright>)\<close>
    by (auto intro!: "strict-can:1[I]" GEN "\<rightarrow>I" simp: "id-nec:2"[THEN "\<rightarrow>E"])

  AOT_obtain x where x_prop: \<open>x = \<^bold>\<iota>s (\<forall>F (s[F] \<equiv> F = [\<lambda>y q\<^sub>1 & \<not>q\<^sub>1]))\<close>
    using "ex:1:b"[THEN "\<forall>E"(1), OF "can-sit-desc:1", OF "cond-prop"]
          "\<exists>E"[rotated] by blast    
  AOT_hence 0: \<open>\<^bold>\<A>(Situation(x) & \<forall>F (x[F] \<equiv> F = [\<lambda>y q\<^sub>1 & \<not>q\<^sub>1]))\<close>
    using "\<rightarrow>E" "actual-desc:2" by blast
  AOT_hence \<open>\<^bold>\<A>(Situation(x))\<close> by (metis "Act-Basic:2" "&E"(1) "\<equiv>E"(1))
  AOT_hence s_sit: \<open>Situation(x)\<close> by (metis "\<equiv>E"(1) "possit-sit:4")
  AOT_have s_enc_prop: \<open>\<forall>F (x[F] \<equiv> F = [\<lambda>y q\<^sub>1 & \<not>q\<^sub>1])\<close>
    using "strict-sit"[OF rigid, OF "cond-prop", THEN "\<rightarrow>E", OF x_prop].
  AOT_hence \<open>x[\<lambda>y q\<^sub>1 & \<not>q\<^sub>1]\<close>
    using "\<forall>E"(1)[rotated, OF "prop-prop2:2"] "rule=I:1"[OF "prop-prop2:2"] "\<equiv>E" by blast
  AOT_hence \<open>x \<Turnstile> (q\<^sub>1 & \<not>q\<^sub>1)\<close>
    using lem1[THEN "\<rightarrow>E", OF s_sit, unvarify p, THEN "\<equiv>E"(2), OF "log-prop-prop:2"]
    by blast
  AOT_hence \<open>\<box>(x \<Turnstile> (q\<^sub>1 & \<not>q\<^sub>1))\<close>
    using "lem2:1"[unconstrain s, THEN "\<rightarrow>E", OF s_sit, unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)] by blast
  moreover AOT_have \<open>\<box>(x \<Turnstile> (q\<^sub>1 & \<not>q\<^sub>1) \<rightarrow> \<not>Actual(x))\<close>
  proof(rule RN; rule "\<rightarrow>I"; rule "raa-cor:2")
    AOT_modally_strict {
      AOT_assume \<open>Actual(x)\<close>
      AOT_hence \<open>\<forall>p (x \<Turnstile> p \<rightarrow> p)\<close>
        using actual[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2)] by blast
      moreover AOT_assume \<open>x \<Turnstile> (q\<^sub>1 & \<not>q\<^sub>1)\<close>
      ultimately AOT_show \<open>q\<^sub>1 & \<not>q\<^sub>1\<close> using "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] "\<rightarrow>E" by metis
    }
  qed
  ultimately AOT_have nec_not_actual_s: \<open>\<box>\<not>Actual(x)\<close>
    using "qml:1"[axiom_inst, THEN "\<rightarrow>E", THEN "\<rightarrow>E"] by blast
  AOT_have 1: \<open>\<not>\<exists>p (x \<Turnstile> p & x \<Turnstile> \<not>p)\<close>
  proof (rule "raa-cor:2")
    AOT_assume \<open>\<exists>p (x \<Turnstile> p & x \<Turnstile> \<not>p)\<close>
    then AOT_obtain p where \<open>x \<Turnstile> p & x \<Turnstile> \<not>p\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>x[\<lambda>y p] & x[\<lambda>y \<not>p]\<close>
      using lem1[unvarify p, THEN "\<rightarrow>E", OF "log-prop-prop:2", OF s_sit, THEN "\<equiv>E"(1)] "&I" "&E" by metis
    AOT_hence \<open>[\<lambda>y p] = [\<lambda>y q\<^sub>1 & \<not>q\<^sub>1]\<close> and \<open>[\<lambda>y \<not>p] = [\<lambda>y q\<^sub>1 & \<not>q\<^sub>1]\<close>
      by (auto intro!: "prop-prop2:2" s_enc_prop[THEN "\<forall>E"(1), THEN "\<equiv>E"(1)] elim: "&E")
    AOT_hence i: \<open>[\<lambda>y p] = [\<lambda>y \<not>p]\<close> by (metis "rule=E" id_sym)
    {
      AOT_assume 0: \<open>p\<close>
      AOT_have \<open>[\<lambda>y p]x\<close> for x
        by (rule "\<beta>\<leftarrow>C"(1); "cqt:2[lambda]"; auto intro!: 0 "cqt:2[const_var]"[axiom_inst])
      AOT_hence \<open>[\<lambda>y \<not>p]x\<close> for x using i "rule=E" by fast
      AOT_hence \<open>\<not>p\<close>
        using "\<beta>\<rightarrow>C"(1) by auto
    }
    moreover {
      AOT_assume 0: \<open>\<not>p\<close>
      AOT_have \<open>[\<lambda>y \<not>p]x\<close> for x
        by (rule "\<beta>\<leftarrow>C"(1); "cqt:2[lambda]"; auto intro!: 0 "cqt:2[const_var]"[axiom_inst])
      AOT_hence \<open>[\<lambda>y p]x\<close> for x using i[symmetric] "rule=E" by fast
      AOT_hence \<open>p\<close>
        using "\<beta>\<rightarrow>C"(1) by auto
    }
    ultimately AOT_show \<open>p & \<not>p\<close> for p by (metis "raa-cor:1" "raa-cor:3")
  qed
  AOT_have 2: \<open>\<not>Possible(x)\<close>
  proof(rule "raa-cor:2")
    AOT_assume \<open>Possible(x)\<close>
    AOT_hence \<open>\<diamond>Actual(x)\<close>
      by (metis "\<equiv>\<^sub>d\<^sub>fE" "&E"(2) pos)
    moreover AOT_have \<open>\<not>\<diamond>Actual(x)\<close> using nec_not_actual_s
      using "\<equiv>\<^sub>d\<^sub>fE" "conventions:5" "reductio-aa:2" by blast
    ultimately AOT_show \<open>\<diamond>Actual(x) & \<not>\<diamond>Actual(x)\<close> by (rule "&I")
  qed
  show ?thesis
    by(rule "\<exists>I"(2)[where \<beta>=x]; safe intro!: "&I" 2 s_sit cons[THEN "\<equiv>\<^sub>d\<^sub>fI"] 1)
qed

AOT_theorem "sit-classical:1": \<open>\<forall>p (s \<Turnstile> p \<equiv> p) \<rightarrow> \<forall>q(s \<Turnstile> \<not>q \<equiv> \<not>s \<Turnstile> q)\<close>
proof(rule "\<rightarrow>I"; rule GEN)
  fix q
  AOT_assume \<open>\<forall>p (s \<Turnstile> p \<equiv> p)\<close>
  AOT_hence \<open>s \<Turnstile> q \<equiv> q\<close> and \<open>s \<Turnstile> \<not>q \<equiv> \<not>q\<close>
    using "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] by blast+
  AOT_thus \<open>s \<Turnstile> \<not>q \<equiv> \<not>s \<Turnstile> q\<close>
    by (metis "deduction-theorem" "\<equiv>I" "\<equiv>E"(1) "\<equiv>E"(2) "\<equiv>E"(4))
qed

AOT_theorem "sit-classical:2": \<open>\<forall>p (s \<Turnstile> p \<equiv> p) \<rightarrow> \<forall>q\<forall>r((s \<Turnstile> (q \<rightarrow> r)) \<equiv> (s \<Turnstile> q \<rightarrow> s \<Turnstile> r))\<close>
proof(rule "\<rightarrow>I"; rule GEN; rule GEN)
  fix q r
  AOT_assume \<open>\<forall>p (s \<Turnstile> p \<equiv> p)\<close>
  AOT_hence \<theta>: \<open>s \<Turnstile> q \<equiv> q\<close> and \<xi>: \<open>s \<Turnstile> r \<equiv> r\<close> and \<zeta>: \<open>(s \<Turnstile> (q \<rightarrow> r)) \<equiv> (q \<rightarrow> r)\<close>
    using "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] by blast+
  AOT_show \<open>(s \<Turnstile> (q \<rightarrow> r)) \<equiv> (s \<Turnstile> q \<rightarrow> s \<Turnstile> r)\<close>
  proof (safe intro!: "\<equiv>I" "\<rightarrow>I")
    AOT_assume \<open>s \<Turnstile> (q \<rightarrow> r)\<close>
    moreover AOT_assume \<open>s \<Turnstile> q\<close>
    ultimately AOT_show \<open>s \<Turnstile> r\<close>
      using \<theta> \<xi> \<zeta> by (metis "\<equiv>E"(1) "\<equiv>E"(2) "vdash-properties:10")
  next
    AOT_assume \<open>s \<Turnstile> q \<rightarrow> s \<Turnstile> r\<close>
    AOT_thus \<open>s \<Turnstile> (q \<rightarrow> r)\<close>
      using \<theta> \<xi> \<zeta> by (metis "deduction-theorem" "\<equiv>E"(1) "\<equiv>E"(2) "vdash-properties:10") 
  qed
qed

AOT_theorem "sit-classical:3": \<open>\<forall>p (s \<Turnstile> p \<equiv> p) \<rightarrow> ((s \<Turnstile> \<forall>\<alpha> \<phi>{\<alpha>}) \<equiv> \<forall>\<alpha> s \<Turnstile> \<phi>{\<alpha>})\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>\<forall>p (s \<Turnstile> p \<equiv> p)\<close>
  AOT_hence \<theta>: \<open>s \<Turnstile> \<phi>{\<alpha>} \<equiv> \<phi>{\<alpha>}\<close> and \<xi>: \<open>s \<Turnstile> \<forall>\<alpha> \<phi>{\<alpha>} \<equiv> \<forall>\<alpha> \<phi>{\<alpha>}\<close> for \<alpha>
    using "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] by blast+
  AOT_show \<open>s \<Turnstile> \<forall>\<alpha> \<phi>{\<alpha>} \<equiv> \<forall>\<alpha> s \<Turnstile> \<phi>{\<alpha>}\<close>
  proof (safe intro!: "\<equiv>I" "\<rightarrow>I" GEN)
    fix \<alpha>
    AOT_assume \<open>s \<Turnstile> \<forall>\<alpha> \<phi>{\<alpha>}\<close>
    AOT_hence \<open>\<phi>{\<alpha>}\<close> using \<xi> "\<forall>E"(2) "\<equiv>E"(1) by blast
    AOT_thus \<open>s \<Turnstile> \<phi>{\<alpha>}\<close> using \<theta> "\<equiv>E"(2) by blast
  next
    AOT_assume \<open>\<forall>\<alpha> s \<Turnstile> \<phi>{\<alpha>}\<close>
    AOT_hence \<open>s \<Turnstile> \<phi>{\<alpha>}\<close> for \<alpha> using "\<forall>E"(2) by blast
    AOT_hence \<open>\<phi>{\<alpha>}\<close> for \<alpha> using \<theta> "\<equiv>E"(1) by blast
    AOT_hence \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close> by (rule GEN)
    AOT_thus \<open>s \<Turnstile> \<forall>\<alpha> \<phi>{\<alpha>}\<close> using \<xi> "\<equiv>E"(2) by blast
  qed
qed

AOT_theorem "sit-classical:4": \<open>\<forall>p (s \<Turnstile> p \<equiv> p) \<rightarrow> \<forall>q (s \<Turnstile> \<box>q \<rightarrow> \<box>s \<Turnstile> q)\<close>
proof(rule "\<rightarrow>I"; rule GEN; rule "\<rightarrow>I")
  fix q
  AOT_assume \<open>\<forall>p (s \<Turnstile> p \<equiv> p)\<close>
  AOT_hence \<theta>: \<open>s \<Turnstile> q \<equiv> q\<close> and \<xi>: \<open>s \<Turnstile> \<box>q \<equiv> \<box>q\<close>
    using "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] by blast+
  AOT_assume \<open>s \<Turnstile> \<box>q\<close>
  AOT_hence \<open>\<box>q\<close> using \<xi> "\<equiv>E"(1) by blast
  AOT_hence \<open>q\<close> using "qml:2"[axiom_inst, THEN "\<rightarrow>E"] by blast
  AOT_hence \<open>s \<Turnstile> q\<close> using \<theta> "\<equiv>E"(2) by blast
  AOT_thus \<open>\<box>s \<Turnstile> q\<close> using "\<equiv>\<^sub>d\<^sub>fE" "&E"(1) "\<equiv>E"(1) "lem2:1" "true-in-s" by blast
qed

AOT_theorem "sit-classical:5":
  \<open>\<forall>p (s \<Turnstile> p \<equiv> p) \<rightarrow> \<exists>q(\<box>(s \<Turnstile> q) & \<not>(s \<Turnstile> \<box> q))\<close>
proof (rule "\<rightarrow>I")
  AOT_obtain r where A: \<open>r\<close> and \<open>\<diamond>\<not>r\<close>
    by (metis "&E"(1) "&E"(2) "\<equiv>\<^sub>d\<^sub>fE" "instantiation" "cont-tf:1" "cont-tf-thm:1")
  AOT_hence B: \<open>\<not>\<box>r\<close>
    using "KBasic:11" "\<equiv>E"(2) by blast
  moreover AOT_assume asm: \<open>\<forall> p (s \<Turnstile> p \<equiv> p)\<close>
  AOT_hence \<open>s \<Turnstile> r\<close> using "\<forall>E"(2) A "\<equiv>E"(2) by blast
  AOT_hence 1: \<open>\<box>s \<Turnstile> r\<close> using "\<equiv>\<^sub>d\<^sub>fE" "&E"(1) "\<equiv>E"(1) "lem2:1" "true-in-s" by blast
  AOT_have \<open>s \<Turnstile> \<not>\<box>r\<close> using asm[THEN "\<forall>E"(1)[rotated, OF "log-prop-prop:2"], THEN "\<equiv>E"(2)] B by blast
  AOT_hence \<open>\<not>s \<Turnstile> \<box>r\<close>
    using "sit-classical:1"[THEN "\<rightarrow>E", OF asm, THEN "\<forall>E"(1)[rotated, OF "log-prop-prop:2"], THEN "\<equiv>E"(1)] by blast
  AOT_hence \<open>\<box>s \<Turnstile> r & \<not>s \<Turnstile> \<box>r\<close> using 1 "&I" by blast
  AOT_thus \<open>\<exists>r (\<box>s \<Turnstile> r & \<not>s \<Turnstile> \<box>r)\<close> by (rule "\<exists>I")
qed

AOT_theorem "sit-classical:6":
  \<open>\<exists>s \<forall>p (s \<Turnstile> p \<equiv> p)\<close>
proof -
  have "cond-prop": \<open>ConditionOnPropositionalProperties (\<lambda> \<Pi> . \<guillemotleft>\<exists>q (q & \<Pi> = [\<lambda>y q])\<guillemotright>)\<close>
  proof (safe intro!: "cond-prop[I]" GEN "\<rightarrow>I")
    fix F
    AOT_modally_strict {
      AOT_assume \<open>\<exists>q (q & F = [\<lambda>y q])\<close>
      then AOT_obtain q where \<open>q & F = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
      AOT_hence \<open>F = [\<lambda>y q]\<close> using "&E" by blast
      AOT_hence \<open>\<exists>q F = [\<lambda>y q]\<close> by (rule "\<exists>I")
      AOT_thus \<open>Propositional([F])\<close>
        by (metis "\<equiv>\<^sub>d\<^sub>fI" "prop-prop1")
    }
  qed
  AOT_have \<open>\<exists>s \<forall>F (s[F] \<equiv> \<exists>q (q & F = [\<lambda>y q]))\<close> using "comp-sit:1"[OF "cond-prop"].
  then AOT_obtain s\<^sub>0 where s\<^sub>0_prop: \<open>\<forall>F (s\<^sub>0[F] \<equiv> \<exists>q (q & F = [\<lambda>y q]))\<close>
    using "Situation.\<exists>E"[rotated] by meson
  AOT_have \<open>\<forall>p (s\<^sub>0 \<Turnstile> p \<equiv> p)\<close>
  proof(safe intro!: GEN "\<equiv>I" "\<rightarrow>I")
    fix p
    AOT_assume \<open>s\<^sub>0 \<Turnstile> p\<close> (* TODO: PLM: missing subscript in assumption and rest of proof (line below \<theta>) *)
    AOT_hence \<open>s\<^sub>0[\<lambda>y p]\<close> using lem1[THEN "\<rightarrow>E", OF Situation.\<psi>, THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>\<exists>q (q & [\<lambda>y p] = [\<lambda>y q])\<close>
      using s\<^sub>0_prop[THEN "\<forall>E"(1)[rotated, OF "prop-prop2:2"], THEN "\<equiv>E"(1)] by blast
    then AOT_obtain q\<^sub>1 where q\<^sub>1_prop: \<open>q\<^sub>1 & [\<lambda>y p] = [\<lambda>y q\<^sub>1]\<close> using "\<exists>E"[rotated] by blast
    AOT_hence \<open>p = q\<^sub>1\<close> by (metis "&E"(2) "\<equiv>E"(2) "p-identity-thm2:3")
    AOT_thus \<open>p\<close> using q\<^sub>1_prop[THEN "&E"(1)] "rule=E" id_sym by fast
  next
    fix p
    AOT_assume \<open>p\<close>
    moreover AOT_have \<open>[\<lambda>y p] = [\<lambda>y p]\<close> by (simp add: "rule=I:1"[OF "prop-prop2:2"])
    ultimately AOT_have \<open>p & [\<lambda>y p] = [\<lambda>y p]\<close> using "&I" by blast
    AOT_hence \<open>\<exists>q (q & [\<lambda>y p] = [\<lambda>y q])\<close> by (rule "\<exists>I")
    AOT_hence \<open>s\<^sub>0[\<lambda>y p]\<close>
      using s\<^sub>0_prop[THEN "\<forall>E"(1)[rotated, OF "prop-prop2:2"], THEN "\<equiv>E"(2)] by blast
    AOT_thus \<open>s\<^sub>0 \<Turnstile> p\<close> using lem1[THEN "\<rightarrow>E", OF Situation.\<psi>, THEN "\<equiv>E"(2)] by blast
  qed
  AOT_hence \<open>\<forall>p (s\<^sub>0 \<Turnstile> p \<equiv> p)\<close> using "&I" by blast
  AOT_thus \<open>\<exists>s \<forall>p (s \<Turnstile> p \<equiv> p)\<close> by (rule "Situation.\<exists>I")
qed

AOT_define PossibleWorld :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>PossibleWorld'(_')\<close>)
  "world:1": \<open>PossibleWorld(x) \<equiv>\<^sub>d\<^sub>f Situation(x) & \<diamond>\<forall>p(x \<Turnstile> p \<equiv> p)\<close>

AOT_theorem "world:2": \<open>\<exists>x PossibleWorld(x)\<close>
proof -
  AOT_obtain s where s_prop: \<open>\<forall>p (s \<Turnstile> p \<equiv> p)\<close>
    using "sit-classical:6" "Situation.\<exists>E"[rotated] by meson
  AOT_have \<open>\<forall>p (s \<Turnstile> p \<equiv> p)\<close>
  proof(safe intro!: GEN "\<equiv>I" "\<rightarrow>I")
    fix p
    AOT_assume \<open>s \<Turnstile> p\<close>
    AOT_thus \<open>p\<close>
      using s_prop[THEN "\<forall>E"(2), THEN "\<equiv>E"(1)] by blast
  next
    fix p
    AOT_assume \<open>p\<close>
    AOT_thus \<open>s \<Turnstile> p\<close>
      using s_prop[THEN "\<forall>E"(2), THEN "\<equiv>E"(2)] by blast
  qed
  AOT_hence \<open>\<diamond>\<forall>p (s \<Turnstile> p \<equiv> p)\<close> by (metis "T\<diamond>"[THEN "\<rightarrow>E"])
  AOT_hence \<open>\<diamond>\<forall>p (s \<Turnstile> p \<equiv> p)\<close> using s_prop "&I" by blast
  AOT_hence \<open>PossibleWorld(s)\<close> using "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] Situation.\<psi> "&I" by blast
  AOT_thus \<open>\<exists>x PossibleWorld(x)\<close> by (rule "\<exists>I")
qed

AOT_theorem "world:3": \<open>PossibleWorld(\<kappa>) \<rightarrow> \<kappa>\<down>\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>PossibleWorld(\<kappa>)\<close>
  AOT_hence \<open>Situation(\<kappa>)\<close> using "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_hence \<open>A!\<kappa>\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "&E"(1) situations)
  AOT_thus \<open>\<kappa>\<down>\<close> by (metis "russell-axiom[exe,1].\<psi>_denotes_asm")
qed

AOT_theorem "rigid-pw:1": \<open>PossibleWorld(x) \<equiv> \<box>PossibleWorld(x)\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>PossibleWorld(x)\<close>
  AOT_hence \<open>Situation(x) & \<diamond>\<forall>p(x \<Turnstile> p \<equiv> p)\<close>
    using "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_hence \<open>\<box>Situation(x) & \<box>\<diamond>\<forall>p(x \<Turnstile> p \<equiv> p)\<close>
    by (metis "S5Basic:1" "&I" "&E"(1) "&E"(2) "\<equiv>E"(1) "possit-sit:1")
  AOT_hence 0: \<open>\<box>(Situation(x) & \<diamond>\<forall>p(x \<Turnstile> p \<equiv> p))\<close>
    by (metis "KBasic:3" "\<equiv>E"(2))
  AOT_show \<open>\<box>PossibleWorld(x)\<close>
    by (AOT_subst \<open>\<guillemotleft>PossibleWorld(x)\<guillemotright>\<close> \<open>\<guillemotleft>Situation(x) & \<diamond>\<forall>p(x \<Turnstile> p \<equiv> p)\<guillemotright>\<close>)
       (auto simp: "\<equiv>Df" "world:1" 0)
next
  AOT_show \<open>PossibleWorld(x)\<close> if \<open>\<box>PossibleWorld(x)\<close>
    using that "qml:2"[axiom_inst, THEN "\<rightarrow>E"] by blast
qed

AOT_theorem "rigid-pw:2": \<open>\<diamond>PossibleWorld(x) \<equiv> PossibleWorld(x)\<close>
  using "rigid-pw:1" by (meson "RE\<diamond>" "S5Basic:2" "\<equiv>E"(2) "\<equiv>E"(6) "Commutativity of \<equiv>")

AOT_theorem "rigid-pw:3": \<open>\<diamond>PossibleWorld(x) \<equiv> \<box>PossibleWorld(x)\<close>
  using "rigid-pw:1" "rigid-pw:2" by (meson "\<equiv>E"(5))

AOT_theorem "rigid-pw:4": \<open>\<^bold>\<A>PossibleWorld(x) \<equiv> PossibleWorld(x)\<close>
  by (metis "Act-Sub:3" "deduction-theorem" "\<equiv>I" "\<equiv>E"(6) "nec-imp-act" "rigid-pw:1" "rigid-pw:2")

AOT_register_rigid_restricted_type
  PossibleWorld: \<open>PossibleWorld(\<kappa>)\<close>
proof
  AOT_modally_strict {
    AOT_show \<open>\<exists>x PossibleWorld(x)\<close> using "world:2".
  }
next
  AOT_modally_strict {
    AOT_show \<open>PossibleWorld(\<kappa>) \<rightarrow> \<kappa>\<down>\<close> for \<kappa> using "world:3".
  }
next
  AOT_modally_strict {
    AOT_show \<open>\<box>(PossibleWorld(\<alpha>) \<rightarrow> \<box>PossibleWorld(\<alpha>))\<close> for \<alpha>
      by (meson RN "deduction-theorem" "\<equiv>E"(1) "rigid-pw:1") 
  }
qed
AOT_register_variable_names
  PossibleWorld: w

AOT_theorem "world-pos": \<open>Possible(w)\<close>
proof (safe intro!: pos[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "\<equiv>\<^sub>d\<^sub>fE"[OF "world:1", OF PossibleWorld.\<psi>, THEN "&E"(1)])
  AOT_have \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
    using "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF PossibleWorld.\<psi>, THEN "&E"(2)].
  AOT_hence \<open>\<diamond>\<forall>p (w \<Turnstile> p \<rightarrow> p)\<close>
  proof (rule "RM\<diamond>"[THEN "\<rightarrow>E", rotated]; safe intro!: "\<rightarrow>I" GEN)
    AOT_modally_strict {
      fix p
      AOT_assume \<open>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
      AOT_hence \<open>w \<Turnstile> p \<equiv> p\<close> using "\<forall>E"(2) by blast
      moreover AOT_assume \<open>w \<Turnstile> p\<close>
      ultimately AOT_show p using "\<equiv>E"(1) by blast
    }
  qed
  AOT_hence 0: \<open>\<diamond>(Situation(w) & \<forall>p (w \<Turnstile> p \<rightarrow> p))\<close>
    using "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF PossibleWorld.\<psi>, THEN "&E"(1), THEN "possit-sit:1"[THEN "\<equiv>E"(1)]]
    by (metis "KBasic:16" "&I" "vdash-properties:10")
  AOT_show \<open>\<diamond>Actual(w)\<close>
    by (AOT_subst \<open>\<guillemotleft>Actual(w)\<guillemotright>\<close> \<open>\<guillemotleft>Situation(w) & \<forall>p (w \<Turnstile> p \<rightarrow> p)\<guillemotright>\<close>)
       (auto simp: actual "\<equiv>Df" 0)
qed

AOT_theorem "world-cons:1": \<open>Consistent(w)\<close>
  using "world-pos"
  using "pos-cons-sit:1"[unconstrain s, THEN "\<rightarrow>E", THEN "\<rightarrow>E"]
  by (meson "\<equiv>\<^sub>d\<^sub>fE" "&E"(1) pos)

AOT_theorem "world-cons:2": \<open>\<not>TrivialSituation(w)\<close>
proof(rule "raa-cor:2")
  AOT_assume \<open>TrivialSituation(w)\<close>
  AOT_hence \<open>Situation(w) & \<forall>p w \<Turnstile> p\<close> using "df-null-trivial:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_hence 0: \<open>\<box>w \<Turnstile> (\<exists>p (p & \<not>p))\<close> using "&E"
    by (metis "Buridan\<diamond>" "T\<diamond>" "&E"(2) "\<equiv>E"(1) "lem2:3"[unconstrain s, THEN "\<rightarrow>E"] "log-prop-prop:2" "rule-ui:1"
              "universal-cor" "vdash-properties:10")
  AOT_have \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p)\<close> using PossibleWorld.\<psi> "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2)] by metis
  AOT_hence \<open>\<forall>p \<diamond>(w \<Turnstile> p \<equiv> p)\<close> using "Buridan\<diamond>"[THEN "\<rightarrow>E"] by blast
  AOT_hence \<open>\<diamond>(w \<Turnstile> (\<exists>p (p & \<not>p)) \<equiv> (\<exists>p (p & \<not>p)))\<close>
    by (metis "log-prop-prop:2" "rule-ui:1")
  AOT_hence \<open>\<diamond>(w \<Turnstile> (\<exists>p (p & \<not>p)) \<rightarrow> (\<exists>p (p & \<not>p)))\<close>
    using "RM\<diamond>"[THEN "\<rightarrow>E"] "deduction-theorem" "\<equiv>E"(1) by meson
  AOT_hence \<open>\<diamond>(\<exists>p (p & \<not>p))\<close> using 0
    by (metis "KBasic2:4" "\<equiv>E"(1) "vdash-properties:10")
  moreover AOT_have \<open>\<not>\<diamond>(\<exists>p (p & \<not>p))\<close>
    by (metis "instantiation" "KBasic2:1" RN "\<equiv>E"(1) "raa-cor:2")
  ultimately AOT_show \<open>\<diamond>(\<exists>p (p & \<not>p)) & \<not>\<diamond>(\<exists>p (p & \<not>p))\<close> using "&I" by blast
qed

AOT_theorem "rigid-truth-at:1": \<open>w \<Turnstile> p \<equiv> \<box>w \<Turnstile> p\<close>
  using "lem2:1"[unconstrain s, THEN "\<rightarrow>E", OF PossibleWorld.\<psi>[THEN "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(1)]].

AOT_theorem "rigid-truth-at:2": \<open>\<diamond>w \<Turnstile> p \<equiv> w \<Turnstile> p\<close>
  using "lem2:2"[unconstrain s, THEN "\<rightarrow>E", OF PossibleWorld.\<psi>[THEN "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(1)]].

AOT_theorem "rigid-truth-at:3": \<open>\<diamond>w \<Turnstile> p \<equiv> \<box>w \<Turnstile> p\<close>
  using "lem2:3"[unconstrain s, THEN "\<rightarrow>E", OF PossibleWorld.\<psi>[THEN "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(1)]].

AOT_theorem "rigid-truth-at:4": \<open>\<^bold>\<A>w \<Turnstile> p \<equiv> w \<Turnstile> p\<close>
  using "lem2:4"[unconstrain s, THEN "\<rightarrow>E", OF PossibleWorld.\<psi>[THEN "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(1)]].

AOT_theorem "rigid-truth-at:5": \<open>\<not>w \<Turnstile> p \<equiv> \<box>\<not>w \<Turnstile> p\<close>
  using "lem2:5"[unconstrain s, THEN "\<rightarrow>E", OF PossibleWorld.\<psi>[THEN "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(1)]].

AOT_define Maximal :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>Maximal'(_')\<close>)
  max: \<open>Maximal(s) \<equiv>\<^sub>d\<^sub>f \<forall>p (s \<Turnstile> p \<or> s \<Turnstile> \<not>p)\<close>

AOT_theorem "world-max": \<open>Maximal(w)\<close>
proof(safe intro!: "\<equiv>\<^sub>d\<^sub>fI"[OF max] "&I" PossibleWorld.\<psi>[THEN "\<equiv>\<^sub>d\<^sub>fE"[OF "world:1"], THEN "&E"(1)] GEN)
  fix q
  AOT_have \<open>\<diamond>(w \<Turnstile> q \<or> w \<Turnstile> \<not>q)\<close>
  proof(rule "RM\<diamond>"[THEN "\<rightarrow>E"]; (rule "\<rightarrow>I")?)
    AOT_modally_strict {
      AOT_assume \<open>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
      AOT_hence \<open>w \<Turnstile> q \<equiv> q\<close> and \<open>w \<Turnstile> \<not>q \<equiv> \<not>q\<close>
        using "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] by blast+
      AOT_thus \<open>w \<Turnstile> q \<or> w \<Turnstile> \<not>q\<close>
        by (metis "\<or>I"(1) "\<or>I"(2) "\<equiv>E"(3) "reductio-aa:1")
    }
  next
    AOT_show \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
      using PossibleWorld.\<psi>[THEN "\<equiv>\<^sub>d\<^sub>fE"[OF "world:1"], THEN "&E"(2)].
  qed
  AOT_hence \<open>\<diamond>w \<Turnstile> q \<or> \<diamond>w \<Turnstile> \<not>q\<close>
    using "KBasic2:2"[THEN "\<equiv>E"(1)] by blast
  AOT_thus \<open>w \<Turnstile> q \<or> w \<Turnstile> \<not>q\<close>
    using "lem2:2"[unconstrain s, THEN "\<rightarrow>E", unvarify p, OF PossibleWorld.\<psi>[THEN "\<equiv>\<^sub>d\<^sub>fE"[OF "world:1"], THEN "&E"(1)], THEN "\<equiv>E"(1), OF "log-prop-prop:2"]
    by (metis "\<or>I"(1) "\<or>I"(2) "\<or>E"(3) "raa-cor:2")
qed

AOT_theorem "world=maxpos:1": \<open>Maximal(x) \<rightarrow> \<box>Maximal(x)\<close>
proof (AOT_subst \<open>\<guillemotleft>Maximal(x)\<guillemotright>\<close> \<open>\<guillemotleft>Situation(x) & \<forall>p (x \<Turnstile> p \<or> x \<Turnstile> \<not>p)\<guillemotright>\<close>;
       safe intro!: max "\<equiv>Df" "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume sit_x: \<open>Situation(x)\<close>
  AOT_hence nec_sit_x: \<open>\<box>Situation(x)\<close> by (metis "\<equiv>E"(1) "possit-sit:1")
  AOT_assume \<open>\<forall>p (x \<Turnstile> p \<or> x \<Turnstile> \<not>p)\<close>
  AOT_hence \<open>x \<Turnstile> p \<or> x \<Turnstile> \<not>p\<close> for p using "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] by blast
  AOT_hence \<open>\<box>x \<Turnstile> p \<or> \<box>x \<Turnstile> \<not>p\<close> for p
    using "lem2:1"[unconstrain s, THEN "\<rightarrow>E", OF sit_x, unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)]
    by (metis "\<or>I"(1) "\<or>I"(2) "\<or>E"(2) "raa-cor:1")
  AOT_hence \<open>\<box>(x \<Turnstile> p \<or> x \<Turnstile> \<not>p)\<close> for p by (metis "KBasic:15" "vdash-properties:10")
  AOT_hence \<open>\<forall>p \<box>(x \<Turnstile> p \<or> x \<Turnstile> \<not>p)\<close> by (rule GEN)
  AOT_hence \<open>\<box>\<forall>p (x \<Turnstile> p \<or> x \<Turnstile> \<not>p)\<close> by (rule BF[THEN "\<rightarrow>E"])
  AOT_thus \<open>\<box>(Situation(x) & \<forall>p (x \<Turnstile> p \<or> x \<Turnstile> \<not>p))\<close>
    using nec_sit_x by (metis "KBasic:3" "&I" "\<equiv>E"(2))
qed

AOT_theorem "world=maxpos:2": \<open>PossibleWorld(x) \<equiv> Maximal(x) & Possible(x)\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I" "&I" "world-pos"[unconstrain w, THEN "\<rightarrow>E"] "world-max"[unconstrain w, THEN "\<rightarrow>E"]; frule "&E"(2); drule "&E"(1))
  AOT_assume pos_x: \<open>Possible(x)\<close>
  AOT_have \<open>\<diamond>(Situation(x) & \<forall>p(x \<Turnstile> p \<rightarrow> p))\<close>
    apply (AOT_subst_rev \<open>\<guillemotleft>Actual(x)\<guillemotright>\<close> \<open>\<guillemotleft>Situation(x) & \<forall>p(x \<Turnstile> p \<rightarrow> p)\<guillemotright>\<close>)
     using actual "\<equiv>Df" apply presburger
    using "\<equiv>\<^sub>d\<^sub>fE" "&E"(2) pos pos_x by blast
  AOT_hence 0: \<open>\<diamond>\<forall>p(x \<Turnstile> p \<rightarrow> p)\<close>
    by (metis "KBasic2:3" "&E"(2) "vdash-properties:6")
  AOT_assume max_x: \<open>Maximal(x)\<close>
  AOT_hence sit_x: \<open>Situation(x)\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" max_x "&E"(1) max)
  AOT_have \<open>\<box>Maximal(x)\<close> using "world=maxpos:1"[THEN "\<rightarrow>E", OF max_x] by simp
  moreover AOT_have \<open>\<box>Maximal(x) \<rightarrow> \<box>(\<forall>p(x \<Turnstile> p \<rightarrow> p) \<rightarrow> \<forall>p (x \<Turnstile> p \<equiv> p))\<close>
  proof(safe intro!: "\<rightarrow>I" RM GEN)
    AOT_modally_strict {
      fix p
      AOT_assume 0: \<open>Maximal(x)\<close>
      AOT_assume 1: \<open>\<forall>p (x \<Turnstile> p \<rightarrow> p)\<close>
      AOT_show \<open>x \<Turnstile> p \<equiv> p\<close>
      proof(safe intro!: "\<equiv>I" "\<rightarrow>I" 1[THEN "\<forall>E"(2), THEN "\<rightarrow>E"]; rule "raa-cor:1")
        AOT_assume \<open>\<not>x \<Turnstile> p\<close>
        AOT_hence \<open>x \<Turnstile> \<not>p\<close>
          using 0[THEN "\<equiv>\<^sub>d\<^sub>fE"[OF max], THEN "&E"(2), THEN "\<forall>E"(2)]
                1 by (metis "\<or>E"(2))
        AOT_hence \<open>\<not>p\<close> using 1[THEN "\<forall>E"(1), OF "log-prop-prop:2", THEN "\<rightarrow>E"] by blast
        moreover AOT_assume p
        ultimately AOT_show \<open>p & \<not>p\<close> using "&I" by blast
      qed
    }
  qed
  ultimately AOT_have \<open>\<box>(\<forall>p(x \<Turnstile> p \<rightarrow> p) \<rightarrow> \<forall>p (x \<Turnstile> p \<equiv> p))\<close> using "\<rightarrow>E" by blast
  AOT_hence \<open>\<diamond>\<forall>p(x \<Turnstile> p \<rightarrow> p) \<rightarrow> \<diamond>\<forall>p(x \<Turnstile> p \<equiv> p)\<close> by (metis "KBasic:13"[THEN "\<rightarrow>E"])
  AOT_hence \<open>\<diamond>\<forall>p(x \<Turnstile> p \<equiv> p)\<close> using 0 "\<rightarrow>E" by blast
  AOT_thus \<open>PossibleWorld(x)\<close> using "\<equiv>\<^sub>d\<^sub>fI"[OF "world:1", OF "&I", OF sit_x] by blast
qed

AOT_define "nec-impl-p:1" :: \<open>\<phi> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (infixl \<open>\<Rightarrow>\<close> 26)
  "nec-impl-p:1": \<open>p \<Rightarrow> q \<equiv>\<^sub>d\<^sub>f \<box>(p \<rightarrow> q)\<close>
AOT_define "nec-impl-p:2" :: \<open>\<phi> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (infixl \<open>\<Leftrightarrow>\<close> 21)
  "nec-impl-p:2": \<open>p \<Leftrightarrow> q \<equiv>\<^sub>d\<^sub>f (p \<Rightarrow> q) & (q \<Rightarrow> p)\<close>

AOT_theorem "nec-equiv-nec-im": \<open>p \<Leftrightarrow> q \<equiv> \<box>(p \<equiv> q)\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>p \<Leftrightarrow> q\<close>
  AOT_hence \<open>(p \<Rightarrow> q)\<close> and \<open>(q \<Rightarrow> p)\<close>
    using "nec-impl-p:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_hence \<open>\<box>(p \<rightarrow> q)\<close> and \<open>\<box>(q \<rightarrow> p)\<close>
    using "nec-impl-p:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast+
  AOT_thus \<open>\<box>(p \<equiv> q)\<close> by (metis "KBasic:4" "&I" "\<equiv>E"(2))
next
  AOT_assume \<open>\<box>(p \<equiv> q)\<close>
  AOT_hence \<open>\<box>(p \<rightarrow> q)\<close> and \<open>\<box>(q \<rightarrow> p)\<close>  using "KBasic:4" "&E" "\<equiv>E"(1) by blast+
  AOT_hence \<open>(p \<Rightarrow> q)\<close> and \<open>(q \<Rightarrow> p)\<close>
    using "nec-impl-p:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast+
  AOT_thus \<open>p \<Leftrightarrow> q\<close> using "nec-impl-p:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" by blast
qed

(* TODO: PLM: discuss these; still not in PLM *)
AOT_theorem world_closed_lem_1_a: \<open>(s \<Turnstile> (\<phi> & \<psi>)) \<rightarrow> (\<forall>p (s \<Turnstile> p \<equiv> p) \<rightarrow> (s \<Turnstile> \<phi> & s \<Turnstile> \<psi>))\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_assume \<open>\<forall> p (s \<Turnstile> p \<equiv> p)\<close>
  AOT_hence \<open>s \<Turnstile> (\<phi> & \<psi>) \<equiv> (\<phi> & \<psi>)\<close> and \<open>s \<Turnstile> \<phi> \<equiv> \<phi>\<close> and \<open>s \<Turnstile> \<psi> \<equiv> \<psi>\<close>
    using "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] by blast+
  moreover AOT_assume \<open>s \<Turnstile> (\<phi> & \<psi>)\<close>
  ultimately AOT_show \<open>s \<Turnstile> \<phi> & s \<Turnstile> \<psi>\<close>
    by (metis "&I" "&E"(1) "&E"(2) "\<equiv>E"(1) "\<equiv>E"(2))
qed

AOT_theorem world_closed_lem_1_b: \<open>(s \<Turnstile> \<phi> & (\<phi> \<rightarrow> q)) \<rightarrow> (\<forall>p (s \<Turnstile> p \<equiv> p) \<rightarrow> s \<Turnstile> q)\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_assume \<open>\<forall> p (s \<Turnstile> p \<equiv> p)\<close>
  AOT_hence \<open>s \<Turnstile> \<phi> \<equiv> \<phi>\<close> for \<phi> using "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] by blast
  moreover AOT_assume \<open>s \<Turnstile> \<phi> & (\<phi> \<rightarrow> q)\<close>
  ultimately AOT_show \<open>s \<Turnstile> q\<close>
    by (metis "&E"(1) "&E"(2) "\<equiv>E"(1) "\<equiv>E"(2) "vdash-properties:10")
qed

AOT_theorem world_closed_lem_1_c: \<open>(s \<Turnstile> \<phi> & s \<Turnstile> (\<phi> \<rightarrow> \<psi>)) \<rightarrow> (\<forall>p (s \<Turnstile> p \<equiv> p) \<rightarrow> s \<Turnstile> \<psi>)\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_assume \<open>\<forall> p (s \<Turnstile> p \<equiv> p)\<close>
  AOT_hence \<open>s \<Turnstile> \<phi> \<equiv> \<phi>\<close> for \<phi> using "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] by blast
  moreover AOT_assume \<open>s \<Turnstile> \<phi> & s \<Turnstile> (\<phi> \<rightarrow> \<psi>)\<close>
  ultimately AOT_show \<open>s \<Turnstile> \<psi>\<close>
    by (metis "&E"(1) "&E"(2) "\<equiv>E"(1) "\<equiv>E"(2) "vdash-properties:10")
qed

AOT_theorem "world-closed-lem:1[0]": \<open>q \<rightarrow> (\<forall>p (s \<Turnstile> p \<equiv> p) \<rightarrow> s \<Turnstile> q)\<close>
  by (meson "deduction-theorem" "\<equiv>E"(2) "log-prop-prop:2" "rule-ui:1")

AOT_theorem "world-closed-lem:1[1]": \<open>s \<Turnstile> p\<^sub>1 & (p\<^sub>1 \<rightarrow> q) \<rightarrow> (\<forall>p (s \<Turnstile> p \<equiv> p) \<rightarrow> s \<Turnstile> q)\<close>
  using world_closed_lem_1_b.

AOT_theorem "world-closed-lem:1[2]": \<open>s \<Turnstile> p\<^sub>1 & s \<Turnstile> p\<^sub>2 & ((p\<^sub>1 & p\<^sub>2) \<rightarrow> q) \<rightarrow> (\<forall>p (s \<Turnstile> p \<equiv> p) \<rightarrow> s \<Turnstile> q)\<close>
  using world_closed_lem_1_b world_closed_lem_1_a
  by (metis (full_types) "&I" "&E" "\<rightarrow>I" "\<rightarrow>E")

AOT_theorem "world-closed-lem:1[3]": \<open>s \<Turnstile> p\<^sub>1 & s \<Turnstile> p\<^sub>2 & s \<Turnstile> p\<^sub>3 & ((p\<^sub>1 & p\<^sub>2 & p\<^sub>3) \<rightarrow> q) \<rightarrow> (\<forall>p (s \<Turnstile> p \<equiv> p) \<rightarrow> s \<Turnstile> q)\<close>
  using world_closed_lem_1_b world_closed_lem_1_a
  by (metis (full_types) "&I" "&E" "\<rightarrow>I" "\<rightarrow>E")

AOT_theorem "world-closed-lem:1[4]": \<open>s \<Turnstile> p\<^sub>1 & s \<Turnstile> p\<^sub>2 & s \<Turnstile> p\<^sub>3 & s \<Turnstile> p\<^sub>4 & ((p\<^sub>1 & p\<^sub>2 & p\<^sub>3 & p\<^sub>4) \<rightarrow> q) \<rightarrow> (\<forall>p (s \<Turnstile> p \<equiv> p) \<rightarrow> s \<Turnstile> q)\<close>
  using world_closed_lem_1_b world_closed_lem_1_a
  by (metis (full_types) "&I" "&E" "\<rightarrow>I" "\<rightarrow>E")

(* TODO: PLM: discuss further - postpone for now *)

AOT_theorem "coherent:1": \<open>w \<Turnstile> \<not>p \<equiv> \<not>w \<Turnstile> p\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume 1: \<open>w \<Turnstile> \<not>p\<close>
  AOT_show \<open>\<not>w \<Turnstile> p\<close>
  proof(rule "raa-cor:2")
    AOT_assume \<open>w \<Turnstile> p\<close>
    AOT_hence \<open>w \<Turnstile> p & w \<Turnstile> \<not>p\<close> using 1 "&I" by blast
    AOT_hence \<open>\<exists>q (w \<Turnstile> q & w \<Turnstile> \<not>q)\<close> by (rule "\<exists>I")
    moreover AOT_have \<open>\<not>\<exists>q (w \<Turnstile> q & w \<Turnstile> \<not>q)\<close>
      using "world-cons:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"[OF cons], THEN "&E"(2)].
    ultimately AOT_show \<open>\<exists>q (w \<Turnstile> q & w \<Turnstile> \<not>q) & \<not>\<exists>q (w \<Turnstile> q & w \<Turnstile> \<not>q)\<close> using "&I" by blast
  qed
next
  AOT_assume \<open>\<not>w \<Turnstile> p\<close>
  AOT_thus \<open>w \<Turnstile> \<not>p\<close>
    using "world-max"[THEN "\<equiv>\<^sub>d\<^sub>fE"[OF max], THEN "&E"(2)]
    by (metis "\<or>E"(2) "log-prop-prop:2" "rule-ui:1")
qed

AOT_theorem "coherent:2": \<open>w \<Turnstile> p \<equiv> \<not>w \<Turnstile> \<not>p\<close>
  by (metis "coherent:1" "deduction-theorem" "\<equiv>I" "\<equiv>E"(1) "\<equiv>E"(2) "raa-cor:3")

AOT_theorem "act-world:1": \<open>\<exists>w \<forall>p (w \<Turnstile> p \<equiv> p)\<close>
proof -
  AOT_obtain s where s_prop: \<open>\<forall>p (s \<Turnstile> p \<equiv> p)\<close> using "sit-classical:6" "Situation.\<exists>E"[rotated] by meson
  AOT_hence \<open>\<diamond>\<forall>p (s \<Turnstile> p \<equiv> p)\<close>
    by (metis "T\<diamond>" "vdash-properties:10")
  AOT_hence \<open>PossibleWorld(s)\<close>
    using "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] Situation.\<psi> "&I" by blast
  AOT_hence \<open>PossibleWorld(s) & \<forall>p (s \<Turnstile> p \<equiv> p)\<close> using "&I" s_prop by blast
  thus ?thesis by (rule "\<exists>I")
qed

AOT_theorem "act-world:2": \<open>\<exists>!w Actual(w)\<close>
proof -
  AOT_obtain w where w_prop: \<open>\<forall>p (w \<Turnstile> p \<equiv> p)\<close> using "act-world:1" "PossibleWorld.\<exists>E"[rotated] by meson
  AOT_have sit_s: \<open>Situation(w)\<close> using PossibleWorld.\<psi> "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(1)] by blast
  show ?thesis
  proof (safe intro!: "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(2) "&I" GEN "\<rightarrow>I"
                      PossibleWorld.\<psi> actual[THEN "\<equiv>\<^sub>d\<^sub>fI"] sit_s "sit-identity"[unconstrain s, unconstrain s', THEN "\<rightarrow>E", THEN "\<rightarrow>E", THEN "\<equiv>E"(2)] "\<equiv>I"
                      w_prop[THEN "\<forall>E"(2), THEN "\<equiv>E"(1)])
    AOT_show \<open>PossibleWorld(w)\<close> using PossibleWorld.\<psi>.
  next
    AOT_show \<open>Situation(w)\<close>
      by (simp add: sit_s)
  next
    fix y p
    AOT_assume w_asm: \<open>PossibleWorld(y) & Actual(y)\<close>
    AOT_assume \<open>w \<Turnstile> p\<close>
    AOT_hence p: \<open>p\<close> using w_prop[THEN "\<forall>E"(2), THEN "\<equiv>E"(1)] by blast
    AOT_show \<open>y \<Turnstile> p\<close>
    proof(rule "raa-cor:1")
      AOT_assume \<open>\<not>y \<Turnstile> p\<close>
      AOT_hence \<open>y \<Turnstile> \<not>p\<close> by (metis "coherent:1"[unconstrain w, THEN "\<rightarrow>E"] "&E"(1) "\<equiv>E"(2) w_asm)
      AOT_hence \<open>\<not>p\<close>
        using w_asm[THEN "&E"(2), THEN actual[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2), THEN "\<forall>E"(1), rotated, OF "log-prop-prop:2"]
              "\<rightarrow>E" by blast
      AOT_thus \<open>p & \<not>p\<close> using p "&I" by blast
    qed
  next
    AOT_show \<open>w \<Turnstile> p\<close> if \<open>y \<Turnstile> p\<close> and \<open>PossibleWorld(y) & Actual(y)\<close> for p y
      using that(2)[THEN "&E"(2), THEN actual[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2), THEN "\<forall>E"(2),
                  THEN "\<rightarrow>E", OF that(1)]
            w_prop[THEN "\<forall>E"(2), THEN "\<equiv>E"(2)] by blast
  next
    AOT_show \<open>Situation(y)\<close> if \<open>PossibleWorld(y) & Actual(y)\<close> for y
      using that[THEN "&E"(1)] "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(1)] by blast
  next
    AOT_show \<open>Situation(w)\<close>
      using sit_s by blast
  qed(simp)
qed

AOT_theorem "pre-walpha": \<open>\<^bold>\<iota>w Actual(w)\<down>\<close>
  using "A-Exists:2" "RA[2]" "act-world:2" "\<equiv>E"(2) by blast

AOT_define TheActualWorld :: \<open>\<kappa>\<^sub>s\<close> (\<open>\<^bold>w\<^sub>\<alpha>\<close>)
  "w-alpha": \<open>\<^bold>w\<^sub>\<alpha> =\<^sub>d\<^sub>f \<^bold>\<iota>w Actual(w)\<close>

AOT_act_theorem "T-world:1": \<open>\<top> = \<^bold>w\<^sub>\<alpha>\<close>
proof -
  AOT_have true_den: \<open>\<top>\<down>\<close> using "A-descriptions" "rule-id-def:2:b[zero]" "the-true:1" "vdash-properties:10" by fast
  AOT_obtain x where x_def: \<open>x = \<top>\<close>
    by (metis "instantiation" "rule=I:1" "existential:1" id_sym true_den)
  AOT_have \<open>Situation(\<top>)\<close>
    using "T-T-value:1" "T-sit"[unvarify x, OF true_den, THEN "\<rightarrow>E"] by blast
  AOT_hence x_sit: \<open>Situation(x)\<close>
    using "rule=E"[rotated, OF x_def[symmetric]] by blast

  AOT_have w_alpha_def: \<open>\<^bold>w\<^sub>\<alpha> = \<^bold>\<iota>w Actual(w)\<close>
    by (simp add: "pre-walpha" "rule-id-def:1[zero]" "w-alpha")
  AOT_hence w_alpha_den: \<open>\<^bold>w\<^sub>\<alpha>\<down>\<close>
    using "pre-walpha" "rule-id-def:2:b[zero]" "w-alpha" by blast
  AOT_obtain y where y_def: \<open>y = \<^bold>w\<^sub>\<alpha>\<close>
    by (metis "instantiation" "existential:1" id_sym w_alpha_def "pre-walpha")
  AOT_have \<open>PossibleWorld(\<^bold>w\<^sub>\<alpha>) & Actual(\<^bold>w\<^sub>\<alpha>)\<close>
    using "y-in:2"[unvarify z, OF w_alpha_den, THEN "\<rightarrow>E", OF w_alpha_def].
  AOT_hence y_prop: \<open>PossibleWorld(y) & Actual(y)\<close>
    using "rule=E"[rotated, OF y_def[symmetric]] by fast
  AOT_hence y_sit: \<open>Situation(y)\<close>
    by (meson "\<equiv>\<^sub>d\<^sub>fE" "&E"(1) pos "world-pos"[unconstrain w, THEN "\<rightarrow>E"])

  AOT_have \<open>x = y\<close>
  proof(safe intro!: "sit-identity"[unconstrain s, unconstrain s', THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF y_sit, OF x_sit, THEN "\<equiv>E"(2)] GEN "\<equiv>I" "\<rightarrow>I")
    fix p
    AOT_assume \<open>x \<Turnstile> p\<close>
    AOT_hence \<open>x[\<lambda>y p]\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "&E"(2) "prop-enc" "true-in-s")
    AOT_hence \<open>\<top>[\<lambda>y p]\<close>
      using "rule=E"[rotated, OF x_def] by fast
    AOT_hence \<open>\<top>\<^bold>\<Sigma>p\<close> 
      by (metis "\<equiv>\<^sub>d\<^sub>fI" "&I" "prop-enc" true_den)
    AOT_hence p: \<open>p\<close> using "q-True:3" by (metis "\<equiv>E"(2)) 
    AOT_show \<open>y \<Turnstile> p\<close>
    proof(rule "raa-cor:1")
      AOT_assume \<open>\<not>y \<Turnstile> p\<close>
      AOT_hence \<open>y \<Turnstile> \<not>p\<close>
        by (metis "coherent:1"[unconstrain w, THEN "\<rightarrow>E"] "&E"(1) "\<equiv>E"(2) y_prop) 
      AOT_hence \<open>\<not>p\<close>
        using actual[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), THEN "\<forall>E"(1)[rotated, OF "log-prop-prop:2"], THEN "\<rightarrow>E", OF y_prop[THEN "&E"(2)]] by blast
      AOT_thus \<open>p & \<not>p\<close> using p "&I" by blast
    qed
  next
    fix p
    AOT_assume \<open>y \<Turnstile> p\<close>
    AOT_hence \<open>p\<close>
      using actual[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF y_prop[THEN "&E"(2)]] by blast
    AOT_hence \<open>\<top>\<^bold>\<Sigma>p\<close> by (metis "\<equiv>E"(1) "q-True:3")
    AOT_hence \<open>x\<^bold>\<Sigma>p\<close> using "rule=E"[rotated, OF x_def[symmetric]] by fast
    AOT_thus \<open>x \<Turnstile> p\<close>
      by (metis "\<equiv>\<^sub>d\<^sub>fI" "&I" "true-in-s" x_sit)
  qed
  AOT_thus \<open>\<top> = \<^bold>w\<^sub>\<alpha>\<close>
    using "rule=E"[rotated, OF x_def] "rule=E"[rotated, OF y_def] by (metis id_sym)
qed

AOT_act_theorem "T-world:2": \<open>p \<equiv> \<^bold>w\<^sub>\<alpha> = \<^bold>\<iota>x (ExtensionOf(x, p))\<close>
  by (metis "rule=E" "T-world:1" "deduction-theorem" "ext-p-tv:3" id_sym "\<equiv>I"
            "\<equiv>E"(1) "\<equiv>E"(2) "q-True:1")

AOT_act_theorem "truth-at-alpha": \<open>p \<equiv> \<^bold>w\<^sub>\<alpha> \<Turnstile> p\<close>
proof -
  AOT_have \<open>PossibleWorld(\<^bold>w\<^sub>\<alpha>)\<close>
    using "&E"(1) "pre-walpha" "rule-id-def:2:b[zero]" "vdash-properties:10" "w-alpha" "y-in:3" by blast
  AOT_hence sit_w_alpha: \<open>Situation(\<^bold>w\<^sub>\<alpha>)\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "&E"(1) "world:1")
  AOT_have w_alpha_den: \<open>\<^bold>w\<^sub>\<alpha>\<down>\<close>
    using "pre-walpha" "rule-id-def:2:b[zero]" "w-alpha" by blast
  AOT_have \<open>p \<equiv> \<top>\<^bold>\<Sigma>p\<close>
    using "q-True:3" by force
  moreover AOT_have \<open>\<top> = \<^bold>w\<^sub>\<alpha>\<close>
    using "T-world:1" by auto
  ultimately AOT_have \<open>p \<equiv> \<^bold>w\<^sub>\<alpha>\<^bold>\<Sigma>p\<close> using "rule=E" by fast
  moreover AOT_have \<open>\<^bold>w\<^sub>\<alpha> \<^bold>\<Sigma> p \<equiv> \<^bold>w\<^sub>\<alpha> \<Turnstile> p\<close>
    using lem1[unvarify x, OF w_alpha_den, THEN "\<rightarrow>E", OF sit_w_alpha]
    using "\<equiv>S"(1) "\<equiv>E"(1) "Commutativity of \<equiv>" "\<equiv>Df" sit_w_alpha "true-in-s" by blast
  ultimately AOT_show \<open>p \<equiv> \<^bold>w\<^sub>\<alpha> \<Turnstile> p\<close> by (metis "\<equiv>E"(5))
qed

AOT_theorem "alpha-world:1": \<open>PossibleWorld(\<^bold>w\<^sub>\<alpha>)\<close>
proof -
  AOT_have 0: \<open>\<^bold>w\<^sub>\<alpha> = \<^bold>\<iota>w Actual(w)\<close>
    using "pre-walpha" "rule-id-def:1[zero]" "w-alpha" by blast
  AOT_hence walpha_den: \<open>\<^bold>w\<^sub>\<alpha>\<down>\<close>
    by (metis "t=t-proper:1" "vdash-properties:6")
  AOT_have \<open>\<^bold>\<A>(PossibleWorld(\<^bold>w\<^sub>\<alpha>) & Actual(\<^bold>w\<^sub>\<alpha>))\<close>
    by (rule "actual-desc:2"[unvarify x, OF walpha_den, THEN "\<rightarrow>E"]) (fact 0)
  AOT_hence \<open>\<^bold>\<A>PossibleWorld(\<^bold>w\<^sub>\<alpha>)\<close> by (metis "Act-Basic:2" "&E"(1) "\<equiv>E"(1))
  AOT_thus \<open>PossibleWorld(\<^bold>w\<^sub>\<alpha>)\<close>
    using "rigid-pw:4"[unvarify x, OF walpha_den, THEN "\<equiv>E"(1)]
    by blast
qed

AOT_theorem "alpha-world:2": \<open>Maximal(\<^bold>w\<^sub>\<alpha>)\<close>
proof -
  AOT_have \<open>\<^bold>w\<^sub>\<alpha>\<down>\<close>
    using "pre-walpha" "rule-id-def:2:b[zero]" "w-alpha" by blast
  then AOT_obtain x where x_def: \<open>x = \<^bold>w\<^sub>\<alpha>\<close>
    by (metis "instantiation" "rule=I:1" "existential:1" id_sym)
  AOT_hence \<open>PossibleWorld(x)\<close> using "alpha-world:1" "rule=E" id_sym by fast
  AOT_hence \<open>Maximal(x)\<close> by (metis "world-max"[unconstrain w, THEN "\<rightarrow>E"]) 
  AOT_thus \<open>Maximal(\<^bold>w\<^sub>\<alpha>)\<close> using x_def "rule=E" by blast
qed

AOT_theorem "t-at-alpha-strict": \<open>\<^bold>w\<^sub>\<alpha> \<Turnstile> p \<equiv> \<^bold>\<A>p\<close>
proof -
  AOT_have 0: \<open>\<^bold>w\<^sub>\<alpha> = \<^bold>\<iota>w Actual(w)\<close>
    using "pre-walpha" "rule-id-def:1[zero]" "w-alpha" by blast
  AOT_hence walpha_den: \<open>\<^bold>w\<^sub>\<alpha>\<down>\<close>
    by (metis "t=t-proper:1" "vdash-properties:6")
  AOT_have 1: \<open>\<^bold>\<A>(PossibleWorld(\<^bold>w\<^sub>\<alpha>) & Actual(\<^bold>w\<^sub>\<alpha>))\<close>
    by (rule "actual-desc:2"[unvarify x, OF walpha_den, THEN "\<rightarrow>E"]) (fact 0)
  AOT_have walpha_sit: \<open>Situation(\<^bold>w\<^sub>\<alpha>)\<close>
    by (meson "\<equiv>\<^sub>d\<^sub>fE" "alpha-world:2" "&E"(1) max)
  {
    fix p
    AOT_have 2: \<open>Situation(x) \<rightarrow> (\<^bold>\<A>x \<Turnstile> p \<equiv> x \<Turnstile> p)\<close> for x using "lem2:4"[unconstrain s] by blast
    AOT_assume \<open>\<^bold>w\<^sub>\<alpha> \<Turnstile> p\<close>
    AOT_hence \<theta>: \<open>\<^bold>\<A>\<^bold>w\<^sub>\<alpha> \<Turnstile> p\<close>
      using 2[unvarify x, OF walpha_den, THEN "\<rightarrow>E", OF walpha_sit, THEN "\<equiv>E"(2)] by argo
    AOT_have 3: \<open>\<^bold>\<A>Actual(\<^bold>w\<^sub>\<alpha>)\<close>
      using "1" "Act-Basic:2" "&E"(2) "\<equiv>E"(1) by blast
    AOT_have \<open>\<^bold>\<A>(Situation(\<^bold>w\<^sub>\<alpha>) & \<forall>q(\<^bold>w\<^sub>\<alpha> \<Turnstile> q \<rightarrow> q))\<close>
      apply (AOT_subst_rev \<open>\<guillemotleft>Actual(\<^bold>w\<^sub>\<alpha>)\<guillemotright>\<close> \<open>\<guillemotleft>Situation(\<^bold>w\<^sub>\<alpha>) & \<forall>q(\<^bold>w\<^sub>\<alpha> \<Turnstile> q \<rightarrow> q)\<guillemotright>\<close>)
       using actual "\<equiv>Df" apply blast
      by (fact 3)
    AOT_hence \<open>\<^bold>\<A>\<forall>q(\<^bold>w\<^sub>\<alpha> \<Turnstile> q \<rightarrow> q)\<close> by (metis "Act-Basic:2" "&E"(2) "\<equiv>E"(1))
    AOT_hence \<open>\<forall>q \<^bold>\<A>(\<^bold>w\<^sub>\<alpha> \<Turnstile> q \<rightarrow> q)\<close>
      using "logic-actual-nec:3"[axiom_inst, THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>\<^bold>\<A>(\<^bold>w\<^sub>\<alpha> \<Turnstile> p \<rightarrow> p)\<close> using "\<forall>E"(2) by blast
    AOT_hence \<open>\<^bold>\<A>(\<^bold>w\<^sub>\<alpha> \<Turnstile> p) \<rightarrow> \<^bold>\<A>p\<close> by (metis "act-cond" "vdash-properties:10")
    AOT_hence \<open>\<^bold>\<A>p\<close> using \<theta> "\<rightarrow>E" by blast
  }
  AOT_hence 2: \<open>\<^bold>w\<^sub>\<alpha> \<Turnstile> p \<rightarrow> \<^bold>\<A>p\<close> for p by (rule "\<rightarrow>I")
  AOT_have walpha_sit: \<open>Situation(\<^bold>w\<^sub>\<alpha>)\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" "alpha-world:2" "&E"(1) max by blast
  show ?thesis
  proof(safe intro!: "\<equiv>I" "\<rightarrow>I" 2)
    AOT_assume actp: \<open>\<^bold>\<A>p\<close>
    AOT_show \<open>\<^bold>w\<^sub>\<alpha> \<Turnstile> p\<close>
    proof(rule "raa-cor:1")
      AOT_assume \<open>\<not>\<^bold>w\<^sub>\<alpha> \<Turnstile> p\<close>
      AOT_hence \<open>\<^bold>w\<^sub>\<alpha> \<Turnstile> \<not>p\<close>
        using "alpha-world:2"[THEN max[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2), THEN "\<forall>E"(1), OF "log-prop-prop:2"]
        by (metis "\<or>E"(2))
      AOT_hence \<open>\<^bold>\<A>\<not>p\<close>
        using 2[unvarify p, OF "log-prop-prop:2", THEN "\<rightarrow>E"] by blast
      AOT_hence \<open>\<not>\<^bold>\<A>p\<close> by (metis "\<not>\<not>I" "Act-Sub:1" "\<equiv>E"(4))
      AOT_thus \<open>\<^bold>\<A>p & \<not>\<^bold>\<A>p\<close> using actp "&I" by blast
    qed
  qed
qed

AOT_act_theorem "not-act": \<open>w \<noteq> \<^bold>w\<^sub>\<alpha> \<rightarrow> \<not>Actual(w)\<close>
proof (rule "\<rightarrow>I"; rule "raa-cor:2")
  AOT_assume \<open>w \<noteq> \<^bold>w\<^sub>\<alpha>\<close>
  AOT_hence 0: \<open>\<not>(w = \<^bold>w\<^sub>\<alpha>)\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "=-infix")
  AOT_have walpha_den: \<open>\<^bold>w\<^sub>\<alpha>\<down>\<close>
    using "pre-walpha" "rule-id-def:2:b[zero]" "w-alpha" by blast
  AOT_have walpha_sit: \<open>Situation(\<^bold>w\<^sub>\<alpha>)\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" "alpha-world:2" "&E"(1) max by blast
  AOT_assume act_w: \<open>Actual(w)\<close>
  AOT_hence w_sit: \<open>Situation(w)\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" actual "&E"(1))
  AOT_have sid: \<open>Situation(x') \<rightarrow> (w = x' \<equiv> \<forall>p (w \<Turnstile> p \<equiv> x' \<Turnstile> p))\<close> for x'
    using "sit-identity"[unconstrain s', unconstrain s, THEN "\<rightarrow>E", OF w_sit] by blast
  AOT_have \<open>w = \<^bold>w\<^sub>\<alpha>\<close>
  proof(safe intro!: GEN sid[unvarify x', OF walpha_den, THEN "\<rightarrow>E", OF walpha_sit, THEN "\<equiv>E"(2)] "\<equiv>I" "\<rightarrow>I")
    fix p
    AOT_assume \<open>w \<Turnstile> p\<close>
    AOT_hence \<open>p\<close> using actual[THEN "\<equiv>\<^sub>d\<^sub>fE", OF act_w, THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>\<^bold>\<A>p\<close>
      by (metis "RA[1]")
    AOT_thus \<open>\<^bold>w\<^sub>\<alpha> \<Turnstile> p\<close> using "t-at-alpha-strict"[THEN "\<equiv>E"(2)] by blast
  next
    fix p
    AOT_assume \<open>\<^bold>w\<^sub>\<alpha> \<Turnstile> p\<close>
    AOT_hence \<open>\<^bold>\<A>p\<close> using "t-at-alpha-strict"[THEN "\<equiv>E"(1)] by blast
    AOT_hence p: \<open>p\<close> using "logic-actual"[act_axiom_inst, THEN "\<rightarrow>E"] by blast
    AOT_show \<open>w \<Turnstile> p\<close>
    proof(rule "raa-cor:1")
      AOT_assume \<open>\<not>w \<Turnstile> p\<close>
      AOT_hence \<open>w \<Turnstile> \<not>p\<close>
        by (metis "coherent:1" "\<equiv>E"(2))
      AOT_hence \<open>\<not>p\<close>
        using actual[THEN "\<equiv>\<^sub>d\<^sub>fE", OF act_w, THEN "&E"(2), THEN "\<forall>E"(1), OF "log-prop-prop:2", THEN "\<rightarrow>E"] by blast
      AOT_thus \<open>p & \<not>p\<close> using p "&I" by blast
    qed
  qed
  AOT_thus \<open>w = \<^bold>w\<^sub>\<alpha> & \<not>(w = \<^bold>w\<^sub>\<alpha>)\<close> using 0 "&I" by blast
qed

AOT_act_theorem "w-alpha-part": \<open>Actual(s) \<equiv> s \<unlhd> \<^bold>w\<^sub>\<alpha>\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I" "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" GEN dest!:  "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fE"])
  AOT_show \<open>Situation(s)\<close> if \<open>Actual(s)\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" actual "&E"(1) that by blast
next
  AOT_show \<open>Situation(\<^bold>w\<^sub>\<alpha>)\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" "alpha-world:2" "&E"(1) max by blast
next
  fix p
  AOT_assume \<open>Actual(s)\<close>
  moreover AOT_assume \<open>s \<Turnstile> p\<close>
  ultimately AOT_have \<open>p\<close>
    using actual[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
  AOT_thus \<open>\<^bold>w\<^sub>\<alpha> \<Turnstile> p\<close>
     by (metis "\<equiv>E"(1) "truth-at-alpha")
next
  AOT_assume 0: \<open>Situation(s) & Situation(\<^bold>w\<^sub>\<alpha>) & \<forall>p (s \<Turnstile> p \<rightarrow> \<^bold>w\<^sub>\<alpha> \<Turnstile> p)\<close>
  AOT_hence \<open>s \<Turnstile> p \<rightarrow> \<^bold>w\<^sub>\<alpha> \<Turnstile> p\<close> for p
    using "&E" "\<forall>E"(2) by blast
  AOT_hence \<open>s \<Turnstile> p \<rightarrow> p\<close> for p
    by (metis "deduction-theorem" "\<equiv>E"(2) "truth-at-alpha" "vdash-properties:10")
  AOT_hence \<open>\<forall>p (s \<Turnstile> p \<rightarrow> p)\<close> by (rule GEN)
  AOT_thus \<open>Actual(s)\<close>
    using actual[THEN "\<equiv>\<^sub>d\<^sub>fI", OF "&I", OF 0[THEN "&E"(1), THEN "&E"(1)]] by blast
qed

AOT_act_theorem "act-world2:1": \<open>\<^bold>w\<^sub>\<alpha> \<Turnstile> p \<equiv> [\<lambda>y p]\<^bold>w\<^sub>\<alpha>\<close>
  apply (AOT_subst \<open>\<guillemotleft>[\<lambda>y p]\<^bold>w\<^sub>\<alpha>\<guillemotright>\<close> \<open>AOT_term_of_var p\<close>)
   apply (rule "beta-C-meta"[THEN "\<rightarrow>E", OF "prop-prop2:2", unvarify \<nu>\<^sub>1\<nu>\<^sub>n])
  using "pre-walpha" "rule-id-def:2:b[zero]" "w-alpha" apply blast
  using "\<equiv>E"(2) "Commutativity of \<equiv>" "truth-at-alpha" by blast

AOT_act_theorem "act-world2:2": \<open>p \<equiv> \<^bold>w\<^sub>\<alpha> \<Turnstile> [\<lambda>y p]\<^bold>w\<^sub>\<alpha>\<close>
proof -
  AOT_have \<open>p \<equiv> [\<lambda>y p]\<^bold>w\<^sub>\<alpha>\<close>
    apply (rule "beta-C-meta"[THEN "\<rightarrow>E", OF "prop-prop2:2", unvarify \<nu>\<^sub>1\<nu>\<^sub>n, symmetric])
    using "pre-walpha" "rule-id-def:2:b[zero]" "w-alpha" by blast
  also AOT_have \<open>\<dots> \<equiv> \<^bold>w\<^sub>\<alpha> \<Turnstile> [\<lambda>y p]\<^bold>w\<^sub>\<alpha>\<close>
    by (meson "log-prop-prop:2" "rule-ui:1" "truth-at-alpha" "universal-cor")
  finally show ?thesis.
qed

AOT_theorem "fund-lem:1": \<open>\<diamond>p \<rightarrow> \<diamond>\<exists>w (w \<Turnstile> p)\<close>
proof (rule "RM\<diamond>"; rule "\<rightarrow>I"; rule "raa-cor:1")
  AOT_modally_strict {
    AOT_obtain w where w_prop: \<open>\<forall>q (w \<Turnstile> q \<equiv> q)\<close>
      using "act-world:1" "PossibleWorld.\<exists>E"[rotated] by meson
    AOT_assume p: \<open>p\<close>
    AOT_assume 0: \<open>\<not>\<exists>w (w \<Turnstile> p)\<close>
    AOT_have \<open>\<forall>w \<not>(w \<Turnstile> p)\<close>
      apply (AOT_subst \<open>\<lambda> \<kappa> . \<guillemotleft>PossibleWorld(\<kappa>) \<rightarrow> \<not>\<kappa> \<Turnstile> p\<guillemotright>\<close> \<open>\<lambda> \<kappa> . \<guillemotleft>\<not>(PossibleWorld(\<kappa>) & \<kappa> \<Turnstile> p)\<guillemotright>\<close>)
      apply (metis "&I" "&E"(1) "&E"(2) "deduction-theorem" "\<equiv>I" "modus-tollens:2")
      using "0" "cqt-further:4" "vdash-properties:10" by blast
    AOT_hence \<open>\<not>(w \<Turnstile> p)\<close> using PossibleWorld.\<psi> "rule-ui:3" "vdash-properties:10" by blast
    AOT_hence \<open>\<not>p\<close> using w_prop[THEN "\<forall>E"(2), THEN "\<equiv>E"(2)] 
      by (metis "raa-cor:3")
    AOT_thus \<open>p & \<not>p\<close> using p "&I" by blast
  }
qed

AOT_theorem "fund-lem:2": \<open>\<diamond>\<exists>w (w \<Turnstile> p) \<rightarrow> \<exists>w (w \<Turnstile> p)\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>\<diamond>\<exists>w (w \<Turnstile> p)\<close>
  AOT_hence \<open>\<exists>w \<diamond>(w \<Turnstile> p)\<close> using "PossibleWorld.res-var-bound-reas[BF\<diamond>]"[THEN "\<rightarrow>E"] by auto
  then AOT_obtain w where \<open>\<diamond>(w \<Turnstile> p)\<close> using "PossibleWorld.\<exists>E"[rotated] by meson
  moreover AOT_have \<open>Situation(w)\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "&E"(1) pos "world-pos")
  ultimately AOT_have \<open>w \<Turnstile> p\<close>
    using "lem2:2"[unconstrain s, THEN "\<rightarrow>E"]  "\<equiv>E" by blast
  AOT_thus \<open>\<exists>w w \<Turnstile> p\<close> by (rule "PossibleWorld.\<exists>I")
qed

AOT_theorem "fund-lem:3": \<open>p \<rightarrow> \<forall>s(\<forall>q (s \<Turnstile> q \<equiv> q) \<rightarrow> s \<Turnstile> p)\<close>
proof(safe intro!: "\<rightarrow>I" Situation.GEN)
  fix s
  AOT_assume \<open>p\<close>
  moreover AOT_assume \<open>\<forall>q (s \<Turnstile> q \<equiv> q)\<close>
  ultimately AOT_show \<open>s \<Turnstile> p\<close> using "\<forall>E"(2) "\<equiv>E"(2) by blast
qed

AOT_theorem "fund-lem:4": \<open>\<box>p \<rightarrow> \<box>\<forall>s(\<forall>q (s \<Turnstile> q \<equiv> q) \<rightarrow> s \<Turnstile> p)\<close>
  using "fund-lem:3" by (rule RM)

AOT_theorem "fund-lem:5": \<open>\<box>\<forall>s \<phi>{s} \<rightarrow> \<forall>s \<box>\<phi>{s}\<close>
proof(safe intro!: "\<rightarrow>I" Situation.GEN)
  fix s
  AOT_assume \<open>\<box>\<forall>s \<phi>{s}\<close>
  AOT_hence \<open>\<forall>s \<box>\<phi>{s}\<close> using "Situation.res-var-bound-reas[CBF]"[THEN "\<rightarrow>E"] by blast
  AOT_thus \<open>\<box>\<phi>{s}\<close>
    using "Situation.\<forall>E" by fast
qed

text\<open>Note: not explicit in PLM.\<close>
AOT_theorem "fund-lem:5[world]": \<open>\<box>\<forall>w \<phi>{w} \<rightarrow> \<forall>w \<box>\<phi>{w}\<close>
proof(safe intro!: "\<rightarrow>I" PossibleWorld.GEN)
  fix w
  AOT_assume \<open>\<box>\<forall>w \<phi>{w}\<close>
  AOT_hence \<open>\<forall>w \<box>\<phi>{w}\<close> using "PossibleWorld.res-var-bound-reas[CBF]"[THEN "\<rightarrow>E"] by blast
  AOT_thus \<open>\<box>\<phi>{w}\<close>
    using "PossibleWorld.\<forall>E" by fast
qed

AOT_theorem "fund-lem:6": \<open>\<forall>w w \<Turnstile> p \<rightarrow> \<box>\<forall>w w \<Turnstile> p\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<forall>w (w \<Turnstile> p)\<close>
  AOT_hence 1: \<open>PossibleWorld(w) \<rightarrow> (w \<Turnstile> p)\<close> for w using "\<forall>E"(2) by blast
  AOT_show \<open>\<box>\<forall>w w \<Turnstile> p\<close>
  proof(rule "raa-cor:1")
    AOT_assume \<open>\<not>\<box>\<forall>w w \<Turnstile> p\<close>
    AOT_hence \<open>\<diamond>\<not>\<forall>w w \<Turnstile> p\<close>
      by (metis "KBasic:11" "\<equiv>E"(1))
    AOT_hence \<open>\<diamond>\<exists>x (\<not>(PossibleWorld(x) \<rightarrow> x \<Turnstile> p))\<close>
      apply (rule "RM\<diamond>"[THEN "\<rightarrow>E", rotated])
      by (simp add: "cqt-further:2")
    AOT_hence \<open>\<exists>x \<diamond>(\<not>(PossibleWorld(x) \<rightarrow> x \<Turnstile> p))\<close>
      by (metis "BF\<diamond>" "vdash-properties:10")
    then AOT_obtain x where x_prop: \<open>\<diamond>\<not>(PossibleWorld(x) \<rightarrow> x \<Turnstile> p)\<close>
      using "\<exists>E"[rotated] by blast
    AOT_have \<open>\<diamond>(PossibleWorld(x) & \<not>x \<Turnstile> p)\<close>
      apply (AOT_subst \<open>\<guillemotleft>PossibleWorld(x) & \<not>x \<Turnstile> p\<guillemotright>\<close> \<open>\<guillemotleft>\<not>(PossibleWorld(x) \<rightarrow> x \<Turnstile> p)\<guillemotright>\<close>)
       apply (meson "\<equiv>E"(6) "oth-class-taut:1:b" "oth-class-taut:3:a")
      by(fact x_prop)
    AOT_hence 2: \<open>\<diamond>PossibleWorld(x) & \<diamond>\<not>x \<Turnstile> p\<close>
      by (metis "KBasic2:3" "vdash-properties:10")
    AOT_hence \<open>PossibleWorld(x)\<close>
      using "&E"(1) "\<equiv>E"(1) "rigid-pw:2" by blast
    AOT_hence \<open>\<box>(x \<Turnstile> p)\<close> using 2[THEN "&E"(2)]  1[unconstrain w, THEN "\<rightarrow>E"] "vdash-properties:6"
      using "rigid-truth-at:1"[unconstrain w, THEN "\<rightarrow>E"]
      by (metis "\<equiv>E"(1))
    moreover AOT_have \<open>\<not>\<box>(x \<Turnstile> p)\<close> using 2[THEN "&E"(2)] by (metis "\<not>\<not>I" "KBasic:12" "\<equiv>E"(4))
    ultimately AOT_show \<open>p & \<not>p\<close> for p by (metis "raa-cor:3")
  qed
qed

AOT_theorem "fund-lem:7": \<open>\<box>\<forall>w(w \<Turnstile> p) \<rightarrow> \<box>p\<close>
proof(rule RM; rule "\<rightarrow>I")
  AOT_modally_strict {
    AOT_obtain w where w_prop: \<open>\<forall>p (w \<Turnstile> p \<equiv> p)\<close> using "act-world:1" "PossibleWorld.\<exists>E"[rotated] by meson
    AOT_assume \<open>\<forall>w (w \<Turnstile> p)\<close>
    AOT_hence \<open>w \<Turnstile> p\<close> using "PossibleWorld.\<forall>E" by fast
    AOT_thus \<open>p\<close> using w_prop[THEN "\<forall>E"(2), THEN "\<equiv>E"(1)] by blast
  }
qed

AOT_theorem "fund:1": \<open>\<diamond>p \<equiv> \<exists>w w \<Turnstile> p\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<diamond>p\<close>
  AOT_thus \<open>\<exists>w w \<Turnstile> p\<close> by (metis "fund-lem:1" "fund-lem:2" "vdash-properties:10")
next
  AOT_assume \<open>\<exists>w w \<Turnstile> p\<close>
  then AOT_obtain w where w_prop: \<open>w \<Turnstile> p\<close> using "PossibleWorld.\<exists>E"[rotated] by meson
  AOT_hence \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p)\<close> using "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2)] PossibleWorld.\<psi> "&E" by blast
  AOT_hence \<open>\<forall>p \<diamond>(w \<Turnstile> p \<equiv> p)\<close> by (metis "Buridan\<diamond>" "vdash-properties:10")
  AOT_hence 1: \<open>\<diamond>(w \<Turnstile> p \<equiv> p)\<close> by (metis "log-prop-prop:2" "rule-ui:1")
  AOT_have \<open>\<diamond>((w \<Turnstile> p \<rightarrow> p) & (p \<rightarrow> w \<Turnstile> p))\<close>
    apply (AOT_subst \<open>\<guillemotleft>(w \<Turnstile> p \<rightarrow> p) & (p \<rightarrow> w \<Turnstile> p)\<guillemotright>\<close> \<open>\<guillemotleft>w \<Turnstile> p \<equiv> p\<guillemotright>\<close>)
     apply (meson "conventions:3" "\<equiv>E"(6) "oth-class-taut:3:a" "\<equiv>Df")
    by (fact 1)
  AOT_hence \<open>\<diamond>(w \<Turnstile> p \<rightarrow> p)\<close> by (metis "RM\<diamond>" "Conjunction Simplification"(1) "vdash-properties:10")
  moreover AOT_have \<open>\<box>(w \<Turnstile> p)\<close>
    using w_prop by (metis "\<equiv>E"(1) "rigid-truth-at:1")
  ultimately AOT_show \<open>\<diamond>p\<close>
    by (metis "KBasic2:4" "\<equiv>E"(1) "vdash-properties:10")
qed

AOT_theorem "fund:2": \<open>\<box>p \<equiv> \<forall>w (w \<Turnstile> p)\<close>
proof -
  AOT_have 0: \<open>\<forall>w (w \<Turnstile> \<not>p \<equiv> \<not>w \<Turnstile> p)\<close>
    apply (rule PossibleWorld.GEN)
    using "coherent:1" by blast
  AOT_have \<open>\<diamond>\<not>p \<equiv> \<exists>w (w \<Turnstile> \<not>p)\<close> using "fund:1"[unvarify p, OF "log-prop-prop:2"] by blast
  also AOT_have \<open>\<dots> \<equiv> \<exists>w \<not>(w \<Turnstile> p)\<close>
  proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
    AOT_assume \<open>\<exists>w w \<Turnstile> \<not>p\<close>
    then AOT_obtain w where w_prop: \<open>w \<Turnstile> \<not>p\<close> using "PossibleWorld.\<exists>E"[rotated] by meson
    AOT_hence \<open>\<not>w \<Turnstile> p\<close> using 0[THEN "PossibleWorld.\<forall>E", THEN "\<equiv>E"(1)] "&E" by blast
    AOT_thus \<open>\<exists>w \<not>w \<Turnstile> p\<close> by (rule "PossibleWorld.\<exists>I")
  next
    AOT_assume \<open>\<exists>w \<not>w \<Turnstile> p\<close>
    then AOT_obtain w where w_prop: \<open>\<not>w \<Turnstile> p\<close> using "PossibleWorld.\<exists>E"[rotated] by meson
    AOT_hence \<open>w \<Turnstile> \<not>p\<close> using 0[THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<equiv>E"(1)] "&E" by (metis "coherent:1" "\<equiv>E"(2))
    AOT_thus \<open>\<exists>w w \<Turnstile> \<not>p\<close> by (rule "PossibleWorld.\<exists>I")
  qed
  finally AOT_have \<open>\<not>\<diamond>\<not>p \<equiv> \<not>\<exists>w \<not>w \<Turnstile> p\<close>
    by (meson "\<equiv>E"(1) "oth-class-taut:4:b")
  AOT_hence \<open>\<box>p \<equiv> \<not>\<exists>w \<not>w \<Turnstile> p\<close> by (metis "KBasic:12" "\<equiv>E"(5))
  also AOT_have \<open>\<dots> \<equiv> \<forall>w w \<Turnstile> p\<close>
  proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
    AOT_assume \<open>\<not>\<exists>w \<not>w \<Turnstile> p\<close>
    AOT_hence 0: \<open>\<forall>x (\<not>(PossibleWorld(x) & \<not>x \<Turnstile> p))\<close>
      by (metis "cqt-further:4" "vdash-properties:10")
    AOT_show \<open>\<forall>w w \<Turnstile> p\<close>
      apply (AOT_subst \<open>\<lambda> \<kappa> . \<guillemotleft>PossibleWorld(\<kappa>) \<rightarrow> \<kappa> \<Turnstile> p\<guillemotright>\<close> \<open>\<lambda> \<kappa> . \<guillemotleft>\<not>(PossibleWorld(\<kappa>) & \<not>\<kappa> \<Turnstile> p)\<guillemotright>\<close>)
       using "oth-class-taut:1:a" apply presburger
      by (fact 0)
  next
    AOT_assume 0: \<open>\<forall>w w \<Turnstile> p\<close>
    AOT_have \<open>\<forall>x (\<not>(PossibleWorld(x) & \<not>x \<Turnstile> p))\<close>
      by (AOT_subst_rev \<open>\<lambda> \<kappa> . \<guillemotleft>PossibleWorld(\<kappa>) \<rightarrow> \<kappa> \<Turnstile> p\<guillemotright>\<close> \<open>\<lambda> \<kappa> . \<guillemotleft>\<not>(PossibleWorld(\<kappa>) & \<not>\<kappa> \<Turnstile> p)\<guillemotright>\<close>)
         (auto simp: "oth-class-taut:1:a" 0)
    AOT_thus \<open>\<not>\<exists>w \<not>w \<Turnstile> p\<close>
      by (metis "instantiation" "raa-cor:3" "rule-ui:3")
  qed
  finally AOT_show \<open>\<box>p \<equiv> \<forall>w w \<Turnstile> p\<close>.
qed

AOT_theorem "fund:3": \<open>\<not>\<diamond>p \<equiv> \<not>\<exists>w w \<Turnstile> p\<close>
  by (metis (full_types) "contraposition:1[1]" "deduction-theorem" "fund:1" "\<equiv>I" "\<equiv>E"(1) "\<equiv>E"(2))

AOT_theorem "fund:4": \<open>\<not>\<box>p \<equiv> \<exists>w \<not>w \<Turnstile>p\<close>
  apply (AOT_subst \<open>\<guillemotleft>\<exists>w \<not>w \<Turnstile> p\<guillemotright>\<close> \<open>\<guillemotleft>\<not> \<forall>w w \<Turnstile> p\<guillemotright>\<close>)
   apply (AOT_subst \<open>\<lambda> \<kappa> . \<guillemotleft>PossibleWorld(\<kappa>) \<rightarrow> \<kappa> \<Turnstile> p\<guillemotright>\<close> \<open>\<lambda> \<kappa> . \<guillemotleft>\<not>(PossibleWorld(\<kappa>) & \<not>\<kappa> \<Turnstile> p)\<guillemotright>\<close>)
  by (auto simp add: "oth-class-taut:1:a" "conventions:4" "\<equiv>Df" RN "fund:2" "rule-sub-lem:1:a")

AOT_theorem "nec-dia-w:1": \<open>\<box>p \<equiv> \<exists>w w \<Turnstile> \<box>p\<close>
proof -
  AOT_have \<open>\<box>p \<equiv> \<diamond>\<box>p\<close>
    using "S5Basic:2" by blast
  also AOT_have \<open>... \<equiv> \<exists>w w \<Turnstile> \<box>p\<close>
    using "fund:1"[unvarify p, OF "log-prop-prop:2"] by blast
  finally show ?thesis.
qed

AOT_theorem "nec-dia-w:2": \<open>\<box>p \<equiv> \<forall>w w \<Turnstile> \<box>p\<close>
proof -
  AOT_have \<open>\<box>p \<equiv> \<box>\<box>p\<close>
    using 4 "qml:2"[axiom_inst] "\<equiv>I" by blast
  also AOT_have \<open>... \<equiv> \<forall>w w \<Turnstile> \<box>p\<close>
    using "fund:2"[unvarify p, OF "log-prop-prop:2"] by blast
  finally show ?thesis.
qed

AOT_theorem "nec-dia-w:3": \<open>\<diamond>p \<equiv> \<exists>w w \<Turnstile> \<diamond>p\<close>
proof -
  AOT_have \<open>\<diamond>p \<equiv> \<diamond>\<diamond>p\<close>
    by (simp add: "4\<diamond>" "T\<diamond>" "\<equiv>I")
  also AOT_have \<open>... \<equiv> \<exists>w w \<Turnstile> \<diamond>p\<close>
    using "fund:1"[unvarify p, OF "log-prop-prop:2"] by blast
  finally show ?thesis.
qed

AOT_theorem "nec-dia-w:4": \<open>\<diamond>p \<equiv> \<forall>w w \<Turnstile> \<diamond>p\<close>
proof -
  AOT_have \<open>\<diamond>p \<equiv> \<box>\<diamond>p\<close>
    by (simp add: "S5Basic:1")
  also AOT_have \<open>... \<equiv> \<forall>w w \<Turnstile> \<diamond>p\<close>
    using "fund:2"[unvarify p, OF "log-prop-prop:2"] by blast
  finally show ?thesis.
qed

AOT_theorem "conj-dist-w:1": \<open>w \<Turnstile> (p & q) \<equiv> ((w \<Turnstile> p) & (w \<Turnstile> q))\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>w \<Turnstile> (p & q)\<close>
  AOT_hence 0: \<open>\<box>w \<Turnstile> (p & q)\<close>
    using "rigid-truth-at:1"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"] by blast
  AOT_modally_strict {
    AOT_have \<open>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> ((w \<Turnstile> (\<phi> & \<psi>)) \<rightarrow> (w \<Turnstile> \<phi> & w \<Turnstile> \<psi>))\<close> for w \<phi> \<psi>
    proof(safe intro!: "\<rightarrow>I")
      AOT_assume \<open>\<forall> p (w \<Turnstile> p \<equiv> p)\<close>
      AOT_hence \<open>w \<Turnstile> (\<phi> & \<psi>) \<equiv> (\<phi> & \<psi>)\<close> and \<open>w \<Turnstile> \<phi> \<equiv> \<phi>\<close> and \<open>w \<Turnstile> \<psi> \<equiv> \<psi>\<close>
        using "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] by blast+
      moreover AOT_assume \<open>w \<Turnstile> (\<phi> & \<psi>)\<close>
      ultimately AOT_show \<open>w \<Turnstile> \<phi> & w \<Turnstile> \<psi>\<close>
        by (metis "&I" "&E"(1) "&E"(2) "\<equiv>E"(1) "\<equiv>E"(2))
    qed
  }
  AOT_hence \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> \<diamond>(w \<Turnstile> (\<phi> & \<psi>) \<rightarrow> w \<Turnstile> \<phi> & w \<Turnstile> \<psi>)\<close> for w \<phi> \<psi> by (rule "RM\<diamond>")
  moreover AOT_have pos: \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
    using "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF PossibleWorld.\<psi>] "&E" by blast
  ultimately AOT_have \<open>\<diamond>(w \<Turnstile> (p & q) \<rightarrow> w \<Turnstile> p & w \<Turnstile> q)\<close> using "\<rightarrow>E" by blast
  AOT_hence \<open>\<diamond>(w \<Turnstile> p) & \<diamond>(w \<Turnstile> q)\<close>
    by (metis 0 "KBasic2:3" "KBasic2:4" "\<equiv>E"(1) "vdash-properties:10")
  AOT_thus \<open>w \<Turnstile> p & w \<Turnstile> q\<close>
    using "rigid-truth-at:2"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"] "&E" "&I" by meson
next
  AOT_assume \<open>w \<Turnstile> p & w \<Turnstile> q\<close>
  AOT_hence \<open>\<box>w \<Turnstile> p & \<box>w \<Turnstile> q\<close>
    using "rigid-truth-at:1"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"] "&E" "&I" by blast
  AOT_hence 0: \<open>\<box>(w \<Turnstile> p & w \<Turnstile> q)\<close>
    by (metis "KBasic:3" "\<equiv>E"(2))
  AOT_modally_strict {
    AOT_have \<open>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> ((w \<Turnstile> \<phi> & w \<Turnstile> \<psi>) \<rightarrow> (w \<Turnstile> (\<phi> & \<psi>)))\<close> for w \<phi> \<psi>
    proof(safe intro!: "\<rightarrow>I")
      AOT_assume \<open>\<forall> p (w \<Turnstile> p \<equiv> p)\<close>
      AOT_hence \<open>w \<Turnstile> (\<phi> & \<psi>) \<equiv> (\<phi> & \<psi>)\<close> and \<open>w \<Turnstile> \<phi> \<equiv> \<phi>\<close> and \<open>w \<Turnstile> \<psi> \<equiv> \<psi>\<close>
        using "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] by blast+
      moreover AOT_assume \<open>w \<Turnstile> \<phi> & w \<Turnstile> \<psi>\<close>
      ultimately AOT_show \<open>w \<Turnstile> (\<phi> & \<psi>)\<close>
        by (metis "&I" "&E"(1) "&E"(2) "\<equiv>E"(1) "\<equiv>E"(2))
    qed
  }
  AOT_hence \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> \<diamond>((w \<Turnstile> \<phi> & w \<Turnstile> \<psi>) \<rightarrow> w \<Turnstile> (\<phi> & \<psi>))\<close> for w \<phi> \<psi> by (rule "RM\<diamond>")
  moreover AOT_have pos: \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
    using "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF PossibleWorld.\<psi>] "&E" by blast
  ultimately AOT_have \<open>\<diamond>((w \<Turnstile> p & w \<Turnstile> q) \<rightarrow> w \<Turnstile> (p & q))\<close> using "\<rightarrow>E" by blast
  AOT_hence \<open>\<diamond>(w \<Turnstile> (p & q))\<close>
    by (metis 0 "KBasic2:4" "\<equiv>E"(1) "vdash-properties:10")
  AOT_thus \<open>w \<Turnstile> (p & q)\<close>
    using "rigid-truth-at:2"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"] by blast
qed

AOT_theorem "conj-dist-w:2": \<open>w \<Turnstile> (p \<rightarrow> q) \<equiv> ((w \<Turnstile> p) \<rightarrow> (w \<Turnstile> q))\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>w \<Turnstile> (p \<rightarrow> q)\<close>
  AOT_hence 0: \<open>\<box>w \<Turnstile> (p \<rightarrow> q)\<close>
    using "rigid-truth-at:1"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"] by blast
  AOT_assume \<open>w \<Turnstile> p\<close>
  AOT_hence 1: \<open>\<box>w \<Turnstile> p\<close> by (metis "T\<diamond>" "\<equiv>E"(1) "rigid-truth-at:3" "vdash-properties:10")
  AOT_modally_strict {
    AOT_have \<open>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> ((w \<Turnstile> (\<phi> \<rightarrow> \<psi>)) \<rightarrow> (w \<Turnstile> \<phi> \<rightarrow> w \<Turnstile> \<psi>))\<close> for w \<phi> \<psi>
    proof(safe intro!: "\<rightarrow>I")
      AOT_assume \<open>\<forall> p (w \<Turnstile> p \<equiv> p)\<close>
      AOT_hence \<open>w \<Turnstile> (\<phi> \<rightarrow> \<psi>) \<equiv> (\<phi> \<rightarrow> \<psi>)\<close> and \<open>w \<Turnstile> \<phi> \<equiv> \<phi>\<close> and \<open>w \<Turnstile> \<psi> \<equiv> \<psi>\<close>
        using "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] by blast+
      moreover AOT_assume \<open>w \<Turnstile> (\<phi> \<rightarrow> \<psi>)\<close>
      moreover AOT_assume \<open>w \<Turnstile> \<phi>\<close>
      ultimately AOT_show \<open>w \<Turnstile> \<psi>\<close>
        by (metis "\<equiv>E"(1) "\<equiv>E"(2) "vdash-properties:10")
    qed
  }
  AOT_hence \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> \<diamond>(w \<Turnstile> (\<phi> \<rightarrow> \<psi>) \<rightarrow> (w \<Turnstile> \<phi> \<rightarrow> w \<Turnstile> \<psi>))\<close> for w \<phi> \<psi> by (rule "RM\<diamond>")
  moreover AOT_have pos: \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
    using "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF PossibleWorld.\<psi>] "&E" by blast
  ultimately AOT_have \<open>\<diamond>(w \<Turnstile> (p \<rightarrow> q) \<rightarrow> (w \<Turnstile> p \<rightarrow> w \<Turnstile> q))\<close> using "\<rightarrow>E" by blast
  AOT_hence \<open>\<diamond>(w \<Turnstile> p \<rightarrow> w \<Turnstile> q)\<close>
    by (metis 0 "KBasic2:4" "\<equiv>E"(1) "vdash-properties:10")
  AOT_hence \<open>\<diamond>w \<Turnstile> q\<close> 
    by (metis 1 "KBasic2:4" "\<equiv>E"(1) "vdash-properties:10")
  AOT_thus \<open>w \<Turnstile> q\<close>
    using "rigid-truth-at:2"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"] "&E" "&I" by meson
next
  AOT_assume \<open>w \<Turnstile> p \<rightarrow> w \<Turnstile> q\<close>
  AOT_hence \<open>\<not>(w \<Turnstile> p) \<or> w \<Turnstile> q\<close>
    by (metis "\<or>I"(1) "\<or>I"(2) "reductio-aa:1" "vdash-properties:10")
  AOT_hence \<open>w \<Turnstile> \<not>p \<or> w \<Turnstile> q\<close>
    by (metis "coherent:1" "\<or>I"(1) "\<or>I"(2) "\<or>E"(2) "\<equiv>E"(2) "reductio-aa:1")
  AOT_hence 0: \<open>\<box>(w \<Turnstile> \<not>p \<or> w \<Turnstile> q)\<close>
    using "rigid-truth-at:1"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"]
    by (metis "KBasic:15" "\<or>I"(1) "\<or>I"(2) "\<or>E"(2) "reductio-aa:1" "vdash-properties:10")
  AOT_modally_strict {
    AOT_have \<open>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> ((w \<Turnstile> \<not>\<phi> \<or> w \<Turnstile> \<psi>) \<rightarrow> (w \<Turnstile> (\<phi> \<rightarrow> \<psi>)))\<close> for w \<phi> \<psi>
    proof(safe intro!: "\<rightarrow>I")
      AOT_assume \<open>\<forall> p (w \<Turnstile> p \<equiv> p)\<close>
      moreover AOT_assume \<open>w \<Turnstile> \<not>\<phi> \<or> w \<Turnstile> \<psi>\<close>
      ultimately AOT_show \<open>w \<Turnstile> (\<phi> \<rightarrow> \<psi>)\<close>
        by (metis "\<or>E"(2) "deduction-theorem" "\<equiv>E"(1) "\<equiv>E"(2) "log-prop-prop:2" "reductio-aa:1" "rule-ui:1")
    qed
  }
  AOT_hence \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> \<diamond>((w \<Turnstile> \<not>\<phi> \<or> w \<Turnstile> \<psi>) \<rightarrow> w \<Turnstile> (\<phi> \<rightarrow> \<psi>))\<close> for w \<phi> \<psi> by (rule "RM\<diamond>")
  moreover AOT_have pos: \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
    using "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF PossibleWorld.\<psi>] "&E" by blast
  ultimately AOT_have \<open>\<diamond>((w \<Turnstile> \<not>p \<or> w \<Turnstile> q) \<rightarrow> w \<Turnstile> (p \<rightarrow> q))\<close> using "\<rightarrow>E" by blast
  AOT_hence \<open>\<diamond>(w \<Turnstile> (p \<rightarrow> q))\<close>
    by (metis 0 "KBasic2:4" "\<equiv>E"(1) "vdash-properties:10")
  AOT_thus \<open>w \<Turnstile> (p \<rightarrow> q)\<close>
    using "rigid-truth-at:2"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"] by blast
qed

AOT_theorem "conj-dist-w:3": \<open>w \<Turnstile> (p \<or> q) \<equiv> ((w \<Turnstile> p) \<or> (w \<Turnstile> q))\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>w \<Turnstile> (p \<or> q)\<close>
  AOT_hence 0: \<open>\<box>w \<Turnstile> (p \<or> q)\<close>
    using "rigid-truth-at:1"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"] by blast
  AOT_modally_strict {
    AOT_have \<open>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> ((w \<Turnstile> (\<phi> \<or> \<psi>)) \<rightarrow> (w \<Turnstile> \<phi> \<or> w \<Turnstile> \<psi>))\<close> for w \<phi> \<psi>
    proof(safe intro!: "\<rightarrow>I")
      AOT_assume \<open>\<forall> p (w \<Turnstile> p \<equiv> p)\<close>
      AOT_hence \<open>w \<Turnstile> (\<phi> \<or> \<psi>) \<equiv> (\<phi> \<or> \<psi>)\<close> and \<open>w \<Turnstile> \<phi> \<equiv> \<phi>\<close> and \<open>w \<Turnstile> \<psi> \<equiv> \<psi>\<close>
        using "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] by blast+
      moreover AOT_assume \<open>w \<Turnstile> (\<phi> \<or> \<psi>)\<close>
      ultimately AOT_show \<open>w \<Turnstile> \<phi> \<or> w \<Turnstile> \<psi>\<close>
        by (metis "\<or>I"(1) "\<or>I"(2) "\<or>E"(3) "\<equiv>E"(1) "\<equiv>E"(2) "reductio-aa:1")
    qed
  }
  AOT_hence \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> \<diamond>(w \<Turnstile> (\<phi> \<or> \<psi>) \<rightarrow> (w \<Turnstile> \<phi> \<or> w \<Turnstile> \<psi>))\<close> for w \<phi> \<psi> by (rule "RM\<diamond>")
  moreover AOT_have pos: \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
    using "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF PossibleWorld.\<psi>] "&E" by blast
  ultimately AOT_have \<open>\<diamond>(w \<Turnstile> (p \<or> q) \<rightarrow> (w \<Turnstile> p \<or> w \<Turnstile> q))\<close> using "\<rightarrow>E" by blast
  AOT_hence \<open>\<diamond>(w \<Turnstile> p \<or> w \<Turnstile> q)\<close>
    by (metis 0 "KBasic2:4" "\<equiv>E"(1) "vdash-properties:10")
  AOT_hence \<open>\<diamond>w \<Turnstile> p \<or> \<diamond>w \<Turnstile> q\<close>
    using "KBasic2:2"[THEN "\<equiv>E"(1)] by blast
  AOT_thus \<open>w \<Turnstile> p \<or> w \<Turnstile> q\<close>
    using "rigid-truth-at:2"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"]
    by (metis "\<or>I"(1) "\<or>I"(2) "\<or>E"(2) "reductio-aa:1")
next
  AOT_assume \<open>w \<Turnstile> p \<or> w \<Turnstile> q\<close>
  AOT_hence 0: \<open>\<box>(w \<Turnstile> p \<or> w \<Turnstile> q)\<close>
    using "rigid-truth-at:1"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"]
    by (metis "KBasic:15" "\<or>I"(1) "\<or>I"(2) "\<or>E"(2) "reductio-aa:1" "vdash-properties:10")
  AOT_modally_strict {
    AOT_have \<open>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> ((w \<Turnstile> \<phi> \<or> w \<Turnstile> \<psi>) \<rightarrow> (w \<Turnstile> (\<phi> \<or> \<psi>)))\<close> for w \<phi> \<psi>
    proof(safe intro!: "\<rightarrow>I")
      AOT_assume \<open>\<forall> p (w \<Turnstile> p \<equiv> p)\<close>
      moreover AOT_assume \<open>w \<Turnstile> \<phi> \<or> w \<Turnstile> \<psi>\<close>
      ultimately AOT_show \<open>w \<Turnstile> (\<phi> \<or> \<psi>)\<close>
        by (metis "\<or>I"(1) "\<or>I"(2) "\<or>E"(2) "\<equiv>E"(1) "\<equiv>E"(2)
                  "log-prop-prop:2" "reductio-aa:1" "rule-ui:1")
    qed
  }
  AOT_hence \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> \<diamond>((w \<Turnstile> \<phi> \<or> w \<Turnstile> \<psi>) \<rightarrow> w \<Turnstile> (\<phi> \<or> \<psi>))\<close> for w \<phi> \<psi> by (rule "RM\<diamond>")
  moreover AOT_have pos: \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
    using "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF PossibleWorld.\<psi>] "&E" by blast
  ultimately AOT_have \<open>\<diamond>((w \<Turnstile> p \<or> w \<Turnstile> q) \<rightarrow> w \<Turnstile> (p \<or> q))\<close> using "\<rightarrow>E" by blast
  AOT_hence \<open>\<diamond>(w \<Turnstile> (p \<or> q))\<close>
    by (metis 0 "KBasic2:4" "\<equiv>E"(1) "vdash-properties:10")
  AOT_thus \<open>w \<Turnstile> (p \<or> q)\<close>
    using "rigid-truth-at:2"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"] by blast
qed

AOT_theorem "conj-dist-w:4": \<open>w \<Turnstile> (p \<equiv> q) \<equiv> ((w \<Turnstile> p) \<equiv> (w \<Turnstile> q))\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>w \<Turnstile> (p \<equiv> q)\<close>
  AOT_hence 0: \<open>\<box>w \<Turnstile> (p \<equiv> q)\<close>
    using "rigid-truth-at:1"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"] by blast
  AOT_modally_strict {
    AOT_have \<open>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> ((w \<Turnstile> (\<phi> \<equiv> \<psi>)) \<rightarrow> (w \<Turnstile> \<phi> \<equiv> w \<Turnstile> \<psi>))\<close> for w \<phi> \<psi>
    proof(safe intro!: "\<rightarrow>I")
      AOT_assume \<open>\<forall> p (w \<Turnstile> p \<equiv> p)\<close>
      AOT_hence \<open>w \<Turnstile> (\<phi> \<equiv> \<psi>) \<equiv> (\<phi> \<equiv> \<psi>)\<close> and \<open>w \<Turnstile> \<phi> \<equiv> \<phi>\<close> and \<open>w \<Turnstile> \<psi> \<equiv> \<psi>\<close>
        using "\<forall>E"(1)[rotated, OF "log-prop-prop:2"] by blast+
      moreover AOT_assume \<open>w \<Turnstile> (\<phi> \<equiv> \<psi>)\<close>
      ultimately AOT_show \<open>w \<Turnstile> \<phi> \<equiv> w \<Turnstile> \<psi>\<close>
        by (metis "\<equiv>E"(2) "\<equiv>E"(5) "Commutativity of \<equiv>")
    qed
  }
  AOT_hence \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> \<diamond>(w \<Turnstile> (\<phi> \<equiv> \<psi>) \<rightarrow> (w \<Turnstile> \<phi> \<equiv> w \<Turnstile> \<psi>))\<close> for w \<phi> \<psi> by (rule "RM\<diamond>")
  moreover AOT_have pos: \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
    using "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF PossibleWorld.\<psi>] "&E" by blast
  ultimately AOT_have \<open>\<diamond>(w \<Turnstile> (p \<equiv> q) \<rightarrow> (w \<Turnstile> p \<equiv> w \<Turnstile> q))\<close> using "\<rightarrow>E" by blast
  AOT_hence 1: \<open>\<diamond>(w \<Turnstile> p \<equiv> w \<Turnstile> q)\<close>
    by (metis 0 "KBasic2:4" "\<equiv>E"(1) "vdash-properties:10")
  AOT_have \<open>\<diamond>((w \<Turnstile> p \<rightarrow> w \<Turnstile> q) & (w \<Turnstile> q \<rightarrow> w \<Turnstile> p))\<close>
    apply (AOT_subst \<open>\<guillemotleft>(w \<Turnstile> p \<rightarrow> w \<Turnstile> q) & (w \<Turnstile> q \<rightarrow> w \<Turnstile> p)\<guillemotright>\<close> \<open>\<guillemotleft>w \<Turnstile> p \<equiv> w \<Turnstile> q\<guillemotright>\<close>)
     apply (meson "\<equiv>\<^sub>d\<^sub>fE" "conventions:3" "deduction-theorem" "df-rules-formulas[4]" "\<equiv>I")
    by (fact 1)
  AOT_hence 2: \<open>\<diamond>(w \<Turnstile> p \<rightarrow> w \<Turnstile> q) & \<diamond>(w \<Turnstile> q \<rightarrow> w \<Turnstile> p)\<close>
    by (metis "KBasic2:3" "vdash-properties:10")
  AOT_have \<open>\<diamond>(\<not>w \<Turnstile> p \<or> w \<Turnstile> q)\<close> and \<open>\<diamond>(\<not>w \<Turnstile> q \<or> w \<Turnstile> p)\<close>
     apply (AOT_subst_rev \<open>\<guillemotleft>w \<Turnstile> p \<rightarrow> w \<Turnstile> q\<guillemotright>\<close> \<open>\<guillemotleft>\<not>w \<Turnstile> p \<or> w \<Turnstile> q\<guillemotright>\<close>)
      apply (simp add: "oth-class-taut:1:c")
     apply (fact 2[THEN "&E"(1)])
    apply (AOT_subst_rev \<open>\<guillemotleft>w \<Turnstile> q \<rightarrow> w \<Turnstile> p\<guillemotright>\<close> \<open>\<guillemotleft>\<not>w \<Turnstile> q \<or> w \<Turnstile> p\<guillemotright>\<close>)
     apply (simp add: "oth-class-taut:1:c")
    by (fact 2[THEN "&E"(2)])
  AOT_hence \<open>\<diamond>(\<not>w \<Turnstile> p) \<or> \<diamond>w \<Turnstile> q\<close> and \<open>\<diamond>\<not>w \<Turnstile> q \<or> \<diamond>w \<Turnstile> p\<close>
    using "KBasic2:2" "\<equiv>E"(1) by blast+
  AOT_hence \<open>\<not>\<box>w \<Turnstile> p \<or> \<diamond>w \<Turnstile> q\<close> and \<open>\<not>\<box>w \<Turnstile> q \<or> \<diamond>w \<Turnstile> p\<close>
    by (metis "KBasic:11" "\<or>I"(1) "\<or>I"(2) "\<or>E"(2) "\<equiv>E"(2) "raa-cor:1")+
  AOT_thus \<open>w \<Turnstile> p \<equiv> w \<Turnstile> q\<close>
    using "rigid-truth-at:2"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"]
    by (metis "\<not>\<not>I" "T\<diamond>" "\<or>E"(2) "deduction-theorem" "\<equiv>I" "\<equiv>E"(1) "rigid-truth-at:3")
next
  AOT_have \<open>\<box>PossibleWorld(w)\<close>
    using "\<equiv>E"(1) "rigid-pw:1" PossibleWorld.\<psi> by blast
  moreover {
    fix p
    AOT_modally_strict {
      AOT_have \<open>PossibleWorld(w) \<rightarrow> (w \<Turnstile> p \<rightarrow> \<box>w \<Turnstile> p)\<close>
        using "rigid-truth-at:1" "\<rightarrow>I"
        by (metis "\<equiv>E"(1))
    }
    AOT_hence \<open>\<box>PossibleWorld(w) \<rightarrow> \<box>(w \<Turnstile> p \<rightarrow> \<box>w \<Turnstile> p)\<close> by (rule RM)
  }
  ultimately AOT_have 1: \<open>\<box>(w \<Turnstile> p \<rightarrow> \<box>w \<Turnstile> p)\<close> for p by (metis "vdash-properties:10")
  AOT_assume \<open>w \<Turnstile> p \<equiv> w \<Turnstile> q\<close>
  AOT_hence 0: \<open>\<box>(w \<Turnstile> p \<equiv> w \<Turnstile> q)\<close>
    using "sc-eq-box-box:5"[THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF "&I"]
          by (metis "1")
  AOT_modally_strict {
    AOT_have \<open>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> ((w \<Turnstile> \<phi> \<equiv> w \<Turnstile> \<psi>) \<rightarrow> (w \<Turnstile> (\<phi> \<equiv> \<psi>)))\<close> for w \<phi> \<psi>
    proof(safe intro!: "\<rightarrow>I")
      AOT_assume \<open>\<forall> p (w \<Turnstile> p \<equiv> p)\<close>
      moreover AOT_assume \<open>w \<Turnstile> \<phi> \<equiv> w \<Turnstile> \<psi>\<close>
      ultimately AOT_show \<open>w \<Turnstile> (\<phi> \<equiv> \<psi>)\<close>
        by (metis "\<equiv>E"(2) "\<equiv>E"(6) "log-prop-prop:2" "rule-ui:1")
    qed
  }
  AOT_hence \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> \<diamond>((w \<Turnstile> \<phi> \<equiv> w \<Turnstile> \<psi>) \<rightarrow> w \<Turnstile> (\<phi> \<equiv> \<psi>))\<close> for w \<phi> \<psi> by (rule "RM\<diamond>")
  moreover AOT_have pos: \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
    using "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF PossibleWorld.\<psi>] "&E" by blast
  ultimately AOT_have \<open>\<diamond>((w \<Turnstile> p \<equiv>  w \<Turnstile> q) \<rightarrow> w \<Turnstile> (p \<equiv> q))\<close> using "\<rightarrow>E" by blast
  AOT_hence \<open>\<diamond>(w \<Turnstile> (p \<equiv> q))\<close>
    by (metis 0 "KBasic2:4" "\<equiv>E"(1) "vdash-properties:10")
  AOT_thus \<open>w \<Turnstile> (p \<equiv> q)\<close>
    using "rigid-truth-at:2"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"] by blast
qed

AOT_theorem "conj-dist-w:5": \<open>w \<Turnstile> (\<forall>\<alpha> \<phi>{\<alpha>}) \<equiv> (\<forall> \<alpha> (w \<Turnstile> \<phi>{\<alpha>}))\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I" GEN)
  AOT_assume \<open>w \<Turnstile> (\<forall>\<alpha> \<phi>{\<alpha>})\<close>
  AOT_hence 0: \<open>\<box>w \<Turnstile> (\<forall>\<alpha> \<phi>{\<alpha>})\<close>
    using "rigid-truth-at:1"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"] by blast
  AOT_modally_strict {
    AOT_have \<open>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> ((w \<Turnstile> (\<forall>\<alpha> \<phi>{\<alpha>})) \<rightarrow> (\<forall>\<alpha> w \<Turnstile> \<phi>{\<alpha>}))\<close> for w
    proof(safe intro!: "\<rightarrow>I" GEN)
      AOT_assume \<open>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
      moreover AOT_assume \<open>w \<Turnstile> (\<forall>\<alpha> \<phi>{\<alpha>})\<close>
      ultimately AOT_show \<open>w \<Turnstile> \<phi>{\<alpha>}\<close> for \<alpha>
        by (metis "\<equiv>E"(1) "\<equiv>E"(2) "log-prop-prop:2" "rule-ui:1" "rule-ui:3")
    qed
  }
  AOT_hence \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> \<diamond>(w \<Turnstile> (\<forall>\<alpha> \<phi>{\<alpha>}) \<rightarrow> (\<forall>\<alpha> w \<Turnstile> \<phi>{\<alpha>}))\<close> for w by (rule "RM\<diamond>")
  moreover AOT_have pos: \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
    using "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF PossibleWorld.\<psi>] "&E" by blast
  ultimately AOT_have \<open>\<diamond>(w \<Turnstile> (\<forall>\<alpha> \<phi>{\<alpha>}) \<rightarrow> (\<forall>\<alpha> w \<Turnstile> \<phi>{\<alpha>}))\<close> using "\<rightarrow>E" by blast
  AOT_hence \<open>\<diamond>(\<forall>\<alpha> w \<Turnstile> \<phi>{\<alpha>})\<close>
    by (metis 0 "KBasic2:4" "\<equiv>E"(1) "vdash-properties:10")
  AOT_hence \<open>\<forall>\<alpha> \<diamond>w \<Turnstile> \<phi>{\<alpha>}\<close>
    by (metis "Buridan\<diamond>" "vdash-properties:10")
  AOT_thus \<open>w \<Turnstile> \<phi>{\<alpha>}\<close> for \<alpha>
    using "rigid-truth-at:2"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"]
          "\<forall>E"(2) by blast
next
  AOT_assume \<open>\<forall>\<alpha> w \<Turnstile> \<phi>{\<alpha>}\<close>
  AOT_hence \<open>w \<Turnstile> \<phi>{\<alpha>}\<close> for \<alpha> using "\<forall>E"(2) by blast
  AOT_hence \<open>\<box>w \<Turnstile> \<phi>{\<alpha>}\<close> for \<alpha>
    using "rigid-truth-at:1"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"] "&E" "&I" by blast
  AOT_hence \<open>\<forall>\<alpha> \<box>w \<Turnstile> \<phi>{\<alpha>}\<close> by (rule GEN)
  AOT_hence 0: \<open>\<box>\<forall>\<alpha> w \<Turnstile> \<phi>{\<alpha>}\<close> by (rule BF[THEN "\<rightarrow>E"])
  AOT_modally_strict {
    AOT_have \<open>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> ((\<forall>\<alpha> w \<Turnstile> \<phi>{\<alpha>}) \<rightarrow> (w \<Turnstile> (\<forall>\<alpha> \<phi>{\<alpha>})))\<close> for w
    proof(safe intro!: "\<rightarrow>I")
      AOT_assume \<open>\<forall> p (w \<Turnstile> p \<equiv> p)\<close>
      moreover AOT_assume \<open>\<forall>\<alpha> w \<Turnstile> \<phi>{\<alpha>}\<close>
      ultimately AOT_show \<open>w \<Turnstile> (\<forall>\<alpha> \<phi>{\<alpha>})\<close>
        by (metis "\<equiv>E"(1) "\<equiv>E"(2) "log-prop-prop:2" "rule-ui:1" "rule-ui:3" "universal-cor")
    qed
  }
  AOT_hence \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> \<diamond>((\<forall>\<alpha> w \<Turnstile> \<phi>{\<alpha>}) \<rightarrow> w \<Turnstile> (\<forall>\<alpha> \<phi>{\<alpha>}))\<close> for w by (rule "RM\<diamond>")
  moreover AOT_have pos: \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
    using "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF PossibleWorld.\<psi>] "&E" by blast
  ultimately AOT_have \<open>\<diamond>((\<forall>\<alpha> w \<Turnstile> \<phi>{\<alpha>}) \<rightarrow> w \<Turnstile> (\<forall>\<alpha> \<phi>{\<alpha>}))\<close> using "\<rightarrow>E" by blast
  AOT_hence \<open>\<diamond>(w \<Turnstile> (\<forall>\<alpha> \<phi>{\<alpha>}))\<close>
    by (metis 0 "KBasic2:4" "\<equiv>E"(1) "vdash-properties:10")
  AOT_thus \<open>w \<Turnstile> (\<forall>\<alpha> \<phi>{\<alpha>})\<close>
    using "rigid-truth-at:2"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"] by blast
qed

AOT_theorem "conj-dist-w:6": \<open>w \<Turnstile> (\<exists>\<alpha> \<phi>{\<alpha>}) \<equiv> (\<exists> \<alpha> (w \<Turnstile> \<phi>{\<alpha>}))\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I" GEN)
  AOT_assume \<open>w \<Turnstile> (\<exists>\<alpha> \<phi>{\<alpha>})\<close>
  AOT_hence 0: \<open>\<box>w \<Turnstile> (\<exists>\<alpha> \<phi>{\<alpha>})\<close>
    using "rigid-truth-at:1"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"] by blast
  AOT_modally_strict {
    AOT_have \<open>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> ((w \<Turnstile> (\<exists>\<alpha> \<phi>{\<alpha>})) \<rightarrow> (\<exists>\<alpha> w \<Turnstile> \<phi>{\<alpha>}))\<close> for w
    proof(safe intro!: "\<rightarrow>I" GEN)
      AOT_assume \<open>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
      moreover AOT_assume \<open>w \<Turnstile> (\<exists>\<alpha> \<phi>{\<alpha>})\<close>
      ultimately AOT_show \<open>\<exists> \<alpha> (w \<Turnstile> \<phi>{\<alpha>})\<close>
        by (metis "instantiation" "existential:2[const_var]" "\<equiv>E"(1) "\<equiv>E"(2) "log-prop-prop:2" "rule-ui:1") 
    qed
  }
  AOT_hence \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> \<diamond>(w \<Turnstile> (\<exists>\<alpha> \<phi>{\<alpha>}) \<rightarrow> (\<exists>\<alpha> w \<Turnstile> \<phi>{\<alpha>}))\<close> for w by (rule "RM\<diamond>")
  moreover AOT_have pos: \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
    using "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF PossibleWorld.\<psi>] "&E" by blast
  ultimately AOT_have \<open>\<diamond>(w \<Turnstile> (\<exists>\<alpha> \<phi>{\<alpha>}) \<rightarrow> (\<exists>\<alpha> w \<Turnstile> \<phi>{\<alpha>}))\<close> using "\<rightarrow>E" by blast
  AOT_hence \<open>\<diamond>(\<exists>\<alpha> w \<Turnstile> \<phi>{\<alpha>})\<close>
    by (metis 0 "KBasic2:4" "\<equiv>E"(1) "vdash-properties:10")
  AOT_hence \<open>\<exists>\<alpha> \<diamond>w \<Turnstile> \<phi>{\<alpha>}\<close>
    by (metis "BF\<diamond>" "vdash-properties:10")
  then AOT_obtain \<alpha> where \<open>\<diamond>w \<Turnstile> \<phi>{\<alpha>}\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<open>w \<Turnstile> \<phi>{\<alpha>}\<close>
    using "rigid-truth-at:2"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"] by blast
  AOT_thus \<open>\<exists> \<alpha> w \<Turnstile> \<phi>{\<alpha>}\<close> by (rule "\<exists>I")
next
  AOT_assume \<open>\<exists>\<alpha> w \<Turnstile> \<phi>{\<alpha>}\<close>
  then AOT_obtain \<alpha> where \<open>w \<Turnstile> \<phi>{\<alpha>}\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<open>\<box>w \<Turnstile> \<phi>{\<alpha>}\<close>
    using "rigid-truth-at:1"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"] "&E" "&I" by blast
  AOT_hence \<open>\<exists>\<alpha> \<box>w \<Turnstile> \<phi>{\<alpha>}\<close> by (rule "\<exists>I")
  AOT_hence 0: \<open>\<box>\<exists>\<alpha> w \<Turnstile> \<phi>{\<alpha>}\<close> by (metis Buridan "vdash-properties:10")
  AOT_modally_strict {
    AOT_have \<open>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> ((\<exists>\<alpha> w \<Turnstile> \<phi>{\<alpha>}) \<rightarrow> (w \<Turnstile> (\<exists>\<alpha> \<phi>{\<alpha>})))\<close> for w
    proof(safe intro!: "\<rightarrow>I")
      AOT_assume \<open>\<forall> p (w \<Turnstile> p \<equiv> p)\<close>
      moreover AOT_assume \<open>\<exists>\<alpha> w \<Turnstile> \<phi>{\<alpha>}\<close>
      then AOT_obtain \<alpha> where \<open>w \<Turnstile> \<phi>{\<alpha>}\<close> using "\<exists>E"[rotated] by blast
      ultimately AOT_show \<open>w \<Turnstile> (\<exists>\<alpha> \<phi>{\<alpha>})\<close>
        by (metis "existential:2[const_var]" "\<equiv>E"(1) "\<equiv>E"(2) "log-prop-prop:2" "rule-ui:1")
    qed
  }
  AOT_hence \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> \<diamond>((\<exists>\<alpha> w \<Turnstile> \<phi>{\<alpha>}) \<rightarrow> w \<Turnstile> (\<exists>\<alpha> \<phi>{\<alpha>}))\<close> for w by (rule "RM\<diamond>")
  moreover AOT_have pos: \<open>\<diamond>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
    using "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF PossibleWorld.\<psi>] "&E" by blast
  ultimately AOT_have \<open>\<diamond>((\<exists>\<alpha> w \<Turnstile> \<phi>{\<alpha>}) \<rightarrow> w \<Turnstile> (\<exists>\<alpha> \<phi>{\<alpha>}))\<close> using "\<rightarrow>E" by blast
  AOT_hence \<open>\<diamond>(w \<Turnstile> (\<exists>\<alpha> \<phi>{\<alpha>}))\<close>
    by (metis 0 "KBasic2:4" "\<equiv>E"(1) "vdash-properties:10")
  AOT_thus \<open>w \<Turnstile> (\<exists>\<alpha> \<phi>{\<alpha>})\<close>
    using "rigid-truth-at:2"[unvarify p, THEN "\<equiv>E"(1), OF "log-prop-prop:2"] by blast
qed

AOT_theorem "conj-dist-w:7": \<open>(w \<Turnstile> \<box>p) \<rightarrow> \<box>w \<Turnstile> p\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>w \<Turnstile> \<box>p\<close>
  AOT_hence \<open>\<exists>w w \<Turnstile> \<box>p\<close> by (rule "PossibleWorld.\<exists>I")
  AOT_hence \<open>\<diamond>\<box>p\<close> using "fund:1"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(2)] by blast
  AOT_hence \<open>\<box>p\<close> by (metis "5\<diamond>" "vdash-properties:6")
  AOT_hence 1: \<open>\<box>\<box>p\<close> by (metis "S5Basic:6" "\<equiv>E"(1))
  AOT_have \<open>\<box>\<forall>w w \<Turnstile> p\<close>
    by (AOT_subst_rev \<open>\<guillemotleft>\<box>p\<guillemotright>\<close> \<open>\<guillemotleft>\<forall>w w \<Turnstile> p\<guillemotright>\<close>)
       (auto simp add: "fund:2" 1)
  AOT_hence \<open>\<forall>w \<box>w \<Turnstile> p\<close>
    using "fund-lem:5[world]"[THEN "\<rightarrow>E"] by simp
  AOT_thus \<open>\<box>w \<Turnstile> p\<close> using "\<rightarrow>E" "PossibleWorld.\<forall>E" by fast
qed

AOT_theorem "conj-dist-w:8": \<open>\<exists>w\<exists>p((\<box>w \<Turnstile> p) & \<not>w \<Turnstile> \<box>p)\<close>
proof -
  AOT_obtain r where A: r and \<open>\<diamond>\<not>r\<close>
    by (metis "&E"(1) "&E"(2) "\<equiv>\<^sub>d\<^sub>fE" "instantiation" "cont-tf:1" "cont-tf-thm:1")
  AOT_hence B: \<open>\<not>\<box>r\<close> by (metis "KBasic:11" "\<equiv>E"(2))
  AOT_have \<open>\<diamond>r\<close> using A "T\<diamond>"[THEN "\<rightarrow>E"] by simp
  AOT_hence \<open>\<exists>w w \<Turnstile> r\<close> using "fund:1"[THEN "\<equiv>E"(1)] by blast
  then AOT_obtain w where w: \<open>w \<Turnstile> r\<close> using "PossibleWorld.\<exists>E"[rotated] by meson
  AOT_hence \<open>\<box>w \<Turnstile> r\<close>
    by (metis "T\<diamond>" "\<equiv>E"(1) "rigid-truth-at:3" "vdash-properties:10")
  moreover AOT_have \<open>\<not>w \<Turnstile> \<box>r\<close>
  proof(rule "raa-cor:2")
    AOT_assume \<open>w \<Turnstile> \<box>r\<close>
    AOT_hence \<open>\<exists>w w \<Turnstile> \<box>r\<close> by (rule "PossibleWorld.\<exists>I")
    AOT_hence \<open>\<box>r\<close> by (metis "\<equiv>E"(2) "nec-dia-w:1")
    AOT_thus \<open>\<box>r & \<not>\<box>r\<close> using B "&I" by blast
  qed
  ultimately AOT_have \<open>\<box>w \<Turnstile> r & \<not>w \<Turnstile> \<box>r\<close> by (rule "&I")
  AOT_hence \<open>\<exists>p (\<box>w \<Turnstile> p & \<not>w \<Turnstile> \<box>p)\<close> by (rule "\<exists>I")
  thus ?thesis by (rule "PossibleWorld.\<exists>I")
qed

AOT_theorem "conj-dist-w:9": \<open>(\<diamond>w \<Turnstile> p) \<rightarrow> w \<Turnstile> \<diamond>p\<close>
proof(rule "\<rightarrow>I"; rule "raa-cor:1")
  AOT_assume \<open>\<diamond>w \<Turnstile> p\<close>
  AOT_hence 0: \<open>w \<Turnstile> p\<close> by (metis "\<equiv>E"(1) "rigid-truth-at:2")
  AOT_assume \<open>\<not>w \<Turnstile> \<diamond>p\<close>
  AOT_hence 1: \<open>w \<Turnstile> \<not>\<diamond>p\<close>
    using "coherent:1"[unvarify p, THEN "\<equiv>E"(2), OF "log-prop-prop:2"] by blast
  moreover AOT_have \<open>w \<Turnstile> (\<not>\<diamond>p \<rightarrow> \<not>p)\<close>
    using "T\<diamond>"[THEN "contraposition:1[1]", THEN RN]
          "fund:2"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1), THEN "\<forall>E"(2), THEN "\<rightarrow>E", rotated, OF PossibleWorld.\<psi>]
          by blast
  ultimately AOT_have \<open>w \<Turnstile> \<not>p\<close>
    using "conj-dist-w:2"[unvarify p q, OF "log-prop-prop:2", OF "log-prop-prop:2", THEN "\<equiv>E"(1), THEN "\<rightarrow>E"]
    by blast
  AOT_hence \<open>w \<Turnstile> p & w \<Turnstile> \<not>p\<close> using 0 "&I" by blast
  AOT_thus \<open>p & \<not>p\<close>
    by (metis "coherent:1" "Conjunction Simplification"(1) "Conjunction Simplification"(2) "\<equiv>E"(4) "modus-tollens:1" "raa-cor:3")
qed

AOT_theorem "conj-dist-w:10": \<open>\<exists>w\<exists>p((w \<Turnstile> \<diamond>p) & \<not>\<diamond>w \<Turnstile> p)\<close>
proof -
  AOT_obtain w where w: \<open>\<forall>p (w \<Turnstile> p \<equiv> p)\<close>
    using "act-world:1" "PossibleWorld.\<exists>E"[rotated] by meson
  AOT_obtain r where \<open>\<not>r\<close> and \<open>\<diamond>r\<close>
    using "cont-tf-thm:2" "cont-tf:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" "\<exists>E"[rotated] by metis
  AOT_hence \<open>w \<Turnstile> \<not>r\<close> and 0: \<open>w \<Turnstile> \<diamond>r\<close>
    using w[THEN "\<forall>E"(1), OF "log-prop-prop:2", THEN "\<equiv>E"(2)] by blast+
  AOT_hence \<open>\<not>w \<Turnstile> r\<close> using "coherent:1"[THEN "\<equiv>E"(1)] by blast
  AOT_hence \<open>\<not>\<diamond>w \<Turnstile> r\<close> by (metis "\<equiv>E"(4) "rigid-truth-at:2")
  AOT_hence \<open>w \<Turnstile> \<diamond>r & \<not>\<diamond>w \<Turnstile> r\<close> using 0 "&I" by blast
  AOT_hence \<open>\<exists>p (w \<Turnstile> \<diamond>p & \<not>\<diamond>w \<Turnstile> p)\<close> by (rule "\<exists>I")
  thus ?thesis by (rule "PossibleWorld.\<exists>I")
qed

AOT_theorem "two-worlds-exist:1": \<open>\<exists>p(ContingentlyTrue(p)) \<rightarrow> \<exists>w (\<not>Actual(w))\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<exists>p ContingentlyTrue(p)\<close>
  then AOT_obtain p where \<open>ContingentlyTrue(p)\<close> using "\<exists>E"[rotated] by blast
  AOT_hence p: \<open>p & \<diamond>\<not>p\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "cont-tf:1")
  AOT_hence \<open>\<exists>w w \<Turnstile> \<not>p\<close> using "fund:1"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)] "&E" by blast
  then AOT_obtain w where w: \<open>w \<Turnstile> \<not>p\<close> using "PossibleWorld.\<exists>E"[rotated] by meson
  AOT_have \<open>\<not>Actual(w)\<close>
  proof(rule "raa-cor:2")
    AOT_assume \<open>Actual(w)\<close>
    AOT_hence \<open>w \<Turnstile> p\<close> using p[THEN "&E"(1)] using actual[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2)]
      by (metis "log-prop-prop:2" "raa-cor:3" "rule-ui:1" "vdash-properties:10" w)
    moreover AOT_have \<open>\<not>(w \<Turnstile> p)\<close> by (metis "coherent:1" "\<equiv>E"(4) "reductio-aa:2" w) 
    ultimately AOT_show \<open>w \<Turnstile> p & \<not>(w \<Turnstile> p)\<close> using "&I" by blast
  qed
  AOT_thus \<open>\<exists>w \<not>Actual(w)\<close> by (rule "PossibleWorld.\<exists>I")
qed


AOT_theorem "two-worlds-exist:2": \<open>\<exists>p(ContingentlyFalse(p)) \<rightarrow> \<exists>w (\<not>Actual(w))\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<exists>p ContingentlyFalse(p)\<close>
  then AOT_obtain p where \<open>ContingentlyFalse(p)\<close> using "\<exists>E"[rotated] by blast
  AOT_hence p: \<open>\<not>p & \<diamond>p\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "cont-tf:2")
  AOT_hence \<open>\<exists>w w \<Turnstile> p\<close> using "fund:1"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)] "&E" by blast
  then AOT_obtain w where w: \<open>w \<Turnstile> p\<close> using "PossibleWorld.\<exists>E"[rotated] by meson
  moreover AOT_have \<open>\<not>Actual(w)\<close>
  proof(rule "raa-cor:2")
    AOT_assume \<open>Actual(w)\<close>
    AOT_hence \<open>w \<Turnstile> \<not>p\<close> using p[THEN "&E"(1)] using actual[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2)]
      by (metis "log-prop-prop:2" "raa-cor:3" "rule-ui:1" "vdash-properties:10" w)
    moreover AOT_have \<open>\<not>(w \<Turnstile> p)\<close>
      using calculation by (metis "coherent:1" "\<equiv>E"(4) "reductio-aa:2") 
    AOT_thus \<open>w \<Turnstile> p & \<not>(w \<Turnstile> p)\<close> using "&I" w by metis
  qed
  AOT_thus \<open>\<exists>w \<not>Actual(w)\<close> by (rule "PossibleWorld.\<exists>I")
qed

AOT_theorem "two-worlds-exist:3": \<open>\<exists>w \<not>Actual(w)\<close>
  using "cont-tf-thm:1" "two-worlds-exist:1" "vdash-properties:10" by blast

AOT_theorem "two-worlds-exist:4": \<open>\<exists>w\<exists>w'(w \<noteq> w')\<close>
proof -
  AOT_obtain w where w: \<open>Actual(w)\<close>
    using "act-world:2"[THEN "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "cqt-further:5"[THEN "\<rightarrow>E"]] "PossibleWorld.\<exists>E"[rotated] "&E"
    by blast
  moreover AOT_obtain w' where w': \<open>\<not>Actual(w')\<close> using "two-worlds-exist:3" "PossibleWorld.\<exists>E"[rotated] by meson
  AOT_have \<open>\<not>(w = w')\<close>
  proof(rule "raa-cor:2")
    AOT_assume \<open>w = w'\<close>
    AOT_thus \<open>p & \<not>p\<close> for p using w w' "&E" by (metis "rule=E" "raa-cor:3")
  qed
  AOT_hence \<open>w \<noteq> w'\<close> by (metis "\<equiv>\<^sub>d\<^sub>fI" "=-infix")
  AOT_hence \<open>\<exists>w' w \<noteq> w'\<close> by (rule "PossibleWorld.\<exists>I")
  thus ?thesis by (rule "PossibleWorld.\<exists>I")
qed

(* TODO: more theorems *)

AOT_theorem "w-rel:1": \<open>[\<lambda>x \<phi>{x}]\<down> \<rightarrow> [\<lambda>x w \<Turnstile> \<phi>{x}]\<down>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>[\<lambda>x \<phi>{x}]\<down>\<close>
  AOT_hence \<open>\<box>[\<lambda>x \<phi>{x}]\<down>\<close> by (metis "exist-nec" "vdash-properties:10")
  moreover AOT_have \<open>\<box>[\<lambda>x \<phi>{x}]\<down> \<rightarrow> \<box>\<forall>x\<forall>y(\<forall>F([F]x \<equiv> [F]y) \<rightarrow> ((w \<Turnstile> \<phi>{x}) \<equiv> ( w \<Turnstile> \<phi>{y})))\<close>
  proof (rule RM; rule "\<rightarrow>I"; rule GEN; rule GEN; rule "\<rightarrow>I")
    AOT_modally_strict {
      fix x y
      AOT_assume \<open>[\<lambda>x \<phi>{x}]\<down>\<close>
      AOT_hence \<open>\<forall>x\<forall>y (\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> \<box>(\<phi>{x} \<equiv> \<phi>{y}))\<close>
        using "&E" "kirchner-thm-cor:1"[THEN "\<rightarrow>E"] by blast
      AOT_hence \<open>\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> \<box>(\<phi>{x} \<equiv> \<phi>{y})\<close> using "\<forall>E"(2) by blast
      moreover AOT_assume \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
      ultimately AOT_have \<open>\<box>(\<phi>{x} \<equiv> \<phi>{y})\<close> using "\<rightarrow>E" by blast
      AOT_hence \<open>\<forall>w (w \<Turnstile> (\<phi>{x} \<equiv> \<phi>{y}))\<close>
        using "fund:2"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)] by blast
      AOT_hence \<open>w \<Turnstile> (\<phi>{x} \<equiv> \<phi>{y})\<close>
        using "\<forall>E"(2) using PossibleWorld.\<psi> "\<rightarrow>E" by blast
      AOT_thus \<open>(w \<Turnstile> \<phi>{x}) \<equiv> (w \<Turnstile> \<phi>{y})\<close>
          using "conj-dist-w:4"[unvarify p q, OF "log-prop-prop:2", OF "log-prop-prop:2", THEN "\<equiv>E"(1)] by blast
    }
  qed
  ultimately AOT_have \<open>\<box>\<forall>x\<forall>y(\<forall>F([F]x \<equiv> [F]y) \<rightarrow> ((w \<Turnstile> \<phi>{x}) \<equiv> ( w \<Turnstile> \<phi>{y})))\<close>
    using "\<rightarrow>E" by blast
  AOT_thus \<open>[\<lambda>x w \<Turnstile> \<phi>{x}]\<down>\<close>
    using "kirchner-thm:1"[THEN "\<equiv>E"(2)] by fast
qed

AOT_theorem "w-rel:2": \<open>[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]\<down> \<rightarrow> [\<lambda>x\<^sub>1...x\<^sub>n w \<Turnstile> \<phi>{x\<^sub>1...x\<^sub>n}]\<down>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]\<down>\<close>
  AOT_hence \<open>\<box>[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]\<down>\<close> by (metis "exist-nec" "vdash-properties:10")
  moreover AOT_have \<open>\<box>[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]\<down> \<rightarrow> \<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n\<forall>y\<^sub>1...\<forall>y\<^sub>n(\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) \<rightarrow> ((w \<Turnstile> \<phi>{x\<^sub>1...x\<^sub>n}) \<equiv> ( w \<Turnstile> \<phi>{y\<^sub>1...y\<^sub>n})))\<close>
  proof (rule RM; rule "\<rightarrow>I"; rule GEN; rule GEN; rule "\<rightarrow>I")
    AOT_modally_strict {
      fix x\<^sub>1x\<^sub>n y\<^sub>1y\<^sub>n
      AOT_assume \<open>[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]\<down>\<close>
      AOT_hence \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n\<forall>y\<^sub>1...\<forall>y\<^sub>n (\<forall>F ([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) \<rightarrow> \<box>(\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n}))\<close>
        using "&E" "kirchner-thm-cor:2"[THEN "\<rightarrow>E"] by blast
      AOT_hence \<open>\<forall>F ([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) \<rightarrow> \<box>(\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n})\<close> using "\<forall>E"(2) by blast
      moreover AOT_assume \<open>\<forall>F ([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n)\<close>
      ultimately AOT_have \<open>\<box>(\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n})\<close> using "\<rightarrow>E" by blast
      AOT_hence \<open>\<forall>w (w \<Turnstile> (\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n}))\<close>
        using "fund:2"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)] by blast
      AOT_hence \<open>w \<Turnstile> (\<phi>{x\<^sub>1...x\<^sub>n} \<equiv> \<phi>{y\<^sub>1...y\<^sub>n})\<close>
        using "\<forall>E"(2) using PossibleWorld.\<psi> "\<rightarrow>E" by blast
      AOT_thus \<open>(w \<Turnstile> \<phi>{x\<^sub>1...x\<^sub>n}) \<equiv> (w \<Turnstile> \<phi>{y\<^sub>1...y\<^sub>n})\<close>
          using "conj-dist-w:4"[unvarify p q, OF "log-prop-prop:2", OF "log-prop-prop:2", THEN "\<equiv>E"(1)] by blast
    }
  qed
  ultimately AOT_have \<open>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n\<forall>y\<^sub>1...\<forall>y\<^sub>n(\<forall>F([F]x\<^sub>1...x\<^sub>n \<equiv> [F]y\<^sub>1...y\<^sub>n) \<rightarrow> ((w \<Turnstile> \<phi>{x\<^sub>1...x\<^sub>n}) \<equiv> ( w \<Turnstile> \<phi>{y\<^sub>1...y\<^sub>n})))\<close>
    using "\<rightarrow>E" by blast
  AOT_thus \<open>[\<lambda>x\<^sub>1...x\<^sub>n w \<Turnstile> \<phi>{x\<^sub>1...x\<^sub>n}]\<down>\<close>
    using "kirchner-thm:2"[THEN "\<equiv>E"(2)] by fast
qed

AOT_theorem "w-rel:3": \<open>[\<lambda>x\<^sub>1...x\<^sub>n w \<Turnstile> [F]x\<^sub>1...x\<^sub>n]\<down>\<close>
  by (rule "w-rel:2"[THEN "\<rightarrow>E"]) "cqt:2[lambda]"

AOT_define WorldIndexedRelation :: \<open>\<Pi> \<Rightarrow> \<tau> \<Rightarrow> \<Pi>\<close> (\<open>_\<^sub>_\<close>)
  "w-index": \<open>[F]\<^sub>w =\<^sub>d\<^sub>f [\<lambda>x\<^sub>1...x\<^sub>n w \<Turnstile> [F]x\<^sub>1...x\<^sub>n]\<close>

AOT_define Rigid :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>Rigid'(_')\<close>)
  "df-rigid-rel:1": \<open>Rigid(F) \<equiv>\<^sub>d\<^sub>f F\<down> & \<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n([F]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[F]x\<^sub>1...x\<^sub>n)\<close>

AOT_define Rigidifies :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>Rigidifies'(_,_')\<close>)
  "df-rigid-rel:2": \<open>Rigidifies(F, G) \<equiv>\<^sub>d\<^sub>f Rigid(F) & \<forall>x\<^sub>1...\<forall>x\<^sub>n([F]x\<^sub>1...x\<^sub>n \<equiv> [G]x\<^sub>1...x\<^sub>n)\<close>

AOT_theorem "rigid-der:1": \<open>[[F]\<^sub>w]x\<^sub>1...x\<^sub>n \<equiv> w \<Turnstile> [F]x\<^sub>1...x\<^sub>n\<close>
  apply (rule "rule-id-def:2:b[2]"[where \<tau>="\<lambda> (\<Pi>, \<kappa>). \<guillemotleft>[\<Pi>]\<^sub>\<kappa>\<guillemotright>" and \<sigma>="\<lambda>(\<Pi>, \<kappa>). \<guillemotleft>[\<lambda>x\<^sub>1...x\<^sub>n \<kappa> \<Turnstile> [\<Pi>]x\<^sub>1...x\<^sub>n]\<guillemotright>", simplified, OF "w-index"])
   apply (fact "w-rel:3")
  apply (rule "beta-C-meta"[THEN "\<rightarrow>E"])
  by (fact "w-rel:3")

AOT_theorem "rigid-der:2": \<open>Rigid([G]\<^sub>w)\<close>
proof(safe intro!: "\<equiv>\<^sub>d\<^sub>fI"[OF "df-rigid-rel:1"] "&I")
  AOT_show \<open>[G]\<^sub>w\<down>\<close>
    by (rule "rule-id-def:2:b[2]"[where \<tau>="\<lambda> (\<Pi>, \<kappa>). \<guillemotleft>[\<Pi>]\<^sub>\<kappa>\<guillemotright>" and \<sigma>="\<lambda>(\<Pi>, \<kappa>). \<guillemotleft>[\<lambda>x\<^sub>1...x\<^sub>n \<kappa> \<Turnstile> [\<Pi>]x\<^sub>1...x\<^sub>n]\<guillemotright>", simplified, OF "w-index"])
       (fact "w-rel:3")+
next
  AOT_have \<open>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([[G]\<^sub>w]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[[G]\<^sub>w]x\<^sub>1...x\<^sub>n)\<close>
  proof(rule RN; safe intro!: "\<rightarrow>I" GEN)
    AOT_modally_strict {
      AOT_have assms: \<open>PossibleWorld(w)\<close> using PossibleWorld.\<psi>.
      AOT_hence nec_pw_w: \<open>\<box>PossibleWorld(w)\<close>
        using "\<equiv>E"(1) "rigid-pw:1" by blast
      fix x\<^sub>1x\<^sub>n
      AOT_assume \<open>[[G]\<^sub>w]x\<^sub>1...x\<^sub>n\<close>
      AOT_hence \<open>[\<lambda>x\<^sub>1...x\<^sub>n w \<Turnstile> [G]x\<^sub>1...x\<^sub>n]x\<^sub>1...x\<^sub>n\<close>
        using "rule-id-def:2:a[2]"[where \<tau>="\<lambda> (\<Pi>, \<kappa>). \<guillemotleft>[\<Pi>]\<^sub>\<kappa>\<guillemotright>" and \<sigma>="\<lambda>(\<Pi>, \<kappa>). \<guillemotleft>[\<lambda>x\<^sub>1...x\<^sub>n \<kappa> \<Turnstile> [\<Pi>]x\<^sub>1...x\<^sub>n]\<guillemotright>", simplified, OF "w-index", OF "w-rel:3"]
        by fast
      AOT_hence \<open>w \<Turnstile> [G]x\<^sub>1...x\<^sub>n\<close>
        by (metis "\<beta>\<rightarrow>C"(1))
      AOT_hence \<open>\<box>w \<Turnstile> [G]x\<^sub>1...x\<^sub>n\<close>
        using "rigid-truth-at:1"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)] by blast
      moreover AOT_have \<open>\<box>w \<Turnstile> [G]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[\<lambda>x\<^sub>1...x\<^sub>n w \<Turnstile> [G]x\<^sub>1...x\<^sub>n]x\<^sub>1...x\<^sub>n\<close>
      proof (rule RM; rule "\<rightarrow>I")
        AOT_modally_strict {
          AOT_assume 1: \<open>w \<Turnstile> [G]x\<^sub>1...x\<^sub>n\<close>
          AOT_show \<open>[\<lambda>x\<^sub>1...x\<^sub>n w \<Turnstile> [G]x\<^sub>1...x\<^sub>n]x\<^sub>1...x\<^sub>n\<close>
            by (rule "\<beta>\<leftarrow>C"(1); fact "w-rel:3")
               (auto simp: 1 "cqt:2[const_var]" "vdash-properties:1[2]")
        }
      qed
      ultimately AOT_have 1: \<open>\<box>[\<lambda>x\<^sub>1...x\<^sub>n w \<Turnstile> [G]x\<^sub>1...x\<^sub>n]x\<^sub>1...x\<^sub>n\<close>
        using "\<rightarrow>E" by blast
      AOT_show \<open>\<box>[[G]\<^sub>w]x\<^sub>1...x\<^sub>n\<close>
        by (rule "rule-id-def:2:b[2]"[where \<tau>="\<lambda> (\<Pi>, \<kappa>). \<guillemotleft>[\<Pi>]\<^sub>\<kappa>\<guillemotright>" and \<sigma>="\<lambda>(\<Pi>, \<kappa>). \<guillemotleft>[\<lambda>x\<^sub>1...x\<^sub>n \<kappa> \<Turnstile> [\<Pi>]x\<^sub>1...x\<^sub>n]\<guillemotright>", simplified, OF "w-index"])
           (auto simp: 1 "w-rel:3")
    }
  qed
  AOT_thus \<open>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([[G]\<^sub>w]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[[G]\<^sub>w]x\<^sub>1...x\<^sub>n)\<close> using "\<rightarrow>E" by blast
qed

AOT_theorem "rigid-der:3": \<open>\<exists>F Rigidifies(F, G)\<close>
proof -
  AOT_obtain w where w: \<open>\<forall>p (w \<Turnstile> p \<equiv> p)\<close> using "act-world:1" "PossibleWorld.\<exists>E"[rotated] by meson
  show ?thesis
  proof (rule "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>[G]\<^sub>w\<guillemotright>\<close>])
    AOT_show \<open>Rigidifies([G]\<^sub>w, [G])\<close>
    proof(safe intro!: "\<equiv>\<^sub>d\<^sub>fI"[OF "df-rigid-rel:2"] "&I" GEN)
      AOT_show \<open>Rigid([G]\<^sub>w)\<close> using "rigid-der:2" by blast (* TODO: PLM misses to apply to thereom in proof of A *)
    next
      fix x\<^sub>1x\<^sub>n
      AOT_have \<open>[[G]\<^sub>w]x\<^sub>1...x\<^sub>n \<equiv> [\<lambda>x\<^sub>1...x\<^sub>n w \<Turnstile> [G]x\<^sub>1...x\<^sub>n]x\<^sub>1...x\<^sub>n\<close>
      proof(rule "\<equiv>I"; rule "\<rightarrow>I")
        AOT_assume \<open>[[G]\<^sub>w]x\<^sub>1...x\<^sub>n\<close>
        AOT_thus \<open>[\<lambda>x\<^sub>1...x\<^sub>n w \<Turnstile> [G]x\<^sub>1...x\<^sub>n]x\<^sub>1...x\<^sub>n\<close>
          by (rule "rule-id-def:2:a[2]"[where \<tau>="\<lambda> (\<Pi>, \<kappa>). \<guillemotleft>[\<Pi>]\<^sub>\<kappa>\<guillemotright>" and \<sigma>="\<lambda>(\<Pi>, \<kappa>). \<guillemotleft>[\<lambda>x\<^sub>1...x\<^sub>n \<kappa> \<Turnstile> [\<Pi>]x\<^sub>1...x\<^sub>n]\<guillemotright>", simplified, OF "w-index", OF "w-rel:3"])
      next
        AOT_assume \<open>[\<lambda>x\<^sub>1...x\<^sub>n w \<Turnstile> [G]x\<^sub>1...x\<^sub>n]x\<^sub>1...x\<^sub>n\<close>
        AOT_thus \<open>[[G]\<^sub>w]x\<^sub>1...x\<^sub>n\<close>
          by (rule "rule-id-def:2:b[2]"[where \<tau>="\<lambda> (\<Pi>, \<kappa>). \<guillemotleft>[\<Pi>]\<^sub>\<kappa>\<guillemotright>" and \<sigma>="\<lambda>(\<Pi>, \<kappa>). \<guillemotleft>[\<lambda>x\<^sub>1...x\<^sub>n \<kappa> \<Turnstile> [\<Pi>]x\<^sub>1...x\<^sub>n]\<guillemotright>", simplified, OF "w-index", OF "w-rel:3"])
      qed
      also AOT_have \<open>\<dots> \<equiv> w \<Turnstile> [G]x\<^sub>1...x\<^sub>n\<close>
        by (rule "beta-C-meta"[THEN "\<rightarrow>E"])
           (fact "w-rel:3")
      also AOT_have \<open>\<dots> \<equiv> [G]x\<^sub>1...x\<^sub>n\<close> using w[THEN "\<forall>E"(1), OF "log-prop-prop:2"] by blast
      finally AOT_show \<open>[[G]\<^sub>w]x\<^sub>1...x\<^sub>n \<equiv> [G]x\<^sub>1...x\<^sub>n\<close>.
    qed
  next
    AOT_show \<open>[G]\<^sub>w\<down>\<close>
      by (rule "rule-id-def:2:b[2]"[where \<tau>="\<lambda> (\<Pi>, \<kappa>). \<guillemotleft>[\<Pi>]\<^sub>\<kappa>\<guillemotright>" and \<sigma>="\<lambda>(\<Pi>, \<kappa>). \<guillemotleft>[\<lambda>x\<^sub>1...x\<^sub>n \<kappa> \<Turnstile> [\<Pi>]x\<^sub>1...x\<^sub>n]\<guillemotright>", simplified, OF "w-index"])
         (auto simp: "w-rel:3")
  qed
qed

AOT_theorem "rigid-rel-thms:1": \<open>\<box>(\<forall>x\<^sub>1...\<forall>x\<^sub>n ([F]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[F]x\<^sub>1...x\<^sub>n)) \<equiv> \<forall>x\<^sub>1...\<forall>x\<^sub>n(\<diamond>[F]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[F]x\<^sub>1...x\<^sub>n)\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I" GEN)
  fix x\<^sub>1x\<^sub>n
  AOT_assume \<open>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([F]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[F]x\<^sub>1...x\<^sub>n)\<close>
  AOT_hence \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n \<box>([F]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[F]x\<^sub>1...x\<^sub>n)\<close>
    by (metis "\<rightarrow>E" GEN RM "cqt-orig:3")
  AOT_hence \<open>\<box>([F]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[F]x\<^sub>1...x\<^sub>n)\<close>
    using "\<forall>E"(2) by blast
  AOT_hence \<open>\<diamond>[F]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[F]x\<^sub>1...x\<^sub>n\<close>
    by (metis "\<equiv>E"(1) "sc-eq-box-box:1")
  moreover AOT_assume \<open>\<diamond>[F]x\<^sub>1...x\<^sub>n\<close>
  ultimately AOT_show \<open>\<box>[F]x\<^sub>1...x\<^sub>n\<close> using "\<rightarrow>E" by blast
next
  AOT_assume \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n (\<diamond>[F]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[F]x\<^sub>1...x\<^sub>n)\<close>
  AOT_hence \<open>\<diamond>[F]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[F]x\<^sub>1...x\<^sub>n\<close> for x\<^sub>1x\<^sub>n using "\<forall>E"(2) by blast
  AOT_hence \<open>\<box>([F]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[F]x\<^sub>1...x\<^sub>n)\<close> for x\<^sub>1x\<^sub>n by (metis "\<equiv>E"(2) "sc-eq-box-box:1")
  AOT_hence 0: \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n \<box>([F]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[F]x\<^sub>1...x\<^sub>n)\<close> by (rule GEN)
  AOT_thus \<open>\<box>(\<forall>x\<^sub>1...\<forall>x\<^sub>n ([F]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[F]x\<^sub>1...x\<^sub>n))\<close>
    using "BF" "vdash-properties:10" by blast
qed

AOT_theorem "rigid-rel-thms:2": \<open>\<box>(\<forall>x\<^sub>1...\<forall>x\<^sub>n ([F]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[F]x\<^sub>1...x\<^sub>n)) \<equiv> \<forall>x\<^sub>1...\<forall>x\<^sub>n(\<box>[F]x\<^sub>1...x\<^sub>n \<or> \<box>\<not>[F]x\<^sub>1...x\<^sub>n)\<close>
  oops (* TODO *)

AOT_theorem "rigid-rel-thms:3": \<open>Rigid(F) \<equiv> \<forall>x\<^sub>1...\<forall>x\<^sub>n (\<box>[F]x\<^sub>1...x\<^sub>n \<or> \<box>\<not>[F]x\<^sub>1...x\<^sub>n)\<close>
  oops (* TODO *)

(*<*)
end
(*>*)
