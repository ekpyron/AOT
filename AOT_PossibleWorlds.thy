theory AOT_PossibleWorlds
  imports AOT_PLM AOT_BasicLogicalObjects
begin

AOT_define situation :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>Situation'(_')\<close>)
  situations: \<open>Situation(x) \<equiv>\<^sub>d\<^sub>f A!x & \<forall>F (x[F] \<rightarrow> Propositional([F]))\<close>

AOT_theorem T_sit: \<open>TruthValue(x) \<rightarrow> Situation(x)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>TruthValue(x)\<close>
  AOT_hence \<open>\<exists>p TruthValueOf(x,p)\<close>
    using T_value[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain p where \<open>TruthValueOf(x,p)\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<theta>: \<open>A!x & \<forall>F (x[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q]))\<close>
    using tv_p[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_show \<open>Situation(x)\<close>
  proof(rule situations[THEN "\<equiv>\<^sub>d\<^sub>fI"]; safe intro!: "&I" GEN "\<rightarrow>I" \<theta>[THEN "&E"(1)])
    fix F
    AOT_assume \<open>x[F]\<close>
    AOT_hence \<open>\<exists>q((q \<equiv> p) & F = [\<lambda>y q])\<close>
      using \<theta>[THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=F], THEN "\<equiv>E"(1)] by argo
    then AOT_obtain q where \<open>(q \<equiv> p) & F = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
    AOT_hence \<open>\<exists>p F = [\<lambda>y p]\<close> using "&E"(2) "\<exists>I"(2) by metis
    AOT_thus \<open>Propositional([F])\<close>
      by (metis "\<equiv>\<^sub>d\<^sub>fI" prop_prop1)
  qed
qed

AOT_theorem possit_sit_1: \<open>Situation(x) \<equiv> \<box>Situation(x)\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>Situation(x)\<close>
  AOT_hence 0: \<open>A!x & \<forall>F (x[F] \<rightarrow> Propositional([F]))\<close>
    using situations[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_have 1: \<open>\<box>(A!x & \<forall>F (x[F] \<rightarrow> Propositional([F])))\<close>
  proof(rule KBasic_3[THEN "\<equiv>E"(2)]; rule "&I")
    AOT_show \<open>\<box>A!x\<close> using 0[THEN "&E"(1)] by (metis oa_facts_2[THEN "\<rightarrow>E"])
  next
    AOT_have \<open>\<forall>F (x[F] \<rightarrow> Propositional([F])) \<rightarrow> \<box>\<forall>F (x[F] \<rightarrow> Propositional([F]))\<close>
      by (AOT_subst \<open>\<lambda> \<Pi> . \<guillemotleft>Propositional([\<Pi>])\<guillemotright>\<close> \<open>\<lambda> \<Pi> . \<guillemotleft>\<exists>p (\<Pi> = [\<lambda>y p])\<guillemotright>\<close>)
    AOT_thus \<open>\<box>\<forall>F (x[F] \<rightarrow> Propositional([F]))\<close>
      using 0[THEN "&E"(2)] "\<rightarrow>E" by blast
  qed
  AOT_show \<open>\<box>Situation(x)\<close>
    by (AOT_subst \<open>\<guillemotleft>Situation(x)\<guillemotright>\<close> \<open>\<guillemotleft>A!x & \<forall>F (x[F] \<rightarrow> Propositional([F]))\<guillemotright>\<close>) (fact 1)
next
  AOT_show \<open>Situation(x)\<close> if \<open>\<box>Situation(x)\<close>
    using qml_2[axiom_inst, THEN "\<rightarrow>E", OF that].
qed

AOT_theorem possit_sit_2: \<open>\<diamond>Situation(x) \<equiv> Situation(x)\<close>
  using possit_sit_1
  by (metis "RE\<diamond>" S5Basic_2 intro_elim_3_a intro_elim_3_e oth_class_taut_2_e)

AOT_theorem possit_sit_3: \<open>\<diamond>Situation(x) \<equiv> \<box>Situation(x)\<close>
  using possit_sit_1 possit_sit_2 by (meson intro_elim_3_e)

AOT_theorem possit_sit_4: \<open>\<^bold>\<A>Situation(x) \<equiv> Situation(x)\<close>
  by (meson Act_Basic_5 Act_Sub_2 RA_2 intro_elim_3_a intro_elim_3_f possit_sit_2)


AOT_register_restricted_type
  Situation: \<open>Situation(\<kappa>)\<close>
proof
  AOT_modally_strict {
    fix p
    AOT_obtain x where \<open>TruthValueOf(x,p)\<close> by (metis "instantiation" p_has_tv_1)
    AOT_hence \<open>\<exists>p TruthValueOf(x,p)\<close> by (rule "\<exists>I")
    AOT_hence \<open>TruthValue(x)\<close> by (metis "\<equiv>\<^sub>d\<^sub>fI" T_value)
    AOT_hence \<open>Situation(x)\<close> using T_sit[THEN "\<rightarrow>E"] by blast
    AOT_thus \<open>\<exists>x Situation(x)\<close> by (rule "\<exists>I")
  }
next
  AOT_modally_strict {
    AOT_show \<open>Situation(\<kappa>) \<rightarrow> \<kappa>\<down>\<close> for \<kappa>
    proof (rule "\<rightarrow>I")
      AOT_assume \<open>Situation(\<kappa>)\<close>
      AOT_hence \<open>A!\<kappa>\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" con_dis_i_e_2_a situations)
      AOT_thus \<open>\<kappa>\<down>\<close> by (metis russell_axiom_exe_1.\<psi>_denotes_asm)
    qed
  }
qed
AOT_register_variable_names
  Situation: s

AOT_define true_in_s :: \<open>\<tau> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (infixl \<open>\<Turnstile>\<close> 49)
  \<open>x \<Turnstile> p \<equiv>\<^sub>d\<^sub>f Situation(x) & x\<^bold>\<Sigma>p\<close>

AOT_theorem lem1: \<open>Situation(x) \<rightarrow> ((x \<Turnstile> p) \<equiv> x[\<lambda>y p])\<close>
proof (rule "\<rightarrow>I"; rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>Situation(x)\<close>
  AOT_assume \<open>x \<Turnstile> p\<close>
  AOT_hence \<open>x\<^bold>\<Sigma>p\<close>
    using true_in_s[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_thus \<open>x[\<lambda>y p]\<close> using prop_enc[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
next
  AOT_assume 1: \<open>Situation(x)\<close>
  AOT_assume \<open>x[\<lambda>y p]\<close>
  AOT_hence \<open>x\<^bold>\<Sigma>p\<close>
    using prop_enc[THEN "\<equiv>\<^sub>d\<^sub>fI", OF "&I", OF cqt_2_const_var[axiom_inst]] by blast
  AOT_thus \<open>x \<Turnstile> p\<close>
    using true_in_s[THEN "\<equiv>\<^sub>d\<^sub>fI"] 1 "&I" by blast
qed

AOT_theorem lem2_1:
  assumes \<open>Situation(x)\<close>
  shows \<open>x \<Turnstile> p \<equiv> \<box>x \<Turnstile> p\<close>
proof -
  AOT_have \<open>x \<Turnstile> p \<equiv> x[\<lambda>y p]\<close>
    using lem1[THEN "\<rightarrow>E", OF assms] by blast
  also AOT_have \<open>\<dots> \<equiv> \<box>x[\<lambda>y p]\<close>
    by (rule en_eq_2_1[unvarify F]) cqt_2_lambda
  also AOT_have \<open>\<dots> \<equiv> \<box>(x \<Turnstile> p)\<close>
    using lem1[THEN RM, THEN "\<rightarrow>E", OF possit_sit_1[THEN "\<equiv>E"(1), OF assms]]
    by (metis KBasic_6 intro_elim_3_b oth_class_taut_2_e vdash_properties_10)
  finally show ?thesis.
qed

AOT_theorem lem2_2:
  assumes \<open>Situation(x)\<close>
  shows \<open>\<diamond>x \<Turnstile> p \<equiv> x \<Turnstile> p\<close>
proof -
  AOT_have \<open>\<box>(x \<Turnstile> p \<rightarrow> \<box>x \<Turnstile> p)\<close>
    using possit_sit_1[THEN "\<equiv>E"(1), OF assms] lem2_1[THEN AOT_equiv[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(1)]] RM[OF "\<rightarrow>I", THEN "\<rightarrow>E"] by blast
  thus ?thesis by (metis "B\<diamond>" S5Basic_13 T_S5_fund_1 intro_elim_2 intro_elim_3_a vdash_properties_10)
qed

AOT_theorem lem2_3:
  assumes \<open>Situation(x)\<close>
  shows \<open>\<diamond>x \<Turnstile> p \<equiv> \<box>x \<Turnstile> p\<close>
  using lem2_1[OF assms] lem2_2[OF assms] by (metis intro_elim_3_e)

AOT_theorem lem2_4:
  assumes \<open>Situation(x)\<close>
  shows \<open>\<^bold>\<A>x \<Turnstile> p \<equiv> x \<Turnstile> p\<close>
proof -
  AOT_have \<open>\<box>(x \<Turnstile> p \<rightarrow> \<box>x \<Turnstile> p)\<close>
    using possit_sit_1[THEN "\<equiv>E"(1), OF assms] lem2_1[THEN AOT_equiv[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(1)]] RM[OF "\<rightarrow>I", THEN "\<rightarrow>E"] by blast
  thus ?thesis
    using sc_eq_fur_2[THEN "\<rightarrow>E"] by blast
qed

AOT_theorem lem2_5:
  assumes \<open>Situation(x)\<close>
  shows \<open>\<not>(x \<Turnstile> p) \<equiv> \<box>\<not>(x \<Turnstile> p)\<close>
  by (metis KBasic2_1 assms contraposition_1_b deduction_theorem intro_elim_2 intro_elim_3_c intro_elim_3_d lem2_2)

AOT_theorem sit_identity:
  assumes \<open>Situation(x)\<close> and \<open>Situation(x')\<close>
  shows \<open>x = x' \<equiv> \<forall>p(x \<Turnstile> p \<equiv> x' \<Turnstile> p)\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>x = x'\<close>
  moreover AOT_have \<open>\<forall>p(x \<Turnstile> p \<equiv> x \<Turnstile> p)\<close>
    by (simp add: oth_class_taut_3_a universal_cor)
  ultimately AOT_show \<open>\<forall>p(x \<Turnstile> p \<equiv> x' \<Turnstile> p)\<close>
    using "=E" by fast
next
  AOT_assume a: \<open>\<forall>p (x \<Turnstile> p \<equiv> x' \<Turnstile> p)\<close>
  AOT_show \<open>x = x'\<close>
  proof(safe intro!: ab_obey_1[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "&I" GEN "\<equiv>I" "\<rightarrow>I")
    AOT_show \<open>A!x\<close> using assms(1) "\<equiv>\<^sub>d\<^sub>fE" con_dis_i_e_2_a situations by blast
  next
    AOT_show \<open>A!x'\<close> using assms(2) "\<equiv>\<^sub>d\<^sub>fE" con_dis_i_e_2_a situations by blast
  next
    fix F
    AOT_assume 0: \<open>x[F]\<close>
    AOT_hence \<open>\<exists>p (F = [\<lambda>y p])\<close>
      using assms(1)[THEN situations[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=F], THEN "\<rightarrow>E"]
            prop_prop1[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
    then AOT_obtain p where F_def: \<open>F = [\<lambda>y p]\<close>
      using "\<exists>E" by metis
    AOT_hence \<open>x[\<lambda>y p]\<close> using 0 "=E" by blast
    AOT_hence \<open>x \<Turnstile> p\<close> using lem1[THEN "\<rightarrow>E", OF assms(1), THEN "\<equiv>E"(2)] by blast
    AOT_hence \<open>x' \<Turnstile> p\<close> using a[THEN "\<forall>E"(2)[where \<beta>=p], THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>x'[\<lambda>y p]\<close> using lem1[THEN "\<rightarrow>E", OF assms(2), THEN "\<equiv>E"(1)] by blast
    AOT_thus \<open>x'[F]\<close> using F_def[symmetric] "=E" by blast
  next
    fix F
    AOT_assume 0: \<open>x'[F]\<close>
    AOT_hence \<open>\<exists>p (F = [\<lambda>y p])\<close>
      using assms(2)[THEN situations[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=F], THEN "\<rightarrow>E"]
            prop_prop1[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
    then AOT_obtain p where F_def: \<open>F = [\<lambda>y p]\<close>
      using "\<exists>E" by metis
    AOT_hence \<open>x'[\<lambda>y p]\<close> using 0 "=E" by blast
    AOT_hence \<open>x' \<Turnstile> p\<close> using lem1[THEN "\<rightarrow>E", OF assms(2), THEN "\<equiv>E"(2)] by blast
    AOT_hence \<open>x \<Turnstile> p\<close> using a[THEN "\<forall>E"(2)[where \<beta>=p], THEN "\<equiv>E"(2)] by blast
    AOT_hence \<open>x[\<lambda>y p]\<close> using lem1[THEN "\<rightarrow>E", OF assms(1), THEN "\<equiv>E"(1)] by blast
    AOT_thus \<open>x[F]\<close> using F_def[symmetric] "=E" by blast
  qed
qed

AOT_define sit_part_whole :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl \<open>\<unlhd>\<close> 80)
  \<open>x \<unlhd> y \<equiv>\<^sub>d\<^sub>f Situation(x) & Situation(y) & \<forall>p (x \<Turnstile> p \<rightarrow> y \<Turnstile> p)\<close>

AOT_theorem part_1: assumes \<open>Situation(x)\<close> shows \<open>x \<unlhd> x\<close>
  by (rule sit_part_whole[THEN "\<equiv>\<^sub>d\<^sub>fI"])
     (safe intro!: "&I" assms GEN "\<rightarrow>I")

(* TODO: PLM: this is unnecessarily restricted to situations in PLM, which is implicit in \<unlhd> *)
AOT_theorem part_2: \<open>x \<unlhd> y & x \<noteq> y \<rightarrow> \<not>(y \<unlhd> x)\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2); rule raa_cor_2)
  AOT_assume 0: \<open>x \<unlhd> y\<close>
  AOT_hence a: \<open>x \<Turnstile> p \<rightarrow> y \<Turnstile> p\<close> for p using "\<forall>E"(2) sit_part_whole[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_assume \<open>y \<unlhd> x\<close>
  AOT_hence b: \<open>y \<Turnstile> p \<rightarrow> x \<Turnstile> p\<close> for p using "\<forall>E"(2) sit_part_whole[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_have \<open>\<forall>p (x \<Turnstile> p \<equiv> y \<Turnstile> p)\<close> using a b by (simp add: intro_elim_2 universal_cor)
  AOT_hence 1: \<open>x = y\<close> using sit_identity[THEN "\<equiv>E"(2)]
    using 0[THEN sit_part_whole[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(1)] "&E" by blast
  AOT_assume \<open>x \<noteq> y\<close>
  AOT_hence \<open>\<not>(x = y)\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" noneq_infix)
  AOT_thus \<open>x = y & \<not>(x = y)\<close> using 1 "&I" by blast
qed

(* TODO: PLM: this is unnecessarily restricted to situations in PLM, which is implicit in \<unlhd> *)
AOT_theorem part_3: \<open>x \<unlhd> y & y \<unlhd> z \<rightarrow> x \<unlhd> z\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2); safe intro!: "&I" GEN "\<rightarrow>I" sit_part_whole[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_show \<open>Situation(x)\<close> if \<open>x \<unlhd> y\<close> using that[THEN sit_part_whole[THEN "\<equiv>\<^sub>d\<^sub>fE"]] "&E" by blast
next
  AOT_show \<open>Situation(z)\<close> if \<open>y \<unlhd> z\<close> using that[THEN sit_part_whole[THEN "\<equiv>\<^sub>d\<^sub>fE"]] "&E" by blast
next
  fix p
  AOT_assume \<open>x \<Turnstile> p\<close>
  moreover AOT_assume \<open>x \<unlhd> y\<close>
  ultimately AOT_have \<open>y \<Turnstile> p\<close>
    using sit_part_whole[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=p], THEN "\<rightarrow>E"] by blast
  moreover AOT_assume \<open>y \<unlhd> z\<close>
  ultimately AOT_show \<open>z \<Turnstile> p\<close>
    using sit_part_whole[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=p], THEN "\<rightarrow>E"] by blast
qed

AOT_theorem sit_identity2_1: assumes \<open>Situation(x)\<close> and \<open>Situation(y)\<close>
  shows \<open>x = y \<equiv> x \<unlhd> y & y \<unlhd> x\<close>
proof (safe intro!: "\<equiv>I" "&I" "\<rightarrow>I")
  AOT_show \<open>x \<unlhd> y\<close> if \<open>x = y\<close>
    using "rule=E" assms(1) part_1 that by blast
next
  AOT_show \<open>y \<unlhd> x\<close> if \<open>x = y\<close>
    using "rule=E" assms(2) part_1 that[symmetric] by blast
next
  AOT_assume \<open>x \<unlhd> y & y \<unlhd> x\<close>
  AOT_thus \<open>x = y\<close> using part_2[THEN "\<rightarrow>E", OF "&I"]
    by (metis "\<equiv>\<^sub>d\<^sub>fI" con_dis_i_e_2_a con_dis_i_e_2_b noneq_infix raa_cor_3)
qed

AOT_theorem sit_identity2_2: assumes \<open>Situation(x)\<close> and \<open>Situation(y)\<close>
  shows \<open>x = y \<equiv> \<forall>s (s \<unlhd> x \<equiv> s \<unlhd> y)\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I" GEN sit_identity[THEN "\<equiv>E"(2), OF assms])
  AOT_show \<open>s \<unlhd> y\<close> if \<open>s \<unlhd> x\<close> and \<open>x = y\<close> for s
    using "rule=E" that by blast
next
  AOT_show \<open>s \<unlhd> x\<close> if \<open>s \<unlhd> y\<close> and \<open>x = y\<close> for s
    using "rule=E" id_sym that by blast
next
  AOT_show \<open>y \<Turnstile> p\<close> if \<open>x \<Turnstile> p\<close> and \<open>\<forall>s (s \<unlhd> x \<equiv> s \<unlhd> y)\<close> for p
    using sit_part_whole[THEN "\<equiv>\<^sub>d\<^sub>fE", OF that(2)[THEN "\<forall>E"(2),
          THEN "\<rightarrow>E", OF assms(1), THEN "\<equiv>E"(1), OF part_1[OF assms(1)]], THEN "&E"(2),
          THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF that(1)].
next
  AOT_show \<open>x \<Turnstile> p\<close> if \<open>y \<Turnstile> p\<close> and \<open>\<forall>s (s \<unlhd> x \<equiv> s \<unlhd> y)\<close> for p
    using sit_part_whole[THEN "\<equiv>\<^sub>d\<^sub>fE", OF that(2)[THEN "\<forall>E"(2),
          THEN "\<rightarrow>E", OF assms(2), THEN "\<equiv>E"(2), OF part_1[OF assms(2)]], THEN "&E"(2),
          THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF that(1)].
qed

AOT_define Persistent :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>Persistent'(_')\<close>)
  persistent: \<open>Persistent(p) \<equiv>\<^sub>d\<^sub>f \<forall>s (s \<Turnstile> p \<rightarrow> \<forall>s' (s \<unlhd> s' \<rightarrow> s' \<Turnstile> p))\<close>

AOT_theorem pers_prop: \<open>\<forall>p Persistent(p)\<close>
  by (safe intro!: GEN persistent[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<rightarrow>I")
     (simp add: sit_part_whole[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"])

AOT_define NullSituation :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>NullSituation'(_')\<close>)
  df_null_trivial_1: \<open>NullSituation(x) \<equiv>\<^sub>d\<^sub>f Situation(x) & \<not>\<exists>p x \<Turnstile> p\<close>

AOT_define TrivialSituation :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>TrivialSituation'(_')\<close>)
  df_null_trivial_2: \<open>TrivialSituation(x) \<equiv>\<^sub>d\<^sub>f Situation(x) & \<forall>p x \<Turnstile> p\<close>

AOT_theorem thm_null_trivial_1: \<open>\<exists>!x NullSituation(x)\<close>
proof (AOT_subst \<open>\<lambda> \<kappa> . \<guillemotleft>NullSituation(\<kappa>)\<guillemotright>\<close> \<open>\<lambda> \<kappa> . \<guillemotleft>A!\<kappa> & \<forall>F (\<kappa>[F] \<equiv> F \<noteq> F)\<guillemotright>\<close>)
  AOT_modally_strict {
    AOT_show \<open>NullSituation(x) \<equiv> A!x & \<forall>F (x[F] \<equiv> F \<noteq> F)\<close> for x
    proof (safe intro!: "\<equiv>I" "\<rightarrow>I" df_null_trivial_1[THEN "\<equiv>\<^sub>d\<^sub>fI"] dest!: df_null_trivial_1[THEN "\<equiv>\<^sub>d\<^sub>fE"])
      AOT_assume 0: \<open>Situation(x) & \<not>\<exists>p x \<Turnstile> p\<close>
      AOT_have 1: \<open>A!x\<close> using 0[THEN "&E"(1), THEN situations[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(1)].
      AOT_have 2: \<open>x[F] \<rightarrow> \<exists>p F = [\<lambda>y p]\<close> for F
        using 0[THEN "&E"(1), THEN situations[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2), THEN "\<forall>E"(2)]
        by (metis "\<equiv>\<^sub>d\<^sub>fE" deduction_theorem prop_prop1 "\<rightarrow>E")
      AOT_show \<open>A!x & \<forall>F (x[F] \<equiv> F \<noteq> F)\<close>
      proof (safe intro!: "&I" 1 GEN "\<equiv>I" "\<rightarrow>I")
        fix F
        AOT_assume \<open>x[F]\<close>
        moreover AOT_obtain p where \<open>F = [\<lambda>y p]\<close>
          using calculation 2[THEN "\<rightarrow>E"] "\<exists>E"[rotated] by blast
        ultimately AOT_have \<open>x[\<lambda>y p]\<close> by (metis "rule=E")
        AOT_hence \<open>x \<Turnstile> p\<close> using lem1[THEN "\<rightarrow>E", OF 0[THEN "&E"(1)], THEN "\<equiv>E"(2)] by blast
        AOT_hence \<open>\<exists>p x \<Turnstile> p\<close> by (rule "\<exists>I")
        AOT_thus \<open>F \<noteq> F\<close> using 0[THEN "&E"(2)] raa_cor_1 "&I" by blast
      next
        fix F :: \<open><\<kappa>> AOT_var\<close>
        AOT_assume \<open>F \<noteq> F\<close>
        AOT_hence \<open>\<not>(F = F)\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" noneq_infix)
        moreover AOT_have \<open>F = F\<close>
          by (simp add: id_eq_1)
        ultimately AOT_show \<open>x[F]\<close> using "&I" raa_cor_1 by blast
      qed
    next
      AOT_assume 0: \<open>A!x & \<forall>F (x[F] \<equiv> F \<noteq> F)\<close>
      AOT_hence \<open>x[F] \<equiv> F \<noteq> F\<close> for F using "\<forall>E" "&E" by blast
      AOT_hence 1: \<open>\<not>x[F]\<close> for F
        using "\<equiv>\<^sub>d\<^sub>fE" id_eq_1 noneq_infix reductio_aa_1 intro_elim_3_a by blast
      AOT_show \<open>Situation(x) & \<not>\<exists>p x \<Turnstile> p\<close>
      proof (safe intro!: "&I" situations[THEN "\<equiv>\<^sub>d\<^sub>fI"] 0[THEN "&E"(1)] GEN "\<rightarrow>I")
        AOT_show \<open>Propositional([F])\<close> if \<open>x[F]\<close> for F using that 1 "&I" raa_cor_1 by fast
      next
        AOT_show \<open>\<not>\<exists>p x \<Turnstile> p\<close>
        proof(rule raa_cor_2)
          AOT_assume \<open>\<exists>p x \<Turnstile> p\<close>
          then AOT_obtain p where \<open>x \<Turnstile> p\<close> using "\<exists>E"[rotated] by blast
          AOT_hence \<open>x[\<lambda>y p]\<close>
            using "\<equiv>\<^sub>d\<^sub>fE" con_dis_i_e_2_a intro_elim_3_a lem1 modus_tollens_1 raa_cor_3 true_in_s by fast
          moreover AOT_have \<open>\<not>x[\<lambda>y p]\<close>
            by (rule 1[unvarify F]) cqt_2_lambda
          ultimately AOT_show \<open>p & \<not>p\<close> for p using "&I" raa_cor_1 by blast
        qed
      qed
    qed
  }
qed


AOT_theorem thm_null_trivial_2: \<open>\<exists>!x TrivialSituation(x)\<close>
proof (AOT_subst \<open>\<lambda> \<kappa> . \<guillemotleft>TrivialSituation(\<kappa>)\<guillemotright>\<close> \<open>\<lambda> \<kappa> . \<guillemotleft>A!\<kappa> & \<forall>F (\<kappa>[F] \<equiv> \<exists>p F = [\<lambda>y p])\<guillemotright>\<close>)
  AOT_modally_strict {
    AOT_show \<open>TrivialSituation(x) \<equiv> A!x & \<forall>F (x[F] \<equiv> \<exists>p F = [\<lambda>y p])\<close> for x
    proof (safe intro!: "\<equiv>I" "\<rightarrow>I" df_null_trivial_2[THEN "\<equiv>\<^sub>d\<^sub>fI"] dest!: df_null_trivial_2[THEN "\<equiv>\<^sub>d\<^sub>fE"])
      AOT_assume 0: \<open>Situation(x) & \<forall>p x \<Turnstile> p\<close>
      AOT_have 1: \<open>A!x\<close> using 0[THEN "&E"(1), THEN situations[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(1)].
      AOT_have 2: \<open>x[F] \<rightarrow> \<exists>p F = [\<lambda>y p]\<close> for F
        using 0[THEN "&E"(1), THEN situations[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2), THEN "\<forall>E"(2)]
        by (metis "\<equiv>\<^sub>d\<^sub>fE" deduction_theorem prop_prop1 "\<rightarrow>E")
      AOT_show \<open>A!x & \<forall>F (x[F] \<equiv> \<exists>p F = [\<lambda>y p])\<close>
      proof (safe intro!: "&I" 1 GEN "\<equiv>I" "\<rightarrow>I" 2)
        fix F
        AOT_assume \<open>\<exists>p F = [\<lambda>y p]\<close>
        then AOT_obtain p where \<open>F = [\<lambda>y p]\<close> using "\<exists>E"[rotated] by blast
        moreover AOT_have \<open>x \<Turnstile> p\<close> using 0[THEN "&E"(2)] "\<forall>E" by blast
        ultimately AOT_show \<open>x[F]\<close>
          by (metis 0 "rule=E" con_dis_i_e_2_a id_sym intro_elim_3_b lem1 oth_class_taut_2_e "\<rightarrow>E")
      qed
    next
      AOT_assume 0: \<open>A!x & \<forall>F (x[F] \<equiv> \<exists>p F = [\<lambda>y p])\<close>
      AOT_hence 1: \<open>x[F] \<equiv> \<exists>p F = [\<lambda>y p]\<close> for F using "\<forall>E" "&E" by blast
      AOT_have 2: \<open>Situation(x)\<close>
      proof (safe intro!: "&I" situations[THEN "\<equiv>\<^sub>d\<^sub>fI"] 0[THEN "&E"(1)] GEN "\<rightarrow>I")
        AOT_show \<open>Propositional([F])\<close> if \<open>x[F]\<close> for F
          using 1[THEN "\<equiv>E"(1), OF that]
          by (metis "\<equiv>\<^sub>d\<^sub>fI" prop_prop1)
      qed
      AOT_show \<open>Situation(x) & \<forall>p x \<Turnstile> p\<close>
      proof (safe intro!: "&I" 2 0[THEN "&E"(1)] GEN "\<rightarrow>I")
        AOT_have \<open>x[\<lambda>y p] \<equiv> \<exists>q [\<lambda>y p] = [\<lambda>y q]\<close> for p
          by (rule 1[unvarify F, where \<tau>="\<guillemotleft>[\<lambda>y p]\<guillemotright>"]) cqt_2_lambda
        moreover AOT_have \<open>\<exists>q [\<lambda>y p] = [\<lambda>y q]\<close> for p
          by (rule_tac \<beta>=p in "\<exists>I"(2))
             (simp add: "rule=I_1" prop_prop2_2)
        ultimately AOT_have \<open>x[\<lambda>y p]\<close> for p by (metis intro_elim_3_b)
        AOT_thus \<open>x \<Turnstile> p\<close> for p
          by (metis "2" intro_elim_3_b lem1 "\<rightarrow>E")
      qed
    qed
  }
qed

AOT_theorem thm_null_trivial_3: \<open>\<^bold>\<iota>x NullSituation(x)\<down>\<close>
  by (meson A_Exists_2 RA_2 intro_elim_3_b thm_null_trivial_1)

AOT_theorem thm_null_trivial_4: \<open>\<^bold>\<iota>x TrivialSituation(x)\<down>\<close>
  using A_Exists_2 RA_2 intro_elim_3_b thm_null_trivial_2 by blast

AOT_define df_the_null_sit_1 :: \<open>\<kappa>\<^sub>s\<close> (\<open>\<^bold>s\<^sub>\<emptyset>\<close>)
  \<open>\<^bold>s\<^sub>\<emptyset> =\<^sub>d\<^sub>f \<^bold>\<iota>x NullSituation(x)\<close>

AOT_define df_the_null_sit_2 :: \<open>\<kappa>\<^sub>s\<close> (\<open>\<^bold>s\<^sub>V\<close>)
  \<open>\<^bold>s\<^sub>V =\<^sub>d\<^sub>f \<^bold>\<iota>x TrivialSituation(x)\<close>

AOT_theorem null_triv_ac_1: \<open>NullSituation(x) \<rightarrow> \<box>NullSituation(x)\<close>
proof(safe intro!: "\<rightarrow>I" dest!: df_null_trivial_1[THEN "\<equiv>\<^sub>d\<^sub>fE"]; frule "&E"(1); drule "&E"(2))
  AOT_assume 1: \<open>\<not>\<exists>p x \<Turnstile> p\<close>
  AOT_assume 0: \<open>Situation(x)\<close>
  AOT_hence \<open>\<box>Situation(x)\<close> by (metis intro_elim_3_a possit_sit_1)
  moreover AOT_have \<open>\<box>\<not>\<exists>p x \<Turnstile> p\<close>
  proof(rule raa_cor_1)
    AOT_assume \<open>\<not>\<box>\<not>\<exists>p x \<Turnstile> p\<close>
    AOT_hence \<open>\<diamond>\<exists>p x \<Turnstile> p\<close>
      by (metis "\<equiv>\<^sub>d\<^sub>fI" AOT_dia)
    AOT_hence \<open>\<exists>p \<diamond>x \<Turnstile> p\<close> by (metis "BF\<diamond>" "\<rightarrow>E")
    then AOT_obtain p where \<open>\<diamond>x \<Turnstile> p\<close> using "\<exists>E"[rotated] by blast
    AOT_hence \<open>x \<Turnstile> p\<close> by (metis 0 intro_elim_3_a lem2_2)
    AOT_hence \<open>\<exists>p x \<Turnstile> p\<close> using "\<exists>I" by fast
    AOT_thus \<open>\<exists>p x \<Turnstile> p & \<not>\<exists>p x \<Turnstile> p\<close> using 1 "&I" by blast
  qed
  ultimately AOT_have 2: \<open>\<box>(Situation(x) & \<not>\<exists>p x \<Turnstile> p)\<close>
    by (metis KBasic_3 con_dis_i_e_1 intro_elim_3_b)
  AOT_show \<open>\<box>NullSituation(x)\<close>
    by (AOT_subst \<open>\<guillemotleft>NullSituation(x)\<guillemotright>\<close> \<open>\<guillemotleft>Situation(x) & \<not>\<exists>p x \<Turnstile> p\<guillemotright>\<close>) (fact 2)
qed


AOT_theorem null_triv_ac_2: \<open>TrivialSituation(x) \<rightarrow> \<box>TrivialSituation(x)\<close>
proof(safe intro!: "\<rightarrow>I" dest!: df_null_trivial_2[THEN "\<equiv>\<^sub>d\<^sub>fE"]; frule "&E"(1); drule "&E"(2))
  AOT_assume 0: \<open>Situation(x)\<close>
  AOT_hence 1: \<open>\<box>Situation(x)\<close> by (metis intro_elim_3_a possit_sit_1)
  AOT_assume \<open>\<forall>p x \<Turnstile> p\<close>
  AOT_hence \<open>x \<Turnstile> p\<close> for p using "\<forall>E" by blast
  AOT_hence \<open>\<box>x \<Turnstile> p\<close> for p using  0 intro_elim_3_a lem2_1 by blast
  AOT_hence \<open>\<forall>p \<box>x \<Turnstile> p\<close> by (rule GEN)
  AOT_hence \<open>\<box>\<forall>p x \<Turnstile> p\<close> by (rule BF[THEN "\<rightarrow>E"])
  AOT_hence 2: \<open>\<box>(Situation(x) & \<forall>p x \<Turnstile> p)\<close>
    using 1 by (metis KBasic_3 con_dis_i_e_1 intro_elim_3_b)
  AOT_show \<open>\<box>TrivialSituation(x)\<close>
    by (AOT_subst \<open>\<guillemotleft>TrivialSituation(x)\<guillemotright>\<close> \<open>\<guillemotleft>Situation(x) & \<forall>p x \<Turnstile> p\<guillemotright>\<close>) (fact 2)
qed

AOT_theorem null_triv_ac_3: \<open>NullSituation(\<^bold>s\<^sub>\<emptyset>)\<close>
  by (safe intro!: df_the_null_sit_1[THEN "=\<^sub>d\<^sub>fI"(2)] thm_null_trivial_3
                   "rule=I_1"[OF thm_null_trivial_3]
                   "!box-desc_2"[THEN "\<rightarrow>E", THEN "\<rightarrow>E", rotated, OF thm_null_trivial_1,
                                 OF "\<forall>I", OF null_triv_ac_1, THEN "\<forall>E"(1), THEN "\<rightarrow>E"])

AOT_theorem null_triv_ac_4: \<open>TrivialSituation(\<^bold>s\<^sub>V)\<close>
  by (safe intro!: df_the_null_sit_2[THEN "=\<^sub>d\<^sub>fI"(2)] thm_null_trivial_4
                   "rule=I_1"[OF thm_null_trivial_4]
                   "!box-desc_2"[THEN "\<rightarrow>E", THEN "\<rightarrow>E", rotated, OF thm_null_trivial_2,
                                 OF "\<forall>I", OF null_triv_ac_2, THEN "\<forall>E"(1), THEN "\<rightarrow>E"])

AOT_theorem null_triv_facts_1: \<open>NullSituation(x) \<equiv> Null(x)\<close>
proof (safe intro!: "\<equiv>I" "\<rightarrow>I" df_null_uni_1[THEN "\<equiv>\<^sub>d\<^sub>fI"] df_null_trivial_1[THEN "\<equiv>\<^sub>d\<^sub>fI"]
            dest!: df_null_uni_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] df_null_trivial_1[THEN "\<equiv>\<^sub>d\<^sub>fE"])
  AOT_assume 0: \<open>Situation(x) & \<not>\<exists>p x \<Turnstile> p\<close>
  AOT_have 1: \<open>x[F] \<rightarrow> \<exists>p F = [\<lambda>y p]\<close> for F
    using 0[THEN "&E"(1), THEN situations[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2), THEN "\<forall>E"(2)]
    by (metis "\<equiv>\<^sub>d\<^sub>fE" deduction_theorem prop_prop1 "\<rightarrow>E")
  AOT_show \<open>A!x & \<not>\<exists>F x[F]\<close>
  proof (safe intro!: "&I" 0[THEN "&E"(1), THEN situations[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(1)]; rule raa_cor_2)
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
    using 0[THEN "&E"(2)] by (metis deduction_theorem existential_2_a raa_cor_3) 
  moreover AOT_have \<open>\<not>\<exists>p x \<Turnstile> p\<close>
  proof (rule raa_cor_2)
    AOT_assume \<open>\<exists>p x \<Turnstile> p\<close>
    then AOT_obtain p where \<open>x \<Turnstile> p\<close> by (metis "instantiation")
    AOT_hence \<open>x[\<lambda>y p]\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" con_dis_i_e_2_b prop_enc true_in_s)
    AOT_hence \<open>\<exists>F x[F]\<close> by (rule "\<exists>I") cqt_2_lambda
    AOT_thus \<open>\<exists>F x[F] & \<not>\<exists>F x[F]\<close> using 0[THEN "&E"(2)] "&I" by blast
  qed
  ultimately AOT_show \<open>Situation(x) & \<not>\<exists>p x \<Turnstile> p\<close> using "&I" by blast
qed

AOT_theorem null_triv_facts_2: \<open>\<^bold>s\<^sub>\<emptyset> = a\<^sub>\<emptyset>\<close>
  apply (rule "=\<^sub>d\<^sub>fI"(2)[OF df_the_null_sit_1])
   apply (fact thm_null_trivial_3)
  apply (rule "=\<^sub>d\<^sub>fI"(2)[OF df_null_uni_terms_1])
   apply (fact null_uni_uniq_3)
  apply (rule equiv_desc_eq_3[THEN "\<rightarrow>E"])
  apply (rule "&I")
   apply (fact thm_null_trivial_3)
  by (rule RN; rule GEN; rule null_triv_facts_1)

AOT_theorem null_triv_facts_3: \<open>\<^bold>s\<^sub>V \<noteq> a\<^sub>V\<close>
proof(rule noneq_infix[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_have \<open>Universal(a\<^sub>V)\<close>
    by (simp add: null_uni_facts_4)
  AOT_hence 0: \<open>a\<^sub>V[A!]\<close>
    using df_null_uni_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" "\<forall>E"(1)
    by (metis cqt_5a vdash_properties_10 vdash_properties_1_b)
  moreover AOT_have 1: \<open>\<not>\<^bold>s\<^sub>V[A!]\<close>
  proof(rule raa_cor_2)
    AOT_have \<open>Situation(\<^bold>s\<^sub>V)\<close>
      using "\<equiv>\<^sub>d\<^sub>fE" con_dis_i_e_2_a df_null_trivial_2 null_triv_ac_4 by blast
    AOT_hence \<open>\<forall>F (\<^bold>s\<^sub>V[F] \<rightarrow> Propositional([F]))\<close>
      by (metis "\<equiv>\<^sub>d\<^sub>fE" con_dis_i_e_2_b situations)
    moreover AOT_assume \<open>\<^bold>s\<^sub>V[A!]\<close>
    ultimately AOT_have \<open>Propositional(A!)\<close> using "\<forall>E"(1)[rotated, OF oa_exist_2] "\<rightarrow>E" by blast
    AOT_thus \<open>Propositional(A!) & \<not>Propositional(A!)\<close> using prop_in_f_4_d "&I" by blast
  qed
  AOT_show \<open>\<not>(\<^bold>s\<^sub>V = a\<^sub>V)\<close>
  proof (rule raa_cor_2)
    AOT_assume \<open>\<^bold>s\<^sub>V = a\<^sub>V\<close>
    AOT_hence \<open>\<^bold>s\<^sub>V[A!]\<close> using 0 "=E" id_sym by fast
    AOT_thus \<open>\<^bold>s\<^sub>V[A!] & \<not>\<^bold>s\<^sub>V[A!]\<close> using 1 "&I" by blast
  qed
qed

(* TODO: continue at (473) cond-prop PDF page 347, numbered page 502 *)

definition cond_prop :: \<open>(<\<kappa>> \<Rightarrow> \<o>) \<Rightarrow> bool\<close> where
  \<open>cond_prop \<equiv> \<lambda> \<phi> . \<forall> v . [v \<Turnstile> \<forall>F (\<phi>{F} \<rightarrow> Propositional([F]))]\<close>

syntax cond_prop :: \<open>id_position \<Rightarrow> AOT_prop\<close> ("CONDITION'_ON'_PROPOSITIONAL'_PROPERTIES'(_')")

AOT_theorem cond_propE:
  assumes \<open>CONDITION_ON_PROPOSITIONAL_PROPERTIES(\<phi>)\<close>
  shows \<open>\<forall>F (\<phi>{F} \<rightarrow> Propositional([F]))\<close>
  using assms[unfolded cond_prop_def] by auto

AOT_theorem cond_propI:
  assumes \<open>\<^bold>\<turnstile>\<^sub>\<box> \<forall>F (\<phi>{F} \<rightarrow> Propositional([F]))\<close>
  shows \<open>CONDITION_ON_PROPOSITIONAL_PROPERTIES(\<phi>)\<close>
  using assms cond_prop_def by metis

AOT_theorem pre_comp_sit:
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
      AOT_thus \<open>Propositional([F])\<close> using cond_propE[OF assms] "\<forall>E" "\<rightarrow>E" by blast
    qed
  next
    AOT_show \<open>\<forall>F (x[F] \<equiv> \<phi>{F})\<close> using 0 "&E" by blast
  qed
qed

AOT_theorem comp_sit_1:
  assumes \<open>CONDITION_ON_PROPOSITIONAL_PROPERTIES(\<phi>)\<close>
  shows \<open>\<exists>s \<forall>F(s[F] \<equiv> \<phi>{F})\<close>
  by (AOT_subst \<open>\<lambda>\<kappa> . \<guillemotleft>Situation(\<kappa>) & \<forall>F(\<kappa>[F] \<equiv> \<phi>{F})\<guillemotright>\<close> \<open>\<lambda>\<kappa>. \<guillemotleft>A!\<kappa> & \<forall>F (\<kappa>[F] \<equiv> \<phi>{F})\<guillemotright>\<close>)
     (auto simp: pre_comp_sit[OF assms] a_objects[where \<phi>=\<phi>, axiom_inst])

AOT_theorem comp_sit_2:
  assumes \<open>CONDITION_ON_PROPOSITIONAL_PROPERTIES(\<phi>)\<close>
  shows \<open>\<exists>!s \<forall>F(s[F] \<equiv> \<phi>{F})\<close>
  by (AOT_subst \<open>\<lambda>\<kappa> . \<guillemotleft>Situation(\<kappa>) & \<forall>F(\<kappa>[F] \<equiv> \<phi>{F})\<guillemotright>\<close> \<open>\<lambda>\<kappa>. \<guillemotleft>A!\<kappa> & \<forall>F (\<kappa>[F] \<equiv> \<phi>{F})\<guillemotright>\<close>)
     (fact pre_comp_sit[OF assms])

AOT_theorem can_sit_desc_1:
  assumes \<open>CONDITION_ON_PROPOSITIONAL_PROPERTIES(\<phi>)\<close>
  shows \<open>\<^bold>\<iota>s(\<forall>F (s[F] \<equiv> \<phi>{F}))\<down>\<close>
  using comp_sit_2[OF assms] A_Exists_2 RA_2 intro_elim_3_b by blast

AOT_theorem can_sit_desc_2:
  assumes \<open>CONDITION_ON_PROPOSITIONAL_PROPERTIES(\<phi>)\<close>
  shows \<open>\<^bold>\<iota>s(\<forall>F (s[F] \<equiv> \<phi>{F})) = \<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<phi>{F}))\<close>
  by (auto intro!: equiv_desc_eq_2[THEN "\<rightarrow>E", OF "&I", OF can_sit_desc_1[OF assms]]
                   RA GEN pre_comp_sit[OF assms]) 

AOT_theorem strict_sit:
  assumes \<open>RIGID_CONDITION(\<phi>)\<close>
      and \<open>CONDITION_ON_PROPOSITIONAL_PROPERTIES(\<phi>)\<close>
    shows \<open>y = \<^bold>\<iota>s(\<forall>F (s[F] \<equiv> \<phi>{F})) \<rightarrow> \<forall>F (y[F] \<equiv> \<phi>{F})\<close>
  using "=E"[rotated, OF can_sit_desc_2[OF assms(2), symmetric]]
        box_phi_a_2[OF assms(1)] "\<rightarrow>E" "\<rightarrow>I" "&E" by fast

(* TODO: exercise (479) sit-lit *)

AOT_define actual :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>Actual'(_')\<close>)
  \<open>Actual(x) \<equiv>\<^sub>d\<^sub>f Situation(x) & \<forall>p (x \<Turnstile> p \<rightarrow> p)\<close>

AOT_theorem act_and_not_pos: \<open>\<exists>s (Actual(s) & \<diamond>\<not>Actual(s))\<close>
proof -
  AOT_obtain q\<^sub>1 where q\<^sub>1_prop: \<open>q\<^sub>1 & \<diamond>\<not>q\<^sub>1\<close>
    by (metis "\<equiv>\<^sub>d\<^sub>fE" "instantiation" cont_tf_1 cont_tf_thm_1)
  AOT_have \<open>\<exists>s (\<forall>F (s[F] \<equiv> F = [\<lambda>y q\<^sub>1]))\<close>
  proof (safe intro!: comp_sit_1 cond_propI GEN "\<rightarrow>I")
    AOT_modally_strict {
      AOT_show \<open>Propositional([F])\<close> if \<open>F = [\<lambda>y q\<^sub>1]\<close> for F
        using "\<equiv>\<^sub>d\<^sub>fI" existential_2_a prop_prop1 that by fastforce
    }
  qed
  then AOT_obtain s\<^sub>1 where s_prop: \<open>Situation(s\<^sub>1) & \<forall>F (s\<^sub>1[F] \<equiv> F = [\<lambda>y q\<^sub>1])\<close>
    using "\<exists>E"[rotated] by blast
  AOT_have \<open>Actual(s\<^sub>1)\<close>
  proof(safe intro!: actual[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" GEN "\<rightarrow>I" s_prop[THEN "&E"(1)])
    fix p
    AOT_assume \<open>s\<^sub>1 \<Turnstile> p\<close>
    AOT_hence \<open>s\<^sub>1[\<lambda>y p]\<close>
      by (metis con_dis_taut_1 intro_elim_3_a lem1 s_prop vdash_properties_10)
    AOT_hence \<open>[\<lambda>y p] = [\<lambda>y q\<^sub>1]\<close>
      by (rule s_prop[THEN "&E"(2), THEN "\<forall>E"(1), THEN "\<equiv>E"(1), rotated]) cqt_2_lambda
    AOT_hence \<open>p = q\<^sub>1\<close> by (metis intro_elim_3_b p_identity_thm2_3)
    AOT_thus \<open>p\<close> using q\<^sub>1_prop[THEN "&E"(1)] "=E" id_sym by fast
  qed
  moreover AOT_have \<open>\<diamond>\<not>Actual(s\<^sub>1)\<close>
  proof(rule raa_cor_1; drule KBasic_12[THEN "\<equiv>E"(2)])
    AOT_assume \<open>\<box>Actual(s\<^sub>1)\<close>
    AOT_hence \<open>\<box>(Situation(s\<^sub>1) & \<forall>p (s\<^sub>1 \<Turnstile> p \<rightarrow> p))\<close>
      using actual[THEN "\<equiv>Df", THEN AOT_equiv[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(1), THEN RM, THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>\<box>\<forall>p (s\<^sub>1 \<Turnstile> p \<rightarrow> p)\<close> by (metis RM_1 con_dis_taut_2 vdash_properties_10)
    AOT_hence \<open>\<forall>p \<box>(s\<^sub>1 \<Turnstile> p \<rightarrow> p)\<close> by (metis BFs_2 vdash_properties_10)
    AOT_hence \<open>\<box>(s\<^sub>1 \<Turnstile> q\<^sub>1 \<rightarrow> q\<^sub>1)\<close> using "\<forall>E" by blast
    AOT_hence \<open>\<box>(s\<^sub>1 \<Turnstile> q\<^sub>1) \<rightarrow> \<box>q\<^sub>1\<close> by (metis "\<rightarrow>E" qml_1 vdash_properties_1_b)
    moreover AOT_have \<open>s\<^sub>1 \<Turnstile> q\<^sub>1\<close>
      using s_prop[THEN "&E"(2), THEN "\<forall>E"(1), THEN "\<equiv>E"(2),
                   THEN lem1[THEN "\<rightarrow>E", OF s_prop[THEN "&E"(1)], THEN "\<equiv>E"(2)]]
            "rule=I_1" prop_prop2_2 by blast
    ultimately AOT_have \<open>\<box>q\<^sub>1\<close>
      using "\<equiv>\<^sub>d\<^sub>fE" con_dis_i_e_2_a intro_elim_3_a lem2_1 true_in_s vdash_properties_10 by fast
    AOT_thus \<open>\<diamond>\<not>q\<^sub>1 & \<not>\<diamond>\<not>q\<^sub>1\<close> using KBasic_12[THEN "\<equiv>E"(1)] q\<^sub>1_prop[THEN "&E"(2)] "&I" by blast
  qed
  ultimately AOT_have \<open>Situation(s\<^sub>1) & (Actual(s\<^sub>1) & \<diamond>\<not>Actual(s\<^sub>1))\<close> using s_prop[THEN "&E"(1)] "&I" by blast
  thus ?thesis by (rule "\<exists>I")
qed

AOT_theorem actual_s_1: \<open>\<exists>s Actual(s)\<close>
proof -
  AOT_obtain s where \<open>Situation(s) & (Actual(s) & \<diamond>\<not>Actual(s))\<close>
    using act_and_not_pos "\<exists>E"[rotated] by blast
  AOT_hence \<open>Situation(s) & Actual(s)\<close> using "&E" "&I" by metis
  thus ?thesis by (rule "\<exists>I")
qed

AOT_theorem actual_s_2: \<open>\<exists>s \<not>Actual(s)\<close>
proof(rule_tac \<tau>="\<guillemotleft>\<^bold>s\<^sub>V\<guillemotright>" in "\<exists>I"(1); (rule "&I")?)
  AOT_show \<open>Situation(\<^bold>s\<^sub>V)\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" con_dis_i_e_2_a df_null_trivial_2 null_triv_ac_4 by blast
next
  AOT_show \<open>\<not>Actual(\<^bold>s\<^sub>V)\<close>
  proof(rule raa_cor_2)
    AOT_assume 0: \<open>Actual(\<^bold>s\<^sub>V)\<close>
    AOT_obtain p\<^sub>1 where notp\<^sub>1: \<open>\<not>p\<^sub>1\<close>
      by (metis "instantiation" existential_1 log_prop_prop_2 non_contradiction)
    AOT_have \<open>\<^bold>s\<^sub>V \<Turnstile> p\<^sub>1\<close>
      using null_triv_ac_4[THEN "\<equiv>\<^sub>d\<^sub>fE"[OF df_null_trivial_2], THEN "&E"(2)] "\<forall>E" by blast
    AOT_hence \<open>p\<^sub>1\<close> using 0[THEN actual[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"]
      by blast
    AOT_thus \<open>p & \<not>p\<close> for p using notp\<^sub>1 by (metis raa_cor_3)
  qed
next
  AOT_show \<open>\<^bold>s\<^sub>V\<down>\<close>
    using df_the_null_sit_2 rule_id_def_2_b' thm_null_trivial_4 by blast
qed

AOT_theorem actual_s_3: \<open>\<exists>p\<forall>s(Actual(s) \<rightarrow> \<not>(s \<Turnstile> p))\<close>
proof -
  AOT_obtain p\<^sub>1 where notp\<^sub>1: \<open>\<not>p\<^sub>1\<close>
    by (metis "instantiation" existential_1 log_prop_prop_2 non_contradiction)
  AOT_have \<open>\<forall>s (Actual(s) \<rightarrow> \<not>(s \<Turnstile> p\<^sub>1))\<close>
  proof (rule GEN; rule "\<rightarrow>I"; rule "\<rightarrow>I"; rule raa_cor_2)
    fix s
    AOT_assume \<open>Actual(s)\<close>
    moreover AOT_assume \<open>s \<Turnstile> p\<^sub>1\<close>
    ultimately AOT_have \<open>p\<^sub>1\<close> using actual[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
    AOT_thus \<open>p\<^sub>1 & \<not>p\<^sub>1\<close> using notp\<^sub>1 "&I" by simp
  qed
  thus ?thesis by (rule "\<exists>I")
qed

(* TODO: PLM: this theorem is probably not the one that was intended
 * It should probably have been \<exists>!s (s' \<unlhd> s & s'' \<unlhd> s & \<forall>s''' (s' \<unlhd> s''' & s'' \<unlhd> s''' \<rightarrow> s \<unlhd> s'''))
 * For the stated theorem the proof below is much simpler than the one given in PLM.
 *)
AOT_theorem comp:
  assumes \<open>Situation(s')\<close> and \<open>Situation(s'')\<close>
  shows \<open>\<exists>s (s' \<unlhd> s & s'' \<unlhd> s)\<close>
proof -
  AOT_have \<open>Situation(\<^bold>s\<^sub>V)\<close>
    by (meson "\<equiv>\<^sub>d\<^sub>fE" con_dis_i_e_2_a df_null_trivial_2 null_triv_ac_4)
  moreover AOT_have 0: \<open>s \<unlhd> \<^bold>s\<^sub>V\<close> if \<open>Situation(s)\<close> for s
  proof(safe intro!: sit_part_whole[THEN "\<equiv>\<^sub>d\<^sub>fI"] calculation that "&I" GEN "\<rightarrow>I")
    AOT_show \<open>\<^bold>s\<^sub>V \<Turnstile> p\<close> for p
      using "\<equiv>\<^sub>d\<^sub>fE" con_dis_i_e_2_b df_null_trivial_2 null_triv_ac_4 rule_ui_2_a by blast
  qed
  moreover AOT_have \<open>\<^bold>s\<^sub>V\<down>\<close>
    using df_the_null_sit_2 rule_id_def_2_b' thm_null_trivial_4 by blast
  ultimately show ?thesis
    using "\<exists>I"(1) assms "&I" by metis
qed

AOT_theorem act_sit_1: \<open>Actual(s) \<rightarrow> (s \<Turnstile> p \<rightarrow> [\<lambda>y p]s)\<close>
proof (safe intro!: "\<rightarrow>I")
  AOT_assume \<open>Actual(s)\<close>
  AOT_hence p if \<open>s \<Turnstile> p\<close> using actual[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"] that by blast
  moreover AOT_assume \<open>s \<Turnstile> p\<close>
  ultimately AOT_have p: p by blast
  AOT_show \<open>[\<lambda>y p]s\<close>
    by (rule betaC_2_a; cqt_2_lambda)
       (auto simp: p ex_1_a rule_ui_2_a)
qed

AOT_theorem act_sit_2: \<open>(Actual(s') & Actual(s'')) \<rightarrow> \<exists>x (Actual(x) & s' \<unlhd> x & s'' \<unlhd> x)\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume act_s': \<open>Actual(s')\<close>
  AOT_assume act_s'': \<open>Actual(s'')\<close>
  have cond_prop: \<open>cond_prop (\<lambda> \<Pi> . \<guillemotleft>\<exists>p (\<Pi> = [\<lambda>y p] & (s' \<Turnstile> p \<or> s'' \<Turnstile> p))\<guillemotright>)\<close>
  proof (safe intro!: cond_propI  "\<forall>I" "\<rightarrow>I" prop_prop1[THEN "\<equiv>\<^sub>d\<^sub>fI"])
    AOT_modally_strict {
      fix \<beta>
      AOT_assume \<open>\<exists>p (\<beta> = [\<lambda>y p] & (s' \<Turnstile> p \<or> s'' \<Turnstile> p))\<close>
      then AOT_obtain p where \<open>\<beta> = [\<lambda>y p]\<close> using "\<exists>E"[rotated] "&E" by blast
      AOT_thus \<open>\<exists>p \<beta> = [\<lambda>y p]\<close> by (rule "\<exists>I")
    }
  qed
  have rigid: \<open>rigid_condition (\<lambda> \<Pi> . \<guillemotleft>\<exists>p (\<Pi> = [\<lambda>y p] & (s' \<Turnstile> p \<or> s'' \<Turnstile> p))\<guillemotright>)\<close>
  proof(safe intro!: rigid_conditionI "\<rightarrow>I" GEN)
    AOT_modally_strict {
      fix F
      AOT_assume \<open>\<exists>p (F = [\<lambda>y p] & (s' \<Turnstile> p \<or> s'' \<Turnstile> p))\<close>
      then AOT_obtain p\<^sub>1 where p\<^sub>1_prop: \<open>F = [\<lambda>y p\<^sub>1] & (s' \<Turnstile> p\<^sub>1 \<or> s'' \<Turnstile> p\<^sub>1)\<close>
        using "\<exists>E"[rotated] by blast
      AOT_hence \<open>\<box>(F = [\<lambda>y p\<^sub>1])\<close>
        using con_dis_i_e_2_a id_nec_2 vdash_properties_10 by blast
      moreover AOT_have \<open>\<box>(s' \<Turnstile> p\<^sub>1 \<or> s'' \<Turnstile> p\<^sub>1)\<close>
      proof(rule "\<or>E"; (rule "\<rightarrow>I"; rule KBasic_15[THEN "\<rightarrow>E"])?)
        AOT_show \<open>s' \<Turnstile> p\<^sub>1 \<or> s'' \<Turnstile> p\<^sub>1\<close> using p\<^sub>1_prop "&E" by blast
      next
        AOT_show \<open>\<box>s' \<Turnstile> p\<^sub>1 \<or> \<box>s'' \<Turnstile> p\<^sub>1\<close> if \<open>s' \<Turnstile> p\<^sub>1\<close>
          apply (rule "\<or>I"(1))
          using "\<equiv>\<^sub>d\<^sub>fE" con_dis_i_e_2_a intro_elim_3_a lem2_1 that true_in_s by blast
      next
        AOT_show \<open>\<box>s' \<Turnstile> p\<^sub>1 \<or> \<box>s'' \<Turnstile> p\<^sub>1\<close> if \<open>s'' \<Turnstile> p\<^sub>1\<close>
          apply (rule "\<or>I"(2))
          using "\<equiv>\<^sub>d\<^sub>fE" con_dis_i_e_2_a intro_elim_3_a lem2_1 that true_in_s by blast
      qed
      ultimately AOT_have \<open>\<box>(F = [\<lambda>y p\<^sub>1] & (s' \<Turnstile> p\<^sub>1 \<or> s'' \<Turnstile> p\<^sub>1))\<close>
        by (metis KBasic_3 con_dis_i_e_1 intro_elim_3_b)
      AOT_hence \<open>\<exists>p \<box>(F = [\<lambda>y p] & (s' \<Turnstile> p \<or> s'' \<Turnstile> p))\<close> by (rule "\<exists>I")
      AOT_thus \<open>\<box>\<exists>p (F = [\<lambda>y p] & (s' \<Turnstile> p \<or> s'' \<Turnstile> p))\<close>
        using sign_S5_thm_1[THEN "\<rightarrow>E"] by fast
    }
  qed

  AOT_have \<open>\<^bold>\<iota>s(\<forall>F (s[F] \<equiv> \<exists>p (F = [\<lambda>y p] & (s' \<Turnstile> p \<or> s'' \<Turnstile> p))))\<down>\<close>
    by (rule can_sit_desc_1[OF cond_prop])
  then AOT_obtain s\<^sub>0 where s\<^sub>0_prop1: \<open>s\<^sub>0 = \<^bold>\<iota>s(\<forall>F (s[F] \<equiv> \<exists>p (F = [\<lambda>y p] & (s' \<Turnstile> p \<or> s'' \<Turnstile> p))))\<close>
    by (metis (no_types, lifting) "instantiation" "rule=I_1" existential_1 id_sym)
  AOT_hence s\<^sub>0_sit: \<open>Situation(s\<^sub>0)\<close>
    using actual_desc_3[THEN "\<rightarrow>E"] Act_Basic_2 con_dis_i_e_2_a intro_elim_3_a possit_sit_4 by blast

  AOT_have 1: \<open>\<forall>F (s\<^sub>0[F] \<equiv> \<exists>p (F = [\<lambda>y p] & (s' \<Turnstile> p \<or> s'' \<Turnstile> p)))\<close>
    using strict_sit[OF rigid, OF cond_prop, THEN "\<rightarrow>E", OF s\<^sub>0_prop1].
  AOT_have 2: \<open>(s\<^sub>0 \<Turnstile> p) \<equiv> (s' \<Turnstile> p \<or> s'' \<Turnstile> p)\<close> for p
  proof (rule "\<equiv>I"; rule "\<rightarrow>I")
    AOT_assume \<open>s\<^sub>0 \<Turnstile> p\<close>
    AOT_hence \<open>s\<^sub>0[\<lambda>y p]\<close> using lem1[THEN "\<rightarrow>E", OF s\<^sub>0_sit, THEN "\<equiv>E"(1)] by blast
    then AOT_obtain q where \<open>[\<lambda>y p] = [\<lambda>y q] & (s' \<Turnstile> q \<or> s'' \<Turnstile> q)\<close>
      using 1[THEN "\<forall>E"(1)[where \<tau>="\<guillemotleft>[\<lambda>y p]\<guillemotright>"], OF prop_prop2_2, THEN "\<equiv>E"(1)]
            "\<exists>E"[rotated] by blast
    AOT_thus \<open>s' \<Turnstile> p \<or> s'' \<Turnstile> p\<close>
      by (metis "rule=E" con_dis_i_e_2_a con_dis_i_e_2_b con_dis_i_e_3_a con_dis_i_e_3_b
                con_dis_i_e_4_a deduction_theorem id_sym intro_elim_3_b p_identity_thm2_3)
  next
    AOT_assume \<open>s' \<Turnstile> p \<or> s'' \<Turnstile> p\<close>
    AOT_hence \<open>[\<lambda>y p] = [\<lambda>y p] & (s' \<Turnstile> p \<or> s'' \<Turnstile> p)\<close>
      by (metis "rule=I_1" con_dis_i_e_1 prop_prop2_2) 
    AOT_hence \<open>\<exists>q ([\<lambda>y p] = [\<lambda>y q] & (s' \<Turnstile> q \<or> s'' \<Turnstile> q))\<close>
      by (rule "\<exists>I")
    AOT_hence \<open>s\<^sub>0[\<lambda>y p]\<close>
      using 1[THEN "\<forall>E"(1), OF prop_prop2_2, THEN "\<equiv>E"(2)] by blast
    AOT_thus \<open>s\<^sub>0 \<Turnstile> p\<close> by (metis "\<equiv>\<^sub>d\<^sub>fI" con_dis_i_e_1 ex_1_a prop_enc rule_ui_2_a s\<^sub>0_sit true_in_s)
  qed

  AOT_have \<open>Actual(s\<^sub>0) & s' \<unlhd> s\<^sub>0 & s'' \<unlhd> s\<^sub>0\<close>
  proof(safe intro!: "\<rightarrow>I" "&I" "\<exists>I"(1) actual[THEN "\<equiv>\<^sub>d\<^sub>fI"] s\<^sub>0_sit GEN sit_part_whole[THEN "\<equiv>\<^sub>d\<^sub>fI"])
    fix p
    AOT_assume \<open>s\<^sub>0 \<Turnstile> p\<close>
    AOT_hence \<open>s' \<Turnstile> p \<or> s'' \<Turnstile> p\<close>
      using 2 "\<equiv>E"(1) by metis
    AOT_thus \<open>p\<close> using act_s' act_s'' actual[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"]
      by (metis con_dis_i_e_4_c reductio_aa_1)
  next
    AOT_show \<open>s\<^sub>0 \<Turnstile> p\<close> if \<open>s' \<Turnstile> p\<close> for p using 2[THEN "\<equiv>E"(2), OF "\<or>I"(1), OF that].
  next
    AOT_show \<open>s\<^sub>0 \<Turnstile> p\<close> if \<open>s'' \<Turnstile> p\<close> for p using 2[THEN "\<equiv>E"(2), OF "\<or>I"(2), OF that].
  next
    AOT_show \<open>Situation(s')\<close> using act_s'[THEN actual[THEN "\<equiv>\<^sub>d\<^sub>fE"]] "&E" by blast
  next
    AOT_show \<open>Situation(s'')\<close> using act_s''[THEN actual[THEN "\<equiv>\<^sub>d\<^sub>fE"]] "&E" by blast
  qed
  AOT_thus \<open>\<exists>x (Actual(x) & s' \<unlhd> x & s'' \<unlhd> x)\<close>
    by (rule "\<exists>I")
qed

AOT_define consistent :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>Consistent'(_')\<close>)
  cons: \<open>Consistent(x) \<equiv>\<^sub>d\<^sub>f Situation(x) & \<not>\<exists>p (x \<Turnstile> p & x \<Turnstile> \<not>p)\<close>

AOT_theorem sit_cons: \<open>Actual(s) \<rightarrow> Consistent(s)\<close>
proof(safe intro!: "\<rightarrow>I" cons[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" dest!: actual[THEN "\<equiv>\<^sub>d\<^sub>fE"]; frule "&E"(1); drule "&E"(2))
  AOT_show \<open>Situation(s)\<close> if \<open>Situation(s)\<close> by (fact that)
next
  AOT_assume 0: \<open>\<forall>p (s \<Turnstile> p \<rightarrow> p)\<close>
  AOT_show \<open>\<not>\<exists>p (s \<Turnstile> p & s \<Turnstile> \<not>p)\<close>
  proof (rule raa_cor_2)
    AOT_assume \<open>\<exists>p (s \<Turnstile> p & s \<Turnstile> \<not>p)\<close>
    then AOT_obtain p where \<open>s \<Turnstile> p & s \<Turnstile> \<not>p\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>p & \<not>p\<close>
      using 0[THEN "\<forall>E"(1)[where \<tau>=\<open>\<guillemotleft>\<not>p\<guillemotright>\<close>, THEN "\<rightarrow>E"], OF log_prop_prop_2]
            0[THEN "\<forall>E"(2)[where \<beta>=p], THEN "\<rightarrow>E"] "&E" "&I" by blast
    AOT_thus \<open>p & \<not>p\<close> for p by (metis raa_cor_1) 
  qed
qed

(* TODO: PLM: recheck use of substitution with restricted variables *)
AOT_theorem cons_rigid_1:
  assumes \<open>Situation(s)\<close>
  shows \<open>\<not>Consistent(s) \<equiv> \<box>\<not>Consistent(s)\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<not>Consistent(s)\<close>
  AOT_hence \<open>\<exists>p (s \<Turnstile> p & s \<Turnstile> \<not>p)\<close>
    using cons[THEN "\<equiv>\<^sub>d\<^sub>fI", OF "&I", OF assms] by (metis raa_cor_3)
  then AOT_obtain p where p_prop: \<open>s \<Turnstile> p & s \<Turnstile> \<not>p\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<open>\<box>s \<Turnstile> p\<close>
    using T_S5_fund_1 assms "&E" intro_elim_3_a lem2_3 
      modus_tollens_1 raa_cor_3 by blast
  moreover AOT_have \<open>\<box>s \<Turnstile> \<not>p\<close>
    using p_prop T_S5_fund_1 assms "&E" intro_elim_3_a
      modus_tollens_1 raa_cor_3 lem2_3[unvarify p]
      log_prop_prop_2 by metis
  ultimately AOT_have \<open>\<box>(s \<Turnstile> p & s \<Turnstile> \<not>p)\<close>
    by (metis KBasic_3 con_dis_i_e_1 intro_elim_3_b)
  AOT_hence \<open>\<exists>p \<box>(s \<Turnstile> p & s \<Turnstile> \<not>p)\<close>
    by (rule "\<exists>I")
  AOT_hence \<open>\<box>\<exists>p(s \<Turnstile> p & s \<Turnstile> \<not>p)\<close>
    by (metis sign_S5_thm_1 vdash_properties_10) 
  AOT_hence \<open>\<box>(Situation(s) & \<exists>p(s \<Turnstile> p & s \<Turnstile> \<not>p))\<close>
    using assms by (metis KBasic_3 df_simplify_1 intro_elim_3_a intro_elim_3_b possit_sit_1) 
  AOT_thus \<open>\<box>\<not>Consistent(s)\<close>
    apply (rule qml_1[axiom_inst, THEN "\<rightarrow>E", THEN "\<rightarrow>E", rotated])
    apply (rule RN)
    apply (rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2); rule raa_cor_2)
    using "\<equiv>\<^sub>d\<^sub>fE" con_dis_i_e_2_b cons raa_cor_3 by blast
next
  AOT_assume \<open>\<box>\<not>Consistent(s)\<close>
  AOT_thus \<open>\<not>Consistent(s)\<close> using qml_2[axiom_inst, THEN "\<rightarrow>E"] by auto
qed

AOT_theorem cons_rigid_2: \<open>\<diamond>Consistent(x) \<equiv> Consistent(x)\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<diamond>Consistent(x)\<close>
  AOT_have \<open>\<diamond>(Situation(x) & \<not>\<exists>p (x \<Turnstile> p & x \<Turnstile> \<not>p))\<close>
    by (AOT_subst \<open>\<guillemotleft>Situation(x) & \<not>\<exists>p (x \<Turnstile> p & x \<Turnstile> \<not>p)\<guillemotright>\<close> \<open>\<guillemotleft>Consistent(x)\<guillemotright>\<close>) (fact 0)
  AOT_hence \<open>\<diamond>Situation(x)\<close> and 1: \<open>\<diamond>\<not>\<exists>p (x \<Turnstile> p & x \<Turnstile> \<not>p)\<close>
    using "RM\<diamond>" con_dis_taut_1 con_dis_taut_2 modus_tollens_1 raa_cor_3 by blast+
  AOT_hence 2: \<open>Situation(x)\<close> by (metis intro_elim_3_a possit_sit_2)
  AOT_have 3: \<open>\<not>\<box>\<exists>p (x \<Turnstile> p & x \<Turnstile> \<not>p)\<close>
    using 2 using 1 KBasic_11 intro_elim_3_b by blast
  AOT_show \<open>Consistent(x)\<close>
  proof (rule raa_cor_1)
    AOT_assume \<open>\<not>Consistent(x)\<close>
    AOT_hence \<open>\<exists>p (x \<Turnstile> p & x \<Turnstile> \<not>p)\<close>
      using 0 "\<equiv>\<^sub>d\<^sub>fE" AOT_dia 2 cons_rigid_1 modus_tollens_1 raa_cor_3 intro_elim_3_d by meson
    then AOT_obtain p where \<open>x \<Turnstile> p\<close> and 4: \<open>x \<Turnstile> \<not>p\<close> using "\<exists>E"[rotated] "&E" by blast
    AOT_hence \<open>\<box>x \<Turnstile> p\<close> by (metis "2" intro_elim_3_a lem2_1)
    moreover AOT_have \<open>\<box>x \<Turnstile> \<not>p\<close> using 4 lem2_1[unvarify p]  by (metis 2 intro_elim_3_a log_prop_prop_2)
    ultimately AOT_have \<open>\<box>(x \<Turnstile> p & x \<Turnstile> \<not>p)\<close> by (metis KBasic_3 con_dis_i_e_1 intro_elim_3_c raa_cor_3)
    AOT_hence \<open>\<exists>p \<box>(x \<Turnstile> p & x \<Turnstile> \<not>p)\<close> by (metis existential_1 log_prop_prop_2)
    AOT_hence \<open>\<box>\<exists>p (x \<Turnstile> p & x \<Turnstile> \<not>p)\<close> by (metis sign_S5_thm_1 vdash_properties_10)
    AOT_thus \<open>p & \<not>p\<close> for p using 3 "&I"  by (metis raa_cor_3)
  qed
next
  AOT_show \<open>\<diamond>Consistent(x)\<close> if \<open>Consistent(x)\<close>
    using T_S5_fund_1 that vdash_properties_10 by blast
qed

AOT_define possible :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>Possible'(_')\<close>)
  pos: \<open>Possible(x) \<equiv>\<^sub>d\<^sub>f Situation(x) & \<diamond>Actual(x)\<close>

AOT_theorem sit_pos_1: \<open>Actual(s) \<rightarrow> Possible(s)\<close>
  apply(rule "\<rightarrow>I"; rule pos[THEN "\<equiv>\<^sub>d\<^sub>fI"]; rule "&I")
  apply (meson "\<equiv>\<^sub>d\<^sub>fE" actual con_dis_i_e_2_a)
  using T_S5_fund_1 vdash_properties_10 by blast

AOT_theorem sit_pos_2:
  assumes \<open>Situation(s)\<close>
  shows \<open>\<exists>p ((s \<Turnstile> p) & \<not>\<diamond>p) \<rightarrow> \<not>Possible(s)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<exists>p ((s \<Turnstile> p) & \<not>\<diamond>p)\<close>
  then AOT_obtain p where a: \<open>(s \<Turnstile> p) & \<not>\<diamond>p\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<open>\<box>(s \<Turnstile> p)\<close> using "&E" by (metis T_S5_fund_1 assms intro_elim_3_a lem2_3 vdash_properties_10)
  moreover AOT_have \<open>\<box>\<not>p\<close> using a[THEN "&E"(2)] by (metis KBasic2_1 intro_elim_3_b)
  ultimately AOT_have \<open>\<box>(s \<Turnstile> p & \<not>p)\<close> by (metis KBasic_3 con_dis_i_e_1 intro_elim_3_c raa_cor_3)
  AOT_hence \<open>\<exists>p \<box>(s \<Turnstile> p & \<not>p)\<close> by (rule "\<exists>I")
  AOT_hence 1: \<open>\<box>\<exists>q (s \<Turnstile> q & \<not>q)\<close> by (metis sign_S5_thm_1 vdash_properties_10)
  AOT_have \<open>\<box>\<not>\<forall>q (s \<Turnstile> q \<rightarrow> q)\<close>
    apply (AOT_subst \<open>\<lambda>\<phi> . \<guillemotleft>(s \<Turnstile> \<phi>) \<rightarrow> \<phi>\<guillemotright>\<close> \<open>\<lambda> \<phi> . \<guillemotleft>\<not>((s \<Turnstile> \<phi>) & \<not>\<phi>)\<guillemotright>\<close>)
    apply (AOT_subst \<open>\<guillemotleft>\<not>\<forall>q \<not>(s \<Turnstile> q & \<not>q)\<guillemotright>\<close> \<open>\<guillemotleft>\<exists>q (s \<Turnstile> q & \<not>q)\<guillemotright>\<close>)
    by (fact 1)
  AOT_hence 0: \<open>\<not>\<diamond>\<forall>q (s \<Turnstile> q \<rightarrow> q)\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" AOT_dia raa_cor_3)
  AOT_show \<open>\<not>Possible(s)\<close>
    apply (AOT_subst \<open>\<guillemotleft>Possible(s)\<guillemotright>\<close> \<open>\<guillemotleft>Situation(s) & \<diamond>Actual(s)\<guillemotright>\<close>)
    apply (AOT_subst \<open>\<guillemotleft>Actual(s)\<guillemotright>\<close> \<open>\<guillemotleft>Situation(s) & \<forall>q (s \<Turnstile> q \<rightarrow> q)\<guillemotright>\<close>)
    by (metis "0" KBasic2_3 con_dis_i_e_2_b raa_cor_3 vdash_properties_10)
qed

AOT_theorem pos_cons_sit_1: \<open>Possible(s) \<rightarrow> Consistent(s)\<close>
  by (auto simp: sit_cons[THEN "RM\<diamond>", THEN "\<rightarrow>E", THEN cons_rigid_2[THEN "\<equiv>E"(1)]]
           intro!: "\<rightarrow>I" dest!: pos[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E"(2))

term "\<guillemotleft>q\<^sub>0\<guillemotright>"
thm q\<^sub>0_prop

AOT_theorem pos_cons_sit_2: \<open>\<exists>s (Consistent(s) & \<not>Possible(s))\<close>
proof -
  AOT_obtain q\<^sub>1 where \<open>q\<^sub>1 & \<diamond>\<not>q\<^sub>1\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" "instantiation" cont_tf_1 cont_tf_thm_1 by blast
  have cond_prop: \<open>cond_prop (\<lambda> \<Pi> . \<guillemotleft>\<Pi> = [\<lambda>y q\<^sub>1 & \<not>q\<^sub>1]\<guillemotright>)\<close>
    by (auto intro!: cond_propI GEN "\<rightarrow>I" prop_prop1[THEN "\<equiv>\<^sub>d\<^sub>fI"]
                     "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>q\<^sub>1 & \<not>q\<^sub>1\<guillemotright>\<close>, rotated, OF log_prop_prop_2])
  have rigid: \<open>rigid_condition (\<lambda> \<Pi> . \<guillemotleft>\<Pi> = [\<lambda>y q\<^sub>1 & \<not>q\<^sub>1]\<guillemotright>)\<close>
    by (auto intro!: rigid_conditionI GEN "\<rightarrow>I" simp: id_nec_2[THEN "\<rightarrow>E"])

  AOT_obtain s where s_prop: \<open>s = \<^bold>\<iota>s (\<forall>F (s[F] \<equiv> F = [\<lambda>y q\<^sub>1 & \<not>q\<^sub>1]))\<close>
    using ex_1_b[THEN "\<forall>E"(1), OF can_sit_desc_1, OF cond_prop]
          "\<exists>E"[rotated] by blast    
  AOT_hence 0: \<open>\<^bold>\<A>(Situation(s) & \<forall>F (s[F] \<equiv> F = [\<lambda>y q\<^sub>1 & \<not>q\<^sub>1]))\<close>
    using "\<rightarrow>E" actual_desc_2 by blast
  AOT_hence \<open>\<^bold>\<A>(Situation(s))\<close> by (metis Act_Basic_2 con_dis_i_e_2_a intro_elim_3_a)
  AOT_hence s_sit: \<open>Situation(s)\<close> by (metis intro_elim_3_a possit_sit_4)
  AOT_have s_enc_prop: \<open>\<forall>F (s[F] \<equiv> F = [\<lambda>y q\<^sub>1 & \<not>q\<^sub>1])\<close>
    using strict_sit[OF rigid, OF cond_prop, THEN "\<rightarrow>E", OF s_prop].
  AOT_hence \<open>s[\<lambda>y q\<^sub>1 & \<not>q\<^sub>1]\<close>
    using "\<forall>E"(1)[rotated, OF prop_prop2_2] "rule=I_1"[OF prop_prop2_2] "\<equiv>E" by blast
  AOT_hence \<open>s \<Turnstile> (q\<^sub>1 & \<not>q\<^sub>1)\<close> (* TODO: fix precedence *)
    using lem1[THEN "\<rightarrow>E", OF s_sit, unvarify p, THEN "\<equiv>E"(2), OF log_prop_prop_2]
    by blast
  AOT_hence \<open>\<box>(s \<Turnstile> (q\<^sub>1 & \<not>q\<^sub>1))\<close>
    using lem2_1[OF s_sit, unvarify p, OF log_prop_prop_2, THEN "\<equiv>E"(1)] by blast
  moreover AOT_have \<open>\<box>((s \<Turnstile> (q\<^sub>1 & \<not>q\<^sub>1)) \<rightarrow> \<not>Actual(s))\<close>
  proof(rule RN; rule "\<rightarrow>I"; rule raa_cor_2)
    AOT_modally_strict {
      AOT_assume \<open>Actual(s)\<close>
      AOT_hence \<open>\<forall>p (s \<Turnstile> p \<rightarrow> p)\<close>
        using actual[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2)] by blast
      moreover AOT_assume \<open>s \<Turnstile> (q\<^sub>1 & \<not>q\<^sub>1)\<close>
      ultimately AOT_show \<open>q\<^sub>1 & \<not>q\<^sub>1\<close> using "\<forall>E"(1)[rotated, OF log_prop_prop_2] "\<rightarrow>E" by metis
    }
  qed
  ultimately AOT_have nec_not_actual_s: \<open>\<box>\<not>Actual(s)\<close>
    using qml_1[axiom_inst, THEN "\<rightarrow>E", THEN "\<rightarrow>E"] by blast
  AOT_have 1: \<open>\<not>\<exists>p (s \<Turnstile> p & s \<Turnstile> \<not>p)\<close>
  proof (rule raa_cor_2)
    AOT_assume \<open>\<exists>p (s \<Turnstile> p & s \<Turnstile> \<not>p)\<close>
    then AOT_obtain p where \<open>s \<Turnstile> p & s \<Turnstile> \<not>p\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>s[\<lambda>y p] & s[\<lambda>y \<not>p]\<close>
      using lem1[unvarify p, THEN "\<rightarrow>E", OF log_prop_prop_2, OF s_sit, THEN "\<equiv>E"(1)] "&I" "&E" by metis
    AOT_hence \<open>[\<lambda>y p] = [\<lambda>y q\<^sub>1 & \<not>q\<^sub>1]\<close> and \<open>[\<lambda>y \<not>p] = [\<lambda>y q\<^sub>1 & \<not>q\<^sub>1]\<close>
      by (auto intro!: prop_prop2_2 s_enc_prop[THEN "\<forall>E"(1), THEN "\<equiv>E"(1)] elim: "&E")
    AOT_hence i: \<open>[\<lambda>y p] = [\<lambda>y \<not>p]\<close> by (metis "rule=E" id_sym)
    {
      AOT_assume 0: \<open>p\<close>
      AOT_have \<open>[\<lambda>y p]x\<close> for x
        by (rule betaC_2_a; cqt_2_lambda; auto intro!: 0 cqt_2_const_var[axiom_inst])
      AOT_hence \<open>[\<lambda>y \<not>p]x\<close> for x using i "rule=E" by fast
      AOT_hence \<open>\<not>p\<close>
        using betaC_1_a by auto
    }
    moreover {
      AOT_assume 0: \<open>\<not>p\<close>
      AOT_have \<open>[\<lambda>y \<not>p]x\<close> for x
        by (rule betaC_2_a; cqt_2_lambda; auto intro!: 0 cqt_2_const_var[axiom_inst])
      AOT_hence \<open>[\<lambda>y p]x\<close> for x using i[symmetric] "rule=E" by fast
      AOT_hence \<open>p\<close>
        using betaC_1_a by auto
    }
    ultimately AOT_show \<open>p & \<not>p\<close> for p by (metis raa_cor_1 raa_cor_3)
  qed
  AOT_have 2: \<open>\<not>Possible(s)\<close>
  proof(rule raa_cor_2)
    AOT_assume \<open>Possible(s)\<close>
    AOT_hence \<open>\<diamond>Actual(s)\<close>
      by (metis "\<equiv>\<^sub>d\<^sub>fE" con_dis_i_e_2_b pos)
    moreover AOT_have \<open>\<not>\<diamond>Actual(s)\<close> using nec_not_actual_s
      using "\<equiv>\<^sub>d\<^sub>fE" AOT_dia reductio_aa_2 by blast
    ultimately AOT_show \<open>\<diamond>Actual(s) & \<not>\<diamond>Actual(s)\<close> by (rule "&I")
  qed
  show ?thesis
    by(rule_tac \<beta>=s in "\<exists>I"(2); safe intro!: "&I" 2 s_sit cons[THEN "\<equiv>\<^sub>d\<^sub>fI"] 1)
qed

end
