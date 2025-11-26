theory AOT_TruthmakerSemantics
  imports AOT_PossibleWorlds AOT_Possibilities
begin

AOT_register_variable_names
  Situation: t

AOT_define UpperBound :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>UpperBound'(_,_')\<close>)
  \<open>UpperBound(s, \<guillemotleft>\<psi>\<guillemotright>) \<equiv>\<^sub>d\<^sub>f \<forall>t(\<psi>{t} \<rightarrow> t \<unlhd> s)\<close>

syntax "_UpperBound" :: \<open>\<tau> \<Rightarrow> id_position \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close>  (\<open>UpperBound'(_,_._')\<close>)
translations
  "_UpperBound \<tau> x \<psi>" == "CONST UpperBound \<tau> (_abs x \<psi>)"

AOT_define LeastUpperBound :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>LeastUpperBound'(_,_')\<close>)
  \<open>LeastUpperBound(s, \<guillemotleft>\<psi>\<guillemotright>) \<equiv>\<^sub>d\<^sub>f UpperBound(s, s. \<psi>{s}) & \<forall>t(UpperBound(t,s. \<psi>{s}) \<rightarrow> s \<unlhd> t)\<close>

syntax "_LeastUpperBound" :: \<open>\<tau> \<Rightarrow> id_position \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close>  (\<open>LeastUpperBound'(_,_. _')\<close>)
translations
  "_LeastUpperBound \<tau> x \<psi>" == "CONST LeastUpperBound \<tau> (_abs x \<psi>)"

AOT_theorem LeastUpperBound_exists: \<open>\<exists>s LeastUpperBound(s,s. \<psi>{s})\<close>
proof -
  AOT_have \<open>\<exists>s \<forall>p(s \<Turnstile> p \<equiv> \<exists>t(\<psi>{t} & t \<Turnstile> p))\<close>
    by (simp add: "sit-comp-simp:1")
  then AOT_obtain s\<^sub>0 where s\<^sub>0_prop: \<open>\<forall>p(s\<^sub>0 \<Turnstile> p \<equiv> \<exists>t(\<psi>{t} & t \<Turnstile> p))\<close>
    using "Situation.\<exists>E"[rotated] by meson
  AOT_have \<open>UpperBound(s\<^sub>0, s. \<psi>{s})\<close>
  proof(safe intro!: "UpperBound.\<equiv>\<^sub>d\<^sub>fI" "&I" Situation.\<psi> GEN Situation.GEN
                     "\<rightarrow>I" "sit-part-whole.\<equiv>\<^sub>d\<^sub>fI")
    fix t p
    AOT_assume \<open>\<psi>{t}\<close>
    moreover AOT_assume \<open>t \<Turnstile> p\<close>
    ultimately AOT_have \<open>\<exists>t(\<psi>{t} & t \<Turnstile> p)\<close>
      by (meson "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "cqt:2"(1) "existential:1" "true-in-s.\<equiv>\<^sub>d\<^sub>fE.&E(1)")
    AOT_thus \<open>s\<^sub>0 \<Turnstile> p\<close>
      using s\<^sub>0_prop "intro-elim:3:b" "rule-ui:3" by blast
  qed
  moreover AOT_have \<open>\<forall>t(UpperBound(t,s. \<psi>{s}) \<rightarrow> s\<^sub>0 \<unlhd> t)\<close>
  proof(safe intro!: GEN Situation.GEN "\<rightarrow>I" "sit-part-whole.\<equiv>\<^sub>d\<^sub>fI" "&I" Situation.\<psi>)
    fix t p
    AOT_assume \<open>UpperBound(t,s. \<psi>{s})\<close>
    AOT_hence 0: \<open>\<forall>t'(\<psi>{t'} \<rightarrow> t' \<unlhd> t)\<close>
      by (simp add: "UpperBound.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E.\<rightarrow>E" "cqt:2"(1)
                    "deduction-theorem" "universal-cor")
    AOT_assume \<open>s\<^sub>0 \<Turnstile> p\<close>
    AOT_hence \<open>\<exists>t(\<psi>{t} & t \<Turnstile> p)\<close>
      using "intro-elim:3:a" "rule-ui:3" s\<^sub>0_prop by blast
    then AOT_obtain t\<^sub>1 where 4: \<open>\<psi>{t\<^sub>1} & t\<^sub>1 \<Turnstile> p\<close>
      using "Situation.\<exists>E"[rotated] by meson
    moreover AOT_have \<open>t\<^sub>1 \<unlhd> t\<close>
      using calculation 0[THEN "\<forall>E"(1), THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "con-dis-i-e:2:a"
            "con-dis-i-e:2:b" "cqt:2"(1) "true-in-s.\<equiv>\<^sub>d\<^sub>fE.&E(1)" by blast
    ultimately AOT_show \<open>t \<Turnstile> p\<close>
      using "con-dis-i-e:2:b" "cqt:2"(1) "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E" by blast
  qed
  ultimately show ?thesis
    by (metis (no_types, lifting) "LeastUpperBound.\<equiv>\<^sub>d\<^sub>fI" "Situation.res-var:3"
        "UpperBound.\<equiv>\<^sub>d\<^sub>fE.&E(1)" "con-dis-taut:5" "existential:1" "rule-ui:3"
        "universal-cor" "vdash-properties:10")
qed

AOT_theorem UniqueLeastUpperBound_exists: \<open>\<exists>!s LeastUpperBound(s,s. \<psi>{s})\<close>
proof -
  AOT_obtain s\<^sub>0 where \<open>LeastUpperBound(s\<^sub>0,s. \<psi>{s})\<close>
    by (metis LeastUpperBound_exists Situation.instantiation)
  moreover AOT_have \<open>\<forall>t(LeastUpperBound(t,s. \<psi>{s}) \<rightarrow> t = s\<^sub>0)\<close>
  proof(safe intro!: "Situation.GEN" "\<rightarrow>I")
    fix t
    AOT_assume 1: \<open>LeastUpperBound(t,\<guillemotleft>\<psi>\<guillemotright>)\<close>
    AOT_hence \<open>UpperBound(t, s. \<psi>{s}) & \<forall>t'(UpperBound(t',s. \<psi>{s}) \<rightarrow> t \<unlhd> t')\<close>
      using "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:b" LeastUpperBound by blast
    AOT_show \<open>t = s\<^sub>0\<close>
      by (meson "1" "LeastUpperBound.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(1)" "situations:3.\<rightarrow>E" calculation
          "LeastUpperBound.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(2).\<forall>E(1).\<rightarrow>E.\<rightarrow>E"
          "UpperBound.\<equiv>\<^sub>d\<^sub>fE.&E(1)" "df-simplify:2.\<equiv>E(2)" "sit-identity2:1")
  qed
  ultimately show ?thesis
    using "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"]
    by (smt (verit, del_insts) "LeastUpperBound.\<equiv>\<^sub>d\<^sub>fE.&E(1)" "con-dis-i-e:2:b"
        "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "deduction-theorem" "existential:2[const_var]" "rule-ui:3"
        "universal-cor" "vdash-properties:10")
qed

AOT_theorem TheLeastUpperBound_denotes: \<open>\<^bold>\<iota>s LeastUpperBound(s,s. \<psi>{s})\<down>\<close>
  by (simp add: "A-Exists:2.\<equiv>E(2)" "RA[2]" UniqueLeastUpperBound_exists)

AOT_define TheLeastUpperBound :: \<open>id_position \<Rightarrow> \<tau>\<close> (\<open>\<Squnion>_\<close>)
  \<open>\<Squnion>\<psi> =\<^sub>d\<^sub>f \<^bold>\<iota>s LeastUpperBound(s,s. \<psi>{s})\<close>

AOT_theorem T37: \<open>\<Squnion>\<psi>\<down>\<close>
  using "rule-id-df:2:b[schematic]"[OF TheLeastUpperBound, OF TheLeastUpperBound_denotes] TheLeastUpperBound_denotes
  by simp

syntax "_TheLeastUpperBound" :: \<open>id_position \<Rightarrow> \<phi> \<Rightarrow> \<tau>\<close> (\<open>'(\<Squnion>_._')\<close>)
translations
  "_TheLeastUpperBound s \<phi>" == "CONST TheLeastUpperBound (_abs s \<phi>)"

AOT_theorem PairFusionTheorem: \<open>\<forall>s\<forall>t\<exists>!s'\<forall>p(s' \<Turnstile> p \<equiv> s \<Turnstile> p \<or> t \<Turnstile> p)\<close>
  by (auto intro!: Situation.GEN simp: "sit-comp-simp-unique")

syntax "_PairFusion" :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau>\<close> (infix \<open>\<squnion>\<close> 100)
abbreviation (input) PairFusion where \<open>PairFusion \<kappa> \<kappa>' \<equiv> \<guillemotleft>(\<Squnion>s'. s' = \<kappa> \<or> s' = \<kappa>')\<guillemotright>\<close>
translations
  "_PairFusion s t" => "CONST PairFusion s t"

notepad
begin
  AOT_modally_strict {
    AOT_have \<open>s \<squnion> t = (\<Squnion>s'. s' = s \<or> s' = t)\<close> for s t
      using "=I"(1)[OF T37].
  }
end

(* change to T43 *)
AOT_theorem T40: \<open>s \<squnion> t = \<^bold>\<iota>s'\<forall>p(s' \<Turnstile> p \<equiv> s \<Turnstile> p \<or> t \<Turnstile> p)\<close>
proof -
  AOT_have \<open>s \<squnion> t = (\<Squnion>s'. s' = s \<or> s' = t)\<close>
    using "=I"(1)[OF T37].
  AOT_have \<open>(\<Squnion>s'. s' = s \<or> s' = t) = \<^bold>\<iota>s' LeastUpperBound(s',s'. s' = s \<or> s' = t)\<close>
    using "rule-id-df:1[schematic].rule=E'" TheLeastUpperBound TheLeastUpperBound_denotes "=I"(1)[OF T37] by fastforce
  also AOT_have \<open>\<^bold>\<iota>s' LeastUpperBound(s',s'. s' = s \<or> s' = t) =  \<^bold>\<iota>s'\<forall>p(s' \<Turnstile> p \<equiv> s \<Turnstile> p \<or> t \<Turnstile> p)\<close>
  proof(safe intro!: "equiv-desc-eq:2"[THEN "\<rightarrow>E"] "&I" TheLeastUpperBound_denotes)
    AOT_show \<open>\<^bold>\<A>\<forall>x(Situation(x) & LeastUpperBound(x,s'. s' = s \<or> s' = t) \<equiv> Situation(x) & \<forall>p(x \<Turnstile> p \<equiv> s \<Turnstile> p \<or> t \<Turnstile> p))\<close>
    proof(safe intro!: "nec-imp-act"[THEN "\<rightarrow>E"] RN "\<equiv>I" GEN "\<rightarrow>I")
      AOT_modally_strict {
        AOT_have desc_denotes: \<open>\<^bold>\<iota>s'\<forall>p(s' \<Turnstile> p \<equiv> s \<Turnstile> p \<or> t \<Turnstile> p)\<down>\<close>
          by (simp add: "sit-comp-simp:3")
        then AOT_obtain s\<^sub>0 where \<open>s\<^sub>0 = \<^bold>\<iota>s'\<forall>p(s' \<Turnstile> p \<equiv> s \<Turnstile> p \<or> t \<Turnstile> p)\<close>
          by (metis (no_types, lifting) "Act-Basic:2.\<equiv>E(1).&E(1)" "actual-desc:4.\<rightarrow>E" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "existential:1"
              "possit-sit:4.unvarify_x.\<forall>E(1).\<equiv>E(1)" "rule=I:1" Situation.instantiation id_sym)
        AOT_hence true_in_desc: \<open>s\<^sub>0 \<Turnstile> p \<equiv> (s \<Turnstile> p \<or> t \<Turnstile> p)\<close> for p
        proof (safe intro!: "sit-comp-simp:4"[THEN "\<rightarrow>E", THEN "\<forall>E"(2)] "strict-can:1[I]" "\<rightarrow>I" GEN)
          AOT_modally_strict {
            fix p
            AOT_assume \<open>s \<Turnstile> p \<or> t \<Turnstile> p\<close>
            AOT_thus \<open>\<box>(s \<Turnstile> p \<or> t \<Turnstile> p)\<close>
              using "KBasic:15.\<rightarrow>E" "intro-elim:1" "lem2:1" by blast
          }
        qed
        AOT_have s\<^sub>0_upper_bound: \<open>UpperBound(s\<^sub>0,s'. s' = s \<or> s' = t)\<close>
        proof(safe intro!: "\<equiv>\<^sub>d\<^sub>fI"[OF UpperBound] "&I" Situation.GEN "\<rightarrow>I" Situation.\<psi>)
          fix s'
          AOT_assume \<open>s' = s \<or> s' = t\<close>
          moreover {
            AOT_assume 0: \<open>s' = s\<close>
            AOT_have \<open>s \<unlhd> s\<^sub>0\<close>
              by (metis (no_types, lifting) "con-dis-i-e:3:a" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "intro-elim:3:b" "sit-part-whole.\<equiv>\<^sub>d\<^sub>fI" CP GEN
                  Situation.restricted_var_condition true_in_desc)
            AOT_hence \<open>s' \<unlhd> s\<^sub>0\<close>
              using "rule=E"[rotated, OF 0[symmetric]] by fast
          }
          moreover {
            AOT_assume 0: \<open>s' = t\<close>
            AOT_have \<open>t \<unlhd> s\<^sub>0\<close>
              by (metis (no_types, lifting) "\<or>I"(2) "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "intro-elim:3:b" "sit-part-whole.\<equiv>\<^sub>d\<^sub>fI" CP GEN Situation.restricted_var_condition
                  true_in_desc)
            AOT_hence \<open>s' \<unlhd> s\<^sub>0\<close>
              using "rule=E"[rotated, OF 0[symmetric]] by fast
          }
          ultimately AOT_show \<open>s' \<unlhd> s\<^sub>0\<close>
            using "con-dis-i-e:4:b" "raa-cor:2" by blast
        qed

        fix x
        AOT_assume 0: \<open>Situation(x) & LeastUpperBound(x,s'. s' = s \<or> s' = t)\<close>
        AOT_hence \<open>UpperBound(x,s'. s' = s \<or> s' = t)\<close>
          using "LeastUpperBound.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(1)" "con-dis-i-e:2:b" by blast
        AOT_hence \<open>s' \<unlhd> x\<close> if \<open>s' = s \<or> s' = t\<close> for s'
          using "UpperBound.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E.\<rightarrow>E" "cqt:2"(1) Situation.restricted_var_condition that by blast
        AOT_hence s_part_x: \<open>s \<unlhd> x\<close> and t_part_x: \<open>t \<unlhd> x\<close>
          by (auto simp add: "\<or>I" "id-eq:1")
        AOT_have x_part_s\<^sub>0: \<open>x \<unlhd> s\<^sub>0\<close>
          using 0[THEN "&E"(2), THEN "\<equiv>\<^sub>d\<^sub>fE"[OF LeastUpperBound], THEN "&E"(2), THEN "&E"(2), THEN "Situation.\<forall>E", THEN "\<rightarrow>E", OF s\<^sub>0_upper_bound]
          by simp
        AOT_show \<open>Situation(x) & \<forall>p(x \<Turnstile> p \<equiv> s \<Turnstile> p \<or> t \<Turnstile> p)\<close>
        proof(safe intro!: "&I" 0[THEN "&E"(1)] GEN "\<equiv>I" "\<rightarrow>I")
          fix p
          AOT_assume \<open>x \<Turnstile> p\<close>
          AOT_thus \<open>s \<Turnstile> p \<or> t \<Turnstile> p\<close>
            using "intro-elim:3:a" "log-prop-prop:2" "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E" true_in_desc x_part_s\<^sub>0 by blast
        next
          fix p
          AOT_assume \<open>s \<Turnstile> p \<or> t \<Turnstile> p\<close>
          AOT_thus \<open>x \<Turnstile> p\<close>
            using "con-dis-i-e:4:c" "log-prop-prop:2" "raa-cor:1" "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E" s_part_x t_part_x by blast
        qed
      }
    next
      AOT_modally_strict {
        fix x
        AOT_assume 0: \<open>Situation(x) & \<forall>p(x \<Turnstile> p \<equiv> s \<Turnstile> p \<or> t \<Turnstile> p)\<close>
        AOT_show \<open>Situation(x) & LeastUpperBound(x,s'. s' = s \<or> s' = t)\<close>
        proof(safe intro!: "&I" 0[THEN "&E"(1)] Situation.GEN "\<equiv>I" "\<rightarrow>I" "\<equiv>\<^sub>d\<^sub>fI"[OF LeastUpperBound] "\<equiv>\<^sub>d\<^sub>fI"[OF UpperBound])
          fix t'
          AOT_assume \<open>t' = s \<or> t' = t\<close>
          moreover {
            AOT_assume 1: \<open>t' = s\<close>
            AOT_have \<open>s \<unlhd> x\<close>
              by (safe intro!: "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" Situation.\<psi> 0[THEN "&E"(1)])
                 (metis (no_types, lifting) "0" "con-dis-i-e:2:b" "con-dis-i-e:3:a" "deduction-theorem" "intro-elim:3:b" "rule-ui:3" "universal-cor")
            AOT_hence \<open>t' \<unlhd> x\<close>
              using "rule=E"[rotated, OF 1[symmetric]] by fast
          }
          moreover {
            AOT_assume 1: \<open>t' = t\<close>
            AOT_have \<open>t \<unlhd> x\<close>
              by (safe intro!: "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" Situation.\<psi> 0[THEN "&E"(1)])
                 (metis (lifting) "0" "con-dis-i-e:2:b" "con-dis-i-e:3:b" "deduction-theorem" "intro-elim:3:b" "rule-ui:3" "universal-cor")
            AOT_hence \<open>t' \<unlhd> x\<close>
              using "rule=E"[rotated, OF 1[symmetric]] by fast
          }
          ultimately AOT_show \<open>t' \<unlhd> x\<close>
            using "con-dis-i-e:4:c" "raa-cor:2" by blast
        next
          fix t'
          AOT_assume \<open>UpperBound(t',s'. s' = s \<or> s' = t)\<close>
          AOT_hence \<open>s' \<unlhd> t'\<close> if \<open>s' = s \<or> s' = t\<close> for s'
            using "UpperBound.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E.\<rightarrow>E" "cqt:2"(1) Situation.restricted_var_condition that by blast
          AOT_hence s_part_t': \<open>s \<unlhd> t'\<close> and t_part_t': \<open>t \<unlhd> t'\<close>
            by (auto simp add: "\<or>I" "id-eq:1")
          AOT_show \<open>x \<unlhd> t'\<close>
          proof(safe intro!: "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" 0[THEN "&E"(1)] Situation.\<psi> GEN "\<rightarrow>I")
            fix p
            AOT_assume \<open>x \<Turnstile> p\<close>
            AOT_hence \<open>s \<Turnstile> p \<or> t \<Turnstile> p\<close>
              using "0" "con-dis-i-e:2:b" "intro-elim:3:a" "log-prop-prop:2" "rule-ui:1" by blast
            AOT_thus \<open>t' \<Turnstile> p\<close>
              using "con-dis-i-e:4:b" "log-prop-prop:2" "raa-cor:1" "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E" s_part_t' t_part_t' by blast
          qed
        qed
      }
    qed
  qed
  finally AOT_show \<open>(\<Squnion>s'. s' = s \<or> s' = t) = \<^bold>\<iota>s'\<forall>p(s' \<Turnstile> p \<equiv> s \<Turnstile> p \<or> t \<Turnstile> p)\<close>.
qed

AOT_theorem PairFusion_denotes_lem: \<open>\<^bold>\<iota>s'\<forall>p(s' \<Turnstile> p \<equiv> s \<Turnstile> p \<or> t \<Turnstile> p)\<down>\<close>
  by (simp add: "sit-comp-simp:3")

AOT_theorem PairFusion_denotes: \<open>s \<squnion> t\<down>\<close>
  by (simp add: T37)

AOT_theorem PairFusion_situation: \<open>Situation(s \<squnion> t)\<close>
proof -
  AOT_have \<open>\<^bold>\<A>Situation(\<^bold>\<iota>s'\<forall>p(s' \<Turnstile> p \<equiv> s \<Turnstile> p \<or> t \<Turnstile> p))\<close>
    using "Act-Basic:2.\<equiv>E(1).&E(1)" "actual-desc:4.\<rightarrow>E" PairFusion_denotes_lem by blast
  AOT_hence \<open>\<^bold>\<A>Situation(s \<squnion> t)\<close>
    using "rule=E"[rotated, OF T40[symmetric]] by fast
  thus ?thesis
    by (simp add: "possit-sit:4.unvarify_x.\<forall>E(1).\<equiv>E(1)" PairFusion_denotes)
qed

AOT_theorem PairFusion_prop: \<open>s \<squnion> t \<Turnstile> p \<equiv> s \<Turnstile> p \<or> t \<Turnstile> p\<close>
proof -
  AOT_have \<open>\<^bold>\<A>\<forall>p(\<^bold>\<iota>s'\<forall>p(s' \<Turnstile> p \<equiv> s \<Turnstile> p \<or> t \<Turnstile> p) \<Turnstile> p \<equiv> s \<Turnstile> p \<or> t \<Turnstile> p)\<close>
    using "Act-Basic:2.\<equiv>E(1).&E(2)" "actual-desc:4.\<rightarrow>E" PairFusion_denotes_lem by blast
  AOT_hence \<open>\<^bold>\<A>\<forall>p(s \<squnion> t \<Turnstile> p \<equiv> s \<Turnstile> p \<or> t \<Turnstile> p)\<close>
    using "rule=E"[rotated, OF T40[symmetric]] by fast
  AOT_hence \<open>\<forall>p\<^bold>\<A>(s \<squnion> t \<Turnstile> p \<equiv> s \<Turnstile> p \<or> t \<Turnstile> p)\<close>
    by (meson "RA[2]" "act-cond.\<rightarrow>E.\<rightarrow>E" "cqt-basic:5" "universal-cor")
  AOT_hence \<open>\<^bold>\<A>(s \<squnion> t \<Turnstile> p \<equiv> s \<Turnstile> p \<or> t \<Turnstile> p)\<close>
    using "rule-ui:2[const_var]" by auto
  AOT_hence \<open>\<^bold>\<A>s \<squnion> t \<Turnstile> p \<equiv> \<^bold>\<A>(s \<Turnstile> p \<or> t \<Turnstile> p)\<close>
    using "Act-Basic:5" "intro-elim:3:a" by blast
  AOT_hence \<open>s \<squnion> t \<Turnstile> p \<equiv> \<^bold>\<A>(s \<Turnstile> p \<or> t \<Turnstile> p)\<close>
    using "lem2:4"[unconstrain s, unvarify \<beta>, OF PairFusion_denotes, THEN "\<rightarrow>E",
                   OF PairFusion_situation] "intro-elim:3:f" by blast
  also AOT_have \<open>\<dots> \<equiv> \<^bold>\<A>(s \<Turnstile> p) \<or> \<^bold>\<A>(t \<Turnstile> p)\<close>
    using "Act-Basic:9" by auto
  also AOT_have \<open>\<dots> \<equiv> s \<Turnstile> p \<or> t \<Turnstile> p\<close>
    using "intro-elim:3:e" "lem2:4" "oth-class-taut:8:g.\<rightarrow>E" "oth-class-taut:8:h.\<rightarrow>E" by blast
  finally show ?thesis.
qed


AOT_theorem ClosureUnderPartPrinciple: \<open>(Possible(s) & t \<unlhd> s) \<rightarrow> Possible(t)\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_assume 0: \<open>Possible(s) & t \<unlhd> s\<close>
  AOT_hence \<open>\<exists>w(s \<unlhd> w)\<close>
    using "con-dis-i-e:2:a" "intro-elim:3:a" "poss-sit-part-w:1" by blast
  then AOT_obtain w\<^sub>1 where \<open>s \<unlhd> w\<^sub>1\<close>
    using PossibleWorld.instantiation by blast
  AOT_hence \<open>t \<unlhd> w\<^sub>1\<close>
    using 0[THEN "&E"(2)]
    by (meson "con-dis-i-e:1" "cqt:2"(1)
        "part:3.unconstrain_s.unconstrain_s'.unconstrain_s''.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<rightarrow>E"
        "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(1).&E(1)" "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(1).&E(2)")
  AOT_hence \<open>\<exists>w t \<unlhd> w\<close>
    by (rule "PossibleWorld.\<exists>I")
  AOT_thus \<open>Possible(t)\<close>
    by (simp add: "poss-sit-part-w:1.unconstrain_s.\<forall>E(1).\<rightarrow>E.\<equiv>E(2)" "situations:3.\<rightarrow>E"
        Situation.restricted_var_condition)
qed

AOT_define Compatible :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>Compatible'(_,_')\<close>)
  \<open>Compatible(s,t) \<equiv>\<^sub>d\<^sub>f Possible(s \<squnion> t)\<close>

AOT_define Incompatible :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>Incompatible'(_,_')\<close>)
  \<open>Incompatible(s,t) \<equiv>\<^sub>d\<^sub>f \<not>Possible(s \<squnion> t)\<close>

AOT_define WorldState :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>WorldState'(_')\<close>)
  \<open>WorldState(s) \<equiv>\<^sub>d\<^sub>f Possible(s) & \<forall>t(t \<unlhd> s \<or> Incompatible(t, s))\<close>

AOT_theorem \<open>WorldState(s) \<equiv> PossibleWorld(s)\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume A: \<open>WorldState(s)\<close>
  AOT_hence 0: \<open>Possible(s)\<close> and B: \<open>\<forall>t(t \<unlhd> s \<or> Incompatible(t, s))\<close>
    using "WorldState.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(1)" "WorldState"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), THEN "&E"(2)]
    by auto
  moreover AOT_have \<open>Maximal(s)\<close>
  proof(rule "raa-cor:1")
    AOT_assume 1: \<open>\<not>Maximal(s)\<close>
    AOT_hence 2: \<open>\<exists>p \<not>(s \<Turnstile> p \<or> s \<Turnstile> \<not>p)\<close>
      by (metis (no_types, lifting) "con-dis-i-e:1" "existential:1" "log-prop-prop:2" "max.\<equiv>\<^sub>d\<^sub>fI"
          "raa-cor:2" "universal-cor" Situation.restricted_var_condition)
    then AOT_obtain q\<^sub>1 where q\<^sub>1_prop: \<open>\<not>s \<Turnstile> q\<^sub>1 & \<not>s \<Turnstile> \<not>q\<^sub>1\<close>
      using "\<exists>E'" "intro-elim:3:a" "oth-class-taut:5:d" by blast
    AOT_have 3: \<open>\<exists>w s \<unlhd> w\<close>
      using 0 "intro-elim:3:a" "poss-sit-part-w:1" by blast
    then AOT_obtain w\<^sub>1 where w\<^sub>1_prop: \<open>s \<unlhd> w\<^sub>1\<close>
      using PossibleWorld.instantiation by blast
    AOT_have 4: \<open>w\<^sub>1 \<Turnstile> q\<^sub>1 \<or> w\<^sub>1 \<Turnstile> \<not>q\<^sub>1\<close>
      by (simp add: "cqt:2"(1) "max.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1)" "world-max")
    moreover {
      AOT_assume 5: \<open>w\<^sub>1 \<Turnstile> q\<^sub>1\<close>
      AOT_hence 6: \<open>s\<^sup>+q\<^sub>1 \<unlhd> w\<^sub>1\<close>
        by (simp add: "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "log-prop-prop:2"
          "poss-sit-part-w:2.unconstrain_s.unvarify_p.unconstrain_w.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<equiv>E(2)"
          "situations:3.\<rightarrow>E"  "world:3.\<rightarrow>E" PossibleWorld.restricted_var_condition
          Situation.restricted_var_condition w\<^sub>1_prop)
      AOT_hence 7: \<open>Possible(s\<^sup>+q\<^sub>1)\<close>
        by (meson "ClosureUnderPartPrinciple.unconstrain_s.unconstrain_t.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<rightarrow>E"
            "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(1).&E(1)"
            "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(1).&E(2)" "situations:3.\<rightarrow>E" "world-pos")
      AOT_obtain t where t_prop: \<open>\<forall>p(t \<Turnstile> p \<equiv> p = q\<^sub>1)\<close>
        using "sit-comp-simp:1" Situation.instantiation[rotated] by meson
      AOT_hence 8: \<open>t \<Turnstile> q\<^sub>1\<close>
        using "intro-elim:3:b" "rule-ui:3" "rule=I:2[const_var]" by blast
      AOT_hence 9: \<open>\<not>t \<unlhd> s\<close>
        by (metis "con-dis-i-e:2:a" "log-prop-prop:2" "raa-cor:3"
            "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E" q\<^sub>1_prop)
      AOT_hence 10: \<open>Incompatible(t,s)\<close>
        using "8" "WorldState.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(2).\<forall>E(1).\<rightarrow>E" "con-dis-i-e:4:b"
          "situations:3.\<rightarrow>E" "true-in-s.\<equiv>\<^sub>d\<^sub>fE.&E(1)" A by blast
      AOT_have 11: \<open>s\<^sup>+q\<^sub>1 = t \<squnion> s\<close>
      proof(safe intro!: "sit-identity"[unconstrain s, unvarify \<beta>, OF pext_denotes,
            THEN "\<rightarrow>E", OF pext_situation, unconstrain s', unvarify \<beta>, OF PairFusion_denotes,
            THEN "\<rightarrow>E", OF PairFusion_situation, THEN "\<equiv>E"(2)] GEN "\<equiv>I" "\<rightarrow>I")
        fix p
        AOT_assume \<open>s\<^sup>+q\<^sub>1 \<Turnstile> p\<close>
        AOT_hence \<open>s \<Turnstile> p \<or> p = q\<^sub>1\<close>
          by (simp add: "cqt:2"(1) Situation.restricted_var_condition
              "pext-lem:2.unconstrain_s.unvarify_p.unvarify_q.\<forall>E(1).\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<equiv>E(1)")
        AOT_thus \<open>t \<squnion> s \<Turnstile> p\<close>
          by (metis "8" "con-dis-i-e:3:a" "con-dis-i-e:4:c" "con-dis-taut:4.\<rightarrow>E" "log-prop-prop:2"
          "raa-cor:1" "situations:3.\<rightarrow>E" "term-out:5.unvarify_\<beta>.\<forall>E(1).\<equiv>E(2).\<forall>E(1).\<rightarrow>E" Situation.\<psi>
          "PairFusion_prop.unconstrain_s.unconstrain_t.unvarify_p.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<equiv>E(2)")
      next
        fix p
        AOT_assume \<open>t \<squnion> s \<Turnstile> p\<close>
        AOT_hence \<open>t \<Turnstile> p \<or> s \<Turnstile> p\<close>
          by (simp add: "cqt:2"(1) Situation.restricted_var_condition
          "PairFusion_prop.unconstrain_s.unconstrain_t.unvarify_p.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<equiv>E(1)")
        AOT_hence \<open>p = q\<^sub>1 \<or> s \<Turnstile> p\<close>
          using "intro-elim:1" "oth-class-taut:3:a" "rule-ui:3" t_prop by blast
        AOT_thus \<open>s\<^sup>+q\<^sub>1 \<Turnstile> p\<close>
          by (metis "con-dis-i-e:4:c" "id_sym.rule=E'" "log-prop-prop:2"
              "pext-lem:3.unconstrain_s.unvarify_q.unvarify_p.\<forall>E(1).\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<rightarrow>E"
              "pext-lem:4" "raa-cor:2" "situations:3.\<rightarrow>E" Situation.restricted_var_condition)
      qed
      AOT_hence 12: \<open>t \<squnion> s \<unlhd> w\<^sub>1\<close>
        by (meson "6" "id_sym.rule=E'" id_sym)
      AOT_hence 13: \<open>Possible(t \<squnion> s)\<close>
        using "11" "7" "rule=E" by blast
      AOT_hence \<open>p & \<not>p\<close> for p
        using "10" "Incompatible.\<equiv>\<^sub>d\<^sub>fE.&E(2)" "raa-cor:4" by blast
    }
    moreover {
      AOT_assume 5: \<open>w\<^sub>1 \<Turnstile> \<not>q\<^sub>1\<close>
      AOT_hence 6: \<open>s\<^sup>+\<not>q\<^sub>1 \<unlhd> w\<^sub>1\<close>
        by (simp add: "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "log-prop-prop:2"  Situation.\<psi> w\<^sub>1_prop
          "poss-sit-part-w:2.unconstrain_s.unvarify_p.unconstrain_w.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<equiv>E(2)"
          "situations:3.\<rightarrow>E" "world:3.\<rightarrow>E" PossibleWorld.restricted_var_condition)
      AOT_hence 7: \<open>Possible(s\<^sup>+\<not>q\<^sub>1)\<close>
        by (meson "ClosureUnderPartPrinciple.unconstrain_s.unconstrain_t.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<rightarrow>E"
            "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(1).&E(1)"
            "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(1).&E(2)" "situations:3.\<rightarrow>E" "world-pos")
      AOT_obtain t where t_prop: \<open>\<forall>p(t \<Turnstile> p \<equiv> p = (\<not>q\<^sub>1))\<close>
        using "sit-comp-simp:1" Situation.instantiation[rotated] by meson
      AOT_hence 8: \<open>t \<Turnstile> \<not>q\<^sub>1\<close>
        using "intro-elim:3:b" "log-prop-prop:2" "rule-ui:1" "rule=I:1" by blast
      AOT_hence 9: \<open>\<not>t \<unlhd> s\<close>
        by (metis "con-dis-i-e:2:b" "log-prop-prop:2" "reductio-aa:1"
            "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E" q\<^sub>1_prop)
      AOT_hence 10: \<open>Incompatible(t,s)\<close>
        using "8" "WorldState.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(2).\<forall>E(1).\<rightarrow>E" "con-dis-i-e:4:b" "situations:3.\<rightarrow>E"
          "true-in-s.\<equiv>\<^sub>d\<^sub>fE.&E(1)" A by blast
      AOT_have 11: \<open>s\<^sup>+\<not>q\<^sub>1 = t \<squnion> s\<close>
      proof(safe intro!: "sit-identity"[unconstrain s, unvarify \<beta>,
            OF pext_denotes[unvarify p, OF "log-prop-prop:2"], THEN "\<rightarrow>E",
            OF pext_situation[unvarify p, OF "log-prop-prop:2"], unconstrain s', unvarify \<beta>,
            OF PairFusion_denotes, THEN "\<rightarrow>E", OF PairFusion_situation, THEN "\<equiv>E"(2)]
          GEN "\<equiv>I" "\<rightarrow>I")
        fix p
        AOT_assume \<open>s\<^sup>+\<not>q\<^sub>1 \<Turnstile> p\<close>
        AOT_hence \<open>s \<Turnstile> p \<or> p = (\<not>q\<^sub>1)\<close>
          by (simp add: "cqt:2"(1) "log-prop-prop:2"
              "pext-lem:2.unconstrain_s.unvarify_p.unvarify_q.\<forall>E(1).\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<equiv>E(1)"
              Situation.restricted_var_condition)
        AOT_thus \<open>t \<squnion> s \<Turnstile> p\<close>
          by (metis "8" "con-dis-i-e:3:a" "con-dis-i-e:4:c"  "raa-cor:1" "situations:3.\<rightarrow>E"
            "PairFusion_prop.unconstrain_s.unconstrain_t.unvarify_p.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<equiv>E(2)"
              "con-dis-taut:4.\<rightarrow>E" "log-prop-prop:2" "term-out:5.unvarify_\<beta>.\<forall>E(1).\<equiv>E(2).\<forall>E(1).\<rightarrow>E"
              Situation.restricted_var_condition)
      next
        fix p
        AOT_assume \<open>t \<squnion> s \<Turnstile> p\<close>
        AOT_hence \<open>t \<Turnstile> p \<or> s \<Turnstile> p\<close>
          by (simp add:  "cqt:2"(1) Situation.\<psi>
           "PairFusion_prop.unconstrain_s.unconstrain_t.unvarify_p.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<equiv>E(1)")
        AOT_hence \<open>p = (\<not>q\<^sub>1) \<or> s \<Turnstile> p\<close>
          using "intro-elim:1" "oth-class-taut:3:a" "rule-ui:3" t_prop by blast
        AOT_thus \<open>s\<^sup>+\<not>q\<^sub>1 \<Turnstile> p\<close>
          by (meson "Commutativity of \<or>" "intro-elim:3:b" "log-prop-prop:2" "situations:3.\<rightarrow>E"
              "pext-lem:2.unconstrain_s.unvarify_p.unvarify_q.\<forall>E(1).\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<equiv>E(2)"
              Situation.\<psi>)
      qed
      AOT_hence 12: \<open>t \<squnion> s \<unlhd> w\<^sub>1\<close>
        by (metis (mono_tags, lifting) "6" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "cqt:2"(1)
            "part:3.unconstrain_s.unconstrain_s'.unconstrain_s''.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<rightarrow>E" "rule=E"
            "sit-identity2:1.unconstrain_s.unconstrain_s'.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<equiv>E(1).&E(2)" "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(1).&E(1)"
            "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(1).&E(2)" T37 id_sym)
      AOT_hence 13: \<open>Possible(t \<squnion> s)\<close>
        using "11" "7" "rule=E" by blast
      AOT_hence \<open>p & \<not>p\<close> for p
        using "10" "Incompatible.\<equiv>\<^sub>d\<^sub>fE.&E(2)" "raa-cor:4" by blast
    }
    ultimately AOT_show \<open>p & \<not>p\<close> for p
      using "con-dis-i-e:4:c" "raa-cor:1" by blast
  qed
  ultimately AOT_show \<open>PossibleWorld(s)\<close>
    by (simp add: "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "cqt:2"(1) "world=maxpos:2.unvarify_x.\<forall>E(1).\<equiv>E(2)")
next
  AOT_assume 0: \<open>PossibleWorld(s)\<close>
  AOT_hence 1: \<open>\<diamond>\<forall>p(s \<Turnstile> p \<equiv> p)\<close>
    by (simp add: "world:1.\<equiv>\<^sub>d\<^sub>fE.&E(2)")
  AOT_have \<open>Possible(s)\<close>
    by (simp add: "0" "world:3.\<rightarrow>E" "world=maxpos:2.unvarify_x.\<forall>E(1).\<equiv>E(1).&E(2)")
  moreover AOT_have \<open>\<forall>t(t \<unlhd> s \<or> Incompatible(t, s))\<close>
  proof(rule "raa-cor:1")
    AOT_assume \<open>\<not>\<forall>t(t \<unlhd> s \<or> Incompatible(t, s))\<close>
    AOT_hence \<open>\<exists>t \<not>(t \<unlhd> s \<or> Incompatible(t, s))\<close>
      by (metis (no_types, lifting) "existential:2[const_var]" "intro-elim:3:b"
          "oth-class-taut:1:a" "reductio-aa:1" "universal-cor")
    then AOT_obtain t\<^sub>1 where t\<^sub>1_prop: \<open>\<not>t\<^sub>1 \<unlhd> s & \<not>Incompatible(t\<^sub>1, s)\<close>
      by (metis (mono_tags, lifting) "\<exists>E'" "con-dis-i-e:2:a" "con-dis-i-e:2:b" "con-dis-i-e:3:a"
          "con-dis-taut:4.\<rightarrow>E" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E"
          "existential:2[const_var]" "raa-cor:3" Situation.instantiation)
    AOT_hence FusionPossible: \<open>Possible(t\<^sub>1 \<squnion> s)\<close>
      by (metis "Incompatible.\<equiv>\<^sub>d\<^sub>fI" "con-dis-i-e:1" "con-dis-i-e:2:b" "raa-cor:1"
                Situation.restricted_var_condition)
    AOT_have \<open>\<exists>q (t\<^sub>1 \<Turnstile> q & \<not>s \<Turnstile> q)\<close>
    proof(rule "raa-cor:1")
      AOT_assume \<open>\<not>\<exists>q (t\<^sub>1 \<Turnstile> q & \<not>s \<Turnstile> q)\<close>
      AOT_hence \<open>\<forall>q(t\<^sub>1 \<Turnstile> q \<rightarrow> s \<Turnstile> q)\<close>
        by (metis (lifting) "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "deduction-theorem"
            "existential:2[const_var]" "reductio-aa:1" "universal-cor")
      AOT_hence \<open>t\<^sub>1 \<unlhd> s\<close>
        using "\<equiv>\<^sub>d\<^sub>fI" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "sit-part-whole" Situation.\<psi> by blast
      AOT_thus \<open>t\<^sub>1 \<unlhd> s & \<not>t\<^sub>1 \<unlhd> s\<close>
        using t\<^sub>1_prop "&E" "&I" by blast
    qed
    then AOT_obtain q\<^sub>1 where q\<^sub>1_prop: \<open>t\<^sub>1 \<Turnstile> q\<^sub>1 & \<not>s \<Turnstile> q\<^sub>1\<close>
      using "\<exists>E'" by blast
    AOT_hence 2: \<open>s \<Turnstile> \<not>q\<^sub>1\<close>
      by (meson "0" "coherent:1.unconstrain_w.unvarify_p.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<equiv>E(2)"
          "con-dis-i-e:2:b" "cqt:2"(1))
    AOT_have \<open>\<not>Consistent(s\<^sup>+q\<^sub>1)\<close>
    proof(rule "raa-cor:2")
      AOT_assume \<open>Consistent(s\<^sup>+q\<^sub>1)\<close>
      AOT_hence A: \<open>\<not>\<exists>p((s\<^sup>+q\<^sub>1 \<Turnstile> p) & s\<^sup>+q\<^sub>1 \<Turnstile> \<not>p)\<close>
        by (simp add: "cons.\<equiv>\<^sub>d\<^sub>fE.&E(2)")
      moreover AOT_have \<open>\<exists>p ((s\<^sup>+q\<^sub>1 \<Turnstile> p) & s\<^sup>+q\<^sub>1 \<Turnstile> \<not>p)\<close>
        using "pext-lem:4" 2
        by (meson "0" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "existential:2[const_var]" "log-prop-prop:2"
            "pext-lem:3.unconstrain_s.unvarify_q.unvarify_p.\<forall>E(1).\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<rightarrow>E"
            "true-in-s.\<equiv>\<^sub>d\<^sub>fE.&E(1)" "world:3.\<rightarrow>E")
      ultimately AOT_show \<open>p & \<not>p\<close> for p
        using "raa-cor:4" by blast
    qed      
    AOT_hence 3: \<open>\<not>Possible(s\<^sup>+q\<^sub>1)\<close>
      by (simp add: "pos-cons-sit:1.unconstrain_s.\<forall>E(1).\<rightarrow>E.\<rightarrow>E" "reductio-aa:2"
          pext_denotes pext_situation)
    moreover AOT_have \<open>s\<^sup>+q\<^sub>1 \<unlhd> t\<^sub>1 \<squnion> s\<close>
    proof(safe intro!: "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" pext_situation
                       PairFusion_situation GEN "\<rightarrow>I")
      fix p
      AOT_assume \<open>s\<^sup>+q\<^sub>1 \<Turnstile> p\<close>
      AOT_hence \<open>s \<Turnstile> p \<or> p = q\<^sub>1\<close>
        by (simp add: "cqt:2"(1) Situation.\<psi>
            "pext-lem:2.unconstrain_s.unvarify_p.unvarify_q.\<forall>E(1).\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<equiv>E(1)")
      AOT_hence \<open>s \<Turnstile> p \<or> t\<^sub>1 \<Turnstile> p\<close>
        by (metis "con-dis-i-e:2:a" "con-dis-i-e:3:a" "con-dis-i-e:4:c" "con-dis-taut:4.\<rightarrow>E"
                  "raa-cor:1" "rule=E" id_sym q\<^sub>1_prop)
      AOT_thus \<open>t\<^sub>1 \<squnion> s \<Turnstile> p\<close>
        using "Commutativity of \<or>"  "intro-elim:3:b"
          "PairFusion_prop.unconstrain_s.unconstrain_t.unvarify_p.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<equiv>E(2)"
          "log-prop-prop:2" "situations:3.\<rightarrow>E" Situation.restricted_var_condition by blast
    qed
    ultimately AOT_have \<open>Possible(s\<^sup>+q\<^sub>1)\<close>
      by (metis "ClosureUnderPartPrinciple.unconstrain_s.unconstrain_t.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<rightarrow>E" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E"
          "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(1).&E(1)" "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(1).&E(2)" "situations:3.\<rightarrow>E" FusionPossible)
    AOT_thus \<open>p & \<not>p\<close> for p
      using "3" "raa-cor:4" by blast
  qed
  ultimately AOT_show \<open>WorldState(s)\<close>
    by (simp add: "WorldState.\<equiv>\<^sub>d\<^sub>fI" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" Situation.restricted_var_condition)
qed

AOT_theorem \<open>WorldState(s) \<rightarrow> \<forall>s'((s' \<noteq> s \<rightarrow> (s' \<unlhd> s \<or> Incompatible(s',s))))\<close>
proof(safe intro!: "\<rightarrow>I" Situation.GEN)
  fix s'
  AOT_assume 1: \<open>WorldState(s)\<close>
  AOT_assume 2: \<open>s' \<noteq> s\<close>
  AOT_show \<open>s' \<unlhd> s \<or> Incompatible(s',s)\<close>
  proof(rule "raa-cor:1")
    AOT_assume 3: \<open>\<not>(s' \<unlhd> s \<or> Incompatible(s',s))\<close>
    AOT_hence 4: \<open>\<not>s' \<unlhd> s & \<not>Incompatible(s',s)\<close>
      using "intro-elim:3:a" "oth-class-taut:5:d" by blast
    AOT_hence \<open>\<exists>p(s' \<Turnstile> p & \<not>s \<Turnstile> p)\<close>
      by (meson "1" "3" "WorldState.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(2).\<forall>E(1).\<rightarrow>E" "cqt:2"(1) "useful-tautologies:3.\<rightarrow>E.\<rightarrow>E"
          AOT_restricted_type.restricted_var_condition Situation.AOT_restricted_type_axioms)
    then AOT_obtain q where q: \<open>s' \<Turnstile> q & \<not>s \<Turnstile> q\<close>
      by (meson "instantiation")
    AOT_have 5: \<open>Compatible(s',s)\<close>
      using "1" "3" "WorldState.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(2).\<forall>E(1).\<rightarrow>E" "raa-cor:3" "situations:3.\<rightarrow>E" Situation.restricted_var_condition
      by blast
    AOT_hence 6: \<open>Possible(s' \<squnion> s)\<close>
      using "Compatible.\<equiv>\<^sub>d\<^sub>fE.&E(2)" by blast
    AOT_have 7: \<open>s' \<squnion> s \<Turnstile> q\<close>
      using "PairFusion_prop.unconstrain_s.unconstrain_t.unvarify_p.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<equiv>E(2)" "con-dis-i-e:2:a" "con-dis-i-e:3:a"
        "log-prop-prop:2" "situations:3.\<rightarrow>E" Situation.restricted_var_condition q by blast
    AOT_have 8: \<open>s' \<squnion> s \<Turnstile> \<not>q\<close>
      using "1" "3" "WorldState.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(2).\<forall>E(1).\<rightarrow>E" "raa-cor:3" "situations:3.\<rightarrow>E" Situation.restricted_var_condition
      by blast
    AOT_show \<open>p & \<not>p\<close> for p
      using "1" "3" "WorldState.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(2).\<forall>E(1).\<rightarrow>E" "raa-cor:4" "situations:3.\<rightarrow>E" Situation.restricted_var_condition
      by blast
  qed
qed

AOT_theorem T53: \<open>Possible(s) \<rightarrow> \<exists>s'(WorldState(s') \<rightarrow> s \<unlhd> s')\<close>
  by (meson "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "deduction-theorem" "existential:2[const_var]" "part:1"
      Situation.restricted_var_condition)

end