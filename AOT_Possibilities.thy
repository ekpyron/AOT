theory AOT_Possibilities
  imports AOT_PossibleWorlds
begin

section\<open>Possibilities\<close>

AOT_define ModallyClosed :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>ModallyClosed'(_')\<close>)
  "sit-clo": \<open>ModallyClosed(s) \<equiv>\<^sub>d\<^sub>f \<forall>p((Actual(s) \<Rightarrow> p) \<rightarrow> s \<Turnstile> p)\<close>

AOT_theorem "modal-clos-facts:1": \<open>ModallyClosed(s) \<rightarrow> \<forall>p\<forall>q((s \<Turnstile> p & (p \<Rightarrow> q)) \<rightarrow> s \<Turnstile> q)\<close>
proof(safe intro!: "\<rightarrow>I" GEN)
  fix p q
  AOT_assume \<open>ModallyClosed(s)\<close>
  AOT_hence \<theta>: \<open>\<forall>q((Actual(s) \<Rightarrow> q) \<rightarrow> s \<Turnstile> q)\<close>
    using "&E"(2) "rule-eq-df:2" "sit-clo" by blast
  AOT_assume \<xi>: \<open>s \<Turnstile> p & (p \<Rightarrow> q)\<close>
  AOT_have \<zeta>: \<open>(Actual(s) \<Rightarrow> q) \<rightarrow> s \<Turnstile> q\<close>
    using \<theta> "\<forall>E" by blast
  AOT_have \<open>\<forall>r(\<box>s \<Turnstile> r \<rightarrow> \<box>(Actual(s) \<rightarrow> r))\<close>
  proof(safe intro!: GEN)
    fix r
    AOT_modally_strict {
      AOT_have \<open>s \<Turnstile> r \<rightarrow> (Actual(s) \<rightarrow> r)\<close>
      proof(safe intro!: "\<rightarrow>I")
        AOT_assume 1: \<open>s \<Turnstile> r\<close>
        AOT_assume \<open>Actual(s)\<close>
        AOT_hence \<open>\<forall>p(s \<Turnstile> p \<rightarrow> p)\<close>
          using "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:b" actual by blast
        AOT_hence \<open>s \<Turnstile> r \<rightarrow> r\<close>
          using "\<forall>E" by blast
        AOT_thus \<open>r\<close>
          using 1 MP by blast
      qed
    }
    AOT_thus \<open>\<box>s \<Turnstile> r \<rightarrow> \<box>(Actual(s) \<rightarrow> r)\<close>
      using "RM:1" by blast
  qed
  AOT_hence \<open>\<box>s \<Turnstile> p \<rightarrow> \<box>(Actual(s) \<rightarrow> p)\<close>
    using "\<forall>E" by blast
  moreover AOT_have \<open>\<box>s \<Turnstile> p\<close>
    using \<xi> "con-dis-i-e:2:a" "intro-elim:3:a" "lem2:1" by blast
  ultimately AOT_have \<open>\<box>(Actual(s) \<rightarrow> p)\<close>
    using "vdash-properties:10" by blast
  AOT_hence \<open>Actual(s) \<Rightarrow> p\<close>
    using "\<equiv>\<^sub>d\<^sub>fI" "nec-impl-p:1" by blast
  AOT_hence \<open>Actual(s) \<Rightarrow> q\<close>
    using \<xi>
    using "nec-impl-p:3[trans]"[unvarify p, OF "log-prop-prop:2"]
    by (meson "con-dis-i-e:1" "con-dis-i-e:2:b" "vdash-properties:10")
  AOT_thus \<open>s \<Turnstile> q\<close>
    using \<zeta> "\<rightarrow>E" by blast
qed

AOT_theorem "modal-clos-facts:1b":
  \<open>ModallyClosed(s) \<rightarrow> \<forall>p\<^sub>1\<forall>p\<^sub>2\<forall>q((s \<Turnstile> p\<^sub>1 & s \<Turnstile> p\<^sub>2 & ((p\<^sub>1 & p\<^sub>2) \<Rightarrow> q)) \<rightarrow> s \<Turnstile> q)\<close>
proof(safe intro!: "\<rightarrow>I" GEN)
  fix p\<^sub>1 p\<^sub>2 q
  AOT_assume \<open>ModallyClosed(s)\<close>
  AOT_hence \<theta>: \<open>\<forall>q((Actual(s) \<Rightarrow> q) \<rightarrow> s \<Turnstile> q)\<close>
    using "&E"(2) "rule-eq-df:2" "sit-clo" by blast
  AOT_assume \<xi>: \<open>s \<Turnstile> p\<^sub>1 & s \<Turnstile> p\<^sub>2 & ((p\<^sub>1 & p\<^sub>2) \<Rightarrow> q)\<close>
  AOT_have \<zeta>: \<open>(Actual(s) \<Rightarrow> q) \<rightarrow> s \<Turnstile> q\<close>
    using \<theta> "\<forall>E" by blast
  AOT_have 0: \<open>\<forall>r(\<box>s \<Turnstile> r \<rightarrow> \<box>(Actual(s) \<rightarrow> r))\<close>
  proof(safe intro!: GEN)
    fix r
    AOT_modally_strict {
      AOT_have \<open>s \<Turnstile> r \<rightarrow> (Actual(s) \<rightarrow> r)\<close>
      proof(safe intro!: "\<rightarrow>I")
        AOT_assume 1: \<open>s \<Turnstile> r\<close>
        AOT_assume \<open>Actual(s)\<close>
        AOT_hence \<open>\<forall>p(s \<Turnstile> p \<rightarrow> p)\<close>
          using "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:b" actual by blast
        AOT_hence \<open>s \<Turnstile> r \<rightarrow> r\<close>
          using "\<forall>E" by blast
        AOT_thus \<open>r\<close>
          using 1 MP by blast
      qed
    }
    AOT_thus \<open>\<box>s \<Turnstile> r \<rightarrow> \<box>(Actual(s) \<rightarrow> r)\<close>
      using "RM:1" by blast
  qed
  AOT_hence \<open>\<box>s \<Turnstile> p\<^sub>1 \<rightarrow> \<box>(Actual(s) \<rightarrow> p\<^sub>1)\<close>
    using "\<forall>E" by blast
  moreover AOT_have \<open>\<box>s \<Turnstile> p\<^sub>1\<close>
    using \<xi> "con-dis-i-e:2:a" "intro-elim:3:a" "lem2:1" by blast
  ultimately AOT_have 1: \<open>\<box>(Actual(s) \<rightarrow> p\<^sub>1)\<close>
    using "vdash-properties:10" by blast
  AOT_have \<open>\<box>s \<Turnstile> p\<^sub>2 \<rightarrow> \<box>(Actual(s) \<rightarrow> p\<^sub>2)\<close>
    using 0 "\<forall>E" by blast
  moreover AOT_have \<open>\<box>s \<Turnstile> p\<^sub>2\<close>
    using \<xi> "con-dis-i-e:2:a" "intro-elim:3:a" "lem2:1"
    using "con-dis-i-e:2:b" by blast
  ultimately AOT_have \<open>\<box>(Actual(s) \<rightarrow> p\<^sub>2)\<close>
    using "vdash-properties:10" by blast
  AOT_hence \<open>\<box>(Actual(s) \<rightarrow> (p\<^sub>1 & p\<^sub>2))\<close>
    by (meson "1" "KBasic:1.\<rightarrow>E" "KBasic:5.\<rightarrow>E.\<equiv>E(1)" "RM:1.\<rightarrow>E" "con-dis-i-e:1" "oth-class-taut:8:b")
  AOT_hence \<open>Actual(s) \<Rightarrow> (p\<^sub>1 & p\<^sub>2)\<close>
    by (simp add: "nec-impl-p:1.\<equiv>\<^sub>d\<^sub>fI")
  AOT_hence \<open>Actual(s) \<Rightarrow> q\<close>
    using \<xi>
    using "nec-impl-p:3[trans]"[unvarify p, OF "log-prop-prop:2"]
    by (meson "&E"(2) "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "log-prop-prop:2"
              "nec-impl-p:3[trans].unvarify_p.unvarify_q.unvarify_r.\<forall>E(1).\<forall>E(1).\<forall>E(1).\<rightarrow>E")
  AOT_thus \<open>s \<Turnstile> q\<close>
    using \<zeta> "\<rightarrow>E" by blast
qed

AOT_theorem "modal-clos-facts:2": \<open>(ModallyClosed(s) & Consistent(s)) \<rightarrow> Possible(s)\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_assume 1: \<open>ModallyClosed(s) & Consistent(s)\<close>

  AOT_have \<theta>: \<open>\<forall>q((Actual(s) \<Rightarrow> q) \<rightarrow> s \<Turnstile> q)\<close>
    using 1 "\<equiv>\<^sub>d\<^sub>fE" "&E" "sit-clo" by blast
  AOT_have \<xi>: \<open>\<not>\<exists>p(s \<Turnstile> p & s \<Turnstile> \<not>p)\<close>
    using 1 by (metis (no_types, lifting) "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:b" "existential:2[const_var]"
                                          "instantiation" "reductio-aa:1" cons)

  AOT_show \<open>Possible(s)\<close>
  proof(rule "RAA")
    AOT_assume \<open>\<not>Possible(s)\<close>
    AOT_hence \<open>\<not>(Situation(s) & \<diamond>Actual(s))\<close>
      by (AOT_subst_def (reverse) pos)
    AOT_thus \<open>\<not>\<diamond>Actual(s)\<close>
      using "con-dis-i-e:1" "raa-cor:6" Situation.restricted_var_condition by presburger
    AOT_hence \<open>\<not>Actual(s)\<close>
      by (metis "T\<diamond>" "modus-tollens:1")
    AOT_hence \<open>\<not>(Situation(s) & \<forall>p (s \<Turnstile> p \<rightarrow> p))\<close>
      by (AOT_subst_def (reverse) actual)
    AOT_hence \<open>\<not>(\<forall>p (s \<Turnstile> p \<rightarrow> p))\<close>
      by (meson "con-dis-i-e:1" "raa-cor:6" Situation.restricted_var_condition)
    AOT_hence 2: \<open>\<exists>p \<not>(s \<Turnstile> p \<rightarrow> p)\<close>
      by (meson "existential:1" "log-prop-prop:2" "reductio-aa:1" "universal-cor")
    AOT_have \<open>\<exists>p(s \<Turnstile> p & \<not>p)\<close>
    proof (AOT_subst \<open>s \<Turnstile> p & \<not>p\<close> \<open>\<not>(s \<Turnstile> p \<rightarrow> p)\<close> for: p)
      AOT_modally_strict {
        fix p
        AOT_show \<open>s \<Turnstile> p & \<not>p \<equiv> \<not>(s \<Turnstile> p \<rightarrow> p)\<close>
          by (meson "intro-elim:3:f" "oth-class-taut:1:b" "oth-class-taut:3:a")
      }
    next
      AOT_show \<open>\<exists>p \<not>(s \<Turnstile> p \<rightarrow> p)\<close>
        using 2.
    qed
    then AOT_obtain p\<^sub>1 where \<open>s \<Turnstile> p\<^sub>1 & \<not>p\<^sub>1\<close>
      using "\<exists>E" by meson
    AOT_hence \<open>\<not>s \<Turnstile> \<not>p\<^sub>1\<close>
      using \<xi>
      by (metis (mono_tags, lifting) "con-dis-i-e:1" "con-dis-i-e:2:a"
                                     "existential:2[const_var]" "raa-cor:6")
    moreover AOT_have \<open>((Actual(s) \<Rightarrow> \<not>p\<^sub>1) \<rightarrow> s \<Turnstile> \<not>p\<^sub>1)\<close>
      using \<theta> "log-prop-prop:2" "rule-ui:1" by blast
    ultimately AOT_have \<open>\<not>(Actual(s) \<Rightarrow> \<not>p\<^sub>1)\<close>
      using "modus-tollens:1" by blast
    AOT_hence \<open>\<not>\<box>(Actual(s) \<rightarrow> \<not>p\<^sub>1)\<close>
      by (AOT_subst_def (reverse) "nec-impl-p:1")
    AOT_hence 2: \<open>\<diamond>\<not>(Actual(s) \<rightarrow> \<not>p\<^sub>1)\<close>
      using "KBasic:11" "\<equiv>E"(1) by blast
    AOT_have \<open>\<diamond>(Actual(s) & \<not>\<not>p\<^sub>1)\<close>
    proof (AOT_subst \<open>Actual(s) & \<not>\<not>p\<^sub>1\<close> \<open>\<not>(Actual(s) \<rightarrow> \<not>p\<^sub>1)\<close>)
      AOT_modally_strict {
        AOT_show \<open>Actual(s) & \<not>\<not>p\<^sub>1 \<equiv> \<not>(Actual(s) \<rightarrow> \<not>p\<^sub>1)\<close>
          using "intro-elim:3:f" "oth-class-taut:1:b" "oth-class-taut:3:a" by blast
      }
    next
      AOT_show \<open>\<diamond>\<not>(Actual(s) \<rightarrow> \<not>p\<^sub>1)\<close>
        using 2.
    qed
    AOT_thus \<open>\<diamond>(Actual(s))\<close>
      using "RM\<diamond>" "con-dis-taut:1" "vdash-properties:10" by blast
  qed
qed

AOT_theorem "modal-clos-facts:3": \<open>(ModallyClosed(s) & \<box>p) \<rightarrow> s \<Turnstile> p\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_assume 1: \<open>ModallyClosed(s) & \<box>p\<close>
  AOT_hence \<open>\<box>p\<close>
    using "&E" by blast
  AOT_hence \<open>\<box>(Actual(s) \<rightarrow> p)\<close>
    using "KBasic:1" "\<rightarrow>E" by blast
  AOT_hence 2: \<open>Actual(s) \<Rightarrow> p\<close>
    using "\<equiv>\<^sub>d\<^sub>fI" "nec-impl-p:1" by blast
  AOT_have \<open>ModallyClosed(s)\<close>
    using 1 "&E" by blast
  AOT_hence \<open>\<forall>p((Actual(s) \<Rightarrow> p) \<rightarrow> s \<Turnstile> p)\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:b" "sit-clo" by blast
  AOT_hence \<open>(Actual(s) \<Rightarrow> p) \<rightarrow> s \<Turnstile> p\<close>
    using "\<forall>E" by blast
  AOT_thus \<open>s \<Turnstile> p\<close>
    using 2 "\<rightarrow>E" by blast
qed

AOT_theorem "modal-clos-facts:4": \<open>ModallyClosed(s) \<rightarrow> \<not>NullSituation(s)\<close>
proof (rule "\<rightarrow>I")
  AOT_assume 1: \<open>ModallyClosed(s)\<close>
  AOT_obtain q\<^sub>1 where \<open>\<box>q\<^sub>1\<close>
    by (metis "\<exists>I"(1) "instantiation" "log-prop-prop:2" RN)
  AOT_hence \<open>s \<Turnstile> q\<^sub>1\<close>
    using "modal-clos-facts:3" 1
    by (meson "con-dis-i-e:1" "vdash-properties:10")
  AOT_thus \<open>\<not>NullSituation(s)\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:b" "df-null-trivial:1"
          "existential:2[const_var]" "raa-cor:3" by blast
qed

AOT_theorem "world-closed:1": \<open>ModallyClosed(w)\<close>
proof -
  AOT_modally_strict {
    AOT_have A: \<open>(Actual(s) \<rightarrow> q) \<rightarrow> (\<forall>p(s \<Turnstile> p \<equiv> p) \<rightarrow> s \<Turnstile> q)\<close> for s q
    proof(safe intro!: "\<rightarrow>I")
      AOT_assume \<theta>: \<open>Actual(s) \<rightarrow> q\<close>
      AOT_assume \<xi>: \<open>\<forall>p(s \<Turnstile> p \<equiv> p)\<close>
      AOT_hence \<open>\<forall>p(s \<Turnstile> p \<rightarrow> p)\<close>
        by (metis (no_types, lifting) "deduction-theorem" "intro-elim:3:a"
                                      "rule-ui:2[const_var]" "universal-cor")
      AOT_hence \<open>Actual(s)\<close>
        using "\<equiv>\<^sub>d\<^sub>fI" "con-dis-i-e:1" Situation.restricted_var_condition actual by blast
      AOT_hence \<open>q\<close>
        using \<theta> "\<rightarrow>E" by blast
      AOT_thus \<open>s \<Turnstile> q\<close>
        using \<xi>  "intro-elim:3:b" "rule-ui:3" by blast
    qed
  }
  AOT_hence B: \<open>\<box>(Actual(s) \<rightarrow> q) \<rightarrow> \<box>(\<forall>p(s \<Turnstile> p \<equiv> p) \<rightarrow> s \<Turnstile> q)\<close> for s q
    by (rule RM)

  (* C: *)
  AOT_have C: \<open>PossibleWorld(w)\<close>
    by (simp add: PossibleWorld.restricted_var_condition)
  AOT_hence C2: \<open>\<diamond>\<forall>p(w \<Turnstile> p \<equiv> p)\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:b" "world:1" by blast

  (* D: *)
  {
    fix q
    AOT_assume 1: \<open>Actual(w) \<Rightarrow> q\<close>

    (* E: *)
    AOT_have 2: \<open>\<box>(Actual(w) \<rightarrow> q)\<close>
      using 1 "\<equiv>\<^sub>d\<^sub>fE" "nec-impl-p:1" by blast

    AOT_have 3: \<open>Situation(w)\<close>
      using "&E"(1) "rule-eq-df:2" "world-pos" pos by blast

    AOT_have \<open>\<box>(\<forall>p (w \<Turnstile> p \<equiv> p) \<rightarrow> w \<Turnstile> q)\<close>
      using B[unconstrain s, THEN "\<rightarrow>E", OF 3, THEN "\<rightarrow>E", OF 2].

    (* F: *)
    AOT_hence \<open>\<diamond>w \<Turnstile> q\<close>
      using C "T\<diamond>" "\<rightarrow>E" C2 "K\<diamond>" by blast

    (* G: *)
    AOT_hence \<open>w \<Turnstile> q\<close>
      using "intro-elim:3:a" "rigid-truth-at:2" by blast
  }
  AOT_hence \<open>\<forall>p((Actual(w) \<Rightarrow> p) \<rightarrow> w \<Turnstile> p)\<close>
    by (simp add: "deduction-theorem" "universal-cor")
  AOT_hence \<open>Situation(w) & \<forall>p (Actual(w) \<Rightarrow> p \<rightarrow> w \<Turnstile> p)\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:1" "con-dis-i-e:2:a" "world:1" C by blast
  AOT_thus \<open>ModallyClosed(w)\<close>
    by (safe intro!: "\<equiv>\<^sub>d\<^sub>fI"[OF "sit-clo"])
qed

(* TODO: world-closed:2 *)

AOT_theorem "world-closed:3":\<open>PossibleWorld(s) \<equiv> Maximal(s) & Consistent(s) & ModallyClosed(s)\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>PossibleWorld(s)\<close>
  AOT_thus \<open>Maximal(s) & Consistent(s) & ModallyClosed(s)\<close>
    by (simp add: "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "world-closed:1.unconstrain_w.\<forall>E(1).\<rightarrow>E"
                  "world-cons:1.unconstrain_w.\<forall>E(1).\<rightarrow>E" "world:3.\<rightarrow>E"
                  "world=maxpos:2.unvarify_x.\<forall>E(1).\<equiv>E(1).&E(1)")
next
  AOT_assume 1: \<open>Maximal(s) & Consistent(s) & ModallyClosed(s)\<close>
  AOT_hence \<open>Possible(s)\<close>
    by (meson "con-dis-i-e:1" "con-dis-i-e:2:a" "con-dis-i-e:2:b"
              "modal-clos-facts:2" "vdash-properties:10")
  AOT_thus \<open>PossibleWorld(s)\<close>
    using "1" "con-dis-i-e:2:a" "df-simplify:1" "intro-elim:3:b" "world=maxpos:2" by blast
qed

AOT_find_theorems "Possible(\<kappa>)"

AOT_define p_ext :: \<open>\<tau> \<Rightarrow> \<phi> \<Rightarrow> \<tau>\<close> ("_\<^sup>+_")
  "p-ext": \<open>s\<^sup>+p =\<^sub>d\<^sub>f \<^bold>\<iota>s' \<forall>q(s' \<Turnstile> q \<equiv> (s \<Turnstile> q \<or> q = p))\<close>

AOT_theorem "pext-lem:1": \<open>\<forall>q((s \<Turnstile> q \<or> q = p) \<rightarrow> \<box>(s \<Turnstile> q \<or> q = p))\<close>
proof(safe intro!: GEN "\<rightarrow>I")
  fix q
  AOT_assume \<open>s \<Turnstile> q \<or> q = p\<close>
  moreover AOT_have \<open>s \<Turnstile> q \<rightarrow> \<box>s \<Turnstile> q\<close>
    using "deduction-theorem" "intro-elim:3:a" "lem2:1" by blast
  moreover AOT_have \<open>q = p \<rightarrow> \<box>q = p\<close>
    using "id-nec:1" by blast
  ultimately AOT_show \<open>\<box>(s \<Turnstile> q \<or> q = p)\<close>
    by (metis "KBasic:15" "\<or>E"(2) "\<or>I"(1) "\<or>I"(2) "vdash-properties:10" RAA(1))
qed

AOT_theorem "pext-lem:2": \<open>(s\<^sup>+p \<Turnstile> q) \<equiv> (s \<Turnstile> q \<or> q = p)\<close>
proof -
  AOT_have 1: \<open>\<^bold>\<iota>s' \<forall>q(s' \<Turnstile> q \<equiv> (s \<Turnstile> q \<or> q = p))\<down>\<close>
    using "sit-comp-simp:3".
  AOT_hence 2: \<open>s\<^sup>+p = \<^bold>\<iota>s' \<forall>q(s' \<Turnstile> q \<equiv> (s \<Turnstile> q \<or> q = p))\<close>
    using "p-ext" "rule-id-df:1"[OF "p-ext", of _ "(_,_)", simplified]
    by blast
  then AOT_obtain y where y_id: \<open>y = s\<^sup>+p\<close>
    using "1" "existential:1" "instantiation" id_sym by blast
  AOT_hence 3: \<open>y = \<^bold>\<iota>s' \<forall>q(s' \<Turnstile> q \<equiv> (s \<Turnstile> q \<or> q = p))\<close>
    using 2 "rule=E" by blast

  AOT_have \<open>\<forall>q (y \<Turnstile> q \<equiv> s \<Turnstile> q \<or> q = p)\<close>
  proof(safe intro!: "sit-comp-simp:4"[THEN "\<rightarrow>E"] 3 "strict-can:1[I]")
    AOT_modally_strict {
      AOT_show \<open>\<forall>q(s \<Turnstile> q \<or> q = p \<rightarrow> \<box>(s \<Turnstile> q \<or> q = p))\<close>
      proof(safe intro!: GEN "\<rightarrow>I")
        fix q
        AOT_assume \<open>s \<Turnstile> q \<or> q = p\<close>
        moreover AOT_have \<open>s \<Turnstile> q \<rightarrow> \<box>s \<Turnstile> q\<close>
          using "deduction-theorem" "intro-elim:3:a" "lem2:1" by blast
        moreover AOT_have \<open>q = p \<rightarrow> \<box>q = p\<close>
          using "id-nec:1" by blast
        ultimately AOT_show \<open>\<box>(s \<Turnstile> q \<or> q = p)\<close>
          by (metis "KBasic:15" "con-dis-i-e:3:a" "con-dis-i-e:3:b"
                    "con-dis-i-e:4:a" "deduction-theorem")
      qed
    }
  qed
  AOT_hence \<open>y \<Turnstile> q \<equiv> s \<Turnstile> q \<or> q = p\<close>
    using "\<forall>E" by blast
  AOT_thus \<open>s\<^sup>+p \<Turnstile> q \<equiv> s \<Turnstile> q \<or> q = p\<close>
    using y_id "rule=E" by fast
qed

AOT_theorem "pext-lem:3": \<open>s \<Turnstile> q \<rightarrow> s\<^sup>+p \<Turnstile> q\<close>
  by (metis "con-dis-i-e:3:a" "deduction-theorem" "intro-elim:3:b" "pext-lem:2")

AOT_theorem "pext-lem:4": \<open>s\<^sup>+p \<Turnstile> p\<close>
  using "con-dis-i-e:3:b" "intro-elim:3:b" "pext-lem:2" "rule=I:2[const_var]" by blast

AOT_theorem pext_denotes: \<open>s\<^sup>+p\<down>\<close>
  using "pext-lem:4" "situations:3.\<rightarrow>E" "true-in-s.\<equiv>\<^sub>d\<^sub>fE.&E(1)" by blast

AOT_theorem pext_situation: \<open>Situation(s\<^sup>+p)\<close>
  using "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:a" "pext-lem:4" "true-in-s" by blast
                            
(* TODO: put into correct position *)
AOT_theorem "oth-class-taut:8:j":
  \<open>((\<phi> \<or> \<psi>) \<rightarrow> \<chi>) \<equiv> ((\<phi> \<rightarrow> \<chi>) & (\<psi> \<rightarrow> \<chi>))\<close>
  by (metis "con-dis-i-e:1" "con-dis-i-e:2:a" "con-dis-i-e:2:b" "con-dis-i-e:3:a"
            "con-dis-i-e:3:b" "con-dis-i-e:4:c" "deduction-theorem" "intro-elim:2"
            "reductio-aa:1" "vdash-properties:10")

(* TODO: put into correct position *)
AOT_theorem "term-out:5": \<open>\<forall>\<alpha>(\<alpha> = \<beta> \<rightarrow> \<phi>{\<alpha>}) \<equiv> \<phi>{\<beta>}\<close>
  by (metis (no_types, lifting) "\<forall>E"(4) "\<rightarrow>E" "deduction-theorem" "id-eq:1"
                                "intro-elim:2" "rule=E" GEN id_sym)

AOT_theorem "poss-sit-part-w:2": \<open>s\<^sup>+p \<unlhd> w \<equiv> s \<unlhd> w & w \<Turnstile> p\<close>
proof -
  AOT_have 1: \<open>s\<^sup>+p \<unlhd> w \<equiv> (Situation(s\<^sup>+p) & Situation(w) & \<forall>q(s\<^sup>+p \<Turnstile> q \<rightarrow> w \<Turnstile> q))\<close>
    using "sit-part-whole"[THEN "\<equiv>Df"].
  also AOT_have \<open>... \<equiv> \<forall>q(s\<^sup>+p \<Turnstile> q \<rightarrow> w \<Turnstile> q)\<close>
    by (meson "&E"(1) "\<equiv>S"(1) "intro-elim:3:b" "oth-class-taut:3:a"
              "rule-eq-df:2" "world-pos" pos pext_situation)
  also AOT_have \<open>... \<equiv> \<forall>q((s \<Turnstile> q \<or> q = p) \<rightarrow> w \<Turnstile> q)\<close>
    by (simp add: "pext-lem:2" "rule-sub-lem:1:b" "rule-sub-lem:1:d" RN)
  also AOT_have \<open>... \<equiv> \<forall>q((s \<Turnstile> q \<rightarrow> w \<Turnstile> q) & (q = p \<rightarrow> w \<Turnstile> q))\<close>
    using "oth-class-taut:8:j"
    by (simp add: "rule-sub-lem:1:d" RN)
  also AOT_have \<open>... \<equiv> \<forall>q(s \<Turnstile> q \<rightarrow> w \<Turnstile> q) & \<forall>q(q = p \<rightarrow> w \<Turnstile> q)\<close>
    using "cqt-basic:4" by fast
  also AOT_have \<open>... \<equiv> \<forall>q(s \<Turnstile> q \<rightarrow> w \<Turnstile> q) & w \<Turnstile> p\<close>
    apply (AOT_subst \<open>\<forall>q (q = p \<rightarrow> w \<Turnstile> q)\<close> \<open>w \<Turnstile> p\<close>)
    using "term-out:5" apply blast
    using "oth-class-taut:3:a" by blast
  also AOT_have \<open>... \<equiv> (Situation(s) & Situation(w) & \<forall>q(s \<Turnstile> q \<rightarrow> w \<Turnstile> q)) & w \<Turnstile> p\<close>
    by (metis (no_types, lifting) 1 "con-dis-i-e:1" "con-dis-i-e:2:a" "con-dis-i-e:2:b"
                                  "deduction-theorem" "intro-elim:2" "intro-elim:3:a"
                                  "intro-elim:3:b" Situation.restricted_var_condition
                                  calculation)
  also AOT_have \<open>... \<equiv> s \<unlhd> w & w \<Turnstile> p\<close>
    apply (AOT_subst \<open>Situation(s) & Situation(w) & \<forall>q (s \<Turnstile> q \<rightarrow> w \<Turnstile> q)\<close> \<open>s \<unlhd> w\<close>)
    using "sit-part-whole"[THEN "\<equiv>Df", symmetric] apply simp
    by (simp add: "oth-class-taut:3:a")
  finally AOT_show \<open>s\<^sup>+p \<unlhd> w \<equiv> s \<unlhd> w & w \<Turnstile> p\<close>.
qed

AOT_theorem aux: \<open>w \<Turnstile> s \<Turnstile> p \<equiv> s \<Turnstile> p\<close>
  using "fund:2"[unvarify p, OF "log-prop-prop:2"] "fund:1"[unvarify p, OF "log-prop-prop:2"]
  by (metis "PossibleWorld.\<forall>E" "\<rightarrow>I" "\<equiv>I" "\<equiv>E"(1,2) "lem2:1" "lem2:3" "PossibleWorld.\<exists>I")

AOT_theorem aux2: \<open>w \<Turnstile> Actual(s) \<equiv> s \<unlhd> w\<close>
proof -
  AOT_have \<open>w \<Turnstile> (Actual(s) \<equiv> (Situation(s) & \<forall>p (s \<Turnstile> p \<rightarrow> p)))\<close>
    by (simp add: "\<equiv>Df" "fund:2.unvarify_p.\<forall>E(1).\<equiv>E(1).\<forall>E(1).\<rightarrow>E" "log-prop-prop:2"
                  "world:3.\<rightarrow>E" PossibleWorld.restricted_var_condition RN actual)
  AOT_hence \<open>w \<Turnstile> Actual(s) \<equiv> w \<Turnstile> (Situation(s) & \<forall>p (s \<Turnstile> p \<rightarrow> p))\<close>
    using "conj-dist-w:4"[unvarify p, OF "log-prop-prop:2", unvarify q, OF "log-prop-prop:2"]
    using "intro-elim:3:a" by blast
  also AOT_have \<open>... \<equiv> (w \<Turnstile> Situation(s) & w \<Turnstile> \<forall>p (s \<Turnstile> p \<rightarrow> p))\<close>
    using "conj-dist-w:1"[unvarify p, OF "log-prop-prop:2", unvarify q, OF "log-prop-prop:2"].
  also AOT_have \<open>... \<equiv> w \<Turnstile> \<forall>p (s \<Turnstile> p \<rightarrow> p)\<close>
    by (meson "fund:2.unvarify_p.\<forall>E(1).\<equiv>E(1).\<forall>E(1).\<rightarrow>E" "log-prop-prop:2" "oth-class-taut:3:a"
              "oth-class-taut:8:i.\<rightarrow>E.\<rightarrow>E" "world:3.\<rightarrow>E" PossibleWorld.restricted_var_condition
              RN Situation.restricted_var_condition)
  also AOT_have \<open>... \<equiv> \<forall>p w \<Turnstile> (s \<Turnstile> p \<rightarrow> p)\<close>
    by (simp add: "conj-dist-w:5")
  also AOT_have \<open>... \<equiv> \<forall>p (w \<Turnstile> s \<Turnstile> p \<rightarrow> w \<Turnstile> p)\<close>
    using "conj-dist-w:2"[unvarify p, OF "log-prop-prop:2"]
    by (simp add: "rule-sub-lem:1:d" RN)
  also AOT_have \<open>... \<equiv> \<forall>p (s \<Turnstile> p \<rightarrow> w \<Turnstile> p)\<close>
    using aux by (simp add: "rule-sub-lem:1:b" "rule-sub-lem:1:d" RN)
  also AOT_have \<open>... \<equiv> s \<unlhd> w\<close>
    by (AOT_subst_def "sit-part-whole")
       (simp add: "con-dis-taut:2" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "deduction-theorem"
                  "intro-elim:2" "sit-clo.\<equiv>\<^sub>d\<^sub>fE.&E(1)" "world-closed:1" Situation.\<psi>)
  finally show ?thesis.
qed

AOT_theorem "poss-sit-part-w:3[newproof]": \<open>\<forall>w(s \<unlhd> w \<rightarrow> w \<Turnstile> p) \<equiv> (Actual(s) \<Rightarrow> p)\<close>
proof -
  AOT_have \<open>Actual(s) \<Rightarrow> p \<equiv> \<box>(Actual(s) \<rightarrow> p)\<close>
    by (simp add: "nec-impl-p:1" "rule-eq-df:1")
  also AOT_have \<open>\<dots> \<equiv> \<forall>w(w \<Turnstile> (Actual(s) \<rightarrow> p))\<close>
    using "fund:2"[unvarify p, OF "log-prop-prop:2"]
    by blast
  also AOT_have \<open>\<dots> \<equiv> \<forall>w(w \<Turnstile> Actual(s) \<rightarrow> w \<Turnstile> p)\<close>
    apply (safe intro!: "rule-sub-lem:1:d" RN)
    using "conj-dist-w:2"[unvarify p, OF "log-prop-prop:2", unconstrain w]
    by (metis "deduction-theorem" "intro-elim:2" "oth-class-taut:4:d" "vdash-properties:10")
  also AOT_have \<open>... \<equiv> \<forall>w(s \<unlhd> w \<rightarrow> w \<Turnstile> p)\<close>
    apply (safe intro!: "rule-sub-lem:1:d" RN)
    using aux2[unconstrain w]
    by (metis "deduction-theorem" "intro-elim:2" "intro-elim:3:a" "intro-elim:3:b")
  finally show ?thesis
    using "intro-elim:3:f" "oth-class-taut:3:a" by blast
qed

AOT_theorem tmp2: \<open>(\<chi> \<rightarrow> (\<phi> \<equiv> \<psi>)) \<rightarrow> ((\<chi> & \<phi>) \<equiv> (\<chi> & \<psi>))\<close>
  by (metis "\<equiv>E"(1) "\<equiv>E"(2) "con-dis-i-e:1" "con-dis-i-e:2:a" "con-dis-i-e:2:b" "intro-elim:2" CP)

AOT_theorem tmp3: \<open>s\<^sup>+p\<down>\<close>
  using "Situation.res-var:3" "vdash-properties:10" pext_situation by blast

AOT_theorem tmp4: \<open>s \<unlhd> w \<equiv> \<box>s \<unlhd> w\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>s \<unlhd> w\<close>
  AOT_hence \<open>\<forall>p (s \<Turnstile> p \<rightarrow> w \<Turnstile> p)\<close>
    using "sit-part-whole"
    using "\<equiv>\<^sub>d\<^sub>fE" "&E" by blast
  AOT_hence 1: \<open>w \<Turnstile> p\<close> if \<open>s \<Turnstile> p\<close> for p
    using "rule-ui:3" "vdash-properties:10" that by blast
  AOT_have \<open>\<box>(s \<Turnstile> p \<rightarrow> w \<Turnstile> p)\<close> for p
    apply (rule "sc-eq-box-box:6"[THEN "\<rightarrow>E", THEN "\<rightarrow>E"])
    using "if-p-then-p" "lem2:1" "rule-sub-remark:6[1]" RN apply blast
    using "1" "deduction-theorem" "intro-elim:3:a" "rigid-truth-at:1" by blast
  AOT_hence \<open>\<box>\<forall>p (s \<Turnstile> p \<rightarrow> w \<Turnstile> p)\<close>
    by (metis (full_types) "BFs:1" "universal-cor" "vdash-properties:10")
  moreover AOT_have \<open>\<box>Situation(s)\<close>
    by (simp add: RN Situation.restricted_var_condition)
  moreover AOT_have \<open>\<box>Situation(w)\<close>
    using "&E"(1) "intro-elim:3:a" "possit-sit:1" "rule-eq-df:2" "world-pos" pos by blast
  ultimately AOT_show \<open>\<box>s \<unlhd> w\<close>
    apply (AOT_subst_def "sit-part-whole")
    by (meson "KBasic:3" "df-simplify:2" "intro-elim:3:b")
next
  AOT_assume \<open>\<box>s \<unlhd> w\<close>
  AOT_thus \<open>s \<unlhd> w\<close>
    using "qml:2"[axiom_inst] "\<rightarrow>E" by blast
qed

AOT_theorem "poss-sit-part-w:3": \<open>\<forall>w(s \<unlhd> w \<rightarrow> w \<Turnstile> p) \<equiv> (Actual(s) \<Rightarrow> p)\<close>
proof -
  AOT_have \<open>\<forall>w(s \<unlhd> w \<rightarrow> w \<Turnstile> p) \<equiv> \<forall>w \<not>(s \<unlhd> w & \<not>w \<Turnstile> p)\<close>
    by (simp add: "oth-class-taut:1:a" "rule-sub-lem:1:c" "rule-sub-lem:1:d" RN)
  also AOT_have \<open>... \<equiv> \<forall>w \<not>(s \<unlhd> w & w \<Turnstile> \<not>p)\<close>
  proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
    AOT_assume \<open>\<forall>w \<not>(s \<unlhd> w & \<not>w \<Turnstile> p)\<close>
    AOT_hence \<open>\<not>(s \<unlhd> w & \<not>w \<Turnstile> p)\<close> for w
      using "rule-ui:3" "vdash-properties:10" PossibleWorld.restricted_var_condition by blast
    AOT_hence \<open>\<not>(s \<unlhd> w & w \<Turnstile> \<not>p)\<close> for w
      by (metis "&E"(2) "coherent:1" "con-dis-i-e:1" "con-dis-i-e:2:a"
                "intro-elim:3:a" "reductio-aa:1")
    AOT_thus \<open>\<forall>w \<not>(s \<unlhd> w & w \<Turnstile> \<not>p)\<close>
      using "PossibleWorld.\<forall>I" by presburger
  next
    AOT_assume \<open>\<forall>w \<not>(s \<unlhd> w & w \<Turnstile> \<not>p)\<close>
    AOT_hence \<open>\<not>(s \<unlhd> w & w \<Turnstile> \<not>p)\<close> for w
      using "PossibleWorld.rule-ui" by fastforce
    AOT_hence \<open>\<not>(s \<unlhd> w & \<not>w \<Turnstile> p)\<close> for w
      by (metis "coherent:1" "con-dis-i-e:1" "con-dis-i-e:2:a" "con-dis-i-e:2:b"
                "intro-elim:3:b" "reductio-aa:1")
    AOT_thus \<open>\<forall>w \<not>(s \<unlhd> w & \<not>w \<Turnstile> p)\<close>
      using "PossibleWorld.\<forall>I" by presburger
  qed
  also AOT_have \<open>... \<equiv> \<not>\<exists>w(s \<unlhd> w & w \<Turnstile> \<not>p)\<close>
    by (metis (no_types, lifting) "con-dis-i-e:1" "con-dis-i-e:2:a" "con-dis-i-e:2:b"
                                  "deduction-theorem" "existential:2[const_var]"
                                  "instantiation" "intro-elim:2" "reductio-aa:1"
                                  "rule-ui:3" "universal-cor" "vdash-properties:10")
  also AOT_have \<open>... \<equiv> \<not>\<exists>w(s\<^sup>+(\<not>p) \<unlhd> w)\<close>
    apply (AOT_subst \<open>PossibleWorld(w) & (s \<unlhd> w & w \<Turnstile> (\<not>p))\<close>
                     \<open>PossibleWorld(w) & (s\<^sup>+(\<not>p) \<unlhd> w)\<close> for: w)
     apply (rule tmp2[THEN "\<rightarrow>E"])
     apply (rule "PossibleWorld.\<forall>I"[THEN "\<forall>E"(2)])
    using "poss-sit-part-w:2"[unvarify p, OF "log-prop-prop:2", symmetric]
     apply force
    using "oth-class-taut:3:a" by auto
  also AOT_have \<open>... \<equiv> \<not>Possible(s\<^sup>+(\<not>p))\<close>
    using "poss-sit-part-w:1"[unconstrain s, unvarify \<beta>, OF tmp3, THEN "\<rightarrow>E",
                              OF pext_situation, symmetric, unvarify p, OF "log-prop-prop:2"]
    by (simp add: "rule-sub-lem:1:a" RN)
  also AOT_have \<open>... \<equiv> \<not>\<diamond>Actual(s\<^sup>+(\<not>p))\<close>
    apply (AOT_subst_def pos)
    apply (rule "oth-class-taut:4:b"[THEN "\<equiv>E"(1)])
    using pext_situation[unvarify p, OF "log-prop-prop:2"]
    using "df-simplify:1" "oth-class-taut:3:a" by blast
  also AOT_have \<open>... \<equiv> \<not>\<diamond>\<forall>q(s\<^sup>+(\<not>p) \<Turnstile> q \<rightarrow> q)\<close>
    apply (AOT_subst_def actual)
    apply (rule "oth-class-taut:4:b"[THEN "\<equiv>E"(1)])
    using pext_situation[unvarify p, OF "log-prop-prop:2"]
    by (simp add: "RE\<diamond>" "con-dis-i-e:1" "con-dis-taut:2" "deduction-theorem" "intro-elim:2")
  also AOT_have \<open>... \<equiv> \<not>\<diamond>\<forall>q((s \<Turnstile> q \<or> q = (\<not>p)) \<rightarrow> q)\<close>
    apply (AOT_subst \<open>s\<^sup>+(\<not>p) \<Turnstile> q\<close> \<open>s \<Turnstile> q \<or> q = (\<not>p)\<close> for: q)
    using "pext-lem:2"[unvarify p, OF "log-prop-prop:2"]
    using "oth-class-taut:3:a" by auto
  also AOT_have \<open>... \<equiv> \<not>\<diamond>\<forall>q((s \<Turnstile> q \<rightarrow> q) & (q = (\<not>p) \<rightarrow> q))\<close>
    by (meson "RE\<diamond>" "intro-elim:3:a" "oth-class-taut:4:b" "oth-class-taut:8:j"
              "rule-sub-lem:1:d" RN)
  also AOT_have \<open>... \<equiv> \<not>\<diamond>(\<forall>q(s \<Turnstile> q \<rightarrow> q) & \<forall>q(q = (\<not>p) \<rightarrow> q))\<close>
    apply (AOT_subst \<open>\<forall>q ((s \<Turnstile> q \<rightarrow> q) & (q = (\<not>p) \<rightarrow> q))\<close> \<open>\<forall>q(s \<Turnstile> q \<rightarrow> q) & \<forall>q(q = (\<not>p) \<rightarrow> q)\<close>)
     apply (simp add: "cqt-basic:4")
    by (simp add: "oth-class-taut:3:a")
  also AOT_have \<open>... \<equiv> \<not>\<diamond>(\<forall>q(s \<Turnstile> q \<rightarrow> q) & \<not>p)\<close>
    apply (AOT_subst \<open>\<forall>q(q = (\<not>p) \<rightarrow> q)\<close>  \<open>\<not>p\<close>)
    using "term-out:5"[unvarify \<beta>, OF "log-prop-prop:2"]
    apply meson
    by (simp add: "oth-class-taut:3:a")
  also AOT_have \<open>... \<equiv> \<not>\<diamond>(Actual(s) & \<not>p)\<close>
    apply (AOT_subst_def actual)
    apply (AOT_subst \<open>Situation(s) & \<forall>p (s \<Turnstile> p \<rightarrow> p) & \<not>p\<close> \<open>\<forall>p (s \<Turnstile> p \<rightarrow> p) & \<not>p\<close>)
     apply (metis (no_types, lifting) "con-dis-i-e:1" "con-dis-i-e:2:a" "con-dis-i-e:2:b"
            "deduction-theorem" "intro-elim:2" Situation.restricted_var_condition)
    using "oth-class-taut:3:a" by auto
  also AOT_have \<open>... \<equiv> \<box>\<not>(Actual(s) & \<not>p)\<close>
    using "KBasic2:1" "intro-elim:3:f" "oth-class-taut:3:a" by blast
  also AOT_have \<open>... \<equiv> \<box>(Actual(s) \<rightarrow> p)\<close>
    using "Commutativity of \<equiv>" "RM:3" "intro-elim:3:a" "oth-class-taut:1:a" by blast
  also AOT_have \<open>... \<equiv> Actual(s) \<Rightarrow> p\<close>
    using "intro-elim:3:f" "nec-impl-p:1" "oth-class-taut:3:a" "rule-eq-df:1" by blast
  finally show ?thesis.
qed

AOT_define s_star :: \<open>\<tau> \<Rightarrow> \<tau>\<close> (\<open>_\<^sup>\<star>\<close>)
  "poss-sit-part-w:4": \<open>s\<^sup>\<star> =\<^sub>d\<^sub>f \<^bold>\<iota>s' \<forall>p(s' \<Turnstile> p \<equiv> (Actual(s) \<Rightarrow> p))\<close>



AOT_theorem "poss-sit-part-w:5": \<open>\<forall>p(s\<^sup>\<star> \<Turnstile> p \<equiv> (Actual(s) \<Rightarrow> p))\<close>
proof -
  AOT_have 0: \<open>s\<^sup>\<star> = \<^bold>\<iota>s' \<forall>p(s' \<Turnstile> p \<equiv> (Actual(s) \<Rightarrow> p))\<close>
    using "rule-id-df:1"[OF "poss-sit-part-w:4", OF "sit-comp-simp:3"]
    by blast
  AOT_obtain y where 1: \<open>y = \<^bold>\<iota>s' \<forall>p(s' \<Turnstile> p \<equiv> (Actual(s) \<Rightarrow> p))\<close>
    using "free-thms:3[const_var].unvarify_\<alpha>.\<forall>E(1).\<exists>E'" "sit-comp-simp:3" by blast
  AOT_have \<open>\<forall>p(y \<Turnstile> p \<equiv> (Actual(s) \<Rightarrow> p))\<close>
  proof(safe intro!: "sit-comp-simp:4"[THEN "\<rightarrow>E"] "strict-can:1[I]")
    AOT_modally_strict {
      AOT_show \<open>\<forall>p (Actual(s) \<Rightarrow> p \<rightarrow> \<box>(Actual(s) \<Rightarrow> p))\<close>
      proof(safe intro!: GEN "\<rightarrow>I")
        fix p
        AOT_assume \<open>Actual(s) \<Rightarrow> p\<close>
        AOT_hence \<open>\<box>(Actual(s) \<rightarrow> p)\<close>
          using "\<equiv>\<^sub>d\<^sub>fE" "nec-impl-p:1" by blast
        AOT_hence \<open>\<box>\<box>(Actual(s) \<rightarrow> p)\<close>
          using "S5Basic:5" "vdash-properties:10" by blast
        AOT_thus \<open>\<box>(Actual(s) \<Rightarrow> p)\<close>
          using "RM:3" "intro-elim:3:b" "nec-impl-p:1" "rule-eq-df:1" by blast
      qed
    }
  next
    AOT_show \<open>y = \<^bold>\<iota>s' \<forall>p(s' \<Turnstile> p \<equiv> (Actual(s) \<Rightarrow> p))\<close>
      using 1 by auto
  qed
  AOT_thus \<open>\<forall>p(s\<^sup>\<star> \<Turnstile> p \<equiv> (Actual(s) \<Rightarrow> p))\<close>
    using 0 1
    using "rule=E" id_sym by meson
qed

AOT_theorem aux4: \<open>Situation(s\<^sup>\<star>)\<close>
proof -
  AOT_have \<open>Situation(\<^bold>\<iota>s'(\<forall>p (s' \<Turnstile> p \<equiv> Actual(s) \<Rightarrow> p)))\<close>
    using "actual-desc:4"[THEN "\<rightarrow>E", OF "sit-comp-simp:3",
        THEN "Act-Basic:2"[THEN "\<equiv>E"(1)], THEN "&E"(1)]
        "possit-sit:4"[unvarify x, THEN "\<equiv>E"(1)]
    using "sit-comp-simp:3" by blast
  thus ?thesis
    using "sit-comp-simp:3" "=\<^sub>d\<^sub>fI"(1)[OF "poss-sit-part-w:4", OF "sit-comp-simp:3"]
    by simp
qed

AOT_theorem "poss-sit-part-w:6": \<open>s \<unlhd> s\<^sup>\<star>\<close>
proof(safe intro!: "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I")
  AOT_show \<open>Situation(s)\<close>
    using "Situation.\<psi>" by blast
next
  AOT_show \<open>Situation(s\<^sup>\<star>)\<close>
    using aux4 by blast
next
  AOT_show \<open>\<forall>p(s \<Turnstile> p \<rightarrow> s\<^sup>\<star> \<Turnstile> p)\<close>
  proof(safe intro!: GEN "\<rightarrow>I")
    fix p
    AOT_assume 1: \<open>s \<Turnstile> p\<close>
    AOT_have \<open>\<box>(Actual(s) \<rightarrow> p)\<close>
    proof (rule RM[THEN "\<rightarrow>E"])
        AOT_modally_strict {
          AOT_show \<open>(s \<Turnstile> p) \<rightarrow> (Actual(s) \<rightarrow> p)\<close>
            by (meson "actual.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E" "log-prop-prop:2" CP)
        }
      next
        AOT_show \<open>\<box>s \<Turnstile> p\<close> using 1 "intro-elim:3:a" "lem2:1" by blast
    qed
    AOT_hence \<open>Actual(s) \<Rightarrow> p\<close>
      using "\<equiv>\<^sub>d\<^sub>fI" "nec-impl-p:1" by blast
    AOT_thus \<open>s\<^sup>\<star> \<Turnstile> p\<close>
      using "intro-elim:3:b" "poss-sit-part-w:5" "rule-ui:3" by blast
  qed
qed

(* 549; pdf page 416; numbered page 566 *)
AOT_theorem "poss-sit-part-w:7": \<open>s \<unlhd> w \<equiv> s\<^sup>\<star> \<unlhd> w\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume 1: \<open>s \<unlhd> w\<close>
  AOT_show \<open>s\<^sup>\<star> \<unlhd> w\<close>
  proof(rule "RAA")
    AOT_assume \<open>\<not>s\<^sup>\<star> \<unlhd> w\<close>
    AOT_hence \<open>\<not>(Situation(s\<^sup>\<star>) & Situation(w) & \<forall>p (s\<^sup>\<star> \<Turnstile> p \<rightarrow> w \<Turnstile> p))\<close>
      by (AOT_subst_def (reverse) "sit-part-whole")
    AOT_hence \<open>\<not>(\<forall>p (s\<^sup>\<star> \<Turnstile> p \<rightarrow> w \<Turnstile> p))\<close>
      by (metis "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "raa-cor:2" "sit-clo.\<equiv>\<^sub>d\<^sub>fE.&E(1)" "world-closed:1" aux4)
    AOT_hence \<open>\<exists>p \<not>(s\<^sup>\<star> \<Turnstile> p \<rightarrow> w \<Turnstile> p)\<close>
      by (metis "cqt-further:2.\<rightarrow>E.\<exists>E'" "existential:1" "log-prop-prop:2")
    AOT_hence \<open>\<exists>p (s\<^sup>\<star> \<Turnstile> p & \<not>w \<Turnstile> p)\<close>
      by (metis (no_types, lifting) "con-dis-i-e:1" "deduction-theorem"
          "existential:2[const_var]" "instantiation" "raa-cor:3")
    then AOT_obtain p\<^sub>1 where p\<^sub>1_prop: \<open>s\<^sup>\<star> \<Turnstile> p\<^sub>1 & \<not>w \<Turnstile> p\<^sub>1\<close>
      using "\<exists>E"[rotated] by meson
    AOT_hence 2: \<open>\<not>(w \<Turnstile> p\<^sub>1)\<close>
      using "con-dis-i-e:2:b" by blast
    AOT_have \<open>Actual(s) \<Rightarrow> p\<^sub>1\<close>
      using p\<^sub>1_prop[THEN "&E"(1)] "intro-elim:3:a" "log-prop-prop:2"
            "poss-sit-part-w:5" "rule-ui:1" by blast
    AOT_hence \<open>s \<unlhd> w \<rightarrow> w \<Turnstile> p\<^sub>1\<close>
      using "poss-sit-part-w:3"[THEN "\<equiv>E"(2), THEN "PossibleWorld.\<forall>E"]
      by blast
    AOT_hence 3: \<open>w \<Turnstile> p\<^sub>1\<close>
      using 1 "\<rightarrow>E" by blast
    AOT_show \<open>\<not>\<forall>p(p \<rightarrow> p)\<close>
      using 2 3  "raa-cor:3" by blast
    AOT_show \<open>\<forall>p(p \<rightarrow> p)\<close>
      by (simp add: "if-p-then-p" "universal-cor")
  qed
next
  AOT_assume A: \<open>s\<^sup>\<star> \<unlhd> w\<close>
  AOT_have B: \<open>s \<unlhd> s\<^sup>\<star>\<close>
    using "poss-sit-part-w:6" by blast
  AOT_have 1: \<open>s\<^sup>\<star>\<down>\<close>
    using "Situation.res-var:3" "vdash-properties:10" aux4 by blast
  AOT_have 2: \<open>Situation(w)\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:a" "world-pos" pos by blast
  AOT_show \<open>s \<unlhd> w\<close>
    using "part:3"[unconstrain s', unconstrain s'', THEN "\<rightarrow>E",
                   OF 2, unvarify \<beta>, OF 1, THEN "\<rightarrow>E", OF aux4]
    using A B
    by (meson "con-dis-i-e:1" "vdash-properties:10")
qed

AOT_theorem "poss-sit-part-w:8": \<open>Possible(s) \<equiv> Possible(s\<^sup>\<star>)\<close>
proof -
  AOT_have \<open>Possible(s) \<equiv> \<exists>w(s \<unlhd> w)\<close>
    using "poss-sit-part-w:1" by auto
  also AOT_have \<open>\<exists>w(s \<unlhd> w) \<equiv> \<exists>w(s\<^sup>\<star> \<unlhd> w)\<close>
    by (metis "deduction-theorem" "intro-elim:2" "intro-elim:3:a" "intro-elim:3:b"
              "poss-sit-part-w:7" PossibleWorld.existential PossibleWorld.instantiation)
  also AOT_have \<open>\<exists>w(s\<^sup>\<star> \<unlhd> w) \<equiv> Possible(s\<^sup>\<star>)\<close>
    using "poss-sit-part-w:1"[unconstrain s, unvarify \<beta>, THEN "\<rightarrow>E", symmetric]
    using "Situation.res-var:3" "vdash-properties:10" aux4 by blast
  finally show ?thesis.
  thm "poss-sit-part-w:1"
qed

AOT_theorem aux5: \<open>Situation(s\<^sup>+\<phi>)\<close>
  using pext_situation[unvarify p, OF "log-prop-prop:2"] by simp

AOT_theorem "poss-sit-part-w:9": \<open>ModallyClosed(s\<^sup>\<star>)\<close>
proof -
  AOT_have \<open>\<forall>p((Actual(s\<^sup>\<star>) \<Rightarrow> p) \<rightarrow> s\<^sup>\<star> \<Turnstile> p)\<close>
  proof(safe intro!: GEN "\<rightarrow>I")
    fix p
    AOT_have A: \<open>(Actual(s\<^sup>\<star>) \<Rightarrow> p) \<rightarrow> (Actual(s) \<Rightarrow> p)\<close>
    proof(safe intro!: "\<rightarrow>I")
      AOT_assume Z: \<open>Actual(s\<^sup>\<star>) \<Rightarrow> p\<close>
      AOT_show \<open>Actual(s) \<Rightarrow> p\<close>
      proof(rule RAA)
        AOT_assume \<open>\<not>(Actual(s) \<Rightarrow> p)\<close>
        AOT_hence \<open>\<not>\<box>(Actual(s) \<rightarrow> p)\<close>
          using "\<equiv>\<^sub>d\<^sub>fI" "nec-impl-p:1" "raa-cor:6" by blast
        AOT_hence \<open>\<diamond>\<not>(Actual(s) \<rightarrow> p)\<close>
          using "KBasic:11" "intro-elim:3:a" by blast
        AOT_hence \<open>\<diamond>(Actual(s) & (\<not>p))\<close>
          apply (AOT_subst \<open>Actual(s) & (\<not>p)\<close> \<open>\<not>(Actual(s) \<rightarrow> p)\<close>)
          using "intro-elim:3:f" "oth-class-taut:1:b" "oth-class-taut:3:a" by blast auto
        moreover {
          AOT_have \<open>\<diamond>(Actual(s) & (\<not>p)) \<equiv> \<diamond>(\<forall>q(s \<Turnstile> q \<rightarrow> q) & \<not>p)\<close>
            by (AOT_subst_def actual)
               (smt (verit, del_insts) "RM\<diamond>" "con-dis-i-e:1" "con-dis-i-e:2:a"
                 "con-dis-i-e:2:b" "deduction-theorem" "intro-elim:2"
                 Situation.\<psi>)
          also AOT_have \<open>\<dots> \<equiv> \<diamond>(\<forall>q(s \<Turnstile> q \<rightarrow> q) & \<forall>q(q = (\<not>p) \<rightarrow> q))\<close>
          proof (AOT_subst \<open>\<forall>q (s \<Turnstile> q \<rightarrow> q) & \<not>p\<close> \<open>\<forall>q(s \<Turnstile> q \<rightarrow> q) & \<forall>q(q = (\<not>p) \<rightarrow> q)\<close>)
            AOT_modally_strict {
              AOT_have \<open>\<not>p \<equiv> \<forall>q (q = (\<not>p) \<rightarrow> q)\<close>
                using "term-out:5"[unvarify \<beta>, OF "log-prop-prop:2", symmetric, where \<tau>=\<open>\<guillemotleft>\<not>p\<guillemotright>\<close>]
                by meson
              AOT_thus \<open>\<forall>q (s \<Turnstile> q \<rightarrow> q) & \<not>p \<equiv> \<forall>q (s \<Turnstile> q \<rightarrow> q) & \<forall>q (q = (\<not>p) \<rightarrow> q)\<close>
                using "oth-class-taut:4:f" "vdash-properties:6" by blast
            }
          qed(safe intro!: "\<equiv>I" "\<rightarrow>I")
          also AOT_have \<open>\<dots> \<equiv> \<diamond>\<forall>q((s \<Turnstile> q \<or> q = (\<not>p)) \<rightarrow> q)\<close>
          proof (AOT_subst \<open>\<forall>q (s \<Turnstile> q \<rightarrow> q) & \<forall>q (q = (\<not>p) \<rightarrow> q)\<close> \<open>\<forall>q ((s \<Turnstile> q \<or> q = (\<not>p)) \<rightarrow> q)\<close>)
            AOT_modally_strict {
              AOT_have \<open>(\<forall>q (s \<Turnstile> q \<rightarrow> q) & \<forall>q (q = (\<not>p) \<rightarrow> q)) \<equiv>
                        \<forall>q((s \<Turnstile> q \<rightarrow> q) & (q = (\<not>p) \<rightarrow> q))\<close>
                using "cqt-basic:13" "cqt-basic:4" "intro-elim:3:f" by blast
              also AOT_have \<open>\<dots> \<equiv> \<forall>q ((s \<Turnstile> q \<or> q = (\<not>p)) \<rightarrow> q)\<close>
                by (meson "Commutativity of \<equiv>" "intro-elim:3:a"
                          "oth-class-taut:8:j" "rule-sub-lem:1:d" RN)
              finally AOT_show \<open>(\<forall>q (s \<Turnstile> q \<rightarrow> q) & \<forall>q (q = (\<not>p) \<rightarrow> q)) \<equiv>
                                \<forall>q ((s \<Turnstile> q \<or> q = (\<not>p)) \<rightarrow> q)\<close>
                by blast
            }
          qed(safe intro!: "\<equiv>I" "\<rightarrow>I")
          also AOT_have \<open>\<dots> \<equiv> \<diamond>\<forall>q(s\<^sup>+(\<not>p) \<Turnstile> q \<rightarrow> q)\<close>
            apply (AOT_subst \<open>s \<Turnstile> q \<or> q = (\<not>p)\<close> \<open>s\<^sup>+(\<not>p) \<Turnstile> q\<close> for: q)
            using "pext-lem:2"[unvarify p, OF "log-prop-prop:2"]
            using "intro-elim:3:f" "oth-class-taut:3:a" apply blast
            using "oth-class-taut:3:a" by blast
          also AOT_have \<open>\<dots> \<equiv> \<diamond>Actual(s\<^sup>+(\<not>p))\<close>
            apply (AOT_subst_def actual)
            by (simp add: "RE\<diamond>" "con-dis-taut:2" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E"
                          "deduction-theorem" "intro-elim:2" aux5)
          also AOT_have \<open>\<dots> \<equiv> Possible(s\<^sup>+(\<not>p))\<close>
            apply (AOT_subst_def pos)
            by (simp add: "con-dis-i-e:1" "con-dis-taut:2" "deduction-theorem"
                          "intro-elim:2" aux5)
          also AOT_have \<open>\<dots> \<equiv> \<exists>w(s\<^sup>+(\<not>p) \<unlhd> w)\<close>
            using "poss-sit-part-w:1"[unconstrain s, unvarify \<beta>, THEN "\<rightarrow>E"]
            using "Situation.res-var:3" "vdash-properties:10" aux5 by blast
          also AOT_have \<open>\<dots> \<equiv> \<exists>w(s\<^sup>\<star> \<unlhd> w & \<not>w \<Turnstile> p)\<close>
          proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
            AOT_assume \<open>\<exists>w s\<^sup>+\<not>p \<unlhd> w\<close>
            then AOT_obtain w where \<open>s\<^sup>+\<not>p \<unlhd> w\<close>
              using PossibleWorld.instantiation by blast
            AOT_hence \<open>s \<unlhd> w & w \<Turnstile> (\<not>p)\<close>
              using "poss-sit-part-w:2"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)]
              by blast
            AOT_hence \<open>s\<^sup>\<star> \<unlhd> w & \<not>w \<Turnstile> p\<close>
              by (metis "\<equiv>E"(4) "coherent:1" "con-dis-i-e:1" "con-dis-i-e:2:a" "con-dis-taut:2"
                        "modus-tollens:1" "poss-sit-part-w:7" "reductio-aa:1")
            AOT_thus \<open>\<exists>w(s\<^sup>\<star> \<unlhd> w & \<not>w \<Turnstile> p)\<close>
              using "PossibleWorld.\<exists>I" by simp
          next
            AOT_assume \<open>\<exists>w(s\<^sup>\<star> \<unlhd> w & \<not>w \<Turnstile> p)\<close>
            then AOT_obtain w where \<open>s\<^sup>\<star> \<unlhd> w & \<not>w \<Turnstile> p\<close>
              using PossibleWorld.instantiation[rotated] by meson
            AOT_hence \<open>s \<unlhd> w & w \<Turnstile> (\<not>p)\<close>
              by (metis "coherent:1" "con-dis-i-e:1" "con-dis-i-e:2:a" "con-dis-i-e:2:b"
                        "intro-elim:3:b" "poss-sit-part-w:7")
            AOT_hence \<open>s\<^sup>+\<not>p \<unlhd> w\<close>
              using "poss-sit-part-w:2"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(2)]
              by blast
            AOT_thus \<open>\<exists>w s\<^sup>+\<not>p \<unlhd> w\<close>
              using "PossibleWorld.\<exists>I" by simp
          qed
          also AOT_have \<open>\<dots> \<equiv> \<exists>w \<not>(s\<^sup>\<star> \<unlhd> w \<rightarrow> w \<Turnstile> p)\<close>
            by (metis (no_types, lifting) "con-dis-i-e:1" "con-dis-i-e:2:a" "con-dis-i-e:2:b"
                                          "deduction-theorem" "existential:2[const_var]"
                                          "instantiation" "intro-elim:2" "reductio-aa:1"
                                          "vdash-properties:10")
          also AOT_have \<open>\<dots> \<equiv> \<not>\<forall>w (s\<^sup>\<star> \<unlhd> w \<rightarrow> w \<Turnstile> p)\<close>
            by (metis (no_types, lifting) "con-dis-i-e:1" "con-dis-i-e:2:a" "con-dis-i-e:2:b"
                  "deduction-theorem" "existential:2[const_var]" "instantiation"
                  "intro-elim:2" "reductio-aa:1" "rule-ui:3" "universal-cor"
                  "vdash-properties:10")
          also AOT_have \<open>\<dots> \<equiv> \<not>(Actual(s\<^sup>\<star>) \<Rightarrow> p)\<close>
            using "poss-sit-part-w:3"[unconstrain s, unvarify \<beta>, THEN "\<rightarrow>E"]
            by (meson "Situation.res-var:3" "intro-elim:3:a" "oth-class-taut:4:b"
                      "vdash-properties:10" aux4)
          finally AOT_have \<open>\<diamond>(Actual(s) & \<not>p) \<equiv> \<not>(Actual(s\<^sup>\<star>) \<Rightarrow> p)\<close>.
        }
        ultimately AOT_show \<open>\<not>(Actual(s\<^sup>\<star>) \<Rightarrow> p)\<close>
          using "intro-elim:3:a" by blast
        AOT_show \<open>Actual(s\<^sup>\<star>) \<Rightarrow> p\<close>
          using Z.
      qed
    qed
    moreover AOT_have B: \<open>(Actual(s) \<Rightarrow> p) \<rightarrow> s\<^sup>\<star> \<Turnstile> p\<close>
      using "deduction-theorem" "intro-elim:3:b" "log-prop-prop:2"
            "poss-sit-part-w:5" "rule-ui:1" by blast
    moreover AOT_assume \<open>Actual(s\<^sup>\<star>) \<Rightarrow> p\<close>
    ultimately AOT_show \<open>s\<^sup>\<star> \<Turnstile> p\<close>
      using "vdash-properties:10" by blast
  qed
  AOT_thus \<open>ModallyClosed(s\<^sup>\<star>)\<close>
    using "\<equiv>\<^sub>d\<^sub>fI" "con-dis-i-e:1" "sit-clo" aux4 by blast
qed

AOT_theorem "poss-sit-part-w:10": \<open>Possible(s) \<equiv> Consistent(s\<^sup>\<star>)\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>Possible(s)\<close>
  AOT_hence 1: \<open>Possible(s\<^sup>\<star>)\<close>
    using "intro-elim:3:a" "poss-sit-part-w:8" by blast
  AOT_show \<open>Consistent(s\<^sup>\<star>)\<close>
    using "pos-cons-sit:1"[unconstrain s, unvarify \<beta>] 1
    by (meson "Situation.res-var:3" "vdash-properties:10" aux4)
next
  AOT_assume \<open>Consistent(s\<^sup>\<star>)\<close>
  moreover AOT_have \<open>ModallyClosed(s\<^sup>\<star>)\<close>
    by (simp add: "poss-sit-part-w:9")
  ultimately AOT_have \<open>Possible(s\<^sup>\<star>)\<close>
    using "modal-clos-facts:2"[unconstrain s, unvarify \<beta>]
    by (metis "con-dis-i-e:1" "situations:3" "vdash-properties:6" aux4)
  AOT_thus \<open>Possible(s)\<close>
    using "intro-elim:3:b" "poss-sit-part-w:8" by blast
qed

AOT_define Possibility :: \<open>\<tau> \<Rightarrow> \<phi>\<close> ("Possibility'(_')")
 "possibilities:1": \<open>Possibility(s) \<equiv>\<^sub>d\<^sub>f Consistent(s) & ModallyClosed(s)\<close>

AOT_theorem "possibilites:2": \<open>Possibility(w)\<close>
  apply(safe intro!: "\<equiv>\<^sub>d\<^sub>fI"[OF "possibilities:1"] "&I" "world-cons:1" "world-closed:1")
  using "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:a" "world-pos" pos by blast

AOT_theorem "possiblities:3": \<open>Possibility(s) \<rightarrow> \<box>Possibility(s)\<close>
proof(safe intro!: "\<rightarrow>I" dest!: "possibilities:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"])
  AOT_have 1: \<open>\<box>Consistent(s) \<equiv> Consistent(s)\<close>
    using "cons-rigid:2"
    by (meson "RM:3" "S5Basic:1" "intro-elim:3:f")
  AOT_have 2: \<open>ModallyClosed(s) \<equiv> \<box>ModallyClosed(s)\<close>
  proof(safe intro!: "\<rightarrow>I" "\<equiv>I" "&I" dest!: "\<equiv>\<^sub>d\<^sub>fE"[OF "sit-clo"])
    AOT_assume \<open>Situation(s) & \<forall>p (Actual(s) \<Rightarrow> p \<rightarrow> s \<Turnstile> p)\<close>
    AOT_hence 1: \<open>\<forall>p (Actual(s) \<Rightarrow> p \<rightarrow> s \<Turnstile> p)\<close>
      using "&E" by blast
    AOT_have \<open>\<box>(Actual(s) \<Rightarrow> p \<rightarrow> s \<Turnstile> p)\<close> for p
    proof (rule "sc-eq-box-box:6"[THEN "\<rightarrow>E", THEN "\<rightarrow>E"])
      AOT_show \<open>\<box>(Actual(s) \<Rightarrow> p \<rightarrow> \<box>(Actual(s) \<Rightarrow> p))\<close>
        apply (AOT_subst_def "nec-impl-p:1")
        by (simp add: "S5Basic:5" RN)
    next
      AOT_have \<open>Actual(s) \<Rightarrow> p \<rightarrow> s \<Turnstile> p\<close>
        using 1  "rule-ui:3" by blast
      AOT_thus \<open>Actual(s) \<Rightarrow> p \<rightarrow> \<box>s \<Turnstile> p\<close>
        by (metis "deduction-theorem" "intro-elim:3:a" "lem2:1" "vdash-properties:10")
    qed
    AOT_hence \<open>\<forall>p \<box>(Actual(s) \<Rightarrow> p \<rightarrow> s \<Turnstile> p)\<close>
      by (simp add: "universal-cor")
    AOT_hence \<open>\<box>\<forall>p (Actual(s) \<Rightarrow> p \<rightarrow> s \<Turnstile> p)\<close>
      by (metis "BFs:1" "vdash-properties:10")
    AOT_thus \<open>\<box>ModallyClosed(s)\<close>
      apply (AOT_subst_def "sit-clo")
      by (metis "KBasic:3" "\<equiv>E"(2) "con-dis-i-e:1" RN Situation.restricted_var_condition) 
  next
    AOT_assume \<open>\<box>ModallyClosed(s)\<close>
    AOT_thus \<open>ModallyClosed(s)\<close>
      using "qml:2" "vdash-properties:10" "vdash-properties:1[2]" by blast
  qed

  AOT_assume \<open>Situation(s) & (Consistent(s) & ModallyClosed(s))\<close>
  AOT_thus \<open>\<box>Possibility(s)\<close>
    apply (AOT_subst_def "possibilities:1")
    by (metis "1" "2" "KBasic:3" "con-dis-i-e:1" "con-dis-i-e:2:a" "con-dis-i-e:2:b"
              "intro-elim:3:a" "intro-elim:3:b" RN Situation.restricted_var_condition)
qed


AOT_register_rigid_restricted_type
  Possibilities: \<open>Possibility(\<kappa>)\<close>
proof
  AOT_modally_strict {
    AOT_show \<open>\<exists>x Possibility(x)\<close>
      using "existential:2[const_var]" "possibilites:2" by blast
  }
next
  AOT_modally_strict {
    AOT_show \<open>Possibility(\<kappa>) \<rightarrow> \<kappa>\<down>\<close> for \<kappa>
      by (metis "Hypothetical Syllogism" "Situation.res-var:3" "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:a"
                "deduction-theorem" "possibilities:1")
  }
next
  AOT_modally_strict {
    AOT_show \<open>\<forall>\<alpha>(Possibility(\<alpha>) \<rightarrow> \<box>Possibility(\<alpha>))\<close>
      using "possiblities:3"
      by (smt (verit, del_insts) "Situation.\<forall>I" "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:a" "deduction-theorem"
            "possibilities:1" "rule-ui:3" "universal-cor" "vdash-properties:10")
  }
qed

AOT_register_variable_names
  Possibilities: \<ss>

AOT_theorem "possibilities:4": \<open>\<box>p \<rightarrow> \<forall>\<ss>(\<ss> \<Turnstile> p)\<close>
proof(safe intro!: "\<rightarrow>I" "Possibilities.\<forall>I")
  fix \<ss>
  AOT_assume 1: \<open>\<box>p\<close>
  AOT_show \<open>\<ss> \<Turnstile> p\<close>
    by (meson "1" "con-dis-i-e:1" "cqt:2"(1)
        "modal-clos-facts:3.unconstrain_s.unvarify_p.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<rightarrow>E"
        "possibilities:1.\<equiv>\<^sub>d\<^sub>fE.&E(1)" "possibilities:1.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(2)"
        AOT_restricted_type.\<psi> Possibilities.AOT_restricted_type_axioms)
qed

AOT_define Contains :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl \<open>\<unrhd>\<close> 80)
  "possibilities:5": \<open>s' \<unrhd> s \<equiv>\<^sub>d\<^sub>f s \<unlhd> s' \<close>

(* TODO: "possibilities:6" *)

AOT_theorem "possibilitites:7(a)": \<open>s \<unrhd> s\<close>
  by (meson "\<equiv>\<^sub>d\<^sub>fI" "con-dis-i-e:1" "part:1" "possibilities:5" Situation.restricted_var_condition)

AOT_theorem "possibilitites:7(b)": \<open>(s' \<unrhd> s & s' \<noteq> s) \<rightarrow> \<not>s \<unrhd> s'\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_assume 0: \<open>s' \<unrhd> s & s' \<noteq> s\<close>
  AOT_show \<open>\<not>s \<unrhd> s'\<close>
  proof(rule "raa-cor:2")
    AOT_assume 1: \<open>s \<unrhd> s'\<close>
    AOT_hence \<open>s'\<unlhd> s\<close>
      using "0" "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:a" "con-dis-i-e:2:b" "possibilities:5" by blast
    moreover AOT_have \<open>s \<unlhd> s'\<close>
      using 0 "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:a" "con-dis-i-e:2:b" "possibilities:5" by blast
    ultimately AOT_have \<open>s = s'\<close>
      using "df-simplify:2" "intro-elim:3:b" "sit-identity2:1" by blast
    moreover AOT_have \<open>\<not>(s = s')\<close>
      using 0
      using "=-infix" "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:b" "raa-cor:6" id_sym by blast
    ultimately AOT_show \<open>s = s' & \<not>(s = s')\<close>
      using "&I" by blast
  qed
qed

AOT_theorem "possiblities:7(c)": \<open>(s'' \<unrhd> s' & s' \<unrhd> s) \<rightarrow> s'' \<unrhd> s\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_assume 0: \<open>s'' \<unrhd> s' & s' \<unrhd> s\<close>
  AOT_hence \<open>s' \<unlhd> s''\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:a" "con-dis-i-e:2:b" "possibilities:5" by blast
  moreover AOT_have \<open>s \<unlhd> s'\<close>
    using 0"\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:b" "possibilities:5" by blast
  ultimately AOT_have \<open>s \<unlhd> s''\<close>
    by (meson "con-dis-i-e:1" "part:3" "vdash-properties:6")
  AOT_thus \<open>s'' \<unrhd> s\<close>
    by (meson "\<equiv>\<^sub>d\<^sub>fI" "con-dis-i-e:1" "possibilities:5" Situation.restricted_var_condition)
qed

AOT_theorem "possibilities:8": \<open>\<forall>p(\<ss> \<Turnstile> p & \<ss>' \<unrhd> \<ss> \<rightarrow> \<ss>' \<Turnstile> p)\<close>
proof(safe intro!: GEN "\<rightarrow>I")
  fix p
  AOT_assume 0: \<open>\<ss> \<Turnstile> p & \<ss>' \<unrhd> \<ss>\<close>
  AOT_hence \<open>\<ss> \<unlhd> \<ss>'\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:b" "possibilities:5" by blast
  AOT_hence \<open>\<forall>p(\<ss> \<Turnstile> p \<rightarrow> \<ss>' \<Turnstile> p)\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:b" "sit-part-whole" by blast
  AOT_thus \<open>\<ss>' \<Turnstile> p\<close>
    using "0" "con-dis-i-e:2:a" "rule-ui:3" "vdash-properties:10" by blast
qed

AOT_define AbsoluteNecessity :: \<open>\<tau>\<close> (\<open>s\<^sub>\<box>\<close>)
  "possibilities:9": \<open>s\<^sub>\<box> =\<^sub>d\<^sub>f \<^bold>\<iota>s\<forall>p(s \<Turnstile> p \<equiv> \<box>p)\<close>

(* Note: the following theorems prefixed absolute_necessity_* are considered trivial and not
         explicitly mentioned in PLM *)

AOT_theorem absolute_necessity_denotes: \<open>s\<^sub>\<box>\<down>\<close>
proof -
  AOT_have \<open>\<^bold>\<iota>s(\<forall>p (s \<Turnstile> p \<equiv> \<box>p))\<down>\<close>
    using "sit-comp-simp:3" by blast
  AOT_thus \<open>s\<^sub>\<box>\<down>\<close>
    using "possibilities:9" "rule-id-df:2:b[zero]" by blast 
qed

AOT_theorem absolute_necessity_matrix: \<open>\<forall>p(s\<^sub>\<box> \<Turnstile> p \<equiv> \<box>p)\<close>
proof -
  AOT_obtain y where y_def: \<open>y = \<^bold>\<iota>s(\<forall>p (s \<Turnstile> p \<equiv> \<box>p))\<close>
    using "free-thms:1"[THEN "\<equiv>E"(1), OF "sit-comp-simp:3"]
          "instantiation" by meson

  AOT_have \<open>\<forall>p(y \<Turnstile> p \<equiv> \<box>p)\<close>
  proof(safe intro!: "sit-comp-simp:4"[THEN "\<rightarrow>E"] "strict-can:1[I]" y_def)
    AOT_modally_strict {
      AOT_show \<open>\<forall>p (\<box>p \<rightarrow> \<box>\<box>p)\<close>
        by (simp add: "S5Basic:5" "universal-cor")
    }
  qed
  AOT_hence \<open>\<forall>p(\<^bold>\<iota>s(\<forall>p (s \<Turnstile> p \<equiv> \<box>p)) \<Turnstile> p \<equiv> \<box>p)\<close>
    using y_def 
    by (meson "rule=E")
  moreover AOT_have \<open>s\<^sub>\<box> = \<^bold>\<iota>s\<forall>p(s \<Turnstile> p \<equiv> \<box>p)\<close>
    by (simp add: "possibilities:9" "rule-id-df:1[zero]" "sit-comp-simp:3")
  ultimately AOT_show \<open>\<forall>p(s\<^sub>\<box> \<Turnstile> p \<equiv> \<box>p)\<close>
    using "log-prop-prop:2" "rule-ui:1" "rule=E" "universal-cor" id_sym by fast
qed

AOT_theorem absolute_necessity_situation: \<open>Situation(s\<^sub>\<box>)\<close>
proof -
  AOT_obtain p where \<open>\<box>p\<close>
    by (metis "existential:1" "instantiation" "log-prop-prop:2" "o-objects-exist:1")
  AOT_hence \<open>s\<^sub>\<box> \<Turnstile> p\<close>
    using "intro-elim:3:b" "log-prop-prop:2" "rule-ui:1" absolute_necessity_matrix by blast
  AOT_thus \<open>Situation(s\<^sub>\<box>)\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:a" "true-in-s" by blast
qed

AOT_theorem "possibilities:10": \<open>Contingent0(p) \<rightarrow> GapOn(s\<^sub>\<box>, p)\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_assume 0: \<open>Contingent0(p)\<close>

  AOT_hence \<open>\<diamond>p\<close>
    using "&E" "\<equiv>E"(1) "thm-cont-propos:2" by blast
  AOT_hence \<open>\<not>\<box>\<not>p\<close>
    using "KBasic2:1" "\<not>\<not>I" "intro-elim:3:d" by blast
  AOT_hence \<open>\<not>s\<^sub>\<box> \<Turnstile> \<not>p\<close>
    using absolute_necessity_matrix[THEN "\<forall>E"(1), OF "log-prop-prop:2", THEN "\<equiv>E"(1)]
          "reductio-aa:2" by blast
  AOT_hence \<open>\<not>s\<^sub>\<box> \<Turnstile> ((p)\<^sup>-)\<close>
    by (metis "log-prop-prop:2" "reductio-aa:1" "thm-relation-negation:7.unvarify_p.\<forall>E(1).rule=E'")

  moreover {
    AOT_have \<open>\<diamond>\<not>p\<close>
      using 0 "&E" "\<equiv>E"(1) "thm-cont-propos:2" by blast
    AOT_hence \<open>\<not>\<box>p\<close>
      using "KBasic:11" "\<equiv>E"(2) "possibilities:1"by blast
    AOT_hence \<open>\<not>s\<^sub>\<box> \<Turnstile> p\<close>
      using absolute_necessity_matrix
            "intro-elim:3:a" "log-prop-prop:2" "raa-cor:6" "rule-ui:1" by blast
  }
  ultimately AOT_show \<open>GapOn(s\<^sub>\<box>, p)\<close>
     by (safe intro!: "routley-star:5"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" absolute_necessity_situation)
 qed

AOT_theorem "possibilities:11": \<open>Possibility(s\<^sub>\<box>)\<close>
proof(safe intro!: "\<equiv>\<^sub>d\<^sub>fI"[OF "possibilities:1"] "&I" absolute_necessity_situation)
  AOT_show \<open>Consistent(s\<^sub>\<box>)\<close>
  proof(rule "raa-cor:1")
    AOT_assume \<open>\<not>Consistent(s\<^sub>\<box>)\<close>
    AOT_hence \<open>\<not>(Situation(s\<^sub>\<box>) & \<not>\<exists>p (s\<^sub>\<box> \<Turnstile> p & s\<^sub>\<box> \<Turnstile> \<not>p))\<close>
      by (AOT_subst_def (reverse) cons)
    AOT_hence \<open>\<exists>p(s\<^sub>\<box> \<Turnstile> p & s\<^sub>\<box> \<Turnstile> \<not>p)\<close>
      using "con-dis-i-e:1" "raa-cor:4" absolute_necessity_situation by blast
    then AOT_obtain q\<^sub>1 where \<open>s\<^sub>\<box> \<Turnstile> q\<^sub>1 & s\<^sub>\<box> \<Turnstile> \<not>q\<^sub>1\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>\<box>q\<^sub>1\<close> and \<open>\<box>\<not>q\<^sub>1\<close>
      using "&E" "intro-elim:3:a" "log-prop-prop:2" "rule-ui:1" absolute_necessity_matrix by blast+
    AOT_hence \<open>q\<^sub>1 & \<not>q\<^sub>1\<close>
      by (meson "B\<diamond>" "T\<diamond>" "con-dis-i-e:1" "vdash-properties:10")
    AOT_thus \<open>p & \<not>p\<close>
      using "raa-cor:1" by blast
  qed

  AOT_show \<open>ModallyClosed(s\<^sub>\<box>)\<close>
  proof(safe intro!: "\<equiv>\<^sub>d\<^sub>fI"[OF "sit-clo"] "&I" absolute_necessity_situation GEN "\<rightarrow>I")
    fix p
    AOT_assume \<open>Actual(s\<^sub>\<box>) \<Rightarrow> p\<close>
    AOT_hence \<open>\<box>(Actual(s\<^sub>\<box>) \<rightarrow> p)\<close>
      using "\<equiv>\<^sub>d\<^sub>fE" "nec-impl-p:1" by blast
    AOT_hence \<open>\<box>(\<not>p \<rightarrow> \<not>Actual(s\<^sub>\<box>))\<close>
      by (simp add: "intro-elim:2" "rule-sub-remark:5[1]"
                    "useful-tautologies:4" "useful-tautologies:5")
    AOT_hence \<xi>: \<open>\<diamond>\<not>p \<rightarrow> \<diamond>\<not>Actual(s\<^sub>\<box>)\<close>
      using "K\<diamond>" "vdash-properties:10" by blast
    AOT_have \<open>\<box>p\<close>
    proof(rule "raa-cor:1")
      AOT_assume \<open>\<not>\<box>p\<close>
      AOT_hence \<open>\<diamond>\<not>p\<close>
        using "KBasic:11" "intro-elim:3:a" by blast
      AOT_hence \<open>\<diamond>(\<not>Actual(s\<^sub>\<box>))\<close>
        using "vdash-properties:10" \<xi> by blast
      AOT_hence \<open>\<diamond>(\<not>(Situation(s\<^sub>\<box>) & \<forall>p (s\<^sub>\<box> \<Turnstile> p \<rightarrow> p)))\<close>
        by (AOT_subst_def (reverse) actual)
      AOT_hence \<open>\<diamond>(\<not>\<forall>p (s\<^sub>\<box> \<Turnstile> p \<rightarrow> p))\<close>
        by (smt (verit, del_insts) "RM:2.\<rightarrow>E" "con-dis-i-e:1" "contraposition:1[1]" "deduction-theorem"
            absolute_necessity_situation)
      AOT_hence \<open>\<diamond>(\<exists>p \<not>(s\<^sub>\<box> \<Turnstile> p \<rightarrow> p))\<close>
        using "RM:2.\<rightarrow>E" "cqt-further:2" by blast
      AOT_hence \<open>\<exists>p \<diamond>\<not>(s\<^sub>\<box> \<Turnstile> p \<rightarrow> p)\<close>
        using "BF\<diamond>" "vdash-properties:10" by blast
      then AOT_obtain p\<^sub>1 where \<open>\<diamond>\<not>(s\<^sub>\<box> \<Turnstile> p\<^sub>1 \<rightarrow> p\<^sub>1)\<close>
        using "\<exists>E"[rotated] by blast
      AOT_hence 1: \<open>\<diamond>(s\<^sub>\<box> \<Turnstile> p\<^sub>1 & \<not>p\<^sub>1)\<close>
        apply (AOT_subst \<open>s\<^sub>\<box> \<Turnstile> p\<^sub>1 & \<not>p\<^sub>1\<close> \<open>\<not>(s\<^sub>\<box> \<Turnstile> p\<^sub>1 \<rightarrow> p\<^sub>1)\<close>)
        using "intro-elim:3:f" "oth-class-taut:1:b" "oth-class-taut:3:a" apply blast
        by auto
      AOT_hence 2: \<open>\<diamond>s\<^sub>\<box> \<Turnstile> p\<^sub>1\<close> and 3: \<open>\<diamond>\<not>p\<^sub>1\<close>
        using "KBasic2:3" "con-dis-i-e:2:a" "vdash-properties:10" apply blast
        using "1" "KBasic2:3" "con-dis-i-e:2:b" "vdash-properties:10" by blast
      AOT_hence 4: \<open>\<not>\<box>p\<^sub>1\<close>
        using 3  "KBasic:11" "intro-elim:3:b" by blast
      AOT_have \<open>\<box>(s\<^sub>\<box> \<Turnstile> p\<^sub>1 \<rightarrow> \<box>p\<^sub>1)\<close>
        using "if-p-then-p" "log-prop-prop:2" "rule-sub-remark:6[1]" "rule-ui:1"
              RN absolute_necessity_matrix by blast
      AOT_hence \<open>\<diamond>\<box>p\<^sub>1\<close>
        using 2
        using "K\<diamond>" "vdash-properties:10" by blast
      AOT_hence \<open>\<box>p\<^sub>1\<close>
        using "S5Basic:2" "intro-elim:3:b" by blast
      AOT_thus \<open>p & \<not>p\<close>
        using 4 "raa-cor:3" by blast
    qed
    AOT_thus \<open>s\<^sub>\<box> \<Turnstile> p\<close>
      using "cqt-orig:3" "intro-elim:3:b" "vdash-properties:10"
            absolute_necessity_matrix by blast
  qed
qed

AOT_theorem Aux: \<open>s \<unlhd> s' \<equiv> Situation(s) & Situation(s') & \<forall>p (s \<Turnstile> p \<rightarrow> s' \<Turnstile> p)\<close>
    using "sit-part-whole"[THEN "\<equiv>Df"].


AOT_theorem "possibilities:12": \<open>\<forall>s((s \<unlhd> s\<^sub>\<box> & s \<noteq> s\<^sub>\<box>) \<rightarrow> \<not>Possibility(s))\<close>
proof (safe intro!: "\<rightarrow>I" "Situation.GEN")
  fix s
  AOT_find_theorems item: 474
  AOT_assume 1: \<open>s \<unlhd> s\<^sub>\<box> & s \<noteq> s\<^sub>\<box>\<close>
  AOT_hence \<open>\<not>(s = s\<^sub>\<box>)\<close>
    using "=-infix" "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:b" by blast
  AOT_hence \<open>\<not>\<forall>p(s \<Turnstile> p \<equiv> s\<^sub>\<box> \<Turnstile> p)\<close>
    by (metis (full_types) "reductio-aa:1" "rule=I:1"
          "sit-identity.unconstrain_s.unconstrain_s'.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E.\<equiv>E(2).rule=E'"
          "situations:3.\<rightarrow>E" Situation.restricted_var_condition absolute_necessity_situation)
  AOT_hence \<open>\<exists>p \<not>(s \<Turnstile> p \<equiv> s\<^sub>\<box> \<Turnstile> p)\<close>
    using "cqt-further:2" "vdash-properties:10" by blast
  then AOT_obtain q\<^sub>1 where \<open>\<not>(s \<Turnstile> q\<^sub>1 \<equiv> s\<^sub>\<box> \<Turnstile> q\<^sub>1)\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<open>(s \<Turnstile> q\<^sub>1 & \<not>s\<^sub>\<box> \<Turnstile> q\<^sub>1) \<or> (s\<^sub>\<box> \<Turnstile> q\<^sub>1 & \<not>s \<Turnstile> q\<^sub>1)\<close>
    by (metis "con-dis-i-e:1" "con-dis-i-e:3:a" "con-dis-i-e:3:b"
              "deduction-theorem" "intro-elim:2" "reductio-aa:1")
  moreover {
    AOT_assume 0: \<open>s \<Turnstile> q\<^sub>1 & \<not>s\<^sub>\<box> \<Turnstile> q\<^sub>1\<close>
    AOT_have \<open>s \<unlhd> s\<^sub>\<box>\<close>
      using "1" "con-dis-i-e:2:a" by blast
    AOT_hence \<open>\<forall>p (s \<Turnstile> p \<rightarrow> s\<^sub>\<box> \<Turnstile> p)\<close>
      using "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:2:b" "sit-part-whole" by blast
    AOT_hence \<open>s\<^sub>\<box> \<Turnstile> q\<^sub>1\<close>
      using 0 "con-dis-i-e:2:a" "log-prop-prop:2" "rule-ui:1" "vdash-properties:10" by blast
    AOT_hence \<open>\<exists>p (p & \<not>p)\<close>
      using 0 "con-dis-i-e:2:b" "raa-cor:3" by blast
  }
  ultimately AOT_have 3: \<open>s\<^sub>\<box> \<Turnstile> q\<^sub>1 & \<not>s \<Turnstile> q\<^sub>1\<close>
    by (metis "con-dis-i-e:4:c" "instantiation" "raa-cor:1")
  AOT_hence 2: \<open>\<box>q\<^sub>1\<close>
    using "absolute_necessity_matrix.\<forall>E(1).\<equiv>E(1)" "con-dis-i-e:2:a" "log-prop-prop:2" by blast
  AOT_show \<open>\<not>Possibility(s)\<close>
  proof(rule "raa-cor:2")
    AOT_assume \<open>Possibility(s)\<close>
    AOT_hence \<open>s \<Turnstile> q\<^sub>1\<close>
      using 2 "possibilities:4" "rule-ui:2[const_var]" "vdash-properties:6" by blast
    AOT_thus \<open>s \<Turnstile> q\<^sub>1 & \<not>s \<Turnstile> q\<^sub>1\<close>
      using 3 "con-dis-i-e:1" "con-dis-i-e:2:b" by blast
  qed
qed

AOT_theorem Possibilities_are_Situations: \<open>Situation(\<ss>)\<close>
  using "&E"(1) "possibilities:1" "rule-eq-df:2" Possibilities.\<psi> by blast

AOT_theorem "possibilities:13": \<open>\<forall>\<ss>(\<ss> \<unrhd> s\<^sub>\<box>)\<close>
proof(safe intro!: "Possibilities.GEN")
  fix \<ss>
  AOT_have \<open>\<forall>p(s\<^sub>\<box> \<Turnstile> p \<rightarrow> \<ss> \<Turnstile> p)\<close>
  proof(safe intro!: GEN "\<rightarrow>I")
    fix p
    AOT_assume \<open>s\<^sub>\<box> \<Turnstile> p\<close>
    AOT_hence \<open>\<box>p\<close>
      using "intro-elim:3:a" "log-prop-prop:2" "rule-ui:1" absolute_necessity_matrix by blast
    AOT_thus \<open>\<ss> \<Turnstile> p\<close>
      using "possibilities:4"
      by (meson "cqt-orig:3" MP Possibilities.\<psi>)
  qed
  AOT_hence \<open>s\<^sub>\<box> \<unlhd> \<ss>\<close>
    using "sit-part-whole"[THEN "\<equiv>\<^sub>d\<^sub>fI"]
    "con-dis-i-e:1" Possibilities_are_Situations
    absolute_necessity_situation
    by presburger
  AOT_thus \<open>\<ss> \<unrhd> s\<^sub>\<box>\<close>
    by (meson "\<equiv>\<^sub>d\<^sub>fE" "\<equiv>\<^sub>d\<^sub>fI" "con-dis-i-e:1" "con-dis-i-e:2:a"
              "intro-elim:3:a" "oth-class-taut:2:a" "possibilities:5"
              "sit-part-whole")
qed

AOT_theorem "possibilities:14": \<open>GapOn(\<ss>,p) \<rightarrow> Contingent0(p)\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_assume 0: \<open>GapOn(\<ss>,p)\<close>
  AOT_hence 1: \<open>\<not>\<ss> \<Turnstile> p\<close> and 2: \<open>\<not>\<ss> \<Turnstile> ((p)\<^sup>-)\<close>
    by (auto simp add: "routley-star:5.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(1)" "routley-star:5.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(2)")
  AOT_show \<open>Contingent0(p)\<close>
  proof(rule "raa-cor:1")
    AOT_assume \<open>\<not>Contingent0(p)\<close>
    AOT_hence \<open>\<not>(\<diamond>p & \<diamond>\<not>p)\<close>
      using "intro-elim:3:c" "thm-cont-propos:2" by blast
    AOT_hence \<open>\<box>\<not>p \<or> \<box>p\<close>
      by (metis "KBasic2:1.\<equiv>E(2)" "KBasic:12.\<equiv>E(2)" "con-dis-i-e:1" "con-dis-i-e:3:a"
                "con-dis-i-e:3:b" "reductio-aa:2")
    moreover {
      AOT_assume \<open>\<box>\<not>p\<close>
      AOT_hence \<open>\<ss> \<Turnstile> ((p)\<^sup>-)\<close>
        by (meson "RM:3.\<equiv>E(2)" "cqt:2"(1) "log-prop-prop:2" "possibilities:4.unvarify_p.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E"
            "thm-relation-negation:3" Possibilities.restricted_var_condition)
      AOT_hence \<open>p & \<not>p\<close>
        using "2" "raa-cor:3" by blast
    }
    moreover {
      AOT_assume \<open>\<box>p\<close>
      AOT_hence \<open>\<ss> \<Turnstile> p\<close>
        by (metis "Possibilities.\<forall>E" "\<rightarrow>E" "possibilities:4")
      AOT_hence \<open>p & \<not>p\<close>
        using "1" "raa-cor:3" by blast
    }
    ultimately AOT_show \<open>p & \<not>p\<close>
      using "con-dis-i-e:4:b" "raa-cor:2" by blast
  qed
qed

AOT_theorem "possibilities:15[a]": \<open>Possibility(s) \<rightarrow> Possible(s)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>Possibility(s)\<close>
  AOT_hence \<open>Consistent(s)\<close> and \<open>ModallyClosed(s)\<close>
    using "possibilities:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_thus \<open>Possible(s)\<close>
    by (meson "con-dis-i-e:1" "modal-clos-facts:2" "vdash-properties:10")
qed

AOT_theorem "possibilities:15[b]": \<open>Possible(\<ss>)\<close>
  by (simp add: "cqt:2"(1) "possibilities:15[a].unconstrain_s.\<forall>E(1).\<rightarrow>E.\<rightarrow>E"
                Possibilities.\<psi> Possibilities_are_Situations)

AOT_theorem "possibilities:16": \<open>GapOn(\<ss>, p) \<rightarrow> \<exists>\<ss>'(\<ss>' \<unrhd> \<ss> & \<ss>' \<Turnstile> p) & \<exists>\<ss>'(\<ss>' \<unrhd> \<ss> & \<ss>' \<Turnstile> \<not>p)\<close>
proof(safe intro!: "\<rightarrow>I" "&I")
  {
    fix p
    AOT_have sit: \<open>Situation(\<ss>\<^sup>+p\<^sup>\<star>)\<close>
      by (simp add: "aux4.unconstrain_s.\<forall>E(1).\<rightarrow>E" "aux5.unconstrain_s.\<forall>E(1).\<rightarrow>E"
                    "situations:3.\<rightarrow>E" Possibilities_are_Situations)
    AOT_assume A: \<open>GapOn(\<ss>, p)\<close>
    AOT_show \<open>\<exists>\<ss>'(\<ss>' \<unrhd> \<ss> & \<ss>' \<Turnstile> p)\<close>
    proof(safe intro!: "\<exists>I"(1) "&I")
      AOT_have \<theta>: \<open>\<forall>q(\<ss> \<Turnstile> q \<rightarrow> \<ss>\<^sup>+p\<^sup>\<star> \<Turnstile> q)\<close>
      proof(safe intro!: "\<rightarrow>I" GEN)
        fix q
        AOT_assume \<open>\<ss> \<Turnstile> q\<close>
        AOT_thus \<open>\<ss>\<^sup>+p\<^sup>\<star> \<Turnstile> q\<close>
          by (meson "aux5.unconstrain_s.\<forall>E(1).\<rightarrow>E" "log-prop-prop:2"
                    "pext-lem:3.unconstrain_s.unvarify_q.unvarify_p.\<forall>E(1).\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<rightarrow>E"
                    "poss-sit-part-w:6.unconstrain_s.\<forall>E(1).\<rightarrow>E" "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E"
                    "situations:3.\<rightarrow>E" Possibilities_are_Situations)
      qed
      AOT_hence \<open>\<ss> \<unlhd> \<ss>\<^sup>+p\<^sup>\<star>\<close>
        by (simp add: "con-dis-i-e:1" "sit-part-whole.\<equiv>\<^sub>d\<^sub>fI" Possibilities_are_Situations sit)
      AOT_thus \<open>\<ss>\<^sup>+p\<^sup>\<star> \<unrhd> \<ss>\<close>
        by (simp add: "con-dis-i-e:1" "possibilities:5.\<equiv>\<^sub>d\<^sub>fI" "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(1).&E(1)" sit)
      AOT_show \<open>\<ss>\<^sup>+p\<^sup>\<star> \<Turnstile> p\<close>
        by (meson "log-prop-prop:2" "pext-lem:4.unconstrain_s.unvarify_p.\<forall>E(1).\<forall>E(1).\<rightarrow>E"
                  "poss-sit-part-w:6.unconstrain_s.\<forall>E(1).\<rightarrow>E" "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E"
                  "situations:3.\<rightarrow>E" "true-in-s.\<equiv>\<^sub>d\<^sub>fE.&E(1)" Possibilities_are_Situations)
      AOT_show 1: \<open>Possibility(\<ss>\<^sup>+p\<^sup>\<star>)\<close>
      proof(safe intro!: "possibilities:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" sit)
        AOT_have B: \<open>Possible(\<ss>\<^sup>+p)\<close>
        proof(rule "raa-cor:1")
          AOT_assume \<open>\<not>Possible(\<ss>\<^sup>+p)\<close>
          AOT_hence \<open>\<not>\<exists>w (\<ss>\<^sup>+p \<unlhd> w)\<close>
            using "aux5.unconstrain_s.\<forall>E(1).\<rightarrow>E" "poss-sit-part-w:1.unconstrain_s.\<forall>E(1).\<rightarrow>E.\<equiv>E(2)"
                  "raa-cor:3" "situations:3.\<rightarrow>E" Possibilities_are_Situations by blast
          AOT_hence \<open>\<forall>w \<not>(\<ss>\<^sup>+p \<unlhd> w)\<close>
            by (metis (no_types, lifting) "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "deduction-theorem"
                "existential:2[const_var]" "reductio-aa:2" "universal-cor")
          AOT_hence \<open>\<not>(\<ss>\<^sup>+p \<unlhd> w)\<close> for w
            using "PossibleWorld.\<forall>E" by fastforce
          AOT_hence \<open>\<not>(\<ss> \<unlhd> w & w \<Turnstile> p)\<close> for w
            by (metis "cqt:2"(1)
                "poss-sit-part-w:2.unconstrain_s.unvarify_p.unconstrain_w.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<equiv>E(2)"
                "reductio-aa:2" Possibilities_are_Situations PossibleWorld.\<psi>)
          AOT_hence \<open>\<ss> \<unlhd> w \<rightarrow> w \<Turnstile> \<not>p\<close> for w
            by (metis "\<equiv>E"(2) "coherent:1" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "reductio-aa:2" CP)
          AOT_hence \<open>\<ss> \<unlhd> w \<rightarrow> w \<Turnstile> ((p)\<^sup>-)\<close> for w
            by (metis "deduction-theorem" "id_sym.rule=E'" "thm-relation-negation:7" "vdash-properties:10")
          AOT_hence \<open>\<forall>w (\<ss> \<unlhd> w \<rightarrow> w \<Turnstile> ((p)\<^sup>-))\<close>
            using "PossibleWorld.\<forall>I" by force
          AOT_hence \<open>Actual(\<ss>) \<Rightarrow> ((p)\<^sup>-)\<close>
            by (simp add: "log-prop-prop:2"
                "poss-sit-part-w:3[newproof].unconstrain_s.unvarify_p.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<equiv>E(1)"
                "situations:3.\<rightarrow>E" Possibilities_are_Situations)
          AOT_hence \<open>\<ss> \<Turnstile> ((p)\<^sup>-)\<close>
            by (meson "log-prop-prop:2" "possibilities:1.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(2)"
                      "sit-clo.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E" AOT_restricted_type.\<psi>
                      Possibilities.AOT_restricted_type_axioms)
          moreover AOT_have \<open>\<not>\<ss> \<Turnstile> ((p)\<^sup>-)\<close>
            using "routley-star:5.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(2)" A by auto
          ultimately AOT_show \<open>p & \<not>p\<close>
            using "raa-cor:3" by blast
        qed
        AOT_hence C: \<open>Possible(\<ss>\<^sup>+p\<^sup>\<star>)\<close>
          by (simp add: "pos.\<equiv>\<^sub>d\<^sub>fE.&E(1)" "poss-sit-part-w:8.unconstrain_s.\<forall>E(1).\<rightarrow>E.\<equiv>E(1)"
                        "situations:3.\<rightarrow>E")
        AOT_thus \<open>Consistent(\<ss>\<^sup>+p\<^sup>\<star>)\<close>
          using "sit-pos:3.unconstrain_s.\<forall>E(1).\<rightarrow>E.\<rightarrow>E" "situations:3.\<rightarrow>E" sit by blast
        AOT_show \<open>ModallyClosed(\<ss>\<^sup>+p\<^sup>\<star>)\<close>
          by (simp add: "pos.\<equiv>\<^sub>d\<^sub>fE.&E(1)" "poss-sit-part-w:9.unconstrain_s.\<forall>E(1).\<rightarrow>E"
                        "situations:3.\<rightarrow>E" local.B)
      qed
      AOT_show \<open>\<ss>\<^sup>+p\<^sup>\<star>\<down>\<close>
        by (simp add: "situations:3.\<rightarrow>E" sit)
    qed
  }
  AOT_hence 1: \<open>\<forall>p(GapOn(\<ss>, p) \<rightarrow> \<exists>\<ss>'(\<ss>' \<unrhd> \<ss> & \<ss>' \<Turnstile> p))\<close>
    by (simp add: "deduction-theorem" "universal-cor")

  AOT_have 2: \<open>\<forall>p(GapOn(\<ss>, p) \<rightarrow> GapOn(\<ss>, \<not>p))\<close>
  proof(safe intro!: "\<rightarrow>I" GEN)
    fix p
    AOT_assume 1: \<open>GapOn(\<ss>, p)\<close>
    AOT_show \<open>GapOn(\<ss>, \<not>p)\<close>
    proof(rule "raa-cor:1")
      AOT_assume 2: \<open>\<not>GapOn(\<ss>, \<not>p)\<close>
      AOT_hence \<open>\<ss> \<Turnstile> \<not>p \<or> \<ss> \<Turnstile> ((\<not>p)\<^sup>-)\<close>
        by (metis "1" "con-dis-i-e:1" "con-dis-i-e:3:a" "con-dis-taut:4.\<rightarrow>E" "raa-cor:3" "routley-star:5.\<equiv>\<^sub>d\<^sub>fE.&E(1)"
            "routley-star:5.\<equiv>\<^sub>d\<^sub>fI")
      AOT_hence \<open>\<ss> \<Turnstile> \<not>p \<or> \<ss> \<Turnstile> \<not>\<not>p\<close>
        by (meson "log-prop-prop:2" "thm-relation-negation:7.unvarify_p.\<forall>E(1).rule=E'")
      moreover {
        AOT_assume \<open>\<ss> \<Turnstile> \<not>p\<close>
        AOT_hence \<open>\<ss> \<Turnstile> ((p)\<^sup>-)\<close>
          using "id_sym.rule=E'" "thm-relation-negation:7" by blast
        AOT_hence \<open>\<forall>p(p & \<not>p)\<close>
          by (smt (verit) "1" "raa-cor:3" "routley-star:5.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(2)")
      }
      AOT_find_theorems item: 529
      moreover {
        AOT_have \<open>ModallyClosed(\<ss>)\<close>
          by (simp add: "possibilities:1.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(2)" Possibilities.restricted_var_condition)
        AOT_hence aux: \<open>\<forall>p \<forall>q (\<ss> \<Turnstile> p & (p \<Rightarrow> q) \<rightarrow> \<ss> \<Turnstile> q)\<close>
          using "modal-clos-facts:1"[unconstrain s, unvarify \<beta>, THEN "\<rightarrow>E", THEN "\<rightarrow>E"]
          by (simp add: "cqt:2"(1) Possibilities_are_Situations)
        AOT_assume 2: \<open>\<ss> \<Turnstile> \<not>\<not>p\<close>
        AOT_have \<open>\<ss> \<Turnstile> p\<close>
        proof (safe intro!: aux[THEN "\<forall>E"(1), THEN "\<forall>E"(2), THEN "\<rightarrow>E"])
          AOT_show \<open>(\<not>\<not>p)\<down>\<close>
            by (simp add: "log-prop-prop:2")
          AOT_show \<open>\<ss> \<Turnstile> \<not>\<not>p & (\<not>\<not>p \<Rightarrow> p)\<close>
            by (simp add: "2" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "nec-impl-p:1.\<equiv>\<^sub>d\<^sub>fI"
                          "useful-tautologies:1" RN)
        qed
        AOT_hence \<open>\<forall>p(p & \<not>p)\<close>
          using "1" "raa-cor:4" "routley-star:5.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(1)" by blast
      }
      ultimately AOT_show \<open>p & \<not>p\<close>
        using "1" "con-dis-i-e:4:b" "routley-star:5.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(2)" "rule-ui:3"
        using "raa-cor:1" by blast
    qed
  qed
        
  AOT_assume A: \<open>GapOn(\<ss>, p)\<close>
  AOT_hence \<open>GapOn(\<ss>, \<not>p)\<close>
    using 2 "log-prop-prop:2" "rule-ui:1" "vdash-properties:10" by blast
  AOT_thus \<open>\<exists>\<ss>'(\<ss>' \<unrhd> \<ss> & \<ss>' \<Turnstile> \<not>p)\<close>
    using 1 "log-prop-prop:2" "rule-ui:1" "vdash-properties:10" by blast
qed

AOT_theorem "possibilites:17": \<open>\<forall>\<ss>'(\<ss>' \<unrhd> \<ss> \<rightarrow> \<exists>\<ss>''(\<ss>'' \<unrhd> \<ss>' & \<ss>'' \<Turnstile> p)) \<rightarrow> \<ss> \<Turnstile> p\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_assume \<theta>: \<open>\<forall>\<ss>'(\<ss>' \<unrhd> \<ss> \<rightarrow> \<exists>\<ss>''(\<ss>'' \<unrhd> \<ss>' & \<ss>'' \<Turnstile> p))\<close>
  AOT_show \<open>\<ss> \<Turnstile> p\<close>
  proof(rule "raa-cor:1")
    AOT_assume 0: \<open>\<not>\<ss> \<Turnstile> p\<close>
    {
      AOT_assume a: \<open>\<ss> \<Turnstile> \<not>p\<close>
      AOT_have \<open>\<ss> \<unrhd> \<ss>\<close>
        by (simp add: "possibilitites:7(a).unconstrain_s.\<forall>E(1).\<rightarrow>E" "situations:3.\<rightarrow>E"
                      Possibilities_are_Situations)
      AOT_hence \<open>\<exists>\<ss>''(\<ss>'' \<unrhd> \<ss> & \<ss>'' \<Turnstile> p)\<close>
        using \<theta>[THEN "\<forall>E"(1), THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "cqt:2"(1) Possibilities.\<psi> by blast
      then AOT_obtain \<ss>\<^sub>1 where 1: \<open>\<ss>\<^sub>1 \<unrhd> \<ss> & \<ss>\<^sub>1 \<Turnstile> p\<close>
        using "Possibilities.\<exists>E" by meson
      AOT_hence 2: \<open>\<ss>\<^sub>1 \<Turnstile> \<not>p\<close>
        using "con-dis-i-e:2:a" "log-prop-prop:2" "possibilities:5.\<equiv>\<^sub>d\<^sub>fE.&E(2)"
              "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E" a by blast
      AOT_have \<open>Consistent(\<ss>\<^sub>1)\<close>
        using "possibilities:1.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(1)" Possibilities.restricted_var_condition by auto
      AOT_hence \<open>\<not>\<exists>p (\<ss>\<^sub>1 \<Turnstile> p & \<ss>\<^sub>1 \<Turnstile> \<not>p)\<close>
        by (simp add: "cons.\<equiv>\<^sub>d\<^sub>fE.&E(2)")
      moreover AOT_have \<open>\<exists>p (\<ss>\<^sub>1 \<Turnstile> p & \<ss>\<^sub>1 \<Turnstile> \<not>p)\<close>
        using 1[THEN "&E"(2)] 2 "&I" "\<exists>I" by meson
      ultimately AOT_have \<open>p & \<not>p\<close>
        using "raa-cor:3" by blast
    }
    moreover {
      AOT_assume b: \<open>\<not>\<ss> \<Turnstile> \<not>p\<close>
      AOT_hence \<open>\<not>\<ss> \<Turnstile> ((p)\<^sup>-)\<close>
        using "propositions-lemma:1.rule=E'" "raa-cor:2" "rel-neg-T:2[zero].rule=E'" calculation by blast
      AOT_hence \<open>GapOn(\<ss>, p)\<close>
        using "0" "con-dis-i-e:1" "routley-star:5.\<equiv>\<^sub>d\<^sub>fI" Possibilities_are_Situations by presburger
      AOT_hence \<open>\<exists>\<ss>'(\<ss>' \<unrhd> \<ss> & \<ss>' \<Turnstile> \<not>p)\<close>
        by (meson "\<exists>I"(2) "cqt:2"(1)
            "possibilities:16.unconstrain_\<ss>.unvarify_p.\<forall>E(1).\<forall>E(1).\<rightarrow>E.\<rightarrow>E.&E(2).\<exists>E'" Possibilities.\<psi>)
      then AOT_obtain \<ss>\<^sub>2 where 1: \<open>\<ss>\<^sub>2 \<unrhd> \<ss> & \<ss>\<^sub>2 \<Turnstile> \<not>p\<close>
        using "Possibilities.\<exists>E" by meson
      AOT_hence \<open>\<exists>\<ss>''(\<ss>'' \<unrhd> \<ss>\<^sub>2 & \<ss>'' \<Turnstile> p)\<close>
        using \<theta>[THEN "\<forall>E"(1), THEN "\<rightarrow>E", THEN "\<rightarrow>E"]
        using "con-dis-i-e:2:a" "cqt:2"(1) Possibilities.restricted_var_condition by blast
      then AOT_obtain \<ss>\<^sub>3 where 2: \<open>\<ss>\<^sub>3 \<unrhd> \<ss>\<^sub>2 & \<ss>\<^sub>3 \<Turnstile> p\<close>
        using "Possibilities.\<exists>E" by meson
      AOT_have 3: \<open>\<ss>\<^sub>3 \<Turnstile> \<not>p\<close>
        using "possibilities:8"[THEN "\<forall>E"(1), OF "log-prop-prop:2"] 1[THEN "&E"(2)] 2[THEN "&E"(1)]
              "oth-class-taut:7:a.\<rightarrow>E.\<rightarrow>E.\<rightarrow>E" by blast
      AOT_have \<open>Consistent(\<ss>\<^sub>3)\<close>
        using "possibilities:1.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(1)" Possibilities.restricted_var_condition by auto
      AOT_hence \<open>\<not>\<exists>p (\<ss>\<^sub>3 \<Turnstile> p & \<ss>\<^sub>3 \<Turnstile> \<not>p)\<close>
        by (simp add: "cons.\<equiv>\<^sub>d\<^sub>fE.&E(2)")
      moreover AOT_have \<open>\<exists>p (\<ss>\<^sub>3 \<Turnstile> p & \<ss>\<^sub>3 \<Turnstile> \<not>p)\<close>
        by (meson "2" "3" "con-dis-i-e:2:b" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "existential:2[const_var]")
      ultimately AOT_have \<open>p & \<not>p\<close>
        using "raa-cor:3" by blast
    }
    ultimately AOT_show \<open>p & \<not>p\<close>
      using "raa-cor:1" by blast
  qed
qed

AOT_theorem "possibilities:18": \<open>\<ss> \<Turnstile> \<not>p \<equiv> \<forall>\<ss>'(\<ss>' \<unrhd> \<ss> \<rightarrow> \<not>\<ss>' \<Turnstile> p)\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I" "Possibilities.GEN")
  fix \<ss>'
  AOT_assume 0: \<open>\<ss> \<Turnstile> \<not>p\<close>
  AOT_assume \<open>\<ss>' \<unrhd> \<ss>\<close>
  AOT_hence 1: \<open>\<ss> \<unlhd> \<ss>'\<close>
    using "possibilities:5.\<equiv>\<^sub>d\<^sub>fE.&E(2)" by auto
  AOT_hence \<open>\<forall>p(\<ss> \<Turnstile> p \<rightarrow> \<ss>' \<Turnstile> p)\<close>
    by (simp add: "deduction-theorem" "log-prop-prop:2"
                  "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E" "universal-cor")
  AOT_hence 2: \<open>\<ss>' \<Turnstile> \<not>p\<close>
    using "0" "1" "log-prop-prop:2" "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E" by auto
  AOT_show \<open>\<not>\<ss>' \<Turnstile> p\<close>
  proof(rule "raa-cor:2")
    AOT_assume \<open>\<ss>' \<Turnstile> p\<close>
    AOT_hence \<open>\<exists>q(\<ss>' \<Turnstile> q & \<ss>' \<Turnstile> \<not>q)\<close>
      by (meson "2" "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "existential:2[const_var]")
    AOT_hence \<open>\<not>Consistent(\<ss>')\<close>
      using "cons.\<equiv>\<^sub>d\<^sub>fE.&E(2)" "raa-cor:3" by blast
    moreover AOT_have \<open>Consistent(\<ss>')\<close>
      by (simp add: "possibilities:1.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(1)" Possibilities.restricted_var_condition)
    ultimately AOT_show \<open>p & \<not>p\<close>
      using "raa-cor:3" by blast
  qed
next
  AOT_assume 1: \<open>\<forall>\<ss>'(\<ss>' \<unrhd> \<ss> \<rightarrow> \<not>\<ss>' \<Turnstile> p)\<close>
  AOT_show \<open>\<ss> \<Turnstile> \<not>p\<close>
  proof(rule "raa-cor:1")
    AOT_assume 2: \<open>\<not>\<ss> \<Turnstile> \<not>p\<close>
    AOT_have \<open>\<ss> \<unrhd> \<ss>\<close>
      using "cqt:2"(1) "possibilitites:7(a).unconstrain_s.\<forall>E(1).\<rightarrow>E"
            Possibilities_are_Situations by blast
    AOT_hence \<open>\<not>\<ss> \<Turnstile> p\<close>
      using "1" "rule-ui:3" "vdash-properties:10" Possibilities.restricted_var_condition by blast
    AOT_hence \<open>GapOn(\<ss>, p)\<close>
      by (smt (verit, ccfv_threshold) "2" "\<equiv>\<^sub>d\<^sub>fI" "con-dis-i-e:1" "cqt:2"(1) "raa-cor:2" "routley-star:5"
          "thm-relation-negation:7.unvarify_p.\<forall>E(1).rule=E'" Possibilities_are_Situations)
    AOT_hence \<open>\<exists>\<ss>'(\<ss>' \<unrhd> \<ss> & \<ss>' \<Turnstile> p)\<close>
      using "con-dis-taut:1" "oth-class-taut:4:a.\<rightarrow>E.\<rightarrow>E.\<rightarrow>E" "possibilities:16" by blast
    then AOT_obtain \<ss>\<^sub>1 where 3: \<open>\<ss>\<^sub>1 \<unrhd> \<ss> & \<ss>\<^sub>1 \<Turnstile> p\<close>
      using "Possibilities.\<exists>E" by meson
    AOT_hence \<open>\<not>\<ss>\<^sub>1 \<Turnstile> p\<close>
      using 1
      using "con-dis-i-e:2:a" "ded-thm-cor:4.\<rightarrow>E" "rule-ui:3" Possibilities.\<psi> by blast
    AOT_thus \<open>p & \<not>p\<close>
      using "3" "con-dis-i-e:2:b" "raa-cor:3" by blast
  qed
qed

AOT_theorem "possibilities:19": \<open>\<ss> \<Turnstile> (p & q) \<equiv> (\<ss> \<Turnstile> p & \<ss> \<Turnstile> q)\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I" "&I")
  AOT_assume \<open>\<ss> \<Turnstile> (p & q)\<close>
  moreover AOT_have \<open>(p & q) \<Rightarrow> p\<close>
    by (simp add: "con-dis-taut:1" "nec-impl-p:1.\<equiv>\<^sub>d\<^sub>fI" RN)
  ultimately AOT_show \<open>\<ss> \<Turnstile> p\<close>
    by (meson "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "cqt:2"(1) "log-prop-prop:2"
              "modal-clos-facts:1.unconstrain_s.\<forall>E(1).\<rightarrow>E.\<rightarrow>E.\<forall>E(1).\<forall>E(1).\<rightarrow>E"
              "possibilities:1.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(2)" "true-in-s.\<equiv>\<^sub>d\<^sub>fE.&E(1)" Possibilities.\<psi>)
next
  AOT_assume \<open>\<ss> \<Turnstile> (p & q)\<close>
  moreover AOT_have \<open>(p & q) \<Rightarrow> q\<close>
    using "con-dis-taut:2" "nec-impl-p:1.\<equiv>\<^sub>d\<^sub>fI" RN by blast
  ultimately AOT_show \<open>\<ss> \<Turnstile> q\<close>
    by (meson "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "cqt:2"(1) "log-prop-prop:2"
              "modal-clos-facts:1.unconstrain_s.\<forall>E(1).\<rightarrow>E.\<rightarrow>E.\<forall>E(1).\<forall>E(1).\<rightarrow>E"
              "possibilities:1.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(2)" "true-in-s.\<equiv>\<^sub>d\<^sub>fE.&E(1)" Possibilities.\<psi>)
next
  AOT_assume \<open>\<ss> \<Turnstile> p & \<ss> \<Turnstile> q\<close>
  moreover AOT_have \<open>(p & q) \<Rightarrow> (p & q)\<close>
    using "log-prop-prop:2" "nec-impl-p:3[rec].unvarify_p.\<forall>E(1)" by auto
  ultimately AOT_show \<open>\<ss> \<Turnstile> (p & q)\<close>
    by (meson "con-dis-i-e:1" "cqt:2"(1) "log-prop-prop:2"
        "modal-clos-facts:1b.unconstrain_s.\<forall>E(1).\<rightarrow>E.\<rightarrow>E.\<forall>E(1).\<forall>E(1).\<forall>E(1).\<rightarrow>E"
        "possibilities:1.\<equiv>\<^sub>d\<^sub>fE.&E(2).&E(2)" AOT_restricted_type.\<psi>
        Possibilities.AOT_restricted_type_axioms Possibilities_are_Situations)
qed

AOT_theorem "possibilities:20": \<open>\<diamond>p \<equiv> \<exists>\<ss>(\<ss> \<Turnstile> p)\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>\<diamond>p\<close>
  AOT_hence \<open>\<exists>w w \<Turnstile> p\<close>
    using "fund:3.unvarify_p.\<forall>E(1).\<equiv>E(2)" "log-prop-prop:2" "reductio-aa:1" by blast
  then AOT_obtain w where \<open>w \<Turnstile> p\<close>
    by (metis "PossibleWorld.\<exists>E")
  AOT_thus \<open>\<exists>\<ss>(\<ss> \<Turnstile> p)\<close>
    by (meson "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "existential:2[const_var]" "possibilites:2")
next
  AOT_assume \<open>\<exists>\<ss>(\<ss> \<Turnstile> p)\<close>
  then AOT_obtain \<ss> where 1: \<open>\<ss> \<Turnstile> p\<close>
    by (metis "Possibilities.\<exists>E")
  AOT_have \<open>Possible(\<ss>)\<close>
    by (simp add: "possibilities:15[b]")
  AOT_hence \<open>\<exists>w \<ss> \<unlhd> w\<close>
    by (meson "\<exists>I"(2) "pos.\<equiv>\<^sub>d\<^sub>fE.&E(1)" "situations:3.\<rightarrow>E"
              "poss-sit-part-w:1.unconstrain_s.\<forall>E(1).\<rightarrow>E.\<equiv>E(1).\<exists>E'")
  then AOT_obtain w where \<open>\<ss> \<unlhd> w\<close>
    using PossibleWorld.instantiation by blast
  AOT_hence \<open>w \<Turnstile> p\<close>
    using 1 by (simp add: "log-prop-prop:2" "sit-part-whole.\<equiv>\<^sub>d\<^sub>fE.&E(2).\<forall>E(1).\<rightarrow>E")
  AOT_thus \<open>\<diamond>p\<close>
    by (metis (no_types, lifting) "con-dis-taut:5.\<rightarrow>E.\<rightarrow>E" "existential:2[const_var]"
          "fund:1" "intro-elim:3:b" PossibleWorld.restricted_var_condition)
qed

AOT_theorem "possibilities:21": \<open>\<box>p \<equiv> \<forall>\<ss>(\<ss> \<Turnstile> p)\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I" Possibilities.GEN)
  fix \<ss>
  AOT_assume \<open>\<box>p\<close>
  AOT_thus \<open>\<ss> \<Turnstile> p\<close>
    by (simp add: "cqt:2"(1) "possibilities:4.unvarify_p.\<forall>E(1).\<rightarrow>E.\<forall>E(1).\<rightarrow>E" Possibilities.\<psi>)
next
  AOT_assume \<open>\<forall>\<ss>(\<ss> \<Turnstile> p)\<close>
  AOT_hence \<open>s\<^sub>\<box> \<Turnstile> p\<close>
    using "Possibilities.res-var:3" "possibilities:11" "rule-ui:1" "vdash-properties:10" by blast
  AOT_thus \<open>\<box>p\<close>
    by (simp add: "absolute_necessity_matrix.\<forall>E(1).\<equiv>E(1)" "cqt:2"(1))
qed

end
