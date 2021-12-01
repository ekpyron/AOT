theory AOT_misc
  imports AOT_NaturalNumbers
begin

AOT_theorem PossiblyNumbersEmptyPropertyImpliesZero:
  \<open>\<diamond>Numbers(x,[\<lambda>z O!z & z \<noteq>\<^sub>E z]) \<rightarrow> x = 0\<close>
proof(rule "\<rightarrow>I")
  AOT_have \<open>Rigid([\<lambda>z O!z & z \<noteq>\<^sub>E z])\<close>
  proof (safe intro!: "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2";
         rule RN; safe intro!: GEN "\<rightarrow>I")
    AOT_modally_strict {
      fix x
      AOT_assume \<open>[\<lambda>z O!z & z \<noteq>\<^sub>E z]x\<close>
      AOT_hence \<open>O!x & x \<noteq>\<^sub>E x\<close> by (rule "\<beta>\<rightarrow>C")
      moreover AOT_have \<open>x =\<^sub>E x\<close> using calculation[THEN "&E"(1)] 
        by (metis "ord=Eequiv:1" "vdash-properties:10")
      ultimately AOT_have \<open>x =\<^sub>E x & \<not>x =\<^sub>E x\<close>
        by (metis "con-dis-i-e:1" "con-dis-i-e:2:b" "intro-elim:3:a" "thm-neg=E")
      AOT_thus \<open>\<box>[\<lambda>z O!z & z \<noteq>\<^sub>E z]x\<close> using "raa-cor:1" by blast
    }
  qed
  AOT_hence \<open>\<box>\<forall>x (Numbers(x,[\<lambda>z O!z & z \<noteq>\<^sub>E z]) \<rightarrow> \<box>Numbers(x,[\<lambda>z O!z & z \<noteq>\<^sub>E z]))\<close>
    by (safe intro!: "num-cont:2"[unvarify G, THEN "\<rightarrow>E"] "cqt:2")
  AOT_hence \<open>\<forall>x \<box>(Numbers(x,[\<lambda>z O!z & z \<noteq>\<^sub>E z]) \<rightarrow> \<box>Numbers(x,[\<lambda>z O!z & z \<noteq>\<^sub>E z]))\<close>
    using "BFs:2"[THEN "\<rightarrow>E"] by blast
  AOT_hence \<open>\<box>(Numbers(x,[\<lambda>z O!z & z \<noteq>\<^sub>E z]) \<rightarrow> \<box>Numbers(x,[\<lambda>z O!z & z \<noteq>\<^sub>E z]))\<close>
    using "\<forall>E"(2) by auto
  moreover AOT_assume \<open>\<diamond>Numbers(x,[\<lambda>z O!z & z \<noteq>\<^sub>E z])\<close>
  ultimately AOT_have \<open>\<^bold>\<A>Numbers(x,[\<lambda>z O!z & z \<noteq>\<^sub>E z])\<close>
    using "sc-eq-box-box:1"[THEN "\<equiv>E"(1), THEN "\<rightarrow>E", THEN "nec-imp-act"[THEN "\<rightarrow>E"]]
    by blast
  AOT_hence \<open>Numbers(x,[\<lambda>z \<^bold>\<A>[\<lambda>z O!z & z \<noteq>\<^sub>E z]z])\<close>
    by (safe intro!: "eq-num:1"[unvarify G, THEN "\<equiv>E"(1)] "cqt:2")
  AOT_hence \<open>x = #[\<lambda>z O!z & z \<noteq>\<^sub>E z]\<close>
    by (safe intro!: "eq-num:2"[unvarify G, THEN "\<equiv>E"(1)] "cqt:2")
  AOT_thus \<open>x = 0\<close>
    using "cqt:2"(1) "rule-id-df:2:b[zero]" "rule=E" "zero:1" by blast
qed

AOT_define Numbers' :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>Numbers'''(_,_')\<close>)
  \<open>Numbers'(x, G) \<equiv>\<^sub>d\<^sub>f A!x & G\<down> & \<forall>F (x[F] \<equiv> F \<approx>\<^sub>E G)\<close>
AOT_theorem Numbers'equiv: \<open>Numbers'(x,G) \<equiv> A!x & \<forall>F (x[F] \<equiv> F \<approx>\<^sub>E G)\<close>
  by (AOT_subst_def Numbers')
     (auto intro!: "\<equiv>I" "\<rightarrow>I" "&I" "cqt:2" dest: "&E")

AOT_theorem Numbers'DistinctZeroes:
  \<open>\<exists>x\<exists>y (\<diamond>Numbers'(x,[\<lambda>z O!z & z \<noteq>\<^sub>E z]) & \<diamond>Numbers'(y,[\<lambda>z O!z & z \<noteq>\<^sub>E z]) & x \<noteq> y)\<close>
proof -
  AOT_obtain w\<^sub>1 where \<open>\<exists>w w\<^sub>1 \<noteq> w\<close>
    using "two-worlds-exist:4" "PossibleWorld.\<exists>E"[rotated] by fast
  then AOT_obtain w\<^sub>2 where distinct_worlds: \<open>w\<^sub>1 \<noteq> w\<^sub>2\<close>
    using "PossibleWorld.\<exists>E"[rotated] by blast
  AOT_obtain x where x_prop:
    \<open>A!x & \<forall>F (x[F] \<equiv> w\<^sub>1 \<Turnstile> F \<approx>\<^sub>E [\<lambda>z O!z & z \<noteq>\<^sub>E z])\<close>
    using "A-objects"[axiom_inst] "\<exists>E"[rotated] by fast
  moreover AOT_obtain y where y_prop:
    \<open>A!y & \<forall>F (y[F] \<equiv> w\<^sub>2 \<Turnstile> F \<approx>\<^sub>E [\<lambda>z O!z & z \<noteq>\<^sub>E z])\<close>
    using "A-objects"[axiom_inst] "\<exists>E"[rotated] by fast
  moreover {
    fix x w
    AOT_assume x_prop: \<open>A!x & \<forall>F (x[F] \<equiv> w \<Turnstile> F \<approx>\<^sub>E [\<lambda>z O!z & z \<noteq>\<^sub>E z])\<close>
    AOT_have \<open>\<forall>F w \<Turnstile> (x[F] \<equiv> F \<approx>\<^sub>E [\<lambda>z O!z & z \<noteq>\<^sub>E z])\<close>
    proof(safe intro!: GEN "conj-dist-w:4"[unvarify p q, OF "log-prop-prop:2",
                              OF "log-prop-prop:2",THEN "\<equiv>E"(2)] "\<equiv>I" "\<rightarrow>I")
      fix F
      AOT_assume \<open>w \<Turnstile> x[F]\<close>
      AOT_hence \<open>\<diamond>x[F]\<close>
        using "fund:1"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(2),
                       OF "PossibleWorld.\<exists>I"] by blast
      AOT_hence \<open>x[F]\<close>
        by (metis "en-eq:3[1]" "intro-elim:3:a")
      AOT_thus \<open>w \<Turnstile> (F \<approx>\<^sub>E [\<lambda>z O!z & z \<noteq>\<^sub>E z])\<close>
        using x_prop[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<equiv>E"(1)] by blast
    next
      fix F
      AOT_assume \<open>w \<Turnstile> (F \<approx>\<^sub>E [\<lambda>z O!z & z \<noteq>\<^sub>E z])\<close>
      AOT_hence \<open>x[F]\<close>
        using x_prop[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<equiv>E"(2)] by blast
      AOT_hence \<open>\<box>x[F]\<close>
        using "pre-en-eq:1[1]"[THEN "\<rightarrow>E"] by blast
      AOT_thus \<open>w \<Turnstile> x[F]\<close>
        using "fund:2"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)]
              "PossibleWorld.\<forall>E" by fast
    qed
    AOT_hence \<open>w \<Turnstile> \<forall>F (x[F] \<equiv> F \<approx>\<^sub>E [\<lambda>z O!z & z \<noteq>\<^sub>E z])\<close>
      using "conj-dist-w:5"[THEN "\<equiv>E"(2)] by fast
    moreover {
      AOT_have \<open>\<box>[\<lambda>z O!z & z \<noteq>\<^sub>E z]\<down>\<close>
        by (safe intro!: RN "cqt:2")
      AOT_hence \<open>w \<Turnstile> [\<lambda>z O!z & z \<noteq>\<^sub>E z]\<down>\<close>
        using "fund:2"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1),
                       THEN "PossibleWorld.\<forall>E"] by blast
    }
    moreover {
      AOT_have \<open>\<box>A!x\<close>
        using x_prop[THEN "&E"(1)] by (metis "oa-facts:2" "\<rightarrow>E")
      AOT_hence \<open>w \<Turnstile> A!x\<close>
        using "fund:2"[unvarify p, OF "log-prop-prop:2",
                       THEN "\<equiv>E"(1), THEN "PossibleWorld.\<forall>E"] by blast
    }
    ultimately AOT_have \<open>w \<Turnstile> (A!x & [\<lambda>z O!z & z \<noteq>\<^sub>E z]\<down> &
                               \<forall>F (x[F] \<equiv> F \<approx>\<^sub>E [\<lambda>z O!z & z \<noteq>\<^sub>E z]))\<close>
      using "conj-dist-w:1"[unvarify p q, OF "log-prop-prop:2",
              OF "log-prop-prop:2", THEN "\<equiv>E"(2), OF "&I"] by auto
    AOT_hence \<open>\<exists>w w \<Turnstile> (A!x & [\<lambda>z O!z & z \<noteq>\<^sub>E z]\<down> &
                        \<forall>F (x[F] \<equiv> F \<approx>\<^sub>E [\<lambda>z O!z & z \<noteq>\<^sub>E z]))\<close>
      using "PossibleWorld.\<exists>I" by auto
    AOT_hence \<open>\<diamond>(A!x & [\<lambda>z O!z & z \<noteq>\<^sub>E z]\<down> & \<forall>F (x[F] \<equiv> F \<approx>\<^sub>E [\<lambda>z O!z & z \<noteq>\<^sub>E z]))\<close>
      using "fund:1"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(2)] by blast
    AOT_hence \<open>\<diamond>Numbers'(x,[\<lambda>z O!z & z \<noteq>\<^sub>E z])\<close>
      by (AOT_subst_def Numbers')
  }
  ultimately AOT_have \<open>\<diamond>Numbers'(x,[\<lambda>z O!z & z \<noteq>\<^sub>E z])\<close>
                  and \<open>\<diamond>Numbers'(y,[\<lambda>z O!z & z \<noteq>\<^sub>E z])\<close>
    by auto
  moreover AOT_have \<open>x \<noteq> y\<close>
  proof (rule "ab-obey:2"[THEN "\<rightarrow>E"])
    AOT_have \<open>\<box>\<not>\<exists>u [\<lambda>z O!z & z \<noteq>\<^sub>E z]u\<close>
    proof (safe intro!: RN "raa-cor:2")
      AOT_modally_strict {
        AOT_assume \<open>\<exists>u [\<lambda>z O!z & z \<noteq>\<^sub>E z]u\<close>
        then AOT_obtain u where \<open>[\<lambda>z O!z & z \<noteq>\<^sub>E z]u\<close>
          using "Ordinary.\<exists>E"[rotated] by blast
        AOT_hence \<open>O!u & u \<noteq>\<^sub>E u\<close>
          by (rule "\<beta>\<rightarrow>C")
        AOT_hence \<open>\<not>(u =\<^sub>E u)\<close>
          by (metis "con-dis-taut:2" "intro-elim:3:d" "modus-tollens:1"
                    "raa-cor:3" "thm-neg=E")
        AOT_hence \<open>u =\<^sub>E u & \<not>u =\<^sub>E u\<close>
          by (metis "modus-tollens:1" "ord=Eequiv:1" "raa-cor:3" Ordinary.\<psi>)
        AOT_thus \<open>p & \<not>p\<close> for p
          by (metis "raa-cor:1")
      }
    qed
    AOT_hence nec_not_ex: \<open>\<forall>w w \<Turnstile> \<not>\<exists>u [\<lambda>z O!z & z \<noteq>\<^sub>E z]u\<close>
      using "fund:2"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)] by blast
    AOT_have \<open>\<box>([\<lambda>y p]x \<equiv> p)\<close> for x p
      by (safe intro!: RN "beta-C-meta"[THEN "\<rightarrow>E"] "cqt:2")
    AOT_hence \<open>\<forall>w w \<Turnstile> ([\<lambda>y p]x \<equiv> p)\<close> for x p
      using "fund:2"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)] by blast
    AOT_hence world_prop_beta: \<open>\<forall>w (w \<Turnstile> [\<lambda>y p]x \<equiv> w \<Turnstile> p)\<close> for x p
      using "conj-dist-w:4"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)]
            "PossibleWorld.\<forall>E" "PossibleWorld.\<forall>I" by meson

    AOT_have \<open>\<exists>p (w\<^sub>1 \<Turnstile> p & \<not>w\<^sub>2 \<Turnstile> p)\<close>
    proof(rule "raa-cor:1")
      AOT_assume 0: \<open>\<not>\<exists>p (w\<^sub>1 \<Turnstile> p & \<not>w\<^sub>2 \<Turnstile> p)\<close>
      AOT_have 1: \<open>w\<^sub>1 \<Turnstile> p \<rightarrow> w\<^sub>2 \<Turnstile> p\<close> for p
      proof(safe intro!: GEN "\<rightarrow>I")
        AOT_assume \<open>w\<^sub>1 \<Turnstile> p\<close>
        AOT_thus \<open>w\<^sub>2 \<Turnstile> p\<close>
          using 0 "con-dis-i-e:1" "\<exists>I"(2) "raa-cor:4" by fast
      qed
      moreover AOT_have \<open>w\<^sub>2 \<Turnstile> p \<rightarrow> w\<^sub>1 \<Turnstile> p\<close> for p
      proof(safe intro!: GEN "\<rightarrow>I")
        AOT_assume \<open>w\<^sub>2 \<Turnstile> p\<close>
        AOT_hence \<open>\<not>w\<^sub>2 \<Turnstile> \<not>p\<close>
          using "coherent:2" "intro-elim:3:a" by blast
        AOT_hence \<open>\<not>w\<^sub>1 \<Turnstile> \<not>p\<close>
          using 1["\<forall>I" p, THEN "\<forall>E"(1), OF "log-prop-prop:2"]
          by (metis "modus-tollens:1")
        AOT_thus \<open>w\<^sub>1 \<Turnstile> p\<close>
          using "coherent:1" "intro-elim:3:b" "reductio-aa:1" by blast
      qed
      ultimately AOT_have \<open>w\<^sub>1 \<Turnstile> p \<equiv> w\<^sub>2 \<Turnstile> p\<close> for p
        by (metis "intro-elim:2")
      AOT_hence \<open>w\<^sub>1 = w\<^sub>2\<close>
        using "sit-identity"[unconstrain s, THEN "\<rightarrow>E",
            OF PossibleWorld.\<psi>[THEN "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(1)],
            unconstrain s', THEN "\<rightarrow>E",
            OF PossibleWorld.\<psi>[THEN "world:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(1)],
            THEN "\<equiv>E"(2)] GEN by fast
      AOT_thus \<open>w\<^sub>1 = w\<^sub>2 & \<not>w\<^sub>1 = w\<^sub>2\<close>
        using  "=-infix" "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:1" distinct_worlds by blast
    qed
    then AOT_obtain p where 0: \<open>w\<^sub>1 \<Turnstile> p & \<not>w\<^sub>2 \<Turnstile> p\<close>
      using "\<exists>E"[rotated] by blast
    AOT_have \<open>y[\<lambda>y p]\<close>
    proof (safe intro!: y_prop[THEN "&E"(2), THEN "\<forall>E"(1), THEN "\<equiv>E"(2)] "cqt:2")
      AOT_show \<open>w\<^sub>2 \<Turnstile> [\<lambda>y p] \<approx>\<^sub>E [\<lambda>z O!z & z \<noteq>\<^sub>E z]\<close>
      proof (safe intro!:  "cqt:2" "empty-approx:1"[unvarify F H, THEN RN,
                  THEN "fund:2"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)],
                  THEN "PossibleWorld.\<forall>E",
                  THEN "conj-dist-w:2"[unvarify p q, OF "log-prop-prop:2",
                                       OF "log-prop-prop:2", THEN "\<equiv>E"(1)],
                                       THEN "\<rightarrow>E"]
                  "conj-dist-w:1"[unvarify p q, OF "log-prop-prop:2",
                                  OF "log-prop-prop:2", THEN "\<equiv>E"(2)] "&I")
        AOT_have \<open>\<not>w\<^sub>2 \<Turnstile> \<exists>u [\<lambda>y p]u\<close>
        proof (rule "raa-cor:2")
          AOT_assume \<open>w\<^sub>2 \<Turnstile> \<exists>u [\<lambda>y p]u\<close>
          AOT_hence \<open>\<exists>x w\<^sub>2 \<Turnstile> (O!x & [\<lambda>y p]x)\<close>
            by (metis "conj-dist-w:6" "intro-elim:3:a")
          then AOT_obtain x where \<open>w\<^sub>2 \<Turnstile> (O!x & [\<lambda>y p]x)\<close>
            using "\<exists>E"[rotated] by blast
          AOT_hence \<open>w\<^sub>2 \<Turnstile> [\<lambda>y p]x\<close>
            using "conj-dist-w:1"[unvarify p q, OF "log-prop-prop:2",
                    OF "log-prop-prop:2", THEN "\<equiv>E"(1), THEN "&E"(2)] by blast
          AOT_hence \<open>w\<^sub>2 \<Turnstile> p\<close>
            using world_prop_beta[THEN "PossibleWorld.\<forall>E", THEN "\<equiv>E"(1)] by blast
          AOT_thus \<open>w\<^sub>2 \<Turnstile> p & \<not>w\<^sub>2 \<Turnstile> p\<close>
            using 0[THEN "&E"(2)] "&I" by blast
        qed
        AOT_thus \<open>w\<^sub>2 \<Turnstile> \<not>\<exists>u [\<lambda>y p]u\<close>
          by (safe intro!: "coherent:1"[unvarify p, OF "log-prop-prop:2",
                                        THEN "\<equiv>E"(2)])
      next
        AOT_show \<open>w\<^sub>2 \<Turnstile> \<not>\<exists>v [\<lambda>z O!z & z \<noteq>\<^sub>E z]v\<close>
          using nec_not_ex[THEN "PossibleWorld.\<forall>E"] by blast
      qed
    qed
    moreover AOT_have \<open>\<not>x[\<lambda>y p]\<close>
    proof(rule "raa-cor:2")
      AOT_assume \<open>x[\<lambda>y p]\<close>
      AOT_hence "w\<^sub>1 \<Turnstile> [\<lambda>y p] \<approx>\<^sub>E [\<lambda>z O!z & z \<noteq>\<^sub>E z]"
        using x_prop[THEN "&E"(2), THEN "\<forall>E"(1), THEN "\<equiv>E"(1)]
              "prop-prop2:2" by blast
      AOT_hence "\<not>w\<^sub>1 \<Turnstile> \<not>[\<lambda>y p] \<approx>\<^sub>E [\<lambda>z O!z & z \<noteq>\<^sub>E z]"
        using "coherent:2"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)] by blast
      moreover AOT_have "w\<^sub>1 \<Turnstile> \<not>([\<lambda>y p] \<approx>\<^sub>E [\<lambda>z O!z & z \<noteq>\<^sub>E z])"
      proof (safe intro!: "cqt:2" "empty-approx:2"[unvarify F H, THEN RN,
                    THEN "fund:2"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)],
                    THEN "PossibleWorld.\<forall>E",
                    THEN "conj-dist-w:2"[unvarify p q, OF "log-prop-prop:2",
                        OF "log-prop-prop:2", THEN "\<equiv>E"(1)], THEN "\<rightarrow>E"]
                    "conj-dist-w:1"[unvarify p q, OF "log-prop-prop:2",
                                    OF "log-prop-prop:2", THEN "\<equiv>E"(2)] "&I")
        fix u
        AOT_have \<open>w\<^sub>1 \<Turnstile> O!u\<close>
          using Ordinary.\<psi>[THEN RN,
                  THEN "fund:2"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)],
                  THEN "PossibleWorld.\<forall>E"] by simp
        moreover AOT_have \<open>w\<^sub>1 \<Turnstile> [\<lambda>y p]u\<close>
          by (safe intro!: world_prop_beta[THEN "PossibleWorld.\<forall>E", THEN "\<equiv>E"(2)]
                           0[THEN "&E"(1)])
        ultimately AOT_have \<open>w\<^sub>1 \<Turnstile> (O!u & [\<lambda>y p]u)\<close>
          using "conj-dist-w:1"[unvarify p q, OF "log-prop-prop:2",
                                OF "log-prop-prop:2", THEN "\<equiv>E"(2),
                                OF "&I"] by blast
        AOT_hence \<open>\<exists>x w\<^sub>1 \<Turnstile> (O!x & [\<lambda>y p]x)\<close>
          by (rule "\<exists>I")
        AOT_thus \<open>w\<^sub>1 \<Turnstile> \<exists>u [\<lambda>y p]u\<close>
          by (metis "conj-dist-w:6" "intro-elim:3:b")
      next
        AOT_show \<open>w\<^sub>1 \<Turnstile> \<not>\<exists>v [\<lambda>z O!z & z \<noteq>\<^sub>E z]v\<close>
          using "PossibleWorld.\<forall>E" nec_not_ex by fastforce
      qed
      ultimately AOT_show \<open>p & \<not>p\<close> for p
        using "raa-cor:3" by blast
    qed
    ultimately AOT_have \<open>y[\<lambda>y p] & \<not>x[\<lambda>y p]\<close>
      using "&I" by blast
    AOT_hence \<open>\<exists>F (y[F] & \<not>x[F])\<close>
      by (metis "existential:1" "prop-prop2:2")
    AOT_thus \<open>\<exists>F (x[F] & \<not>y[F]) \<or> \<exists>F (y[F] & \<not>x[F])\<close>
      by (rule "\<or>I")
  qed
  ultimately AOT_have \<open>\<diamond>Numbers'(x,[\<lambda>z O!z & z \<noteq>\<^sub>E z]) &
                       \<diamond>Numbers'(y,[\<lambda>z O!z & z \<noteq>\<^sub>E z]) & x \<noteq> y\<close>
    using "&I" by blast
  AOT_thus \<open>\<exists>x\<exists>y (\<diamond>Numbers'(x,[\<lambda>z O!z & z \<noteq>\<^sub>E z]) &
                  \<diamond>Numbers'(y,[\<lambda>z O!z & z \<noteq>\<^sub>E z]) & x \<noteq> y)\<close>
    using "\<exists>I"(2)[where \<beta>=x] "\<exists>I"(2)[where \<beta>=y] by auto
qed

AOT_theorem restricted_identity:
  \<open>x =\<^sub>\<R> y \<equiv> (InDomainOf(x,\<R>) & InDomainOf(y,\<R>) & x = y)\<close>
  by (auto intro!: "\<equiv>I" "\<rightarrow>I" "&I"
             dest: "id-R-thm:2"[THEN "\<rightarrow>E"] "&E"
                   "id-R-thm:3"[THEN "\<rightarrow>E"]
                   "id-R-thm:4"[THEN "\<rightarrow>E", OF "\<or>I"(1), THEN "\<equiv>E"(2)])

AOT_theorem induction': \<open>\<forall>F ([F]0 & \<forall>n([F]n \<rightarrow> [F]n\<^bold>') \<rightarrow> \<forall>n [F]n)\<close>
proof(rule GEN; rule "\<rightarrow>I")
  fix F n
  AOT_assume A: \<open>[F]0 & \<forall>n([F]n \<rightarrow> [F]n\<^bold>')\<close>
  AOT_have \<open>\<forall>n\<forall>m([\<P>]nm \<rightarrow> ([F]n \<rightarrow> [F]m))\<close>
  proof(safe intro!: "Number.GEN" "\<rightarrow>I")
    fix n m
    AOT_assume \<open>[\<P>]nm\<close>
    moreover AOT_have \<open>[\<P>]n n\<^bold>'\<close>
      using "suc-thm".
    ultimately AOT_have m_eq_suc_n: \<open>m = n\<^bold>'\<close>
      using "pred-func:1"[unvarify z, OF "def-suc[den2]", THEN "\<rightarrow>E", OF "&I"]
      by blast
    AOT_assume \<open>[F]n\<close>
    AOT_hence \<open>[F]n\<^bold>'\<close>
      using A[THEN "&E"(2), THEN "Number.\<forall>E", THEN "\<rightarrow>E"] by blast
    AOT_thus \<open>[F]m\<close>
      using m_eq_suc_n[symmetric] "rule=E" by fast
  qed
  AOT_thus \<open>\<forall>n[F]n\<close>
    using induction[THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF "&I", OF A[THEN "&E"(1)]]
    by simp
qed

AOT_define ExtensionOf :: \<open>\<tau> \<Rightarrow> \<Pi> \<Rightarrow> \<phi>\<close> (\<open>ExtensionOf'(_,_')\<close>)
  "exten-property:1": \<open>ExtensionOf(x,[G]) \<equiv>\<^sub>d\<^sub>f A!x & G\<down> & \<forall>F(x[F] \<equiv> \<forall>z([F]z \<equiv> [G]z))\<close>

AOT_define OrdinaryExtensionOf :: \<open>\<tau> \<Rightarrow> \<Pi> \<Rightarrow> \<phi>\<close> (\<open>OrdinaryExtensionOf'(_,_')\<close>)
   \<open>OrdinaryExtensionOf(x,[G]) \<equiv>\<^sub>d\<^sub>f A!x & G\<down> & \<forall>F(x[F] \<equiv> \<forall>z(O!z \<rightarrow> ([F]z \<equiv> [G]z)))\<close>

AOT_theorem BeingOrdinaryExtensionOfDenotes:
  \<open>[\<lambda>x OrdinaryExtensionOf(x,[G])]\<down>\<close>
proof(rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E", OF "&I"])
  AOT_show \<open>[\<lambda>x A!x & G\<down> & [\<lambda>x \<forall>F(x[F] \<equiv> \<forall>z(O!z \<rightarrow> ([F]z \<equiv> [G]z)))]x]\<down>\<close>
    by "cqt:2"
next
  AOT_show \<open>\<box>\<forall>x (A!x & G\<down> & [\<lambda>x \<forall>F (x[F] \<equiv> \<forall>z (O!z \<rightarrow> ([F]z \<equiv> [G]z)))]x \<equiv>
            OrdinaryExtensionOf(x,[G]))\<close>
  proof(safe intro!: RN GEN)
    AOT_modally_strict {
      fix x
      AOT_modally_strict {
        AOT_have \<open>[\<lambda>x \<forall>F (x[F] \<equiv> \<forall>z (O!z \<rightarrow> ([F]z \<equiv> [G]z)))]\<down>\<close>
        proof (safe intro!: "Comprehension_3"[THEN "\<rightarrow>E"] RN GEN
                            "\<rightarrow>I" "\<equiv>I" Ordinary.GEN)
          AOT_modally_strict {
            fix F H u
            AOT_assume \<open>\<box>H \<equiv>\<^sub>E F\<close>
            AOT_hence \<open>\<forall>u([H]u \<equiv> [F]u)\<close>
              using eqE[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2)] "qml:2"[axiom_inst, THEN "\<rightarrow>E"]
              by blast
            AOT_hence 0: \<open>[H]u \<equiv> [F]u\<close> using "Ordinary.\<forall>E" by fast
            {
              AOT_assume \<open>\<forall>u([F]u \<equiv> [G]u)\<close>
              AOT_hence 1: \<open>[F]u \<equiv> [G]u\<close> using "Ordinary.\<forall>E" by fast
              AOT_show \<open>[G]u\<close> if \<open>[H]u\<close> using 0 1 "\<equiv>E"(1) that by blast
              AOT_show \<open>[H]u\<close> if \<open>[G]u\<close> using 0 1 "\<equiv>E"(2) that by blast
            }
            {
              AOT_assume \<open>\<forall>u([H]u \<equiv> [G]u)\<close>
              AOT_hence 1: \<open>[H]u \<equiv> [G]u\<close> using "Ordinary.\<forall>E" by fast
              AOT_show \<open>[G]u\<close> if \<open>[F]u\<close> using 0 1 "\<equiv>E"(1,2) that by blast 
              AOT_show \<open>[F]u\<close> if \<open>[G]u\<close> using 0 1 "\<equiv>E"(1,2) that by blast 
            }
          }
        qed
      }
      AOT_thus \<open>(A!x & G\<down> & [\<lambda>x \<forall>F (x[F] \<equiv> \<forall>z (O!z \<rightarrow> ([F]z \<equiv> [G]z)))]x) \<equiv>
                OrdinaryExtensionOf(x,[G])\<close>
        apply (AOT_subst_def OrdinaryExtensionOf)
        apply (AOT_subst \<open>[\<lambda>x \<forall>F (x[F] \<equiv> \<forall>z (O!z \<rightarrow> ([F]z \<equiv> [G]z)))]x\<close>
                         \<open>\<forall>F (x[F] \<equiv> \<forall>z (O!z \<rightarrow> ([F]z \<equiv> [G]z)))\<close>)
        by (auto intro!: "beta-C-meta"[THEN "\<rightarrow>E"] simp: "oth-class-taut:3:a")
    }
  qed
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

AOT_theorem ConceptOfOrdinaryProperty: \<open>([H] \<Rightarrow> O!) \<rightarrow> [\<lambda>x ConceptOf(x,H)]\<down>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>[H] \<Rightarrow> O!\<close>
  AOT_hence \<open>\<box>\<forall>x([H]x \<rightarrow> O!x)\<close>
    using "F-imp-G"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_hence \<open>\<box>\<box>\<forall>x([H]x \<rightarrow> O!x)\<close>
    using "S5Basic:6"[THEN "\<equiv>E"(1)] by blast
  moreover AOT_have \<open>\<box>\<box>\<forall>x([H]x \<rightarrow> O!x) \<rightarrow>
                     \<box>\<forall>F\<forall>G(\<box>(G \<equiv>\<^sub>E F) \<rightarrow> ([H] \<Rightarrow> [F] \<equiv> [H] \<Rightarrow> [G]))\<close>
  proof(rule RM; safe intro!: "\<rightarrow>I" GEN "\<equiv>I")
    AOT_modally_strict {
      fix F G
      AOT_assume 0: \<open>\<box>\<forall>x([H]x \<rightarrow> O!x)\<close>
      AOT_assume \<open>\<box>G \<equiv>\<^sub>E F\<close>
      AOT_hence 1: \<open>\<box>\<forall>u([G]u \<equiv> [F]u)\<close>
        by (AOT_subst_thm eqE[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I",
              OF "cqt:2[const_var]"[axiom_inst],
              OF "cqt:2[const_var]"[axiom_inst], symmetric])
      {
        AOT_assume \<open>[H] \<Rightarrow> [F]\<close>
        AOT_hence \<open>\<box>\<forall>x([H]x \<rightarrow> [F]x)\<close>
          using "F-imp-G"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
        moreover AOT_modally_strict {
          AOT_assume \<open>\<forall>x([H]x \<rightarrow> O!x)\<close>
          moreover AOT_assume \<open>\<forall>u([G]u \<equiv> [F]u)\<close>
          moreover AOT_assume \<open>\<forall>x([H]x \<rightarrow> [F]x)\<close>
          ultimately AOT_have \<open>[H]x \<rightarrow> [G]x\<close> for x
            by (auto intro!: "\<rightarrow>I" dest!: "\<forall>E"(2) dest: "\<rightarrow>E" "\<equiv>E")
          AOT_hence \<open>\<forall>x([H]x \<rightarrow> [G]x)\<close>
            by (rule GEN)
        }
        ultimately AOT_have \<open>\<box>\<forall>x([H]x \<rightarrow> [G]x)\<close>
          using "RN[prem]"[where
              \<Gamma>="{\<guillemotleft>\<forall>x([H]x \<rightarrow> O!x)\<guillemotright>, \<guillemotleft>\<forall>u([G]u \<equiv> [F]u)\<guillemotright>, \<guillemotleft>\<forall>x([H]x \<rightarrow> [F]x)\<guillemotright>}"]
          using 0 1 by fast
        AOT_thus \<open>[H] \<Rightarrow> [G]\<close>
          by (AOT_subst_def "F-imp-G")
             (safe intro!: "cqt:2" "&I")
      }
      {
        AOT_assume \<open>[H] \<Rightarrow> [G]\<close>
        AOT_hence \<open>\<box>\<forall>x([H]x \<rightarrow> [G]x)\<close>
          using "F-imp-G"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
        moreover AOT_modally_strict {
          AOT_assume \<open>\<forall>x([H]x \<rightarrow> O!x)\<close>
          moreover AOT_assume \<open>\<forall>u([G]u \<equiv> [F]u)\<close>
          moreover AOT_assume \<open>\<forall>x([H]x \<rightarrow> [G]x)\<close>
          ultimately AOT_have \<open>[H]x \<rightarrow> [F]x\<close> for x
            by (auto intro!: "\<rightarrow>I" dest!: "\<forall>E"(2) dest: "\<rightarrow>E" "\<equiv>E")
          AOT_hence \<open>\<forall>x([H]x \<rightarrow> [F]x)\<close>
            by (rule GEN)
        }
        ultimately AOT_have \<open>\<box>\<forall>x([H]x \<rightarrow> [F]x)\<close>
          using "RN[prem]"[where
              \<Gamma>="{\<guillemotleft>\<forall>x([H]x \<rightarrow> O!x)\<guillemotright>, \<guillemotleft>\<forall>u([G]u \<equiv> [F]u)\<guillemotright>, \<guillemotleft>\<forall>x([H]x \<rightarrow> [G]x)\<guillemotright>}"]
          using 0 1 by fast
        AOT_thus \<open>[H] \<Rightarrow> [F]\<close>
          by (AOT_subst_def "F-imp-G")
             (safe intro!: "cqt:2" "&I")
      }
    }
  qed
  ultimately AOT_have \<open>\<box>\<forall>F\<forall>G(\<box>(G \<equiv>\<^sub>E F) \<rightarrow> ([H] \<Rightarrow> [F] \<equiv> [H] \<Rightarrow> [G]))\<close>
    using "\<rightarrow>E" by blast
  AOT_hence 0: \<open>[\<lambda>x \<forall>F(x[F] \<equiv> ([H] \<Rightarrow> [F]))]\<down>\<close>
    using Comprehension_3[THEN "\<rightarrow>E"] by blast
  AOT_show \<open>[\<lambda>x ConceptOf(x,H)]\<down>\<close>
  proof (rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E", OF "&I"])
    AOT_show \<open>[\<lambda>x C!x & [\<lambda>x \<forall>F(x[F] \<equiv> ([H] \<Rightarrow> [F]))]x]\<down>\<close> by "cqt:2"
  next
    AOT_show \<open>\<box>\<forall>x (C!x & [\<lambda>x \<forall>F (x[F] \<equiv> [H] \<Rightarrow> [F])]x \<equiv> ConceptOf(x,H))\<close>
    proof (rule "RN[prem]"[where \<Gamma>=\<open>{\<guillemotleft>[\<lambda>x \<forall>F(x[F] \<equiv> ([H] \<Rightarrow> [F]))]\<down>\<guillemotright>}\<close>, simplified])
      AOT_modally_strict {
        AOT_assume 0: \<open>[\<lambda>x \<forall>F (x[F] \<equiv> [H] \<Rightarrow> [F])]\<down>\<close>
        AOT_show \<open>\<forall>x (C!x & [\<lambda>x \<forall>F (x[F] \<equiv> [H] \<Rightarrow> [F])]x \<equiv> ConceptOf(x,H))\<close>
        proof(safe intro!: GEN "\<equiv>I" "\<rightarrow>I" "&I")
          fix x
          AOT_assume \<open>C!x & [\<lambda>x \<forall>F (x[F] \<equiv> [H] \<Rightarrow> [F])]x\<close>
          AOT_thus \<open>ConceptOf(x,H)\<close>
            by (AOT_subst_def "concept-of-G")
               (auto intro!: "&I" "cqt:2" dest: "&E" "\<beta>\<rightarrow>C")
        next
          fix x
          AOT_assume \<open>ConceptOf(x,H)\<close>
          AOT_hence \<open>C!x & (H\<down> & \<forall>F(x[F] \<equiv> [H] \<Rightarrow> [F]))\<close>
            by (AOT_subst_def (reverse) "concept-of-G")
          AOT_thus \<open>C!x\<close> and \<open>[\<lambda>x \<forall>F(x[F] \<equiv> [H] \<Rightarrow> [F])]x\<close>
            by (auto intro!: "\<beta>\<leftarrow>C" 0 "cqt:2" dest: "&E")
        qed
      }
    next
      AOT_show \<open>\<box>[\<lambda>x \<forall>F(x[F] \<equiv> ([H] \<Rightarrow> [F]))]\<down>\<close>
        using "exist-nec"[THEN "\<rightarrow>E"] 0 by blast
    qed
  qed
qed

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

AOT_theorem conH_enc_ord:
  \<open>([H] \<Rightarrow> O!) \<rightarrow> \<box>\<forall>F \<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<^bold>c\<^sub>H[F] \<equiv> \<^bold>c\<^sub>H[G]))\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>[H] \<Rightarrow> O!\<close>
  AOT_have 0: \<open>\<box>([H] \<Rightarrow> O!)\<close>
    apply (AOT_subst_def "F-imp-G")
    using 0[THEN "\<equiv>\<^sub>d\<^sub>fE"[OF "F-imp-G"]]
    by (auto intro!: "KBasic:3"[THEN "\<equiv>E"(2)] "&I" "exist-nec"[THEN "\<rightarrow>E"]
               dest: "&E" 4[THEN "\<rightarrow>E"])
  moreover AOT_have \<open>\<box>([H] \<Rightarrow> O!) \<rightarrow> \<box>\<forall>F \<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<^bold>c\<^sub>H[F] \<equiv> \<^bold>c\<^sub>H[G]))\<close>
  proof(rule RM; safe intro!: "\<rightarrow>I" GEN)
    AOT_modally_strict {
      fix F G
      AOT_assume \<open>[H] \<Rightarrow> O!\<close>
      AOT_hence 0: \<open>\<box>\<forall>x ([H]x \<rightarrow> O!x)\<close>
        by (safe dest!: "F-imp-G"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E"(2))
      AOT_assume 1: \<open>\<box>G \<equiv>\<^sub>E F\<close>
      AOT_assume \<open>\<^bold>c\<^sub>H[F]\<close>
      AOT_hence \<open>[H] \<Rightarrow> [F]\<close>
        using "conG-lemma:1"[THEN "\<forall>E"(2), THEN "\<equiv>E"(1)] by simp
      AOT_hence 2: \<open>\<box>\<forall>x ([H]x \<rightarrow> [F]x)\<close>
        by (safe dest!: "F-imp-G"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E"(2))
      AOT_modally_strict {
        AOT_assume 0: \<open>\<forall>x ([H]x \<rightarrow> O!x)\<close>
        AOT_assume 1: \<open>\<forall>x ([H]x \<rightarrow> [F]x)\<close>
        AOT_assume 2: \<open>G \<equiv>\<^sub>E F\<close>
        AOT_have \<open>\<forall>x ([H]x \<rightarrow> [G]x)\<close>
        proof(safe intro!: GEN "\<rightarrow>I")
          fix x
          AOT_assume \<open>[H]x\<close>
          AOT_hence \<open>O!x\<close> and \<open>[F]x\<close>
            using 0 1 "\<forall>E"(2) "\<rightarrow>E" by blast+
          AOT_thus \<open>[G]x\<close>
            using 2[THEN eqE[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2)]
                  "\<forall>E"(2) "\<rightarrow>E" "\<equiv>E"(2) calculation by blast
        qed
      }
      AOT_hence \<open>\<box>\<forall>x ([H]x \<rightarrow> [G]x)\<close>
        using "RN[prem]"[where \<Gamma>=\<open>{\<guillemotleft>\<forall>x ([H]x \<rightarrow> O!x)\<guillemotright>,
                               \<guillemotleft>\<forall>x ([H]x \<rightarrow> [F]x)\<guillemotright>,
                               \<guillemotleft>G \<equiv>\<^sub>E F\<guillemotright>}\<close>, simplified] 0 1 2 by fast
      AOT_hence \<open>[H] \<Rightarrow> [G]\<close>
        by (safe intro!: "F-imp-G"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2")
      AOT_hence \<open>\<^bold>c\<^sub>H[G]\<close>
        using "conG-lemma:1"[THEN "\<forall>E"(2), THEN "\<equiv>E"(2)] by simp
    } note 0 = this
    AOT_modally_strict {
      fix F G
      AOT_assume \<open>[H] \<Rightarrow> O!\<close>
      moreover AOT_assume \<open>\<box>G \<equiv>\<^sub>E F\<close>
      moreover AOT_have \<open>\<box>F \<equiv>\<^sub>E G\<close>
        by (AOT_subst \<open>F \<equiv>\<^sub>E G\<close> \<open>G \<equiv>\<^sub>E F\<close>)
            (auto intro!: calculation(2)
                          eqE[THEN "\<equiv>\<^sub>d\<^sub>fI"]
                          "\<equiv>I" "\<rightarrow>I" "&I" "cqt:2" Ordinary.GEN
                  dest!: eqE[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E"(2)
                  dest: "\<equiv>E"(1,2) "Ordinary.\<forall>E")
      ultimately AOT_show \<open>(\<^bold>c\<^sub>H[F] \<equiv> \<^bold>c\<^sub>H[G])\<close>
        using 0 "\<equiv>I" "\<rightarrow>I" by auto
    }
  qed
  ultimately AOT_show \<open>\<box>\<forall>F \<forall>G (\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<^bold>c\<^sub>H[F] \<equiv> \<^bold>c\<^sub>H[G]))\<close>
    using "\<rightarrow>E" by blast
qed

AOT_theorem concept_inclusion_denotes_1:
  \<open>([H] \<Rightarrow> O!) \<rightarrow> [\<lambda>x \<^bold>c\<^sub>H \<preceq> x]\<down>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>[H] \<Rightarrow> O!\<close>
  AOT_show \<open>[\<lambda>x \<^bold>c\<^sub>H \<preceq> x]\<down>\<close>
  proof(rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E", OF "&I"])
    AOT_show \<open>[\<lambda>x C!x & \<forall>F(\<^bold>c\<^sub>H[F] \<rightarrow> x[F])]\<down>\<close>
      by (safe intro!: conjunction_denotes[THEN "\<rightarrow>E", OF "&I"]
                       Comprehension_2'[THEN "\<rightarrow>E"]
                       conH_enc_ord[THEN "\<rightarrow>E", OF 0]) "cqt:2"
  next
    AOT_show \<open>\<box>\<forall>x (C!x & \<forall>F (\<^bold>c\<^sub>H[F] \<rightarrow> x[F]) \<equiv> \<^bold>c\<^sub>H \<preceq> x)\<close>
      by (safe intro!: RN GEN; AOT_subst_def "con:1")
         (auto intro!: "\<equiv>I" "\<rightarrow>I" "&I" "concept-G[concept]" dest: "&E")
  qed
qed

AOT_theorem concept_inclusion_denotes_2:
  \<open>([H] \<Rightarrow> O!) \<rightarrow> [\<lambda>x x \<preceq> \<^bold>c\<^sub>H]\<down>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>[H] \<Rightarrow> O!\<close>
  AOT_show \<open>[\<lambda>x x \<preceq> \<^bold>c\<^sub>H]\<down>\<close>
  proof(rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E", OF "&I"])
    AOT_show \<open>[\<lambda>x C!x & \<forall>F(x[F] \<rightarrow> \<^bold>c\<^sub>H[F])]\<down>\<close>
      by (safe intro!: conjunction_denotes[THEN "\<rightarrow>E", OF "&I"]
                       Comprehension_1'[THEN "\<rightarrow>E"]
                       conH_enc_ord[THEN "\<rightarrow>E", OF 0]) "cqt:2"
  next
    AOT_show \<open>\<box>\<forall>x (C!x & \<forall>F (x[F] \<rightarrow> \<^bold>c\<^sub>H[F]) \<equiv> x \<preceq> \<^bold>c\<^sub>H)\<close>
      by (safe intro!: RN GEN; AOT_subst_def "con:1")
         (auto intro!: "\<equiv>I" "\<rightarrow>I" "&I" "concept-G[concept]" dest: "&E")
  qed
qed

AOT_define ThickForm :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>FormOf'(_,_')\<close>)
  "tform-of": \<open>FormOf(x,G) \<equiv>\<^sub>d\<^sub>f A!x & G\<down> & \<forall>F(x[F] \<equiv> [G] \<Rightarrow> [F])\<close>

AOT_theorem FormOfOrdinaryProperty: \<open>([H] \<Rightarrow> O!) \<rightarrow> [\<lambda>x FormOf(x,H)]\<down>\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>[H] \<Rightarrow> [O!]\<close>
  AOT_show \<open>[\<lambda>x FormOf(x,H)]\<down>\<close>
  proof (rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E", OF "&I"])
    AOT_show \<open>[\<lambda>x ConceptOf(x,H)]\<down>\<close>
      using 0 ConceptOfOrdinaryProperty[THEN "\<rightarrow>E"] by blast
    AOT_show \<open>\<box>\<forall>x (ConceptOf(x,H) \<equiv> FormOf(x,H))\<close>
    proof(safe intro!: RN GEN)
      AOT_modally_strict {
        fix x
        AOT_modally_strict {
          AOT_have \<open>A!x \<equiv> A!x\<close>
            by (simp add: "oth-class-taut:3:a")
          AOT_hence \<open>C!x \<equiv> A!x\<close>
            using "rule-id-df:1[zero]"[OF concepts, OF "oa-exist:2"]
                  "rule=E" id_sym by fast
        }
        AOT_thus \<open>ConceptOf(x,H) \<equiv> FormOf(x,H)\<close>
          by (AOT_subst_def "tform-of";
              AOT_subst_def "concept-of-G";
              AOT_subst \<open>C!x\<close> \<open>A!x\<close>)
             (auto intro!: "\<equiv>I" "\<rightarrow>I" "&I" dest: "&E")
      }
    qed
  qed
qed

end
