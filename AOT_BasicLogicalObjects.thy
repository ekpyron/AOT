(*<*)
theory AOT_BasicLogicalObjects
  imports AOT_PLM
begin
(*>*)

section\<open>Basic Logical Objects\<close>

(* TODO: so far only the parts required for possible world theory *)

AOT_define TruthValueOf :: \<open>\<tau> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (\<open>TruthValueOf'(_,_')\<close>)
  "tv-p": \<open>TruthValueOf(x,p) \<equiv>\<^sub>d\<^sub>f A!x & \<forall>F (x[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q]))\<close>

AOT_theorem "p-has-!tv:1": \<open>\<exists>x TruthValueOf(x,p)\<close>
  using  "tv-p"[THEN "\<equiv>Df"]
  by (AOT_subst \<open>TruthValueOf(x,p)\<close>
                \<open>A!x & \<forall>F (x[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q]))\<close> for: x)
     (simp add: "A-objects"[axiom_inst])


AOT_theorem "p-has-!tv:2": \<open>\<exists>!x TruthValueOf(x,p)\<close>
  using  "tv-p"[THEN "\<equiv>Df"]
  by (AOT_subst \<open>TruthValueOf(x,p)\<close>
                \<open>A!x & \<forall>F (x[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q]))\<close> for: x)
     (simp add: "A-objects!")


AOT_theorem "uni-tv": \<open>\<^bold>\<iota>x TruthValueOf(x,p)\<down>\<close>
  using "A-Exists:2" "RA[2]" "\<equiv>E"(2) "p-has-!tv:2" by blast

AOT_define TheTruthValueOf :: \<open>\<phi> \<Rightarrow> \<kappa>\<^sub>s\<close> (\<open>\<circ>_\<close> [100] 100)
  "the-tv-p": \<open>\<circ>p =\<^sub>d\<^sub>f \<^bold>\<iota>x TruthValueOf(x,p)\<close>

AOT_define PropEnc :: \<open>\<tau> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (infixl \<open>\<^bold>\<Sigma>\<close> 40)
  "prop-enc": \<open>x\<^bold>\<Sigma>p \<equiv>\<^sub>d\<^sub>f x\<down> & x[\<lambda>y p]\<close>

AOT_theorem "tv-id:1": \<open>\<circ>p = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q])))\<close>
proof -
  AOT_have \<open>\<box>\<forall>x(TruthValueOf(x,p)  \<equiv> A!x & \<forall>F (x[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q])))\<close>
    by (rule RN; rule GEN; rule "tv-p"[THEN "\<equiv>Df"])
  AOT_hence \<open>\<^bold>\<iota>x TruthValueOf(x,p) = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q])))\<close>
    using "equiv-desc-eq:3"[THEN "\<rightarrow>E", OF "&I", OF "uni-tv"] by simp
  thus ?thesis
    using "=\<^sub>d\<^sub>fI"(1)[OF "the-tv-p", OF "uni-tv"] by fast
qed

AOT_theorem "tv-id:2": \<open>\<circ>p\<^bold>\<Sigma>p\<close>
proof -
  AOT_modally_strict {
    AOT_have \<open>(p \<equiv> p) & [\<lambda>y p] = [\<lambda>y p]\<close>
      by (auto simp: "prop-prop2:2" "rule=I:1" intro!: "\<equiv>I" "\<rightarrow>I" "&I")
    AOT_hence \<open>\<exists>q ((q \<equiv> p) & [\<lambda>y p] = [\<lambda>y q])\<close>
      using "\<exists>I" by fast
  }
  AOT_hence \<open>\<^bold>\<A>\<exists>q ((q \<equiv> p) & [\<lambda>y p] = [\<lambda>y q])\<close>
    using "RA[2]" by blast
  AOT_hence \<open>\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q])))[\<lambda>y p]\<close>
    by (safe intro!: "desc-nec-encode:1"[unvarify F, THEN "\<equiv>E"(2)] "cqt:2")
  AOT_hence \<open>\<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q])))\<^bold>\<Sigma>p\<close>
    by (safe intro!: "prop-enc"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "A-descriptions")
  AOT_thus \<open>\<circ>p\<^bold>\<Sigma>p\<close>
    by (rule "rule=E"[rotated, OF "tv-id:1"[symmetric]])
qed

(* TODO more theorems *)

AOT_theorem "TV-lem1:1":
  \<open>p \<equiv> \<forall>F(\<exists>q (q & F = [\<lambda>y q]) \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q]))\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I" GEN)
  fix F
  AOT_assume \<open>\<exists>q (q & F = [\<lambda>y q])\<close>
  then AOT_obtain q where \<open>q & F = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
  moreover AOT_assume p
  ultimately AOT_have \<open>(q \<equiv> p) & F = [\<lambda>y q]\<close>
    by (metis "&I" "&E"(1) "&E"(2) "deduction-theorem" "\<equiv>I")
  AOT_thus \<open>\<exists>q ((q \<equiv> p) & F = [\<lambda>y q])\<close> by (rule "\<exists>I")
next
  fix F
  AOT_assume \<open>\<exists>q ((q \<equiv> p) & F = [\<lambda>y q])\<close>
  then AOT_obtain q where \<open>(q \<equiv> p) & F = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
  moreover AOT_assume p
  ultimately AOT_have \<open>q & F = [\<lambda>y q]\<close>
    by (metis "&I" "&E"(1) "&E"(2) "\<equiv>E"(2))
  AOT_thus \<open>\<exists>q (q & F = [\<lambda>y q])\<close> by (rule "\<exists>I")
next
  AOT_assume \<open>\<forall>F (\<exists>q (q & F = [\<lambda>y q]) \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
  AOT_hence \<open>\<exists>q (q & [\<lambda>y p] = [\<lambda>y q]) \<equiv> \<exists>q ((q \<equiv> p) & [\<lambda>y p] = [\<lambda>y q])\<close>
    using "\<forall>E"(1)[rotated, OF "prop-prop2:2"] by blast
  moreover AOT_have \<open>\<exists>q ((q \<equiv> p) & [\<lambda>y p] = [\<lambda>y q])\<close>
    by (rule "\<exists>I"(2)[where \<beta>=p])
       (simp add: "rule=I:1" "&I" "oth-class-taut:3:a" "prop-prop2:2")
  ultimately AOT_have \<open>\<exists>q (q & [\<lambda>y p] = [\<lambda>y q])\<close> using "\<equiv>E"(2) by blast
  then AOT_obtain q where \<open>q & [\<lambda>y p] = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
  AOT_thus \<open>p\<close>
    using "rule=E" "&E"(1) "&E"(2) id_sym "\<equiv>E"(2) "p-identity-thm2:3" by fast
qed

AOT_theorem "TV-lem1:2":
  \<open>\<not>p \<equiv> \<forall>F(\<exists>q (\<not>q & F = [\<lambda>y q]) \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q]))\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I" GEN)
  fix F
  AOT_assume \<open>\<exists>q (\<not>q & F = [\<lambda>y q])\<close>
  then AOT_obtain q where \<open>\<not>q & F = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
  moreover AOT_assume \<open>\<not>p\<close>
  ultimately AOT_have \<open>(q \<equiv> p) & F = [\<lambda>y q]\<close>
    by (metis "&I" "&E"(1) "&E"(2) "deduction-theorem" "\<equiv>I" "raa-cor:3")
  AOT_thus \<open>\<exists>q ((q \<equiv> p) & F = [\<lambda>y q])\<close> by (rule "\<exists>I")
next
  fix F
  AOT_assume \<open>\<exists>q ((q \<equiv> p) & F = [\<lambda>y q])\<close>
  then AOT_obtain q where \<open>(q \<equiv> p) & F = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
  moreover AOT_assume \<open>\<not>p\<close>
  ultimately AOT_have \<open>\<not>q & F = [\<lambda>y q]\<close>
    by (metis "&I" "&E"(1) "&E"(2) "\<equiv>E"(1) "raa-cor:3")
  AOT_thus \<open>\<exists>q (\<not>q & F = [\<lambda>y q])\<close> by (rule "\<exists>I")
next
  AOT_assume \<open>\<forall>F (\<exists>q (\<not>q & F = [\<lambda>y q]) \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
  AOT_hence \<open>\<exists>q (\<not>q & [\<lambda>y p] = [\<lambda>y q]) \<equiv> \<exists>q ((q \<equiv> p) & [\<lambda>y p] = [\<lambda>y q])\<close>
    using "\<forall>E"(1)[rotated, OF "prop-prop2:2"] by blast
  moreover AOT_have \<open>\<exists>q ((q \<equiv> p) & [\<lambda>y p] = [\<lambda>y q])\<close>
    by (rule "\<exists>I"(2)[where \<beta>=p])
       (simp add: "rule=I:1" "&I" "oth-class-taut:3:a" "prop-prop2:2")
  ultimately AOT_have \<open>\<exists>q (\<not>q & [\<lambda>y p] = [\<lambda>y q])\<close> using "\<equiv>E"(2) by blast
  then AOT_obtain q where \<open>\<not>q & [\<lambda>y p] = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
  AOT_thus \<open>\<not>p\<close>
    using "rule=E" "&E"(1) "&E"(2) id_sym "\<equiv>E"(2) "p-identity-thm2:3" by fast
qed


AOT_define TruthValue :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>TruthValue'(_')\<close>)
  "T-value": \<open>TruthValue(x) \<equiv>\<^sub>d\<^sub>f \<exists>p (TruthValueOf(x,p))\<close>

(* TODO more theorems *)

AOT_act_theorem "T-lem:1": \<open>TruthValueOf(\<circ>p, p)\<close>
proof -
  AOT_have \<theta>: \<open>\<circ>p = \<^bold>\<iota>x TruthValueOf(x, p)\<close>
    using "rule-id-df:1" "the-tv-p" "uni-tv" by blast
  moreover AOT_have \<open>\<circ>p\<down>\<close>
    using "t=t-proper:1" calculation "vdash-properties:10" by blast
  ultimately show ?thesis by (metis "rule=E" id_sym "vdash-properties:10" "y-in:3")
qed

AOT_act_theorem "T-lem:2": \<open>\<forall>F (\<circ>p[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q]))\<close>
  using "T-lem:1"[THEN "tv-p"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2)].

AOT_act_theorem "T-lem:3": \<open>\<circ>p\<^bold>\<Sigma>r \<equiv> (r \<equiv> p)\<close>
proof -
  AOT_have \<theta>: \<open>\<circ>p[\<lambda>y r] \<equiv> \<exists>q ((q \<equiv> p) & [\<lambda>y r] = [\<lambda>y q])\<close>
    using "T-lem:2"[THEN "\<forall>E"(1), OF "prop-prop2:2"].
  show ?thesis
  proof(rule "\<equiv>I"; rule "\<rightarrow>I")
    AOT_assume \<open>\<circ>p\<^bold>\<Sigma>r\<close>
    AOT_hence \<open>\<circ>p[\<lambda>y r]\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "&E"(2) "prop-enc")
    AOT_hence \<open>\<exists>q ((q \<equiv> p) & [\<lambda>y r] = [\<lambda>y q])\<close> using \<theta> "\<equiv>E"(1) by blast
    then AOT_obtain q where \<open>(q \<equiv> p) & [\<lambda>y r] = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
    moreover AOT_have \<open>r = q\<close> using calculation
      using "&E"(2) "\<equiv>E"(2) "p-identity-thm2:3" by blast
    ultimately AOT_show \<open>r \<equiv> p\<close>
      by (metis "rule=E" "&E"(1) "\<equiv>E"(6) "oth-class-taut:3:a")
  next
    AOT_assume \<open>r \<equiv> p\<close>
    moreover AOT_have \<open>[\<lambda>y r] = [\<lambda>y r]\<close>
      by (simp add: "rule=I:1" "prop-prop2:2")
    ultimately AOT_have \<open>(r \<equiv> p) & [\<lambda>y r] = [\<lambda>y r]\<close> using "&I" by blast
    AOT_hence \<open>\<exists>q ((q \<equiv> p) & [\<lambda>y r] = [\<lambda>y q])\<close> by (rule "\<exists>I"(2)[where \<beta>=r])
    AOT_hence \<open>\<circ>p[\<lambda>y r]\<close> using \<theta> "\<equiv>E"(2) by blast
    AOT_thus \<open>\<circ>p\<^bold>\<Sigma>r\<close>
      by (metis "\<equiv>\<^sub>d\<^sub>fI" "&I" "prop-enc" "russell-axiom[enc,1].\<psi>_denotes_asm")
  qed
qed

AOT_act_theorem "T-lem:4": \<open>TruthValueOf(x, p) \<equiv> x = \<circ>p\<close>
proof -
  AOT_have \<open>\<forall>x (x = \<^bold>\<iota>x TruthValueOf(x, p) \<equiv> \<forall>z (TruthValueOf(z, p) \<equiv> z = x))\<close>
    by (simp add: "fund-cont-desc" GEN)
  moreover AOT_have \<open>\<circ>p\<down>\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" "tv-id:2" "&E"(1) "prop-enc" by blast
  ultimately AOT_have
    \<open>(\<circ>p = \<^bold>\<iota>x TruthValueOf(x, p)) \<equiv> \<forall>z (TruthValueOf(z, p) \<equiv> z = \<circ>p)\<close>
    using "\<forall>E"(1) by blast
  AOT_hence \<open>\<forall>z (TruthValueOf(z, p) \<equiv> z = \<circ>p)\<close>
    using "\<equiv>E"(1) "rule-id-df:1" "the-tv-p" "uni-tv" by blast
  AOT_thus \<open>TruthValueOf(x, p) \<equiv> x = \<circ>p\<close> using "\<forall>E"(2) by blast
qed


(* TODO more theorems *)

AOT_theorem "TV-lem2:1":
  \<open>(A!x & \<forall>F (x[F] \<equiv> \<exists>q (q & F = [\<lambda>y q]))) \<rightarrow> TruthValue(x)\<close>
proof(safe intro!: "\<rightarrow>I" "T-value"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "tv-p"[THEN "\<equiv>\<^sub>d\<^sub>fI"]
                   "\<exists>I"(1)[rotated, OF "log-prop-prop:2"])
  AOT_assume \<open>[A!]x & \<forall>F (x[F] \<equiv> \<exists>q (q & F = [\<lambda>y q]))\<close>
  AOT_thus \<open>[A!]x & \<forall>F (x[F] \<equiv> \<exists>q ((q \<equiv> (\<forall>p (p \<rightarrow> p))) & F = [\<lambda>y q]))\<close>
    apply (AOT_subst \<open>\<exists>q ((q \<equiv> (\<forall>p (p \<rightarrow> p))) & F = [\<lambda>y q])\<close>
                     \<open>\<exists>q (q & F = [\<lambda>y q])\<close> for: F :: \<open><\<kappa>>\<close>)
     apply (AOT_subst \<open>q \<equiv> \<forall>p (p \<rightarrow>p)\<close> \<open>q\<close> for: q)
    apply (metis (no_types, lifting) "\<rightarrow>I" "\<equiv>I" "\<equiv>E"(2) GEN)
    by (auto simp: "cqt-further:7")
qed

AOT_theorem "TV-lem2:2":
  \<open>(A!x & \<forall>F (x[F] \<equiv> \<exists>q (\<not>q & F = [\<lambda>y q]))) \<rightarrow> TruthValue(x)\<close>
proof(safe intro!: "\<rightarrow>I" "T-value"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "tv-p"[THEN "\<equiv>\<^sub>d\<^sub>fI"]
                   "\<exists>I"(1)[rotated, OF "log-prop-prop:2"])
  AOT_assume \<open>[A!]x & \<forall>F (x[F] \<equiv> \<exists>q (\<not>q & F = [\<lambda>y q]))\<close>
  AOT_thus \<open>[A!]x & \<forall>F (x[F] \<equiv> \<exists>q ((q \<equiv> (\<exists>p (p & \<not>p))) & F = [\<lambda>y q]))\<close>
    apply (AOT_subst \<open>\<exists>q ((q \<equiv> (\<exists>p (p & \<not>p))) & F = [\<lambda>y q])\<close>
                     \<open>\<exists>q (\<not>q & F = [\<lambda>y q])\<close> for: F :: \<open><\<kappa>>\<close>)
     apply (AOT_subst \<open>q \<equiv> \<exists>p (p & \<not>p)\<close> \<open>\<not>q\<close> for: q)
      apply (metis (no_types, lifting)
        "\<rightarrow>I" "\<exists>E" "\<equiv>E"(1) "\<equiv>I" "raa-cor:1" "raa-cor:3")
    by (auto simp add: "cqt-further:7")
qed

AOT_define TheTrue :: \<kappa>\<^sub>s (\<open>\<top>\<close>)
  "the-true:1": \<open>\<top> =\<^sub>d\<^sub>f \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(p & F = [\<lambda>y p])))\<close>
AOT_define TheFalse :: \<kappa>\<^sub>s (\<open>\<bottom>\<close>)
  "the-true:2": \<open>\<bottom> =\<^sub>d\<^sub>f \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(\<not>p & F = [\<lambda>y p])))\<close>


AOT_theorem "the-true:3": \<open>\<top> \<noteq> \<bottom>\<close>
proof(safe intro!: "ab-obey:2"[unvarify x y, THEN "\<rightarrow>E", rotated 2, OF "\<or>I"(1)]
                   "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>[\<lambda>x \<forall>q(q \<rightarrow> q)]\<guillemotright>\<close>] "&I" "prop-prop2:2")
  AOT_have false_def: \<open>\<bottom> = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(\<not>p & F = [\<lambda>y p])))\<close>
    by (simp add: "A-descriptions" "rule-id-df:1[zero]" "the-true:2")
  moreover AOT_show false_den: \<open>\<bottom>\<down>\<close>
    by (meson "\<rightarrow>E" "t=t-proper:1" "A-descriptions"
              "rule-id-df:1[zero]" "the-true:2")
  ultimately AOT_have false_prop: \<open>\<^bold>\<A>(A!\<bottom> & \<forall>F (\<bottom>[F] \<equiv> \<exists>p(\<not>p & F = [\<lambda>y p])))\<close>
    using "nec-hintikka-scheme"[unvarify x, THEN "\<equiv>E"(1), THEN "&E"(1)] by blast
  AOT_hence \<open>\<^bold>\<A>\<forall>F (\<bottom>[F] \<equiv> \<exists>p(\<not>p & F = [\<lambda>y p]))\<close>
    using "Act-Basic:2" "&E"(2) "\<equiv>E"(1) by blast
  AOT_hence \<open>\<forall>F \<^bold>\<A>(\<bottom>[F] \<equiv> \<exists>p(\<not>p & F = [\<lambda>y p]))\<close>
    using "\<equiv>E"(1) "logic-actual-nec:3"[axiom_inst] by blast
  AOT_hence false_enc_cond:
    \<open>\<^bold>\<A>(\<bottom>[\<lambda>x \<forall>q(q \<rightarrow> q)] \<equiv> \<exists>p(\<not>p & [\<lambda>x \<forall>q(q \<rightarrow> q)] = [\<lambda>y p]))\<close>
    using "\<forall>E"(1)[rotated, OF "prop-prop2:2"] by blast

  AOT_have true_def: \<open>\<top> = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(p & F = [\<lambda>y p])))\<close>
    by (simp add: "A-descriptions" "rule-id-df:1[zero]" "the-true:1")
  moreover AOT_show true_den: \<open>\<top>\<down>\<close>
    by (meson "t=t-proper:1" "A-descriptions" "rule-id-df:1[zero]" "the-true:1" "\<rightarrow>E")
  ultimately AOT_have true_prop: \<open>\<^bold>\<A>(A!\<top> & \<forall>F (\<top>[F] \<equiv> \<exists>p(p & F = [\<lambda>y p])))\<close>
    using "nec-hintikka-scheme"[unvarify x, THEN "\<equiv>E"(1), THEN "&E"(1)]  by blast
  AOT_hence \<open>\<^bold>\<A>\<forall>F (\<top>[F] \<equiv> \<exists>p(p & F = [\<lambda>y p]))\<close>
    using "Act-Basic:2" "&E"(2) "\<equiv>E"(1) by blast
  AOT_hence \<open>\<forall>F \<^bold>\<A>(\<top>[F] \<equiv> \<exists>p(p & F = [\<lambda>y p]))\<close>
    using "\<equiv>E"(1) "logic-actual-nec:3"[axiom_inst] by blast
  AOT_hence \<open>\<^bold>\<A>(\<top>[\<lambda>x \<forall>q(q \<rightarrow> q)] \<equiv> \<exists>p(p & [\<lambda>x \<forall>q(q \<rightarrow> q)] = [\<lambda>y p]))\<close>
    using "\<forall>E"(1)[rotated, OF "prop-prop2:2"] by blast
  moreover AOT_have \<open>\<^bold>\<A>\<exists>p(p & [\<lambda>x \<forall>q(q \<rightarrow> q)] = [\<lambda>y p])\<close>
    by (safe intro!: "nec-imp-act"[THEN "\<rightarrow>E"] RN "\<exists>I"(1)[where \<tau>="\<guillemotleft>\<forall>q(q \<rightarrow> q)\<guillemotright>"] "&I"
                     GEN "\<rightarrow>I" "log-prop-prop:2" "rule=I:1" "prop-prop2:2")
  ultimately AOT_have \<open>\<^bold>\<A>(\<top>[\<lambda>x \<forall>q(q \<rightarrow> q)])\<close>
    using "Act-Basic:5" "\<equiv>E"(1,2) by blast
  AOT_thus \<open>\<top>[\<lambda>x \<forall>q(q \<rightarrow> q)]\<close>
    using "en-eq:10[1]"[unvarify x\<^sub>1 F, THEN "\<equiv>E"(1)] true_den "prop-prop2:2" by blast

  AOT_show \<open>\<not>\<bottom>[\<lambda>x \<forall>q(q \<rightarrow> q)]\<close>
  proof(rule "raa-cor:2")
    AOT_assume \<open>\<bottom>[\<lambda>x \<forall>q(q \<rightarrow> q)]\<close>
    AOT_hence \<open>\<^bold>\<A>\<bottom>[\<lambda>x \<forall>q(q \<rightarrow> q)]\<close>
      using "en-eq:10[1]"[unvarify x\<^sub>1 F, THEN "\<equiv>E"(2)]
            false_den "prop-prop2:2" by blast
    AOT_hence \<open>\<^bold>\<A>\<exists>p(\<not>p & [\<lambda>x \<forall>q(q \<rightarrow> q)] = [\<lambda>y p])\<close>
      using false_enc_cond "Act-Basic:5" "\<equiv>E"(1) by blast
    AOT_hence \<open>\<exists>p \<^bold>\<A>(\<not>p & [\<lambda>x \<forall>q(q \<rightarrow> q)] = [\<lambda>y p])\<close>
      using "Act-Basic:10" "\<equiv>E"(1) by blast
    then AOT_obtain p where p_prop: \<open>\<^bold>\<A>(\<not>p & [\<lambda>x \<forall>q(q \<rightarrow> q)] = [\<lambda>y p])\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>\<^bold>\<A>[\<lambda>x \<forall>q(q \<rightarrow> q)] = [\<lambda>y p]\<close>
      by (metis "Act-Basic:2" "&E"(2) "\<equiv>E"(1))
    AOT_hence \<open>[\<lambda>x \<forall>q(q \<rightarrow> q)] = [\<lambda>y p]\<close>
      using "id-act:1"[unvarify \<alpha> \<beta>, THEN "\<equiv>E"(2)] "prop-prop2:2" by blast
    AOT_hence \<open>(\<forall>q(q \<rightarrow> q)) = p\<close>
      using "p-identity-thm2:3"[unvarify p, THEN "\<equiv>E"(2)]
            "log-prop-prop:2" by blast
    moreover AOT_have \<open>\<^bold>\<A>\<not>p\<close> using p_prop
      using "Act-Basic:2" "&E"(1) "\<equiv>E"(1) by blast
    ultimately AOT_have \<open>\<^bold>\<A>\<not>\<forall>q(q \<rightarrow> q)\<close>
      by (metis "Act-Sub:1" "\<equiv>E"(1,2) "raa-cor:3" "rule=E")
    moreover AOT_have \<open>\<not>\<^bold>\<A>\<not>\<forall>q(q \<rightarrow> q)\<close>
      by (meson "Act-Sub:1" "RA[2]" "if-p-then-p" "\<equiv>E"(1) "universal-cor")
    ultimately AOT_show \<open>\<^bold>\<A>\<not>\<forall>q(q \<rightarrow> q) & \<not>\<^bold>\<A>\<not>\<forall>q(q \<rightarrow> q)\<close>
      using "&I" by blast
  qed
qed

AOT_act_theorem "T-T-value:1": \<open>TruthValue(\<top>)\<close>
proof -
  AOT_have true_def: \<open>\<top> = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(p & F = [\<lambda>y p])))\<close>
    by (simp add: "A-descriptions" "rule-id-df:1[zero]" "the-true:1")
  AOT_hence true_den: \<open>\<top>\<down>\<close>
    using "t=t-proper:1" "vdash-properties:6" by blast
  AOT_show \<open>TruthValue(\<top>)\<close>
    using "y-in:2"[unvarify z, OF true_den, THEN "\<rightarrow>E", OF true_def]
          "TV-lem2:1"[unvarify x, OF true_den, THEN "\<rightarrow>E"] by blast
qed

AOT_act_theorem "T-T-value:2": \<open>TruthValue(\<bottom>)\<close>
proof -
  AOT_have false_def: \<open>\<bottom> = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(\<not>p & F = [\<lambda>y p])))\<close>
    by (simp add: "A-descriptions" "rule-id-df:1[zero]" "the-true:2")
  AOT_hence false_den: \<open>\<bottom>\<down>\<close>
    using "t=t-proper:1" "vdash-properties:6" by blast
  AOT_show \<open>TruthValue(\<bottom>)\<close>
    using "y-in:2"[unvarify z, OF false_den, THEN "\<rightarrow>E", OF false_def]
          "TV-lem2:2"[unvarify x, OF false_den, THEN "\<rightarrow>E"] by blast
qed

AOT_theorem "two-T": \<open>\<exists>x\<exists>y(TruthValue(x) & TruthValue(y) & x \<noteq> y &
                           \<forall>z (TruthValue(z) \<rightarrow> z = x \<or> z = y))\<close>
proof -
  AOT_obtain a where a_prop: \<open>A!a & \<forall>F (a[F] \<equiv> \<exists>p (p & F = [\<lambda>y p]))\<close>
    using "A-objects"[axiom_inst] "\<exists>E"[rotated] by fast
  AOT_obtain b where b_prop: \<open>A!b & \<forall>F (b[F] \<equiv> \<exists>p (\<not>p & F = [\<lambda>y p]))\<close>
    using "A-objects"[axiom_inst] "\<exists>E"[rotated] by fast
  AOT_obtain p where p: p
    by (metis "log-prop-prop:2" "raa-cor:3" "rule-ui:1" "universal-cor")
  show ?thesis
  proof(rule "\<exists>I"(2)[where \<beta>=a]; rule "\<exists>I"(2)[where \<beta>=b];
        safe intro!: "&I" GEN "\<rightarrow>I")
    AOT_show \<open>TruthValue(a)\<close>
      using "TV-lem2:1" a_prop "vdash-properties:10" by blast
  next
    AOT_show \<open>TruthValue(b)\<close>
      using "TV-lem2:2" b_prop "vdash-properties:10" by blast
  next
    AOT_show \<open>a \<noteq> b\<close>
    proof(rule "ab-obey:2"[THEN "\<rightarrow>E", OF "\<or>I"(1)])
      AOT_show \<open>\<exists>F (a[F] & \<not>b[F])\<close>
      proof(rule "\<exists>I"(1)[where \<tau>="\<guillemotleft>[\<lambda>y p]\<guillemotright>"]; rule "&I" "prop-prop2:2")
        AOT_show \<open>a[\<lambda>y p]\<close>
          by(safe intro!: "\<exists>I"(2)[where \<beta>=p] "&I" p "rule=I:1"[OF "prop-prop2:2"]
              a_prop[THEN "&E"(2), THEN "\<forall>E"(1), THEN "\<equiv>E"(2), OF "prop-prop2:2"])
      next
        AOT_show \<open>\<not>b[\<lambda>y p]\<close>
        proof (rule "raa-cor:2")
          AOT_assume \<open>b[\<lambda>y p]\<close>
          AOT_hence \<open>\<exists>q (\<not>q & [\<lambda>y p] = [\<lambda>y q])\<close>
            using "\<forall>E"(1)[rotated, OF "prop-prop2:2", THEN "\<equiv>E"(1)]
                  b_prop[THEN "&E"(2)] by fast
          then AOT_obtain q where \<open>\<not>q & [\<lambda>y p] = [\<lambda>y q]\<close>
            using "\<exists>E"[rotated] by blast
          AOT_hence \<open>\<not>p\<close>
            by (metis "rule=E" "&E"(1) "&E"(2) "deduction-theorem" "\<equiv>I"
                      "\<equiv>E"(2) "p-identity-thm2:3" "raa-cor:3")
          AOT_thus \<open>p & \<not>p\<close> using p "&I" by blast
        qed
      qed
    qed
  next
    fix z
    AOT_assume \<open>TruthValue(z)\<close>
    AOT_hence \<open>\<exists>p (TruthValueOf(z, p))\<close>
      by (metis "\<equiv>\<^sub>d\<^sub>fE" "T-value")
    then AOT_obtain p where \<open>TruthValueOf(z, p)\<close> using "\<exists>E"[rotated] by blast
    AOT_hence z_prop: \<open>A!z & \<forall>F (z[F] \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
      using "\<equiv>\<^sub>d\<^sub>fE" "tv-p" by blast
    {
      AOT_assume p: \<open>p\<close>
      AOT_have \<open>z = a\<close>
      proof(rule "ab-obey:1"[THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF "&I",
                             OF z_prop[THEN "&E"(1)], OF a_prop[THEN "&E"(1)]];
            rule GEN)
        fix G
        AOT_have \<open>z[G] \<equiv> \<exists>q ((q \<equiv> p) & G = [\<lambda>y q])\<close>
          using z_prop[THEN "&E"(2)] "\<forall>E"(2) by blast
        also AOT_have \<open>\<exists>q ((q \<equiv> p) & G = [\<lambda>y q]) \<equiv> \<exists>q (q & G = [\<lambda>y q])\<close>
          using "TV-lem1:1"[THEN "\<equiv>E"(1), OF p, THEN "\<forall>E"(2)[where \<beta>=G], symmetric].
        also AOT_have \<open>\<dots> \<equiv> a[G]\<close>
          using a_prop[THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=G], symmetric].
        finally AOT_show \<open>z[G] \<equiv> a[G]\<close>.
      qed
      AOT_hence \<open>z = a \<or> z = b\<close> by (rule "\<or>I")
    }
    moreover {
      AOT_assume notp: \<open>\<not>p\<close>
      AOT_have \<open>z = b\<close>
      proof(rule "ab-obey:1"[THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF "&I",
                             OF z_prop[THEN "&E"(1)], OF b_prop[THEN "&E"(1)]];
            rule GEN)
        fix G
        AOT_have \<open>z[G] \<equiv> \<exists>q ((q \<equiv> p) & G = [\<lambda>y q])\<close>
          using z_prop[THEN "&E"(2)] "\<forall>E"(2) by blast
        also AOT_have \<open>\<exists>q ((q \<equiv> p) & G = [\<lambda>y q]) \<equiv> \<exists>q (\<not>q & G = [\<lambda>y q])\<close>
          using "TV-lem1:2"[THEN "\<equiv>E"(1), OF notp, THEN "\<forall>E"(2), symmetric].
        also AOT_have \<open>\<dots> \<equiv> b[G]\<close>
          using b_prop[THEN "&E"(2), THEN "\<forall>E"(2), symmetric].
        finally AOT_show \<open>z[G] \<equiv> b[G]\<close>.
      qed
      AOT_hence \<open>z = a \<or> z = b\<close> by (rule "\<or>I")
    }
    ultimately AOT_show \<open>z = a \<or> z = b\<close>
      by (metis "reductio-aa:1")
  qed
qed

AOT_act_theorem "valueof-facts:1": \<open>TruthValueOf(x, p) \<rightarrow> (p \<equiv> x = \<top>)\<close>
proof(safe intro!: "\<rightarrow>I" dest!: "tv-p"[THEN "\<equiv>\<^sub>d\<^sub>fE"])
  AOT_assume \<theta>: \<open>[A!]x & \<forall>F (x[F] \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
  AOT_have a: \<open>A!\<top>\<close>
    using "\<exists>E" "T-T-value:1" "T-value" "&E"(1) "\<equiv>\<^sub>d\<^sub>fE" "tv-p" by blast
  AOT_have true_def: \<open>\<top> = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(p & F = [\<lambda>y p])))\<close>
    by (simp add: "A-descriptions" "rule-id-df:1[zero]" "the-true:1")
  AOT_hence true_den: \<open>\<top>\<down>\<close>
    using "t=t-proper:1" "vdash-properties:6" by blast
  AOT_have b: \<open>\<forall>F (\<top>[F] \<equiv> \<exists>q (q & F = [\<lambda>y q]))\<close>
    using "y-in:2"[unvarify z, OF true_den, THEN "\<rightarrow>E", OF true_def] "&E" by blast
  AOT_show \<open>p \<equiv> x = \<top>\<close>
  proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
    AOT_assume p
    AOT_hence \<open>\<forall>F (\<exists>q (q & F = [\<lambda>y q]) \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
      using "TV-lem1:1"[THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>\<forall>F(\<top>[F] \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
      using b "cqt-basic:10"[THEN "\<rightarrow>E", OF "&I", OF b] by fast
    AOT_hence c: \<open>\<forall>F(\<exists>q((q \<equiv> p) & F = [\<lambda>y q]) \<equiv> \<top>[F])\<close>
      using "cqt-basic:11"[THEN "\<equiv>E"(1)] by fast
    AOT_hence \<open>\<forall>F (x[F] \<equiv> \<top>[F])\<close>
      using "cqt-basic:10"[THEN "\<rightarrow>E", OF "&I", OF \<theta>[THEN "&E"(2)]] by fast
    AOT_thus \<open>x = \<top>\<close>
      by (rule "ab-obey:1"[unvarify y, OF true_den, THEN "\<rightarrow>E", THEN "\<rightarrow>E",
                           OF "&I", OF \<theta>[THEN "&E"(1)], OF a])
  next
    AOT_assume \<open>x = \<top>\<close>
    AOT_hence d: \<open>\<forall>F (\<top>[F] \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
      using "rule=E" \<theta>[THEN "&E"(2)] by fast
    AOT_have \<open>\<forall>F (\<exists>q (q & F = [\<lambda>y q]) \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
      using "cqt-basic:10"[THEN "\<rightarrow>E", OF "&I",
              OF b[THEN "cqt-basic:11"[THEN "\<equiv>E"(1)]], OF d].
    AOT_thus p using "TV-lem1:1"[THEN "\<equiv>E"(2)] by blast
  qed
qed

AOT_act_theorem "valueof-facts:2": \<open>TruthValueOf(x, p) \<rightarrow> (\<not>p \<equiv> x = \<bottom>)\<close>
proof(safe intro!: "\<rightarrow>I" dest!: "tv-p"[THEN "\<equiv>\<^sub>d\<^sub>fE"])
  AOT_assume \<theta>: \<open>[A!]x & \<forall>F (x[F] \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
  AOT_have a: \<open>A!\<bottom>\<close>
    using "\<exists>E" "T-T-value:2" "T-value" "&E"(1) "\<equiv>\<^sub>d\<^sub>fE" "tv-p" by blast
  AOT_have false_def: \<open>\<bottom> = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(\<not>p & F = [\<lambda>y p])))\<close>
    by (simp add: "A-descriptions" "rule-id-df:1[zero]" "the-true:2")
  AOT_hence false_den: \<open>\<bottom>\<down>\<close>
    using "t=t-proper:1" "vdash-properties:6" by blast
  AOT_have b: \<open>\<forall>F (\<bottom>[F] \<equiv> \<exists>q (\<not>q & F = [\<lambda>y q]))\<close>
    using "y-in:2"[unvarify z, OF false_den, THEN "\<rightarrow>E", OF false_def] "&E" by blast
  AOT_show \<open>\<not>p \<equiv> x = \<bottom>\<close>
  proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
    AOT_assume \<open>\<not>p\<close>
    AOT_hence \<open>\<forall>F (\<exists>q (\<not>q & F = [\<lambda>y q]) \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
      using "TV-lem1:2"[THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>\<forall>F(\<bottom>[F] \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
      using b "cqt-basic:10"[THEN "\<rightarrow>E", OF "&I", OF b] by fast
    AOT_hence c: \<open>\<forall>F(\<exists>q((q \<equiv> p) & F = [\<lambda>y q]) \<equiv> \<bottom>[F])\<close>
      using "cqt-basic:11"[THEN "\<equiv>E"(1)] by fast
    AOT_hence \<open>\<forall>F (x[F] \<equiv> \<bottom>[F])\<close>
      using "cqt-basic:10"[THEN "\<rightarrow>E", OF "&I", OF \<theta>[THEN "&E"(2)]] by fast
    AOT_thus \<open>x = \<bottom>\<close>
      by (rule "ab-obey:1"[unvarify y, OF false_den, THEN "\<rightarrow>E", THEN "\<rightarrow>E",
                           OF "&I", OF \<theta>[THEN "&E"(1)], OF a])
  next
    AOT_assume \<open>x = \<bottom>\<close>
    AOT_hence d: \<open>\<forall>F (\<bottom>[F] \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
      using "rule=E" \<theta>[THEN "&E"(2)] by fast
    AOT_have \<open>\<forall>F (\<exists>q (\<not>q & F = [\<lambda>y q]) \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
      using "cqt-basic:10"[THEN "\<rightarrow>E", OF "&I",
                OF b[THEN "cqt-basic:11"[THEN "\<equiv>E"(1)]], OF d].
    AOT_thus \<open>\<not>p\<close> using "TV-lem1:2"[THEN "\<equiv>E"(2)] by blast
  qed
qed

AOT_act_theorem "q-True:1": \<open>p \<equiv> (\<circ>p = \<top>)\<close>
  apply (rule "valueof-facts:1"[unvarify x, THEN "\<rightarrow>E", rotated, OF "T-lem:1"])
  using "\<equiv>\<^sub>d\<^sub>fE" "tv-id:2" "&E"(1) "prop-enc" by blast

AOT_act_theorem "q-True:2": \<open>\<not>p \<equiv> (\<circ>p = \<bottom>)\<close>
  apply (rule "valueof-facts:2"[unvarify x, THEN "\<rightarrow>E", rotated, OF "T-lem:1"])
  using "\<equiv>\<^sub>d\<^sub>fE" "tv-id:2" "&E"(1) "prop-enc" by blast

AOT_act_theorem "q-True:3": \<open>p \<equiv> \<top>\<^bold>\<Sigma>p\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume p
  AOT_hence \<open>\<circ>p = \<top>\<close> by (metis "\<equiv>E"(1) "q-True:1")
  moreover AOT_have \<open>\<circ>p\<^bold>\<Sigma>p\<close>
    by (simp add: "tv-id:2")
  ultimately AOT_show \<open>\<top>\<^bold>\<Sigma>p\<close>
    using "rule=E" "T-lem:4" by fast
next
  AOT_have true_def: \<open>\<top> = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(p & F = [\<lambda>y p])))\<close>
    by (simp add: "A-descriptions" "rule-id-df:1[zero]" "the-true:1")
  AOT_hence true_den: \<open>\<top>\<down>\<close>
    using "t=t-proper:1" "vdash-properties:6" by blast
  AOT_have b: \<open>\<forall>F (\<top>[F] \<equiv> \<exists>q (q & F = [\<lambda>y q]))\<close>
    using "y-in:2"[unvarify z, OF true_den, THEN "\<rightarrow>E", OF true_def] "&E" by blast

  AOT_assume \<open>\<top>\<^bold>\<Sigma>p\<close>
  AOT_hence \<open>\<top>[\<lambda>y p]\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "&E"(2) "prop-enc")
  AOT_hence \<open>\<exists>q (q & [\<lambda>y p] = [\<lambda>y q])\<close>
    using b[THEN "\<forall>E"(1), OF "prop-prop2:2", THEN "\<equiv>E"(1)] by blast
  then AOT_obtain q where \<open>q & [\<lambda>y p] = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
  AOT_thus \<open>p\<close>
    using "rule=E" "&E"(1) "&E"(2) id_sym "\<equiv>E"(2) "p-identity-thm2:3" by fast
qed


AOT_act_theorem "q-True:5": \<open>\<not>p \<equiv> \<bottom>\<^bold>\<Sigma>p\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>\<not>p\<close>
  AOT_hence \<open>\<circ>p = \<bottom>\<close> by (metis "\<equiv>E"(1) "q-True:2")
  moreover AOT_have \<open>\<circ>p\<^bold>\<Sigma>p\<close>
    by (simp add: "tv-id:2")
  ultimately AOT_show \<open>\<bottom>\<^bold>\<Sigma>p\<close>
    using "rule=E" "T-lem:4" by fast
next
  AOT_have false_def: \<open>\<bottom> = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(\<not>p & F = [\<lambda>y p])))\<close>
    by (simp add: "A-descriptions" "rule-id-df:1[zero]" "the-true:2")
  AOT_hence false_den: \<open>\<bottom>\<down>\<close>
    using "t=t-proper:1" "vdash-properties:6" by blast
  AOT_have b: \<open>\<forall>F (\<bottom>[F] \<equiv> \<exists>q (\<not>q & F = [\<lambda>y q]))\<close>
    using "y-in:2"[unvarify z, OF false_den, THEN "\<rightarrow>E", OF false_def] "&E" by blast

  AOT_assume \<open>\<bottom>\<^bold>\<Sigma>p\<close>
  AOT_hence \<open>\<bottom>[\<lambda>y p]\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "&E"(2) "prop-enc")
  AOT_hence \<open>\<exists>q (\<not>q & [\<lambda>y p] = [\<lambda>y q])\<close>
    using b[THEN "\<forall>E"(1), OF "prop-prop2:2", THEN "\<equiv>E"(1)] by blast
  then AOT_obtain q where \<open>\<not>q & [\<lambda>y p] = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
  AOT_thus \<open>\<not>p\<close>
    using "rule=E" "&E"(1) "&E"(2) id_sym "\<equiv>E"(2) "p-identity-thm2:3" by fast
qed

AOT_act_theorem "q-True:4": \<open>p \<equiv> \<not>(\<bottom>\<^bold>\<Sigma>p)\<close>
  using "q-True:5"
  by (metis "deduction-theorem" "\<equiv>I" "\<equiv>E"(2) "\<equiv>E"(4) "raa-cor:3")

AOT_act_theorem "q-True:6": \<open>\<not>p \<equiv> \<not>(\<top>\<^bold>\<Sigma>p)\<close>
  using "\<equiv>E"(1) "oth-class-taut:4:b" "q-True:3" by blast

AOT_define ExtensionOf :: \<open>\<tau> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (\<open>ExtensionOf'(_,_')\<close>)
  "exten-p": \<open>ExtensionOf(x,p) \<equiv>\<^sub>d\<^sub>f A!x &
                                   \<forall>F (x[F] \<rightarrow> Propositional([F])) &
                                   \<forall>q ((x\<^bold>\<Sigma>q) \<equiv> (q \<equiv> p))\<close>

AOT_theorem "extof-e": \<open>ExtensionOf(x, p) \<equiv> TruthValueOf(x, p)\<close>
proof (safe intro!: "\<equiv>I" "\<rightarrow>I" "tv-p"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "exten-p"[THEN "\<equiv>\<^sub>d\<^sub>fI"]
            dest!: "tv-p"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "exten-p"[THEN "\<equiv>\<^sub>d\<^sub>fE"])
  AOT_assume 1: \<open>[A!]x & \<forall>F (x[F] \<rightarrow> Propositional([F])) & \<forall>q (x \<^bold>\<Sigma> q \<equiv> (q \<equiv> p))\<close>
  AOT_hence \<theta>: \<open>[A!]x & \<forall>F (x[F] \<rightarrow> \<exists>q(F = [\<lambda>y q])) & \<forall>q (x \<^bold>\<Sigma> q \<equiv> (q \<equiv> p))\<close>
    by (AOT_subst \<open>\<exists>q(F = [\<lambda>y q])\<close> \<open>Propositional([F])\<close> for: F :: \<open><\<kappa>>\<close>)
       (auto simp add: "df-rules-formulas[3]" "df-rules-formulas[4]"
                       "\<equiv>I" "prop-prop1")
  AOT_show \<open>[A!]x & \<forall>F (x[F] \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
  proof(safe intro!: "&I" GEN 1[THEN "&E"(1), THEN "&E"(1)] "\<equiv>I" "\<rightarrow>I")
    fix F
    AOT_assume 0: \<open>x[F]\<close>
    AOT_hence \<open>\<exists>q (F = [\<lambda>y q])\<close>
      using \<theta>[THEN "&E"(1), THEN "&E"(2)] "\<forall>E"(2) "\<rightarrow>E" by blast
    then AOT_obtain q where q_prop: \<open>F = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
    AOT_hence \<open>x[\<lambda>y q]\<close> using 0 "rule=E" by blast
    AOT_hence \<open>x\<^bold>\<Sigma>q\<close> by (metis "\<equiv>\<^sub>d\<^sub>fI" "&I" "ex:1:a" "prop-enc" "rule-ui:3")
    AOT_hence \<open>q \<equiv> p\<close> using \<theta>[THEN "&E"(2)] "\<forall>E"(2) "\<equiv>E"(1) by blast
    AOT_hence \<open>(q \<equiv> p) & F = [\<lambda>y q]\<close> using q_prop "&I" by blast
    AOT_thus \<open>\<exists>q ((q \<equiv> p) & F = [\<lambda>y q])\<close> by (rule "\<exists>I")
  next
    fix F
    AOT_assume \<open>\<exists>q ((q \<equiv> p) & F = [\<lambda>y q])\<close>
    then AOT_obtain q where q_prop: \<open>(q \<equiv> p) & F = [\<lambda>y q]\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>x\<^bold>\<Sigma>q\<close> using \<theta>[THEN "&E"(2)] "\<forall>E"(2) "&E" "\<equiv>E"(2) by blast
    AOT_hence \<open>x[\<lambda>y q]\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "&E"(2) "prop-enc")
    AOT_thus \<open>x[F]\<close> using q_prop[THEN "&E"(2), symmetric] "rule=E" by blast
  qed
next
  AOT_assume 0: \<open>[A!]x & \<forall>F (x[F] \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
  AOT_show \<open>[A!]x & \<forall>F (x[F] \<rightarrow> Propositional([F])) & \<forall>q (x \<^bold>\<Sigma> q \<equiv> (q \<equiv> p))\<close>
  proof(safe intro!: "&I" 0[THEN "&E"(1)] GEN "\<rightarrow>I")
    fix F
    AOT_assume \<open>x[F]\<close>
    AOT_hence \<open>\<exists>q ((q \<equiv> p) & F = [\<lambda>y q])\<close>
      using 0[THEN "&E"(2)] "\<forall>E"(2) "\<equiv>E"(1) by blast
    then AOT_obtain q where \<open>(q \<equiv> p) & F = [\<lambda>y q]\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>F = [\<lambda>y q]\<close> using "&E"(2) by blast
    AOT_hence \<open>\<exists>q F = [\<lambda>y q]\<close> by (rule "\<exists>I")
    AOT_thus \<open>Propositional([F])\<close> by (metis "\<equiv>\<^sub>d\<^sub>fI" "prop-prop1")
  next
    AOT_show \<open>x\<^bold>\<Sigma>r \<equiv> (r \<equiv> p)\<close> for r
    proof(rule "\<equiv>I"; rule "\<rightarrow>I")
      AOT_assume \<open>x\<^bold>\<Sigma>r\<close>
      AOT_hence \<open>x[\<lambda>y r]\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "&E"(2) "prop-enc")
      AOT_hence \<open>\<exists>q ((q \<equiv> p) & [\<lambda>y r] = [\<lambda>y q])\<close> 
        using 0[THEN "&E"(2), THEN "\<forall>E"(1), OF "prop-prop2:2", THEN "\<equiv>E"(1)] by blast
      then AOT_obtain q where \<open>(q \<equiv> p) & [\<lambda>y r] = [\<lambda>y q]\<close>
        using "\<exists>E"[rotated] by blast
      AOT_thus \<open>r \<equiv> p\<close>
        by (metis "rule=E" "&E"(1,2) id_sym "\<equiv>E"(2) "Commutativity of \<equiv>"
                  "p-identity-thm2:3")
    next
      AOT_assume \<open>r \<equiv> p\<close>
      AOT_hence \<open>(r \<equiv> p) & [\<lambda>y r] = [\<lambda>y r]\<close>
        by (metis "rule=I:1" "\<equiv>S"(1) "\<equiv>E"(2) "Commutativity of &" "prop-prop2:2")
      AOT_hence \<open>\<exists>q ((q \<equiv> p) & [\<lambda>y r] = [\<lambda>y q])\<close> by (rule "\<exists>I")
      AOT_hence \<open>x[\<lambda>y r]\<close>
        using 0[THEN "&E"(2), THEN "\<forall>E"(1), OF "prop-prop2:2", THEN "\<equiv>E"(2)] by blast
      AOT_thus \<open>x\<^bold>\<Sigma>r\<close> by (metis "\<equiv>\<^sub>d\<^sub>fI" "&I" "ex:1:a" "prop-enc" "rule-ui:3")
    qed
  qed
qed

AOT_theorem "ext-p-tv:1": \<open>\<exists>!x ExtensionOf(x, p)\<close>
  by (AOT_subst \<open>ExtensionOf(x, p)\<close> \<open>TruthValueOf(x, p)\<close> for: x)
     (auto simp: "extof-e" "p-has-!tv:2")

AOT_theorem "ext-p-tv:2": \<open>\<^bold>\<iota>x(ExtensionOf(x, p))\<down>\<close>
  using "A-Exists:2" "RA[2]" "ext-p-tv:1" "\<equiv>E"(2) by blast

AOT_theorem "ext-p-tv:3": \<open>\<^bold>\<iota>x(ExtensionOf(x, p)) = \<circ>p\<close>
proof -
  AOT_have 0: \<open>\<^bold>\<A>\<forall>x(ExtensionOf(x, p) \<equiv> TruthValueOf(x,p))\<close>
    by (rule "RA[2]"; rule GEN; rule "extof-e")
  AOT_have 1: \<open>\<circ>p = \<^bold>\<iota>x TruthValueOf(x,p)\<close>
    using "rule-id-df:1" "the-tv-p" "uni-tv" by blast
  show ?thesis
    apply (rule "equiv-desc-eq:1"[THEN "\<rightarrow>E", OF 0, THEN "\<forall>E"(1)[where \<tau>=\<open>\<guillemotleft>\<circ>p\<guillemotright>\<close>],
                                  THEN "\<equiv>E"(2), symmetric])
    using "1" "t=t-proper:1" "vdash-properties:10" apply blast
    by (fact 1)
qed

(*<*)
end
(*>*)
