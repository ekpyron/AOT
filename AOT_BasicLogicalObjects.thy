(*<*)
theory AOT_BasicLogicalObjects
  imports AOT_PLM
begin
(*>*)

section\<open>Basic Logical Objects\<close>

(* TODO: so far only the parts required for possible world theory *)

AOT_define TruthValueOf :: \<open>\<tau> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (\<open>TruthValueOf'(_,_')\<close>)
  tv_p: \<open>TruthValueOf(x,p) \<equiv>\<^sub>d\<^sub>f A!x & \<forall>F (x[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q]))\<close>

AOT_theorem p_has_tv_1: \<open>\<exists>x TruthValueOf(x,p)\<close>
  apply (AOT_subst \<open>\<lambda> \<kappa> . \<guillemotleft>TruthValueOf(\<kappa>,p)\<guillemotright>\<close> \<open>\<lambda> \<kappa> . \<guillemotleft>A!\<kappa> & \<forall>F (\<kappa>[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q]))\<guillemotright>\<close>)
   using "\<equiv>Df" tv_p apply blast
  by (fact "A-objects"[where \<phi>=\<open>\<lambda> \<Pi> . \<guillemotleft>\<exists>q ((q \<equiv>p) & \<Pi> = [\<lambda>y q])\<guillemotright>\<close>, axiom_inst])


AOT_theorem p_has_tv_2: \<open>\<exists>!x TruthValueOf(x,p)\<close>
  apply (AOT_subst \<open>\<lambda> \<kappa> . \<guillemotleft>TruthValueOf(\<kappa>,p)\<guillemotright>\<close> \<open>\<lambda> \<kappa> . \<guillemotleft>A!\<kappa> & \<forall>F (\<kappa>[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q]))\<guillemotright>\<close>)
   using "\<equiv>Df" tv_p apply presburger
  by (simp add: A_objects_unique)


AOT_theorem uni_tv: \<open>\<^bold>\<iota>x TruthValueOf(x,p)\<down>\<close>
  using "A-Exists:2" "RA[2]" "\<equiv>E"(2) p_has_tv_2 by blast

AOT_define the_tv_p :: \<open>\<phi> \<Rightarrow> \<kappa>\<^sub>s\<close> (\<open>\<circ>_\<close> [100] 100)
  \<open>\<circ>p =\<^sub>d\<^sub>f \<^bold>\<iota>x TruthValueOf(x,p)\<close>

AOT_theorem tv_id: \<open>\<circ>p = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q])))\<close>
proof -
  AOT_have \<open>\<box>\<forall>x(TruthValueOf(x,p)  \<equiv> A!x & \<forall>F (x[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q])))\<close>
    by (rule RN; rule GEN; rule tv_p[THEN "\<equiv>Df"])
  AOT_hence \<open>\<^bold>\<iota>x TruthValueOf(x,p) = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q])))\<close>
    using "equiv-desc-eq:3"[THEN "\<rightarrow>E", OF "&I", OF uni_tv] by simp
  thus ?thesis
    using "=\<^sub>d\<^sub>fI"(1)[OF the_tv_p, OF uni_tv] by fast
qed

(* TODO more theorems *)

AOT_theorem TV_lem1_1: \<open>p \<equiv> \<forall>F(\<exists>q (q & F = [\<lambda>y q]) \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q]))\<close>
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
    using "\<forall>E"(1)[rotated, OF prop_prop2_2] by blast
  moreover AOT_have \<open>\<exists>q ((q \<equiv> p) & [\<lambda>y p] = [\<lambda>y q])\<close>
    by (rule "\<exists>I"(2)[where \<beta>=p])
       (simp add: "rule=I:1" "&I" "oth-class-taut:3:a" prop_prop2_2)
  ultimately AOT_have \<open>\<exists>q (q & [\<lambda>y p] = [\<lambda>y q])\<close> using "\<equiv>E"(2) by blast
  then AOT_obtain q where \<open>q & [\<lambda>y p] = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
  AOT_thus \<open>p\<close>
    using "rule=E" "&E"(1) "&E"(2) id_sym "\<equiv>E"(2) "p-identity-thm2:3" by fast
qed

AOT_theorem TV_lem1_2: \<open>\<not>p \<equiv> \<forall>F(\<exists>q (\<not>q & F = [\<lambda>y q]) \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q]))\<close>
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
    using "\<forall>E"(1)[rotated, OF prop_prop2_2] by blast
  moreover AOT_have \<open>\<exists>q ((q \<equiv> p) & [\<lambda>y p] = [\<lambda>y q])\<close>
    by (rule "\<exists>I"(2)[where \<beta>=p])
       (simp add: "rule=I:1" "&I" "oth-class-taut:3:a" prop_prop2_2)
  ultimately AOT_have \<open>\<exists>q (\<not>q & [\<lambda>y p] = [\<lambda>y q])\<close> using "\<equiv>E"(2) by blast
  then AOT_obtain q where \<open>\<not>q & [\<lambda>y p] = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
  AOT_thus \<open>\<not>p\<close>
    using "rule=E" "&E"(1) "&E"(2) id_sym "\<equiv>E"(2) "p-identity-thm2:3" by fast
qed


AOT_define TruthValue :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>TruthValue'(_')\<close>)
  T_value: \<open>TruthValue(x) \<equiv>\<^sub>d\<^sub>f \<exists>p (TruthValueOf(x,p))\<close>

(* TODO more theorems *)

AOT_define prop_enc :: \<open>\<tau> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (infixl \<open>\<^bold>\<Sigma>\<close> 40)
  \<open>x\<^bold>\<Sigma>p \<equiv>\<^sub>d\<^sub>f x\<down> & x[\<lambda>y p]\<close>

AOT_act_theorem T_lem_1: \<open>TruthValueOf(\<circ>p, p)\<close>
proof -
  AOT_have \<theta>: \<open>\<circ>p = \<^bold>\<iota>x TruthValueOf(x, p)\<close>
    using "rule-id-def:1" the_tv_p uni_tv by blast
  moreover AOT_have \<open>\<circ>p\<down>\<close>
    using "t=t-proper:1" calculation "vdash-properties:10" by blast
  ultimately show ?thesis by (metis "rule=E" id_sym "vdash-properties:10" "y-in:3")
qed

AOT_act_theorem T_lem_2: \<open>\<forall>F (\<circ>p[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q]))\<close>
  using T_lem_1[THEN tv_p[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2)].

AOT_act_theorem T_lem_3: \<open>\<circ>p\<^bold>\<Sigma>r \<equiv> (r \<equiv> p)\<close>
proof -
  AOT_have \<theta>: \<open>\<circ>p[\<lambda>y r] \<equiv> \<exists>q ((q \<equiv> p) & [\<lambda>y r] = [\<lambda>y q])\<close>
    using T_lem_2[THEN "\<forall>E"(1), OF prop_prop2_2].
  show ?thesis
  proof(rule "\<equiv>I"; rule "\<rightarrow>I")
    AOT_assume \<open>\<circ>p\<^bold>\<Sigma>r\<close>
    AOT_hence \<open>\<circ>p[\<lambda>y r]\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "&E"(2) prop_enc)
    AOT_hence \<open>\<exists>q ((q \<equiv> p) & [\<lambda>y r] = [\<lambda>y q])\<close> using \<theta> "\<equiv>E"(1) by blast
    then AOT_obtain q where \<open>(q \<equiv> p) & [\<lambda>y r] = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
    moreover AOT_have \<open>r = q\<close> using calculation
      using "&E"(2) "\<equiv>E"(2) "p-identity-thm2:3" by blast
    ultimately AOT_show \<open>r \<equiv> p\<close>
      by (metis "rule=E" "&E"(1) "\<equiv>E"(6) "oth-class-taut:3:a")
  next
    AOT_assume \<open>r \<equiv> p\<close>
    moreover AOT_have \<open>[\<lambda>y r] = [\<lambda>y r]\<close>
      by (simp add: "rule=I:1" prop_prop2_2)
    ultimately AOT_have \<open>(r \<equiv> p) & [\<lambda>y r] = [\<lambda>y r]\<close> using "&I" by blast
    AOT_hence \<open>\<exists>q ((q \<equiv> p) & [\<lambda>y r] = [\<lambda>y q])\<close> by (rule "\<exists>I"(2)[where \<beta>=r])
    AOT_hence \<open>\<circ>p[\<lambda>y r]\<close> using \<theta> "\<equiv>E"(2) by blast
    AOT_thus \<open>\<circ>p\<^bold>\<Sigma>r\<close> by (metis "\<equiv>\<^sub>d\<^sub>fI" "&I" prop_enc "russell-axiom[enc,1].\<psi>_denotes_asm")
  qed
qed

AOT_act_theorem T_lem_4: \<open>\<circ>p\<^bold>\<Sigma>p\<close>
  using T_lem_3 "\<equiv>E"(2) "oth-class-taut:3:a" by blast

AOT_act_theorem T_lem_5: \<open>TruthValueOf(x, p) \<equiv> x = \<circ>p\<close>
proof -
  AOT_have \<open>\<forall>x (x = \<^bold>\<iota>x TruthValueOf(x, p) \<equiv> \<forall>z (TruthValueOf(z, p) \<equiv> z = x))\<close>
    by (simp add: "fund-cont-desc" GEN)
  moreover AOT_have \<open>\<circ>p\<down>\<close>
    using "\<equiv>\<^sub>d\<^sub>fE" T_lem_4 "&E"(1) prop_enc by blast
  ultimately AOT_have \<open>(\<circ>p = \<^bold>\<iota>x TruthValueOf(x, p)) \<equiv> \<forall>z (TruthValueOf(z, p) \<equiv> z = \<circ>p)\<close>
    using "\<forall>E"(1) by blast
  AOT_hence \<open>\<forall>z (TruthValueOf(z, p) \<equiv> z = \<circ>p)\<close>
    using "\<equiv>E"(1) "rule-id-def:1" the_tv_p uni_tv by blast
  AOT_thus \<open>TruthValueOf(x, p) \<equiv> x = \<circ>p\<close> using "\<forall>E"(2) by blast
qed


(* TODO more theorems *)

AOT_theorem TV_lem2_1: \<open>(A!x & \<forall>F (x[F] \<equiv> \<exists>q (q & F = [\<lambda>y q]))) \<rightarrow> TruthValue(x)\<close>
proof(safe intro!: "\<rightarrow>I" T_value[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(1)[rotated, OF "log-prop-prop:2"] tv_p[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_assume 0: \<open>[A!]x & \<forall>F (x[F] \<equiv> \<exists>q (q & F = [\<lambda>y q]))\<close>
  AOT_show \<open>[A!]x & \<forall>F (x[F] \<equiv> \<exists>q ((q \<equiv> (\<forall>p (p \<rightarrow> p))) & F = [\<lambda>y q]))\<close>
    apply (AOT_subst \<open>\<lambda> \<Pi> . \<guillemotleft>\<exists>q ((q \<equiv> (\<forall>p (p \<rightarrow> p))) & \<Pi> = [\<lambda>y q])\<guillemotright>\<close> \<open>\<lambda> \<Pi> . \<guillemotleft>\<exists>q (q & \<Pi> = [\<lambda>y q])\<guillemotright>\<close>)
     apply (AOT_subst \<open>\<lambda> \<phi> . \<guillemotleft>\<phi> \<equiv> (\<forall>p (p \<rightarrow> p))\<guillemotright>\<close> \<open>\<lambda> \<phi> . \<phi>\<close>)
      apply (metis (full_types) "deduction-theorem" "\<equiv>I" "\<equiv>E"(2) "universal-cor")
    by (auto simp add: "cqt-further:7" 0)
qed

AOT_theorem TV_lem2_2: \<open>(A!x & \<forall>F (x[F] \<equiv> \<exists>q (\<not>q & F = [\<lambda>y q]))) \<rightarrow> TruthValue(x)\<close>
proof(safe intro!: "\<rightarrow>I" T_value[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(1)[rotated, OF "log-prop-prop:2"] tv_p[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_assume 0: \<open>[A!]x & \<forall>F (x[F] \<equiv> \<exists>q (\<not>q & F = [\<lambda>y q]))\<close>
  AOT_show \<open>[A!]x & \<forall>F (x[F] \<equiv> \<exists>q ((q \<equiv> (\<exists>p (p & \<not>p))) & F = [\<lambda>y q]))\<close>
    apply (AOT_subst \<open>\<lambda> \<Pi> . \<guillemotleft>\<exists>q ((q \<equiv> (\<exists>p (p & \<not>p))) & \<Pi> = [\<lambda>y q])\<guillemotright>\<close> \<open>\<lambda> \<Pi> . \<guillemotleft>\<exists>q (\<not>q & \<Pi> = [\<lambda>y q])\<guillemotright>\<close>)
     apply (AOT_subst \<open>\<lambda> \<phi> . \<guillemotleft>\<phi> \<equiv> (\<exists>p (p & \<not>p))\<guillemotright>\<close> \<open>\<lambda> \<phi> . \<guillemotleft>\<not>\<phi>\<guillemotright>\<close>)
      apply (metis "instantiation" "deduction-theorem" "\<equiv>I" "\<equiv>E"(1) "raa-cor:1" "raa-cor:3")
    by (auto simp add: "cqt-further:7" 0)
qed

AOT_define TheTrue :: \<kappa>\<^sub>s (\<open>\<top>\<close>)
  the_true_1: \<open>\<top> =\<^sub>d\<^sub>f \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(p & F = [\<lambda>y p])))\<close>
AOT_define TheFalse :: \<kappa>\<^sub>s (\<open>\<bottom>\<close>)
  the_true_2: \<open>\<bottom> =\<^sub>d\<^sub>f \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(\<not>p & F = [\<lambda>y p])))\<close>

AOT_act_theorem T_T_value_1: \<open>TruthValue(\<top>)\<close>
proof -
  AOT_have true_def: \<open>\<top> = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(p & F = [\<lambda>y p])))\<close>
    by (simp add: A_descriptions "rule-id-def:1[zero]" the_true_1)
  AOT_hence true_den: \<open>\<top>\<down>\<close>
    using "t=t-proper:1" "vdash-properties:6" by blast
  AOT_show \<open>TruthValue(\<top>)\<close>
    using "y-in:2"[unvarify z, OF true_den, THEN "\<rightarrow>E", OF true_def]
          TV_lem2_1[unvarify x, OF true_den, THEN "\<rightarrow>E"] by blast
qed

AOT_act_theorem T_T_value_2: \<open>TruthValue(\<bottom>)\<close>
proof -
  AOT_have false_def: \<open>\<bottom> = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(\<not>p & F = [\<lambda>y p])))\<close>
    by (simp add: A_descriptions "rule-id-def:1[zero]" the_true_2)
  AOT_hence false_den: \<open>\<bottom>\<down>\<close>
    using "t=t-proper:1" "vdash-properties:6" by blast
  AOT_show \<open>TruthValue(\<bottom>)\<close>
    using "y-in:2"[unvarify z, OF false_den, THEN "\<rightarrow>E", OF false_def]
          TV_lem2_2[unvarify x, OF false_den, THEN "\<rightarrow>E"] by blast
qed

AOT_act_theorem T_T_value_3: \<open>\<top> \<noteq> \<bottom>\<close>
proof -
  AOT_have true_def: \<open>\<top> = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(p & F = [\<lambda>y p])))\<close>
    by (simp add: A_descriptions "rule-id-def:1[zero]" the_true_1)
  moreover AOT_have true_den: \<open>\<top>\<down>\<close>
    by (meson "t=t-proper:1" A_descriptions "rule-id-def:1[zero]" the_true_1 "vdash-properties:10")
  ultimately AOT_have true_prop: \<open>A!\<top> & \<forall>F (\<top>[F] \<equiv> \<exists>p(p & F = [\<lambda>y p]))\<close>
    using "y-in:2"[unvarify z, THEN "\<rightarrow>E"] by blast
  AOT_have false_def: \<open>\<bottom> = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(\<not>p & F = [\<lambda>y p])))\<close>
    by (simp add: A_descriptions "rule-id-def:1[zero]" the_true_2)
  moreover AOT_have false_den: \<open>\<bottom>\<down>\<close>
    by (meson "\<rightarrow>E" "t=t-proper:1" A_descriptions "rule-id-def:1[zero]" the_true_2)
  ultimately AOT_have false_prop: \<open>A!\<bottom> & \<forall>F (\<bottom>[F] \<equiv> \<exists>p(\<not>p & F = [\<lambda>y p]))\<close>
    using "y-in:2"[unvarify z, THEN "\<rightarrow>E"] by blast
  AOT_obtain p where p: p
    by (metis "instantiation" "act-conj-act:4" "existential:1" "log-prop-prop:2" "logic-actual"
              "vdash-properties:1[1]" "vdash-properties:6")
  show ?thesis
  proof(safe intro!: "ab-obey:2"[unvarify x y, THEN "\<rightarrow>E"]
                     false_den true_den true_prop[THEN "&E"(1)] "&I"
                     false_prop[THEN "&E"(1)] "\<or>I"(1) "\<exists>I"(1))
    AOT_show \<open>\<top>[\<lambda>y p]\<close>
      apply (rule true_prop[THEN "&E"(2), THEN "\<forall>E"(1), THEN "\<equiv>E"(2), OF prop_prop2_2])
      apply (rule "\<exists>I"(2)[where \<beta>=p])
      by (simp add: "rule=I:1" "&I" p prop_prop2_2)
  next
    AOT_show \<open>\<not>\<bottom>[\<lambda>y p]\<close>
    proof (rule false_prop[THEN "&E"(2), THEN "\<forall>E"(1), THEN "\<equiv>E"(4), OF prop_prop2_2]; rule "raa-cor:2")
      AOT_assume \<open>\<exists>q (\<not>q & [\<lambda>y p] = [\<lambda>y q])\<close>
      then AOT_obtain q where \<open>\<not>q & [\<lambda>y p] = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
      AOT_hence \<open>\<not>p\<close>
        by (metis "rule=E" "&E"(1) "&E"(2) "\<equiv>E"(2) "modus-tollens:1"
                  "oth-class-taut:1:a" "p-identity-thm2:3" "raa-cor:1")
      AOT_thus \<open>p & \<not>p\<close> using p "&I" by blast
    qed
  qed("cqt:2[lambda]")
qed

AOT_theorem \<open>\<exists>x\<exists>y(TruthValue(x) & TruthValue(y) & x \<noteq> y & \<forall>z (TruthValue(z) \<rightarrow> z = x \<or> z = y))\<close>
proof -
  AOT_obtain a where a_prop: \<open>A!a & \<forall>F (a[F] \<equiv> \<exists>p (p & F = [\<lambda>y p]))\<close>
    using "A-objects"[axiom_inst] "\<exists>E"[rotated] by fast
  AOT_obtain b where b_prop: \<open>A!b & \<forall>F (b[F] \<equiv> \<exists>p (\<not>p & F = [\<lambda>y p]))\<close>
    using "A-objects"[axiom_inst] "\<exists>E"[rotated] by fast
  AOT_obtain p where p: p
    by (metis "log-prop-prop:2" "raa-cor:3" "rule-ui:1" "universal-cor")
  show ?thesis
  proof(rule "\<exists>I"(2)[where \<beta>=a]; rule "\<exists>I"(2)[where \<beta>=b]; safe intro!: "&I" GEN "\<rightarrow>I")
    AOT_show \<open>TruthValue(a)\<close>
      using TV_lem2_1 a_prop "vdash-properties:10" by blast
  next
    AOT_show \<open>TruthValue(b)\<close>
      using TV_lem2_2 b_prop "vdash-properties:10" by blast
  next
    AOT_show \<open>a \<noteq> b\<close>
    proof(rule "ab-obey:2"[THEN "\<rightarrow>E", OF "\<or>I"(1)])
      AOT_show \<open>\<exists>F (a[F] & \<not>b[F])\<close>
      proof(rule "\<exists>I"(1)[where \<tau>="\<guillemotleft>[\<lambda>y p]\<guillemotright>"]; rule "&I" prop_prop2_2)
        AOT_show \<open>a[\<lambda>y p]\<close>
          by(safe intro!: a_prop[THEN "&E"(2), THEN "\<forall>E"(1), THEN "\<equiv>E"(2), OF prop_prop2_2]
                          "\<exists>I"(2)[where \<beta>=p] "&I" p "rule=I:1"[OF prop_prop2_2])
      next
        AOT_show \<open>\<not>b[\<lambda>y p]\<close>
        proof (rule "raa-cor:2")
          AOT_assume \<open>b[\<lambda>y p]\<close>
          AOT_hence \<open>\<exists>q (\<not>q & [\<lambda>y p] = [\<lambda>y q])\<close>
            using b_prop[THEN "&E"(2), THEN "\<forall>E"(1)[rotated, OF prop_prop2_2, THEN "\<equiv>E"(1)]] by blast
          then AOT_obtain q where \<open>\<not>q & [\<lambda>y p] = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
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
      by (metis "\<equiv>\<^sub>d\<^sub>fE" T_value)
    then AOT_obtain p where \<open>TruthValueOf(z, p)\<close> using "\<exists>E"[rotated] by blast
    AOT_hence z_prop: \<open>A!z & \<forall>F (z[F] \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
      using "\<equiv>\<^sub>d\<^sub>fE" tv_p by blast
    {
      AOT_assume p: \<open>p\<close>
      AOT_have \<open>z = a\<close>
      proof(rule "ab-obey:1"[THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF "&I", OF z_prop[THEN "&E"(1)], OF a_prop[THEN "&E"(1)]]; rule GEN)
        fix G
        AOT_have \<open>z[G] \<equiv> \<exists>q ((q \<equiv> p) & G = [\<lambda>y q])\<close>
          using z_prop[THEN "&E"(2)] "\<forall>E"(2) by blast
        also AOT_have \<open>\<exists>q ((q \<equiv> p) & G = [\<lambda>y q]) \<equiv> \<exists>q (q & G = [\<lambda>y q])\<close>
          using TV_lem1_1[THEN "\<equiv>E"(1), OF p, THEN "\<forall>E"(2)[where \<beta>=G], symmetric].
        also AOT_have \<open>\<dots> \<equiv> a[G]\<close> using a_prop[THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=G], symmetric].
        finally AOT_show \<open>z[G] \<equiv> a[G]\<close>.
      qed
      AOT_hence \<open>z = a \<or> z = b\<close> by (rule "\<or>I")
    }
    moreover {
      AOT_assume notp: \<open>\<not>p\<close>
      AOT_have \<open>z = b\<close>
      proof(rule "ab-obey:1"[THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF "&I", OF z_prop[THEN "&E"(1)], OF b_prop[THEN "&E"(1)]]; rule GEN)
        fix G
        AOT_have \<open>z[G] \<equiv> \<exists>q ((q \<equiv> p) & G = [\<lambda>y q])\<close>
          using z_prop[THEN "&E"(2)] "\<forall>E"(2) by blast
        also AOT_have \<open>\<exists>q ((q \<equiv> p) & G = [\<lambda>y q]) \<equiv> \<exists>q (\<not>q & G = [\<lambda>y q])\<close>
          using TV_lem1_2[THEN "\<equiv>E"(1), OF notp, THEN "\<forall>E"(2)[where \<beta>=G], symmetric].
        also AOT_have \<open>\<dots> \<equiv> b[G]\<close> using b_prop[THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=G], symmetric].
        finally AOT_show \<open>z[G] \<equiv> b[G]\<close>.
      qed
      AOT_hence \<open>z = a \<or> z = b\<close> by (rule "\<or>I")
    }
    ultimately AOT_show \<open>z = a \<or> z = b\<close>
      by (metis "reductio-aa:1")
  qed
qed

AOT_act_theorem valueof_facts_1: \<open>TruthValueOf(x, p) \<rightarrow> (p \<equiv> x = \<top>)\<close>
proof(safe intro!: "\<rightarrow>I" dest!: tv_p[THEN "\<equiv>\<^sub>d\<^sub>fE"])
  AOT_assume \<theta>: \<open>[A!]x & \<forall>F (x[F] \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
  AOT_have a: \<open>A!\<top>\<close>
    using "\<exists>E" T_T_value_1 T_value "&E"(1) "\<equiv>\<^sub>d\<^sub>fE" tv_p by blast
  AOT_have true_def: \<open>\<top> = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(p & F = [\<lambda>y p])))\<close>
    by (simp add: A_descriptions "rule-id-def:1[zero]" the_true_1)
  AOT_hence true_den: \<open>\<top>\<down>\<close>
    using "t=t-proper:1" "vdash-properties:6" by blast
  AOT_have b: \<open>\<forall>F (\<top>[F] \<equiv> \<exists>q (q & F = [\<lambda>y q]))\<close>
    using "y-in:2"[unvarify z, OF true_den, THEN "\<rightarrow>E", OF true_def] "&E" by blast
  AOT_show \<open>p \<equiv> x = \<top>\<close>
  proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
    AOT_assume p
    AOT_hence \<open>\<forall>F (\<exists>q (q & F = [\<lambda>y q]) \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close> using TV_lem1_1[THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>\<forall>F(\<top>[F] \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
      using b "cqt-basic:10"[THEN "\<rightarrow>E", OF "&I", OF b] by fast
    AOT_hence c: \<open>\<forall>F(\<exists>q((q \<equiv> p) & F = [\<lambda>y q]) \<equiv> \<top>[F])\<close>
      using "cqt-basic:11"[THEN "\<equiv>E"(1)] by fast
    AOT_hence \<open>\<forall>F (x[F] \<equiv> \<top>[F])\<close>
      using "cqt-basic:10"[THEN "\<rightarrow>E", OF "&I", OF \<theta>[THEN "&E"(2)]] by fast
    AOT_thus \<open>x = \<top>\<close>
      by (rule "ab-obey:1"[unvarify y, OF true_den, THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF "&I", OF \<theta>[THEN "&E"(1)], OF a])
  next
    AOT_assume \<open>x = \<top>\<close>
    AOT_hence d: \<open>\<forall>F (\<top>[F] \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
      using "rule=E" \<theta>[THEN "&E"(2)] by fast
    AOT_have \<open>\<forall>F (\<exists>q (q & F = [\<lambda>y q]) \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
      using "cqt-basic:10"[THEN "\<rightarrow>E", OF "&I", OF b[THEN "cqt-basic:11"[THEN "\<equiv>E"(1)]], OF d].
    AOT_thus p using TV_lem1_1[THEN "\<equiv>E"(2)] by blast
  qed
qed

AOT_act_theorem valueof_facts_2: \<open>TruthValueOf(x, p) \<rightarrow> (\<not>p \<equiv> x = \<bottom>)\<close>
proof(safe intro!: "\<rightarrow>I" dest!: tv_p[THEN "\<equiv>\<^sub>d\<^sub>fE"])
  AOT_assume \<theta>: \<open>[A!]x & \<forall>F (x[F] \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
  AOT_have a: \<open>A!\<bottom>\<close>
    using "\<exists>E" T_T_value_2 T_value "&E"(1) "\<equiv>\<^sub>d\<^sub>fE" tv_p by blast
  AOT_have false_def: \<open>\<bottom> = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(\<not>p & F = [\<lambda>y p])))\<close>
    by (simp add: A_descriptions "rule-id-def:1[zero]" the_true_2)
  AOT_hence false_den: \<open>\<bottom>\<down>\<close>
    using "t=t-proper:1" "vdash-properties:6" by blast
  AOT_have b: \<open>\<forall>F (\<bottom>[F] \<equiv> \<exists>q (\<not>q & F = [\<lambda>y q]))\<close>
    using "y-in:2"[unvarify z, OF false_den, THEN "\<rightarrow>E", OF false_def] "&E" by blast
  AOT_show \<open>\<not>p \<equiv> x = \<bottom>\<close>
  proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
    AOT_assume \<open>\<not>p\<close>
    AOT_hence \<open>\<forall>F (\<exists>q (\<not>q & F = [\<lambda>y q]) \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close> using TV_lem1_2[THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>\<forall>F(\<bottom>[F] \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
      using b "cqt-basic:10"[THEN "\<rightarrow>E", OF "&I", OF b] by fast
    AOT_hence c: \<open>\<forall>F(\<exists>q((q \<equiv> p) & F = [\<lambda>y q]) \<equiv> \<bottom>[F])\<close>
      using "cqt-basic:11"[THEN "\<equiv>E"(1)] by fast
    AOT_hence \<open>\<forall>F (x[F] \<equiv> \<bottom>[F])\<close>
      using "cqt-basic:10"[THEN "\<rightarrow>E", OF "&I", OF \<theta>[THEN "&E"(2)]] by fast
    AOT_thus \<open>x = \<bottom>\<close>
      by (rule "ab-obey:1"[unvarify y, OF false_den, THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF "&I", OF \<theta>[THEN "&E"(1)], OF a])
  next
    AOT_assume \<open>x = \<bottom>\<close>
    AOT_hence d: \<open>\<forall>F (\<bottom>[F] \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
      using "rule=E" \<theta>[THEN "&E"(2)] by fast
    AOT_have \<open>\<forall>F (\<exists>q (\<not>q & F = [\<lambda>y q]) \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
      using "cqt-basic:10"[THEN "\<rightarrow>E", OF "&I", OF b[THEN "cqt-basic:11"[THEN "\<equiv>E"(1)]], OF d].
    AOT_thus \<open>\<not>p\<close> using TV_lem1_2[THEN "\<equiv>E"(2)] by blast
  qed
qed

AOT_act_theorem q_True_1: \<open>p \<equiv> (\<circ>p = \<top>)\<close>
  apply (rule valueof_facts_1[unvarify x, THEN "\<rightarrow>E", rotated, OF T_lem_1])
  using "\<equiv>\<^sub>d\<^sub>fE" T_lem_4 "&E"(1) prop_enc by blast

AOT_act_theorem q_True_2: \<open>\<not>p \<equiv> (\<circ>p = \<bottom>)\<close>
  apply (rule valueof_facts_2[unvarify x, THEN "\<rightarrow>E", rotated, OF T_lem_1])
  using "\<equiv>\<^sub>d\<^sub>fE" T_lem_4 "&E"(1) prop_enc by blast

AOT_act_theorem q_True_3: \<open>p \<equiv> \<top>\<^bold>\<Sigma>p\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume p
  AOT_hence \<open>\<circ>p = \<top>\<close> by (metis "\<equiv>E"(1) q_True_1)
  moreover AOT_have \<open>\<circ>p\<^bold>\<Sigma>p\<close>
    by (simp add: T_lem_4)
  ultimately AOT_show \<open>\<top>\<^bold>\<Sigma>p\<close>
    using "rule=E" T_lem_4 by fast
next
  AOT_have true_def: \<open>\<top> = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(p & F = [\<lambda>y p])))\<close>
    by (simp add: A_descriptions "rule-id-def:1[zero]" the_true_1)
  AOT_hence true_den: \<open>\<top>\<down>\<close>
    using "t=t-proper:1" "vdash-properties:6" by blast
  AOT_have b: \<open>\<forall>F (\<top>[F] \<equiv> \<exists>q (q & F = [\<lambda>y q]))\<close>
    using "y-in:2"[unvarify z, OF true_den, THEN "\<rightarrow>E", OF true_def] "&E" by blast

  AOT_assume \<open>\<top>\<^bold>\<Sigma>p\<close>
  AOT_hence \<open>\<top>[\<lambda>y p]\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "&E"(2) prop_enc)
  AOT_hence \<open>\<exists>q (q & [\<lambda>y p] = [\<lambda>y q])\<close>
    using b[THEN "\<forall>E"(1), OF prop_prop2_2, THEN "\<equiv>E"(1)] by blast
  then AOT_obtain q where \<open>q & [\<lambda>y p] = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
  AOT_thus \<open>p\<close>
    using "rule=E" "&E"(1) "&E"(2) id_sym "\<equiv>E"(2) "p-identity-thm2:3" by fast
qed


AOT_act_theorem q_True_5: \<open>\<not>p \<equiv> \<bottom>\<^bold>\<Sigma>p\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>\<not>p\<close>
  AOT_hence \<open>\<circ>p = \<bottom>\<close> by (metis "\<equiv>E"(1) q_True_2)
  moreover AOT_have \<open>\<circ>p\<^bold>\<Sigma>p\<close>
    by (simp add: T_lem_4)
  ultimately AOT_show \<open>\<bottom>\<^bold>\<Sigma>p\<close>
    using "rule=E" T_lem_4 by fast
next
  AOT_have false_def: \<open>\<bottom> = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(\<not>p & F = [\<lambda>y p])))\<close>
    by (simp add: A_descriptions "rule-id-def:1[zero]" the_true_2)
  AOT_hence false_den: \<open>\<bottom>\<down>\<close>
    using "t=t-proper:1" "vdash-properties:6" by blast
  AOT_have b: \<open>\<forall>F (\<bottom>[F] \<equiv> \<exists>q (\<not>q & F = [\<lambda>y q]))\<close>
    using "y-in:2"[unvarify z, OF false_den, THEN "\<rightarrow>E", OF false_def] "&E" by blast

  AOT_assume \<open>\<bottom>\<^bold>\<Sigma>p\<close>
  AOT_hence \<open>\<bottom>[\<lambda>y p]\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "&E"(2) prop_enc)
  AOT_hence \<open>\<exists>q (\<not>q & [\<lambda>y p] = [\<lambda>y q])\<close>
    using b[THEN "\<forall>E"(1), OF prop_prop2_2, THEN "\<equiv>E"(1)] by blast
  then AOT_obtain q where \<open>\<not>q & [\<lambda>y p] = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
  AOT_thus \<open>\<not>p\<close>
    using "rule=E" "&E"(1) "&E"(2) id_sym "\<equiv>E"(2) "p-identity-thm2:3" by fast
qed

AOT_act_theorem q_True_4: \<open>p \<equiv> \<not>(\<bottom>\<^bold>\<Sigma>p)\<close>
  using q_True_5
  by (metis "deduction-theorem" "\<equiv>I" "\<equiv>E"(2) "\<equiv>E"(4) "raa-cor:3")

AOT_act_theorem q_True_6: \<open>\<not>p \<equiv> \<not>(\<top>\<^bold>\<Sigma>p)\<close>
  using "\<equiv>E"(1) "oth-class-taut:4:b" q_True_3 by blast

AOT_define exten_p :: \<open>\<tau> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (\<open>ExtensionOf'(_,_')\<close>)
  \<open>ExtensionOf(x,p) \<equiv>\<^sub>d\<^sub>f A!x & \<forall>F (x[F] \<rightarrow> Propositional([F])) & \<forall>q ((x\<^bold>\<Sigma>q) \<equiv> (q \<equiv> p))\<close>

AOT_theorem extof_e: \<open>ExtensionOf(x, p) \<equiv> TruthValueOf(x, p)\<close>
proof (safe intro!: "\<equiv>I" "\<rightarrow>I" tv_p[THEN "\<equiv>\<^sub>d\<^sub>fI"] exten_p[THEN "\<equiv>\<^sub>d\<^sub>fI"]
            dest!: tv_p[THEN "\<equiv>\<^sub>d\<^sub>fE"] exten_p[THEN "\<equiv>\<^sub>d\<^sub>fE"])
  AOT_assume 1: \<open>[A!]x & \<forall>F (x[F] \<rightarrow> Propositional([F])) & \<forall>q (x \<^bold>\<Sigma> q \<equiv> (q \<equiv> p))\<close>
  AOT_have \<theta>: \<open>[A!]x & \<forall>F (x[F] \<rightarrow> \<exists>q(F = [\<lambda>y q])) & \<forall>q (x \<^bold>\<Sigma> q \<equiv> (q \<equiv> p))\<close>
    apply (AOT_subst \<open>\<lambda> \<Pi> . \<guillemotleft>\<exists>q(\<Pi> = [\<lambda>y q])\<guillemotright>\<close> \<open>\<lambda> \<Pi> . \<guillemotleft>Propositional([\<Pi>])\<guillemotright>\<close>)
     using "\<equiv>E"(2) "Commutativity of \<equiv>" prop_prop1 "\<equiv>Df" apply blast
    by (simp add: 1)
  AOT_show \<open>[A!]x & \<forall>F (x[F] \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
  proof(safe intro!: "&I" GEN 1[THEN "&E"(1), THEN "&E"(1)] "\<equiv>I" "\<rightarrow>I")
    fix F
    AOT_assume 0: \<open>x[F]\<close>
    AOT_hence \<open>\<exists>q (F = [\<lambda>y q])\<close>
      using \<theta>[THEN "&E"(1), THEN "&E"(2)] "\<forall>E"(2) "\<rightarrow>E" by blast
    then AOT_obtain q where q_prop: \<open>F = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
    AOT_hence \<open>x[\<lambda>y q]\<close> using 0 "rule=E" by blast
    AOT_hence \<open>x\<^bold>\<Sigma>q\<close> by (metis "\<equiv>\<^sub>d\<^sub>fI" "&I" "ex:1:a" prop_enc "rule-ui:3")
    AOT_hence \<open>q \<equiv> p\<close> using \<theta>[THEN "&E"(2)] "\<forall>E"(2) "\<equiv>E"(1) by blast
    AOT_hence \<open>(q \<equiv> p) & F = [\<lambda>y q]\<close> using q_prop "&I" by blast
    AOT_thus \<open>\<exists>q ((q \<equiv> p) & F = [\<lambda>y q])\<close> by (rule "\<exists>I")
  next
    fix F
    AOT_assume \<open>\<exists>q ((q \<equiv> p) & F = [\<lambda>y q])\<close>
    then AOT_obtain q where q_prop: \<open>(q \<equiv> p) & F = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
    AOT_hence \<open>x\<^bold>\<Sigma>q\<close> using \<theta>[THEN "&E"(2)] "\<forall>E"(2) "&E" "\<equiv>E"(2) by blast
    AOT_hence \<open>x[\<lambda>y q]\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "&E"(2) prop_enc)
    AOT_thus \<open>x[F]\<close> using q_prop[THEN "&E"(2), symmetric] "rule=E" by blast
  qed
next
  AOT_assume 0: \<open>[A!]x & \<forall>F (x[F] \<equiv> \<exists>q ((q \<equiv> p) & F = [\<lambda>y q]))\<close>
  AOT_show \<open>[A!]x & \<forall>F (x[F] \<rightarrow> Propositional([F])) & \<forall>q (x \<^bold>\<Sigma> q \<equiv> (q \<equiv> p))\<close>
  proof(safe intro!: "&I" 0[THEN "&E"(1)] GEN "\<rightarrow>I")
    fix F
    AOT_assume \<open>x[F]\<close>
    AOT_hence \<open>\<exists>q ((q \<equiv> p) & F = [\<lambda>y q])\<close> using 0[THEN "&E"(2)] "\<forall>E"(2) "\<equiv>E"(1) by blast
    then AOT_obtain q where \<open>(q \<equiv> p) & F = [\<lambda>y q]\<close> using "\<exists>E"[rotated] by blast
    AOT_hence \<open>F = [\<lambda>y q]\<close> using "&E"(2) by blast
    AOT_hence \<open>\<exists>q F = [\<lambda>y q]\<close> by (rule "\<exists>I")
    AOT_thus \<open>Propositional([F])\<close> by (metis "\<equiv>\<^sub>d\<^sub>fI" prop_prop1)
  next
    AOT_show \<open>x\<^bold>\<Sigma>r \<equiv> (r \<equiv> p)\<close> for r
    proof(rule "\<equiv>I"; rule "\<rightarrow>I")
      AOT_assume \<open>x\<^bold>\<Sigma>r\<close>
      AOT_hence \<open>x[\<lambda>y r]\<close> by (metis "\<equiv>\<^sub>d\<^sub>fE" "&E"(2) prop_enc)
      AOT_hence \<open>\<exists>q ((q \<equiv> p) & [\<lambda>y r] = [\<lambda>y q])\<close> 
        using 0[THEN "&E"(2), THEN "\<forall>E"(1), OF prop_prop2_2, THEN "\<equiv>E"(1)] by blast
      then AOT_obtain q where \<open>(q \<equiv> p) & [\<lambda>y r] = [\<lambda>y q]\<close>
        using "\<exists>E"[rotated] by blast
      AOT_thus \<open>r \<equiv> p\<close>
        by (metis "rule=E" "&E"(1) "&E"(2) id_sym "\<equiv>E"(2) "Commutativity of \<equiv>" "p-identity-thm2:3")
    next
      AOT_assume \<open>r \<equiv> p\<close>
      AOT_hence \<open>(r \<equiv> p) & [\<lambda>y r] = [\<lambda>y r]\<close>
        by (metis "rule=I:1" "\<equiv>S"(1) "\<equiv>E"(2) "Commutativity of &" prop_prop2_2)
      AOT_hence \<open>\<exists>q ((q \<equiv> p) & [\<lambda>y r] = [\<lambda>y q])\<close> by (rule "\<exists>I")
      AOT_hence \<open>x[\<lambda>y r]\<close> using 0[THEN "&E"(2), THEN "\<forall>E"(1), OF prop_prop2_2, THEN "\<equiv>E"(2)] by blast
      AOT_thus \<open>x\<^bold>\<Sigma>r\<close> by (metis "\<equiv>\<^sub>d\<^sub>fI" "&I" "ex:1:a" prop_enc "rule-ui:3")
    qed
  qed
qed

AOT_theorem ext_p_tv_1: \<open>\<exists>!x ExtensionOf(x, p)\<close>
  by (AOT_subst \<open>\<lambda> \<kappa> . \<guillemotleft>ExtensionOf(\<kappa>, p)\<guillemotright>\<close> \<open>\<lambda> \<kappa> . \<guillemotleft>TruthValueOf(\<kappa>, p)\<guillemotright>\<close>)
     (auto simp: extof_e p_has_tv_2)

AOT_theorem ext_p_tv_2: \<open>\<^bold>\<iota>x(ExtensionOf(x, p))\<down>\<close>
  using "A-Exists:2" "RA[2]" ext_p_tv_1 "\<equiv>E"(2) by blast

AOT_theorem ext_p_tv_3: \<open>\<^bold>\<iota>x(ExtensionOf(x, p)) = \<circ>p\<close>
proof -
  AOT_have 0: \<open>\<^bold>\<A>\<forall>x(ExtensionOf(x, p) \<equiv> TruthValueOf(x,p))\<close>
    by (rule "RA[2]"; rule GEN; rule extof_e)
  AOT_have 1: \<open>\<circ>p = \<^bold>\<iota>x TruthValueOf(x,p)\<close>
    using "rule-id-def:1" the_tv_p uni_tv by blast
  show ?thesis
    apply (rule "equiv-desc-eq:1"[THEN "\<rightarrow>E", OF 0, THEN "\<forall>E"(1)[where \<tau>=\<open>\<guillemotleft>\<circ>p\<guillemotright>\<close>], THEN "\<equiv>E"(2), symmetric])
    using "1" "t=t-proper:1" "vdash-properties:10" apply blast
    by (fact 1)
qed

(* TODO: PLM: is this really true? Seems to be modally fragile. *)
AOT_theorem ext_p_tv_4: \<open>TruthValue(\<^bold>\<iota>x(ExtensionOf(x,p)))\<close>
  oops

(*<*)
end
(*>*)
