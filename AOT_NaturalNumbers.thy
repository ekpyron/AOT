(*<*)
theory AOT_NaturalNumbers
  imports AOT_PossibleWorlds AOT_RestrictedVariables
  abbrevs one-to-one = \<open>\<^sub>1\<^sub>-\<^sub>1\<close>
      and onto = \<open>\<^sub>o\<^sub>n\<^sub>t\<^sub>o\<close>
begin
(*>*)

AOT_define Discernible :: \<open>\<Pi>\<close> (\<open>D!\<close>)
  \<open>D! =\<^sub>d\<^sub>f [\<lambda>x \<box>\<forall>y(y \<noteq> x \<rightarrow> \<exists>F \<not>([F]y \<equiv> [F]x))]\<close>

AOT_theorem Discernible_den_1: \<open>[\<lambda>x \<box>\<forall>y(y \<noteq> x \<rightarrow> \<exists>F \<not>([F]y \<equiv> [F]x))]\<down>\<close>
proof(safe intro!: "kirchner-thm:1"[THEN "\<equiv>E"(2)] RN GEN "\<rightarrow>I")
  AOT_modally_strict {
    fix x y
    AOT_assume 0: \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
    AOT_assume 1: \<open>\<box>\<forall>y(y \<noteq> x \<rightarrow> \<exists>F \<not>([F]y \<equiv> [F]x))\<close>
    AOT_hence 2: \<open>\<forall>y(y \<noteq> x \<rightarrow> \<exists>F \<not>([F]y \<equiv> [F]x))\<close>
      using "qml:2"[axiom_inst, THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>y \<noteq> x \<rightarrow> \<exists>F \<not>([F]y \<equiv> [F]x)\<close> for y
      using "\<forall>E"(2) by blast
    AOT_have \<open>y = x\<close>
    proof(rule "raa-cor:1")
      AOT_assume \<open>\<not>y = x\<close>
      AOT_hence \<open>y \<noteq> x\<close>
        using "=-infix"[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
      AOT_hence \<open>\<exists>F \<not>([F]y \<equiv> [F]x)\<close>
        using 2[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
      then AOT_obtain F where \<open>\<not>([F]y \<equiv> [F]x)\<close>
        using "\<exists>E"[rotated] by blast
      moreover AOT_have \<open>[F]y \<equiv> [F]x\<close> using 0[THEN "\<forall>E"(2), symmetric].
      ultimately AOT_show \<open>p & \<not>p\<close> using "reductio-aa:1" by blast
    qed
    AOT_hence \<open>\<box>\<forall>z(z \<noteq> y \<rightarrow> \<exists>F \<not>([F]z \<equiv> [F]y))\<close>
        using 0 1 "rule=E" id_sym by fast
  } note impl = this
  AOT_modally_strict {
    fix x y
    AOT_assume \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
    moreover AOT_have \<open>\<forall>F ([F]y \<equiv> [F]x)\<close>
      by (metis calculation "cqt-basic:11" "intro-elim:3:b")
    ultimately AOT_show \<open>\<box>\<forall>z(z \<noteq> x \<rightarrow> \<exists>F \<not>([F]z \<equiv> [F]x)) \<equiv> \<box>\<forall>z(z \<noteq> y \<rightarrow> \<exists>F \<not>([F]z \<equiv> [F]y))\<close>
      using impl "\<rightarrow>I" "\<equiv>I" by auto
  }
qed

AOT_theorem Discernible_eq: \<open>D! = [\<lambda>x \<box>\<forall>y(y \<noteq> x \<rightarrow> \<exists>F \<not>([F]y \<equiv> [F]x))]\<close>
  using "rule-id-df:1[zero]"[OF Discernible, OF Discernible_den_1].

AOT_theorem Discernible_den: \<open>D!\<down>\<close>
  using Discernible_eq "t=t-proper:1" "vdash-properties:10" by blast

AOT_theorem Discernible_equiv: \<open>D!x \<equiv> \<box>\<forall>y(y \<noteq> x \<rightarrow> \<exists>F \<not>([F]y \<equiv> [F]x))\<close>
proof -
  AOT_have \<open>[\<lambda>x \<box>\<forall>y(y \<noteq> x \<rightarrow> \<exists>F \<not>([F]y \<equiv> [F]x))]x \<equiv> \<box>\<forall>y(y \<noteq> x \<rightarrow> \<exists>F \<not>([F]y \<equiv> [F]x))\<close>
    using "beta-C-meta"[THEN "\<rightarrow>E"] Discernible_den_1 by fast
  thus ?thesis using Discernible_eq "rule=E" id_sym by fast
qed

AOT_define eq_D :: \<open>\<Pi>\<close> (\<open>'(=\<^sub>D')\<close>)
  "=D": \<open>(=\<^sub>D) =\<^sub>d\<^sub>f [\<lambda>xy \<box>\<forall>F([F]x \<equiv> [F]y)]\<close>

syntax "_AOT_eq_D_infix" :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl "=\<^sub>D" 50)
translations
  "_AOT_eq_D_infix \<kappa> \<kappa>'" == "CONST AOT_exe (CONST eq_D) (CONST Pair \<kappa> \<kappa>')"
print_translation\<open>
AOT_syntax_print_translations
[(\<^const_syntax>\<open>AOT_exe\<close>, fn ctxt => fn [
  Const ("\<^const>AOT_PLM.eq_D", _),
  Const (\<^const_syntax>\<open>Pair\<close>, _) $ lhs $ rhs
] => Const (\<^syntax_const>\<open>_AOT_eq_D_infix\<close>, dummyT) $ lhs $ rhs)]\<close>

AOT_theorem "=D[denotes]": \<open>[(=\<^sub>D)]\<down>\<close>
  by (rule "=\<^sub>d\<^sub>fI"(2)[OF "=D"]) "cqt:2"

AOT_theorem "=D-simple:1": \<open>x =\<^sub>D y \<equiv> \<box>\<forall>F ([F]x \<equiv> [F]y)\<close>
proof -
  AOT_have 0: \<open>\<guillemotleft>(AOT_term_of_var x,AOT_term_of_var y)\<guillemotright>\<down>\<close>
    by (simp add: "&I" "cqt:2[const_var]"[axiom_inst] prod_denotesI)
  AOT_have 1: \<open>[\<lambda>xy \<box>\<forall>F ([F]x \<equiv> [F]y)]\<down>\<close> by "cqt:2"
  show ?thesis apply (rule "=\<^sub>d\<^sub>fI"(2)[OF "=D"]; "cqt:2[lambda]"?)
    using "beta-C-meta"[THEN "\<rightarrow>E", OF 1, unvarify \<nu>\<^sub>1\<nu>\<^sub>n, of "(_,_)", OF 0]
    by fast
qed

AOT_theorem "=D-simple:2": \<open>D!x \<rightarrow> (x =\<^sub>D y \<rightarrow> x = y)\<close>
proof (rule "\<rightarrow>I"; rule "\<rightarrow>I")
  AOT_assume \<open>D!x\<close>
  AOT_hence 0: \<open>\<box>\<forall>y (y \<noteq> x \<rightarrow> \<exists>F \<not>([F]y \<equiv> [F]x))\<close>
    using Discernible_equiv[THEN "\<equiv>E"(1)] by auto
  AOT_assume \<open>x =\<^sub>D y\<close>
  AOT_hence 1: \<open>\<box>\<forall>F ([F]x \<equiv> [F]y)\<close>
    using "=D-simple:1"[THEN "\<equiv>E"(1)] by blast
  AOT_hence 2: \<open>[\<Pi>]x \<equiv> [\<Pi>]y\<close> if \<open>\<Pi>\<down>\<close> for \<Pi>
    using "qml:2"[axiom_inst, THEN "\<rightarrow>E"] "\<forall>E"(1) that by blast
  AOT_have \<open>y = x\<close>
  proof(rule "raa-cor:1")
    AOT_assume \<open>\<not>y = x\<close>
    AOT_hence \<open>y \<noteq> x\<close>
       by (metis "=-infix" "\<equiv>\<^sub>d\<^sub>fI")
    AOT_hence \<open>\<exists>F \<not>([F]y \<equiv> [F]x)\<close>
      using 0[THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"], THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by simp
    then AOT_obtain F where \<open>\<not>([F]y \<equiv> [F]x)\<close>
      using "\<exists>E"[rotated] by blast
    moreover AOT_have \<open>[F]y \<equiv> [F]x\<close>
      using 1[THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"]] "\<forall>E"(2)
      "Commutativity of \<equiv>" "intro-elim:3:b"
      by blast
    ultimately AOT_show \<open>p & \<not>p\<close> for p
       by (metis "raa-cor:3")
  qed
  AOT_thus \<open>x = y\<close>
    using id_sym by blast
qed

AOT_theorem "id-nec4:1": \<open>x =\<^sub>D y \<equiv> \<box>(x =\<^sub>D y)\<close>
proof (rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>x =\<^sub>D y\<close>
  AOT_hence \<open>\<box>\<forall>F ([F]x \<equiv> [F]y)\<close>
    using "=D-simple:1" "\<equiv>E" by blast
  AOT_hence \<open>\<box>\<box>\<forall>F ([F]x \<equiv> [F]y)\<close>
    using "S5Basic:5" "vdash-properties:6" by blast
  AOT_thus \<open>\<box>(x =\<^sub>D y)\<close>
    apply (AOT_subst \<open>x =\<^sub>D y\<close> \<open>\<box>\<forall>F ([F]x \<equiv> [F]y)\<close>)
    using "=D-simple:1" "\<equiv>E" by blast
next
  AOT_assume \<open>\<box>(x =\<^sub>D y)\<close>
  AOT_thus \<open>x =\<^sub>D y\<close> using "qml:2"[axiom_inst, THEN "\<rightarrow>E"] by blast
qed

AOT_theorem "disc=Dequiv:2": \<open>x =\<^sub>D y \<rightarrow> y =\<^sub>D x\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>x =\<^sub>D y\<close>
  AOT_hence \<open>\<box>\<forall>F([F]x \<equiv> [F]y)\<close>
    by (metis "=D-simple:1" "intro-elim:3:a")
  AOT_hence \<open>\<box>\<forall>F([F]y \<equiv> [F]x)\<close>
    by (metis "RM:3" "cqt-basic:11" "intro-elim:3:a")
  AOT_thus \<open>y =\<^sub>D x\<close>
    by (metis "=D-simple:1" "intro-elim:3:b")
qed

AOT_theorem "disc=Dequiv:3": \<open>x =\<^sub>D y & y =\<^sub>D z \<rightarrow> x =\<^sub>D z\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>x =\<^sub>D y & y =\<^sub>D z\<close>
  AOT_hence \<open>\<box>\<forall>F([F]x \<equiv> [F]y)\<close> and \<open>\<box>\<forall>F([F]y \<equiv> [F]z)\<close>
    using "=D-simple:1" "intro-elim:3:a" "&E" by blast+
  AOT_hence \<open>\<box>(\<forall>F([F]x \<equiv> [F]y) & \<forall>F([F]y \<equiv> [F]z))\<close>
    by (smt (verit) "KBasic:3" "df-simplify:1" "intro-elim:3:b")
  moreover AOT_have \<open>\<box>(\<forall>F([F]x \<equiv> [F]y) & \<forall>F([F]y \<equiv> [F]z)) \<rightarrow> \<box>\<forall>F([F]x \<equiv> [F]z)\<close>
    apply (rule RM)
    by (simp add: "cqt-basic:10")
  ultimately AOT_have \<open>\<box>\<forall>F([F]x \<equiv> [F]z)\<close>
    using "vdash-properties:6" by blast
  AOT_thus \<open>x =\<^sub>D z\<close>
    by (metis "=D-simple:1" "intro-elim:3:b")
qed

AOT_theorem "disc=Dequiv:1": \<open>x =\<^sub>D x\<close>
  by (safe intro!: "=D-simple:1"[THEN "\<equiv>E"(2)] RN "\<equiv>I" "\<rightarrow>I" GEN)

AOT_theorem "disc-=D=:1": \<open>D!x \<or> D!y \<rightarrow> \<box>(x = y \<equiv> x =\<^sub>D y)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>D!x \<or> D!y\<close>
  {
    fix x y
    AOT_assume Dx: \<open>D!x\<close>
    AOT_have \<open>(x = y \<equiv> x =\<^sub>D y)\<close>
    proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
      AOT_assume \<open>x = y\<close>
      AOT_thus \<open>x =\<^sub>D y\<close>
        using "disc=Dequiv:1" "rule=E" by fast
    next
      AOT_assume \<open>x =\<^sub>D y\<close>
      AOT_thus \<open>x = y\<close>
        using "=D-simple:2"[THEN "\<rightarrow>E", OF Dx, THEN "\<rightarrow>E"] by blast
    qed
  } note 1 = this
  {
    AOT_assume \<open>D!x\<close>
    AOT_hence \<open>(x = y \<equiv> x =\<^sub>D y)\<close>
      using 1 by blast
    moreover AOT_have \<open>(x = y) \<equiv> \<box>(x = y)\<close>
      by (simp add: "id-nec:2" "intro-elim:2" "qml:2" "vdash-properties:1[2]")
    moreover AOT_have \<open>(x =\<^sub>D y) \<equiv> \<box>(x =\<^sub>D y)\<close> using "id-nec4:1" by blast
    ultimately AOT_have \<open>\<box>(x = y \<equiv> x =\<^sub>D y)\<close>
    proof (safe intro!: "sc-eq-box-box:4"[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "&I")
      AOT_show \<open>\<box>(x = y \<rightarrow> \<box>x = y)\<close>
        by (simp add: "id-nec:1" RN)
    next
      AOT_show \<open>\<box>(x =\<^sub>D y \<rightarrow> \<box>x =\<^sub>D y)\<close>
        using "id-nec4:1"
        by (meson "if-p-then-p" "rule-sub-remark:6[1]" RN)
    next
      AOT_assume \<open>x = y \<equiv> x =\<^sub>D y\<close>
      moreover AOT_assume \<open>x = y \<equiv> \<box>x = y\<close>
      moreover AOT_assume \<open>x =\<^sub>D y \<equiv> \<box>x =\<^sub>D y\<close>
      ultimately AOT_show \<open>\<box>x = y \<equiv> \<box>x =\<^sub>D y\<close>
        using "intro-elim:3:f" by blast
    qed
  }
  moreover {
    AOT_assume Dy: \<open>D!y\<close>
    AOT_hence 0: \<open>y = x \<equiv> y =\<^sub>D x\<close>
      using 1 by blast
    AOT_hence \<open>x = y \<equiv> x =\<^sub>D y\<close>
    proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
      AOT_assume 2: \<open>x = y\<close>
      AOT_hence 3: \<open>y = x\<close> using id_sym by blast
      AOT_hence \<open>y =\<^sub>D x\<close> using 0[THEN "\<equiv>E"(1)] by blast
      AOT_thus \<open>x =\<^sub>D y\<close>
        using "1" "2" "3" "intro-elim:3:a" "rule=E" Dy by blast
    next
      AOT_assume \<open>x =\<^sub>D y\<close>
      AOT_thus \<open>x = y\<close>
        by (metis "0" "disc=Dequiv:2" "id-eq:2" "intro-elim:2" "intro-elim:3:b")
    qed
    moreover AOT_have \<open>(x = y) \<equiv> \<box>(x = y)\<close>
      by (simp add: "id-nec:2" "intro-elim:2" "qml:2" "vdash-properties:1[2]")
    moreover AOT_have \<open>(x =\<^sub>D y) \<equiv> \<box>(x =\<^sub>D y)\<close> using "id-nec4:1" by blast
    ultimately AOT_have \<open>\<box>(x = y \<equiv> x =\<^sub>D y)\<close>
    proof (safe intro!: "sc-eq-box-box:4"[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "&I")
      AOT_show \<open>\<box>(x = y \<rightarrow> \<box>x = y)\<close>
        by (simp add: "id-nec:1" RN)
    next
      AOT_show \<open>\<box>(x =\<^sub>D y \<rightarrow> \<box>x =\<^sub>D y)\<close>
        using "id-nec4:1"
        by (meson "if-p-then-p" "rule-sub-remark:6[1]" RN)
    next
      AOT_assume \<open>x = y \<equiv> x =\<^sub>D y\<close>
      moreover AOT_assume \<open>x = y \<equiv> \<box>x = y\<close>
      moreover AOT_assume \<open>x =\<^sub>D y \<equiv> \<box>x =\<^sub>D y\<close>
      ultimately AOT_show \<open>\<box>x = y \<equiv> \<box>x =\<^sub>D y\<close>
        using "intro-elim:3:f" by blast
    qed
  }
  ultimately AOT_show \<open>\<box>(x = y \<equiv> x =\<^sub>D y)\<close>
    using 0 by (metis "con-dis-i-e:4:b" "raa-cor:1")
qed

AOT_theorem ord_disc: \<open>O!x \<rightarrow> D!x\<close>
proof(safe intro!: "\<rightarrow>I" Discernible_equiv[THEN "\<equiv>E"(2)])
  AOT_assume \<open>O!x\<close>
  AOT_hence \<open>\<box>O!x\<close>
    by (metis "oa-facts:1" "vdash-properties:10")
  moreover AOT_have \<open>\<box>O!x \<rightarrow> \<box>\<forall>y (y \<noteq> x \<rightarrow> \<exists>F \<not>([F]y \<equiv> [F]x))\<close>
  proof(rule RM; safe intro!: "\<rightarrow>I" GEN "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>[\<lambda>z z =\<^sub>E x]\<guillemotright>\<close>] "cqt:2")
    AOT_modally_strict {
      fix y
      AOT_assume Ox: \<open>O!x\<close>
      AOT_assume \<open>y \<noteq> x\<close>
      AOT_hence 0: \<open>\<not>y = x\<close>
        using "=-infix"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by auto
      AOT_show \<open>\<not>([\<lambda>z z =\<^sub>E x]y \<equiv> [\<lambda>z z =\<^sub>E x]x)\<close>
      proof(rule "raa-cor:2")
        AOT_assume \<open>[\<lambda>z z =\<^sub>E x]y \<equiv> [\<lambda>z z =\<^sub>E x]x\<close>
        moreover AOT_have \<open>[\<lambda>z z =\<^sub>E x]x\<close>
          apply (safe intro!: "\<beta>\<leftarrow>C" "cqt:2")
          using "ord=Eequiv:1" "vdash-properties:10" Ox by blast
        ultimately AOT_have \<open>[\<lambda>z z =\<^sub>E x]y\<close>
          using "\<equiv>E" by blast
        AOT_hence \<open>y =\<^sub>E x\<close>
          using "\<beta>\<rightarrow>C" by blast
        AOT_hence \<open>y = x\<close>
          using "=E-simple:2"[THEN "\<rightarrow>E"] by blast
        AOT_thus \<open>y = x & \<not>y = x\<close> using 0 "&I" by blast
      qed
    }
  qed
  ultimately AOT_show \<open>\<box>\<forall>y (y \<noteq> x \<rightarrow> \<exists>F \<not>([F]y \<equiv> [F]x))\<close>
    using "\<rightarrow>E" by blast
qed

AOT_register_rigid_restricted_type
  Discernible: \<open>D!\<kappa>\<close>
proof
  AOT_modally_strict {
    AOT_obtain x where \<open>O!x\<close>
      using "o-objects-exist:1"[THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"]] "\<exists>E"[rotated] by blast
    AOT_hence \<open>D!x\<close> using ord_disc[THEN "\<rightarrow>E"] by blast
    AOT_thus \<open>\<exists>x D!x\<close> by (rule "\<exists>I")
  }
next
  AOT_modally_strict {
    AOT_show \<open>D!\<kappa> \<rightarrow> \<kappa>\<down>\<close> for \<kappa>
      by (simp add: "deduction-theorem" "russell-axiom[exe,1].\<psi>_denotes_asm")
  }
next
  AOT_modally_strict {
    AOT_show \<open>\<box>(D!x \<rightarrow> \<box>D!x)\<close> for x
    proof (rule RN; rule "\<rightarrow>I")
      AOT_modally_strict {
        AOT_assume \<open>D!x\<close>
        AOT_hence 0: \<open>\<box>\<forall>y(y \<noteq> x \<rightarrow> \<exists>F \<not>([F]y \<equiv> [F]x))\<close>
          using Discernible_equiv[THEN "\<equiv>E"(1)] by blast
        AOT_have 1: \<open>\<box>\<box>(\<forall>y(y \<noteq> x \<rightarrow> \<exists>F \<not>([F]y \<equiv> [F]x)))\<close>
          using "0" "S5Basic:6" "intro-elim:3:a" by blast
        AOT_thus \<open>\<box>D!x\<close>
          apply (AOT_subst \<open>D!x\<close> \<open>\<box>\<forall>y(y \<noteq> x \<rightarrow> \<exists>F \<not>([F]y \<equiv> [F]x))\<close>)
          using Discernible_equiv by auto
      }
    qed
  }
qed
(*
text\<open>We have already introduced the restricted type of Ordinary objects in the
     Extended Relation Comprehension theory. However, make sure all variable names
     are defined as expected (avoiding conflicts with situations
     of possible world theory).\<close>
AOT_register_variable_names
  Discernible: u v r t s
*)

section\<open>Natural Numbers\<close>
 
AOT_define CorrelatesOneToOne :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>_ |: _ \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> _\<close>)
  "1-1-cor": \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> G \<equiv>\<^sub>d\<^sub>f R\<down> & F\<down> & G\<down> &
                                   \<forall>x ([F]x \<rightarrow> \<exists>!y([G]y & [R]xy)) &
                                   \<forall>y ([G]y \<rightarrow> \<exists>!x([F]x & [R]xy))\<close>

AOT_define MapsTo :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>_ |: _ \<longrightarrow> _\<close>)
  "fFG:1": \<open>R |: F \<longrightarrow> G \<equiv>\<^sub>d\<^sub>f R\<down> & F\<down> & G\<down> & \<forall>x ([F]x \<rightarrow> \<exists>!y([G]y & [R]xy))\<close>

AOT_define MapsToOneToOne :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>_ |: _ \<^sub>1\<^sub>-\<^sub>1\<longrightarrow> _\<close>)
  "fFG:2": \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow> G \<equiv>\<^sub>d\<^sub>f
      R |: F \<longrightarrow> G & \<forall>x\<forall>y\<forall>z (([F]x & [F]y & [G]z) \<rightarrow> ([R]xz & [R]yz \<rightarrow> x = y))\<close>

AOT_define MapsOnto :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>_ |: _ \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>o _\<close>)
  "fFG:3": \<open>R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>o G \<equiv>\<^sub>d\<^sub>f R |: F \<longrightarrow> G & \<forall>y ([G]y \<rightarrow> \<exists>x([F]x & [R]xy))\<close>

AOT_define MapsOneToOneOnto :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>_ |: _ \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>o _\<close>)
  "fFG:4": \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>o G \<equiv>\<^sub>d\<^sub>f R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow> G & R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>o G\<close>

AOT_theorem "eq-1-1": \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> G \<equiv> R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>o G\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> G\<close>
  AOT_hence A: \<open>\<forall>x ([F]x \<rightarrow> \<exists>!y([G]y & [R]xy))\<close>
        and B: \<open>\<forall>y ([G]y \<rightarrow> \<exists>!x([F]x & [R]xy))\<close>
    using "\<equiv>\<^sub>d\<^sub>fE"[OF "1-1-cor"] "&E" by blast+
  AOT_have C: \<open>R |: F \<longrightarrow> G\<close>
  proof (rule "\<equiv>\<^sub>d\<^sub>fI"[OF "fFG:1"]; rule "&I")
    AOT_show \<open>R\<down> & F\<down> & G\<down>\<close>
      using "cqt:2[const_var]"[axiom_inst] "&I" by metis
  next
    AOT_show \<open>\<forall>x ([F]x \<rightarrow> \<exists>!y([G]y & [R]xy))\<close> by (rule A)
  qed
  AOT_show \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>o G\<close>
  proof (rule "\<equiv>\<^sub>d\<^sub>fI"[OF "fFG:4"]; rule "&I")
    AOT_show \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow> G\<close>
    proof (rule "\<equiv>\<^sub>d\<^sub>fI"[OF "fFG:2"]; rule "&I")
      AOT_show \<open>R |: F \<longrightarrow> G\<close> using C.
    next
      AOT_show \<open>\<forall>x\<forall>y\<forall>z ([F]x & [F]y & [G]z \<rightarrow> ([R]xz & [R]yz \<rightarrow> x = y))\<close>
      proof(rule GEN; rule GEN; rule GEN; rule "\<rightarrow>I"; rule "\<rightarrow>I")
        fix x y z
        AOT_assume 1: \<open>[F]x & [F]y & [G]z\<close>
        moreover AOT_assume 2: \<open>[R]xz & [R]yz\<close>
        ultimately AOT_have 3: \<open>\<exists>!x ([F]x & [R]xz)\<close>
          using B "&E" "\<forall>E" "\<rightarrow>E" by fast
        AOT_show \<open>x = y\<close>
          by (rule "uni-most"[THEN "\<rightarrow>E", OF 3, THEN "\<forall>E"(2)[where \<beta>=x],
                              THEN "\<forall>E"(2)[where \<beta>=y], THEN "\<rightarrow>E"])
             (metis "&I" "&E" 1 2)
      qed
    qed
  next
    AOT_show \<open>R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>o G\<close>
    proof (rule "\<equiv>\<^sub>d\<^sub>fI"[OF "fFG:3"]; rule "&I")
      AOT_show \<open>R |: F \<longrightarrow> G\<close> using C.
    next
      AOT_show \<open>\<forall>y ([G]y \<rightarrow> \<exists>x ([F]x & [R]xy))\<close>
      proof(rule GEN; rule "\<rightarrow>I")
        fix y
        AOT_assume \<open>[G]y\<close>
        AOT_hence \<open>\<exists>!x ([F]x & [R]xy)\<close>
          using B[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
        AOT_hence \<open>\<exists>x ([F]x & [R]xy & \<forall>\<beta> (([F]\<beta> & [R]\<beta>y) \<rightarrow> \<beta> = x))\<close>
          using "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
        then AOT_obtain x where \<open>[F]x & [R]xy\<close>
          using "\<exists>E"[rotated] "&E" by blast
        AOT_thus \<open>\<exists>x ([F]x & [R]xy)\<close> by (rule "\<exists>I")
      qed
    qed
  qed
next
  AOT_assume \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>o G\<close>
  AOT_hence \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow> G\<close> and \<open>R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>o G\<close>
    using "\<equiv>\<^sub>d\<^sub>fE"[OF "fFG:4"] "&E" by blast+
  AOT_hence C: \<open>R |: F \<longrightarrow> G\<close>
    and D: \<open>\<forall>x\<forall>y\<forall>z ([F]x & [F]y & [G]z \<rightarrow> ([R]xz & [R]yz \<rightarrow> x = y))\<close>
    and E: \<open>\<forall>y ([G]y \<rightarrow> \<exists>x ([F]x & [R]xy))\<close>
    using "\<equiv>\<^sub>d\<^sub>fE"[OF "fFG:2"] "\<equiv>\<^sub>d\<^sub>fE"[OF "fFG:3"] "&E" by blast+
  AOT_show \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> G\<close>
  proof(rule "1-1-cor"[THEN "\<equiv>\<^sub>d\<^sub>fI"]; safe intro!: "&I" "cqt:2[const_var]"[axiom_inst])
    AOT_show \<open>\<forall>x ([F]x \<rightarrow> \<exists>!y ([G]y & [R]xy))\<close>
      using "\<equiv>\<^sub>d\<^sub>fE"[OF "fFG:1", OF C] "&E" by blast
  next
    AOT_show \<open>\<forall>y ([G]y \<rightarrow> \<exists>!x ([F]x & [R]xy))\<close>
    proof (rule "GEN"; rule "\<rightarrow>I")
      fix y
      AOT_assume 0: \<open>[G]y\<close>
      AOT_hence \<open>\<exists>x ([F]x & [R]xy)\<close>
        using E "\<forall>E" "\<rightarrow>E" by fast
      then AOT_obtain a where a_prop: \<open>[F]a & [R]ay\<close>
        using "\<exists>E"[rotated] by blast
      moreover AOT_have \<open>\<forall>z ([F]z & [R]zy \<rightarrow> z = a)\<close>
      proof (rule GEN; rule "\<rightarrow>I")
        fix z
        AOT_assume \<open>[F]z & [R]zy\<close>
        AOT_thus \<open>z = a\<close>
          using D[THEN "\<forall>E"(2)[where \<beta>=z], THEN "\<forall>E"(2)[where \<beta>=a],
                  THEN "\<forall>E"(2)[where \<beta>=y], THEN "\<rightarrow>E", THEN "\<rightarrow>E"]
                a_prop 0 "&E" "&I" by metis
      qed
      ultimately AOT_have \<open>\<exists>x ([F]x & [R]xy & \<forall>z ([F]z & [R]zy \<rightarrow> z = x))\<close>
        using "&I" "\<exists>I"(2) by fast
      AOT_thus \<open>\<exists>!x ([F]x & [R]xy)\<close>
        using "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] by fast
    qed
  qed
qed

AOT_define AOT_exists_unique_D :: \<open>\<alpha> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close>
  "equi:1":  \<open>\<guillemotleft>AOT_exists_unique_D \<phi>\<guillemotright> \<equiv>\<^sub>d\<^sub>f \<exists>\<alpha> (\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>))\<close>
syntax "_AOT_exists_unique_D" :: \<open>\<alpha> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> ("\<exists>!\<^sub>D_ _" [1,40])
AOT_syntax_print_translations
  "_AOT_exists_unique_D \<tau> \<phi>" <= "CONST AOT_exists_unique_D (_abs \<tau> \<phi>)"
syntax
   "_AOT_exists_unique_ellipse_D" :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close>
   (\<open>\<exists>!\<^sub>D_...\<exists>!\<^sub>D_ _\<close> [1,40])
parse_ast_translation\<open>
[(\<^syntax_const>\<open>_AOT_exists_unique_ellipse_D\<close>,
  fn ctx => fn [a,b,c] => Ast.mk_appl (Ast.Constant "AOT_exists_unique_D")
  [parseEllipseList "_AOT_vars" ctx [a,b],c]),
 (\<^syntax_const>\<open>_AOT_exists_unique_D\<close>,
  AOT_restricted_binder
    \<^const_name>\<open>AOT_exists_unique_D\<close>
    \<^const_syntax>\<open>AOT_conj\<close>)]\<close>
print_translation\<open>AOT_syntax_print_translations [
  AOT_preserve_binder_abs_tr'
    \<^const_syntax>\<open>AOT_exists_unique_D\<close>
    \<^syntax_const>\<open>_AOT_exists_unique_D\<close>
    (\<^syntax_const>\<open>_AOT_exists_unique_ellipse_D\<close>, true)
    \<^const_name>\<open>AOT_conj\<close>,
  AOT_binder_trans
    @{theory}
    @{binding "AOT_exists_unique_binder_D"}
    \<^syntax_const>\<open>_AOT_exists_unique_D\<close>
]\<close>

AOT_register_variable_names
  Individual: u v t s r

AOT_define CorrelatesDOneToOne :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>_ |: _ \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D _\<close>)
  "equi:2": \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G \<equiv>\<^sub>d\<^sub>f R\<down> & F\<down> & G\<down> &
                               \<forall>u ([F]u \<rightarrow> \<exists>!\<^sub>Dv([G]v & [R]uv)) &
                               \<forall>v ([G]v \<rightarrow> \<exists>!\<^sub>Du([F]u & [R]uv))\<close>

AOT_define EquinumerousE :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl "\<approx>\<^sub>D" 50)
  "equi:3": \<open>F \<approx>\<^sub>D G \<equiv>\<^sub>d\<^sub>f \<exists>R (R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G)\<close>

text\<open>Note: not explicitly in PLM.\<close>
AOT_theorem eq_den_1: \<open>\<Pi>\<down>\<close> if \<open>\<Pi> \<approx>\<^sub>D \<Pi>'\<close>
proof -
  AOT_have \<open>\<exists>R (R |: \<Pi> \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D \<Pi>')\<close>
    using "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fE"] that by blast
  then AOT_obtain R where \<open>R |: \<Pi> \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D \<Pi>'\<close>
    using "\<exists>E"[rotated] by blast
  AOT_thus \<open>\<Pi>\<down>\<close>
    using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
qed

text\<open>Note: not explicitly in PLM.\<close>
AOT_theorem eq_den_2: \<open>\<Pi>'\<down>\<close> if \<open>\<Pi> \<approx>\<^sub>D \<Pi>'\<close>
proof -
  AOT_have \<open>\<exists>R (R |: \<Pi> \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D \<Pi>')\<close>
    using "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fE"] that by blast
  then AOT_obtain R where \<open>R |: \<Pi> \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D \<Pi>'\<close>
    using "\<exists>E"[rotated] by blast
  AOT_thus \<open>\<Pi>'\<down>\<close>
    using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
qed

AOT_theorem "eq-part:1": \<open>F \<approx>\<^sub>D F\<close>
proof (safe intro!: "&I" GEN "\<rightarrow>I" "cqt:2[const_var]"[axiom_inst]
                    "\<equiv>\<^sub>d\<^sub>fI"[OF "equi:3"] "\<equiv>\<^sub>d\<^sub>fI"[OF "equi:2"] "\<exists>I"(1))
  fix x
  AOT_assume 2: \<open>[F]x\<close>
  AOT_show \<open>\<exists>!\<^sub>Dv ([F]v & x =\<^sub>D v)\<close>
  proof(rule "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"];
        rule "\<exists>I"(2)[where \<beta>=x];
        safe dest!: "&E"(2)
             intro!:  "&I" "\<rightarrow>I" 2 GEN "disc=Dequiv:1")
    AOT_show \<open>v =\<^sub>D x\<close> if \<open>x =\<^sub>D v\<close> for v
      by (metis that "disc=Dequiv:2"[THEN "\<rightarrow>E"])
  qed
next
  fix y
  AOT_assume 2: \<open>[F]y\<close>
  AOT_show \<open>\<exists>!\<^sub>Du ([F]u & u =\<^sub>D y)\<close>
    by(safe dest!: "&E"(2)
            intro!: "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(2)[where \<beta>=y]
                    "&I" "\<rightarrow>I" 2 GEN "disc=Dequiv:1")
qed(auto simp: "=D[denotes]")


AOT_theorem "eq-part:2": \<open>F \<approx>\<^sub>D G \<rightarrow> G \<approx>\<^sub>D F\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>F \<approx>\<^sub>D G\<close>
  AOT_hence \<open>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
    using "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain R where \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence 0: \<open>R\<down> & F\<down> & G\<down> & \<forall>u ([F]u \<rightarrow> \<exists>!\<^sub>Dv([G]v & [R]uv)) &
                            \<forall>v ([G]v \<rightarrow> \<exists>!\<^sub>Du([F]u & [R]uv))\<close>
    using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast

  AOT_have \<open>[\<lambda>xy [R]yx]\<down> & G\<down> & F\<down> & \<forall>u ([G]u \<rightarrow> \<exists>!\<^sub>Dv([F]v & [\<lambda>xy [R]yx]uv)) &
                            \<forall>v ([F]v \<rightarrow> \<exists>!\<^sub>Du([G]u & [\<lambda>xy [R]yx]uv))\<close>
  proof (AOT_subst \<open>[\<lambda>xy [R]yx]yx\<close> \<open>[R]xy\<close> for: x y;
        (safe intro!: "&I" "cqt:2[const_var]"[axiom_inst] 0[THEN "&E"(2)]
                      0[THEN "&E"(1), THEN "&E"(2)]; "cqt:2[lambda]")?)
    AOT_modally_strict {
      AOT_have \<open>[\<lambda>xy [R]yx]xy\<close> if \<open>[R]yx\<close> for y x
        by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2"
                 simp: "&I" "ex:1:a" prod_denotesI "rule-ui:3" that)
      moreover AOT_have \<open>[R]yx\<close> if \<open>[\<lambda>xy [R]yx]xy\<close> for y x
        using "\<beta>\<rightarrow>C"(1)[where \<phi>="\<lambda>(x,y). _ (x,y)" and \<kappa>\<^sub>1\<kappa>\<^sub>n="(_,_)",
                        simplified, OF that, simplified].
      ultimately AOT_show \<open>[\<lambda>xy [R]yx]\<alpha>\<beta> \<equiv> [R]\<beta>\<alpha>\<close> for \<alpha> \<beta>
        by (metis "deduction-theorem" "\<equiv>I")
    }
  qed
  AOT_hence \<open>[\<lambda>xy [R]yx] |: G \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D F\<close>
    using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
  AOT_hence \<open>\<exists>R R |: G \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D F\<close>
    by (rule "\<exists>I"(1)) "cqt:2[lambda]"
  AOT_thus \<open>G \<approx>\<^sub>D F\<close>
    using "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
qed

text\<open>Note: not explicitly in PLM.\<close>
AOT_theorem "eq-part:2[terms]": \<open>\<Pi> \<approx>\<^sub>D \<Pi>' \<rightarrow> \<Pi>' \<approx>\<^sub>D \<Pi>\<close>
  using "eq-part:2"[unvarify F G] eq_den_1 eq_den_2 "\<rightarrow>I" by meson
declare "eq-part:2[terms]"[THEN "\<rightarrow>E", sym]

AOT_theorem "eq-part:3": \<open>(F \<approx>\<^sub>D G & G \<approx>\<^sub>D H) \<rightarrow> F \<approx>\<^sub>D H\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>F \<approx>\<^sub>D G & G \<approx>\<^sub>D H\<close>
  then AOT_obtain R\<^sub>1 and R\<^sub>2 where
       \<open>R\<^sub>1 |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
   and \<open>R\<^sub>2 |: G \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D H\<close>
    using "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" "\<exists>E"[rotated] by metis
  AOT_hence \<theta>: \<open>\<forall>u ([F]u \<rightarrow> \<exists>!\<^sub>Dv([G]v & [R\<^sub>1]uv)) & \<forall>v ([G]v \<rightarrow> \<exists>!\<^sub>Du([F]u & [R\<^sub>1]uv))\<close>
        and \<xi>: \<open>\<forall>u ([G]u \<rightarrow> \<exists>!\<^sub>Dv([H]v & [R\<^sub>2]uv)) & \<forall>v ([H]v \<rightarrow> \<exists>!\<^sub>Du([G]u & [R\<^sub>2]uv))\<close>
    using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2)]
          "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(1), THEN "&E"(2)]
          "&I" by blast+
  AOT_have \<open>\<exists>R R = [\<lambda>xy \<exists>v ([G]v & [R\<^sub>1]xv & [R\<^sub>2]vy)]\<close>
    by (rule "free-thms:3[lambda]") cqt_2_lambda_inst_prover
  then AOT_obtain R where R_def: \<open>R = [\<lambda>xy \<exists>v ([G]v & [R\<^sub>1]xv & [R\<^sub>2]vy)]\<close>
    using "\<exists>E"[rotated] by blast
  AOT_have 1: \<open>\<exists>!\<^sub>Dv (([H]v & [R]uv))\<close> if b: \<open>[F]u\<close> for u
  proof (rule "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
    AOT_obtain b where
      b_prop: \<open>([G]b & [R\<^sub>1]ub & \<forall>v ([G]v & [R\<^sub>1]uv \<rightarrow> v =\<^sub>D b))\<close>
      using \<theta>[THEN "&E"(1), THEN "\<forall>E"(2), THEN "\<rightarrow>E",
              OF b, THEN "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"]]
            "\<exists>E"[rotated] by blast
    AOT_obtain c where
      c_prop: "([H]c & [R\<^sub>2]bc & \<forall>v ([H]v & [R\<^sub>2]bv \<rightarrow> v =\<^sub>D c))"
      using \<xi>[THEN "&E"(1), THEN "\<forall>E"(2)[where \<beta>=b], THEN "\<rightarrow>E",
              OF b_prop[THEN "&E"(1), THEN "&E"(1)], THEN "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"]]
            "\<exists>E"[rotated] by blast
    AOT_show \<open>\<exists>v ([H]v & [R]uv & \<forall>v' ([H]v' & [R]uv' \<rightarrow> v' =\<^sub>D v))\<close>
    proof (safe intro!: "&I" GEN "\<rightarrow>I" "\<exists>I"(2)[where \<beta>=c])
      AOT_show \<open>[H]c\<close> using c_prop "&E" by blast
    next
      AOT_have 0: \<open>\<exists>v ([G]v & [R\<^sub>1]uv & [R\<^sub>2]vc)\<close>
        by (safe intro!: "&I" c_prop[THEN "&E"(1)] "\<exists>I"(2)[where \<beta>=b]
                         b_prop[THEN "&E"(1)]
                         c_prop[THEN "&E"(1), THEN "&E"(2)])
      AOT_show \<open>[R]uc\<close>
        by (auto intro: "rule=E"[rotated, OF R_def[symmetric]]
                 intro!: "\<beta>\<leftarrow>C"(1) "cqt:2"
                 simp: "&I" "ex:1:a" prod_denotesI "rule-ui:3" 0)
    next
      fix x
      AOT_assume \<open>[H]x & [R]ux\<close>
      AOT_hence hx: \<open>[H]x\<close> and \<open>[R]ux\<close> using "&E" by blast+
      AOT_hence \<open>[\<lambda>xy \<exists>v ([G]v & [R\<^sub>1]xv & [R\<^sub>2]vy)]ux\<close>
        using "rule=E"[rotated, OF R_def] by fast
      AOT_hence \<open>\<exists>v ([G]v & [R\<^sub>1]uv & [R\<^sub>2]vx)\<close>
        by (rule "\<beta>\<rightarrow>C"(1)[where \<phi>="\<lambda>(\<kappa>,\<kappa>'). _ \<kappa> \<kappa>'" and \<kappa>\<^sub>1\<kappa>\<^sub>n="(_,_)", simplified])
      then AOT_obtain z where z_prop: \<open>([G]z & [R\<^sub>1]uz & [R\<^sub>2]zx)\<close>
        using "&E" "\<exists>E"[rotated] by blast
      AOT_hence \<open>z =\<^sub>D b\<close>
        using b_prop[THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=z]]
        using "&E" "\<rightarrow>E" by metis
      AOT_hence \<open>\<forall>F([F]z \<equiv> [F]b)\<close>
        using "=D-simple:1"[THEN "\<equiv>E"(1), THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"]] by blast
      moreover AOT_have \<open>[\<lambda>z [R\<^sub>2]zx]\<down>\<close> by "cqt:2"
      ultimately AOT_have \<open>[\<lambda>z [R\<^sub>2]zx]z \<equiv> [\<lambda>z [R\<^sub>2]zx]b\<close>
        using "\<forall>E"(1) by blast
      moreover AOT_have \<open>[\<lambda>z [R\<^sub>2]zx]z\<close>
        by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2" z_prop[THEN "&E"(2)])
      ultimately AOT_have \<open>[\<lambda>z [R\<^sub>2]zx]b\<close>
        using "\<equiv>E" by blast
      AOT_hence \<open>[R\<^sub>2]bx\<close>
        using "\<beta>\<rightarrow>C" by blast
      AOT_thus \<open>x =\<^sub>D c\<close>
        using c_prop[THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=x],
                     THEN "\<rightarrow>E"]
              hx "&I" by blast
    qed
  qed
  AOT_have 2: \<open>\<exists>!\<^sub>Du (([F]u & [R]uv))\<close> if b: \<open>[H]v\<close> for v
  proof (rule "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
    AOT_obtain b where
      b_prop: \<open>([G]b & [R\<^sub>2]bv & \<forall>u ([G]u & [R\<^sub>2]uv \<rightarrow> u =\<^sub>D b))\<close>
      using \<xi>[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E",
              OF b, THEN "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"]]
            "\<exists>E"[rotated] by blast
    AOT_obtain c where
      c_prop: "([F]c & [R\<^sub>1]cb & \<forall>v ([F]v & [R\<^sub>1]vb \<rightarrow> v =\<^sub>D c))"
      using \<theta>[THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=b], THEN "\<rightarrow>E",
              OF b_prop[THEN "&E"(1), THEN "&E"(1)],
              THEN "\<equiv>\<^sub>d\<^sub>fE"[OF "equi:1"]]
    "\<exists>E"[rotated] by blast
    AOT_show \<open>\<exists>u ([F]u & [R]uv & \<forall>v' ([F]v' & [R]v'v \<rightarrow> v' =\<^sub>D u))\<close>
    proof (safe intro!: "&I" GEN "\<rightarrow>I" "\<exists>I"(2)[where \<beta>=c])
      AOT_show \<open>[F]c\<close> using c_prop "&E" by blast
    next
      AOT_have \<open>\<exists>u ([G]u & [R\<^sub>1]cu & [R\<^sub>2]uv)\<close>
        by (safe intro!: "&I" "\<exists>I"(2)[where \<beta>=b] 
                     b_prop[THEN "&E"(1), THEN "&E"(1)]
                     b_prop[THEN "&E"(1), THEN "&E"(2)]
                     c_prop[THEN "&E"(1), THEN "&E"(2)])
      AOT_thus \<open>[R]cv\<close>
        by (auto intro: "rule=E"[rotated, OF R_def[symmetric]]
                 intro!: "\<beta>\<leftarrow>C"(1) "cqt:2"
                 simp: "&I" "ex:1:a" prod_denotesI "rule-ui:3")
    next
      fix x
      AOT_assume \<open>[F]x & [R]xv\<close>
      AOT_hence hx: \<open>[F]x\<close> and \<open>[R]xv\<close> using "&E" by blast+
      AOT_hence \<open>[\<lambda>xy \<exists>v ([G]v & [R\<^sub>1]xv & [R\<^sub>2]vy)]xv\<close>
        using "rule=E"[rotated, OF R_def] by fast
      AOT_hence \<open>\<exists>u ([G]u & [R\<^sub>1]xu & [R\<^sub>2]uv)\<close>
        by (rule "\<beta>\<rightarrow>C"(1)[where \<phi>="\<lambda>(\<kappa>,\<kappa>'). _ \<kappa> \<kappa>'" and \<kappa>\<^sub>1\<kappa>\<^sub>n="(_,_)", simplified])
      then AOT_obtain z where z_prop: \<open>([G]z & [R\<^sub>1]xz & [R\<^sub>2]zv)\<close>
        using "&E" "\<exists>E"[rotated] by blast
      AOT_hence \<open>z =\<^sub>D b\<close>
        using b_prop[THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=z]]
        using "&E" "\<rightarrow>E" "&I" by metis
      AOT_hence \<open>\<forall>F([F]z \<equiv> [F]b)\<close>
        using "=D-simple:1"[THEN "\<equiv>E"(1), THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"]] by blast
      moreover AOT_have \<open>[\<lambda>z [R\<^sub>1]xz]\<down>\<close> by "cqt:2"
      ultimately AOT_have \<open>[\<lambda>z [R\<^sub>1]xz]z \<equiv> [\<lambda>z [R\<^sub>1]xz]b\<close>
        using "\<forall>E"(1) by blast
      moreover AOT_have \<open>[\<lambda>z [R\<^sub>1]xz]z\<close>
        by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2" z_prop[THEN "&E"(1), THEN "&E"(2)])
      ultimately AOT_have \<open>[\<lambda>z [R\<^sub>1]xz]b\<close>
        using "\<equiv>E" by blast
      AOT_hence \<open>[R\<^sub>1]xb\<close>
        using "\<beta>\<rightarrow>C" by blast
      AOT_thus \<open>x =\<^sub>D c\<close>
        using c_prop[THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=x],
                     THEN "\<rightarrow>E"]
              hx "&I" by blast
    qed
  qed
  AOT_show \<open>F \<approx>\<^sub>D H\<close>
    apply (rule "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
    apply (rule "\<exists>I"(2)[where \<beta>=R])
    by (auto intro!: 1 2 "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2[const_var]"[axiom_inst]
                     GEN "\<rightarrow>I")
qed

text\<open>Note: not explicitly in PLM.\<close>
AOT_theorem "eq-part:3[terms]": \<open>\<Pi> \<approx>\<^sub>D \<Pi>''\<close> if \<open>\<Pi> \<approx>\<^sub>D \<Pi>'\<close> and \<open>\<Pi>' \<approx>\<^sub>D \<Pi>''\<close>
  using "eq-part:3"[unvarify F G H, THEN "\<rightarrow>E"] eq_den_1 eq_den_2 "\<rightarrow>I" "&I"
  by (metis that(1) that(2))
declare "eq-part:3[terms]"[trans]

AOT_theorem "eq-part:4": \<open>F \<approx>\<^sub>D G \<equiv> \<forall>H (H \<approx>\<^sub>D F \<equiv> H \<approx>\<^sub>D G)\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume 0: \<open>F \<approx>\<^sub>D G\<close>
  AOT_hence 1: \<open>G \<approx>\<^sub>D F\<close> using "eq-part:2"[THEN "\<rightarrow>E"] by blast
  AOT_show \<open>\<forall>H (H \<approx>\<^sub>D F \<equiv> H \<approx>\<^sub>D G)\<close>
  proof (rule GEN; rule "\<equiv>I"; rule "\<rightarrow>I")
    AOT_show \<open>H \<approx>\<^sub>D G\<close> if \<open>H \<approx>\<^sub>D F\<close> for H using 0
      by (meson "&I" "eq-part:3" that "vdash-properties:6")
  next
    AOT_show \<open>H \<approx>\<^sub>D F\<close> if \<open>H \<approx>\<^sub>D G\<close> for H using 1
      by (metis "&I" "eq-part:3" that "vdash-properties:6")
  qed
next
  AOT_assume \<open>\<forall>H (H \<approx>\<^sub>D F \<equiv> H \<approx>\<^sub>D G)\<close>
  AOT_hence \<open>F \<approx>\<^sub>D F \<equiv> F \<approx>\<^sub>D G\<close> using "\<forall>E" by blast
  AOT_thus \<open>F \<approx>\<^sub>D G\<close> using "eq-part:1" "\<equiv>E" by blast
qed

AOT_define MapsD :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> ("_ |: _ \<longrightarrow>D _")
  "equi-rem:1":
  \<open>R |: F \<longrightarrow>D G \<equiv>\<^sub>d\<^sub>f R\<down> & F\<down> & G\<down> & \<forall>u ([F]u \<rightarrow> \<exists>!\<^sub>Dv ([G]v & [R]uv))\<close>

AOT_define MapsDOneToOne :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> ("_ |: _ \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>D _")
  "equi-rem:2":
  \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>D G \<equiv>\<^sub>d\<^sub>f
      R |: F \<longrightarrow>D G & \<forall>t\<forall>u\<forall>v (([F]t & [F]u & [G]v) \<rightarrow> ([R]tv & [R]uv \<rightarrow> t =\<^sub>D u))\<close>

AOT_define MapsDOnto :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> ("_ |: _ \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oD _")
  "equi-rem:3":
  \<open>R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oD G \<equiv>\<^sub>d\<^sub>f R |: F \<longrightarrow>D G & \<forall>v ([G]v \<rightarrow> \<exists>u ([F]u & [R]uv))\<close>

AOT_define MapsDOneToOneOnto :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> ("_ |: _ \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oD _")
  "equi-rem:4":
  \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oD G \<equiv>\<^sub>d\<^sub>f R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>D G & R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oD G\<close>


AOT_theorem "equi-rem-thm":
  \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G \<rightarrow> R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oD G\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
  AOT_hence 1: \<open>\<forall>u ([F]u \<rightarrow> \<exists>!\<^sub>Dv ([G]v & [R]uv))\<close>
        and 2: \<open>\<forall>v ([G]v \<rightarrow> \<exists>!\<^sub>Du ([F]u & [R]uv))\<close>
    using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_have \<open>R |: F \<longrightarrow>D G\<close>
    by(safe intro!: "equi-rem:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" 1)
  moreover AOT_have \<open>\<forall>v ([G]v \<rightarrow> \<exists>u ([F]u & [R]uv))\<close>
  proof(safe intro!: GEN "\<rightarrow>I")
    fix v
    AOT_assume \<open>[G]v\<close>
    AOT_hence \<open>\<exists>!\<^sub>Du ([F]u & [R]uv)\<close>
      using 2[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>\<exists>u ([F]u & [R]uv & \<forall>z ([F]z & [R]zv \<rightarrow> z =\<^sub>D u))\<close>
      using "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
    then AOT_obtain u where \<open>[F]u & [R]uv & \<forall>z ([F]z & [R]zv \<rightarrow> z =\<^sub>D u)\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>[F]u & [R]uv\<close> using "&E" by blast
    AOT_thus \<open>\<exists>u ([F]u & [R]uv)\<close> by (rule "\<exists>I")
  qed
  moreover AOT_have \<open>\<forall>t \<forall>u \<forall>v ([F]t & [F]u & [G]v \<rightarrow> ([R]tv & [R]uv \<rightarrow> t =\<^sub>D u))\<close>
  proof(safe intro!: GEN "\<rightarrow>I")
    fix t u v
    AOT_assume A: \<open>[F]t & [F]u & [G]v\<close>
    AOT_assume B: \<open>[R]tv & [R]uv\<close>
    AOT_have \<open>\<exists>!\<^sub>Du ([F]u & [R]uv)\<close>
      using 2[THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF A[THEN "&E"(2)]].
    AOT_hence \<open>\<exists>u ([F]u & [R]uv & \<forall>u' ([F]u' & [R]u'v \<rightarrow> u' =\<^sub>D u))\<close>
      using "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
    then AOT_obtain u' where \<open>[F]u' & [R]u'v & \<forall>u ([F]u & [R]uv \<rightarrow> u =\<^sub>D u')\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence C: \<open>\<forall>u([F]u & [R]uv \<rightarrow> u =\<^sub>D u')\<close>
      using "&E" by blast
    AOT_hence \<open>u =\<^sub>D u'\<close>
      using "\<forall>E"(2)[where \<beta>=u] A[THEN "&E"(1), THEN "&E"(2)] B[THEN "&E"(2)] "\<rightarrow>E" "&I" by blast
    moreover AOT_have \<open>t =\<^sub>D u'\<close>
      using C "\<forall>E"(2)[where \<beta>=t] A[THEN "&E"(1), THEN "&E"(1)] B[THEN "&E"(1)] "\<rightarrow>E" "&I" by blast
    ultimately AOT_show \<open>t =\<^sub>D u\<close>
      by (metis "con-dis-i-e:1" "disc=Dequiv:2" "disc=Dequiv:3" "vdash-properties:10")
  qed
  ultimately AOT_show \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oD G\<close>
    by (safe intro!: "equi-rem:4"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "equi-rem:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "equi-rem:3"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
(*
next
  AOT_assume \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oD G\<close>
  AOT_hence \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>D G\<close> and \<open>R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oD G\<close>
    using "equi-rem:4"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_show \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
  proof(safe intro!: "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" GEN "\<rightarrow>I")
    fix u
    AOT_assume \<open>[F]u\<close>
    AOT_show \<open>\<exists>!\<^sub>Dv ([G]v & [R]uv)\<close>
      sorry
  next
    fix v
    AOT_assume \<open>[G]v\<close>
    AOT_show \<open>\<exists>!\<^sub>Du ([F]u & [R]uv)\<close>
      sorry
  qed
*)
qed


AOT_theorem "empty-approx:1": \<open>(\<not>\<exists>u [F]u & \<not>\<exists>v [H]v) \<rightarrow> F \<approx>\<^sub>D H\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume 0: \<open>\<not>\<exists>u [F]u\<close> and 1: \<open>\<not>\<exists>v [H]v\<close>
  AOT_have \<open>\<forall>u ([F]u \<rightarrow> \<exists>!\<^sub>Dv ([H]v & [R]uv))\<close> for R
  proof(rule GEN; rule "\<rightarrow>I"; rule "raa-cor:1")
    fix u
    AOT_assume \<open>[F]u\<close>
    AOT_hence \<open>\<exists>u [F]u\<close> using "\<exists>I" "&I" by fast
    AOT_thus \<open>\<exists>u [F]u & \<not>\<exists>u [F]u\<close> using "&I" 0 by blast
  qed
  moreover AOT_have \<open>\<forall>v ([H]v \<rightarrow> \<exists>!\<^sub>Du ([F]u & [R]uv))\<close> for R
  proof(rule GEN; rule "\<rightarrow>I"; rule "raa-cor:1")
    fix v
    AOT_assume \<open>[H]v\<close>
    AOT_hence \<open>\<exists>v [H]v\<close> using "\<exists>I" "&I" by fast
    AOT_thus \<open>\<exists>v [H]v & \<not>\<exists>v [H]v\<close> using 1 "&I" by blast
  qed
  ultimately AOT_have \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D H\<close> for R
    apply (safe intro!: "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" GEN "cqt:2[const_var]"[axiom_inst])
    using "\<forall>E" by blast+
  AOT_hence \<open>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D H\<close> by (rule "\<exists>I")
  AOT_thus \<open>F \<approx>\<^sub>D H\<close>
    by (rule "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
qed

AOT_theorem "empty-approx:2": \<open>(\<exists>u [F]u & \<not>\<exists>v [H]v) \<rightarrow> \<not>(F \<approx>\<^sub>D H)\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2); rule "raa-cor:2")
  AOT_assume 1: \<open>\<exists>u [F]u\<close> and 2: \<open>\<not>\<exists>v [H]v\<close>
  AOT_obtain b where b_prop: \<open>[F]b\<close>
    using 1 "\<exists>E"[rotated] by blast
  AOT_assume \<open>F \<approx>\<^sub>D H\<close>
  AOT_hence \<open>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D H\<close>
    by (rule "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fE"])
  then AOT_obtain R where \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D H\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<theta>: \<open>\<forall>u ([F]u \<rightarrow> \<exists>!\<^sub>Dv ([H]v & [R]uv))\<close>
    using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_have \<open>\<exists>!\<^sub>Dv ([H]v & [R]bv)\<close> for u
    using \<theta>[THEN "\<forall>E"(2)[where \<beta>=b], THEN "\<rightarrow>E", OF b_prop].
  AOT_hence \<open>\<exists>v ([H]v & [R]bv & \<forall>u ([H]u & [R]bu \<rightarrow> u =\<^sub>D v))\<close>
    by (rule "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"])
  then AOT_obtain x where \<open>([H]x & [R]bx & \<forall>u ([H]u & [R]bu \<rightarrow> u =\<^sub>D x))\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<open>[H]x\<close> using "&E" "&I" by blast
  AOT_hence \<open>\<exists>v [H]v\<close> by (rule "\<exists>I")
  AOT_thus \<open>\<exists>v [H]v & \<not>\<exists>v [H]v\<close> using 2 "&I" by blast
qed

syntax "_AOT_non_eq_D" :: \<open>\<Pi>\<close> ("'(\<noteq>\<^sub>D')")
translations
  (\<Pi>) "(\<noteq>\<^sub>D)" == (\<Pi>) "(=\<^sub>D)\<^sup>-"
syntax "_AOT_non_eq_D_infix" :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl "\<noteq>\<^sub>D" 50)
translations
 "_AOT_non_eq_D_infix \<kappa> \<kappa>'" ==
 "CONST AOT_exe (CONST relation_negation (CONST eq_D)) (CONST Pair \<kappa> \<kappa>')"
print_translation\<open>
AOT_syntax_print_translations
[(\<^const_syntax>\<open>AOT_exe\<close>, fn ctxt => fn [
  Const (\<^const_syntax>\<open>relation_negation\<close>, _) $ Const ("\<^const>AOT_PLM.eq_D", _),
  Const (\<^const_syntax>\<open>Pair\<close>, _) $ lhs $ rhs
] => Const (\<^syntax_const>\<open>_AOT_non_eq_D_infix\<close>, dummyT) $ lhs $ rhs)]\<close>
AOT_theorem "thm-neg=D": \<open>x \<noteq>\<^sub>D y \<equiv> \<not>(x =\<^sub>D y)\<close>
proof -
  AOT_have 0: \<open>\<guillemotleft>(AOT_term_of_var x,AOT_term_of_var y)\<guillemotright>\<down>\<close>
    by (simp add: "&I" "cqt:2[const_var]"[axiom_inst] prod_denotesI)
  AOT_have \<theta>: \<open>[\<lambda>x\<^sub>1...x\<^sub>2 \<not>(=\<^sub>D)x\<^sub>1...x\<^sub>2]\<down>\<close> by "cqt:2"
  AOT_have \<open>x \<noteq>\<^sub>D y \<equiv> [\<lambda>x\<^sub>1...x\<^sub>2 \<not>(=\<^sub>D)x\<^sub>1...x\<^sub>2]xy\<close>
    by (rule "=\<^sub>d\<^sub>fI"(1)[OF "df-relation-negation", OF \<theta>])
       (meson "oth-class-taut:3:a")
  also AOT_have \<open>\<dots> \<equiv> \<not>(=\<^sub>D)xy\<close>
    apply (rule "beta-C-meta"[THEN "\<rightarrow>E", unvarify \<nu>\<^sub>1\<nu>\<^sub>n])
     apply "cqt:2[lambda]"
    by (fact 0)
  finally show ?thesis.
qed

(*
AOT_theorem "id-nec5:1": \<open>x \<noteq>\<^sub>D y \<equiv> \<box>(x \<noteq>\<^sub>D y)\<close>
proof -
  AOT_have \<open>x \<noteq>\<^sub>D y \<equiv> \<not>(x =\<^sub>D y)\<close> using "thm-neg=D".
  also AOT_have \<open>\<dots> \<equiv> \<not>\<diamond>(x =\<^sub>D y)\<close>
    by (meson "id-nec3:2" "\<equiv>E"(1) "Commutativity of \<equiv>" "oth-class-taut:4:b")
  also AOT_have \<open>\<dots> \<equiv> \<box>\<not>(x =\<^sub>D y)\<close>
    by (meson "KBasic2:1" "\<equiv>E"(2) "Commutativity of \<equiv>")
  also AOT_have \<open>\<dots> \<equiv> \<box>(x \<noteq>\<^sub>E y)\<close>
    by (AOT_subst (reverse) \<open>\<not>(x =\<^sub>E y)\<close> \<open>x \<noteq>\<^sub>E y\<close>)
       (auto simp: "thm-neg=E" "oth-class-taut:3:a")
  finally show ?thesis.
qed

AOT_theorem "id-nec4:2": \<open>\<diamond>(x \<noteq>\<^sub>E y) \<equiv> (x \<noteq>\<^sub>E y)\<close>
  by (meson "RE\<diamond>" "S5Basic:2" "id-nec4:1" "\<equiv>E"(2,5) "Commutativity of \<equiv>")

AOT_theorem "id-nec4:3": \<open>\<diamond>(x \<noteq>\<^sub>E y) \<equiv> \<box>(x \<noteq>\<^sub>E y)\<close>
  by (meson "id-nec4:1" "id-nec4:2" "\<equiv>E"(5))

AOT_theorem "id-act2:1": \<open>x =\<^sub>E y \<equiv> \<^bold>\<A>x =\<^sub>E y\<close>
  by (meson "Act-Basic:5" "Act-Sub:2" "RA[2]" "id-nec3:2" "\<equiv>E"(1,6))
AOT_theorem "id-act2:2": \<open>x \<noteq>\<^sub>E y \<equiv> \<^bold>\<A>x \<noteq>\<^sub>E y\<close>
  by (meson "Act-Basic:5" "Act-Sub:2" "RA[2]" "id-nec4:2" "\<equiv>E"(1,6))
*)

AOT_define FminusU :: \<open>\<Pi> \<Rightarrow> \<tau> \<Rightarrow> \<Pi>\<close> ("_\<^sup>-\<^sup>_")
  "F-u": \<open>[F]\<^sup>-\<^sup>x =\<^sub>d\<^sub>f [\<lambda>z [F]z & z \<noteq>\<^sub>D x]\<close>

text\<open>Note: not explicitly in PLM.\<close>
AOT_theorem "F-u[den]": \<open>[F]\<^sup>-\<^sup>x\<down>\<close>
  by (rule "=\<^sub>d\<^sub>fI"(1)[OF "F-u", where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", simplified]; "cqt:2[lambda]")

AOT_theorem "F-u[equiv]": \<open>[[F]\<^sup>-\<^sup>x]y \<equiv> [F]y & y \<noteq>\<^sub>D x\<close>
  by (auto intro: "=\<^sub>d\<^sub>fI"(1)[OF "F-u", where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", simplified]
           intro!: "cqt:2" "beta-C-meta"[THEN "\<rightarrow>E"])

AOT_theorem eqP': \<open>F \<approx>\<^sub>D G & [F]u & [G]v \<rightarrow> [F]\<^sup>-\<^sup>u \<approx>\<^sub>D [G]\<^sup>-\<^sup>v\<close>
proof (rule "\<rightarrow>I"; frule "&E"(2); drule "&E"(1); frule "&E"(2); drule "&E"(1))

  AOT_modally_strict {
    fix x y \<phi>
    AOT_assume 0: \<open>[\<lambda>x \<phi>{v,x}]\<down>\<close> for v
    AOT_assume \<open>x =\<^sub>D y\<close>
    AOT_hence 1: \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
      using "=D-simple:1"[THEN "\<equiv>E"(1), THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"]] by blast
    AOT_assume \<open>\<exists>!\<^sub>Dv (\<phi>{v,x})\<close>

    AOT_hence \<open>\<exists>v (\<phi>{v,x} & \<forall>t (\<phi>{t,x} \<rightarrow> t =\<^sub>D v))\<close>
      using "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by fast
    then AOT_obtain v where v_prop: \<open>\<phi>{v, x} & \<forall>t (\<phi>{t,x} \<rightarrow> t =\<^sub>D v)\<close>
      using "\<exists>E"[rotated] by blast
    AOT_have \<open>\<phi>{v,y} & \<forall>t (\<phi>{t,y} \<rightarrow> t =\<^sub>D v)\<close>
    proof(safe intro!: "&I" GEN "\<rightarrow>I")
      AOT_have \<open>[\<lambda>x \<phi>{v,x}]x\<close>
        by (safe intro!: "\<beta>\<leftarrow>C" 0 "cqt:2" v_prop[THEN "&E"(1)])
      AOT_hence \<open>[\<lambda>x \<phi>{v,x}]y\<close>
        using 1[THEN "\<forall>E"(1), OF 0, THEN "\<equiv>E"(1)] by blast
      AOT_thus \<open>\<phi>{v,y}\<close>
        using "\<beta>\<rightarrow>C" by blast
    next
      fix t
      AOT_assume \<open>\<phi>{t,y}\<close>
      AOT_hence \<open>[\<lambda>x \<phi>{t,x}]y\<close>
        by (safe intro!: "\<beta>\<leftarrow>C" 0 "cqt:2")
      AOT_hence \<open>[\<lambda>x \<phi>{t,x}]x\<close>
        using 1[THEN "\<forall>E"(1), OF 0, THEN "\<equiv>E"(2)] by blast
      AOT_hence \<open>\<phi>{t,x}\<close> using "\<beta>\<rightarrow>C" by blast
      AOT_thus \<open>t =\<^sub>D v\<close>
        using v_prop[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
    qed
    AOT_hence \<open>\<exists>v (\<phi>{v,y} & \<forall>t (\<phi>{t,y} \<rightarrow> t =\<^sub>D v))\<close>
      by (rule "\<exists>I")
    AOT_hence \<open>\<exists>!\<^sub>Dv (\<phi>{v,y})\<close>
      using "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] by fast
  } note Aux = this

  AOT_assume \<open>F \<approx>\<^sub>D G\<close>
  AOT_hence \<open>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
    using "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain R where R_prop: \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence A: \<open>\<forall>u ([F]u \<rightarrow> \<exists>!\<^sub>Dv ([G]v & [R]uv))\<close>
        and B: \<open>\<forall>v ([G]v \<rightarrow> \<exists>!\<^sub>Du ([F]u & [R]uv))\<close>
    using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_have \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oD G\<close>
    using "equi-rem-thm" "\<equiv>E"(1) "\<rightarrow>E" R_prop by blast
  AOT_hence \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>D G & R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oD G\<close>
    using "equi-rem:4"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_hence C: \<open>\<forall>t\<forall>u\<forall>v (([F]t & [F]u & [G]v) \<rightarrow> ([R]tv & [R]uv \<rightarrow> t =\<^sub>D u))\<close>
    using "equi-rem:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_assume fu: \<open>[F]u\<close>
  AOT_assume gv: \<open>[G]v\<close>
  AOT_have \<open>[\<lambda>z [\<Pi>]z & z \<noteq>\<^sub>D \<kappa>]\<down>\<close> for \<Pi> \<kappa>
    by "cqt:2[lambda]"
  note \<Pi>_minus_\<kappa>I = "rule-id-df:2:b[2]"[
      where \<tau>=\<open>(\<lambda>(\<Pi>, \<kappa>). \<guillemotleft>[\<Pi>]\<^sup>-\<^sup>\<kappa>\<guillemotright>)\<close>, simplified, OF "F-u", simplified, OF this]
   and \<Pi>_minus_\<kappa>E = "rule-id-df:2:a[2]"[
      where \<tau>=\<open>(\<lambda>(\<Pi>, \<kappa>). \<guillemotleft>[\<Pi>]\<^sup>-\<^sup>\<kappa>\<guillemotright>)\<close>, simplified, OF "F-u", simplified, OF this]
  AOT_have \<Pi>_minus_\<kappa>_den: \<open>[\<Pi>]\<^sup>-\<^sup>\<kappa>\<down>\<close> for \<Pi> \<kappa>
    by (rule \<Pi>_minus_\<kappa>I) "cqt:2[lambda]"+
  {
    fix R
    AOT_assume R_prop: \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
    AOT_hence A: \<open>\<forall>u ([F]u \<rightarrow> \<exists>!\<^sub>Dv ([G]v & [R]uv))\<close>
          and B: \<open>\<forall>v ([G]v \<rightarrow> \<exists>!\<^sub>Du ([F]u & [R]uv))\<close>
      using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
    AOT_have \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oD G\<close>
      using "equi-rem-thm" "\<equiv>E"(1) "\<rightarrow>E" R_prop by blast
    AOT_hence \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>D G & R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oD G\<close>
      using "equi-rem:4"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
    AOT_hence C: \<open>\<forall>t\<forall>u\<forall>v (([F]t & [F]u & [G]v) \<rightarrow> ([R]tv & [R]uv \<rightarrow> t =\<^sub>D u))\<close>
      using "equi-rem:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast

    AOT_assume Ruv: \<open>[R]uv\<close>
    AOT_have \<open>R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D [G]\<^sup>-\<^sup>v\<close>
    proof(safe intro!: "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2[const_var]"[axiom_inst]
                       \<Pi>_minus_\<kappa>_den GEN "\<rightarrow>I")
      fix u'
      AOT_assume \<open>[[F]\<^sup>-\<^sup>u]u'\<close>
      AOT_hence 0: \<open>[\<lambda>z [F]z & z \<noteq>\<^sub>D u]u'\<close>
        using \<Pi>_minus_\<kappa>E by fast
      AOT_have 0: \<open>[F]u' & u' \<noteq>\<^sub>D u\<close>
        by (rule "\<beta>\<rightarrow>C"(1)) (fact 0)
      AOT_have \<open>\<exists>!\<^sub>Dv ([G]v & [R]u'v)\<close>
        using A[THEN "\<forall>E"(2)[where \<beta>=u'], THEN "\<rightarrow>E", OF 0[THEN "&E"(1)]].
      then AOT_obtain v' where
        v'_prop: \<open>[G]v' & [R]u'v' & \<forall> t ([G]t & [R]u't \<rightarrow> t =\<^sub>D v')\<close>
        using "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "\<exists>E"[rotated] by fastforce

      AOT_show \<open>\<exists>!\<^sub>Dv' ([[G]\<^sup>-\<^sup>v]v' & [R]u'v')\<close>
      proof (safe intro!: "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(2)[where \<beta>=v']
                          "&I" GEN "\<rightarrow>I")
        AOT_show \<open>[[G]\<^sup>-\<^sup>v]v'\<close>
        proof (rule \<Pi>_minus_\<kappa>I; 
               safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" "thm-neg=D"[THEN "\<equiv>E"(2)])
          AOT_show \<open>[G]v'\<close> using v'_prop "&E" by blast
        next
          AOT_show \<open>\<not>v' =\<^sub>D v\<close>
          proof (rule "raa-cor:2")
            AOT_assume \<open>v' =\<^sub>D v\<close>
            AOT_hence \<open>\<forall>F([F]v' \<equiv> [F]v)\<close>
              using "=D-simple:1"[THEN "\<equiv>E"(1), THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"]] by blast
            moreover AOT_have \<open>[\<lambda>z [R]uz]\<down>\<close> by "cqt:2"
            ultimately AOT_have \<open>[\<lambda>z [R]uz]v' \<equiv> [\<lambda>z [R]uz]v\<close>
              using "\<forall>E"(1) by blast
            moreover AOT_have \<open>[\<lambda>z [R]uz]v\<close>
              by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2" Ruv)
            ultimately AOT_have \<open>[\<lambda>z [R]uz]v'\<close>
              using "\<equiv>E" by blast
            AOT_hence Ruv': \<open>[R]uv'\<close> using "\<beta>\<rightarrow>C" by fast
            AOT_have \<open>u' =\<^sub>D u\<close>
              by (rule C[THEN "\<forall>E"(2), THEN "\<forall>E"(2),
                         THEN "\<forall>E"(2)[where \<beta>=v'], THEN "\<rightarrow>E", THEN "\<rightarrow>E"])
                 (safe intro!: "&I" 0[THEN "&E"(1)] fu
                               v'_prop[THEN "&E"(1), THEN "&E"(1)]
                               Ruv' v'_prop[THEN "&E"(1), THEN "&E"(2)])
            moreover AOT_have \<open>\<not>(u' =\<^sub>D u)\<close>
              using "0" "&E"(2) "\<equiv>E"(1) "thm-neg=D" by blast
            ultimately AOT_show \<open>u' =\<^sub>D u & \<not>u' =\<^sub>D u\<close> using "&I" by blast
          qed
        qed
      next
        AOT_show \<open>[R]u'v'\<close> using v'_prop "&E" by blast
      next
        fix t
        AOT_assume t_prop: \<open>[[G]\<^sup>-\<^sup>v]t & [R]u't\<close>
        AOT_have gt_t_noteq_v: \<open>[G]t & t \<noteq>\<^sub>D v\<close>
          apply (rule "\<beta>\<rightarrow>C"(1)[where \<kappa>\<^sub>1\<kappa>\<^sub>n="AOT_term_of_var t"])
          apply (rule \<Pi>_minus_\<kappa>E)
          by (fact t_prop[THEN "&E"(1)])
        AOT_show \<open>t =\<^sub>D v'\<close>
          using v'_prop[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E",
                        OF "&I", OF gt_t_noteq_v[THEN "&E"(1)],
                        OF t_prop[THEN "&E"(2)]].
      qed
    next
      fix v'
      AOT_assume G_minus_v_v': \<open>[[G]\<^sup>-\<^sup>v]v'\<close>
      AOT_have gt_t_noteq_v: \<open>[G]v' & v' \<noteq>\<^sub>D v\<close>
        apply (rule "\<beta>\<rightarrow>C"(1)[where \<kappa>\<^sub>1\<kappa>\<^sub>n="AOT_term_of_var (v')"])
        apply (rule \<Pi>_minus_\<kappa>E)
        by (fact G_minus_v_v')
      AOT_have \<open>\<exists>!\<^sub>Du([F]u & [R]uv')\<close>
        using B[THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF gt_t_noteq_v[THEN "&E"(1)]].
      then AOT_obtain u' where
        u'_prop: \<open>[F]u' & [R]u'v' & \<forall>t ([F]t & [R]tv' \<rightarrow> t =\<^sub>D u')\<close>
        using "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "\<exists>E"[rotated] by fastforce
      AOT_show \<open>\<exists>!\<^sub>Du' ([[F]\<^sup>-\<^sup>u]u' & [R]u'v')\<close>
      proof (safe intro!: "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(2)[where \<beta>=u'] "&I"
                          u'_prop[THEN "&E"(1), THEN "&E"(2)] GEN "\<rightarrow>I")
        AOT_show \<open>[[F]\<^sup>-\<^sup>u]u'\<close>
        proof (rule \<Pi>_minus_\<kappa>I;
               safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" "thm-neg=D"[THEN "\<equiv>E"(2)]
               u'_prop[THEN "&E"(1), THEN "&E"(1)]; rule "raa-cor:2")
          AOT_assume u'_eq_u: \<open>u' =\<^sub>D u\<close>
          AOT_hence \<open>\<forall>F([F]u' \<equiv> [F]u)\<close>
            using "=D-simple:1"[THEN "\<equiv>E"(1), THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"]] by blast
          moreover AOT_have \<open>[\<lambda>z [R]zv]\<down>\<close> by "cqt:2"
          ultimately AOT_have \<open>[\<lambda>z [R]zv]u' \<equiv> [\<lambda>z [R]zv]u\<close>
            using "\<forall>E"(1) by blast
          moreover AOT_have \<open>[\<lambda>z [R]zv]u\<close>
            by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2" Ruv)
          ultimately AOT_have \<open>[\<lambda>z [R]zv]u'\<close>
            using "\<equiv>E" by blast
          AOT_hence Ru'v: \<open>[R]u'v\<close> using "\<beta>\<rightarrow>C" by blast
          AOT_have \<open>v' \<noteq>\<^sub>D v\<close>
            using "&E"(2) gt_t_noteq_v by blast
          AOT_hence v'_noteq_v: \<open>\<not>(v' =\<^sub>D v)\<close> by (metis "\<equiv>E"(1) "thm-neg=D")
          AOT_have \<open>\<exists>u ([G]u & [R]u'u & \<forall>v ([G]v & [R]u'v \<rightarrow> v =\<^sub>D u))\<close>
            using A[THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF u'_prop[THEN "&E"(1), THEN "&E"(1)],
                    THEN "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"]].
          then AOT_obtain t where
            t_prop: \<open>[G]t & [R]u't & \<forall>v ([G]v & [R]u'v \<rightarrow> v =\<^sub>D t)\<close>
            using "\<exists>E"[rotated] by blast
          AOT_have \<open>v =\<^sub>D t\<close> if \<open>[G]v\<close> and \<open>[R]u'v\<close> for v
            using t_prop[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E",
                         OF "&I", OF that].
          AOT_hence \<open>v' =\<^sub>D t\<close> and v_eq_t: \<open>v =\<^sub>D t\<close>
            by (auto simp: gt_t_noteq_v[THEN "&E"(1)] Ru'v gv
                           u'_prop[THEN "&E"(1), THEN "&E"(2)])
          AOT_hence \<open>v' =\<^sub>D t\<close> and \<open>t =\<^sub>D v\<close>
            apply simp
            using "disc=Dequiv:2" "vdash-properties:10" v_eq_t by blast
          AOT_hence \<open>v' =\<^sub>D v\<close>
            by (metis "con-dis-i-e:1" "disc=Dequiv:3" "vdash-properties:10")
          AOT_thus \<open>v' =\<^sub>D v & \<not>v' =\<^sub>D v\<close>
            using v'_noteq_v "&I" by blast
        qed
      next
        fix t
        AOT_assume 0: \<open>[[F]\<^sup>-\<^sup>u]t & [R]tv'\<close>
        moreover AOT_have \<open>[F]t & t \<noteq>\<^sub>D u\<close>
          apply (rule "\<beta>\<rightarrow>C"(1)[where \<kappa>\<^sub>1\<kappa>\<^sub>n="AOT_term_of_var t"])
          apply (rule \<Pi>_minus_\<kappa>E)
          by (fact 0[THEN "&E"(1)])
        ultimately AOT_show \<open>t =\<^sub>D u'\<close>
          using u'_prop[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF "&I"]
                "&E" by blast
      qed
    qed
    AOT_hence \<open>\<exists>R R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D [G]\<^sup>-\<^sup>v\<close>
      by (rule "\<exists>I")
  } note 1 = this
  moreover {
    AOT_assume not_Ruv: \<open>\<not>[R]uv\<close>
    AOT_have \<open>\<exists>!\<^sub>Dv ([G]v & [R]uv)\<close>
      using A[THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF fu].
    then AOT_obtain b where
      b_prop: \<open>([G]b & [R]ub & \<forall>t([G]t & [R]ut \<rightarrow> t =\<^sub>D b))\<close>
      using "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "\<exists>E"[rotated] by fastforce
    AOT_hence gb: \<open>[G]b\<close> and Rub: \<open>[R]ub\<close>
      using "&E" by blast+
    AOT_have \<open>([G]t & [R]ut \<rightarrow> t =\<^sub>D b)\<close> for t
      using b_prop "&E"(2) "\<forall>E"(2) by blast
    AOT_hence b_unique: \<open>t =\<^sub>D b\<close> if \<open>[G]t\<close> and \<open>[R]ut\<close> for t
      by (metis Adjunction "modus-tollens:1" "reductio-aa:1" that)
    AOT_have not_v_eq_b: \<open>\<not>(v =\<^sub>D b)\<close>
    proof(rule "raa-cor:2")
      AOT_assume \<open>v =\<^sub>D b\<close>
      AOT_hence \<open>\<forall>F([F]v \<equiv> [F]b)\<close>
        using "=D-simple:1"[THEN "\<equiv>E"(1), THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"]] by blast
      moreover AOT_have \<open>[\<lambda>z [R]uz]\<down>\<close> by "cqt:2"
      ultimately AOT_have \<open>[\<lambda>z [R]uz]v \<equiv> [\<lambda>z [R]uz]b\<close>
        using "\<forall>E"(1) by blast
      moreover AOT_have \<open>[\<lambda>z [R]uz]b\<close>
        by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2" Rub)
      ultimately AOT_have \<open>[\<lambda>z [R]uz]v\<close>
        using "\<equiv>E" by blast
      AOT_hence \<open>[R]uv\<close> using "\<beta>\<rightarrow>C" by blast
      AOT_thus \<open>[R]uv & \<not>[R]uv\<close>
        using not_Ruv "&I" by blast
    qed
    AOT_have not_b_eq_v: \<open>\<not>(b =\<^sub>D v)\<close>
      using "modus-tollens:1" not_v_eq_b "disc=Dequiv:2" by blast
    AOT_have \<open>\<exists>!\<^sub>Du ([F]u & [R]uv)\<close>
      using B[THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF gv].
    then AOT_obtain a where
      a_prop: \<open>([F]a & [R]av & \<forall>t([F]t & [R]tv \<rightarrow> t =\<^sub>D a))\<close>
      using "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "\<exists>E"[rotated] by fastforce
    AOT_hence fa: \<open>[F]a\<close> and Rav: \<open>[R]av\<close>
      using "&E" by blast+
    AOT_have \<open>([F]t & [R]tv \<rightarrow> t =\<^sub>D a)\<close> for t
      using a_prop "&E" "\<forall>E"(2) by blast
    AOT_hence a_unique: \<open>t =\<^sub>D a\<close> if\<open>[F]t\<close> and \<open>[R]tv\<close> for t
      by (metis Adjunction "modus-tollens:1" "reductio-aa:1" that) 
    AOT_have not_u_eq_a: \<open>\<not>(u =\<^sub>D a)\<close>
    proof(rule "raa-cor:2")
      AOT_assume \<open>u =\<^sub>D a\<close>
      AOT_hence \<open>\<forall>F([F]u \<equiv> [F]a)\<close>
        using "=D-simple:1"[THEN "\<equiv>E"(1), THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"]] by blast
      moreover AOT_have \<open>[\<lambda>z [R]zv]\<down>\<close> by "cqt:2"
      ultimately AOT_have \<open>[\<lambda>z [R]zv]u \<equiv> [\<lambda>z [R]zv]a\<close>
        using "\<forall>E"(1) by blast
      moreover AOT_have \<open>[\<lambda>z [R]zv]a\<close>
        by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2" Rav)
      ultimately AOT_have \<open>[\<lambda>z [R]zv]u\<close>
        using "\<equiv>E" by blast
      AOT_hence \<open>[R]uv\<close>
        using "\<beta>\<rightarrow>C" by blast
      AOT_thus \<open>[R]uv & \<not>[R]uv\<close>
        using not_Ruv "&I" by blast
    qed
    AOT_have not_a_eq_u: \<open>\<not>(a =\<^sub>D u)\<close>
      using "modus-tollens:1" not_u_eq_a "disc=Dequiv:2" by blast
    let ?R = \<open>\<guillemotleft>[\<lambda>u'v' (u' \<noteq>\<^sub>D u & v' \<noteq>\<^sub>D v & [R]u'v') \<or>
                      (u' =\<^sub>D a & v' =\<^sub>D b) \<or>
                      (u' =\<^sub>D u & v' =\<^sub>D v)]\<guillemotright>\<close>
    AOT_have \<open>[\<guillemotleft>?R\<guillemotright>]\<down>\<close> by "cqt:2[lambda]"
    AOT_hence \<open>\<exists> \<beta> \<beta> = [\<guillemotleft>?R\<guillemotright>]\<close>
      using "free-thms:1" "\<equiv>E"(1) by fast
    then AOT_obtain R\<^sub>1 where R\<^sub>1_def: \<open>R\<^sub>1 = [\<guillemotleft>?R\<guillemotright>]\<close>
      using "\<exists>E"[rotated] by blast
    AOT_have Rxy1: \<open>[R]xy\<close> if \<open>[R\<^sub>1]xy\<close> and \<open>x \<noteq>\<^sub>D u\<close> and \<open>x \<noteq>\<^sub>D a\<close> for x y
    proof -
      AOT_have 0: \<open>[\<guillemotleft>?R\<guillemotright>]xy\<close>
        by (rule "rule=E"[rotated, OF R\<^sub>1_def]) (fact that(1))
      AOT_have \<open>(x \<noteq>\<^sub>D u & y \<noteq>\<^sub>D v & [R]xy) \<or> (x =\<^sub>D a & y =\<^sub>D b) \<or> (x =\<^sub>D u & y =\<^sub>D v)\<close>
        using "\<beta>\<rightarrow>C"(1)[OF 0] by simp
      AOT_hence \<open>x \<noteq>\<^sub>D u & y \<noteq>\<^sub>D v & [R]xy\<close> using that(2,3)
        by (metis "\<or>E"(3) "Conjunction Simplification"(1) "\<equiv>E"(1)
                  "modus-tollens:1" "thm-neg=D")
      AOT_thus \<open>[R]xy\<close> using "&E" by blast+
    qed
    AOT_have Rxy2: \<open>[R]xy\<close>  if \<open>[R\<^sub>1]xy\<close> and \<open>y \<noteq>\<^sub>D v\<close> and \<open>y \<noteq>\<^sub>D b\<close> for x y
    proof -
      AOT_have 0: \<open>[\<guillemotleft>?R\<guillemotright>]xy\<close>
        by (rule "rule=E"[rotated, OF R\<^sub>1_def]) (fact that(1))
      AOT_have \<open>(x \<noteq>\<^sub>D u & y \<noteq>\<^sub>D v & [R]xy) \<or> (x =\<^sub>D a & y =\<^sub>D b) \<or> (x =\<^sub>D u & y =\<^sub>D v)\<close>
        using "\<beta>\<rightarrow>C"(1)[OF 0] by simp
      AOT_hence \<open>x \<noteq>\<^sub>D u & y \<noteq>\<^sub>D v & [R]xy\<close>
        using that(2,3)
        by (metis "\<or>E"(3) "Conjunction Simplification"(2) "\<equiv>E"(1)
                  "modus-tollens:1" "thm-neg=D")
      AOT_thus \<open>[R]xy\<close> using "&E" by blast+
    qed
    AOT_have R\<^sub>1xy: \<open>[R\<^sub>1]xy\<close> if \<open>[R]xy\<close> and \<open>x \<noteq>\<^sub>D u\<close> and \<open>y \<noteq>\<^sub>D v\<close> for x y
      by (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
         (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2"
                 simp: "&I" "ex:1:a" prod_denotesI "rule-ui:3" that "\<or>I"(1))
    AOT_have R\<^sub>1ab: \<open>[R\<^sub>1]ab\<close>
      apply (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
      apply (safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" prod_denotesI "&I")
      by (meson a_prop b_prop "&I" "&E"(1) "\<or>I"(1) "\<or>I"(2) "disc=Dequiv:1" "\<rightarrow>E")
    AOT_have R\<^sub>1uv: \<open>[R\<^sub>1]uv\<close>
      apply (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
      apply (safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" prod_denotesI "&I")
      by (meson "&I" "\<or>I"(2) "disc=Dequiv:1" Discernible.\<psi> "\<rightarrow>E")
    moreover AOT_have \<open>R\<^sub>1 |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
    proof (safe intro!: "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" GEN "\<rightarrow>I")
      fix u'
      AOT_assume fu': \<open>[F]u'\<close>
      {
        AOT_assume not_u'_eq_u: \<open>\<not>(u' =\<^sub>D u)\<close> and not_u'_eq_a: \<open>\<not>(u' =\<^sub>D a)\<close>
        AOT_hence u'_noteq_u: \<open>u' \<noteq>\<^sub>D u\<close> and u'_noteq_a: \<open>u' \<noteq>\<^sub>D a\<close>
          by (metis "\<equiv>E"(2) "thm-neg=D")+
        AOT_have \<open>\<exists>!\<^sub>Dv ([G]v & [R]u'v)\<close>
          using A[THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF fu'].
        AOT_hence \<open>\<exists>v ([G]v & [R]u'v & \<forall>t ([G]t & [R]u't \<rightarrow> t =\<^sub>D v))\<close>
          using "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by simp
        then AOT_obtain v' where
          v'_prop: \<open>[G]v' & [R]u'v' & \<forall>t ([G]t & [R]u't \<rightarrow> t =\<^sub>D v')\<close>
          using "\<exists>E"[rotated] by blast
        AOT_hence gv': \<open>[G]v'\<close> and Ru'v': \<open>[R]u'v'\<close>
          using "&E" by blast+
        AOT_have not_v'_eq_v: \<open>\<not>v' =\<^sub>D v\<close>
        proof (rule "raa-cor:2")
          AOT_assume \<open>v' =\<^sub>D v\<close>
          AOT_hence \<open>\<forall>F([F]v' \<equiv> [F]v)\<close>
            using "=D-simple:1"[THEN "\<equiv>E"(1), THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"]] by blast
          moreover AOT_have \<open>[\<lambda>z [R]u'z]\<down>\<close> by "cqt:2"
          ultimately AOT_have \<open>[\<lambda>z [R]u'z]v' \<equiv> [\<lambda>z [R]u'z]v\<close>
            using "\<forall>E"(1) by blast
          moreover AOT_have \<open>[\<lambda>z [R]u'z]v'\<close>
            by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2" Ru'v')
          ultimately AOT_have \<open>[\<lambda>z [R]u'z]v\<close>
            using "\<equiv>E" by blast
          AOT_hence Ru'v: \<open>[R]u'v\<close> using "\<beta>\<rightarrow>C" by blast
          AOT_have \<open>u' =\<^sub>D a\<close>
            using a_unique[OF fu', OF Ru'v].
          AOT_thus \<open>u' =\<^sub>D a & \<not>u' =\<^sub>D a\<close>
            using not_u'_eq_a "&I" by blast
        qed
        AOT_hence v'_noteq_v: \<open>v' \<noteq>\<^sub>D v\<close>
          using "\<equiv>E"(2) "thm-neg=D" by blast
        AOT_have \<open>\<forall>t ([G]t & [R]u't \<rightarrow> t =\<^sub>D v')\<close>
          using v'_prop "&E" by blast
        AOT_hence \<open>[G]t & [R]u't \<rightarrow> t =\<^sub>D v'\<close> for t
          using "\<forall>E"(2) by blast
        AOT_hence v'_unique: \<open>t =\<^sub>D v'\<close> if \<open>[G]t\<close> and \<open>[R]u't\<close> for t
          by (metis "&I" that "\<rightarrow>E")

        AOT_have \<open>[G]v' & [R\<^sub>1]u'v' & \<forall>t ([G]t & [R\<^sub>1]u't \<rightarrow> t =\<^sub>D v')\<close>
        proof (safe intro!: "&I" gv' R\<^sub>1xy Ru'v' u'_noteq_u u'_noteq_a "\<rightarrow>I"
                            GEN "thm-neg=D"[THEN "\<equiv>E"(2)] not_v'_eq_v)
          fix t
          AOT_assume 1: \<open>[G]t & [R\<^sub>1]u't\<close>
          AOT_have \<open>[R]u't\<close>
            using Rxy1[OF 1[THEN "&E"(2)], OF u'_noteq_u, OF u'_noteq_a].
          AOT_thus \<open>t =\<^sub>D v'\<close>
            using v'_unique 1[THEN "&E"(1)] by blast
        qed
        AOT_hence \<open>\<exists>v ([G]v & [R\<^sub>1]u'v & \<forall>t ([G]t & [R\<^sub>1]u't \<rightarrow> t =\<^sub>D v))\<close>
          by (rule "\<exists>I")
        AOT_hence \<open>\<exists>!\<^sub>Dv ([G]v & [R\<^sub>1]u'v)\<close>
          by (rule "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
      }
      moreover {
        AOT_assume 0: \<open>u' =\<^sub>D u\<close>
        AOT_hence 1: \<open>\<forall>F([F]u' \<equiv> [F]u)\<close>
          using "=D-simple:1"[THEN "\<equiv>E"(1), THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"]] by blast

        AOT_have \<open>\<exists>!\<^sub>Dv ([G]v & [R\<^sub>1]u'v)\<close>
        proof (safe intro!: "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(2)[where \<beta>=v]
                            "&I" GEN "\<rightarrow>I" gv)
          AOT_show \<open>[R\<^sub>1]u'v\<close>
            apply (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
            apply (safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" prod_denotesI)
            apply (safe intro!: "\<or>I"(2) "&I" 0)
            by (simp add: "disc=Dequiv:1")
        next
          fix v'
          AOT_assume 2: \<open>[G]v' & [R\<^sub>1]u'v'\<close>
          moreover AOT_have \<open>[\<lambda>z [R\<^sub>1]zv']\<down>\<close> by "cqt:2"
          ultimately AOT_have \<open>[\<lambda>z [R\<^sub>1]zv']u' \<equiv> [\<lambda>z [R\<^sub>1]zv']u\<close>
            using "\<forall>E"(1) 1 by blast
          moreover AOT_have \<open>[\<lambda>z [R\<^sub>1]zv']u'\<close>
            by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2" 2[THEN "&E"(2)])
          ultimately AOT_have \<open>[\<lambda>z [R\<^sub>1]zv']u\<close>
            using "\<equiv>E" by blast
          AOT_hence 0: \<open>[R\<^sub>1]uv'\<close>
            using "\<beta>\<rightarrow>C" by blast
          AOT_have 1: \<open>[\<guillemotleft>?R\<guillemotright>]uv'\<close>
            by (rule "rule=E"[rotated, OF R\<^sub>1_def]) (fact 0)
          AOT_have 2: \<open>(u \<noteq>\<^sub>D u & v' \<noteq>\<^sub>D v & [R]uv') \<or>
                       (u =\<^sub>D a & v' =\<^sub>D b) \<or>
                       (u =\<^sub>D u & v' =\<^sub>D v)\<close>
            using "\<beta>\<rightarrow>C"(1)[OF 1] by simp
          AOT_have \<open>\<not>u \<noteq>\<^sub>D u\<close>
            using "\<equiv>E"(4) "modus-tollens:1" "disc=Dequiv:1" Discernible.\<psi>
                  "reductio-aa:2" "thm-neg=D" by blast
          AOT_hence \<open>\<not>((u \<noteq>\<^sub>D u & v' \<noteq>\<^sub>D v & [R]uv') \<or> (u =\<^sub>D a & v' =\<^sub>D b))\<close>
            using not_u_eq_a
            by (metis "\<or>E"(2) "Conjunction Simplification"(1)
                      "modus-tollens:1" "reductio-aa:1")
          AOT_hence \<open>(u =\<^sub>D u & v' =\<^sub>D v)\<close>
            using 2 by (metis "\<or>E"(2))
          AOT_thus \<open>v' =\<^sub>D v\<close>
            using "&E" by blast
        qed
      }
      moreover {
        AOT_assume u'_eqD_a: \<open>u' =\<^sub>D a\<close>
        AOT_hence 1: \<open>\<forall>F([F]u' \<equiv> [F]a)\<close>
          using "=D-simple:1"[THEN "\<equiv>E"(1), THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"]] by blast
        AOT_have \<open>\<exists>!\<^sub>Dv ([G]v & [R\<^sub>1]u'v)\<close>
        proof (safe intro!: "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(2)[where \<beta>=b] "&I"
                            GEN "\<rightarrow>I" b_prop[THEN "&E"(1)]
                            b_prop[THEN "&E"(1), THEN "&E"(1)])
          AOT_show \<open>[R\<^sub>1]u'b\<close>
            apply (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
            apply (safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" prod_denotesI)
            apply (rule "\<or>I"(1); rule "\<or>I"(2); rule "&I")
             apply (fact u'_eqD_a)
            using b_prop "&E"(1) "disc=Dequiv:1" "\<rightarrow>E" by blast
        next
          fix v' 
          AOT_assume gv'_R1u'v': \<open>[G]v' & [R\<^sub>1]u'v'\<close>
          moreover AOT_have \<open>[\<lambda>z [R\<^sub>1]zv']\<down>\<close> by "cqt:2"
          ultimately AOT_have \<open>[\<lambda>z [R\<^sub>1]zv']u' \<equiv> [\<lambda>z [R\<^sub>1]zv']a\<close>
            using "\<forall>E"(1) 1 by blast
          moreover AOT_have \<open>[\<lambda>z [R\<^sub>1]zv']u'\<close>
            by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2" gv'_R1u'v'[THEN "&E"(2)])
          ultimately AOT_have \<open>[\<lambda>z [R\<^sub>1]zv']a\<close>
            using "\<equiv>E" by blast
          AOT_hence 0: \<open>[R\<^sub>1]av'\<close> using "\<beta>\<rightarrow>C" by blast
          AOT_have 1: \<open>[\<guillemotleft>?R\<guillemotright>]av'\<close>
            by (rule "rule=E"[rotated, OF R\<^sub>1_def]) (fact 0)
          AOT_have \<open>(a \<noteq>\<^sub>D u & v' \<noteq>\<^sub>D v & [R]av') \<or>
                    (a =\<^sub>D a & v' =\<^sub>D b) \<or>
                    (a =\<^sub>D u & v' =\<^sub>D v)\<close>
            using "\<beta>\<rightarrow>C"(1)[OF 1] by simp
          moreover {
            AOT_assume 0: \<open>a \<noteq>\<^sub>D u & v' \<noteq>\<^sub>D v & [R]av'\<close>
            AOT_have \<open>\<exists>!\<^sub>Dv ([G]v & [R]u'v)\<close>
              using A[THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF fu'].
            AOT_hence \<open>\<exists>!\<^sub>Dv ([G]v & [R]av)\<close>
              by (safe_step intro!: Aux)
                 (auto intro!: "cqt:2" u'_eqD_a)
            AOT_hence \<open>\<exists>v ([G]v & [R]av & \<forall>t ([G]t & [R]at \<rightarrow> t =\<^sub>D v))\<close>
              using "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by fast
            then AOT_obtain s where
              s_prop: \<open>[G]s & [R]as & \<forall>t ([G]t & [R]at \<rightarrow> t =\<^sub>D s)\<close>
              using "\<exists>E"[rotated] by blast
            AOT_have \<open>v' =\<^sub>D s\<close>
              using s_prop[THEN "&E"(2), THEN "\<forall>E"(2)]
                    gv'_R1u'v'[THEN "&E"(1)] 0[THEN "&E"(2)]
              by (metis "&I" "vdash-properties:10")
            moreover AOT_have \<open>v =\<^sub>D s\<close>
              using s_prop[THEN "&E"(2), THEN "\<forall>E"(2)] gv Rav
              by (metis "&I" "\<rightarrow>E")
            ultimately AOT_have \<open>v' =\<^sub>D v\<close>
              by (metis "&I" "disc=Dequiv:2" "disc=Dequiv:3" "\<rightarrow>E")
            moreover AOT_have \<open>\<not>(v' =\<^sub>D v)\<close>
              using 0[THEN "&E"(1), THEN "&E"(2)]
              by (metis "\<equiv>E"(1) "thm-neg=D") 
            ultimately AOT_have \<open>v' =\<^sub>D b\<close>
              by (metis "raa-cor:3")
          }
          moreover {
            AOT_assume \<open>a =\<^sub>D u & v' =\<^sub>D v\<close>
            AOT_hence \<open>v' =\<^sub>D b\<close>
              by (metis "&E"(1) not_a_eq_u "reductio-aa:1")
          }
          ultimately AOT_show \<open>v' =\<^sub>D b\<close>
            by (metis "&E"(2) "\<or>E"(3) "reductio-aa:1") 
        qed
      }
      ultimately AOT_show \<open>\<exists>!\<^sub>Dv ([G]v & [R\<^sub>1]u'v)\<close>
        by (metis "raa-cor:1")
    next
      fix v'
      AOT_assume gv': \<open>[G]v'\<close>
      {
        AOT_assume not_v'_eq_v: \<open>\<not>(v' =\<^sub>D v)\<close>
               and not_v'_eq_b: \<open>\<not>(v' =\<^sub>D b)\<close>
        AOT_hence v'_noteq_v: \<open>v' \<noteq>\<^sub>D v\<close>
              and v'_noteq_b: \<open>v' \<noteq>\<^sub>D b\<close>
          by (metis "\<equiv>E"(2) "thm-neg=D")+
        AOT_have \<open>\<exists>!\<^sub>Du ([F]u & [R]uv')\<close>
          using B[THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF gv'].
        AOT_hence \<open>\<exists>u ([F]u & [R]uv' & \<forall>t ([F]t & [R]tv' \<rightarrow> t =\<^sub>D u))\<close>
          using "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by simp
        then AOT_obtain u' where
          u'_prop: \<open>[F]u' & [R]u'v' & \<forall>t ([F]t & [R]tv' \<rightarrow> t =\<^sub>D u')\<close>
          using "\<exists>E"[rotated] by blast
        AOT_hence fu': \<open>[F]u'\<close> and Ru'v': \<open>[R]u'v'\<close>
          using "&E" by blast+
        AOT_have not_u'_eq_u: \<open>\<not>u' =\<^sub>D u\<close>
        proof (rule "raa-cor:2")
          AOT_assume \<open>u' =\<^sub>D u\<close>
          AOT_hence \<open>[\<lambda>z [R]zv']u' \<equiv> [\<lambda>z [R]zv']u\<close>
            by (safe intro!: "=D-simple:1"[THEN "\<equiv>E"(1), THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"], THEN "\<forall>E"(1)] "cqt:2")
          moreover AOT_have \<open>[\<lambda>z [R]zv']u'\<close>
            using u'_prop
            by (auto intro!: "\<beta>\<leftarrow>C" "cqt:2" dest: "&E")
          ultimately AOT_have \<open>[\<lambda>z [R]zv']u\<close>
            using "\<equiv>E" by blast
          AOT_hence Ruv': \<open>[R]uv'\<close>
            using "\<beta>\<rightarrow>C" by blast
          AOT_have \<open>v' =\<^sub>D b\<close>
            using b_unique[OF gv', OF Ruv'].
          AOT_thus \<open>v' =\<^sub>D b & \<not>v' =\<^sub>D b\<close>
            using not_v'_eq_b "&I" by blast
        qed
        AOT_hence u'_noteq_u: \<open>u' \<noteq>\<^sub>D u\<close>
          using "\<equiv>E"(2) "thm-neg=D" by blast
        AOT_have \<open>\<forall>t ([F]t & [R]tv' \<rightarrow> t =\<^sub>D u')\<close>
          using u'_prop "&E" by blast
        AOT_hence \<open>[F]t & [R]tv' \<rightarrow> t =\<^sub>D u'\<close> for t
          using "\<forall>E"(2) by blast
        AOT_hence u'_unique: \<open>t =\<^sub>D u'\<close> if \<open>[F]t\<close> and \<open>[R]tv'\<close> for t
          by (metis "&I" that "\<rightarrow>E")

        AOT_have \<open>[F]u' & [R\<^sub>1]u'v' & \<forall>t ([F]t & [R\<^sub>1]tv' \<rightarrow> t =\<^sub>D u')\<close>
        proof (safe intro!: "&I" gv' R\<^sub>1xy Ru'v' u'_noteq_u GEN "\<rightarrow>I"
                            "thm-neg=D"[THEN "\<equiv>E"(2)] not_v'_eq_v fu')
          fix t
          AOT_assume 1: \<open>[F]t & [R\<^sub>1]tv'\<close>
          AOT_have \<open>[R]tv'\<close>
            using Rxy2[OF 1[THEN "&E"(2)], OF v'_noteq_v, OF v'_noteq_b].
          AOT_thus \<open>t =\<^sub>D u'\<close>
            using u'_unique 1[THEN "&E"(1)] by blast
        qed
        AOT_hence \<open>\<exists>u ([F]u & [R\<^sub>1]uv' & \<forall>t ([F]t & [R\<^sub>1]tv' \<rightarrow> t =\<^sub>D u))\<close>
          by (rule "\<exists>I")
        AOT_hence \<open>\<exists>!\<^sub>Du ([F]u & [R\<^sub>1]uv')\<close>
          by (rule "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
      }
      moreover {
        AOT_assume 0: \<open>v' =\<^sub>D v\<close>

        AOT_have \<open>\<exists>!\<^sub>Du ([F]u & [R\<^sub>1]uv')\<close>
        proof (safe intro!: "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(2)[where \<beta>=u]
                            "&I" GEN "\<rightarrow>I" fu)
          AOT_show \<open>[R\<^sub>1]uv'\<close>
            apply (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
            apply (safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" prod_denotesI "&I" "\<or>I"(2))
            apply (simp add: "disc=Dequiv:1")
            by (simp add: "0")
        next
          fix u'
          AOT_assume \<open>[F]u' & [R\<^sub>1]u'v'\<close>
          AOT_hence \<open>[\<lambda>z [R\<^sub>1]u'z]v'\<close>
            by (auto intro!: "\<beta>\<leftarrow>C" "cqt:2" dest: "&E")
          moreover AOT_have \<open>[\<lambda>z [R\<^sub>1]u'z]v' \<equiv> [\<lambda>z [R\<^sub>1]u'z]v\<close>
            using 0
            by (safe intro!: "=D-simple:1"[THEN "\<equiv>E"(1), THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"], THEN "\<forall>E"(1)] "cqt:2")
          ultimately AOT_have \<open>[\<lambda>z [R\<^sub>1]u'z]v\<close>
            using "\<equiv>E" by blast
          AOT_hence 0: \<open>[R\<^sub>1]u'v\<close>
            using "\<beta>\<rightarrow>C" by blast
          AOT_have 1: \<open>[\<guillemotleft>?R\<guillemotright>]u'v\<close>
            by (rule "rule=E"[rotated, OF R\<^sub>1_def]) (fact 0)
          AOT_have 2: \<open>(u' \<noteq>\<^sub>D u & v \<noteq>\<^sub>D v & [R]u'v) \<or>
                       (u' =\<^sub>D a & v =\<^sub>D b) \<or>
                       (u' =\<^sub>D u & v =\<^sub>D v)\<close>
            using "\<beta>\<rightarrow>C"(1)[OF 1, simplified] by simp
          AOT_have \<open>\<not>v \<noteq>\<^sub>D v\<close>
            using "\<equiv>E"(4) "modus-tollens:1" "disc=Dequiv:1" Discernible.\<psi>
                  "reductio-aa:2" "thm-neg=D" by blast
          AOT_hence \<open>\<not>((u' \<noteq>\<^sub>D u & v \<noteq>\<^sub>D v & [R]u'v) \<or> (u' =\<^sub>D a & v =\<^sub>D b))\<close>
            by (metis "&E"(1) "&E"(2) "\<or>E"(3) not_v_eq_b "raa-cor:3")
          AOT_hence \<open>(u' =\<^sub>D u & v =\<^sub>D v)\<close>
            using 2 by (metis "\<or>E"(2))
          AOT_thus \<open>u' =\<^sub>D u\<close>
            using "&E" by blast
        qed
      }
      moreover {
        AOT_assume v'_eq_b: \<open>v' =\<^sub>D b\<close>
        AOT_have \<open>\<exists>!\<^sub>Du ([F]u & [R\<^sub>1]uv')\<close>
        proof (safe intro!: "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(2)[where \<beta>=a] "&I"
                            GEN "\<rightarrow>I" fa
                            b_prop[THEN "&E"(1), THEN "&E"(1)])
          AOT_show \<open>[R\<^sub>1]av'\<close>
            apply (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
            apply (safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" prod_denotesI)
            apply (rule "\<or>I"(1); rule "\<or>I"(2); rule "&I")
            using "disc=Dequiv:1" "\<rightarrow>E" apply blast
            using "v'_eq_b" by blast
        next
          fix u'
          AOT_assume fu'_R1u'v': \<open>[F]u' & [R\<^sub>1]u'v'\<close>

          AOT_hence \<open>[\<lambda>z [R\<^sub>1]u'z]v'\<close>
            by (auto intro!: "\<beta>\<leftarrow>C" "cqt:2" dest: "&E")
          moreover AOT_have \<open>[\<lambda>z [R\<^sub>1]u'z]v' \<equiv> [\<lambda>z [R\<^sub>1]u'z]b\<close>
            using v'_eq_b
            by (safe intro!: "=D-simple:1"[THEN "\<equiv>E"(1), THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"], THEN "\<forall>E"(1)] "cqt:2")
          ultimately AOT_have \<open>[\<lambda>z [R\<^sub>1]u'z]b\<close>
            using "\<equiv>E" by blast
          AOT_hence 0: \<open>[R\<^sub>1]u'b\<close>
            using "\<beta>\<rightarrow>C" by blast
          AOT_have 1: \<open>[\<guillemotleft>?R\<guillemotright>]u'b\<close>
            by (rule "rule=E"[rotated, OF R\<^sub>1_def]) (fact 0)
          AOT_have \<open>(u' \<noteq>\<^sub>D u & b \<noteq>\<^sub>D v & [R]u'b) \<or>
                    (u' =\<^sub>D a & b =\<^sub>D b) \<or>
                    (u' =\<^sub>D u & b =\<^sub>D v)\<close>
            using "\<beta>\<rightarrow>C"(1)[OF 1, simplified] by simp
          moreover {
            AOT_assume 0: \<open>u' \<noteq>\<^sub>D u & b \<noteq>\<^sub>D v & [R]u'b\<close>
            AOT_have \<open>\<exists>!\<^sub>Du ([F]u & [R]uv')\<close>
              using B[THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF gv'].
            AOT_hence \<open>\<exists>!\<^sub>Du ([F]u & [R]ub)\<close>
              by (safe_step intro!: Aux)
                 (auto intro!: "cqt:2" v'_eq_b)
            AOT_hence \<open>\<exists>u ([F]u & [R]ub & \<forall>t ([F]t & [R]tb \<rightarrow> t =\<^sub>D u))\<close>
              using "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"(1)] by fast
            then AOT_obtain s where
              s_prop: \<open>[F]s & [R]sb & \<forall>t ([F]t & [R]tb \<rightarrow> t =\<^sub>D s)\<close>
              using "\<exists>E"[rotated] by blast
            AOT_have \<open>u' =\<^sub>D s\<close>
              using s_prop[THEN "&E"(2), THEN "\<forall>E"(2)]
                    fu'_R1u'v'[THEN "&E"(1)] 0[THEN "&E"(2)]
              by (metis "&I" "\<rightarrow>E")
            moreover AOT_have \<open>u =\<^sub>D s\<close>
              using s_prop[THEN "&E"(2), THEN "\<forall>E"(2)] fu Rub
              by (metis "&I" "\<rightarrow>E")
            ultimately AOT_have \<open>u' =\<^sub>D u\<close>
              by (metis "&I" "disc=Dequiv:2" "disc=Dequiv:3" "\<rightarrow>E")
            moreover AOT_have \<open>\<not>(u' =\<^sub>D u)\<close>
              using 0[THEN "&E"(1), THEN "&E"(1)] by (metis "\<equiv>E"(1) "thm-neg=D") 
            ultimately AOT_have \<open>u' =\<^sub>D a\<close>
              by (metis "raa-cor:3")
          }
          moreover {
            AOT_assume \<open>u' =\<^sub>D u & b =\<^sub>D v\<close>
            AOT_hence \<open>u' =\<^sub>D a\<close>
              by (metis "&E"(2) not_b_eq_v "reductio-aa:1")
          }
          ultimately AOT_show \<open>u' =\<^sub>D a\<close>
            by (metis "&E"(1) "\<or>E"(3) "reductio-aa:1") 
        qed
      }
      ultimately AOT_show \<open>\<exists>!\<^sub>Du ([F]u & [R\<^sub>1]uv')\<close>
        by (metis "raa-cor:1")
    qed
    ultimately AOT_have \<open>\<exists>R R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D [G]\<^sup>-\<^sup>v\<close>
      using 1 by blast
  }
  ultimately AOT_have \<open>\<exists>R R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D [G]\<^sup>-\<^sup>v\<close>
    using R_prop by (metis "reductio-aa:2") 
  AOT_thus \<open>[F]\<^sup>-\<^sup>u \<approx>\<^sub>D [G]\<^sup>-\<^sup>v\<close>
    by (rule "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
qed


AOT_theorem "P'-eq": \<open>[F]\<^sup>-\<^sup>u \<approx>\<^sub>D [G]\<^sup>-\<^sup>v & [F]u & [G]v \<rightarrow> F \<approx>\<^sub>D G\<close>
proof(safe intro!: "\<rightarrow>I"; frule "&E"(1); drule "&E"(2);
      frule "&E"(1); drule "&E"(2))
  AOT_have \<open>[\<lambda>z [\<Pi>]z & z \<noteq>\<^sub>D \<kappa>]\<down>\<close> for \<Pi> \<kappa> by "cqt:2[lambda]"
  note \<Pi>_minus_\<kappa>I = "rule-id-df:2:b[2]"[
      where \<tau>=\<open>(\<lambda>(\<Pi>, \<kappa>). \<guillemotleft>[\<Pi>]\<^sup>-\<^sup>\<kappa>\<guillemotright>)\<close>, simplified, OF "F-u", simplified, OF this]
   and \<Pi>_minus_\<kappa>E = "rule-id-df:2:a[2]"[
   where \<tau>=\<open>(\<lambda>(\<Pi>, \<kappa>). \<guillemotleft>[\<Pi>]\<^sup>-\<^sup>\<kappa>\<guillemotright>)\<close>, simplified, OF "F-u", simplified, OF this]
  AOT_have \<Pi>_minus_\<kappa>_den: \<open>[\<Pi>]\<^sup>-\<^sup>\<kappa>\<down>\<close> for \<Pi> \<kappa>
    by (rule \<Pi>_minus_\<kappa>I) "cqt:2[lambda]"+

  AOT_have \<Pi>_minus_\<kappa>E1: \<open>[\<Pi>]\<kappa>'\<close>
       and \<Pi>_minus_\<kappa>E2: \<open>\<kappa>' \<noteq>\<^sub>D \<kappa>\<close> if \<open>[[\<Pi>]\<^sup>-\<^sup>\<kappa>]\<kappa>'\<close> for \<Pi> \<kappa> \<kappa>'
  proof -
    AOT_have \<open>[\<lambda>z [\<Pi>]z & z \<noteq>\<^sub>D \<kappa>]\<kappa>'\<close>
      using \<Pi>_minus_\<kappa>E that by fast
    AOT_hence \<open>[\<Pi>]\<kappa>' & \<kappa>' \<noteq>\<^sub>D \<kappa>\<close>
      by (rule "\<beta>\<rightarrow>C"(1))
    AOT_thus \<open>[\<Pi>]\<kappa>'\<close> and \<open>\<kappa>' \<noteq>\<^sub>D \<kappa>\<close>
      using "&E" by blast+
  qed
  AOT_have \<Pi>_minus_\<kappa>I': \<open>[[\<Pi>]\<^sup>-\<^sup>\<kappa>]\<kappa>'\<close> if \<open>[\<Pi>]\<kappa>'\<close> and \<open>\<kappa>' \<noteq>\<^sub>D \<kappa>\<close> for \<Pi> \<kappa> \<kappa>'
  proof -
    AOT_have \<kappa>'_den: \<open>\<kappa>'\<down>\<close>
      by (metis "russell-axiom[exe,1].\<psi>_denotes_asm" that(1))
    AOT_have \<open>[\<lambda>z [\<Pi>]z & z \<noteq>\<^sub>D \<kappa>]\<kappa>'\<close>
      by (safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" \<kappa>'_den "&I" that)
    AOT_thus \<open>[[\<Pi>]\<^sup>-\<^sup>\<kappa>]\<kappa>'\<close>
      using \<Pi>_minus_\<kappa>I by fast
  qed

  AOT_assume Gv: \<open>[G]v\<close>
  AOT_assume Fu: \<open>[F]u\<close>
  AOT_assume \<open>[F]\<^sup>-\<^sup>u \<approx>\<^sub>D [G]\<^sup>-\<^sup>v\<close>
  AOT_hence \<open>\<exists>R R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D [G]\<^sup>-\<^sup>v\<close>
    using "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain R where R_prop: \<open>R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D [G]\<^sup>-\<^sup>v\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence Fact1: \<open>\<forall>r([[F]\<^sup>-\<^sup>u]r \<rightarrow> \<exists>!\<^sub>Ds ([[G]\<^sup>-\<^sup>v]s & [R]rs))\<close>
        and Fact1': \<open>\<forall>s([[G]\<^sup>-\<^sup>v]s \<rightarrow> \<exists>!\<^sub>Dr ([[F]\<^sup>-\<^sup>u]r & [R]rs))\<close>
    using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_have \<open>R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oD [G]\<^sup>-\<^sup>v\<close>
    using "equi-rem-thm"[unvarify F G, OF \<Pi>_minus_\<kappa>_den, OF \<Pi>_minus_\<kappa>_den,
                         THEN "\<rightarrow>E", OF R_prop].
  AOT_hence \<open>R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>D [G]\<^sup>-\<^sup>v & R |: [F]\<^sup>-\<^sup>u \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oD [G]\<^sup>-\<^sup>v\<close>
    using "equi-rem:4"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_hence Fact2:
    \<open>\<forall>r\<forall>s\<forall>t(([[F]\<^sup>-\<^sup>u]r & [[F]\<^sup>-\<^sup>u]s & [[G]\<^sup>-\<^sup>v]t) \<rightarrow> ([R]rt & [R]st \<rightarrow> r =\<^sub>D s))\<close>
    using "equi-rem:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast

  let ?R = \<open>\<guillemotleft>[\<lambda>xy ([[F]\<^sup>-\<^sup>u]x & [[G]\<^sup>-\<^sup>v]y & [R]xy) \<or> (x =\<^sub>D u & y =\<^sub>D v)]\<guillemotright>\<close>
  AOT_have R_den: \<open>\<guillemotleft>?R\<guillemotright>\<down>\<close> by "cqt:2[lambda]"

  AOT_show \<open>F \<approx>\<^sub>D G\<close>
  proof(safe intro!: "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(1)[where \<tau>="?R"] R_den
                     "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" GEN "\<rightarrow>I")
    fix r
    AOT_assume Fr: \<open>[F]r\<close>
    {
      AOT_assume not_r_eq_u: \<open>\<not>(r =\<^sub>D u)\<close>
      AOT_hence r_noteq_u: \<open>r \<noteq>\<^sub>D u\<close>
        using "\<equiv>E"(2) "thm-neg=D" by blast
      AOT_have \<open>[[F]\<^sup>-\<^sup>u]r\<close>
        by(rule \<Pi>_minus_\<kappa>I; safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" Fr r_noteq_u)
      AOT_hence \<open>\<exists>!\<^sub>Ds ([[G]\<^sup>-\<^sup>v]s & [R]rs)\<close>
        using Fact1[THEN "\<forall>E"(2)] "\<rightarrow>E"  by blast
      AOT_hence \<open>\<exists>s ([[G]\<^sup>-\<^sup>v]s & [R]rs & \<forall>t ([[G]\<^sup>-\<^sup>v]t & [R]rt \<rightarrow> t =\<^sub>D s))\<close>
        using "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by simp
      then AOT_obtain s where s_prop: \<open>[[G]\<^sup>-\<^sup>v]s & [R]rs & \<forall>t ([[G]\<^sup>-\<^sup>v]t & [R]rt \<rightarrow> t =\<^sub>D s)\<close>
        using "\<exists>E"[rotated] by blast
      AOT_hence G_minus_v_s: \<open>[[G]\<^sup>-\<^sup>v]s\<close> and Rrs: \<open>[R]rs\<close>
        using "&E" by blast+
      AOT_have s_unique: \<open>t =\<^sub>D s\<close> if \<open>[[G]\<^sup>-\<^sup>v]t\<close> and \<open>[R]rt\<close> for t
        using s_prop[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF "&I", OF that].
      AOT_have Gs: \<open>[G]s\<close>
        using \<Pi>_minus_\<kappa>E1[OF G_minus_v_s].
      AOT_have s_noteq_v: \<open>s \<noteq>\<^sub>D v\<close>
        using \<Pi>_minus_\<kappa>E2[OF G_minus_v_s].
      AOT_have \<open>\<exists>s ([G]s & [\<guillemotleft>?R\<guillemotright>]rs & (\<forall>t ([G]t & [\<guillemotleft>?R\<guillemotright>]rt \<rightarrow> t =\<^sub>D s)))\<close>
      proof(safe intro!: "\<exists>I"(2)[where \<beta>=s] "&I" Gs GEN "\<rightarrow>I")
        AOT_show \<open>[\<guillemotleft>?R\<guillemotright>]rs\<close>
          by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" "\<or>I"(1) \<Pi>_minus_\<kappa>I' Fr Gs
                           s_noteq_v Rrs r_noteq_u
                   simp: "&I" "ex:1:a" prod_denotesI "rule-ui:3")
      next
        fix t
        AOT_assume 0: \<open>[G]t & [\<guillemotleft>?R\<guillemotright>]rt\<close>
        AOT_hence \<open>([[F]\<^sup>-\<^sup>u]r & [[G]\<^sup>-\<^sup>v]t & [R]rt) \<or> (r =\<^sub>D u & t =\<^sub>D v)\<close>
          using "\<beta>\<rightarrow>C"(1)[OF 0[THEN "&E"(2)], simplified] by blast
        AOT_hence 1: \<open>[[F]\<^sup>-\<^sup>u]r & [[G]\<^sup>-\<^sup>v]t & [R]rt\<close>
          using not_r_eq_u by (metis "&E"(1) "\<or>E"(3) "reductio-aa:1")
        AOT_show \<open>t =\<^sub>D s\<close> using s_unique 1 "&E" by blast
      qed
    }
    moreover {
      AOT_assume r_eq_u: \<open>r =\<^sub>D u\<close>
      AOT_have \<open>\<exists>s ([G]s & [\<guillemotleft>?R\<guillemotright>]rs & (\<forall>t ([G]t & [\<guillemotleft>?R\<guillemotright>]rt \<rightarrow> t =\<^sub>D s)))\<close>
      proof(safe intro!: "\<exists>I"(2)[where \<beta>=v] "&I" Gv GEN "\<rightarrow>I")
        AOT_show \<open>[\<guillemotleft>?R\<guillemotright>]rv\<close>
          by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" "\<or>I"(2) \<Pi>_minus_\<kappa>I' Fr r_eq_u
                           "ord=Eequiv:1"[THEN "\<rightarrow>E"] Discernible.\<psi>
                   simp: "&I" "ex:1:a" prod_denotesI "rule-ui:3" "disc=Dequiv:1")
      next
        fix t
        AOT_assume 0: \<open>[G]t & [\<guillemotleft>?R\<guillemotright>]rt\<close>
        AOT_hence \<open>([[F]\<^sup>-\<^sup>u]r & [[G]\<^sup>-\<^sup>v]t & [R]rt) \<or> (r =\<^sub>D u & t =\<^sub>D v)\<close>
          using "\<beta>\<rightarrow>C"(1)[OF 0[THEN "&E"(2)], simplified] by blast
        AOT_hence \<open>r =\<^sub>D u & t =\<^sub>D v\<close>
          using r_eq_u \<Pi>_minus_\<kappa>E2
          by (metis "&E"(1) "\<or>E"(2) "\<equiv>E"(1) "reductio-aa:1" "thm-neg=D")
        AOT_thus \<open>t =\<^sub>D v\<close> using "&E" by blast
      qed
    }
    ultimately AOT_show \<open>\<exists>!\<^sub>Ds ([G]s & [\<guillemotleft>?R\<guillemotright>]rs)\<close>
      using "reductio-aa:2" "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] by fast
  next
    fix s
    AOT_assume Gs: \<open>[G]s\<close>

    {
      AOT_assume not_s_eq_v: \<open>\<not>(s =\<^sub>D v)\<close>
      AOT_hence s_noteq_v: \<open>s \<noteq>\<^sub>D v\<close>
        using "\<equiv>E"(2) "thm-neg=D" by blast
      AOT_have \<open>[[G]\<^sup>-\<^sup>v]s\<close>
        by (rule \<Pi>_minus_\<kappa>I; auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" Gs s_noteq_v)
      AOT_hence \<open>\<exists>!\<^sub>Dr ([[F]\<^sup>-\<^sup>u]r & [R]rs)\<close>
        using Fact1'[THEN "\<forall>E"(2)] "\<rightarrow>E" by blast
      AOT_hence \<open>\<exists>r ([[F]\<^sup>-\<^sup>u]r & [R]rs & \<forall>t ([[F]\<^sup>-\<^sup>u]t & [R]ts \<rightarrow> t =\<^sub>D r))\<close>
        using "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by simp
      then AOT_obtain r where
        r_prop: \<open>[[F]\<^sup>-\<^sup>u]r & [R]rs & \<forall>t ([[F]\<^sup>-\<^sup>u]t & [R]ts \<rightarrow> t =\<^sub>D r)\<close>
        using "\<exists>E"[rotated] by blast
      AOT_hence F_minus_u_r: \<open>[[F]\<^sup>-\<^sup>u]r\<close> and Rrs: \<open>[R]rs\<close>
        using "&E" by blast+
      AOT_have r_unique: \<open>t =\<^sub>D r\<close> if \<open>[[F]\<^sup>-\<^sup>u]t\<close> and \<open>[R]ts\<close> for t
        using r_prop[THEN "&E"(2), THEN "\<forall>E"(2),
                     THEN "\<rightarrow>E", OF "&I", OF that].
      AOT_have Fr: \<open>[F]r\<close>
        using \<Pi>_minus_\<kappa>E1[OF F_minus_u_r].
      AOT_have r_noteq_u: \<open>r \<noteq>\<^sub>D u\<close>
        using \<Pi>_minus_\<kappa>E2[OF F_minus_u_r].
      AOT_have \<open>\<exists>r ([F]r & [\<guillemotleft>?R\<guillemotright>]rs & (\<forall>t ([F]t & [\<guillemotleft>?R\<guillemotright>]ts \<rightarrow> t =\<^sub>D r)))\<close>
      proof(safe intro!: "\<exists>I"(2)[where \<beta>=r] "&I" Fr GEN "\<rightarrow>I")
        AOT_show \<open>[\<guillemotleft>?R\<guillemotright>]rs\<close>
          by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" "\<or>I"(1) \<Pi>_minus_\<kappa>I' Fr
                           Gs s_noteq_v Rrs r_noteq_u
                   simp: "&I" "ex:1:a" prod_denotesI "rule-ui:3")
      next
        fix t
        AOT_assume 0: \<open>[F]t & [\<guillemotleft>?R\<guillemotright>]ts\<close>
        AOT_hence \<open>([[F]\<^sup>-\<^sup>u]t & [[G]\<^sup>-\<^sup>v]s & [R]ts) \<or> (t =\<^sub>D u & s =\<^sub>D v)\<close>
          using "\<beta>\<rightarrow>C"(1)[OF 0[THEN "&E"(2)], simplified] by blast
        AOT_hence 1: \<open>[[F]\<^sup>-\<^sup>u]t & [[G]\<^sup>-\<^sup>v]s & [R]ts\<close>
          using not_s_eq_v by (metis "&E"(2) "\<or>E"(3) "reductio-aa:1")
        AOT_show \<open>t =\<^sub>D r\<close> using r_unique 1 "&E" by blast
      qed
    }
    moreover {
      AOT_assume s_eq_v: \<open>s =\<^sub>D v\<close>
      AOT_have \<open>\<exists>r ([F]r & [\<guillemotleft>?R\<guillemotright>]rs & (\<forall>t ([F]t & [\<guillemotleft>?R\<guillemotright>]ts \<rightarrow> t =\<^sub>D r)))\<close>
      proof(safe intro!: "\<exists>I"(2)[where \<beta>=u] "&I" Fu GEN "\<rightarrow>I")
        AOT_show \<open>[\<guillemotleft>?R\<guillemotright>]us\<close>
          by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" prod_denotesI "\<or>I"(2)
                            \<Pi>_minus_\<kappa>I' Gs s_eq_v
                            "disc=Dequiv:1")
      next
        fix t
        AOT_assume 0: \<open>[F]t & [\<guillemotleft>?R\<guillemotright>]ts\<close>
        AOT_hence 1: \<open>([[F]\<^sup>-\<^sup>u]t & [[G]\<^sup>-\<^sup>v]s & [R]ts) \<or> (t =\<^sub>D u & s =\<^sub>D v)\<close>
          using "\<beta>\<rightarrow>C"(1)[OF 0[THEN "&E"(2)], simplified] by blast
        moreover AOT_have \<open>\<not>([[F]\<^sup>-\<^sup>u]t & [[G]\<^sup>-\<^sup>v]s & [R]ts)\<close>
        proof (rule "raa-cor:2")
          AOT_assume \<open>([[F]\<^sup>-\<^sup>u]t & [[G]\<^sup>-\<^sup>v]s & [R]ts)\<close>
          AOT_hence \<open>[[G]\<^sup>-\<^sup>v]s\<close> using "&E" by blast
          AOT_thus \<open>s =\<^sub>D v & \<not>(s =\<^sub>D v)\<close>
            by (metis \<Pi>_minus_\<kappa>E2 "\<equiv>E"(4) "reductio-aa:1" s_eq_v "thm-neg=D")
        qed
        ultimately AOT_have \<open>t =\<^sub>D u & s =\<^sub>D v\<close>
          by (metis "\<or>E"(2))
        AOT_thus \<open>t =\<^sub>D u\<close> using "&E" by blast
      qed
    }
    ultimately AOT_show \<open>\<exists>!\<^sub>Dr ([F]r & [\<guillemotleft>?R\<guillemotright>]rs)\<close>
      using "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "reductio-aa:2" by fast
  qed
qed


AOT_theorem "approx-cont:1": \<open>\<exists>F\<exists>G \<diamond>(F \<approx>\<^sub>D G & \<diamond>\<not>F \<approx>\<^sub>D G)\<close>
proof -
  let ?P = \<open>\<guillemotleft>[\<lambda>x E!x & \<not>\<^bold>\<A>E!x]\<guillemotright>\<close>
  AOT_have \<open>\<diamond>q\<^sub>0 & \<diamond>\<not>q\<^sub>0\<close> by (metis q\<^sub>0_prop)
  AOT_hence 1: \<open>\<diamond>\<exists>x(E!x & \<not>\<^bold>\<A>E!x) & \<diamond>\<not>\<exists>x(E!x & \<not>\<^bold>\<A>E!x)\<close>
    by (rule q\<^sub>0_def[THEN "=\<^sub>d\<^sub>fE"(2), rotated])
       (simp add: "log-prop-prop:2")
  AOT_have \<theta>: \<open>\<diamond>\<exists>x [\<guillemotleft>?P\<guillemotright>]x & \<diamond>\<not>\<exists>x [\<guillemotleft>?P\<guillemotright>]x\<close>
    apply (AOT_subst \<open>[\<guillemotleft>?P\<guillemotright>]x\<close> \<open>E!x & \<not>\<^bold>\<A>E!x\<close> for: x)
     apply (rule "beta-C-meta"[THEN "\<rightarrow>E"]; "cqt:2[lambda]")
    by (fact 1)
  show ?thesis
  proof (rule "\<exists>I"(1))+
    AOT_have \<open>\<diamond>[L]\<^sup>- \<approx>\<^sub>D [\<guillemotleft>?P\<guillemotright>] & \<diamond>\<not>[L]\<^sup>- \<approx>\<^sub>D [\<guillemotleft>?P\<guillemotright>]\<close>
    proof (rule "&I"; rule "RM\<diamond>"[THEN "\<rightarrow>E"]; (rule "\<rightarrow>I")?)
      AOT_modally_strict {
        AOT_assume A: \<open>\<not>\<exists>x [\<guillemotleft>?P\<guillemotright>]x\<close>
        AOT_show \<open>[L]\<^sup>- \<approx>\<^sub>D [\<guillemotleft>?P\<guillemotright>]\<close>
        proof (safe intro!: "empty-approx:1"[unvarify F H, THEN "\<rightarrow>E"]
                            "rel-neg-T:3" "&I")
          AOT_show \<open>[\<guillemotleft>?P\<guillemotright>]\<down>\<close> by "cqt:2[lambda]"
        next
          AOT_show \<open>\<not>\<exists>u [L\<^sup>-]u\<close>
          proof (rule "raa-cor:2")
            AOT_assume \<open>\<exists>u [L\<^sup>-]u\<close>
            then AOT_obtain u where \<open>[L\<^sup>-]u\<close>
              using "\<exists>E"[rotated] by blast
            moreover AOT_have \<open>\<not>[L\<^sup>-]u\<close>
              using "thm-noncont-e-e:2"[THEN "contingent-properties:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"],
                                        THEN "&E"(2)]
              by (metis "qml:2"[axiom_inst] "rule-ui:3" "\<rightarrow>E")
            ultimately AOT_show \<open>p & \<not>p\<close> for p
              by (metis  "raa-cor:3")
          qed
        next
          AOT_show \<open>\<not>\<exists>v [\<guillemotleft>?P\<guillemotright>]v\<close>
          proof (rule "raa-cor:2")
            AOT_assume \<open>\<exists>v [\<guillemotleft>?P\<guillemotright>]v\<close>
            then AOT_obtain u where \<open>[\<guillemotleft>?P\<guillemotright>]u\<close>
              using "\<exists>E"[rotated] by blast
            AOT_hence \<open>[\<guillemotleft>?P\<guillemotright>]u\<close>
              using "&E" by blast
            AOT_hence \<open>\<exists>x [\<guillemotleft>?P\<guillemotright>]x\<close>
              by (rule "\<exists>I")
            AOT_thus \<open>\<exists>x [\<guillemotleft>?P\<guillemotright>]x & \<not>\<exists>x [\<guillemotleft>?P\<guillemotright>]x\<close>
              using A "&I" by blast
          qed
        qed
      }
    next
      AOT_show \<open>\<diamond>\<not>\<exists>x [\<guillemotleft>?P\<guillemotright>]x\<close>
        using \<theta> "&E" by blast
    next
      AOT_modally_strict {
        AOT_assume A: \<open>\<exists>x [\<guillemotleft>?P\<guillemotright>]x\<close>
        AOT_have B: \<open>\<not>[\<guillemotleft>?P\<guillemotright>] \<approx>\<^sub>D [L]\<^sup>-\<close>
        proof (safe intro!: "empty-approx:2"[unvarify F H, THEN "\<rightarrow>E"]
                            "rel-neg-T:3" "&I")
          AOT_show \<open>[\<guillemotleft>?P\<guillemotright>]\<down>\<close>
            by "cqt:2[lambda]"
        next
          AOT_obtain x where Px: \<open>[\<guillemotleft>?P\<guillemotright>]x\<close>
            using A "\<exists>E" by blast
          AOT_hence \<open>E!x & \<not>\<^bold>\<A>E!x\<close>
            by (rule "\<beta>\<rightarrow>C"(1))
          AOT_hence 1: \<open>\<diamond>E!x\<close>
            by (metis "T\<diamond>" "&E"(1) "vdash-properties:10")
          AOT_have \<open>[\<lambda>x \<diamond>E!x]x\<close>
            by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" 1)
          AOT_hence \<open>O!x\<close>
            by (rule AOT_ordinary[THEN "=\<^sub>d\<^sub>fI"(2), rotated]) "cqt:2[lambda]"
          AOT_hence \<open>D!x\<close>
            using ord_disc[THEN "\<rightarrow>E"] by blast
          AOT_hence \<open>[\<guillemotleft>?P\<guillemotright>]x\<close>
            using Px "&I" by blast
          AOT_thus \<open>\<exists>u [\<guillemotleft>?P\<guillemotright>]u\<close>
            by (rule "\<exists>I")
        next
          AOT_show \<open>\<not>\<exists>u [L\<^sup>-]u\<close>
          proof (rule "raa-cor:2")
            AOT_assume \<open>\<exists>u [L\<^sup>-]u\<close>
            then AOT_obtain u where \<open>[L\<^sup>-]u\<close>
              using "\<exists>E"[rotated] by blast
            moreover AOT_have \<open>\<not>[L\<^sup>-]u\<close>
              using "thm-noncont-e-e:2"[THEN "contingent-properties:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"]]
              by (metis "qml:2"[axiom_inst] "rule-ui:3" "\<rightarrow>E" "&E"(2))
            ultimately AOT_show \<open>p & \<not>p\<close> for p
              by (metis "raa-cor:3")
          qed
        qed
        AOT_show \<open>\<not>[L]\<^sup>- \<approx>\<^sub>D [\<guillemotleft>?P\<guillemotright>]\<close>
        proof (rule "raa-cor:2")
          AOT_assume \<open>[L]\<^sup>- \<approx>\<^sub>D [\<guillemotleft>?P\<guillemotright>]\<close>
          AOT_hence \<open>[\<guillemotleft>?P\<guillemotright>] \<approx>\<^sub>D [L]\<^sup>-\<close>
            apply (rule "eq-part:2"[unvarify F G, THEN "\<rightarrow>E", rotated 2])
             apply "cqt:2[lambda]"
            by (simp add: "rel-neg-T:3")
          AOT_thus \<open>[\<guillemotleft>?P\<guillemotright>] \<approx>\<^sub>D [L]\<^sup>- & \<not>[\<guillemotleft>?P\<guillemotright>] \<approx>\<^sub>D [L]\<^sup>-\<close>
            using B "&I" by blast
        qed
      }
    next
      AOT_show \<open>\<diamond>\<exists>x [\<guillemotleft>?P\<guillemotright>]x\<close>
        using \<theta> "&E" by blast
    qed
    AOT_thus \<open>\<diamond>([L]\<^sup>- \<approx>\<^sub>D [\<guillemotleft>?P\<guillemotright>] & \<diamond>\<not>[L]\<^sup>- \<approx>\<^sub>D [\<guillemotleft>?P\<guillemotright>])\<close>
      using "S5Basic:11" "\<equiv>E"(2) by blast
  next
    AOT_show \<open>[\<lambda>x [E!]x & \<not>\<^bold>\<A>[E!]x]\<down>\<close>
      by "cqt:2"
  next
    AOT_show \<open>[L]\<^sup>-\<down>\<close>
      by (simp add: "rel-neg-T:3")
  qed
qed


AOT_theorem "approx-cont:2":
  \<open>\<exists>F\<exists>G \<diamond>([\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G & \<diamond>\<not>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>
proof -
  let ?P = \<open>\<guillemotleft>[\<lambda>x E!x & \<not>\<^bold>\<A>E!x]\<guillemotright>\<close>
  AOT_have \<open>\<diamond>q\<^sub>0 & \<diamond>\<not>q\<^sub>0\<close> by (metis q\<^sub>0_prop)
  AOT_hence 1: \<open>\<diamond>\<exists>x(E!x & \<not>\<^bold>\<A>E!x) & \<diamond>\<not>\<exists>x(E!x & \<not>\<^bold>\<A>E!x)\<close>
    by (rule q\<^sub>0_def[THEN "=\<^sub>d\<^sub>fE"(2), rotated])
       (simp add: "log-prop-prop:2")
  AOT_have \<theta>: \<open>\<diamond>\<exists>x [\<guillemotleft>?P\<guillemotright>]x & \<diamond>\<not>\<exists>x [\<guillemotleft>?P\<guillemotright>]x\<close>
    apply (AOT_subst \<open>[\<guillemotleft>?P\<guillemotright>]x\<close> \<open>E!x & \<not>\<^bold>\<A>E!x\<close> for: x)
     apply (rule "beta-C-meta"[THEN "\<rightarrow>E"]; "cqt:2")
    by (fact 1)
  show ?thesis
  proof (rule "\<exists>I"(1))+
    AOT_have \<open>\<diamond>[\<lambda>z \<^bold>\<A>[L\<^sup>-]z] \<approx>\<^sub>D [\<guillemotleft>?P\<guillemotright>] & \<diamond>\<not>[\<lambda>z \<^bold>\<A>[L\<^sup>-]z] \<approx>\<^sub>D [\<guillemotleft>?P\<guillemotright>]\<close>
    proof (rule "&I"; rule "RM\<diamond>"[THEN "\<rightarrow>E"]; (rule "\<rightarrow>I")?)
      AOT_modally_strict {
        AOT_assume A: \<open>\<not>\<exists>x [\<guillemotleft>?P\<guillemotright>]x\<close>
        AOT_show \<open>[\<lambda>z \<^bold>\<A>[L\<^sup>-]z] \<approx>\<^sub>D [\<guillemotleft>?P\<guillemotright>]\<close>
        proof (safe intro!: "empty-approx:1"[unvarify F H, THEN "\<rightarrow>E"]
                            "rel-neg-T:3" "&I")
          AOT_show \<open>[\<guillemotleft>?P\<guillemotright>]\<down>\<close> by "cqt:2"
        next
          AOT_show \<open>\<not>\<exists>u [\<lambda>z \<^bold>\<A>[L\<^sup>-]z]u\<close>
          proof (rule "raa-cor:2")
            AOT_assume \<open>\<exists>u [\<lambda>z \<^bold>\<A>[L\<^sup>-]z]u\<close>
            then AOT_obtain u where \<open>[\<lambda>z \<^bold>\<A>[L\<^sup>-]z]u\<close>
              using "\<exists>E"[rotated] by blast
            AOT_hence \<open>\<^bold>\<A>[L\<^sup>-]u\<close>
              using "\<beta>\<rightarrow>C"(1) "&E" by blast
            moreover AOT_have \<open>\<box>\<not>[L\<^sup>-]u\<close>
              using "thm-noncont-e-e:2"[THEN "contingent-properties:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"]]
              by (metis RN "qml:2"[axiom_inst] "rule-ui:3" "\<rightarrow>E" "&E"(2))
            ultimately AOT_show \<open>p & \<not>p\<close> for p
              by (metis "Act-Sub:3" "KBasic2:1" "\<equiv>E"(1) "raa-cor:3" "\<rightarrow>E")
          qed
        next
          AOT_show \<open>\<not>\<exists>v [\<guillemotleft>?P\<guillemotright>]v\<close>
          proof (rule "raa-cor:2")
            AOT_assume \<open>\<exists>v [\<guillemotleft>?P\<guillemotright>]v\<close>
            then AOT_obtain u where \<open>[\<guillemotleft>?P\<guillemotright>]u\<close>
              using "\<exists>E"[rotated] by blast
            AOT_hence \<open>[\<guillemotleft>?P\<guillemotright>]u\<close>
              using "&E" by blast
            AOT_hence \<open>\<exists>x [\<guillemotleft>?P\<guillemotright>]x\<close>
              by (rule "\<exists>I")
            AOT_thus \<open>\<exists>x [\<guillemotleft>?P\<guillemotright>]x & \<not>\<exists>x [\<guillemotleft>?P\<guillemotright>]x\<close>
              using A "&I" by blast
          qed
        next
          AOT_show \<open>[\<lambda>z \<^bold>\<A>[L\<^sup>-]z]\<down>\<close> by "cqt:2"
        qed
      }
    next
      AOT_show \<open>\<diamond>\<not>\<exists>x [\<guillemotleft>?P\<guillemotright>]x\<close> using \<theta> "&E" by blast
    next
      AOT_modally_strict {
        AOT_assume A: \<open>\<exists>x [\<guillemotleft>?P\<guillemotright>]x\<close>
        AOT_have B: \<open>\<not>[\<guillemotleft>?P\<guillemotright>] \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[L\<^sup>-]z]\<close>
        proof (safe intro!: "empty-approx:2"[unvarify F H, THEN "\<rightarrow>E"]
                            "rel-neg-T:3" "&I")
          AOT_show \<open>[\<guillemotleft>?P\<guillemotright>]\<down>\<close> by "cqt:2"
        next
          AOT_obtain x where Px: \<open>[\<guillemotleft>?P\<guillemotright>]x\<close>
            using A "\<exists>E" by blast
          AOT_hence \<open>E!x & \<not>\<^bold>\<A>E!x\<close>
            by (rule "\<beta>\<rightarrow>C"(1))
          AOT_hence \<open>\<diamond>E!x\<close>
            by (metis "T\<diamond>" "&E"(1) "\<rightarrow>E")
          AOT_hence \<open>[\<lambda>x \<diamond>E!x]x\<close>
            by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2")
          AOT_hence \<open>O!x\<close>
            by (rule AOT_ordinary[THEN "=\<^sub>d\<^sub>fI"(2), rotated]) "cqt:2"
          AOT_hence \<open>D!x\<close>
            using "ord_disc"[THEN "\<rightarrow>E"] by blast
          AOT_hence \<open>[\<guillemotleft>?P\<guillemotright>]x\<close>
            using Px "&I" by blast
          AOT_thus \<open>\<exists>u [\<guillemotleft>?P\<guillemotright>]u\<close>
            by (rule "\<exists>I")
        next
          AOT_show \<open>\<not>\<exists>u [\<lambda>z \<^bold>\<A>[L\<^sup>-]z]u\<close>
          proof (rule "raa-cor:2")
            AOT_assume \<open>\<exists>u [\<lambda>z \<^bold>\<A>[L\<^sup>-]z]u\<close>
            then AOT_obtain u where \<open>[\<lambda>z \<^bold>\<A>[L\<^sup>-]z]u\<close>
              using "\<exists>E"[rotated] by blast
            AOT_hence \<open>\<^bold>\<A>[L\<^sup>-]u\<close>
              using "\<beta>\<rightarrow>C"(1) "&E" by blast
            moreover AOT_have \<open>\<box>\<not>[L\<^sup>-]u\<close>
              using "thm-noncont-e-e:2"[THEN "contingent-properties:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"]]
              by (metis RN "qml:2"[axiom_inst] "rule-ui:3" "\<rightarrow>E" "&E"(2))
            ultimately AOT_show \<open>p & \<not>p\<close> for p
              by (metis "Act-Sub:3" "KBasic2:1" "\<equiv>E"(1) "raa-cor:3" "\<rightarrow>E")
          qed
        next
          AOT_show \<open>[\<lambda>z \<^bold>\<A>[L\<^sup>-]z]\<down>\<close> by "cqt:2"
        qed
        AOT_show \<open>\<not>[\<lambda>z \<^bold>\<A>[L\<^sup>-]z] \<approx>\<^sub>D [\<guillemotleft>?P\<guillemotright>]\<close>
        proof (rule "raa-cor:2")
          AOT_assume \<open>[\<lambda>z \<^bold>\<A>[L\<^sup>-]z] \<approx>\<^sub>D [\<guillemotleft>?P\<guillemotright>]\<close>
          AOT_hence \<open>[\<guillemotleft>?P\<guillemotright>] \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[L\<^sup>-]z]\<close>
            by (rule "eq-part:2"[unvarify F G, THEN "\<rightarrow>E", rotated 2])
               "cqt:2"+
          AOT_thus \<open>[\<guillemotleft>?P\<guillemotright>] \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[L\<^sup>-]z] & \<not>[\<guillemotleft>?P\<guillemotright>] \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[L\<^sup>-]z]\<close>
            using B "&I" by blast
        qed
      }
    next
      AOT_show \<open>\<diamond>\<exists>x [\<guillemotleft>?P\<guillemotright>]x\<close>
        using \<theta> "&E" by blast
    qed
    AOT_thus \<open>\<diamond>([\<lambda>z \<^bold>\<A>[L\<^sup>-]z] \<approx>\<^sub>D [\<guillemotleft>?P\<guillemotright>] & \<diamond>\<not>[\<lambda>z \<^bold>\<A>[L\<^sup>-]z] \<approx>\<^sub>D [\<guillemotleft>?P\<guillemotright>])\<close>
      using "S5Basic:11" "\<equiv>E"(2) by blast
  next
    AOT_show \<open>[\<lambda>x [E!]x & \<not>\<^bold>\<A>[E!]x]\<down>\<close> by "cqt:2"
  next
    AOT_show \<open>[L]\<^sup>-\<down>\<close>
      by (simp add: "rel-neg-T:3")
  qed
qed

AOT_define eqD :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl \<open>\<equiv>\<^sub>D\<close> 50)
  \<open>F \<equiv>\<^sub>D G \<equiv>\<^sub>d\<^sub>f F\<down> & G\<down> & \<forall>u ([F]u \<equiv> [G]u)\<close>

AOT_theorem "apE-eqE:1": \<open>F \<equiv>\<^sub>D G \<rightarrow> F \<approx>\<^sub>D G\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>F \<equiv>\<^sub>D G\<close>
  AOT_have \<open>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
  proof (safe intro!: "\<exists>I"(1)[where \<tau>="\<guillemotleft>(=\<^sub>D)\<guillemotright>"] "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I"
                      "=D[denotes]" "cqt:2[const_var]"[axiom_inst] GEN
                      "\<rightarrow>I" "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
    fix u
    AOT_assume Fu: \<open>[F]u\<close>
    AOT_hence Gu: \<open>[G]u\<close>
      using "\<equiv>\<^sub>d\<^sub>fE"[OF eqD, OF 0, THEN "&E"(2),
                   THEN "\<forall>E"(2)[where \<beta>=u], THEN "\<equiv>E"(1)]
            Fu by blast
    AOT_show \<open>\<exists>v ([G]v & u =\<^sub>D v & \<forall>v' ([G]v' & u =\<^sub>D v' \<rightarrow> v' =\<^sub>D v))\<close>
      by (auto intro!: "\<exists>I"(2)[where \<beta>=u] "&I" GEN "\<rightarrow>I" Gu
                       "disc=Dequiv:1"
                       "disc=Dequiv:2"[THEN "\<rightarrow>E"] dest!: "&E"(2))
  next
    fix v
    AOT_assume Gv: \<open>[G]v\<close>
    AOT_hence Fv: \<open>[F]v\<close>
      using "\<equiv>\<^sub>d\<^sub>fE"[OF eqD, OF 0, THEN "&E"(2),
                   THEN "\<forall>E"(2)[where \<beta>=v], THEN "\<equiv>E"(2)]
            Gv by blast
    AOT_show \<open>\<exists>u ([F]u & u =\<^sub>D v & \<forall>v' ([F]v' & v' =\<^sub>D v \<rightarrow> v' =\<^sub>D u))\<close>
      by (safe intro!: "\<exists>I"(2)[where \<beta>=v] "&I" GEN "\<rightarrow>I" Discernible.\<psi> Fv
                       "disc=Dequiv:1"
                       "disc=Dequiv:2"[THEN "\<rightarrow>E"] dest!: "&E"(2))
  qed
  AOT_thus \<open>F \<approx>\<^sub>D G\<close>
    by (rule "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
qed

AOT_theorem "apE-eqE:2": \<open>(F \<approx>\<^sub>D G & G \<equiv>\<^sub>D H) \<rightarrow> F \<approx>\<^sub>D H\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>F \<approx>\<^sub>D G & G \<equiv>\<^sub>D H\<close>
  AOT_hence \<open>F \<approx>\<^sub>D G\<close> and \<open>G \<approx>\<^sub>D H\<close>
    using "apE-eqE:1"[THEN "\<rightarrow>E"] "&E" by blast+
  AOT_thus \<open>F \<approx>\<^sub>D H\<close>
    by (metis Adjunction "eq-part:3" "vdash-properties:10")
qed


AOT_act_theorem "eq-part-act:1": \<open>[\<lambda>z \<^bold>\<A>[F]z] \<equiv>\<^sub>D F\<close>
proof (safe intro!: eqD[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" GEN "\<rightarrow>I")
  fix u
  AOT_have \<open>[\<lambda>z \<^bold>\<A>[F]z]u \<equiv> \<^bold>\<A>[F]u\<close>
    by (rule "beta-C-meta"[THEN "\<rightarrow>E"]) "cqt:2[lambda]"
  also AOT_have \<open>\<dots> \<equiv> [F]u\<close>
    using "act-conj-act:4" "logic-actual"[act_axiom_inst, THEN "\<rightarrow>E"] by blast
  finally AOT_show \<open>[\<lambda>z \<^bold>\<A>[F]z]u \<equiv> [F]u\<close>.
qed

AOT_act_theorem "eq-part-act:2": \<open>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D F\<close>
  by (safe intro!: "apE-eqE:1"[unvarify F, THEN "\<rightarrow>E"] "eq-part-act:1") "cqt:2"


AOT_theorem "actuallyF:1": \<open>\<^bold>\<A>(F \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[F]z])\<close>
proof -
  AOT_have 1: \<open>\<^bold>\<A>([F]x \<equiv> \<^bold>\<A>[F]x)\<close> for x
    by (meson "Act-Basic:5" "act-conj-act:4" "\<equiv>E"(2) "Commutativity of \<equiv>")
  AOT_have \<open>\<^bold>\<A>([F]x \<equiv> [\<lambda>z \<^bold>\<A>[F]z]x)\<close> for x
    apply (AOT_subst \<open>[\<lambda>z \<^bold>\<A>[F]z]x\<close> \<open>\<^bold>\<A>[F]x\<close>)
     apply (rule "beta-C-meta"[THEN "\<rightarrow>E"])
     apply "cqt:2[lambda]"
    by (fact 1)
  AOT_hence \<open>\<forall>u \<^bold>\<A>([F]u \<equiv> [\<lambda>z \<^bold>\<A>[F]z]u)\<close>
    using "\<forall>I" by fast
  AOT_hence 1: \<open>\<^bold>\<A>\<forall>u ([F]u \<equiv> [\<lambda>z \<^bold>\<A>[F]z]u)\<close>
    using "logic-actual-nec:3"[axiom_inst, THEN "\<equiv>E"(2)] by fast
  AOT_modally_strict {
    AOT_have \<open>[\<lambda>z \<^bold>\<A>[F]z]\<down>\<close> by "cqt:2"
  } note 2 = this
  AOT_have \<open>\<^bold>\<A>(F \<equiv>\<^sub>D [\<lambda>z \<^bold>\<A>[F]z])\<close>
    apply (AOT_subst \<open>F \<equiv>\<^sub>D [\<lambda>z \<^bold>\<A>[F]z]\<close> \<open>\<forall>u ([F]u \<equiv> [\<lambda>z \<^bold>\<A>[F]z]u)\<close>)
    using eqD[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I",
              OF "cqt:2[const_var]"[axiom_inst], OF 2]
    by (auto simp: 1)
  moreover AOT_have \<open>\<^bold>\<A>(F \<equiv>\<^sub>D [\<lambda>z \<^bold>\<A>[F]z] \<rightarrow> F \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[F]z])\<close>
    using "apE-eqE:1"[unvarify G, THEN "RA[2]", OF 2] by metis
  ultimately AOT_show \<open>\<^bold>\<A>F \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[F]z]\<close>
    by (metis "act-cond" "\<rightarrow>E")
qed

AOT_theorem "actuallyF:2": \<open>Rigid([\<lambda>z \<^bold>\<A>[F]z])\<close>
proof(safe intro!: GEN "\<rightarrow>I" "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I")
  AOT_show \<open>[\<lambda>z \<^bold>\<A>[F]z]\<down>\<close> by "cqt:2"
next
  AOT_show \<open>\<box>\<forall>x ([\<lambda>z \<^bold>\<A>[F]z]x \<rightarrow> \<box>[\<lambda>z \<^bold>\<A>[F]z]x)\<close>
  proof(rule RN; rule GEN; rule "\<rightarrow>I")
    AOT_modally_strict {
      fix x
      AOT_assume \<open>[\<lambda>z \<^bold>\<A>[F]z]x\<close>
      AOT_hence \<open>\<^bold>\<A>[F]x\<close>
        by (rule "\<beta>\<rightarrow>C"(1))
      AOT_hence 1: \<open>\<box>\<^bold>\<A>[F]x\<close> by (metis "Act-Basic:6" "\<equiv>E"(1))
      AOT_show \<open>\<box>[\<lambda>z \<^bold>\<A>[F]z]x\<close>
        apply (AOT_subst \<open>[\<lambda>z \<^bold>\<A>[F]z]x\<close> \<open>\<^bold>\<A>[F]x\<close>)
         apply (rule "beta-C-meta"[THEN "\<rightarrow>E"])
         apply "cqt:2[lambda]"
        by (fact 1)
    }
  qed
qed

AOT_theorem "approx-nec:1": \<open>Rigid(F) \<rightarrow> F \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[F]z]\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>Rigid([F])\<close>
  AOT_hence A: \<open>\<box>\<forall>x ([F]x \<rightarrow> \<box>[F]x)\<close>
    using "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2)] by blast
  AOT_hence 0: \<open>\<forall>x \<box>([F]x \<rightarrow> \<box>[F]x)\<close>
    using CBF[THEN "\<rightarrow>E"] by blast
  AOT_hence 1: \<open>\<forall>x ([F]x \<rightarrow> \<box>[F]x)\<close>
    using A "qml:2"[axiom_inst, THEN "\<rightarrow>E"] by blast
  AOT_have act_F_den: \<open>[\<lambda>z \<^bold>\<A>[F]z]\<down>\<close>
    by "cqt:2"
  AOT_show \<open>F \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[F]z]\<close>
  proof (safe intro!: "apE-eqE:1"[unvarify G, THEN "\<rightarrow>E"] eqD[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I"
                      "cqt:2" act_F_den GEN "\<rightarrow>I" "\<equiv>I")
    fix u
    AOT_assume \<open>[F]u\<close>
    AOT_hence \<open>\<box>[F]u\<close>
      using 1[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
    AOT_hence act_F_u: \<open>\<^bold>\<A>[F]u\<close>
      by (metis "nec-imp-act" "\<rightarrow>E")
    AOT_show \<open>[\<lambda>z \<^bold>\<A>[F]z]u\<close>
      by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" act_F_u)
  next
    fix u
    AOT_assume \<open>[\<lambda>z \<^bold>\<A>[F]z]u\<close>
    AOT_hence \<open>\<^bold>\<A>[F]u\<close>
      by (rule "\<beta>\<rightarrow>C"(1))
    AOT_thus \<open>[F]u\<close>
      using 0[THEN "\<forall>E"(2)]
      by (metis "\<equiv>E"(1) "sc-eq-fur:2" "\<rightarrow>E")
  qed
qed


AOT_theorem "approx-nec:2":
  \<open>F \<approx>\<^sub>D G \<equiv> \<forall>H ([\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>D F \<equiv> [\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>D G)\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume 0: \<open>F \<approx>\<^sub>D G\<close>
  AOT_assume 0: \<open>F \<approx>\<^sub>D G\<close>
  AOT_hence \<open>\<forall>H (H \<approx>\<^sub>D F \<equiv> H \<approx>\<^sub>D G)\<close>
    using "eq-part:4"[THEN "\<equiv>E"(1), OF 0] by blast
  AOT_have \<open>[\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>D F \<equiv> [\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>D G\<close> for H
    by (rule "\<forall>E"(1)[OF "eq-part:4"[THEN "\<equiv>E"(1), OF 0]]) "cqt:2"
  AOT_thus \<open>\<forall>H ([\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>D F \<equiv> [\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>D G)\<close>
    by (rule GEN)
next
  AOT_assume 0: \<open>\<forall>H ([\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>D F \<equiv> [\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>D G)\<close>
  AOT_obtain H where \<open>Rigidifies(H,F)\<close>
    using "rigid-der:3" "\<exists>E" by metis
  AOT_hence H: \<open>Rigid(H) & \<forall>x ([H]x \<equiv> [F]x)\<close>
    using "df-rigid-rel:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_have H_rigid: \<open>\<box>\<forall>x ([H]x \<rightarrow> \<box>[H]x)\<close>
    using H[THEN "&E"(1), THEN "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2)].
  AOT_hence \<open>\<forall>x \<box>([H]x \<rightarrow> \<box>[H]x)\<close>
    using "CBF" "vdash-properties:10" by blast
  AOT_hence \<open>\<box>([H]x \<rightarrow> \<box>[H]x)\<close> for x using "\<forall>E"(2) by blast
  AOT_hence rigid: \<open>[H]x \<equiv> \<^bold>\<A>[H]x\<close> for x
     by (metis "\<equiv>E"(6) "oth-class-taut:3:a" "sc-eq-fur:2" "\<rightarrow>E")
  AOT_have \<open>H \<equiv>\<^sub>D F\<close>
  proof (safe intro!: eqD[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" GEN "\<rightarrow>I")
    AOT_show \<open>[H]u \<equiv> [F]u\<close> for u using H[THEN "&E"(2)] "\<forall>E"(2) by fast
  qed
  AOT_hence \<open>H \<approx>\<^sub>D F\<close>
    by (rule "apE-eqE:2"[THEN "\<rightarrow>E", OF "&I", rotated])
       (simp add: "eq-part:1")
  AOT_hence F_approx_H: \<open>F \<approx>\<^sub>D H\<close>
    by (metis "eq-part:2" "\<rightarrow>E")
  moreover AOT_have H_eq_act_H: \<open>H \<equiv>\<^sub>D [\<lambda>z \<^bold>\<A>[H]z]\<close>
  proof (safe intro!: eqD[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" GEN "\<rightarrow>I")
    AOT_show \<open>[H]u \<equiv> [\<lambda>z \<^bold>\<A>[H]z]u\<close> for u
      apply (AOT_subst \<open>[\<lambda>z \<^bold>\<A>[H]z]u\<close> \<open>\<^bold>\<A>[H]u\<close>)
       apply (rule "beta-C-meta"[THEN "\<rightarrow>E"])
       apply "cqt:2[lambda]"
      using rigid by blast
  qed
  AOT_have a: \<open>F \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[H]z]\<close>
    apply (rule "apE-eqE:2"[unvarify H, THEN "\<rightarrow>E"])
     apply "cqt:2[lambda]"
    using F_approx_H H_eq_act_H "&I" by blast
  AOT_hence \<open>[\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>D F\<close>
    apply (rule "eq-part:2"[unvarify G, THEN "\<rightarrow>E", rotated])
    by "cqt:2[lambda]"
  AOT_hence b: \<open>[\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>D G\<close>
    by (rule 0[THEN "\<forall>E"(1), THEN "\<equiv>E"(1), rotated]) "cqt:2" 
  AOT_show \<open>F \<approx>\<^sub>D G\<close>
    by (rule "eq-part:3"[unvarify G, THEN "\<rightarrow>E", rotated, OF "&I", OF a, OF b])
       "cqt:2"
qed

AOT_theorem "approx-nec:3":
  \<open>(Rigid(F) & Rigid(G)) \<rightarrow> \<box>(F \<approx>\<^sub>D G \<rightarrow> \<box>F \<approx>\<^sub>D G)\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>Rigid(F) & Rigid(G)\<close>
  AOT_hence \<open>\<box>\<forall>x([F]x \<rightarrow> \<box>[F]x)\<close> and \<open>\<box>\<forall>x([G]x \<rightarrow> \<box>[G]x)\<close>
    using "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2)] "&E" by blast+
  AOT_hence \<open>\<box>(\<box>\<forall>x([F]x \<rightarrow> \<box>[F]x) & \<box>\<forall>x([G]x \<rightarrow> \<box>[G]x))\<close>
    using "KBasic:3" "4" "&I" "\<equiv>E"(2) "vdash-properties:10" by meson
  moreover AOT_have \<open>\<box>(\<box>\<forall>x([F]x \<rightarrow> \<box>[F]x) & \<box>\<forall>x([G]x \<rightarrow> \<box>[G]x)) \<rightarrow>
                     \<box>(F \<approx>\<^sub>D G \<rightarrow> \<box>F \<approx>\<^sub>D G)\<close>
  proof(rule RM; rule "\<rightarrow>I"; rule "\<rightarrow>I")
    AOT_modally_strict {
      AOT_assume \<open>\<box>\<forall>x([F]x \<rightarrow> \<box>[F]x) & \<box>\<forall>x([G]x \<rightarrow> \<box>[G]x)\<close>
      AOT_hence \<open>\<box>\<forall>x([F]x \<rightarrow> \<box>[F]x)\<close> and \<open>\<box>\<forall>x([G]x \<rightarrow> \<box>[G]x)\<close>
        using "&E" by blast+
      AOT_hence \<open>\<forall>x\<box>([F]x \<rightarrow> \<box>[F]x)\<close> and \<open>\<forall>x\<box>([G]x \<rightarrow> \<box>[G]x)\<close>
        using CBF[THEN "\<rightarrow>E"] by blast+
      AOT_hence F_nec: \<open>\<box>([F]x \<rightarrow> \<box>[F]x)\<close>
            and G_nec: \<open>\<box>([G]x \<rightarrow> \<box>[G]x)\<close> for x
        using "\<forall>E"(2) by blast+
      AOT_assume \<open>F \<approx>\<^sub>D G\<close>
      AOT_hence \<open>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
        by (metis "\<equiv>\<^sub>d\<^sub>fE" "equi:3")
      then AOT_obtain R where \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
        using "\<exists>E"[rotated] by blast
      AOT_hence C1: \<open>\<forall>u ([F]u \<rightarrow> \<exists>!\<^sub>Dv ([G]v & [R]uv))\<close>
            and C2: \<open>\<forall>v ([G]v \<rightarrow> \<exists>!\<^sub>Du ([F]u & [R]uv))\<close>
        using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
      AOT_obtain R' where \<open>Rigidifies(R', R)\<close>
        using "rigid-der:3" "\<exists>E"[rotated] by blast
      AOT_hence 1: \<open>Rigid(R') & \<forall>x\<^sub>1...\<forall>x\<^sub>n ([R']x\<^sub>1...x\<^sub>n \<equiv> [R]x\<^sub>1...x\<^sub>n)\<close>
        using "df-rigid-rel:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
      AOT_hence \<open>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([R']x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[R']x\<^sub>1...x\<^sub>n)\<close>
        using "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
      AOT_hence \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n (\<diamond>[R']x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[R']x\<^sub>1...x\<^sub>n)\<close>
        using "\<equiv>E"(1) "rigid-rel-thms:1" by blast
      AOT_hence D: \<open>\<forall>x\<^sub>1\<forall>x\<^sub>2 (\<diamond>[R']x\<^sub>1x\<^sub>2 \<rightarrow> \<box>[R']x\<^sub>1x\<^sub>2)\<close>
        using tuple_forall[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
      AOT_have E: \<open>\<forall>x\<^sub>1\<forall>x\<^sub>2 ([R']x\<^sub>1x\<^sub>2 \<equiv> [R]x\<^sub>1x\<^sub>2)\<close>
        using tuple_forall[THEN "\<equiv>\<^sub>d\<^sub>fE", OF 1[THEN "&E"(2)]] by blast
      AOT_have \<open>\<forall>u \<box>([F]u \<rightarrow> \<exists>!\<^sub>Dv ([G]v & [R']uv))\<close>
           and \<open>\<forall>v \<box>([G]v \<rightarrow> \<exists>!\<^sub>Du ([F]u & [R']uv))\<close>
      proof (safe intro!: GEN "\<rightarrow>I")
        fix u
        AOT_show \<open>\<box>([F]u \<rightarrow> \<exists>!\<^sub>Dv ([G]v & [R']uv))\<close>
        proof (rule "raa-cor:1")
          AOT_assume \<open>\<not>\<box>([F]u \<rightarrow> \<exists>!\<^sub>Dv ([G]v & [R']uv))\<close>
          AOT_hence 1: \<open>\<diamond>\<not>([F]u \<rightarrow> \<exists>!\<^sub>Dv ([G]v & [R']uv))\<close>
            using "KBasic:11" "\<equiv>E"(1) by blast
          AOT_have \<open>\<diamond>([F]u & \<not>\<exists>!\<^sub>Dv ([G]v & [R']uv))\<close>
            apply (AOT_subst \<open>[F]u & \<not>\<exists>!\<^sub>Dv ([G]v & [R']uv)\<close>
                             \<open>\<not>([F]u \<rightarrow> \<exists>!\<^sub>Dv ([G]v & [R']uv))\<close>)
             apply (meson "\<equiv>E"(6) "oth-class-taut:1:b" "oth-class-taut:3:a")
            by (fact 1)
          AOT_hence A: \<open>\<diamond>[F]u & \<diamond>\<not>\<exists>!\<^sub>Dv ([G]v & [R']uv)\<close>
            using "KBasic2:3" "\<rightarrow>E" by blast
          AOT_hence \<open>\<box>[F]u\<close>
            using F_nec "&E"(1) "\<equiv>E"(1) "sc-eq-box-box:1" "\<rightarrow>E" by blast
          AOT_hence \<open>[F]u\<close>
            by (metis "qml:2"[axiom_inst] "\<rightarrow>E")
          AOT_hence \<open>\<exists>!\<^sub>Dv ([G]v & [R]uv)\<close>
            using C1[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
          AOT_hence \<open>\<exists>v ([G]v & [R]uv & \<forall>v' ([G]v' & [R]uv' \<rightarrow> v' =\<^sub>D v))\<close>
            using "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by auto
          then AOT_obtain a where
            a_prop: \<open>([G]a & [R]ua & \<forall>v' ([G]v' & [R]uv' \<rightarrow> v' =\<^sub>D a))\<close>
            using "\<exists>E"[rotated] by blast
          AOT_have \<open>\<exists>v \<box>([G]v & [R']uv & \<forall>v' ([G]v' & [R']uv' \<rightarrow> v' =\<^sub>D v))\<close>
          proof(safe intro!: "\<exists>I"(2)[where \<beta>=a] "&I" a_prop[THEN "&E"(1)]
                             "KBasic:3"[THEN "\<equiv>E"(2)])
            AOT_show \<open>\<box>[G]a\<close>
              using a_prop[THEN "&E"(1), THEN "&E"(1)]
              by (metis G_nec "qml:2"[axiom_inst] "\<rightarrow>E")
          next
            AOT_show \<open>\<box>[R']ua\<close>
              using D[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"]
                    E[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<equiv>E"(2),
                      OF a_prop[THEN "&E"(1), THEN "&E"(2)]]
              by (metis "T\<diamond>" "\<rightarrow>E")
          next
            AOT_have \<open>\<forall>v' \<box>([G]v' & [R']uv' \<rightarrow> v' =\<^sub>D a)\<close>
            proof (rule GEN; rule "raa-cor:1")
              fix v'
              AOT_assume \<open>\<not>\<box>([G]v' & [R']uv' \<rightarrow> v' =\<^sub>D a)\<close>
              AOT_hence \<open>\<diamond>\<not>([G]v' & [R']uv' \<rightarrow> v' =\<^sub>D a)\<close>
                by (metis "KBasic:11" "\<equiv>E"(1))
              AOT_hence \<open>\<diamond>([G]v' & [R']uv' & \<not>v' =\<^sub>D a)\<close>
                by (AOT_subst \<open>[G]v' & [R']uv' & \<not>v' =\<^sub>D a\<close>
                              \<open>\<not>([G]v' & [R']uv' \<rightarrow> v' =\<^sub>D a)\<close>)
                   (meson "\<equiv>E"(6) "oth-class-taut:1:b" "oth-class-taut:3:a")
              AOT_hence 1: \<open>\<diamond>[G]v'\<close> and 2: \<open>\<diamond>[R']uv'\<close> and 3: \<open>\<diamond>\<not>v' =\<^sub>D a\<close>
                using "KBasic2:3"[THEN "\<rightarrow>E", THEN "&E"(1)]
                      "KBasic2:3"[THEN "\<rightarrow>E", THEN "&E"(2)] by blast+
              AOT_have Gv': \<open>[G]v'\<close> using G_nec 1
                by (meson "B\<diamond>" "KBasic:13" "\<rightarrow>E")
              AOT_have \<open>\<box>[R']uv'\<close>
                using 2 D[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
              AOT_hence R'uv': \<open>[R']uv'\<close>
                by (metis "B\<diamond>" "T\<diamond>" "\<rightarrow>E") 
              AOT_hence \<open>[R]uv'\<close>
                using E[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<equiv>E"(1)] by blast
              AOT_hence \<open>v' =\<^sub>D a\<close>
                using a_prop[THEN "&E"(2), THEN "\<forall>E"(2),
                             THEN "\<rightarrow>E", OF "&I", OF Gv'] by blast
              AOT_hence \<open>\<box>(v' =\<^sub>D a)\<close>
                by (metis "id-nec4:1" "intro-elim:3:d" "raa-cor:3")
              moreover AOT_have \<open>\<not>\<box>(v' =\<^sub>D a)\<close>
                using 3 "KBasic:11" "\<equiv>E"(2) by blast
              ultimately AOT_show \<open>\<box>(v' =\<^sub>D a) & \<not>\<box>(v' =\<^sub>D a)\<close>
                using "&I" by blast
            qed
            AOT_thus \<open>\<box>\<forall>v'([G]v' & [R']uv' \<rightarrow> v' =\<^sub>D a)\<close>
              using "BF" "\<rightarrow>E" by fast
          qed
          AOT_hence \<open>\<box>\<exists>v ([G]v & [R']uv & \<forall>v' ([G]v' & [R']uv' \<rightarrow> v' =\<^sub>D v))\<close>
            using "Buridan" "\<rightarrow>E" by fast
          AOT_hence \<open>\<box>\<exists>!\<^sub>Dv ([G]v & [R']uv)\<close>
            by (AOT_subst_def "equi:1")
          moreover AOT_have \<open>\<not>\<box>\<exists>!\<^sub>Dv ([G]v & [R']uv)\<close>
            using A[THEN "&E"(2)] "KBasic:11"[THEN "\<equiv>E"(2)] by blast
          ultimately AOT_show \<open>\<box>\<exists>!\<^sub>Dv ([G]v & [R']uv) & \<not>\<box>\<exists>!\<^sub>Dv ([G]v & [R']uv)\<close>
            by (rule "&I")
        qed
      next
        fix v
        AOT_show \<open>\<box>([G]v \<rightarrow> \<exists>!\<^sub>Du ([F]u & [R']uv))\<close>
        proof (rule "raa-cor:1")
          AOT_assume \<open>\<not>\<box>([G]v \<rightarrow> \<exists>!\<^sub>Du ([F]u & [R']uv))\<close>
          AOT_hence 1: \<open>\<diamond>\<not>([G]v \<rightarrow> \<exists>!\<^sub>Du ([F]u & [R']uv))\<close>
            using "KBasic:11" "\<equiv>E"(1) by blast
          AOT_hence \<open>\<diamond>([G]v & \<not>\<exists>!\<^sub>Du ([F]u & [R']uv))\<close>
            by (AOT_subst \<open>[G]v & \<not>\<exists>!\<^sub>Du ([F]u & [R']uv)\<close>
                          \<open>\<not>([G]v \<rightarrow> \<exists>!\<^sub>Du ([F]u & [R']uv))\<close>)
               (meson "\<equiv>E"(6) "oth-class-taut:1:b" "oth-class-taut:3:a")
          AOT_hence A: \<open>\<diamond>[G]v & \<diamond>\<not>\<exists>!\<^sub>Du ([F]u & [R']uv)\<close>
            using "KBasic2:3" "\<rightarrow>E" by blast
          AOT_hence \<open>\<box>[G]v\<close>
            using G_nec "&E"(1) "\<equiv>E"(1) "sc-eq-box-box:1" "\<rightarrow>E" by blast
          AOT_hence \<open>[G]v\<close> by (metis "qml:2"[axiom_inst] "\<rightarrow>E")
          AOT_hence \<open>\<exists>!\<^sub>Du ([F]u & [R]uv)\<close>
            using C2[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
          AOT_hence \<open>\<exists>u ([F]u & [R]uv & \<forall>u' ([F]u' & [R]u'v \<rightarrow> u' =\<^sub>D u))\<close>
            using "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by auto
          then AOT_obtain a where
              a_prop: \<open>([F]a & [R]av & \<forall>u' ([F]u' & [R]u'v \<rightarrow> u' =\<^sub>D a))\<close>
            using "\<exists>E"[rotated] by blast
          AOT_have \<open>\<exists>u \<box>([F]u & [R']uv & \<forall>u' ([F]u' & [R']u'v \<rightarrow> u' =\<^sub>D u))\<close>
          proof(safe intro!: "\<exists>I"(2)[where \<beta>=a] "&I"
                             "KBasic:3"[THEN "\<equiv>E"(2)])
            AOT_show \<open>\<box>[F]a\<close>
              using a_prop[THEN "&E"(1), THEN "&E"(1)]
              by (metis F_nec "qml:2"[axiom_inst] "\<rightarrow>E")
          next
            AOT_show \<open>\<box>[R']av\<close>
              using D[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"]
                    E[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<equiv>E"(2),
                      OF a_prop[THEN "&E"(1), THEN "&E"(2)]]
              by (metis "T\<diamond>" "\<rightarrow>E")
          next
            AOT_have \<open>\<forall>u' \<box>([F]u' & [R']u'v \<rightarrow> u' =\<^sub>D a)\<close>
            proof (rule GEN; rule "raa-cor:1")
              fix u'
              AOT_assume \<open>\<not>\<box>([F]u' & [R']u'v \<rightarrow> u' =\<^sub>D a)\<close>
              AOT_hence \<open>\<diamond>\<not>([F]u' & [R']u'v \<rightarrow> u' =\<^sub>D a)\<close>
                by (metis "KBasic:11" "\<equiv>E"(1))
              AOT_hence \<open>\<diamond>([F]u' & [R']u'v & \<not>u' =\<^sub>D a)\<close>
                by (AOT_subst \<open>[F]u' & [R']u'v & \<not>u' =\<^sub>D a\<close>
                              \<open>\<not>([F]u' & [R']u'v \<rightarrow> u' =\<^sub>D a)\<close>)
                   (meson "\<equiv>E"(6) "oth-class-taut:1:b" "oth-class-taut:3:a")
              AOT_hence 1: \<open>\<diamond>[F]u'\<close> and 2: \<open>\<diamond>[R']u'v\<close> and 3: \<open>\<diamond>\<not>u' =\<^sub>D a\<close>
                using "KBasic2:3"[THEN "\<rightarrow>E", THEN "&E"(1)]
                      "KBasic2:3"[THEN "\<rightarrow>E", THEN "&E"(2)] by blast+
              AOT_have Fu': \<open>[F]u'\<close> using F_nec 1
                by (meson "B\<diamond>" "KBasic:13" "\<rightarrow>E")
              AOT_have \<open>\<box>[R']u'v\<close>
                using 2 D[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
              AOT_hence R'u'v: \<open>[R']u'v\<close>
                by (metis "B\<diamond>" "T\<diamond>" "\<rightarrow>E") 
              AOT_hence \<open>[R]u'v\<close>
                using E[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<equiv>E"(1)] by blast
              AOT_hence \<open>u' =\<^sub>D a\<close>
                using a_prop[THEN "&E"(2), THEN "\<forall>E"(2),
                             THEN "\<rightarrow>E", OF "&I", OF Fu'] by blast
              AOT_hence \<open>\<box>(u' =\<^sub>D a)\<close>
                by (metis "id-nec4:1" "\<equiv>E"(4) "raa-cor:3")
              moreover AOT_have \<open>\<not>\<box>(u' =\<^sub>D a)\<close>
                using 3 "KBasic:11" "\<equiv>E"(2) by blast
              ultimately AOT_show \<open>\<box>(u' =\<^sub>D a) & \<not>\<box>(u' =\<^sub>D a)\<close>
                using "&I" by blast
            qed
            AOT_thus \<open>\<box>\<forall>u'([F]u' & [R']u'v \<rightarrow> u' =\<^sub>D a)\<close>
              using "BF" "\<rightarrow>E" by fast
          qed
          AOT_hence 1: \<open>\<box>\<exists>u ([F]u & [R']uv & \<forall>u' ([F]u' & [R']u'v \<rightarrow> u' =\<^sub>D u))\<close>
            using "Buridan" "\<rightarrow>E" by fast
          AOT_hence \<open>\<box>\<exists>!\<^sub>Du ([F]u & [R']uv)\<close>
            by (AOT_subst_def "equi:1")
          moreover AOT_have \<open>\<not>\<box>\<exists>!\<^sub>Du ([F]u & [R']uv)\<close>
            using A[THEN "&E"(2)] "KBasic:11"[THEN "\<equiv>E"(2)] by blast
          ultimately AOT_show \<open>\<box>\<exists>!\<^sub>Du ([F]u & [R']uv) & \<not>\<box>\<exists>!\<^sub>Du ([F]u & [R']uv)\<close>
            by (rule "&I")
        qed
      qed
      AOT_hence \<open>\<box>\<forall>u ([F]u \<rightarrow> \<exists>!\<^sub>Dv ([G]v & [R']uv))\<close>
            and \<open>\<box>\<forall>v ([G]v \<rightarrow> \<exists>!\<^sub>Du ([F]u & [R']uv))\<close>
        using "BF"[THEN "\<rightarrow>E"] by fast+
      moreover AOT_have \<open>\<box>[R']\<down>\<close> and \<open>\<box>[F]\<down>\<close> and \<open>\<box>[G]\<down>\<close>
        by (simp_all add: "ex:2:a")
      ultimately AOT_have \<open>\<box>([R']\<down> & [F]\<down> & [G]\<down> & \<forall>u ([F]u \<rightarrow> \<exists>!\<^sub>Dv ([G]v & [R']uv)) &
                                                   \<forall>v ([G]v \<rightarrow> \<exists>!\<^sub>Du ([F]u & [R']uv)))\<close>
        using "KBasic:3" "&I" "\<equiv>E"(2) by meson
      AOT_hence \<open>\<box>R' |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
        by (AOT_subst_def "equi:2")
      AOT_hence \<open>\<exists>R \<box>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
        by (rule "\<exists>I"(2))
      AOT_hence \<open>\<box>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
        by (metis Buridan "\<rightarrow>E")
      AOT_thus \<open>\<box>F \<approx>\<^sub>D G\<close>
        by (AOT_subst_def "equi:3")
    }
  qed
  ultimately AOT_show \<open>\<box>(F \<approx>\<^sub>D G \<rightarrow> \<box>F \<approx>\<^sub>D G)\<close>
    using "\<rightarrow>E" by blast
qed


AOT_define numbers :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>Numbers'(_,_')\<close>)
  \<open>Numbers(x,G) \<equiv>\<^sub>d\<^sub>f A!x & G\<down> & \<forall>F(x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>

AOT_theorem "numbers[den]":
  \<open>\<Pi>\<down> \<rightarrow> (Numbers(\<kappa>, \<Pi>) \<equiv> A!\<kappa> & \<forall>F(\<kappa>[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D \<Pi>))\<close>
  apply (safe intro!: numbers[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "\<equiv>I" "\<rightarrow>I" "cqt:2"
               dest!: numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"])
  using "&E" by blast+

AOT_theorem "num-tran:1":
  \<open>G \<approx>\<^sub>D H \<rightarrow> (Numbers(x, G) \<equiv> Numbers(x, H))\<close>
proof (safe intro!: "\<rightarrow>I" "\<equiv>I")
  AOT_assume 0: \<open>G \<approx>\<^sub>D H\<close>
  AOT_assume \<open>Numbers(x, G)\<close>
  AOT_hence Ax: \<open>A!x\<close> and \<theta>: \<open>\<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>
    using numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_show \<open>Numbers(x, H)\<close>
  proof(safe intro!: numbers[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" Ax "cqt:2" GEN)
    fix F
    AOT_have \<open>x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G\<close>
      using \<theta>[THEN "\<forall>E"(2)].
    also AOT_have \<open>\<dots> \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D H\<close>
      using 0 "approx-nec:2"[THEN "\<equiv>E"(1), THEN "\<forall>E"(2)] by metis
    finally AOT_show \<open>x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D H\<close>.
  qed
next
  AOT_assume \<open>G \<approx>\<^sub>D H\<close>
  AOT_hence 0: \<open>H \<approx>\<^sub>D G\<close>
    by (metis "eq-part:2" "\<rightarrow>E")
  AOT_assume \<open>Numbers(x, H)\<close>
  AOT_hence Ax: \<open>A!x\<close> and \<theta>: \<open>\<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D H)\<close>
    using numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_show \<open>Numbers(x, G)\<close>
  proof(safe intro!: numbers[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" Ax "cqt:2"  GEN)
    fix F
    AOT_have \<open>x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D H\<close>
      using \<theta>[THEN "\<forall>E"(2)].
    also AOT_have \<open>\<dots> \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G\<close>
      using 0 "approx-nec:2"[THEN "\<equiv>E"(1), THEN "\<forall>E"(2)] by metis
    finally AOT_show \<open>x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G\<close>.
  qed
qed

AOT_theorem "num-tran:2":
  \<open>(Numbers(x, G) & Numbers(x,H)) \<rightarrow> G \<approx>\<^sub>D H\<close>
proof (rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume \<open>Numbers(x,G)\<close>
  AOT_hence \<open>\<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>
    using numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_hence 1: \<open>x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G\<close> for F
    using "\<forall>E"(2) by blast
  AOT_assume \<open>Numbers(x,H)\<close>
  AOT_hence \<open>\<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D H)\<close>
    using numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_hence \<open>x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D H\<close> for F
    using "\<forall>E"(2) by blast
  AOT_hence \<open>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D H\<close> for F
    by (metis "1" "\<equiv>E"(6))
  AOT_thus \<open>G \<approx>\<^sub>D H\<close>
    using "approx-nec:2"[THEN "\<equiv>E"(2), OF GEN] by blast
qed

AOT_theorem "num-tran:3":
  \<open>G \<equiv>\<^sub>D H \<rightarrow> (Numbers(x, G) \<equiv> Numbers(x, H))\<close>
  using "apE-eqE:1" "Hypothetical Syllogism" "num-tran:1" by blast

AOT_theorem "pre-Hume":
  \<open>(Numbers(x,G) & Numbers(y,H)) \<rightarrow> (x = y \<equiv> G \<approx>\<^sub>D H)\<close>
proof(safe intro!: "\<rightarrow>I" "\<equiv>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume \<open>Numbers(x, G)\<close>
  moreover AOT_assume \<open>x = y\<close>
  ultimately AOT_have \<open>Numbers(y, G)\<close> by (rule "rule=E")
  moreover AOT_assume \<open>Numbers(y, H)\<close>
  ultimately AOT_show \<open>G \<approx>\<^sub>D H\<close> using "num-tran:2" "\<rightarrow>E" "&I" by blast
next
  AOT_assume \<open>Numbers(x, G)\<close>
  AOT_hence Ax: \<open>A!x\<close> and xF: \<open>\<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>
    using numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_assume \<open>Numbers(y, H)\<close>
  AOT_hence Ay: \<open>A!y\<close> and yF: \<open>\<forall>F (y[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D H)\<close>
    using numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_assume G_approx_H: \<open>G \<approx>\<^sub>D H\<close>
  AOT_show \<open>x = y\<close>
  proof(rule "ab-obey:1"[THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF "&I", OF Ax, OF Ay]; rule GEN)
    fix F
    AOT_have \<open>x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G\<close>
      using xF[THEN "\<forall>E"(2)].
    also AOT_have \<open>\<dots> \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D H\<close>
      using "approx-nec:2"[THEN "\<equiv>E"(1), OF G_approx_H, THEN "\<forall>E"(2)].
    also AOT_have \<open>\<dots> \<equiv> y[F]\<close>
      using yF[THEN "\<forall>E"(2), symmetric].
    finally AOT_show \<open>x[F] \<equiv> y[F]\<close>.
  qed
qed


AOT_theorem "two-num-not":
  \<open>\<exists>x\<exists>G\<exists>H(Numbers(x,G) & Numbers(x, H) & \<not>G \<equiv>\<^sub>D H)\<close>
proof -
  AOT_have eqE_den: \<open>[\<lambda>x x =\<^sub>D y]\<down>\<close> for y by "cqt:2"
  AOT_obtain c where Oc: \<open>O!c\<close>
    by (metis "instantiation" "o-objects-exist:1" "qml:2" "vdash-properties:10" "vdash-properties:1[2]")
  AOT_obtain d where \<open>A!d\<close>
    by (metis "instantiation" "o-objects-exist:2" "qml:2" "vdash-properties:10" "vdash-properties:1[2]")
  AOT_hence notOd: \<open>\<not>O!d\<close>
    by (meson "intro-elim:3:a" "oa-contingent:3")
  AOT_have not_c_eqE_d: \<open>\<not>c =\<^sub>D d\<close>
  proof(rule "raa-cor:2")
    AOT_assume \<open>c =\<^sub>D d\<close>
    AOT_hence \<open>\<forall>F([F]c \<equiv> [F]d)\<close>
      using "=D-simple:1"[THEN "\<equiv>E"(1), THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"]] by blast
    AOT_hence \<open>O!d\<close> using "\<forall>E"(1) "oa-exist:1" Oc "\<equiv>E" by blast
    AOT_thus \<open>O!d & \<not>O!d\<close> using notOd "&I" by blast
  qed
  AOT_have \<open>\<exists>x (A!x & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D [\<lambda>x x =\<^sub>D c]))\<close>
    by (simp add: "A-objects"[axiom_inst])
  then AOT_obtain a where a_prop: \<open>A!a & \<forall>F (a[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D [\<lambda>x x =\<^sub>D c])\<close>
    using "\<exists>E"[rotated] by blast
  AOT_have \<open>\<exists>x (A!x & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D [\<lambda>x x =\<^sub>D d]))\<close>
    by (simp add: "A-objects" "vdash-properties:1[2]")
  then AOT_obtain b where b_prop: \<open>A!b & \<forall>F (b[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D [\<lambda>x x =\<^sub>D d])\<close>
    using "\<exists>E"[rotated] by blast
  AOT_have num_a_eq_c: \<open>Numbers(a, [\<lambda>x x =\<^sub>D c])\<close>
    by (safe intro!: numbers[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" a_prop[THEN "&E"(1)]
                     a_prop[THEN "&E"(2)]) "cqt:2"
  moreover AOT_have num_b_eq_d: \<open>Numbers(b, [\<lambda>x x =\<^sub>D d])\<close>
    by (safe intro!: numbers[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" b_prop[THEN "&E"(1)]
                     b_prop[THEN "&E"(2)]) "cqt:2"
  moreover AOT_have \<open>[\<lambda>x x =\<^sub>D c] \<approx>\<^sub>D [\<lambda>x x =\<^sub>D d]\<close>
  proof (rule "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
    let ?R = \<open>\<guillemotleft>[\<lambda>xy (x =\<^sub>D c & y =\<^sub>D d)]\<guillemotright>\<close>
    AOT_have Rcd: \<open>[\<guillemotleft>?R\<guillemotright>]cd\<close>
      by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" prod_denotesI
                       "disc=Dequiv:1")
    AOT_show \<open>\<exists>R R |: [\<lambda>x x =\<^sub>D c] \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D [\<lambda>x x =\<^sub>D d]\<close>
    proof (safe intro!: "\<exists>I"(1)[where \<tau>=\<open>?R\<close>] "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I"
                        eqE_den GEN "\<rightarrow>I")
      AOT_show \<open>\<guillemotleft>?R\<guillemotright>\<down>\<close> by "cqt:2"
    next
      fix u
      AOT_assume \<open>[\<lambda>x x =\<^sub>D c]u\<close>
      AOT_hence u_eq_c: \<open>u =\<^sub>D c\<close>
        by (metis "\<beta>\<rightarrow>C"(1))
      AOT_show \<open>\<exists>!\<^sub>Dv ([\<lambda>x x =\<^sub>D d]v & [\<guillemotleft>?R\<guillemotright>]uv)\<close>
      proof (safe intro!: "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(2)[where \<beta>=d] "&I"
                          GEN "\<rightarrow>I")
        AOT_show \<open>[\<lambda>x x =\<^sub>D d]d\<close>
          by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "disc=Dequiv:1")
      next
        AOT_show \<open>[\<guillemotleft>?R\<guillemotright>]ud\<close>
          by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2" tuple_denotes[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" u_eq_c "disc=Dequiv:1")
      next
        fix v
        AOT_assume \<open>[\<lambda>x x =\<^sub>D d]v & [\<guillemotleft>?R\<guillemotright>]uv\<close>
        AOT_thus \<open>v =\<^sub>D d\<close>
          by (metis "\<beta>\<rightarrow>C"(1) "&E"(1))
      qed
    next
      fix v
      AOT_assume \<open>[\<lambda>x x =\<^sub>D d]v\<close>
      AOT_hence v_eq_d: \<open>v =\<^sub>D d\<close>
        by (metis "\<beta>\<rightarrow>C"(1))
      AOT_show \<open>\<exists>!\<^sub>Du ([\<lambda>x x =\<^sub>D c]u & [\<guillemotleft>?R\<guillemotright>]uv)\<close>
      proof (safe intro!: "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(2)[where \<beta>=c] "&I"
                          GEN "\<rightarrow>I")
        AOT_show \<open>[\<lambda>x x =\<^sub>D c]c\<close>
          by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "disc=Dequiv:1")
      next
        AOT_show \<open>[\<guillemotleft>?R\<guillemotright>]cv\<close>
          by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2" tuple_denotes[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" v_eq_d "disc=Dequiv:1")
      next
        fix u
        AOT_assume \<open>[\<lambda>x x =\<^sub>D c]u & [\<guillemotleft>?R\<guillemotright>]uv\<close>
        AOT_thus \<open>u =\<^sub>D c\<close>
          by (metis "\<beta>\<rightarrow>C"(1) "&E"(1))
      qed
    next
      AOT_show \<open>\<guillemotleft>?R\<guillemotright>\<down>\<close>
        by "cqt:2"
    qed
  qed
  ultimately AOT_have \<open>a = b\<close>
    using "pre-Hume"[unvarify G H, OF eqE_den, OF eqE_den, THEN "\<rightarrow>E",
                     OF "&I", THEN "\<equiv>E"(2)] by blast
  AOT_hence num_a_eq_d: \<open>Numbers(a, [\<lambda>x x =\<^sub>D d])\<close>
    using num_b_eq_d "rule=E" id_sym by fast
  AOT_have not_equiv: \<open>\<not>[\<lambda>x x =\<^sub>D c] \<equiv>\<^sub>D [\<lambda>x x =\<^sub>D d]\<close>
  proof (rule "raa-cor:2")
    AOT_assume \<open>[\<lambda>x x =\<^sub>D c] \<equiv>\<^sub>D [\<lambda>x x =\<^sub>D d]\<close>
    AOT_hence \<open>[\<lambda>x x =\<^sub>D c]c \<equiv> [\<lambda>x x =\<^sub>D d]c\<close>
      using eqD[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), THEN "\<forall>E"(2)] by blast
    moreover AOT_have \<open>[\<lambda>x x =\<^sub>D c]c\<close>
      by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "disc=Dequiv:1")
    ultimately AOT_have \<open>[\<lambda>x x =\<^sub>D d]c\<close>
      using "\<equiv>E"(1) by blast
    AOT_hence \<open>c =\<^sub>D d\<close>
      by (rule "\<beta>\<rightarrow>C"(1))
    AOT_thus \<open>c =\<^sub>D d & \<not>c =\<^sub>D d\<close>
      using not_c_eqE_d "&I" by blast
  qed
  AOT_show \<open>\<exists>x \<exists>G \<exists>H (Numbers(x,G) & Numbers(x,H) & \<not>G \<equiv>\<^sub>D H)\<close>
    apply (rule "\<exists>I"(2)[where \<beta>=a])
    apply (rule "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>[\<lambda>x x =\<^sub>D c]\<guillemotright>\<close>])
     apply (rule "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>[\<lambda>x x =\<^sub>D d]\<guillemotright>\<close>])
    by (safe intro!: eqE_den "&I" num_a_eq_c num_a_eq_d not_equiv)
qed

AOT_theorem "num:1": \<open>\<exists>x Numbers(x,G)\<close>
  by (AOT_subst \<open>Numbers(x,G)\<close> \<open>[A!]x & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close> for: x)
     (auto simp: "numbers[den]"[THEN "\<rightarrow>E", OF "cqt:2[const_var]"[axiom_inst]]
                 "A-objects"[axiom_inst])

AOT_theorem "num:2": \<open>\<exists>!x Numbers(x,G)\<close>
  by (AOT_subst \<open>Numbers(x,G)\<close> \<open>[A!]x & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close> for: x)
     (auto simp: "numbers[den]"[THEN "\<rightarrow>E", OF "cqt:2[const_var]"[axiom_inst]]
                 "A-objects!")

AOT_theorem "num-cont:1":
  \<open>\<exists>x\<exists>G(Numbers(x, G) & \<not>\<box>Numbers(x, G))\<close>
proof -
  AOT_have \<open>\<exists>F\<exists>G \<diamond>([\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G & \<diamond>\<not>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>
    using "approx-cont:2".
  then AOT_obtain F where \<open>\<exists>G \<diamond>([\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G & \<diamond>\<not>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>
    using "\<exists>E"[rotated] by blast
  then AOT_obtain G where \<open>\<diamond>([\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G & \<diamond>\<not>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<theta>: \<open>\<diamond>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G\<close> and \<zeta>: \<open>\<diamond>\<not>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G\<close>
    using "KBasic2:3"[THEN "\<rightarrow>E"] "&E" "4\<diamond>"[THEN "\<rightarrow>E"] by blast+
  AOT_obtain a where \<open>Numbers(a, G)\<close>
    using "num:1" "\<exists>E"[rotated] by blast
  moreover AOT_have \<open>\<not>\<box>Numbers(a, G)\<close>
  proof (rule "raa-cor:2")
    AOT_assume \<open>\<box>Numbers(a, G)\<close>
    AOT_hence \<open>\<box>([A!]a & G\<down> & \<forall>F (a[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G))\<close>
      by (AOT_subst_def (reverse) numbers)
    AOT_hence \<open>\<box>A!a\<close> and \<open>\<box>\<forall>F (a[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>
      using "KBasic:3"[THEN "\<equiv>E"(1)] "&E" by blast+
    AOT_hence \<open>\<forall>F \<box>(a[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>
      using CBF[THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>\<box>(a[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>
      using "\<forall>E"(2) by blast
    AOT_hence A: \<open>\<box>(a[F] \<rightarrow> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>
          and B: \<open>\<box>([\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G \<rightarrow> a[F])\<close>
      using "KBasic:4"[THEN "\<equiv>E"(1)] "&E" by blast+
    AOT_have \<open>\<box>(\<not>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G \<rightarrow> \<not>a[F])\<close>
      apply (AOT_subst \<open>\<not>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G \<rightarrow> \<not>a[F]\<close> \<open>a[F] \<rightarrow> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G\<close>)
       using "\<equiv>I" "useful-tautologies:4" "useful-tautologies:5" apply presburger
       by (fact A)
     AOT_hence \<open>\<diamond>\<not>a[F]\<close>
       by (metis "KBasic:13" \<zeta> "\<rightarrow>E")
    AOT_hence \<open>\<not>a[F]\<close>
      by (metis "KBasic:11" "en-eq:2[1]" "\<equiv>E"(2) "\<equiv>E"(4))
    AOT_hence \<open>\<not>\<diamond>a[F]\<close>
      by (metis "en-eq:3[1]" "\<equiv>E"(4))
    moreover AOT_have \<open>\<diamond>a[F]\<close>
      by (meson B \<theta> "KBasic:13" "\<rightarrow>E")
    ultimately AOT_show \<open>\<diamond>a[F] & \<not>\<diamond>a[F]\<close>
      using "&I" by blast
  qed

  ultimately AOT_have \<open>Numbers(a, G) & \<not>\<box>Numbers(a, G)\<close>
    using "&I" by blast
  AOT_hence \<open>\<exists>G (Numbers(a, G) & \<not>\<box>Numbers(a, G))\<close>
    by (rule "\<exists>I")
  AOT_thus \<open>\<exists>x\<exists>G (Numbers(x, G) & \<not>\<box>Numbers(x, G))\<close>
    by (rule "\<exists>I")
qed

AOT_theorem "num-cont:2":
  \<open>Rigid(G) \<rightarrow> \<box>\<forall>x(Numbers(x,G) \<rightarrow> \<box>Numbers(x,G))\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>Rigid(G)\<close>
  AOT_hence \<open>\<box>\<forall>z([G]z \<rightarrow> \<box>[G]z)\<close>
    using "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2)] by blast
  AOT_hence \<open>\<box>\<box>\<forall>z([G]z \<rightarrow> \<box>[G]z)\<close> by (metis "S5Basic:6" "\<equiv>E"(1))
  moreover AOT_have \<open>\<box>\<box>\<forall>z([G]z \<rightarrow> \<box>[G]z) \<rightarrow> \<box>\<forall>x(Numbers(x,G) \<rightarrow> \<box>Numbers(x,G))\<close>
  proof(rule RM; safe intro!: "\<rightarrow>I" GEN)
    AOT_modally_strict {
      AOT_have act_den: \<open>[\<lambda>z \<^bold>\<A>[F]z]\<down>\<close> for F by "cqt:2[lambda]"
      fix x
      AOT_assume G_nec: \<open>\<box>\<forall>z([G]z \<rightarrow> \<box>[G]z)\<close>
      AOT_hence G_rigid: \<open>Rigid(G)\<close>
        using "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fI", OF "&I"] "cqt:2"
        by blast
      AOT_assume \<open>Numbers(x, G)\<close>
      AOT_hence \<open>[A!]x & G\<down> & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>
        using numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
      AOT_hence Ax: \<open>[A!]x\<close> and \<open>\<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>
        using "&E" by blast+
      AOT_hence \<open>x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G\<close> for F
        using "\<forall>E"(2) by blast
      moreover AOT_have \<open>\<box>([\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G \<rightarrow> \<box>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close> for F
        using "approx-nec:3"[unvarify F, OF act_den, THEN "\<rightarrow>E", OF "&I",
                             OF "actuallyF:2", OF G_rigid].
      moreover AOT_have \<open>\<box>(x[F] \<rightarrow> \<box>x[F])\<close> for F
        by (simp add: RN "pre-en-eq:1[1]")
      ultimately AOT_have \<open>\<box>(x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close> for F
        using "sc-eq-box-box:5" "\<rightarrow>E" "qml:2"[axiom_inst] "&I" by meson
      AOT_hence \<open>\<forall>F \<box>(x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>
        by (rule "\<forall>I")
      AOT_hence 1: \<open>\<box>\<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>
        using BF[THEN "\<rightarrow>E"] by fast
      AOT_have \<open>\<box>G\<down>\<close>
        by (simp add: "ex:2:a")
      moreover AOT_have \<open>\<box>[A!]x\<close>
        using Ax "oa-facts:2" "\<rightarrow>E" by blast
      ultimately AOT_have \<open>\<box>(A!x & G\<down>)\<close>
        by (metis "KBasic:3" "&I" "\<equiv>E"(2))
      AOT_hence \<open>\<box>(A!x & G\<down> & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G))\<close>
        using 1 "KBasic:3" "&I" "\<equiv>E"(2) by fast
      AOT_thus \<open>\<box>Numbers(x, G)\<close>
        by (AOT_subst_def numbers)
    }
  qed
  ultimately AOT_show \<open>\<box>\<forall>x(Numbers(x,G) \<rightarrow> \<box>Numbers(x,G))\<close>
    using "\<rightarrow>E" by blast
qed

AOT_theorem "num-cont:3":
  \<open>\<box>\<forall>x(Numbers(x, [\<lambda>z \<^bold>\<A>[G]z]) \<rightarrow> \<box>Numbers(x, [\<lambda>z \<^bold>\<A>[G]z]))\<close>
  by (rule "num-cont:2"[unvarify G, THEN "\<rightarrow>E"];
      ("cqt:2[lambda]" | rule "actuallyF:2"))


AOT_theorem "num-uniq": \<open>\<^bold>\<iota>x Numbers(x, G)\<down>\<close>
  using "\<equiv>E"(2) "A-Exists:2" "RA[2]" "num:2" by blast

AOT_define num :: \<open>\<tau> \<Rightarrow> \<kappa>\<^sub>s\<close> (\<open>#_\<close> [100] 100)
  "num-def:1": \<open>#G =\<^sub>d\<^sub>f \<^bold>\<iota>x Numbers(x, G)\<close>

AOT_theorem "num-def:2": \<open>#G\<down>\<close>
  using "num-def:1"[THEN "=\<^sub>d\<^sub>fI"(1)] "num-uniq" by simp

AOT_theorem "num-can:1":
  \<open>#G = \<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G))\<close>
proof -
  AOT_have \<open>\<box>\<forall>x(Numbers(x,G) \<equiv> [A!]x & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G))\<close>
    by (safe intro!: RN GEN "numbers[den]"[THEN "\<rightarrow>E"] "cqt:2")
  AOT_hence \<open>\<^bold>\<iota>x Numbers(x, G) = \<^bold>\<iota>x([A!]x & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G))\<close>
    using "num-uniq" "equiv-desc-eq:3"[THEN "\<rightarrow>E", OF "&I"] by auto
  thus ?thesis
    by (rule "=\<^sub>d\<^sub>fI"(1)[OF "num-def:1", OF "num-uniq"])
qed

AOT_theorem "num-can:2": \<open>#G = \<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> F \<approx>\<^sub>D G))\<close>
proof (rule id_trans[OF "num-can:1"]; rule "equiv-desc-eq:2"[THEN "\<rightarrow>E"];
       safe intro!: "&I" "A-descriptions" GEN "Act-Basic:5"[THEN "\<equiv>E"(2)]
                    "logic-actual-nec:3"[axiom_inst, THEN "\<equiv>E"(2)])
  AOT_have act_den: \<open>\<^bold>\<turnstile>\<^sub>\<box> [\<lambda>z \<^bold>\<A>[F]z]\<down>\<close> for F
    by "cqt:2"
  AOT_have "eq-part:3[terms]": \<open>\<^bold>\<turnstile>\<^sub>\<box> F \<approx>\<^sub>D G & F \<approx>\<^sub>D H \<rightarrow> G \<approx>\<^sub>D H\<close> for F G H
    by (metis "&I" "eq-part:2" "eq-part:3" "\<rightarrow>I" "&E" "\<rightarrow>E")
  fix x
  {
    fix F
    AOT_have \<open>\<^bold>\<A>(F \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[F]z])\<close>
      by (simp add: "actuallyF:1")
    moreover AOT_have \<open>\<^bold>\<A>((F \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[F]z]) \<rightarrow> ([\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G \<equiv> F \<approx>\<^sub>D G))\<close>
      by (auto intro!: "RA[2]" "\<rightarrow>I" "\<equiv>I"
               simp: "eq-part:3"[unvarify G, OF act_den, THEN "\<rightarrow>E", OF "&I"]
                     "eq-part:3[terms]"[unvarify G, OF act_den, THEN "\<rightarrow>E", OF "&I"])
    ultimately AOT_have \<open>\<^bold>\<A>([\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G \<equiv> F \<approx>\<^sub>D G)\<close>
      using "logic-actual-nec:2"[axiom_inst, THEN "\<equiv>E"(1), THEN "\<rightarrow>E"] by blast

    AOT_hence \<open>\<^bold>\<A>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G \<equiv> \<^bold>\<A>F \<approx>\<^sub>D G\<close>
      by (metis "Act-Basic:5" "\<equiv>E"(1))
    AOT_hence 0: \<open>(\<^bold>\<A>x[F] \<equiv> \<^bold>\<A>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G) \<equiv> (\<^bold>\<A>x[F] \<equiv> \<^bold>\<A>F \<approx>\<^sub>D G)\<close>
      by (auto intro!: "\<equiv>I" "\<rightarrow>I" elim: "\<equiv>E")
    AOT_have \<open>\<^bold>\<A>(x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G) \<equiv> (\<^bold>\<A>x[F] \<equiv> \<^bold>\<A>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>
      by (simp add: "Act-Basic:5")
    also AOT_have \<open>\<dots> \<equiv> (\<^bold>\<A>x[F] \<equiv> \<^bold>\<A>F \<approx>\<^sub>D G)\<close> using 0.
    also AOT_have \<open>\<dots> \<equiv> \<^bold>\<A>((x[F] \<equiv> F \<approx>\<^sub>D G))\<close>
      by (meson "Act-Basic:5" "\<equiv>E"(6) "oth-class-taut:3:a")
    finally AOT_have 0: \<open>\<^bold>\<A>(x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G) \<equiv> \<^bold>\<A>((x[F] \<equiv> F \<approx>\<^sub>D G))\<close>.
  } note 0 = this
  AOT_have \<open>\<^bold>\<A>\<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G) \<equiv> \<forall>F \<^bold>\<A>(x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>
    using "logic-actual-nec:3" "vdash-properties:1[2]" by blast
  also AOT_have \<open>\<dots> \<equiv>  \<forall>F \<^bold>\<A>((x[F] \<equiv> F \<approx>\<^sub>D G))\<close>
    apply (safe intro!: "\<equiv>I" "\<rightarrow>I" GEN)
    using 0 "\<equiv>E"(1) "\<equiv>E"(2) "rule-ui:3" by blast+
  also AOT_have \<open>\<dots> \<equiv> \<^bold>\<A>(\<forall>F (x[F] \<equiv> F \<approx>\<^sub>D G))\<close>
    using "\<equiv>E"(6) "logic-actual-nec:3"[axiom_inst] "oth-class-taut:3:a" by fast
  finally AOT_have 0: \<open>\<^bold>\<A>\<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G) \<equiv> \<^bold>\<A>(\<forall>F (x[F] \<equiv> F \<approx>\<^sub>D G))\<close>.
  AOT_have \<open>\<^bold>\<A>([A!]x & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)) \<equiv>
            (\<^bold>\<A>A!x & \<^bold>\<A>\<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G))\<close>
    by (simp add: "Act-Basic:2")
  also AOT_have \<open>\<dots> \<equiv> \<^bold>\<A>[A!]x & \<^bold>\<A>(\<forall>F (x[F] \<equiv> F \<approx>\<^sub>D G))\<close>
    using 0 "oth-class-taut:4:f" "\<rightarrow>E" by blast
  also AOT_have \<open>\<dots> \<equiv> \<^bold>\<A>(A!x & \<forall>F (x[F] \<equiv> F \<approx>\<^sub>D G))\<close>
    using "Act-Basic:2" "\<equiv>E"(6) "oth-class-taut:3:a" by blast
  finally AOT_show \<open>\<^bold>\<A>([A!]x & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)) \<equiv>
                    \<^bold>\<A>([A!]x & \<forall>F (x[F] \<equiv> F \<approx>\<^sub>D G))\<close>.
qed

AOT_define NaturalCardinal :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>NaturalCardinal'(_')\<close>)
  card: \<open>NaturalCardinal(x) \<equiv>\<^sub>d\<^sub>f \<exists>G(x = #G)\<close>

AOT_theorem "natcard-nec": \<open>NaturalCardinal(x) \<rightarrow> \<box>NaturalCardinal(x)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>NaturalCardinal(x)\<close>
  AOT_hence \<open>\<exists>G(x = #G)\<close> using card[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain G where \<open>x = #G\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<open>\<box>x = #G\<close> by (metis "id-nec:2" "\<rightarrow>E")
  AOT_hence \<open>\<exists>G \<box>x = #G\<close> by (rule "\<exists>I")
  AOT_hence \<open>\<box>\<exists>G x = #G\<close> by (metis Buridan "\<rightarrow>E")
  AOT_thus \<open>\<box>NaturalCardinal(x)\<close>
    by (AOT_subst_def card)
qed

AOT_act_theorem "hume:1": \<open>Numbers(#G, G)\<close>
  apply (rule "=\<^sub>d\<^sub>fI"(1)[OF "num-def:1"])
  apply (simp add: "num-uniq")
  using "num-uniq" "vdash-properties:10" "y-in:3" by blast

AOT_act_theorem "hume:2": \<open>#F = #G \<equiv> F \<approx>\<^sub>D G\<close>
  by (safe intro!: "pre-Hume"[unvarify x y, OF "num-def:2",
                              OF "num-def:2", THEN "\<rightarrow>E"] "&I" "hume:1")

(*
AOT_act_theorem "hume:3": \<open>#F = #G \<equiv> \<exists>R (R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oD G)\<close>
  using "equi-rem-thm"
  apply (AOT_subst (reverse) \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oD G\<close>
                             \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close> for: R :: \<open><\<kappa>\<times>\<kappa>>\<close>)
  using "equi:3" "hume:2" "\<equiv>E"(5) "\<equiv>Df" by blast
*)

AOT_act_theorem "hume:4": \<open>F \<equiv>\<^sub>D G \<rightarrow> #F = #G\<close>
  by (metis "apE-eqE:1" "deduction-theorem" "hume:2" "\<equiv>E"(2) "\<rightarrow>E")

AOT_theorem "hume-strict:1":
  \<open>\<exists>x (Numbers(x, F) & Numbers(x, G)) \<equiv> F \<approx>\<^sub>D G\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>\<exists>x (Numbers(x, F) & Numbers(x, G))\<close>
  then AOT_obtain a where \<open>Numbers(a, F) & Numbers(a, G)\<close>
    using "\<exists>E"[rotated] by blast
  AOT_thus \<open>F \<approx>\<^sub>D G\<close>
    using "num-tran:2" "\<rightarrow>E" by blast
next
  AOT_assume 0: \<open>F \<approx>\<^sub>D G\<close>
  moreover AOT_obtain b where num_b_F: \<open>Numbers(b, F)\<close>
    by (metis "instantiation" "num:1")
  moreover AOT_have num_b_G: \<open>Numbers(b, G)\<close>
    using calculation "num-tran:1"[THEN "\<rightarrow>E", THEN "\<equiv>E"(1)] by blast
  ultimately AOT_have \<open>Numbers(b, F) & Numbers(b, G)\<close>
    by (safe intro!: "&I")
  AOT_thus \<open>\<exists>x (Numbers(x, F) & Numbers(x, G))\<close>
    by (rule "\<exists>I")
qed

AOT_theorem "hume-strict:2":
  \<open>\<exists>x\<exists>y (Numbers(x, F) &
         \<forall>z(Numbers(z,F) \<rightarrow> z = x) &
         Numbers(y, G) &
         \<forall>z (Numbers(z, G) \<rightarrow> z = y) &
         x = y) \<equiv>
   F \<approx>\<^sub>D G\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>\<exists>x\<exists>y (Numbers(x, F) & \<forall>z(Numbers(z,F) \<rightarrow> z = x) &
                    Numbers(y, G) & \<forall>z (Numbers(z, G) \<rightarrow> z = y) & x = y)\<close>
  then AOT_obtain x where
    \<open>\<exists>y (Numbers(x, F) & \<forall>z(Numbers(z,F) \<rightarrow> z = x) & Numbers(y, G) &
         \<forall>z (Numbers(z, G) \<rightarrow> z = y) & x = y)\<close>
    using "\<exists>E"[rotated] by blast
  then AOT_obtain y where
    \<open>Numbers(x, F) & \<forall>z(Numbers(z,F) \<rightarrow> z = x) & Numbers(y, G) &
     \<forall>z (Numbers(z, G) \<rightarrow> z = y) & x = y\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<open>Numbers(x, F)\<close> and \<open>Numbers(y,G)\<close> and \<open>x = y\<close>
    using "&E" by blast+
  AOT_hence \<open>Numbers(y, F) & Numbers(y, G)\<close>
    using "&I" "rule=E" by fast
  AOT_hence \<open>\<exists>y (Numbers(y, F) & Numbers(y, G))\<close>
    by (rule "\<exists>I")
  AOT_thus \<open>F \<approx>\<^sub>D G\<close>
    using "hume-strict:1"[THEN "\<equiv>E"(1)] by blast
next
  AOT_assume \<open>F \<approx>\<^sub>D G\<close>
  AOT_hence \<open>\<exists>x (Numbers(x, F) & Numbers(x, G))\<close>
    using "hume-strict:1"[THEN "\<equiv>E"(2)] by blast
  then AOT_obtain x where \<open>Numbers(x, F) & Numbers(x, G)\<close>
    using "\<exists>E"[rotated] by blast
  moreover AOT_have \<open>\<forall>z (Numbers(z, F) \<rightarrow> z = x)\<close>
                and \<open>\<forall>z (Numbers(z, G) \<rightarrow> z = x)\<close>
    using calculation
    by (auto intro!: GEN "\<rightarrow>I" "pre-Hume"[THEN "\<rightarrow>E", OF "&I", THEN "\<equiv>E"(2),
                                         rotated 2, OF "eq-part:1"] dest: "&E")
  ultimately AOT_have \<open>Numbers(x, F) & \<forall>z(Numbers(z,F) \<rightarrow> z = x) &
                       Numbers(x, G) & \<forall>z (Numbers(z, G) \<rightarrow> z = x) & x = x\<close>
    by (auto intro!: "&I" "id-eq:1" dest: "&E")
  AOT_thus \<open>\<exists>x\<exists>y (Numbers(x, F) & \<forall>z(Numbers(z,F) \<rightarrow> z = x) & Numbers(y, G) &
                  \<forall>z (Numbers(z, G) \<rightarrow> z = y) & x = y)\<close>
    by (auto intro!: "\<exists>I")
qed

AOT_theorem unotEu: \<open>\<not>\<exists>y[\<lambda>x D!x & x \<noteq>\<^sub>D x]y\<close>
proof(rule "raa-cor:2")
  AOT_assume \<open>\<exists>y[\<lambda>x D!x & x \<noteq>\<^sub>D x]y\<close>
  then AOT_obtain y where \<open>[\<lambda>x D!x & x \<noteq>\<^sub>D x]y\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence 0: \<open>D!y & y \<noteq>\<^sub>D y\<close>
    by (rule "\<beta>\<rightarrow>C"(1))
  AOT_hence \<open>\<not>(y =\<^sub>D y)\<close>
    using "&E"(2) "\<equiv>E"(1) "thm-neg=D" by blast
  moreover AOT_have \<open>y =\<^sub>D y\<close>
    by (metis 0[THEN "&E"(1)] "disc=Dequiv:1")
  ultimately AOT_show \<open>p & \<not>p\<close> for p
    by (metis "raa-cor:3")
qed

AOT_define zero :: \<open>\<kappa>\<^sub>s\<close> (\<open>0\<close>)
  "zero:1": \<open>0 =\<^sub>d\<^sub>f #[\<lambda>x D!x & x \<noteq>\<^sub>D x]\<close>

AOT_theorem "zero:2": \<open>0\<down>\<close>
  by (rule "=\<^sub>d\<^sub>fI"(2)[OF "zero:1"]; rule "num-def:2"[unvarify G]; "cqt:2")

AOT_theorem "zero-card": \<open>NaturalCardinal(0)\<close>
  apply (rule "=\<^sub>d\<^sub>fI"(2)[OF "zero:1"])
   apply (rule "num-def:2"[unvarify G]; "cqt:2")
  apply (rule card[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  apply (rule "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>[\<lambda>x [D!]x & x \<noteq>\<^sub>D x]\<guillemotright>\<close>])
   apply (rule "rule=I:1"; rule "num-def:2"[unvarify G]; "cqt:2")
  by "cqt:2"

AOT_theorem "eq-num:1":
  \<open>\<^bold>\<A>Numbers(x, G) \<equiv> Numbers(x,[\<lambda>z \<^bold>\<A>[G]z])\<close>
proof -
  AOT_have act_den: \<open>\<^bold>\<turnstile>\<^sub>\<box> [\<lambda>z \<^bold>\<A>[F]z]\<down>\<close> for F by "cqt:2"
  AOT_have \<open>\<box>(\<exists>x(Numbers(x, G) & Numbers(x,[\<lambda>z \<^bold>\<A>[G]z])) \<equiv> G \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[G]z])\<close>
    using "hume-strict:1"[unvarify G, OF act_den, THEN RN].
  AOT_hence \<open>\<^bold>\<A>(\<exists>x(Numbers(x, G) & Numbers(x,[\<lambda>z \<^bold>\<A>[G]z])) \<equiv> G \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[G]z])\<close>
    using "nec-imp-act"[THEN "\<rightarrow>E"] by fast
  AOT_hence \<open>\<^bold>\<A>(\<exists>x(Numbers(x, G) & Numbers(x,[\<lambda>z \<^bold>\<A>[G]z])))\<close>
    using "actuallyF:1" "Act-Basic:5" "\<equiv>E"(1) "\<equiv>E"(2) by fast
  AOT_hence \<open>\<exists>x \<^bold>\<A>((Numbers(x, G) & Numbers(x,[\<lambda>z \<^bold>\<A>[G]z])))\<close>
    by (metis "Act-Basic:10" "intro-elim:3:a")
  then AOT_obtain a where \<open>\<^bold>\<A>(Numbers(a, G) & Numbers(a,[\<lambda>z \<^bold>\<A>[G]z]))\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence act_a_num_G: \<open>\<^bold>\<A>Numbers(a, G)\<close>
     and act_a_num_actG: \<open>\<^bold>\<A>Numbers(a,[\<lambda>z \<^bold>\<A>[G]z])\<close>
    using "Act-Basic:2" "&E" "\<equiv>E"(1) by blast+
  AOT_hence num_a_act_g: \<open>Numbers(a, [\<lambda>z \<^bold>\<A>[G]z])\<close>
    using "num-cont:2"[unvarify G, OF act_den, THEN "\<rightarrow>E", OF "actuallyF:2",
                       THEN CBF[THEN "\<rightarrow>E"], THEN "\<forall>E"(2)]
    by (metis "\<equiv>E"(1) "sc-eq-fur:2" "vdash-properties:6")
  AOT_have 0: \<open>\<^bold>\<turnstile>\<^sub>\<box> Numbers(x, G) & Numbers(y, G) \<rightarrow> x = y\<close> for y
    using "pre-Hume"[THEN "\<rightarrow>E", THEN "\<equiv>E"(2), rotated, OF "eq-part:1"]
          "\<rightarrow>I" by blast
  show ?thesis
  proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
    AOT_assume \<open>\<^bold>\<A>Numbers(x, G)\<close>
    AOT_hence \<open>\<^bold>\<A>x = a\<close>
      using 0[THEN "RA[2]", THEN "act-cond"[THEN "\<rightarrow>E"], THEN "\<rightarrow>E",
              OF "Act-Basic:2"[THEN "\<equiv>E"(2)], OF "&I"]
            act_a_num_G by blast
    AOT_hence \<open>x = a\<close> by (metis "id-act:1" "\<equiv>E"(2))
    AOT_hence \<open>a = x\<close> using id_sym by auto
    AOT_thus \<open>Numbers(x, [\<lambda>z \<^bold>\<A>[G]z])\<close>
      using "rule=E" num_a_act_g by fast
  next
    AOT_assume \<open>Numbers(x, [\<lambda>z \<^bold>\<A>[G]z])\<close>
    AOT_hence \<open>a = x\<close>
      using "pre-Hume"[unvarify G H, THEN "\<rightarrow>E", OF act_den, OF act_den, OF "&I",
                       OF num_a_act_g, THEN "\<equiv>E"(2)]
            "eq-part:1"[unvarify F, OF act_den] by blast
    AOT_thus \<open>\<^bold>\<A>Numbers(x, G)\<close>
      using act_a_num_G "rule=E" by fast
  qed
qed

AOT_theorem "eq-num:2": \<open>Numbers(x,[\<lambda>z \<^bold>\<A>[G]z]) \<equiv> x = #G\<close>
proof -
  AOT_have 0: \<open>\<^bold>\<turnstile>\<^sub>\<box> x = \<^bold>\<iota>x Numbers(x, G) \<equiv> \<forall>y (Numbers(y, [\<lambda>z \<^bold>\<A>[G]z]) \<equiv> y = x)\<close> for x
    by (AOT_subst (reverse) \<open>Numbers(x, [\<lambda>z \<^bold>\<A>[G]z])\<close> \<open>\<^bold>\<A>Numbers(x, G)\<close> for: x)
       (auto simp: "eq-num:1" descriptions[axiom_inst])
  AOT_have \<open>#G = \<^bold>\<iota>x Numbers(x, G) \<equiv> \<forall>y (Numbers(y, [\<lambda>z \<^bold>\<A>[G]z]) \<equiv> y = #G)\<close>
    using 0[unvarify x, OF "num-def:2"].
  moreover AOT_have \<open>#G = \<^bold>\<iota>x Numbers(x, G)\<close>
    using "num-def:1" "num-uniq" "rule-id-df:1" by blast
  ultimately AOT_have \<open>\<forall>y (Numbers(y, [\<lambda>z \<^bold>\<A>[G]z]) \<equiv> y = #G)\<close>
    using "\<equiv>E" by blast
  thus ?thesis using "\<forall>E"(2) by blast
qed

AOT_theorem "eq-num:3": \<open>Numbers(#G, [\<lambda>y \<^bold>\<A>[G]y])\<close>
proof -
  AOT_have \<open>#G = #G\<close>
    by (simp add: "rule=I:1" "num-def:2")
  thus ?thesis
    using "eq-num:2"[unvarify x, OF "num-def:2", THEN "\<equiv>E"(2)] by blast
qed

AOT_theorem "eq-num:4":
  \<open>A!#G & \<forall>F (#G[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[G]z])\<close>
  by (auto intro!: "&I" "eq-num:3"[THEN numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"],
                                   THEN "&E"(1), THEN "&E"(1)]
                   "eq-num:3"[THEN numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2)])

AOT_theorem "eq-num:5": \<open>#G[G]\<close>
  by (auto intro!: "eq-num:4"[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<equiv>E"(2)]
                   "eq-part:1"[unvarify F] simp: "cqt:2")

AOT_theorem "eq-num:6": \<open>Numbers(x, G) \<rightarrow> NaturalCardinal(x)\<close>
proof(rule "\<rightarrow>I")
  AOT_have act_den: \<open>\<^bold>\<turnstile>\<^sub>\<box> [\<lambda>z \<^bold>\<A>[F]z]\<down>\<close> for F
    by "cqt:2"
  AOT_obtain F where \<open>Rigidifies(F, G)\<close>
    by (metis "instantiation" "rigid-der:3")
  AOT_hence \<theta>: \<open>Rigid(F)\<close> and \<open>\<forall>x([F]x \<equiv> [G]x)\<close>
    using "df-rigid-rel:2"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2)]
          "df-rigid-rel:2"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(1)]
    by blast+
  AOT_hence \<open>F \<equiv>\<^sub>D G\<close>
    by (auto intro!: eqD[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" GEN "\<rightarrow>I" elim: "\<forall>E"(2))
  moreover AOT_assume \<open>Numbers(x, G)\<close>
  ultimately AOT_have \<open>Numbers(x, F)\<close>
    using "num-tran:3"[THEN "\<rightarrow>E", THEN "\<equiv>E"(2)]
    by blast
  moreover AOT_have \<open>F \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[F]z]\<close>
    using \<theta> "approx-nec:1" "\<rightarrow>E" by blast
  ultimately AOT_have \<open>Numbers(x, [\<lambda>z \<^bold>\<A>[F]z])\<close>
    using "num-tran:1"[unvarify H, OF act_den, THEN "\<rightarrow>E", THEN "\<equiv>E"(1)] by blast
  AOT_hence \<open>x = #F\<close>
    using "eq-num:2"[THEN "\<equiv>E"(1)] by blast
  AOT_hence \<open>\<exists>F x = #F\<close>
    by (rule "\<exists>I")
  AOT_thus \<open>NaturalCardinal(x)\<close>
    using card[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
qed

AOT_theorem "eq-df-num": \<open>\<exists>G (x = #G) \<equiv> \<exists>G (Numbers(x,G))\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>\<exists>G (x = #G)\<close>
  then AOT_obtain P where \<open>x = #P\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<open>Numbers(x,[\<lambda>z \<^bold>\<A>[P]z])\<close>
    using "eq-num:2"[THEN "\<equiv>E"(2)] by blast
  moreover AOT_have \<open>[\<lambda>z \<^bold>\<A>[P]z]\<down>\<close> by "cqt:2"
  ultimately AOT_show \<open>\<exists>G(Numbers(x,G))\<close> by (rule "\<exists>I")
next
  AOT_assume \<open>\<exists>G (Numbers(x,G))\<close>
  then AOT_obtain Q where \<open>Numbers(x,Q)\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<open>NaturalCardinal(x)\<close>
    using "eq-num:6"[THEN "\<rightarrow>E"] by blast
  AOT_thus \<open>\<exists>G (x = #G)\<close>
    using card[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
qed

AOT_theorem "card-en": \<open>NaturalCardinal(x) \<rightarrow> \<forall>F(x[F] \<equiv> x = #F)\<close>
proof(rule "\<rightarrow>I"; rule GEN)
  AOT_have act_den: \<open>\<^bold>\<turnstile>\<^sub>\<box> [\<lambda>z \<^bold>\<A>[F]z]\<down>\<close> for F by "cqt:2"
  fix F
  AOT_assume \<open>NaturalCardinal(x)\<close>
  AOT_hence \<open>\<exists>F x = #F\<close>
    using card[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain P where x_def: \<open>x = #P\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence num_x_act_P: \<open>Numbers(x,[\<lambda>z \<^bold>\<A>[P]z])\<close>
    using "eq-num:2"[THEN "\<equiv>E"(2)] by blast
  AOT_have \<open>#P[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[P]z]\<close>
    using "eq-num:4"[THEN "&E"(2), THEN "\<forall>E"(2)] by blast
  AOT_hence \<open>x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[P]z]\<close>
    using x_def[symmetric] "rule=E" by fast
  also AOT_have \<open>\<dots> \<equiv> Numbers(x, [\<lambda>z \<^bold>\<A>[F]z])\<close>
    using "num-tran:1"[unvarify G H, OF act_den, OF act_den]
    using "num-tran:2"[unvarify G H, OF act_den, OF act_den]
    by (metis "&I" "deduction-theorem" "\<equiv>I" "\<equiv>E"(2) num_x_act_P)
  also AOT_have \<open>\<dots> \<equiv> x = #F\<close>
    using "eq-num:2" by blast
  finally AOT_show \<open>x[F] \<equiv> x = #F\<close>.
qed

AOT_theorem "0F:1": \<open>\<not>\<exists>u [F]u \<equiv> Numbers(0, F)\<close>
proof -
  AOT_have unotEu_act_ord: \<open>\<not>\<exists>v[\<lambda>x D!x & \<^bold>\<A>x \<noteq>\<^sub>D x]v\<close>
  proof(rule "raa-cor:2")
    AOT_assume \<open>\<exists>v[\<lambda>x D!x & \<^bold>\<A>x \<noteq>\<^sub>D x]v\<close>
    then AOT_obtain y where \<open>[\<lambda>x D!x & \<^bold>\<A>x \<noteq>\<^sub>D x]y\<close>
      using "\<exists>E"[rotated] "&E" by blast
    AOT_hence 0: \<open>D!y & \<^bold>\<A>y \<noteq>\<^sub>D y\<close>
      by (rule "\<beta>\<rightarrow>C"(1))
    AOT_have \<open>\<^bold>\<A>\<not>(y =\<^sub>D y)\<close>
      apply (AOT_subst  \<open>\<not>(y =\<^sub>D y)\<close> \<open>y \<noteq>\<^sub>D y\<close>)
       apply (meson "\<equiv>E"(2) "Commutativity of \<equiv>" "thm-neg=D")
      by (fact 0[THEN "&E"(2)])
    AOT_hence \<open>\<not>(y =\<^sub>D y)\<close>
      by (metis "Act-Sub:1" "RA[2]" "disc=Dequiv:1" "intro-elim:3:d" "raa-cor:3")
    moreover AOT_have \<open>y =\<^sub>D y\<close>
      by (metis 0[THEN "&E"(1)] "disc=Dequiv:1" "\<rightarrow>E")
    ultimately AOT_show \<open>p & \<not>p\<close> for p
      by (metis "raa-cor:3")
  qed
  AOT_have \<open>Numbers(0, [\<lambda>y \<^bold>\<A>[\<lambda>x D!x & x \<noteq>\<^sub>D x]y])\<close>
    apply (rule "=\<^sub>d\<^sub>fI"(2)[OF "zero:1"])
     apply (rule "num-def:2"[unvarify G]; "cqt:2")
    apply (rule "eq-num:3"[unvarify G])
    by "cqt:2[lambda]"
  AOT_hence numbers0: \<open>Numbers(0, [\<lambda>x [D!]x & \<^bold>\<A>x \<noteq>\<^sub>D x])\<close>
  proof (rule "num-tran:3"[unvarify x G H, THEN "\<rightarrow>E", THEN "\<equiv>E"(1), rotated 4])
    AOT_show \<open>[\<lambda>y \<^bold>\<A>[\<lambda>x D!x & x \<noteq>\<^sub>D x]y] \<equiv>\<^sub>D [\<lambda>x [D!]x & \<^bold>\<A>x \<noteq>\<^sub>D x]\<close>
    proof (safe intro!: eqD[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" GEN "\<rightarrow>I" "cqt:2")
      fix u
      AOT_have \<open>[\<lambda>y \<^bold>\<A>[\<lambda>x D!x & x \<noteq>\<^sub>D x]y]u \<equiv> \<^bold>\<A>[\<lambda>x D!x & x \<noteq>\<^sub>D x]u\<close>
        by (rule "beta-C-meta"[THEN "\<rightarrow>E"]; "cqt:2[lambda]")
      also AOT_have \<open>\<dots> \<equiv> \<^bold>\<A>(D!u & u \<noteq>\<^sub>D u)\<close>
        apply (AOT_subst \<open>[\<lambda>x D!x & x \<noteq>\<^sub>D x]u\<close> \<open>D!u & u \<noteq>\<^sub>D u\<close>)
         apply (rule "beta-C-meta"[THEN "\<rightarrow>E"]; "cqt:2[lambda]")
        by (simp add: "oth-class-taut:3:a")
      also AOT_have \<open>\<dots> \<equiv> (\<^bold>\<A>D!u & \<^bold>\<A>u \<noteq>\<^sub>D u)\<close>
        by (simp add: "Act-Basic:2")
      also AOT_have \<open>\<dots> \<equiv> (D!u & \<^bold>\<A>u \<noteq>\<^sub>D u)\<close>
        using "oth-class-taut:4:e" "sc-eq-fur:2" "vdash-properties:6" Discernible.rigid_condition by blast
      also AOT_have \<open>\<dots> \<equiv> [\<lambda>x [D!]x & \<^bold>\<A>x \<noteq>\<^sub>D x]u\<close>
        by (rule "beta-C-meta"[THEN "\<rightarrow>E", symmetric]; "cqt:2[lambda]")
      finally AOT_show \<open>[\<lambda>y \<^bold>\<A>[\<lambda>x D!x & x \<noteq>\<^sub>D x]y]u \<equiv> [\<lambda>x [D!]x & \<^bold>\<A>x \<noteq>\<^sub>D x]u\<close>.
    qed
  qed(fact "zero:2" | "cqt:2")+
  show ?thesis
  proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
    AOT_assume \<open>\<not>\<exists>u [F]u\<close>
    moreover AOT_have \<open>\<not>\<exists>v [\<lambda>x [D!]x & \<^bold>\<A>x \<noteq>\<^sub>D x]v\<close>
      using unotEu_act_ord.
    ultimately AOT_have 0: \<open>F \<approx>\<^sub>D [\<lambda>x [D!]x & \<^bold>\<A>x \<noteq>\<^sub>D x]\<close>
      by (rule "empty-approx:1"[unvarify H, THEN "\<rightarrow>E", rotated, OF "&I"]) "cqt:2"
    AOT_thus \<open>Numbers(0, F)\<close>
      by (rule "num-tran:1"[unvarify x H, THEN "\<rightarrow>E",
                            THEN "\<equiv>E"(2), rotated, rotated])
         (fact "zero:2" numbers0 | "cqt:2[lambda]")+
  next
    AOT_assume \<open>Numbers(0, F)\<close>
    AOT_hence 1: \<open>F \<approx>\<^sub>D [\<lambda>x [D!]x & \<^bold>\<A>x \<noteq>\<^sub>D x]\<close>
      by (rule "num-tran:2"[unvarify x H, THEN "\<rightarrow>E", rotated 2, OF "&I"])
         (fact numbers0 "zero:2" | "cqt:2[lambda]")+
    AOT_show \<open>\<not>\<exists>u [F]u\<close>
    proof(rule "raa-cor:2")
      AOT_have 0: \<open>[\<lambda>x [D!]x & \<^bold>\<A>x \<noteq>\<^sub>D x]\<down>\<close> by "cqt:2[lambda]"
      AOT_assume \<open>\<exists>u [F]u\<close>
      AOT_hence \<open>\<not>(F \<approx>\<^sub>D [\<lambda>x [D!]x & \<^bold>\<A>x \<noteq>\<^sub>D x])\<close>
        by (rule "empty-approx:2"[unvarify H, OF 0, THEN "\<rightarrow>E", OF "&I"])
           (rule unotEu_act_ord)
      AOT_thus \<open>F \<approx>\<^sub>D [\<lambda>x [D!]x & \<^bold>\<A>x \<noteq>\<^sub>D x] & \<not>(F \<approx>\<^sub>D [\<lambda>x [D!]x & \<^bold>\<A>x \<noteq>\<^sub>D x])\<close> 
        using 1 "&I" by blast
    qed
  qed
qed

AOT_theorem "0F:2": \<open>\<not>\<exists>u \<^bold>\<A>[F]u \<equiv> #F = 0\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<not>\<exists>u \<^bold>\<A>[F]u\<close>
  AOT_have \<open>\<not>\<exists>u [\<lambda>z \<^bold>\<A>[F]z]u\<close>
  proof(rule "raa-cor:2")
    AOT_assume \<open>\<exists>u [\<lambda>z \<^bold>\<A>[F]z]u\<close>
    then AOT_obtain u where \<open>[\<lambda>z \<^bold>\<A>[F]z]u\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>\<^bold>\<A>[F]u\<close>
      by (metis "betaC:1:a")
    AOT_hence \<open>\<exists>u \<^bold>\<A>[F]u\<close>
      by (rule "\<exists>I")
    AOT_thus \<open>\<exists>u \<^bold>\<A>[F]u & \<not>\<exists>u \<^bold>\<A>[F]u\<close>
      using 0 "&I" by blast
  qed
  AOT_hence \<open>Numbers(0,[\<lambda>z \<^bold>\<A>[F]z])\<close>
    by (safe intro!: "0F:1"[unvarify F, THEN "\<equiv>E"(1)]) "cqt:2"
  AOT_hence \<open>0 = #F\<close>
    by (rule "eq-num:2"[unvarify x, OF "zero:2", THEN "\<equiv>E"(1)])
  AOT_thus \<open>#F = 0\<close> using id_sym by blast
next
  AOT_assume \<open>#F = 0\<close>
  AOT_hence \<open>0 = #F\<close> using id_sym by blast
  AOT_hence \<open>Numbers(0,[\<lambda>z \<^bold>\<A>[F]z])\<close>
    by (rule "eq-num:2"[unvarify x, OF "zero:2", THEN "\<equiv>E"(2)])
  AOT_hence 0: \<open>\<not>\<exists>u [\<lambda>z \<^bold>\<A>[F]z]u\<close>
    by (safe intro!: "0F:1"[unvarify F, THEN "\<equiv>E"(2)]) "cqt:2"
  AOT_show \<open>\<not>\<exists>u \<^bold>\<A>[F]u\<close>
  proof(rule "raa-cor:2")
    AOT_assume \<open>\<exists>u \<^bold>\<A>[F]u\<close>
    then AOT_obtain u where \<open>\<^bold>\<A>[F]u\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>[\<lambda>z \<^bold>\<A>[F]z]u\<close>
      by (auto intro!: "\<beta>\<leftarrow>C" "cqt:2")
    AOT_hence \<open>\<exists>u [\<lambda>z \<^bold>\<A>[F]z]u\<close>
      using "\<exists>I" by blast
    AOT_thus \<open>\<exists>u [\<lambda>z \<^bold>\<A>[F]z]u & \<not>\<exists>u [\<lambda>z \<^bold>\<A>[F]z]u\<close>
      using "&I" 0 by blast
  qed
qed

AOT_theorem "0F:3": \<open>\<box>\<not>\<exists>u [F]u \<rightarrow> #F = 0\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>\<box>\<not>\<exists>u [F]u\<close>
  AOT_hence 0: \<open>\<not>\<diamond>\<exists>u [F]u\<close>
    using "KBasic2:1" "\<equiv>E"(1) by blast
  AOT_have \<open>\<not>\<exists>u [\<lambda>z \<^bold>\<A>[F]z]u\<close>
  proof(rule "raa-cor:2")
    AOT_assume \<open>\<exists>u [\<lambda>z \<^bold>\<A>[F]z]u\<close>
    then AOT_obtain u where \<open>[\<lambda>z \<^bold>\<A>[F]z]u\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>\<^bold>\<A>[F]u\<close>
      by (metis "betaC:1:a")
    AOT_hence \<open>\<diamond>[F]u\<close>
      by (metis "Act-Sub:3" "\<rightarrow>E")
    AOT_hence \<open>\<exists>u \<diamond>[F]u\<close>
      by (rule "\<exists>I")
    AOT_hence \<open>\<diamond>\<exists>u [F]u\<close>
      using "CBF\<diamond>"[THEN "\<rightarrow>E"] by blast
    AOT_thus \<open>\<diamond>\<exists>u [F]u & \<not>\<diamond>\<exists>u [F]u\<close>
      using 0 "&I" by blast
  qed
  AOT_hence \<open>Numbers(0,[\<lambda>z \<^bold>\<A>[F]z])\<close>
    by (safe intro!: "0F:1"[unvarify F, THEN "\<equiv>E"(1)]) "cqt:2"
  AOT_hence \<open>0 = #F\<close>
    by (rule "eq-num:2"[unvarify x, OF "zero:2", THEN "\<equiv>E"(1)])
  AOT_thus \<open>#F = 0\<close> using id_sym by blast
qed

AOT_theorem "0F:4": \<open>w \<Turnstile> \<not>\<exists>u [F]u \<equiv> #[F]\<^sub>w = 0\<close>
proof (rule "rule-id-df:2:b"[OF "w-index", where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", simplified])
  AOT_show \<open>[\<lambda>x\<^sub>1...x\<^sub>n w \<Turnstile> [F]x\<^sub>1...x\<^sub>n]\<down>\<close>
    by (simp add: "w-rel:3")
next
  AOT_show \<open>w \<Turnstile> \<not>\<exists>u [F]u \<equiv> #[\<lambda>x w \<Turnstile> [F]x] = 0\<close>
  proof (rule "\<equiv>I"; rule "\<rightarrow>I")
    AOT_assume \<open>w \<Turnstile> \<not>\<exists>u [F]u\<close>
    AOT_hence 0: \<open>\<not>w \<Turnstile> \<exists>u [F]u\<close>
      using "coherent:1"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)] by blast
    AOT_have \<open>\<not>\<exists>u \<^bold>\<A>[\<lambda>x w \<Turnstile> [F]x]u\<close>
    proof(rule "raa-cor:2")
      AOT_assume \<open>\<exists>u \<^bold>\<A>[\<lambda>x w \<Turnstile> [F]x]u\<close>
      then AOT_obtain u where \<open>\<^bold>\<A>[\<lambda>x w \<Turnstile> [F]x]u\<close>
        using "\<exists>E"[rotated] by blast
      AOT_hence \<open>\<^bold>\<A>w \<Turnstile> [F]u\<close>
        by (AOT_subst (reverse) \<open>w \<Turnstile> [F]u\<close> \<open>[\<lambda>x w \<Turnstile> [F]x]u\<close>;
            safe intro!: "beta-C-meta"[THEN "\<rightarrow>E"] "w-rel:1"[THEN "\<rightarrow>E"])
           "cqt:2"
      AOT_hence 1: \<open>w \<Turnstile> [F]u\<close>
        using "rigid-truth-at:4"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)]
        by blast
      AOT_have \<open>\<box>([F]u \<rightarrow> \<exists>u [F]u)\<close>
        using "\<exists>I"(2) "\<rightarrow>I" RN by blast
      AOT_hence \<open>w \<Turnstile> ([F]u \<rightarrow> \<exists>u [F]u)\<close>
        using "fund:2"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)]
              "PossibleWorld.\<forall>E" by fast
      AOT_hence \<open>w \<Turnstile> \<exists>u [F]u\<close>
        using 1 "conj-dist-w:2"[unvarify p q, OF "log-prop-prop:2",
                                OF "log-prop-prop:2", THEN "\<equiv>E"(1),
                                THEN "\<rightarrow>E"] by blast
      AOT_thus \<open>w \<Turnstile> \<exists>u [F]u & \<not>w \<Turnstile> \<exists>u [F]u\<close>
        using 0 "&I" by blast
    qed
    AOT_thus \<open>#[\<lambda>x w \<Turnstile> [F]x] = 0\<close>
      by (safe intro!: "0F:2"[unvarify F, THEN "\<equiv>E"(1)] "w-rel:1"[THEN "\<rightarrow>E"])
         "cqt:2"
  next
    AOT_assume \<open>#[\<lambda>x w \<Turnstile> [F]x] = 0\<close>
    AOT_hence 0: \<open>\<not>\<exists>u \<^bold>\<A>[\<lambda>x w \<Turnstile> [F]x]u\<close>
      by (safe intro!: "0F:2"[unvarify F, THEN "\<equiv>E"(2)] "w-rel:1"[THEN "\<rightarrow>E"])
         "cqt:2"
    AOT_have \<open>\<not>w \<Turnstile> \<exists>u [F]u\<close>
    proof (rule "raa-cor:2")
      AOT_assume \<open>w \<Turnstile> \<exists>u [F]u\<close>
      AOT_hence \<open>\<exists>x w \<Turnstile> ([F]x)\<close>
        using "conj-dist-w:6"[THEN "\<equiv>E"(1)] by fast
      then AOT_obtain x where \<open>w \<Turnstile> ([F]x)\<close>
        using "\<exists>E"[rotated] by blast
      AOT_hence  Fx_in_w: \<open>w \<Turnstile> [F]x\<close>
        using "conj-dist-w:1"[unvarify p q] "\<equiv>E"(1) "log-prop-prop:2"
              "&E" by blast+
      AOT_have \<open>\<^bold>\<A>w \<Turnstile> [F]x\<close>
        using "rigid-truth-at:4"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(2)]
              Fx_in_w by blast
      AOT_hence \<open>\<^bold>\<A>[\<lambda>x w \<Turnstile> [F]x]x\<close>
        by (AOT_subst \<open>[\<lambda>x w \<Turnstile> [F]x]x\<close> \<open>w \<Turnstile> [F]x\<close>;
            safe intro!: "beta-C-meta"[THEN "\<rightarrow>E"] "w-rel:1"[THEN "\<rightarrow>E"]) "cqt:2"
      AOT_hence \<open>\<^bold>\<A>[\<lambda>x w \<Turnstile> [F]x]x\<close>
        using "&I" by blast
      AOT_hence \<open>\<exists>x (\<^bold>\<A>[\<lambda>x w \<Turnstile> [F]x]x)\<close>
        using "\<exists>I" by fast
      AOT_thus \<open>\<exists>u (\<^bold>\<A>[\<lambda>x w \<Turnstile> [F]x]u) & \<not>\<exists>u \<^bold>\<A>[\<lambda>x w \<Turnstile> [F]x]u\<close>
        using 0 "&I" by blast
    qed
    AOT_thus \<open>w \<Turnstile> \<not>\<exists>u[F]u\<close>
      using "coherent:1"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(2)] by blast
  qed
qed

AOT_act_theorem "zero=:1":
  \<open>NaturalCardinal(x) \<rightarrow> \<forall>F (x[F] \<equiv> Numbers(x, F))\<close>
proof(safe intro!: "\<rightarrow>I" GEN)
  fix F
  AOT_assume \<open>NaturalCardinal(x)\<close>
  AOT_hence \<open>\<forall>F (x[F] \<equiv> x = #F)\<close>
    by (metis "card-en" "\<rightarrow>E")
  AOT_hence 1: \<open>x[F] \<equiv> x = #F\<close>
    using "\<forall>E"(2) by blast
  AOT_have 2: \<open>x[F] \<equiv> x = \<^bold>\<iota>y(Numbers(y, F))\<close>
    by (rule "num-def:1"[THEN "=\<^sub>d\<^sub>fE"(1)])
       (auto simp: 1 "num-uniq")
  AOT_have \<open>x = \<^bold>\<iota>y(Numbers(y, F)) \<rightarrow> Numbers(x, F)\<close>
    using "y-in:1" by blast
  moreover AOT_have \<open>Numbers(x, F) \<rightarrow> x = \<^bold>\<iota>y(Numbers(y, F))\<close>
  proof(rule "\<rightarrow>I")
    AOT_assume 1: \<open>Numbers(x, F)\<close>
    moreover AOT_obtain z where z_prop: \<open>\<forall>y (Numbers(y, F) \<rightarrow> y = z)\<close>
      using "num:2"[THEN "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"]] "\<exists>E"[rotated] "&E" by blast
    ultimately AOT_have \<open>x = z\<close>
      using "\<forall>E"(2) "\<rightarrow>E" by blast
    AOT_hence \<open>\<forall>y (Numbers(y, F) \<rightarrow> y = x)\<close>
      using z_prop "rule=E" id_sym by fast
    AOT_thus \<open>x = \<^bold>\<iota>y(Numbers(y,F))\<close>
      by (rule hintikka[THEN "\<equiv>E"(2), OF "&I", rotated])
         (fact 1)
  qed
  ultimately AOT_have \<open>x = \<^bold>\<iota>y(Numbers(y, F)) \<equiv> Numbers(x, F)\<close>
    by (metis "\<equiv>I")
  AOT_thus \<open>x[F] \<equiv> Numbers(x, F)\<close>
    using 2 by (metis "\<equiv>E"(5))
qed

AOT_act_theorem "zero=:2": \<open>0[F] \<equiv> \<not>\<exists>u[F]u\<close>
proof -
  AOT_have \<open>0[F] \<equiv> Numbers(0, F)\<close>
    using "zero=:1"[unvarify x, OF "zero:2", THEN "\<rightarrow>E",
                    OF "zero-card", THEN "\<forall>E"(2)].
  also AOT_have \<open>\<dots> \<equiv> \<not>\<exists>u[F]u\<close>
    using "0F:1"[symmetric].
  finally show ?thesis.
qed

AOT_act_theorem "zero=:3": \<open>\<not>\<exists>u[F]u \<equiv> #F = 0\<close>
proof -
  AOT_have \<open>\<not>\<exists>u[F]u \<equiv> 0[F]\<close> using "zero=:2"[symmetric].
  also AOT_have \<open>\<dots> \<equiv> 0 = #F\<close>
    using "card-en"[unvarify x, OF "zero:2", THEN "\<rightarrow>E",
                    OF "zero-card", THEN "\<forall>E"(2)].
  also AOT_have \<open>\<dots> \<equiv> #F = 0\<close>
    by (simp add: "deduction-theorem" id_sym "\<equiv>I")
  finally show ?thesis.
qed

AOT_define Hereditary :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>Hereditary'(_,_')\<close>)
  "hered:1":
  \<open>Hereditary(F, R) \<equiv>\<^sub>d\<^sub>f R\<down> & F\<down> & \<forall>x\<forall>y([R]xy \<rightarrow> ([F]x \<rightarrow> [F]y))\<close>

AOT_theorem "hered:2":
  \<open>[\<lambda>xy \<forall>F((\<forall>z([R]xz \<rightarrow> [F]z) & Hereditary(F,R)) \<rightarrow> [F]y)]\<down>\<close>
  by "cqt:2[lambda]"

AOT_define StrongAncestral :: \<open>\<tau> \<Rightarrow> \<Pi>\<close> (\<open>_\<^sup>*\<close>)
  "ances-df":
  \<open>R\<^sup>* =\<^sub>d\<^sub>f [\<lambda>xy \<forall>F((\<forall>z([R]xz \<rightarrow> [F]z) & Hereditary(F,R)) \<rightarrow> [F]y)]\<close>

AOT_theorem "ances":
  \<open>[R\<^sup>*]xy \<equiv> \<forall>F((\<forall>z([R]xz \<rightarrow> [F]z) & Hereditary(F,R)) \<rightarrow> [F]y)\<close>
  apply (rule "=\<^sub>d\<^sub>fI"(1)[OF "ances-df"])
   apply "cqt:2[lambda]"
  apply (rule "beta-C-meta"[THEN "\<rightarrow>E", OF "hered:2", unvarify \<nu>\<^sub>1\<nu>\<^sub>n,
                            where \<tau>=\<open>(_,_)\<close>, simplified])
  by (simp add: "&I" "ex:1:a" prod_denotesI "rule-ui:3")

AOT_theorem "anc-her:1":
  \<open>[R]xy \<rightarrow> [R\<^sup>*]xy\<close>
proof (safe intro!: "\<rightarrow>I" ances[THEN "\<equiv>E"(2)] GEN)
  fix F
  AOT_assume \<open>\<forall>z ([R]xz \<rightarrow> [F]z) & Hereditary(F, R)\<close>
  AOT_hence \<open>[R]xy \<rightarrow> [F]y\<close>
    using "\<forall>E"(2) "&E" by blast
  moreover AOT_assume \<open>[R]xy\<close>
  ultimately AOT_show \<open>[F]y\<close>
    using "\<rightarrow>E" by blast
qed

AOT_theorem "anc-her:2":
  \<open>([R\<^sup>*]xy & \<forall>z([R]xz \<rightarrow> [F]z) & Hereditary(F,R)) \<rightarrow> [F]y\<close>
proof(rule "\<rightarrow>I"; (frule "&E"(1); drule "&E"(2))+)
  AOT_assume \<open>[R\<^sup>*]xy\<close>
  AOT_hence \<open>(\<forall>z([R]xz \<rightarrow> [F]z) & Hereditary(F,R)) \<rightarrow> [F]y\<close>
    using ances[THEN "\<equiv>E"(1)] "\<forall>E"(2) by blast
  moreover AOT_assume \<open>\<forall>z([R]xz \<rightarrow> [F]z)\<close>
  moreover AOT_assume \<open>Hereditary(F,R)\<close>
  ultimately AOT_show \<open>[F]y\<close>
    using "\<rightarrow>E" "&I" by blast
qed

AOT_theorem "anc-her:3":
  \<open>([F]x & [R\<^sup>*]xy & Hereditary(F, R)) \<rightarrow> [F]y\<close>
proof(rule "\<rightarrow>I"; (frule "&E"(1); drule "&E"(2))+)
  AOT_assume 1: \<open>[F]x\<close>
  AOT_assume 2: \<open>Hereditary(F, R)\<close>
  AOT_hence 3: \<open>\<forall>x \<forall>y ([R]xy \<rightarrow> ([F]x \<rightarrow> [F]y))\<close>
    using "hered:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_have \<open>\<forall>z ([R]xz \<rightarrow> [F]z)\<close>
  proof (rule GEN; rule "\<rightarrow>I")
    fix z
    AOT_assume \<open>[R]xz\<close>
    moreover AOT_have \<open>[R]xz \<rightarrow> ([F]x \<rightarrow> [F]z)\<close>
      using 3 "\<forall>E"(2) by blast
    ultimately AOT_show \<open>[F]z\<close>
      using 1 "\<rightarrow>E" by blast
  qed
  moreover AOT_assume \<open>[R\<^sup>*]xy\<close>
  ultimately AOT_show \<open>[F]y\<close>
    by (auto intro!: 2 "anc-her:2"[THEN "\<rightarrow>E"] "&I")
qed

AOT_theorem "anc-her:4": \<open>([R]xy & [R\<^sup>*]yz) \<rightarrow> [R\<^sup>*]xz\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume 0: \<open>[R\<^sup>*]yz\<close> and 1: \<open>[R]xy\<close>
  AOT_show \<open>[R\<^sup>*]xz\<close>
  proof(safe intro!: ances[THEN "\<equiv>E"(2)] GEN "&I" "\<rightarrow>I";
                     frule "&E"(1); drule "&E"(2))
    fix F
    AOT_assume \<open>\<forall>z ([R]xz \<rightarrow> [F]z)\<close>
    AOT_hence 1: \<open>[F]y\<close>
      using 1 "\<forall>E"(2) "\<rightarrow>E" by blast
    AOT_assume 2: \<open>Hereditary(F,R)\<close>
    AOT_show \<open>[F]z\<close>
      by (rule "anc-her:3"[THEN "\<rightarrow>E"]; auto intro!: "&I" 1 2 0)
  qed
qed

AOT_theorem "anc-her:5": \<open>[R\<^sup>*]xy \<rightarrow> \<exists>z [R]zy\<close>
proof (rule "\<rightarrow>I")
  AOT_have 0: \<open>[\<lambda>y \<exists>x [R]xy]\<down>\<close> by "cqt:2"
  AOT_assume 1: \<open>[R\<^sup>*]xy\<close>
  AOT_have \<open>[\<lambda>y\<exists>x [R]xy]y\<close>
  proof(rule "anc-her:2"[unvarify F, OF 0, THEN "\<rightarrow>E"];
        safe intro!: "&I" GEN "\<rightarrow>I" "hered:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "cqt:2" 0)
    AOT_show \<open>[R\<^sup>*]xy\<close> using 1.
  next
    fix z
    AOT_assume \<open>[R]xz\<close>
    AOT_hence \<open>\<exists>x [R]xz\<close> by (rule "\<exists>I")
    AOT_thus \<open>[\<lambda>y\<exists>x [R]xy]z\<close>
      by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2")
  next
    fix x y
    AOT_assume \<open>[R]xy\<close>
    AOT_hence \<open>\<exists>x [R]xy\<close> by (rule "\<exists>I")
    AOT_thus \<open>[\<lambda>y \<exists>x [R]xy]y\<close>
      by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2")
  qed
  AOT_thus \<open>\<exists>z [R]zy\<close>
    by (rule "\<beta>\<rightarrow>C"(1))
qed

AOT_theorem "anc-her:6": \<open>([R\<^sup>*]xy & [R\<^sup>*]yz) \<rightarrow> [R\<^sup>*]xz\<close>
proof (rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume \<open>[R\<^sup>*]xy\<close>
  AOT_hence \<theta>: \<open>\<forall>z ([R]xz \<rightarrow> [F]z) & Hereditary(F,R) \<rightarrow> [F]y\<close> for F
    using "\<forall>E"(2)  ances[THEN "\<equiv>E"(1)] by blast
  AOT_assume \<open>[R\<^sup>*]yz\<close>
  AOT_hence \<xi>: \<open>\<forall>z ([R]yz \<rightarrow> [F]z) & Hereditary(F,R) \<rightarrow> [F]z\<close> for F
    using "\<forall>E"(2) ances[THEN "\<equiv>E"(1)] by blast
  AOT_show \<open>[R\<^sup>*]xz\<close>
  proof (rule ances[THEN "\<equiv>E"(2)]; safe intro!: GEN "\<rightarrow>I")
    fix F
    AOT_assume \<zeta>: \<open>\<forall>z ([R]xz \<rightarrow> [F]z) & Hereditary(F,R)\<close>
    AOT_show \<open>[F]z\<close>
    proof (rule \<xi>[THEN "\<rightarrow>E", OF "&I"])
      AOT_show \<open>Hereditary(F,R)\<close>
        using \<zeta>[THEN "&E"(2)].
    next
      AOT_show \<open>\<forall>z ([R]yz \<rightarrow> [F]z)\<close>
      proof(rule GEN; rule "\<rightarrow>I")
        fix z
        AOT_assume \<open>[R]yz\<close>
        moreover AOT_have \<open>[F]y\<close>
          using \<theta>[THEN "\<rightarrow>E", OF \<zeta>].
        ultimately AOT_show \<open>[F]z\<close>
          using \<zeta>[THEN "&E"(2), THEN "hered:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"],
                  THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<forall>E"(2),
                  THEN "\<rightarrow>E", THEN "\<rightarrow>E"]
          by blast
      qed
    qed
  qed
qed

AOT_define OneToOne :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>1-1'(_')\<close>)
  "df-1-1:1": \<open>1-1(R) \<equiv>\<^sub>d\<^sub>f R\<down> & \<forall>x\<forall>y\<forall>z([R]xz & [R]yz \<rightarrow> x = y)\<close>

AOT_define RigidOneToOne :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>Rigid\<^sub>1\<^sub>-\<^sub>1'(_')\<close>)
  "df-1-1:2": \<open>Rigid\<^sub>1\<^sub>-\<^sub>1(R) \<equiv>\<^sub>d\<^sub>f 1-1(R) & Rigid(R)\<close>

AOT_theorem "df-1-1:3": \<open>Rigid\<^sub>1\<^sub>-\<^sub>1(R) \<rightarrow> \<box>1-1(R)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>Rigid\<^sub>1\<^sub>-\<^sub>1(R)\<close>
  AOT_hence \<open>1-1(R)\<close> and RigidR: \<open>Rigid(R)\<close>
    using "df-1-1:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_hence 1: \<open>[R]xz & [R]yz \<rightarrow> x = y\<close> for x y z
    using "df-1-1:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E"(2) "\<forall>E"(2) by blast
  AOT_have 1: \<open>[R]xz & [R]yz \<rightarrow> \<box>x = y\<close> for x y z
    by (AOT_subst (reverse) \<open>\<box>x = y\<close>  \<open>x = y\<close>)
       (auto simp: 1 "id-nec:2" "\<equiv>I" "qml:2"[axiom_inst])
  AOT_have \<open>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([R]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[R]x\<^sub>1...x\<^sub>n)\<close>
    using "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF RigidR] "&E" by blast
  AOT_hence \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n \<box>([R]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[R]x\<^sub>1...x\<^sub>n)\<close>
    using "CBF"[THEN "\<rightarrow>E"] by fast
  AOT_hence \<open>\<forall>x\<^sub>1\<forall>x\<^sub>2 \<box>([R]x\<^sub>1x\<^sub>2 \<rightarrow> \<box>[R]x\<^sub>1x\<^sub>2)\<close>
    using tuple_forall[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_hence \<open>\<box>([R]xy \<rightarrow> \<box>[R]xy)\<close> for x y
    using "\<forall>E"(2) by blast
  AOT_hence \<open>\<box>(([R]xz \<rightarrow> \<box>[R]xz) & ([R]yz \<rightarrow> \<box>[R]yz))\<close> for x y z
    by (metis "KBasic:3" "&I" "\<equiv>E"(3) "raa-cor:3")
  moreover AOT_have \<open>\<box>(([R]xz \<rightarrow> \<box>[R]xz) & ([R]yz \<rightarrow> \<box>[R]yz)) \<rightarrow>
                     \<box>(([R]xz & [R]yz) \<rightarrow> \<box>([R]xz & [R]yz))\<close> for x y z
    by (rule RM) (metis "\<rightarrow>I" "KBasic:3" "&I" "&E"(1) "&E"(2) "\<equiv>E"(2) "\<rightarrow>E")
  ultimately AOT_have 2: \<open>\<box>(([R]xz & [R]yz) \<rightarrow> \<box>([R]xz & [R]yz))\<close> for x y z
    using "\<rightarrow>E" by blast
  AOT_hence 3: \<open>\<box>([R]xz & [R]yz \<rightarrow> x = y)\<close> for x y z
    using "sc-eq-box-box:6"[THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF 2, OF 1] by blast
  AOT_hence 4: \<open>\<box>\<forall>x\<forall>y\<forall>z([R]xz & [R]yz \<rightarrow> x = y)\<close>
    by (safe intro!: GEN BF[THEN "\<rightarrow>E"] 3)
  AOT_thus \<open>\<box>1-1(R)\<close>
    by (AOT_subst_thm "df-1-1:1"[THEN "\<equiv>Df", THEN "\<equiv>S"(1),
                                 OF "cqt:2[const_var]"[axiom_inst]])
qed

AOT_theorem "df-1-1:4": \<open>\<forall>R(Rigid\<^sub>1\<^sub>-\<^sub>1(R) \<rightarrow> \<box>Rigid\<^sub>1\<^sub>-\<^sub>1(R))\<close>
proof(rule GEN;rule "\<rightarrow>I")
AOT_modally_strict {
  fix R
      AOT_assume 0: \<open>Rigid\<^sub>1\<^sub>-\<^sub>1(R)\<close>
      AOT_hence 1: \<open>R\<down>\<close>
        by (meson "\<equiv>\<^sub>d\<^sub>fE" "&E"(1) "df-1-1:1" "df-1-1:2")
      AOT_hence 2: \<open>\<box>R\<down>\<close>
        using "exist-nec" "\<rightarrow>E" by blast
      AOT_have 4: \<open>\<box>1-1(R)\<close>
        using "df-1-1:3"[unvarify R, OF 1, THEN "\<rightarrow>E", OF 0].
      AOT_have \<open>Rigid(R)\<close>
        using 0 "\<equiv>\<^sub>d\<^sub>fE"[OF "df-1-1:2"] "&E" by blast
      AOT_hence \<open>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([R]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[R]x\<^sub>1...x\<^sub>n)\<close>
        using  "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
      AOT_hence \<open>\<box>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([R]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[R]x\<^sub>1...x\<^sub>n)\<close>
        by (metis "S5Basic:6" "\<equiv>E"(1))
      AOT_hence \<open>\<box>Rigid(R)\<close>
        apply (AOT_subst_def "df-rigid-rel:1")
        using 2 "KBasic:3" "\<equiv>S"(2) "\<equiv>E"(2) by blast
      AOT_thus \<open>\<box>Rigid\<^sub>1\<^sub>-\<^sub>1(R)\<close>
        apply (AOT_subst_def "df-1-1:2")
        using 4 "KBasic:3" "\<equiv>S"(2) "\<equiv>E"(2) by blast
}
qed

AOT_define InDomainOf :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>InDomainOf'(_,_')\<close>)
  "df-1-1:5": \<open>InDomainOf(x, R) \<equiv>\<^sub>d\<^sub>f \<exists>y [R]xy\<close>

AOT_register_rigid_restricted_type
  RigidOneToOneRelation: \<open>Rigid\<^sub>1\<^sub>-\<^sub>1(\<Pi>)\<close>
proof
  AOT_modally_strict {
    AOT_show \<open>\<exists>\<alpha> Rigid\<^sub>1\<^sub>-\<^sub>1(\<alpha>)\<close>
    proof (rule "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>(=\<^sub>E)\<guillemotright>\<close>])
      AOT_show \<open>Rigid\<^sub>1\<^sub>-\<^sub>1((=\<^sub>E))\<close>
      proof (safe intro!: "df-1-1:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "df-1-1:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"]
                          GEN "\<rightarrow>I" "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "=E[denotes]")
        fix x y z
        AOT_assume \<open>x =\<^sub>E z & y =\<^sub>E z\<close>
        AOT_thus \<open>x = y\<close>
          by (metis "rule=E" "&E"(1) "Conjunction Simplification"(2)
                    "=E-simple:2" id_sym "\<rightarrow>E")
      next
        AOT_have \<open>\<forall>x\<forall>y \<box>(x =\<^sub>E y \<rightarrow> \<box>x =\<^sub>E y)\<close>
        proof(rule GEN; rule GEN)
          AOT_show \<open>\<box>(x =\<^sub>E y \<rightarrow> \<box>x =\<^sub>E y)\<close> for x y
            by (meson RN "deduction-theorem" "id-nec3:1" "\<equiv>E"(1))
        qed
        AOT_hence \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n \<box>([(=\<^sub>E)]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[(=\<^sub>E)]x\<^sub>1...x\<^sub>n)\<close>
          by (rule tuple_forall[THEN "\<equiv>\<^sub>d\<^sub>fI"])
        AOT_thus \<open>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([(=\<^sub>E)]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[(=\<^sub>E)]x\<^sub>1...x\<^sub>n)\<close>
          using BF[THEN "\<rightarrow>E"] by fast
      qed
    qed(fact "=E[denotes]")
  }
next
  AOT_modally_strict {
    AOT_show \<open>Rigid\<^sub>1\<^sub>-\<^sub>1(\<Pi>) \<rightarrow> \<Pi>\<down>\<close> for \<Pi>
    proof(rule "\<rightarrow>I")
      AOT_assume \<open>Rigid\<^sub>1\<^sub>-\<^sub>1(\<Pi>)\<close>
      AOT_hence \<open>1-1(\<Pi>)\<close>
        using "df-1-1:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
      AOT_thus \<open>\<Pi>\<down>\<close>
        using "df-1-1:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
    qed
  } note 1 = this
  AOT_modally_strict {
    AOT_show \<open>\<box>(Rigid\<^sub>1\<^sub>-\<^sub>1(\<Pi>) \<rightarrow> \<box>Rigid\<^sub>1\<^sub>-\<^sub>1(\<Pi>))\<close> for \<Pi>
      using "df-1-1:4"[THEN "\<forall>E"(1), OF 1[THEN "\<rightarrow>E"], THEN "\<rightarrow>E"] "\<rightarrow>I" RN
      by blast
  }
qed
AOT_register_variable_names
  RigidOneToOneRelation: \<R> \<S>

AOT_define IdentityRestrictedToDomain :: \<open>\<tau> \<Rightarrow> \<Pi>\<close> (\<open>'(=\<^sub>_')\<close>)
  "id-d-R": \<open>(=\<^sub>\<R>) =\<^sub>d\<^sub>f [\<lambda>xy \<exists>z ([\<R>]xz & [\<R>]yz)]\<close>

syntax "_AOT_id_d_R_infix" :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> ("(_ =\<^sub>_/ _)" [50, 51, 51] 50)
translations
  "_AOT_id_d_R_infix \<kappa> \<Pi> \<kappa>'" ==
  "CONST AOT_exe (CONST IdentityRestrictedToDomain \<Pi>) (\<kappa>,\<kappa>')"

AOT_theorem "id-R-thm:1": \<open>x =\<^sub>\<R> y \<equiv> \<exists>z ([\<R>]xz & [\<R>]yz)\<close>
proof -
  AOT_have 0: \<open>[\<lambda>xy \<exists>z ([\<R>]xz & [\<R>]yz)]\<down>\<close> by "cqt:2"
  show ?thesis
    apply (rule "=\<^sub>d\<^sub>fI"(1)[OF "id-d-R"])
    apply (fact 0)
    apply (rule "beta-C-meta"[THEN "\<rightarrow>E", OF 0, unvarify \<nu>\<^sub>1\<nu>\<^sub>n,
                              where \<tau>=\<open>(_,_)\<close>, simplified])
    by (simp add: "&I" "ex:1:a" prod_denotesI "rule-ui:3")
qed

AOT_theorem "id-R-thm:2":
  \<open>x =\<^sub>\<R> y \<rightarrow> (InDomainOf(x, \<R>) & InDomainOf(y, \<R>))\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>x =\<^sub>\<R> y\<close>
  AOT_hence \<open>\<exists>z ([\<R>]xz & [\<R>]yz)\<close>
    using "id-R-thm:1"[THEN "\<equiv>E"(1)] by simp
  then AOT_obtain z where z_prop: \<open>[\<R>]xz & [\<R>]yz\<close>
    using "\<exists>E"[rotated] by blast
  AOT_show \<open>InDomainOf(x, \<R>) & InDomainOf(y, \<R>)\<close>
  proof (safe intro!: "&I" "df-1-1:5"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
    AOT_show \<open>\<exists>y [\<R>]xy\<close>
      using z_prop[THEN "&E"(1)] "\<exists>I" by fast
  next
    AOT_show \<open>\<exists>z [\<R>]yz\<close>
      using z_prop[THEN "&E"(2)] "\<exists>I" by fast
  qed
qed

AOT_theorem "id-R-thm:3": \<open>x =\<^sub>\<R> y \<rightarrow> x = y\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>x =\<^sub>\<R> y\<close>
  AOT_hence \<open>\<exists>z ([\<R>]xz & [\<R>]yz)\<close>
    using "id-R-thm:1"[THEN "\<equiv>E"(1)] by simp
  then AOT_obtain z where z_prop: \<open>[\<R>]xz & [\<R>]yz\<close>
    using "\<exists>E"[rotated] by blast
  AOT_thus \<open>x = y\<close>
    using "df-1-1:3"[THEN "\<rightarrow>E", OF RigidOneToOneRelation.\<psi>,
                     THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"],
                     THEN "\<equiv>\<^sub>d\<^sub>fE"[OF "df-1-1:1"], THEN "&E"(2),
                     THEN "\<forall>E"(2), THEN "\<forall>E"(2),
                     THEN "\<forall>E"(2), THEN "\<rightarrow>E"]
     by blast
qed

AOT_theorem "id-R-thm:4":
  \<open>(InDomainOf(x, \<R>) \<or> InDomainOf(y, \<R>)) \<rightarrow> (x =\<^sub>\<R> y \<equiv> x = y)\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>InDomainOf(x, \<R>) \<or> InDomainOf(y, \<R>)\<close>
  moreover {
    AOT_assume \<open>InDomainOf(x, \<R>)\<close>
    AOT_hence \<open>\<exists>z [\<R>]xz\<close>
      by (metis "\<equiv>\<^sub>d\<^sub>fE" "df-1-1:5")
    then AOT_obtain z where z_prop: \<open>[\<R>]xz\<close>
      using "\<exists>E"[rotated] by blast
    AOT_have \<open>x =\<^sub>\<R> y \<equiv> x = y\<close>
    proof(safe intro!: "\<equiv>I" "\<rightarrow>I" "id-R-thm:3"[THEN "\<rightarrow>E"])
      AOT_assume \<open>x = y\<close>
      AOT_hence \<open>[\<R>]yz\<close>
        using z_prop "rule=E" by fast
      AOT_hence \<open>[\<R>]xz & [\<R>]yz\<close>
        using z_prop "&I" by blast
      AOT_hence \<open>\<exists>z ([\<R>]xz & [\<R>]yz)\<close>
        by (rule "\<exists>I")
      AOT_thus \<open>x =\<^sub>\<R> y\<close>
        using "id-R-thm:1" "\<equiv>E"(2) by blast
    qed
  }
  moreover {
    AOT_assume \<open>InDomainOf(y, \<R>)\<close>
    AOT_hence \<open>\<exists>z [\<R>]yz\<close>
      by (metis "\<equiv>\<^sub>d\<^sub>fE" "df-1-1:5")
    then AOT_obtain z where z_prop: \<open>[\<R>]yz\<close>
      using "\<exists>E"[rotated] by blast
    AOT_have \<open>x =\<^sub>\<R> y \<equiv> x = y\<close>
    proof(safe intro!: "\<equiv>I" "\<rightarrow>I" "id-R-thm:3"[THEN "\<rightarrow>E"])
      AOT_assume \<open>x = y\<close>
      AOT_hence \<open>[\<R>]xz\<close>
        using z_prop "rule=E" id_sym by fast
      AOT_hence \<open>[\<R>]xz & [\<R>]yz\<close>
        using z_prop "&I" by blast
      AOT_hence \<open>\<exists>z ([\<R>]xz & [\<R>]yz)\<close>
        by (rule "\<exists>I")
      AOT_thus \<open>x =\<^sub>\<R> y\<close>
        using "id-R-thm:1" "\<equiv>E"(2) by blast
    qed
  }
  ultimately AOT_show \<open>x =\<^sub>\<R> y \<equiv> x = y\<close>
    by (metis "\<or>E"(2) "raa-cor:1")
qed

AOT_theorem "id-R-thm:5": \<open>InDomainOf(x, \<R>) \<rightarrow> x =\<^sub>\<R> x\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>InDomainOf(x, \<R>)\<close>
  AOT_hence \<open>\<exists>z [\<R>]xz\<close>
    by (metis "\<equiv>\<^sub>d\<^sub>fE" "df-1-1:5")
  then AOT_obtain z where z_prop: \<open>[\<R>]xz\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<open>[\<R>]xz & [\<R>]xz\<close>
    using "&I" by blast
  AOT_hence \<open>\<exists>z ([\<R>]xz & [\<R>]xz)\<close>
    using "\<exists>I" by fast
  AOT_thus \<open>x =\<^sub>\<R> x\<close>
    using "id-R-thm:1" "\<equiv>E"(2) by blast
qed

AOT_theorem "id-R-thm:6": \<open>x =\<^sub>\<R> y \<rightarrow> y =\<^sub>\<R> x\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>x =\<^sub>\<R> y\<close>
  AOT_hence 1: \<open>InDomainOf(x,\<R>) & InDomainOf(y,\<R>)\<close>
    using "id-R-thm:2"[THEN "\<rightarrow>E"] by blast
  AOT_hence \<open>x =\<^sub>\<R> y \<equiv> x = y\<close>
    using "id-R-thm:4"[THEN "\<rightarrow>E", OF "\<or>I"(1)] "&E" by blast
  AOT_hence \<open>x = y\<close>
    using 0 by (metis "\<equiv>E"(1))
  AOT_hence \<open>y = x\<close>
    using id_sym by blast
  moreover AOT_have \<open>y =\<^sub>\<R> x \<equiv> y = x\<close>
    using "id-R-thm:4"[THEN "\<rightarrow>E", OF "\<or>I"(2)] 1 "&E" by blast
  ultimately AOT_show \<open>y =\<^sub>\<R> x\<close>
    by (metis "\<equiv>E"(2))
qed

AOT_theorem "id-R-thm:7": \<open>x =\<^sub>\<R> y & y =\<^sub>\<R> z \<rightarrow> x =\<^sub>\<R> z\<close>
proof (rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume 0: \<open>x =\<^sub>\<R> y\<close>
  AOT_hence 1: \<open>InDomainOf(x,\<R>) & InDomainOf(y,\<R>)\<close>
    using "id-R-thm:2"[THEN "\<rightarrow>E"] by blast
  AOT_hence \<open>x =\<^sub>\<R> y \<equiv> x = y\<close>
    using "id-R-thm:4"[THEN "\<rightarrow>E", OF "\<or>I"(1)] "&E" by blast
  AOT_hence x_eq_y: \<open>x = y\<close>
    using 0 by (metis "\<equiv>E"(1))
  AOT_assume 2: \<open>y =\<^sub>\<R> z\<close>
  AOT_hence 3: \<open>InDomainOf(y,\<R>) & InDomainOf(z,\<R>)\<close>
    using "id-R-thm:2"[THEN "\<rightarrow>E"] by blast
  AOT_hence \<open>y =\<^sub>\<R> z \<equiv> y = z\<close>
    using "id-R-thm:4"[THEN "\<rightarrow>E", OF "\<or>I"(1)] "&E" by blast
  AOT_hence \<open>y = z\<close>
    using 2 by (metis "\<equiv>E"(1))
  AOT_hence x_eq_z: \<open>x = z\<close>
    using x_eq_y id_trans by blast
  AOT_have \<open>InDomainOf(x,\<R>) & InDomainOf(z,\<R>)\<close>
    using 1 3 "&I" "&E" by meson
  AOT_hence \<open>x =\<^sub>\<R> z \<equiv> x = z\<close>
    using "id-R-thm:4"[THEN "\<rightarrow>E", OF "\<or>I"(1)] "&E" by blast
  AOT_thus \<open>x =\<^sub>\<R> z\<close>
    using x_eq_z "\<equiv>E"(2) by blast
qed

AOT_define WeakAncestral :: \<open>\<Pi> \<Rightarrow> \<Pi>\<close> (\<open>_\<^sup>+\<close>)
  "w-ances-df": \<open>[\<R>]\<^sup>+ =\<^sub>d\<^sub>f [\<lambda>xy [\<R>]\<^sup>*xy \<or> x =\<^sub>\<R> y]\<close>

AOT_theorem "w-ances-df[den1]": \<open>[\<lambda>xy [\<Pi>]\<^sup>*xy \<or> x =\<^sub>\<Pi> y]\<down>\<close>
  by "cqt:2"
AOT_theorem "w-ances-df[den2]": \<open>[\<Pi>]\<^sup>+\<down>\<close>
  using "w-ances-df[den1]" "=\<^sub>d\<^sub>fI"(1)[OF "w-ances-df"] by blast

AOT_theorem "w-ances": \<open>[\<R>]\<^sup>+xy \<equiv> ([\<R>]\<^sup>*xy \<or> x =\<^sub>\<R> y)\<close>
proof -
  AOT_have 0: \<open>[\<lambda>xy [\<R>\<^sup>*]xy \<or> x =\<^sub>\<R> y]\<down>\<close>
    by "cqt:2"
  AOT_have 1: \<open>\<guillemotleft>(AOT_term_of_var x,AOT_term_of_var y)\<guillemotright>\<down>\<close>
    by (simp add: "&I" "ex:1:a" prod_denotesI "rule-ui:3")
  have 2: \<open>\<guillemotleft>[\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n [\<R>\<^sup>*]\<mu>\<^sub>1...\<mu>\<^sub>n \<or> [(=\<^sub>\<R>)]\<mu>\<^sub>1...\<mu>\<^sub>n]xy\<guillemotright> =
           \<guillemotleft>[\<lambda>xy [\<R>\<^sup>*]xy \<or> [(=\<^sub>\<R>)]xy]xy\<guillemotright>\<close>
    by (simp add: cond_case_prod_eta)
  show ?thesis
    apply (rule "=\<^sub>d\<^sub>fI"(1)[OF "w-ances-df"])
     apply (fact "w-ances-df[den1]")
    using "beta-C-meta"[THEN "\<rightarrow>E", OF 0, unvarify \<nu>\<^sub>1\<nu>\<^sub>n,
                        where \<tau>=\<open>(_,_)\<close>, simplified, OF 1] 2 by simp
qed

AOT_theorem "w-ances-her:1": \<open>[\<R>]xy \<rightarrow> [\<R>]\<^sup>+xy\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>[\<R>]xy\<close>
  AOT_hence \<open>[\<R>]\<^sup>*xy\<close>
    using "anc-her:1"[THEN "\<rightarrow>E"] by blast
  AOT_thus \<open>[\<R>]\<^sup>+xy\<close>
    using "w-ances"[THEN "\<equiv>E"(2)] "\<or>I" by blast
qed

AOT_theorem "w-ances-her:2":
  \<open>[F]x & [\<R>]\<^sup>+xy & Hereditary(F, \<R>) \<rightarrow> [F]y\<close>
proof(rule "\<rightarrow>I"; (frule "&E"(1); drule "&E"(2))+)
  AOT_assume 0: \<open>[F]x\<close>
  AOT_assume 1: \<open>Hereditary(F, \<R>)\<close>
  AOT_assume \<open>[\<R>]\<^sup>+xy\<close>
  AOT_hence \<open>[\<R>]\<^sup>*xy \<or> x =\<^sub>\<R> y\<close>
    using "w-ances"[THEN "\<equiv>E"(1)] by simp
  moreover {
    AOT_assume \<open>[\<R>]\<^sup>*xy\<close>
    AOT_hence \<open>[F]y\<close>
      using "anc-her:3"[THEN "\<rightarrow>E", OF "&I", OF "&I"] 0 1 by blast
  }
  moreover {
    AOT_assume \<open>x =\<^sub>\<R> y\<close>
    AOT_hence \<open>x = y\<close>
      using "id-R-thm:3"[THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>[F]y\<close>
      using 0 "rule=E" by blast
  }
  ultimately AOT_show \<open>[F]y\<close>
    by (metis "\<or>E"(3) "raa-cor:1")
qed

AOT_theorem "w-ances-her:3": \<open>([\<R>]\<^sup>+xy & [\<R>]yz) \<rightarrow> [\<R>]\<^sup>*xz\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume \<open>[\<R>]\<^sup>+xy\<close>
  moreover AOT_assume Ryz: \<open>[\<R>]yz\<close>
  ultimately AOT_have \<open>[\<R>]\<^sup>*xy \<or> x =\<^sub>\<R> y\<close>
    using "w-ances"[THEN "\<equiv>E"(1)] by metis
  moreover {
    AOT_assume R_star_xy: \<open>[\<R>]\<^sup>*xy\<close>
    AOT_have \<open>[\<R>]\<^sup>*xz\<close>
    proof (safe intro!: ances[THEN "\<equiv>E"(2)] "\<rightarrow>I" GEN)
      fix F
      AOT_assume 0: \<open>\<forall>z ([\<R>]xz \<rightarrow> [F]z) & Hereditary(F,\<R>)\<close>
      AOT_hence \<open>[F]y\<close>
        using R_star_xy ances[THEN "\<equiv>E"(1), OF R_star_xy,
                              THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
      AOT_thus \<open>[F]z\<close>
        using "hered:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF 0[THEN "&E"(2)], THEN "&E"(2)]
              "\<forall>E"(2) "\<rightarrow>E" Ryz by blast
    qed
  }
  moreover {
    AOT_assume \<open>x =\<^sub>\<R> y\<close>
    AOT_hence \<open>x = y\<close>
      using "id-R-thm:3"[THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>[\<R>]xz\<close>
      using Ryz "rule=E" id_sym by fast
    AOT_hence \<open>[\<R>]\<^sup>*xz\<close>
      by (metis "anc-her:1"[THEN "\<rightarrow>E"])
  }
  ultimately AOT_show \<open>[\<R>]\<^sup>*xz\<close>
    by (metis "\<or>E"(3) "raa-cor:1")
qed

AOT_theorem "w-ances-her:4": \<open>([\<R>]\<^sup>*xy & [\<R>]yz) \<rightarrow> [\<R>]\<^sup>+xz\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume \<open>[\<R>]\<^sup>*xy\<close>
  AOT_hence \<open>[\<R>]\<^sup>*xy \<or> x =\<^sub>\<R> y\<close>
    using "\<or>I" by blast
  AOT_hence \<open>[\<R>]\<^sup>+xy\<close>
    using "w-ances"[THEN "\<equiv>E"(2)] by blast
  moreover AOT_assume \<open>[\<R>]yz\<close>
  ultimately AOT_have \<open>[\<R>]\<^sup>*xz\<close>
    using "w-ances-her:3"[THEN "\<rightarrow>E", OF "&I"] by simp
  AOT_hence \<open>[\<R>]\<^sup>*xz \<or> x =\<^sub>\<R> z\<close>
    using "\<or>I" by blast
  AOT_thus \<open>[\<R>]\<^sup>+xz\<close>
    using "w-ances"[THEN "\<equiv>E"(2)] by blast
qed

AOT_theorem "w-ances-her:5": \<open>([\<R>]xy & [\<R>]\<^sup>+yz) \<rightarrow> [\<R>]\<^sup>*xz\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume 0: \<open>[\<R>]xy\<close>
  AOT_assume \<open>[\<R>]\<^sup>+yz\<close>
  AOT_hence \<open>[\<R>]\<^sup>*yz \<or> y =\<^sub>\<R> z\<close>
    by (metis "\<equiv>E"(1) "w-ances")
  moreover {
    AOT_assume \<open>[\<R>]\<^sup>*yz\<close>
    AOT_hence \<open>[\<R>]\<^sup>*xz\<close>
      using 0 by (metis "anc-her:4" Adjunction "\<rightarrow>E")
  }
  moreover {
    AOT_assume \<open>y =\<^sub>\<R> z\<close>
    AOT_hence \<open>y = z\<close>
      by (metis "id-R-thm:3" "\<rightarrow>E")
    AOT_hence \<open>[\<R>]xz\<close>
      using 0 "rule=E" by fast
    AOT_hence \<open>[\<R>]\<^sup>*xz\<close>
      by (metis "anc-her:1" "\<rightarrow>E")
  }
  ultimately AOT_show \<open>[\<R>]\<^sup>*xz\<close> by (metis "\<or>E"(2) "reductio-aa:1")
qed

AOT_theorem "w-ances-her:6": \<open>([\<R>]\<^sup>+xy & [\<R>]\<^sup>+yz) \<rightarrow> [\<R>]\<^sup>+xz\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume 0: \<open>[\<R>]\<^sup>+xy\<close>
  AOT_hence 1: \<open>[\<R>]\<^sup>*xy \<or> x =\<^sub>\<R> y\<close>
    by (metis "\<equiv>E"(1) "w-ances")
  AOT_assume 2: \<open>[\<R>]\<^sup>+yz\<close>
  {
    AOT_assume \<open>x =\<^sub>\<R> y\<close>
    AOT_hence \<open>x = y\<close>
      by (metis "id-R-thm:3" "\<rightarrow>E")
    AOT_hence \<open>[\<R>]\<^sup>+xz\<close>
      using 2 "rule=E" id_sym by fast
  }
  moreover {
    AOT_assume \<open>\<not>(x =\<^sub>\<R> y)\<close>
    AOT_hence 3: \<open>[\<R>]\<^sup>*xy\<close>
      using 1 by (metis "\<or>E"(3)) 
    AOT_have \<open>[\<R>]\<^sup>*yz \<or> y =\<^sub>\<R> z\<close>
      using 2 by (metis "\<equiv>E"(1) "w-ances")
    moreover {
      AOT_assume \<open>[\<R>]\<^sup>*yz\<close>
      AOT_hence \<open>[\<R>]\<^sup>*xz\<close>
        using 3 by (metis "anc-her:6" Adjunction "\<rightarrow>E")
      AOT_hence \<open>[\<R>]\<^sup>+xz\<close>
        by (metis "\<or>I"(1) "\<equiv>E"(2) "w-ances")
    }
    moreover {
      AOT_assume \<open>y =\<^sub>\<R> z\<close>
      AOT_hence \<open>y = z\<close>
        by (metis "id-R-thm:3" "\<rightarrow>E")
      AOT_hence \<open>[\<R>]\<^sup>+xz\<close>
        using 0 "rule=E" id_sym by fast
    }
    ultimately AOT_have \<open>[\<R>]\<^sup>+xz\<close>
      by (metis "\<or>E"(3) "reductio-aa:1")
  }
  ultimately AOT_show \<open>[\<R>]\<^sup>+xz\<close>
    by (metis "reductio-aa:1")
qed

AOT_theorem "w-ances-her:7": \<open>[\<R>]\<^sup>*xy \<rightarrow> \<exists>z([\<R>]\<^sup>+xz & [\<R>]zy)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>[\<R>]\<^sup>*xy\<close>
  AOT_have 1: \<open>\<forall>z ([\<R>]xz \<rightarrow> [\<Pi>]z) & Hereditary(\<Pi>,\<R>) \<rightarrow> [\<Pi>]y\<close> if \<open>\<Pi>\<down>\<close> for \<Pi>
    using ances[THEN "\<equiv>E"(1), THEN "\<forall>E"(1), OF 0] that by blast
  AOT_have \<open>[\<lambda>y \<exists>z([\<R>]\<^sup>+xz & [\<R>]zy)]y\<close>
  proof (rule 1[THEN "\<rightarrow>E"]; "cqt:2[lambda]"?;
         safe intro!: "&I" GEN "\<rightarrow>I" "hered:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "cqt:2")
    fix z
    AOT_assume 0: \<open>[\<R>]xz\<close>
    AOT_hence \<open>\<exists>z [\<R>]xz\<close> by (rule "\<exists>I")
    AOT_hence \<open>InDomainOf(x, \<R>)\<close> by (metis "\<equiv>\<^sub>d\<^sub>fI" "df-1-1:5")
    AOT_hence \<open>x =\<^sub>\<R> x\<close> by (metis "id-R-thm:5" "\<rightarrow>E")
    AOT_hence \<open>[\<R>]\<^sup>+xx\<close> by (metis "\<or>I"(2) "\<equiv>E"(2) "w-ances")
    AOT_hence \<open>[\<R>]\<^sup>+xx & [\<R>]xz\<close> using 0 "&I" by blast
    AOT_hence \<open>\<exists>y ([\<R>]\<^sup>+xy & [\<R>]yz)\<close> by (rule "\<exists>I")
    AOT_thus \<open>[\<lambda>y \<exists>z ([\<R>]\<^sup>+xz & [\<R>]zy)]z\<close>
      by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2")
  next
    fix x' y
    AOT_assume Rx'y: \<open>[\<R>]x'y\<close>
    AOT_assume \<open>[\<lambda>y \<exists>z ([\<R>]\<^sup>+xz & [\<R>]zy)]x'\<close>
    AOT_hence \<open>\<exists>z ([\<R>]\<^sup>+xz & [\<R>]zx')\<close>
      using "\<beta>\<rightarrow>C"(1) by blast
    then AOT_obtain c where c_prop: \<open>[\<R>]\<^sup>+xc & [\<R>]cx'\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>[\<R>]\<^sup>*xx'\<close>
      by (meson Rx'y "anc-her:1" "anc-her:6" Adjunction "\<rightarrow>E" "w-ances-her:3")
    AOT_hence \<open>[\<R>]\<^sup>*xx' \<or> x =\<^sub>\<R> x'\<close> by (rule "\<or>I")
    AOT_hence \<open>[\<R>]\<^sup>+xx'\<close> by (metis "\<equiv>E"(2) "w-ances")
    AOT_hence \<open>[\<R>]\<^sup>+xx' & [\<R>]x'y\<close> using Rx'y by (metis "&I")
    AOT_hence \<open>\<exists>z ([\<R>]\<^sup>+xz & [\<R>]zy)\<close> by (rule "\<exists>I")
    AOT_thus \<open>[\<lambda>y \<exists>z ([\<R>]\<^sup>+xz & [\<R>]zy)]y\<close>
      by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2")
  qed
  AOT_thus \<open>\<exists>z([\<R>]\<^sup>+xz & [\<R>]zy)\<close>
    using "\<beta>\<rightarrow>C"(1) by fast
qed

AOT_theorem "1-1-R:1": \<open>([\<R>]xy & [\<R>]\<^sup>*zy) \<rightarrow> [\<R>]\<^sup>+zx\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume \<open>[\<R>]\<^sup>*zy\<close>
  AOT_hence \<open>\<exists>x ([\<R>]\<^sup>+zx & [\<R>]xy)\<close>
    using "w-ances-her:7"[THEN "\<rightarrow>E"] by simp
  then AOT_obtain a where a_prop: \<open>[\<R>]\<^sup>+za & [\<R>]ay\<close>
    using "\<exists>E"[rotated] by blast
  moreover AOT_assume \<open>[\<R>]xy\<close>
  ultimately AOT_have \<open>x = a\<close>
    using "df-1-1:2"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF RigidOneToOneRelation.\<psi>, THEN "&E"(1),
                     THEN "\<equiv>\<^sub>d\<^sub>fE"[OF "df-1-1:1"], THEN "&E"(2), THEN "\<forall>E"(2),
                     THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF "&I"]
    "&E" by blast
  AOT_thus \<open>[\<R>]\<^sup>+zx\<close>
    using a_prop[THEN "&E"(1)] "rule=E" id_sym by fast
qed

AOT_theorem "1-1-R:2": \<open>[\<R>]xy \<rightarrow> (\<not>[\<R>]\<^sup>*xx \<rightarrow> \<not>[\<R>]\<^sup>*yy)\<close>
proof(rule "\<rightarrow>I"; rule "useful-tautologies:5"[THEN "\<rightarrow>E"]; rule "\<rightarrow>I")
  AOT_assume 0: \<open>[\<R>]xy\<close>
  moreover AOT_assume \<open>[\<R>]\<^sup>*yy\<close>
  ultimately AOT_have \<open>[\<R>]\<^sup>+yx\<close>
    using "1-1-R:1"[THEN "\<rightarrow>E", OF "&I"] by blast
  AOT_thus \<open>[\<R>]\<^sup>*xx\<close>
    using 0 by (metis "&I" "\<rightarrow>E" "w-ances-her:5")
qed

AOT_theorem "1-1-R:3": \<open>\<not>[\<R>]\<^sup>*xx \<rightarrow> ([\<R>]\<^sup>+xy \<rightarrow> \<not>[\<R>]\<^sup>*yy)\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_have 0: \<open>[\<lambda>z \<not>[\<R>]\<^sup>*zz]\<down>\<close> by "cqt:2"
  AOT_assume 1: \<open>\<not>[\<R>]\<^sup>*xx\<close>
  AOT_assume 2: \<open>[\<R>]\<^sup>+xy\<close>
  AOT_have \<open>[\<lambda>z \<not>[\<R>]\<^sup>*zz]y\<close>
  proof(rule "w-ances-her:2"[unvarify F, OF 0, THEN "\<rightarrow>E"];
        safe intro!: "&I" "hered:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "cqt:2" GEN "\<rightarrow>I")
    AOT_show  \<open>[\<lambda>z \<not>[\<R>]\<^sup>*zz]x\<close>
      by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" simp: 1)
  next
    AOT_show \<open>[\<R>]\<^sup>+xy\<close> by (fact 2)
  next
    fix x y
    AOT_assume \<open>[\<lambda>z \<not>[\<R>\<^sup>*]zz]x\<close>
    AOT_hence \<open>\<not>[\<R>]\<^sup>*xx\<close> by (rule "\<beta>\<rightarrow>C"(1))
    moreover AOT_assume \<open>[\<R>]xy\<close>
    ultimately AOT_have \<open>\<not>[\<R>]\<^sup>*yy\<close>
      using "1-1-R:2"[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] by blast
    AOT_thus \<open>[\<lambda>z \<not>[\<R>\<^sup>*]zz]y\<close>
      by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2")
  qed
  AOT_thus \<open>\<not>[\<R>]\<^sup>*yy\<close>
    using "\<beta>\<rightarrow>C"(1) by blast
qed

AOT_theorem "1-1-R:4": \<open>[\<R>]\<^sup>*xy \<rightarrow> InDomainOf(x,\<R>)\<close>
proof(rule "\<rightarrow>I"; rule "df-1-1:5"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_assume 1: \<open>[\<R>]\<^sup>*xy\<close>
  AOT_have \<open>[\<lambda>z [\<R>\<^sup>*]xz \<rightarrow> \<exists>y [\<R>]xy]y\<close>
  proof (safe intro!: "anc-her:2"[unvarify F, THEN "\<rightarrow>E"];
         safe intro!: "cqt:2" "&I" GEN "\<rightarrow>I" "hered:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
    AOT_show \<open>[\<R>]\<^sup>*xy\<close> by (fact 1)
  next
    fix z
    AOT_assume \<open>[\<R>]xz\<close>
    AOT_thus \<open>[\<lambda>z [\<R>\<^sup>*]xz \<rightarrow> \<exists>y [\<R>]xy]z\<close>
      by (safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2")
         (meson "\<rightarrow>I" "existential:2[const_var]")
  next
    fix x' y
    AOT_assume Rx'y: \<open>[\<R>]x'y\<close>
    AOT_assume \<open>[\<lambda>z [\<R>\<^sup>*]xz \<rightarrow> \<exists>y [\<R>]xy]x'\<close>
    AOT_hence 0: \<open>[\<R>\<^sup>*]xx' \<rightarrow> \<exists>y [\<R>]xy\<close> by (rule "\<beta>\<rightarrow>C"(1))
    AOT_have 1: \<open>[\<R>\<^sup>*]xy \<rightarrow> \<exists>y [\<R>]xy\<close>
    proof(rule "\<rightarrow>I")
      AOT_assume \<open>[\<R>]\<^sup>*xy\<close>
      AOT_hence \<open>[\<R>]\<^sup>+xx'\<close> by (metis Rx'y "&I" "1-1-R:1" "\<rightarrow>E")
      AOT_hence \<open>[\<R>]\<^sup>*xx' \<or> x =\<^sub>\<R> x'\<close> by (metis "\<equiv>E"(1) "w-ances")
      moreover {
        AOT_assume \<open>[\<R>]\<^sup>*xx'\<close>
        AOT_hence \<open>\<exists>y [\<R>]xy\<close> using 0 by (metis "\<rightarrow>E")
      }
      moreover {
        AOT_assume \<open>x =\<^sub>\<R> x'\<close>
        AOT_hence \<open>x = x'\<close> by (metis "id-R-thm:3" "\<rightarrow>E")
        AOT_hence \<open>[\<R>]xy\<close> using Rx'y "rule=E" id_sym by fast
        AOT_hence \<open>\<exists>y [\<R>]xy\<close> by (rule "\<exists>I")
      }
      ultimately AOT_show \<open>\<exists>y [\<R>]xy\<close>
        by (metis "\<or>E"(3) "reductio-aa:1")
    qed
    AOT_show \<open>[\<lambda>z [\<R>\<^sup>*]xz \<rightarrow> \<exists>y [\<R>]xy]y\<close>
      by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" 1)
  qed
  AOT_hence \<open>[\<R>\<^sup>*]xy \<rightarrow> \<exists>y [\<R>]xy\<close> by (rule "\<beta>\<rightarrow>C"(1))
  AOT_thus \<open>\<exists>y [\<R>]xy\<close> using 1 "\<rightarrow>E" by blast
qed

AOT_theorem "1-1-R:5": \<open>[\<R>]\<^sup>+xy \<rightarrow> InDomainOf(x,\<R>)\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>[\<R>]\<^sup>+xy\<close>
  AOT_hence \<open>[\<R>]\<^sup>*xy \<or> x =\<^sub>\<R> y\<close>
    by (metis "\<equiv>E"(1) "w-ances")
  moreover {
    AOT_assume \<open>[\<R>]\<^sup>*xy\<close>
    AOT_hence \<open>InDomainOf(x,\<R>)\<close>
      using "1-1-R:4" "\<rightarrow>E" by blast
  }
  moreover {
    AOT_assume \<open>x =\<^sub>\<R> y\<close>
    AOT_hence \<open>InDomainOf(x,\<R>)\<close>
      by (metis "Conjunction Simplification"(1) "id-R-thm:2" "\<rightarrow>E")
  }
  ultimately AOT_show \<open>InDomainOf(x,\<R>)\<close>
    by (metis "\<or>E"(3) "reductio-aa:1")
qed

AOT_theorem "pre-ind":
  \<open>([F]z & \<forall>x\<forall>y(([\<R>]\<^sup>+zx & [\<R>]\<^sup>+zy) \<rightarrow> ([\<R>]xy \<rightarrow> ([F]x \<rightarrow> [F]y)))) \<rightarrow>
   \<forall>x ([\<R>]\<^sup>+zx \<rightarrow> [F]x)\<close>
proof(safe intro!: "\<rightarrow>I" GEN)
  AOT_have den: \<open>[\<lambda>y [F]y & [\<R>]\<^sup>+zy]\<down>\<close> by "cqt:2"
  fix x
  AOT_assume \<theta>: \<open>[F]z & \<forall>x\<forall>y(([\<R>]\<^sup>+zx & [\<R>]\<^sup>+zy) \<rightarrow> ([\<R>]xy \<rightarrow> ([F]x \<rightarrow> [F]y)))\<close>
  AOT_assume 0: \<open>[\<R>]\<^sup>+zx\<close>

  AOT_have \<open>[\<lambda>y [F]y & [\<R>]\<^sup>+zy]x\<close>
  proof (rule "w-ances-her:2"[unvarify F, OF den, THEN "\<rightarrow>E"]; safe intro!: "&I")
    AOT_show \<open>[\<lambda>y [F]y & [\<R>]\<^sup>+zy]z\<close>
    proof (safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I")
      AOT_show \<open>[F]z\<close> using \<theta> "&E" by blast
    next
      AOT_show \<open>[\<R>]\<^sup>+zz\<close>
        by (rule "w-ances"[THEN "\<equiv>E"(2), OF "\<or>I"(2)])
           (meson "0" "id-R-thm:5" "1-1-R:5" "\<rightarrow>E")
    qed
  next
    AOT_show \<open>[\<R>]\<^sup>+zx\<close> by (fact 0)
  next
    AOT_show \<open>Hereditary([\<lambda>y [F]y & [\<R>]\<^sup>+zy],\<R>)\<close>
    proof (safe intro!: "hered:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" GEN "\<rightarrow>I")
      fix x' y
      AOT_assume 1: \<open>[\<R>]x'y\<close>
      AOT_assume \<open>[\<lambda>y [F]y & [\<R>]\<^sup>+zy]x'\<close>
      AOT_hence 2: \<open>[F]x' & [\<R>]\<^sup>+zx'\<close> by (rule "\<beta>\<rightarrow>C"(1))
      AOT_have \<open>[\<R>]\<^sup>*zy\<close> using 1 2[THEN "&E"(2)]
        by (metis Adjunction "modus-tollens:1" "reductio-aa:1" "w-ances-her:3")
      AOT_hence 3: \<open>[\<R>]\<^sup>+zy\<close> by (metis "\<or>I"(1) "\<equiv>E"(2) "w-ances")
      AOT_show \<open>[\<lambda>y [F]y & [\<R>]\<^sup>+zy]y\<close>
      proof (safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" 3)
        AOT_show \<open>[F]y\<close>
        proof (rule \<theta>[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<forall>E"(2),
                      THEN "\<rightarrow>E", THEN "\<rightarrow>E", THEN "\<rightarrow>E"])
          AOT_show \<open>[\<R>]\<^sup>+zx' & [\<R>]\<^sup>+zy\<close>
            using 2 3 "&E" "&I" by blast
        next
          AOT_show \<open>[\<R>]x'y\<close> by (fact 1)
        next
          AOT_show \<open>[F]x'\<close> using 2 "&E" by blast
        qed
      qed
    qed
  qed
  AOT_thus \<open>[F]x\<close> using "\<beta>\<rightarrow>C"(1) "&E"(1) by fast
qed

text\<open>The following are not part of PLM, but theorems of AOT, in preparation
     of the construction of the predecessor axiom.\<close>
AOT_theorem unique_subst:
  assumes \<open>\<forall>x (\<phi>{x} \<equiv> \<psi>{x})\<close>
  shows \<open>\<exists>!x \<phi>{x} \<equiv> \<exists>!x \<psi>{x}\<close>
proof -
  {
    fix \<phi> \<psi>
    AOT_assume 0: \<open>\<forall>x (\<phi>{x} \<equiv> \<psi>{x})\<close>
    AOT_assume \<open>\<exists>!x \<phi>{x}\<close>
    AOT_hence \<open>\<exists>x (\<phi>{x} & \<forall>y (\<phi>{y} \<rightarrow> y = x))\<close>
      using "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
    then AOT_obtain x where \<phi>_prop: \<open>\<phi>{x} & \<forall>y (\<phi>{y} \<rightarrow> y = x)\<close>
      using "\<exists>E"[rotated] by blast
    AOT_have \<open>\<psi>{x} & \<forall>y (\<psi>{y} \<rightarrow> y = x)\<close>
    proof(safe intro!: "&I" GEN "\<rightarrow>I")
      AOT_show \<open>\<psi>{x}\<close>
        using 0[THEN "\<forall>E"(2), THEN "\<equiv>E"(1), OF \<phi>_prop[THEN "&E"(1)]].
    next
      fix y
      AOT_assume \<open>\<psi>{y}\<close>
      AOT_hence \<open>\<phi>{y}\<close>
        using 0[THEN "\<forall>E"(2), THEN "\<equiv>E"(2)] by blast
      AOT_thus \<open>y = x\<close>
        using \<phi>_prop[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
    qed
    AOT_hence \<open>\<exists>x(\<psi>{x} & \<forall>y (\<psi>{y} \<rightarrow> y = x))\<close>
      by (rule "\<exists>I")
    AOT_hence \<open>\<exists>!x \<psi>{x}\<close>
      using "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
  }
  moreover AOT_have \<open>\<forall>x (\<psi>{x} \<equiv> \<phi>{x})\<close>
    using assms  "cqt-basic:11" "\<equiv>E"(1,2) "\<equiv>I" "\<rightarrow>I" by blast
  ultimately AOT_show \<open>\<exists>!x \<phi>{x} \<equiv> \<exists>!x \<psi>{x}\<close>
    using "\<equiv>I" "\<rightarrow>I" assms by auto
qed
AOT_theorem unique_substD:
  assumes \<open>\<forall>x (\<phi>{x} \<equiv> \<psi>{x})\<close>
  shows \<open>\<exists>!\<^sub>Dx \<phi>{x} \<equiv> \<exists>!\<^sub>Dx \<psi>{x}\<close>
proof -
  AOT_have \<open>\<exists>!\<^sub>Dx \<phi>{x} \<equiv> \<exists>\<alpha> (\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>))\<close> 
    using "equi:1"[THEN "\<equiv>Df"].
  also AOT_have \<open>\<dots> \<equiv> \<exists>\<alpha> (\<psi>{\<alpha>} & \<forall>\<beta> (\<psi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>))\<close>
  proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
    AOT_assume \<open>\<exists>\<alpha> (\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>))\<close>
    then AOT_obtain \<alpha> where \<open>\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>)\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>\<psi>{\<alpha>} & \<forall>\<beta> (\<psi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>)\<close>
      using assms[THEN "\<forall>E"(2), THEN "\<equiv>E"(2)]
      using assms[THEN "\<forall>E"(2), THEN "\<equiv>E"(1)]
      by (auto intro!: "&I" GEN "\<rightarrow>I" dest: "&E" "\<forall>E"(2) "\<rightarrow>E")
    AOT_thus \<open>\<exists>\<alpha> (\<psi>{\<alpha>} & \<forall>\<beta> (\<psi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>))\<close>
      by (rule "\<exists>I")
  next
    AOT_assume \<open>\<exists>\<alpha> (\<psi>{\<alpha>} & \<forall>\<beta> (\<psi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>))\<close>
    then AOT_obtain \<alpha> where \<open>\<psi>{\<alpha>} & \<forall>\<beta> (\<psi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>)\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>)\<close>
      using assms[THEN "\<forall>E"(2), THEN "\<equiv>E"(1)]
      using assms[THEN "\<forall>E"(2), THEN "\<equiv>E"(2)]
      by (auto intro!: "&I" GEN "\<rightarrow>I" dest: "&E" "\<forall>E"(2) "\<rightarrow>E")
    AOT_thus \<open>\<exists>\<alpha> (\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>))\<close>
      by (rule "\<exists>I")
  qed
  also AOT_have \<open>\<dots> \<equiv> \<exists>!\<^sub>Dx \<psi>{x}\<close>
    using "equi:1"[THEN "\<equiv>Df", symmetric].
  finally show ?thesis.
qed

AOT_theorem uniqueD_act: \<open>\<exists>!\<^sub>Dx \<^bold>\<A>\<phi>{x} \<equiv> \<^bold>\<A>\<exists>!\<^sub>Dx \<phi>{x}\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I" "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] dest!: "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"])
  AOT_assume \<open>\<exists>\<alpha> (\<^bold>\<A>\<phi>{\<alpha>} & \<forall>\<beta> (\<^bold>\<A>\<phi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>))\<close>
  then AOT_obtain \<alpha> where 1: \<open>\<^bold>\<A>\<phi>{\<alpha>} & \<forall>\<beta> (\<^bold>\<A>\<phi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>)\<close>
    using "\<exists>E"[rotated] by blast
  AOT_have \<open>\<^bold>\<A>(\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>))\<close>
  proof(safe intro!: "Act-Basic:2"[THEN "\<equiv>E"(2)] "&I" "logic-actual-nec:3"[axiom_inst, THEN "\<equiv>E"(2)]
                     "logic-actual-nec:2"[axiom_inst, THEN "\<equiv>E"(2)] "\<rightarrow>I" GEN)
    AOT_show \<open>\<^bold>\<A>\<phi>{\<alpha>}\<close> using 1 "&E" by blast
  next
    fix \<beta>
    AOT_assume \<open>\<^bold>\<A>\<phi>{\<beta>}\<close>
    AOT_hence \<open>\<beta> =\<^sub>D \<alpha>\<close>
      using 1 "&E" "\<rightarrow>E" "\<forall>E" by blast
    AOT_thus \<open>\<^bold>\<A>\<beta> =\<^sub>D \<alpha>\<close>
      using "id-nec4:1" "intro-elim:3:a" "nec-imp-act" "vdash-properties:10" by blast
  qed
  AOT_hence \<open>\<exists>\<alpha> \<^bold>\<A>(\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>))\<close>
    by (rule "\<exists>I")
  AOT_hence \<open>\<^bold>\<A>\<exists>\<alpha> (\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>))\<close>
    using "Act-Basic:10"[THEN "\<equiv>E"(2)] by fast
  AOT_thus \<open>\<^bold>\<A>\<exists>!\<^sub>Dx \<phi>{x}\<close>
    by (AOT_subst_def "equi:1")
next
  AOT_assume \<open>\<^bold>\<A>\<exists>!\<^sub>Dx \<phi>{x}\<close>
  AOT_hence \<open>\<^bold>\<A>\<exists>\<alpha> (\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>))\<close>
    by (AOT_subst_def (reverse) "equi:1")
  AOT_hence \<open>\<exists>\<alpha> \<^bold>\<A>(\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>))\<close>
    using "Act-Basic:10"[THEN "\<equiv>E"(1)] by fast
  then AOT_obtain \<alpha> where \<open>\<^bold>\<A>(\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>))\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<open>\<^bold>\<A>\<phi>{\<alpha>}\<close> and 0: \<open>\<^bold>\<A>\<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>)\<close>
    using "Act-Basic:2"[THEN "\<equiv>E"(1)] "&E" by blast+
  AOT_hence \<open>\<^bold>\<A>\<phi>{\<alpha>} & \<forall>\<beta> (\<^bold>\<A>\<phi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>)\<close>
  proof (safe intro!: "&I" GEN "\<rightarrow>I")
    fix \<beta>
    AOT_assume \<open>\<^bold>\<A>\<phi>{\<beta>}\<close>
    AOT_hence \<open>\<^bold>\<A>\<beta> =\<^sub>D \<alpha>\<close>
      using 0 "logic-actual-nec:3"[axiom_inst, THEN "\<equiv>E"(1), THEN "\<forall>E"(2)]
        "logic-actual-nec:2"[axiom_inst, THEN "\<equiv>E"(1), THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>\<diamond>\<beta> =\<^sub>D \<alpha>\<close>
      by (metis "Act-Sub:3" "vdash-properties:10")
    AOT_hence \<open>\<box>\<beta> =\<^sub>D \<alpha>\<close>
      apply (safe_step intro!: "sc-eq-box-box:1"[THEN "\<equiv>E"(1), THEN "\<rightarrow>E"])
       apply (rule RN)
      using "id-nec4:1" "\<rightarrow>I" "intro-elim:3:a" apply blast
      by blast
    AOT_thus \<open>\<beta> =\<^sub>D \<alpha>\<close>
      using "id-nec4:1"[THEN "\<equiv>E"(2)] by blast
  qed
  AOT_thus \<open>\<exists>\<alpha>(\<^bold>\<A>\<phi>{\<alpha>} & \<forall>\<beta> (\<^bold>\<A>\<phi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>))\<close>
    by (rule "\<exists>I")
qed


AOT_theorem act_approx_lem: \<open>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[G]z] \<equiv> \<^bold>\<A>F \<approx>\<^sub>D G\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[G]z]\<close>
  AOT_hence \<open>\<exists>R R |: [\<lambda>z \<^bold>\<A>[F]z] \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D [\<lambda>z \<^bold>\<A>[G]z]\<close>
    using "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain R where \<open>R |: [\<lambda>z \<^bold>\<A>[F]z] \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D [\<lambda>z \<^bold>\<A>[G]z]\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<open>R\<down> & [\<lambda>z \<^bold>\<A>[F]z]\<down> & [\<lambda>z \<^bold>\<A>[G]z]\<down> & \<forall>u ([\<lambda>z \<^bold>\<A>[F]z]u \<rightarrow> \<exists>!\<^sub>Dv ([\<lambda>z \<^bold>\<A>[G]z]v & [R]uv)) & \<forall>v ([\<lambda>z \<^bold>\<A>[G]z]v \<rightarrow> \<exists>!\<^sub>Du ([\<lambda>z \<^bold>\<A>[F]z]u & [R]uv))\<close>
    using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_hence F_imp: \<open>\<forall>u ([\<lambda>z \<^bold>\<A>[F]z]u \<rightarrow> \<exists>!\<^sub>Dv ([\<lambda>z \<^bold>\<A>[G]z]v & [R]uv))\<close>
        and G_imp: \<open>\<forall>v ([\<lambda>z \<^bold>\<A>[G]z]v \<rightarrow> \<exists>!\<^sub>Du ([\<lambda>z \<^bold>\<A>[F]z]u & [R]uv))\<close>
    using "&E" by blast+
  AOT_obtain R' where \<open>Rigidifies(R',R)\<close>
    using "rigid-der:3" "\<exists>E"[rotated] by blast
  AOT_hence 1: \<open>Rigid(R') & \<forall>x\<^sub>1...\<forall>x\<^sub>n ([R']x\<^sub>1...x\<^sub>n \<equiv> [R]x\<^sub>1...x\<^sub>n)\<close>
    using "df-rigid-rel:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_hence \<open>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([R']x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[R']x\<^sub>1...x\<^sub>n)\<close>
    using "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_hence \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n (\<diamond>[R']x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[R']x\<^sub>1...x\<^sub>n)\<close>
    using "\<equiv>E"(1) "rigid-rel-thms:1" by blast
  AOT_hence D: \<open>\<forall>x\<^sub>1\<forall>x\<^sub>2 (\<diamond>[R']x\<^sub>1x\<^sub>2 \<rightarrow> \<box>[R']x\<^sub>1x\<^sub>2)\<close>
    using tuple_forall[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_have E: \<open>\<forall>x\<^sub>1\<forall>x\<^sub>2 ([R']x\<^sub>1x\<^sub>2 \<equiv> [R]x\<^sub>1x\<^sub>2)\<close>
    using tuple_forall[THEN "\<equiv>\<^sub>d\<^sub>fE", OF 1[THEN "&E"(2)]] by blast
  {
    fix x y
    AOT_assume \<open>[R]xy\<close>
    AOT_hence \<open>[R']xy\<close>
      using E[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<equiv>E"(2)] by blast
    AOT_hence \<open>\<diamond>[R']xy\<close> using "T-S5-fund:1"[THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>\<box>[R']xy\<close> using D[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>\<^bold>\<A>[R']xy\<close> using "nec-imp-act"[THEN "\<rightarrow>E"] by blast
  } note rigid1 = this
  {
    fix x y
    AOT_assume \<open>\<^bold>\<A>[R']xy\<close>
    AOT_hence \<open>\<diamond>[R']xy\<close>
      using "Act-Sub:3"[THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>\<box>[R']xy\<close> using D[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>[R']xy\<close>
      using "qml:2"[axiom_inst, THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>[R]xy\<close>
      using E[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<equiv>E"(1)] by blast
  } note rigid2 = this
  {
    {
      fix u
      AOT_have \<open>\<^bold>\<A>[F]u \<rightarrow> \<^bold>\<A>\<exists>!\<^sub>Dv ([G]v & [R']uv)\<close>
      proof(rule "\<rightarrow>I")
        AOT_assume \<open>\<^bold>\<A>[F]u\<close>
        AOT_hence \<open>[\<lambda>z \<^bold>\<A>[F]z]u\<close>
          by (safe intro!: "betaC:2:a" "cqt:2")
        AOT_hence \<open>\<exists>!\<^sub>Dv ([\<lambda>z \<^bold>\<A>[G]z]v & [R]uv)\<close>
          using F_imp[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
        moreover {
          AOT_have \<open>\<^bold>\<A>[G]x\<close> if \<open>[\<lambda>z \<^bold>\<A>[G]z]x\<close> for x
            using "betaC:1:a" that by blast
          moreover AOT_have \<open>[\<lambda>z \<^bold>\<A>[G]z]x\<close> if \<open>\<^bold>\<A>[G]x\<close> for x
            by (safe intro!: that "cqt:2" "betaC:2:a")
          ultimately AOT_have \<open>\<forall>x ((([\<lambda>z \<^bold>\<A>[G]z]x & [R]ux)) \<equiv> ((\<^bold>\<A>[G]x & \<^bold>\<A>[R']ux)))\<close>
            using rigid1 rigid2
            by(auto intro!: GEN "\<rightarrow>I" "\<equiv>I" "&I" dest: "&E")
        } 
        ultimately AOT_have \<open>\<exists>!\<^sub>Dv (\<^bold>\<A>[G]v & \<^bold>\<A>[R']uv)\<close>
          using unique_substD "\<equiv>E"(1) by fast
        AOT_hence \<open>\<exists>!\<^sub>Dv \<^bold>\<A>([G]v & [R']uv)\<close>
          by (AOT_subst \<open>\<^bold>\<A>([G]v & [R']uv)\<close> \<open>\<^bold>\<A>[G]v & \<^bold>\<A>[R']uv\<close> for: v)
              (auto simp: "Act-Basic:2")
        AOT_thus \<open>\<^bold>\<A>\<exists>!\<^sub>Dv ([G]v & [R']uv)\<close>
          by (metis "intro-elim:3:a" uniqueD_act)
      qed
      AOT_hence \<open>\<^bold>\<A>([F]u \<rightarrow> \<exists>!\<^sub>Dv ([G]v & [R']uv))\<close>
        using "logic-actual-nec:2"[axiom_inst, THEN "\<equiv>E"(2)] by blast
    }
    AOT_hence \<open>\<forall>u \<^bold>\<A>([F]u \<rightarrow> \<exists>!\<^sub>Dv ([G]v & [R']uv))\<close> by (rule "GEN")
    AOT_hence \<open>\<^bold>\<A>\<forall>u ([F]u \<rightarrow> \<exists>!\<^sub>Dv ([G]v & [R']uv))\<close>
      using "logic-actual-nec:3"[axiom_inst, THEN "\<equiv>E"(2)] by fast
  }
  moreover {
    {
      fix v
      AOT_have \<open>\<^bold>\<A>[G]v \<rightarrow> \<^bold>\<A>\<exists>!\<^sub>Du ([F]u & [R']uv)\<close>
      proof(rule "\<rightarrow>I")
        AOT_assume \<open>\<^bold>\<A>[G]v\<close>
        AOT_hence \<open>[\<lambda>z \<^bold>\<A>[G]z]v\<close>
          by (safe intro!: "betaC:2:a" "cqt:2")
        AOT_hence \<open>\<exists>!\<^sub>Du ([\<lambda>z \<^bold>\<A>[F]z]u & [R]uv)\<close>
          using G_imp[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
        moreover {
          AOT_have \<open>\<^bold>\<A>[F]x\<close> if \<open>[\<lambda>z \<^bold>\<A>[F]z]x\<close> for x
            using "betaC:1:a" that by blast
          moreover AOT_have \<open>[\<lambda>z \<^bold>\<A>[F]z]x\<close> if \<open>\<^bold>\<A>[F]x\<close> for x
            by (safe intro!: that "cqt:2" "betaC:2:a")
          ultimately AOT_have \<open>\<forall>x ((([\<lambda>z \<^bold>\<A>[F]z]x & [R]xv)) \<equiv> ((\<^bold>\<A>[F]x & \<^bold>\<A>[R']xv)))\<close>
            using rigid1 rigid2
            by(auto intro!: GEN "\<rightarrow>I" "\<equiv>I" "&I" dest: "&E")
        } 
        ultimately AOT_have \<open>\<exists>!\<^sub>Du (\<^bold>\<A>[F]u & \<^bold>\<A>[R']uv)\<close>
          using unique_substD "\<equiv>E"(1) by fast
        AOT_hence \<open>\<exists>!\<^sub>Du \<^bold>\<A>([F]u & [R']uv)\<close>
          by (AOT_subst \<open>\<^bold>\<A>([F]u & [R']uv)\<close> \<open>\<^bold>\<A>[F]u & \<^bold>\<A>[R']uv\<close> for: u)
              (auto simp: "Act-Basic:2")
        AOT_thus \<open>\<^bold>\<A>\<exists>!\<^sub>Du ([F]u & [R']uv)\<close>
           by (metis "intro-elim:3:a" uniqueD_act)
      qed
      AOT_hence \<open>\<^bold>\<A>([G]v \<rightarrow> \<exists>!\<^sub>Du ([F]u & [R']uv))\<close>
        using "logic-actual-nec:2"[axiom_inst, THEN "\<equiv>E"(2)] by blast
    }
    AOT_hence \<open>\<forall>v \<^bold>\<A>([G]v \<rightarrow> \<exists>!\<^sub>Du ([F]u & [R']uv))\<close> by (rule "GEN")
    AOT_hence \<open>\<^bold>\<A>\<forall>v ([G]v \<rightarrow> \<exists>!\<^sub>Du ([F]u & [R']uv))\<close>
      using "logic-actual-nec:3"[axiom_inst, THEN "\<equiv>E"(2)] by fast
  }
  ultimately AOT_have \<open>\<^bold>\<A>(R'\<down> & [F]\<down> & [G]\<down> & \<forall>u ([F]u \<rightarrow> \<exists>!\<^sub>Dv ([G]v & [R']uv)) & \<forall>v ([G]v \<rightarrow> \<exists>!\<^sub>Du ([F]u & [R']uv)))\<close>
    by (safe intro!: "Act-Basic:2"[THEN "\<equiv>E"(2)] "&I" "cqt:2[const_var]"[axiom_inst, THEN "RA[2]"])
  AOT_hence \<open>\<^bold>\<A>R' |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
    by (AOT_subst_def "equi:2")
  AOT_hence \<open>\<exists>R \<^bold>\<A>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
    by (rule "\<exists>I")
  AOT_hence \<open>\<^bold>\<A>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
    using "Act-Basic:10"[THEN "\<equiv>E"(2)] by fast
  AOT_thus \<open>\<^bold>\<A>F \<approx>\<^sub>D G\<close>
    by (AOT_subst_def "equi:3")
next 
  AOT_have prod_den: \<open>\<^bold>\<turnstile>\<^sub>\<box> \<guillemotleft>(AOT_term_of_var x\<^sub>1,AOT_term_of_var x\<^sub>2)\<guillemotright>\<down>\<close>
    for x\<^sub>1 x\<^sub>2 :: \<open>\<kappa> AOT_var\<close>
    by (simp add: "&I" "ex:1:a" tuple_denotes[THEN "\<equiv>\<^sub>d\<^sub>fI"] "rule-ui:3")
  AOT_have act_den: \<open>\<^bold>\<turnstile>\<^sub>\<box> [\<lambda>xy \<^bold>\<A>[R]xy]\<down>\<close> for R by "cqt:2"
  AOT_assume \<open>\<^bold>\<A>F \<approx>\<^sub>D G\<close>
  AOT_hence \<open>\<^bold>\<A>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
    by (AOT_subst_def (reverse) "equi:3")
  AOT_hence \<open>\<exists>R \<^bold>\<A>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
    using "Act-Basic:10"[THEN "\<equiv>E"(1)] by fast
  then AOT_obtain R where \<open>\<^bold>\<A>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<open>\<^bold>\<A>(R\<down> & [F]\<down> & [G]\<down> & \<forall>u ([F]u \<rightarrow> \<exists>!\<^sub>Dv ([G]v & [R]uv)) & \<forall>v ([G]v \<rightarrow> \<exists>!\<^sub>Du ([F]u & [R]uv)))\<close>
    by (AOT_subst_def (reverse) "equi:2")
  AOT_hence \<open>\<^bold>\<A>\<forall>u ([F]u \<rightarrow> \<exists>!\<^sub>Dv ([G]v & [R]uv))\<close> and \<open>\<^bold>\<A>\<forall>v ([G]v \<rightarrow> \<exists>!\<^sub>Du ([F]u & [R]uv))\<close>
    using "&E" "Act-Basic:2"[THEN "\<equiv>E"(1)] by blast+
  AOT_hence 0: \<open>\<forall>u \<^bold>\<A>([F]u \<rightarrow> \<exists>!\<^sub>Dv ([G]v & [R]uv))\<close> and 1:  \<open>\<forall>v \<^bold>\<A>([G]v \<rightarrow> \<exists>!\<^sub>Du ([F]u & [R]uv))\<close>
    using "logic-actual-nec:3"[axiom_inst, THEN "\<equiv>E"(1)] by blast+

  AOT_have \<open>[\<lambda>xy \<^bold>\<A>[R]xy]\<down> & [\<lambda>z \<^bold>\<A>[F]z]\<down> & [\<lambda>z \<^bold>\<A>[G]z]\<down>
            & \<forall>u ([\<lambda>z \<^bold>\<A>[F]z]u \<rightarrow> \<exists>!\<^sub>Dv ([\<lambda>z \<^bold>\<A>[G]z]v & [\<lambda>xy \<^bold>\<A>[R]xy]uv))
            & \<forall>v ([\<lambda>z \<^bold>\<A>[G]z]v \<rightarrow> \<exists>!\<^sub>Du([\<lambda>z \<^bold>\<A>[F]z]u & [\<lambda>xy \<^bold>\<A>[R]xy]uv))\<close>
  proof(safe intro!: "&I" "cqt:2" GEN "\<rightarrow>I")
    fix u
    AOT_assume \<open>[\<lambda>z \<^bold>\<A>[F]z]u\<close>
    AOT_hence \<open>\<^bold>\<A>[F]u\<close>
      using "\<beta>\<rightarrow>C" by blast
    AOT_hence \<open>\<^bold>\<A>\<exists>!\<^sub>Dv ([G]v & [R]uv)\<close>
      using 0[THEN "\<forall>E"(2), THEN "logic-actual-nec:2"[axiom_inst, THEN "\<equiv>E"(1)], THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>\<exists>!\<^sub>Dv \<^bold>\<A>([G]v & [R]uv)\<close>
      by (metis "intro-elim:3:b" uniqueD_act)
    AOT_thus \<open>\<exists>!\<^sub>Dv ([\<lambda>z \<^bold>\<A>[G]z]v & [\<lambda>xy \<^bold>\<A>[R]xy]uv)\<close>
      apply (AOT_subst \<open>[\<lambda>xy \<^bold>\<A>[R]xy]uv\<close> \<open>\<^bold>\<A>[R]uv\<close> for: v)
       apply (safe intro!: "\<equiv>I" "\<rightarrow>I" dest!: "\<beta>\<rightarrow>C")
       apply (rule "\<beta>\<leftarrow>C")
         apply (safe intro!: "cqt:2" tuple_denotes[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I")
      apply (AOT_subst \<open>[\<lambda>x \<^bold>\<A>[G]x]v\<close> \<open>\<^bold>\<A>[G]v\<close> for: v)
       apply (safe intro!: "cqt:2" "beta-C-meta"[THEN "\<rightarrow>E"])
      using unique_substD[THEN "\<equiv>E"(1), OF GEN]
        "Act-Basic:2" by fast
  next
    fix v
    AOT_assume \<open>[\<lambda>z \<^bold>\<A>[G]z]v\<close>
    AOT_hence \<open>\<^bold>\<A>[G]v\<close>
      using "\<beta>\<rightarrow>C" by blast
    AOT_hence \<open>\<^bold>\<A>\<exists>!\<^sub>Du ([F]u & [R]uv)\<close>
      using 1[THEN "\<forall>E"(2), THEN "logic-actual-nec:2"[axiom_inst, THEN "\<equiv>E"(1)], THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>\<exists>!\<^sub>Du \<^bold>\<A>([F]u & [R]uv)\<close>
      by (metis "intro-elim:3:b" uniqueD_act)
    AOT_thus \<open>\<exists>!\<^sub>Du ([\<lambda>z \<^bold>\<A>[F]z]u & [\<lambda>xy \<^bold>\<A>[R]xy]uv)\<close>
      apply (AOT_subst \<open>[\<lambda>xy \<^bold>\<A>[R]xy]uv\<close> \<open>\<^bold>\<A>[R]uv\<close> for: u)
       apply (safe intro!: "\<equiv>I" "\<rightarrow>I" dest!: "\<beta>\<rightarrow>C")
       apply (rule "\<beta>\<leftarrow>C")
         apply (safe intro!: "cqt:2" tuple_denotes[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I")
      apply (AOT_subst \<open>[\<lambda>x \<^bold>\<A>[F]x]u\<close> \<open>\<^bold>\<A>[F]u\<close> for: u)
       apply (safe intro!: "cqt:2" "beta-C-meta"[THEN "\<rightarrow>E"])
      using unique_substD[THEN "\<equiv>E"(1), OF GEN]
        "Act-Basic:2" by fast
  qed
  AOT_hence \<open>[\<lambda>xy \<^bold>\<A>[R]xy] |: [\<lambda>z \<^bold>\<A>[F]z] \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D [\<lambda>z \<^bold>\<A>[G]z]\<close>
    by (AOT_subst_def "equi:2")
  AOT_hence \<open>\<exists>R R |: [\<lambda>z \<^bold>\<A>[F]z] \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D [\<lambda>z \<^bold>\<A>[G]z]\<close>
    by (auto intro!: "\<exists>I"(1) "cqt:2")
  AOT_thus \<open>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[G]z]\<close>
    by (AOT_subst_def "equi:3")
qed

AOT_theorem disc_props_den: \<open>[\<lambda>x D!x & \<phi>{x}]\<down>\<close>
proof (safe intro!: "kirchner-thm:1"[THEN "\<equiv>E"(2)] RN "\<rightarrow>I" GEN)
  AOT_modally_strict {
    fix x y
    AOT_assume indist: \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
    AOT_assume x: \<open>D!x & \<phi>{x}\<close>
    AOT_hence Dx: \<open>D!x\<close> and \<phi>: \<open>\<phi>{x}\<close> using "&E" by blast+
    AOT_hence x_prop: \<open>\<box>\<forall>y (y \<noteq> x \<rightarrow> \<exists>F \<not>([F]y \<equiv> [F]x))\<close>
      using Discernible_equiv[THEN "\<equiv>E"(1)] by blast
    AOT_have \<open>y = x\<close>
    proof(rule "raa-cor:1")
      AOT_assume \<open>\<not>y = x\<close>
      AOT_hence \<open>y \<noteq> x\<close> using "=-infix" "\<equiv>\<^sub>d\<^sub>fI" by blast
      AOT_hence \<open>\<exists>F \<not>([F]y \<equiv> [F]x)\<close>
        using x_prop[THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"], THEN "\<forall>E"(2), THEN "\<rightarrow>E"]
        by blast
      then AOT_obtain F where \<open>\<not>([F]y \<equiv> [F]x)\<close> using "\<exists>E"[rotated] by blast
      moreover AOT_have \<open>[F]y \<equiv> [F]x\<close>
        using indist[THEN "\<forall>E"(2)] "\<equiv>E"(1,2) "\<rightarrow>I" "\<equiv>I" by metis
      ultimately AOT_show \<open>p & \<not>p\<close> for p using "reductio-aa:1" by blast
    qed
    AOT_hence \<open>x = y\<close>
      using id_sym by auto
    AOT_hence \<open>D!y & \<phi>{y}\<close>
      using x "rule=E" by fast
  } note 0 = this
  AOT_modally_strict {
    fix x y
    AOT_assume \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
    moreover AOT_have \<open>\<forall>F ([F]y \<equiv> [F]x)\<close>
      using calculation
      by (metis "cqt-basic:11" "intro-elim:3:b")
    ultimately AOT_show \<open>D!x & \<phi>{x} \<equiv> D!y & \<phi>{y}\<close>
      using 0 "\<equiv>I" "\<rightarrow>I" by auto
  }
qed

text\<open>The following not part of PLM or AOT, but part of the model construction.\<close>

lemma model_eqD[AOT_no_atp, no_atp]:
  \<open>[v \<Turnstile> \<kappa> =\<^sub>D \<kappa>'] = (AOT_model_denotes \<kappa> \<and> AOT_model_denotes \<kappa>' \<and> \<kappa>\<upsilon> \<kappa> = \<kappa>\<upsilon> \<kappa>')\<close>
proof
    AOT_world v
    AOT_assume \<open>\<kappa> =\<^sub>D \<kappa>'\<close>
    moreover AOT_have \<kappa>_den: \<open>\<kappa>\<down>\<close> and \<kappa>'_den: \<open>\<kappa>'\<down>\<close>
      using "russell-axiom[exe,2,1,2].\<psi>_denotes_asm"
            "russell-axiom[exe,2,1,1].\<psi>_denotes_asm" calculation by blast+
  ultimately AOT_have \<open>\<box>\<forall>F([F]\<kappa> \<equiv> [F]\<kappa>')\<close>
    using "=D-simple:1"[unvarify x, unvarify y, THEN "\<equiv>E"(1)]
    by blast
  AOT_hence \<open>\<forall>F([F]\<kappa> \<equiv> [F]\<kappa>')\<close>
    using "qml:2"[axiom_inst, THEN "\<rightarrow>E"] by blast
  moreover AOT_have lam_den: \<open>[\<lambda>x \<guillemotleft> \<epsilon>\<^sub>\<o> w . \<kappa>\<upsilon> x = \<kappa>\<upsilon> \<kappa>\<guillemotright>]\<down>\<close>
    by (simp add: AOT_model_lambda_denotes AOT_model_term_equiv_\<kappa>_def AOT_sem_denotes)
  ultimately AOT_have
    \<open>[\<lambda>x \<guillemotleft> \<epsilon>\<^sub>\<o> w . \<kappa>\<upsilon> x = \<kappa>\<upsilon> \<kappa>\<guillemotright>]\<kappa> \<equiv>
     [\<lambda>x \<guillemotleft> \<epsilon>\<^sub>\<o> w . \<kappa>\<upsilon> x = \<kappa>\<upsilon> \<kappa>\<guillemotright>]\<kappa>'\<close>
    using "\<forall>E"(1) by blast
  moreover AOT_have \<open>[\<lambda>x \<guillemotleft> \<epsilon>\<^sub>\<o> w . \<kappa>\<upsilon> x = \<kappa>\<upsilon> \<kappa>\<guillemotright>]\<kappa>\<close>
    by (auto intro!: "\<beta>\<leftarrow>C" lam_den \<kappa>_den simp: AOT_model_proposition_choice_simp)
  ultimately AOT_have \<open>[\<lambda>x \<guillemotleft> \<epsilon>\<^sub>\<o> w . \<kappa>\<upsilon> x = \<kappa>\<upsilon> \<kappa>\<guillemotright>]\<kappa>'\<close>
    using "\<equiv>E" by blast
  AOT_hence \<open>\<guillemotleft> \<epsilon>\<^sub>\<o> w . \<kappa>\<upsilon> \<kappa>' = \<kappa>\<upsilon> \<kappa>\<guillemotright>\<close>
    by (rule "\<beta>\<rightarrow>C")
  thus \<open>AOT_model_denotes \<kappa> \<and> AOT_model_denotes \<kappa>' \<and> \<kappa>\<upsilon> \<kappa> = \<kappa>\<upsilon> \<kappa>'\<close>
    using  \<kappa>'_den \<kappa>_den
    by (auto simp: AOT_model_proposition_choice_simp AOT_sem_denotes)
next
  AOT_world v
    assume 0: \<open>AOT_model_denotes \<kappa> \<and> AOT_model_denotes \<kappa>' \<and> \<kappa>\<upsilon> \<kappa> = \<kappa>\<upsilon> \<kappa>'\<close>
    hence 1: \<open>AOT_model_term_equiv \<kappa> \<kappa>'\<close>
      using AOT_model_term_equiv_\<kappa>_def by presburger
      AOT_have \<kappa>_den: \<open>\<kappa>\<down>\<close> and \<kappa>'_den: \<open>\<kappa>'\<down>\<close>
        using 0
      by (auto simp add: AOT_sem_denotes)
  AOT_have \<open>\<forall>F([F]\<kappa> \<equiv> [F]\<kappa>')\<close>
    apply(safe intro!: GEN "\<equiv>I" "\<rightarrow>I")
    using "1" AOT_sem_exe_equiv by fastforce+
  AOT_hence \<open>\<box>\<forall>F([F]\<kappa> \<equiv> [F]\<kappa>')\<close>
    by (safe intro!: "ind-nec"[unvarify x y, THEN "\<rightarrow>E"] \<kappa>_den \<kappa>'_den)
  AOT_thus \<open>\<kappa> =\<^sub>D \<kappa>'\<close>
    by (safe intro!: "=D-simple:1"[unvarify x y, THEN "\<equiv>E"(2)] \<kappa>_den \<kappa>'_den)
qed

lemma
  model_ex1D[AOT_no_atp, no_atp]:
  assumes \<open>AOT_instance_of_cqt_2 \<phi>\<close>
  shows \<open>[v \<Turnstile> \<exists>!\<^sub>D x \<phi>{x}] = (\<exists>!u . \<not>is_null\<upsilon> u \<and> [v \<Turnstile> \<phi>{\<guillemotleft>inv \<kappa>\<upsilon> u\<guillemotright>}])\<close>
proof
  AOT_world v
  AOT_assume \<open>\<exists>!\<^sub>D x \<phi>{x}\<close>
  AOT_hence \<open>\<exists>x (\<phi>{x} & \<forall>y (\<phi>{y} \<rightarrow> y =\<^sub>D x))\<close>
    using "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain x where x_prop: \<open>\<phi>{x} & \<forall>y (\<phi>{y} \<rightarrow> y =\<^sub>D x)\<close>
    using "\<exists>E"[rotated] by blast
  define u where \<open>u = \<kappa>\<upsilon> (AOT_term_of_var x)\<close>
  have 1: \<open>AOT_model_term_equiv (inv \<kappa>\<upsilon> u) (AOT_term_of_var x)\<close>
    by (simp add: AOT_model_term_equiv_\<kappa>_def \<kappa>\<upsilon>_surj surj_f_inv_f u_def)
  moreover have  2:\<open>AOT_model_denotes (AOT_term_of_var x)\<close>
    by (simp add: AOT_model.AOT_term_of_var)
  moreover have 3: \<open>AOT_model_denotes (inv \<kappa>\<upsilon> u)\<close>
    using calculation
    by (metis AOT_model_term_equiv_denotes)
  ultimately have 4: \<open>\<phi> (AOT_term_of_var x) = \<phi> (inv \<kappa>\<upsilon> u)\<close>
    using assms unfolding AOT_instance_of_cqt_2_def by auto
  show \<open>\<exists>!u . \<not>is_null\<upsilon> u \<and> [v \<Turnstile> \<phi>{\<guillemotleft>inv \<kappa>\<upsilon> u\<guillemotright>}]\<close>
  proof(rule ex1I)
    show \<open>\<not>is_null\<upsilon> u \<and> [v \<Turnstile> \<phi>{\<guillemotleft>inv \<kappa>\<upsilon> u\<guillemotright>}]\<close>
      apply safe
       apply (metis AOT_model.AOT_term_of_var AOT_model_denotes_\<kappa>_def \<kappa>.exhaust_disc
                    \<kappa>\<upsilon>.simps(1) \<kappa>\<upsilon>.simps(2) \<upsilon>.disc(7) \<upsilon>.disc(8) is_\<alpha>\<kappa>_def is_\<omega>\<kappa>_def u_def)
      by (metis "con-dis-i-e:2:a" "local.4" x_prop)
  next
    fix u'
    assume \<open>\<not>is_null\<upsilon> u' \<and> [v \<Turnstile> \<phi>{\<guillemotleft>inv \<kappa>\<upsilon> u'\<guillemotright>}]\<close>
    moreover AOT_have \<open>\<guillemotleft>inv \<kappa>\<upsilon> u'\<guillemotright>\<down>\<close>
      by (metis AOT_model_denotes_\<kappa>_def AOT_sem_denotes \<kappa>\<upsilon>.simps(3) \<kappa>\<upsilon>_surj
                is_null\<kappa>_def is_null\<upsilon>_def surj_f_inv_f calculation)
    ultimately AOT_have \<open>\<guillemotleft>inv \<kappa>\<upsilon> u'\<guillemotright> =\<^sub>D x\<close>
      using x_prop[THEN "&E"(2), THEN "\<forall>E"(1), THEN "\<rightarrow>E"]
      by blast
    thus \<open>u' = u\<close>
      unfolding u_def model_eqD
      by (simp add: \<kappa>\<upsilon>_surj surj_f_inv_f)
  qed
next
  AOT_world v
  assume \<open>\<exists>!u . \<not>is_null\<upsilon> u \<and> [v \<Turnstile> \<phi>{\<guillemotleft>inv \<kappa>\<upsilon> u\<guillemotright>}]\<close>
  then obtain u where u_prop: \<open>\<not>is_null\<upsilon> u \<and> [v \<Turnstile> \<phi>{\<guillemotleft>inv \<kappa>\<upsilon> u\<guillemotright>}]\<close> and
      u_prop': \<open>\<And>u' . \<not>is_null\<upsilon> u' \<and> [v \<Turnstile> \<phi>{\<guillemotleft>inv \<kappa>\<upsilon> u'\<guillemotright>}] \<Longrightarrow> u' = u\<close>
    by metis
  hence 0: \<open>AOT_model_denotes (inv \<kappa>\<upsilon> u)\<close>
    by (metis AOT_model_denotes_\<kappa>_def \<kappa>\<upsilon>.simps(3) \<kappa>\<upsilon>_surj is_null\<kappa>_def
              is_null\<upsilon>_def surj_f_inv_f)
  AOT_hence \<open>\<guillemotleft>inv \<kappa>\<upsilon> u\<guillemotright>\<down>\<close>
    by (simp add: AOT_sem_denotes)
  moreover AOT_have \<open>\<phi>{\<guillemotleft>inv \<kappa>\<upsilon> u\<guillemotright>} & \<forall>y (\<phi>{y} \<rightarrow> y =\<^sub>D \<guillemotleft>inv \<kappa>\<upsilon> u\<guillemotright>)\<close>
  proof(safe intro!: "&I" GEN "\<rightarrow>I" u_prop[THEN conjunct2])
    fix y
    AOT_assume \<open>\<phi>{y}\<close>
    moreover have \<open>\<kappa>\<upsilon> (inv \<kappa>\<upsilon> u) = u\<close>
      by (simp add: \<kappa>\<upsilon>_surj surj_f_inv_f)
    moreover have 1: \<open>\<kappa>\<upsilon> (AOT_term_of_var y) = u\<close>
      by (smt (verit, best) AOT_instance_of_cqt_2_def AOT_model.AOT_term_of_var
          AOT_model_denotes_\<kappa>_def AOT_model_term_equiv_\<kappa>_def
          AOT_model_term_equiv_denotes \<kappa>\<upsilon>.simps(3) \<kappa>\<upsilon>_surj assms
          calculation(1) is_null\<kappa>_def is_null\<upsilon>_def surj_f_inv_f u_prop')
    ultimately AOT_show \<open>y =\<^sub>D \<guillemotleft>inv \<kappa>\<upsilon> u\<guillemotright>\<close>
      by (auto simp: model_eqD 0 AOT_model.AOT_term_of_var)
  qed
  ultimately AOT_have \<open>\<exists>x (\<phi>{x} & \<forall>y (\<phi>{y} \<rightarrow> y =\<^sub>D x))\<close>
    by (auto intro: "\<exists>I")
  AOT_thus \<open>\<exists>!\<^sub>D x \<phi>{x}\<close>
    using "equi:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
qed


lemma model_equinum_bij[AOT_no_atp, no_atp]:
  \<open>[w\<^sub>0 \<Turnstile> \<Pi> \<approx>\<^sub>D \<Pi>'] =
    (AOT_model_denotes \<Pi> \<and> AOT_model_denotes \<Pi>' \<and> (\<exists>f .
      bij_betw f
              {u. AOT_model_valid_in w\<^sub>0 (Rep_urrel (rel_to_urrel \<Pi>) u)}
              {u. AOT_model_valid_in w\<^sub>0 (Rep_urrel (rel_to_urrel \<Pi>') u)}))\<close>
  (is \<open>?lhs = ?rhs\<close>)
proof
  AOT_world w\<^sub>0
  AOT_assume \<open>\<Pi> \<approx>\<^sub>D \<Pi>'\<close>
  AOT_hence \<open>\<exists>R R |: \<Pi> \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D \<Pi>'\<close>
    using "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain R where \<open>R |: \<Pi> \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D \<Pi>'\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<open>R\<down> & \<Pi>\<down> & \<Pi>'\<down> & \<forall>u ([\<Pi>]u \<rightarrow> \<exists>!\<^sub>D v ([\<Pi>']v & [R]uv))
                            & \<forall>v ([\<Pi>']v \<rightarrow> \<exists>!\<^sub>D u ([\<Pi>]u & [R]uv))\<close>
    using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_hence \<Pi>_den: \<open>\<Pi>\<down>\<close> and \<Pi>'_den: \<open>\<Pi>'\<down>\<close>
        and \<Pi>_uniq: \<open>\<forall>u ([\<Pi>]u \<rightarrow> \<exists>!\<^sub>Dv ([\<Pi>']v & [R]uv))\<close>
        and \<Pi>'_uniq: \<open>\<forall>v ([\<Pi>']v \<rightarrow> \<exists>!\<^sub>Du ([\<Pi>]u & [R]uv))\<close>
    using "&E" by blast+
  have \<Pi>_den_model: \<open>AOT_model_denotes \<Pi>\<close>
    by (meson AOT_sem_denotes \<Pi>_den)
  have \<Pi>'_den_model: \<open>AOT_model_denotes \<Pi>'\<close>
    by (meson AOT_sem_denotes \<Pi>'_den)
  have 0: \<open>[w \<Turnstile> \<guillemotleft>Rep_rel \<Pi> (SOME xa. \<kappa>\<upsilon> xa = null\<upsilon> x)\<guillemotright>] \<Longrightarrow> False\<close>
    for w x
    by (metis (mono_tags, lifting) AOT_model_denotes_\<kappa>_def AOT_model_denotes_rel.rep_eq
        \<kappa>.exhaust_disc \<kappa>\<upsilon>.simps \<Pi>_den_model \<upsilon>.disc(8,9) \<upsilon>.distinct(3)
        is_\<alpha>\<kappa>_def is_\<omega>\<kappa>_def someI_ex)
  have 1: \<open>[w \<Turnstile> \<guillemotleft>Rep_rel \<Pi>' (SOME xa. \<kappa>\<upsilon> xa = null\<upsilon> x)\<guillemotright>] \<Longrightarrow> False\<close>
    for w x
    by (metis (mono_tags, lifting) AOT_model_denotes_\<kappa>_def AOT_model_denotes_rel.rep_eq
        \<kappa>.exhaust_disc \<kappa>\<upsilon>.simps \<Pi>'_den_model \<upsilon>.disc(8,9) \<upsilon>.distinct(3)
        is_\<alpha>\<kappa>_def is_\<omega>\<kappa>_def someI_ex)
  have \<open>bij_betw (\<lambda> u . THE u' . \<not>is_null\<upsilon> u' \<and> [w\<^sub>0 \<Turnstile> [\<Pi>']\<guillemotleft>(inv \<kappa>\<upsilon> u')\<guillemotright> & [R]\<guillemotleft>(inv \<kappa>\<upsilon> u)\<guillemotright>\<guillemotleft>(inv \<kappa>\<upsilon> u')\<guillemotright>])
            {u. AOT_model_valid_in w\<^sub>0 (Rep_urrel (rel_to_urrel \<Pi>) u)}
            {u. AOT_model_valid_in w\<^sub>0 (Rep_urrel (rel_to_urrel \<Pi>') u)}\<close>
  proof (safe intro!: bij_betw_imageI inj_onI)
    fix x y
    assume A: \<open>(THE u' . \<not>is_null\<upsilon> u' \<and> [w\<^sub>0 \<Turnstile> [\<Pi>']\<guillemotleft>(inv \<kappa>\<upsilon> u')\<guillemotright> & [R]\<guillemotleft>(inv \<kappa>\<upsilon> x)\<guillemotright>\<guillemotleft>(inv \<kappa>\<upsilon> u')\<guillemotright>]) =
            (THE u' . \<not>is_null\<upsilon> u' \<and> [w\<^sub>0 \<Turnstile> [\<Pi>']\<guillemotleft>(inv \<kappa>\<upsilon> u')\<guillemotright> & [R]\<guillemotleft>(inv \<kappa>\<upsilon> y)\<guillemotright>\<guillemotleft>(inv \<kappa>\<upsilon> u')\<guillemotright>])\<close>
            (is \<open>?a = ?b\<close>)
    assume B: \<open>[w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel \<Pi>) x\<guillemotright>]\<close>
    hence \<open>[w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_rel \<Pi> (inv \<kappa>\<upsilon> x)\<guillemotright>]\<close>
      unfolding rel_to_urrel_def inv_def
      apply (subst (asm) Abs_urrel_inverse)
      using 0 by auto
    AOT_hence C: \<open>[\<Pi>]\<guillemotleft>inv \<kappa>\<upsilon> x\<guillemotright>\<close>
      by (metis AOT_sem_exe_denoting \<Pi>_den)
    AOT_hence \<open>\<exists>!\<^sub>Dv ([\<Pi>']v & [R]\<guillemotleft>inv \<kappa>\<upsilon> x\<guillemotright>v)\<close>
      by (auto intro!: \<Pi>_uniq[THEN "\<forall>E"(1), THEN "\<rightarrow>E"] simp: AOT_sem_exe)
    hence a: \<open>\<exists>!v. \<not> is_null\<upsilon> v \<and> [w\<^sub>0 \<Turnstile> [\<Pi>']\<guillemotleft>inv \<kappa>\<upsilon> v\<guillemotright> & [R]\<guillemotleft>inv \<kappa>\<upsilon> x\<guillemotright>\<guillemotleft>inv \<kappa>\<upsilon> v\<guillemotright>]\<close>
      apply (subst (asm) model_ex1D)
      subgoal by "cqt:2"
      by blast
    hence 1: \<open>\<not>is_null\<upsilon> ?a \<and> [w\<^sub>0 \<Turnstile> [\<Pi>']\<guillemotleft>(inv \<kappa>\<upsilon> ?a)\<guillemotright> & [R]\<guillemotleft>(inv \<kappa>\<upsilon> x)\<guillemotright>\<guillemotleft>(inv \<kappa>\<upsilon> ?a)\<guillemotright>]\<close>
      by (auto intro!: theI')
    AOT_hence 2: \<open>\<guillemotleft>(inv \<kappa>\<upsilon> ?a)\<guillemotright>\<down>\<close>
      by (smt (z3) "con-dis-i-e:2:a" "russell-axiom[exe,1].\<psi>_denotes_asm")
    have 3: \<open>AOT_instance_of_cqt_2 (\<lambda>\<kappa>. \<guillemotleft>[\<Pi>]\<kappa> & [R]\<kappa>\<guillemotleft>inv \<kappa>\<upsilon> (THE u'. \<not>is_null\<upsilon> u' \<and> [w\<^sub>0 \<Turnstile> [\<Pi>']\<guillemotleft>inv \<kappa>\<upsilon> u'\<guillemotright> & [R]\<guillemotleft>inv \<kappa>\<upsilon> x\<guillemotright>\<guillemotleft>inv \<kappa>\<upsilon> u'\<guillemotright>])\<guillemotright>\<guillemotright>)\<close>
      by "cqt:2"
    have 4: \<open>\<exists>!u. \<not> is_null\<upsilon> u \<and> [w\<^sub>0 \<Turnstile> [\<Pi>]\<guillemotleft>inv \<kappa>\<upsilon> u\<guillemotright> & [R]\<guillemotleft>inv \<kappa>\<upsilon> u\<guillemotright>\<guillemotleft>inv \<kappa>\<upsilon> ?a\<guillemotright>]\<close>
      using \<Pi>'_uniq[THEN "\<forall>E"(1), OF 2, THEN "\<rightarrow>E", OF 1[THEN conjunct2, THEN "&E"(1)],
                    simplified model_ex1D[OF 3]]
      by blast
    have \<open>\<not>is_null\<upsilon> x\<close>
      using Rep_urrel is_null\<upsilon>_def local.B by auto
    hence x: \<open>\<not>is_null\<upsilon> x \<and> [w\<^sub>0 \<Turnstile> [\<Pi>]\<guillemotleft>inv \<kappa>\<upsilon> x\<guillemotright> & [R]\<guillemotleft>inv \<kappa>\<upsilon> x\<guillemotright>\<guillemotleft>inv \<kappa>\<upsilon> ?a\<guillemotright>]\<close>
      using "1" AOT_sem_conj C by blast
      

    assume D: \<open>[w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel \<Pi>) y\<guillemotright>]\<close>
    hence \<open>[w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_rel \<Pi> (inv \<kappa>\<upsilon> y)\<guillemotright>]\<close>
      using 1 unfolding rel_to_urrel_def inv_def
      apply (subst (asm) Abs_urrel_inverse)
      using 0 by auto
    AOT_hence E: \<open>[\<Pi>]\<guillemotleft>inv \<kappa>\<upsilon> y\<guillemotright>\<close>
      by (metis AOT_sem_exe_denoting \<Pi>_den)
    AOT_hence \<open>\<exists>!\<^sub>Dv ([\<Pi>']v & [R]\<guillemotleft>inv \<kappa>\<upsilon> y\<guillemotright>v)\<close>
      by (auto intro!: \<Pi>_uniq[THEN "\<forall>E"(1), THEN "\<rightarrow>E"] simp: AOT_sem_exe)
    hence b: \<open>\<exists>!v. \<not> is_null\<upsilon> v \<and> [w\<^sub>0 \<Turnstile> [\<Pi>']\<guillemotleft>inv \<kappa>\<upsilon> v\<guillemotright> & [R]\<guillemotleft>inv \<kappa>\<upsilon> y\<guillemotright>\<guillemotleft>inv \<kappa>\<upsilon> v\<guillemotright>]\<close>
      apply (subst (asm) model_ex1D)
      subgoal by "cqt:2"
      by blast
    hence \<open>\<not> is_null\<upsilon> ?b \<and> [w\<^sub>0 \<Turnstile> [\<Pi>']\<guillemotleft>(inv \<kappa>\<upsilon> ?b)\<guillemotright> & [R]\<guillemotleft>(inv \<kappa>\<upsilon> y)\<guillemotright>\<guillemotleft>(inv \<kappa>\<upsilon> ?b)\<guillemotright>]\<close>
      by (auto intro!: theI')
    moreover have \<open>\<not>is_null\<upsilon> y\<close>
      using D Rep_urrel is_null\<upsilon>_def by force
    ultimately have \<open>\<not>is_null\<upsilon> y \<and> [w\<^sub>0 \<Turnstile> [\<Pi>]\<guillemotleft>inv \<kappa>\<upsilon> y\<guillemotright> & [R]\<guillemotleft>inv \<kappa>\<upsilon> y\<guillemotright>\<guillemotleft>inv \<kappa>\<upsilon> ?a\<guillemotright>]\<close>
      by (smt (z3) "con-dis-i-e:1" "con-dis-i-e:2:b" A E)
    find_theorems \<open>(THE x . ?p x) = (THE x . ?q x)\<close>
    thus \<open>x = y\<close>
      using 4 x by blast
  next
    fix  u
    let ?a = \<open>THE u' . \<not>is_null\<upsilon> u' \<and> [w\<^sub>0 \<Turnstile> [\<Pi>']\<guillemotleft>(inv \<kappa>\<upsilon> u')\<guillemotright> & [R]\<guillemotleft>(inv \<kappa>\<upsilon> u)\<guillemotright>\<guillemotleft>(inv \<kappa>\<upsilon> u')\<guillemotright>]\<close>
    assume \<open>[w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel \<Pi>) u\<guillemotright>]\<close>
    hence \<open>[w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_rel \<Pi> (inv \<kappa>\<upsilon> u)\<guillemotright>]\<close>
      unfolding rel_to_urrel_def inv_def
      apply (subst (asm) Abs_urrel_inverse)
      using 0 by auto
    AOT_hence C: \<open>[\<Pi>]\<guillemotleft>inv \<kappa>\<upsilon> u\<guillemotright>\<close>
      by (metis AOT_sem_exe_denoting \<Pi>_den)
    AOT_hence \<open>\<exists>!\<^sub>Dv ([\<Pi>']v & [R]\<guillemotleft>inv \<kappa>\<upsilon> u\<guillemotright>v)\<close>
      by (auto intro!: \<Pi>_uniq[THEN "\<forall>E"(1), THEN "\<rightarrow>E"] simp: AOT_sem_exe)
    hence a: \<open>\<exists>!v. \<not> is_null\<upsilon> v \<and> [w\<^sub>0 \<Turnstile> [\<Pi>']\<guillemotleft>inv \<kappa>\<upsilon> v\<guillemotright> & [R]\<guillemotleft>inv \<kappa>\<upsilon> u\<guillemotright>\<guillemotleft>inv \<kappa>\<upsilon> v\<guillemotright>]\<close>
      apply (subst (asm) model_ex1D)
      subgoal by "cqt:2"
      by blast
    AOT_have \<open>[\<Pi>']\<guillemotleft>inv \<kappa>\<upsilon> ?a\<guillemotright>\<close>
      using theI'[OF a, THEN conjunct2, THEN "&E"(1)]
      by blast
    thus \<open>[w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel \<Pi>') ?a\<guillemotright>]\<close>
      unfolding AOT_sem_exe rel_to_urrel_def inv_def
      apply (subst Abs_urrel_inverse)
      using "1" by auto
  next
    fix x
    assume \<open>[w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel \<Pi>') x\<guillemotright>]\<close>
    hence 2: \<open>[w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_rel \<Pi>' (inv \<kappa>\<upsilon> x)\<guillemotright>]\<close>
      unfolding rel_to_urrel_def inv_def
      apply (subst (asm) Abs_urrel_inverse)
      using 1 by auto
    AOT_hence C: \<open>[\<Pi>']\<guillemotleft>inv \<kappa>\<upsilon> x\<guillemotright>\<close>
      by (metis AOT_sem_exe_denoting \<Pi>'_den)
    AOT_hence \<open>\<exists>!\<^sub>Du ([\<Pi>]u & [R]u\<guillemotleft>inv \<kappa>\<upsilon> x\<guillemotright>)\<close>
      by (auto intro!: \<Pi>'_uniq[THEN "\<forall>E"(1), THEN "\<rightarrow>E"] simp: AOT_sem_exe)
    hence a: \<open>\<exists>!v. \<not> is_null\<upsilon> v \<and> [w\<^sub>0 \<Turnstile> [\<Pi>]\<guillemotleft>inv \<kappa>\<upsilon> v\<guillemotright> & [R]\<guillemotleft>inv \<kappa>\<upsilon> v\<guillemotright>\<guillemotleft>inv \<kappa>\<upsilon> x\<guillemotright>]\<close> (is \<open>\<exists>!v . ?\<phi> v\<close>)
      apply (subst (asm) model_ex1D)
      subgoal by "cqt:2"
      by blast
    then obtain v where v_prop: \<open>?\<phi> v \<and> (\<forall>v' . ?\<phi> v' \<longrightarrow> v' = v)\<close>
      by auto
    AOT_hence \<open>[\<Pi>]\<guillemotleft>inv \<kappa>\<upsilon> v\<guillemotright>\<close>
      using AOT_sem_conj by blast
    AOT_hence \<open>\<exists>!\<^sub>Du ([\<Pi>']u & [R]\<guillemotleft>inv \<kappa>\<upsilon> v\<guillemotright>u)\<close>
      apply (safe intro!: \<Pi>_uniq[THEN "\<forall>E"(1), THEN "\<rightarrow>E"])
      using AOT_sem_exe by blast
    hence b: \<open>\<exists>!u. \<not> is_null\<upsilon> u \<and> [w\<^sub>0 \<Turnstile> [\<Pi>']\<guillemotleft>inv \<kappa>\<upsilon> u\<guillemotright> & [R]\<guillemotleft>inv \<kappa>\<upsilon> v\<guillemotright>\<guillemotleft>inv \<kappa>\<upsilon> u\<guillemotright>]\<close>
          (is \<open>\<exists>!v . ?\<psi> v\<close>)
      apply (subst (asm) model_ex1D)
      subgoal by "cqt:2"
      by blast
    have c: \<open>(THE u'. \<not> is_null\<upsilon> u' \<and> [w\<^sub>0 \<Turnstile> [\<Pi>']\<guillemotleft>inv \<kappa>\<upsilon> u'\<guillemotright> & [R]\<guillemotleft>inv \<kappa>\<upsilon> v\<guillemotright>\<guillemotleft>inv \<kappa>\<upsilon> u'\<guillemotright>]) = x\<close>
      apply (rule the1_equality)
      using b apply blast
      by (metis "1" "2" AOT_sem_conj C inv_def is_null\<upsilon>_def v_prop)
    show \<open>x \<in> (\<lambda>u . (THE u' . \<not>is_null\<upsilon> u' \<and> [w\<^sub>0 \<Turnstile> [\<Pi>']\<guillemotleft>(inv \<kappa>\<upsilon> u')\<guillemotright> & [R]\<guillemotleft>(inv \<kappa>\<upsilon> u)\<guillemotright>\<guillemotleft>(inv \<kappa>\<upsilon> u')\<guillemotright>])) ` {u . [w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel \<Pi>) u\<guillemotright>]}\<close>
      unfolding image_def
      apply simp
      apply (safe intro!: exI[where x=v])
      unfolding rel_to_urrel_def
       apply (subst Abs_urrel_inverse)
      using "0" apply blast
      using v_prop[THEN conjunct1, THEN conjunct2, THEN "&E"(1), simplified inv_def AOT_sem_exe] apply simp
      using c by simp
  qed
  thus ?rhs using \<Pi>_den \<Pi>'_den AOT_sem_denotes by blast
next
  assume 0: \<open>?rhs\<close>
  then obtain f where f_prop: \<open>bij_betw f
              {u. AOT_model_valid_in w\<^sub>0 (Rep_urrel (rel_to_urrel \<Pi>) u)}
              {u. AOT_model_valid_in w\<^sub>0 (Rep_urrel (rel_to_urrel \<Pi>') u)}\<close>
    by blast
  hence 1: \<open>x \<in> {u. AOT_model_valid_in w\<^sub>0 (Rep_urrel (rel_to_urrel \<Pi>) u)} \<Longrightarrow>
        f x \<in> {u. AOT_model_valid_in w\<^sub>0 (Rep_urrel (rel_to_urrel \<Pi>') u)}\<close>
    for x
    using bij_betwE by blast
  define g where \<open>g = the_inv_into {u. AOT_model_valid_in w\<^sub>0 (Rep_urrel (rel_to_urrel \<Pi>) u)} f\<close>
  have g_prop: \<open>bij_betw g
              {u. AOT_model_valid_in w\<^sub>0 (Rep_urrel (rel_to_urrel \<Pi>') u)}
              {u. AOT_model_valid_in w\<^sub>0 (Rep_urrel (rel_to_urrel \<Pi>) u)}\<close>
    by (simp add: bij_betw_the_inv_into f_prop g_def)
  hence 12: \<open>x \<in> {u. AOT_model_valid_in w\<^sub>0 (Rep_urrel (rel_to_urrel \<Pi>') u)} \<Longrightarrow>
        g x \<in> {u. AOT_model_valid_in w\<^sub>0 (Rep_urrel (rel_to_urrel \<Pi>) u)}\<close>
    for x
    using bij_betwE by blast
  find_theorems \<open>bij_betw ?f ?a ?b \<Longrightarrow> bij_betw ?g ?b ?a\<close>
  AOT_world w\<^sub>0
    AOT_have \<Pi>_den: \<open>\<Pi>\<down>\<close> and \<Pi>'_den: \<open>\<Pi>'\<down>\<close>
      by (auto simp add: "0" AOT_sem_denotes)
  AOT_have 0: \<open>[\<lambda>xy \<guillemotleft>\<epsilon>\<^sub>\<o> w . f (\<kappa>\<upsilon> x) = \<kappa>\<upsilon> y\<guillemotright>]\<down>\<close>
    unfolding AOT_sem_denotes AOT_model_lambda_denotes
    by (auto simp: AOT_model_proposition_choice_simp AOT_model_term_equiv_\<kappa>_def
                   AOT_model_term_equiv_prod_def)
  moreover AOT_have \<open>[\<lambda>xy \<guillemotleft>\<epsilon>\<^sub>\<o> w . f (\<kappa>\<upsilon> x) = \<kappa>\<upsilon> y\<guillemotright>] |: \<Pi> \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D \<Pi>'\<close>
  proof (AOT_subst_def "equi:2"; safe intro!: "&I" 0 \<Pi>_den \<Pi>'_den GEN "\<rightarrow>I" "cqt:2")
    fix u
    AOT_assume \<open>[\<Pi>]u\<close>
    hence \<open>AOT_model_valid_in w\<^sub>0 (Rep_urrel (rel_to_urrel \<Pi>) (\<kappa>\<upsilon> (AOT_term_of_var u)))\<close>
      unfolding AOT_sem_exe rel_to_urrel_def
      apply (subst Abs_urrel_inverse)
       apply simp
      apply (metis AOT_model_denotes_\<kappa>_def AOT_model_term_equiv_\<kappa>_def AOT_model_term_equiv_denotes AOT_sem_denotes AOT_sem_exe AOT_sem_exe_denoting \<kappa>.disc(9) \<kappa>\<upsilon>.simps(3) \<kappa>\<upsilon>_surj inv_def surj_f_inv_f)
      by (metis (full_types) AOT_model_denotes_rel.rep_eq AOT_model_term_equiv_\<kappa>_def AOT_sem_denotes \<kappa>\<upsilon>_surj inv_def surj_f_inv_f)
    hence 2: \<open>AOT_model_valid_in w\<^sub>0 (Rep_urrel (rel_to_urrel \<Pi>') (f (\<kappa>\<upsilon> (AOT_term_of_var u))))\<close>
      using 1[simplified] by metis
    AOT_hence 3: \<open>[\<Pi>']\<guillemotleft>inv \<kappa>\<upsilon> (f (\<kappa>\<upsilon> (AOT_term_of_var u)))\<guillemotright>\<close>
      unfolding AOT_sem_exe
      apply auto
        using \<Pi>'_den apply blast
         apply (simp add: AOT_model_denotes_\<kappa>_def AOT_sem_denotes \<kappa>\<upsilon>_surj surj_f_inv_f urrel_null_false)
        unfolding rel_to_urrel_def
        apply (subst (asm) Abs_urrel_inverse)
        apply simp
        apply (metis AOT_model_denotes_\<kappa>_def AOT_model_term_equiv_\<kappa>_def AOT_model_term_equiv_denotes AOT_sem_denotes AOT_sem_exe AOT_sem_exe_denoting \<Pi>'_den \<kappa>.disc(9) \<kappa>\<upsilon>.simps(3) \<kappa>\<upsilon>_surj inv_def surj_f_inv_f)
        by (simp add: inv_def)
    have 4: \<open>\<not>is_null\<upsilon> (f (\<kappa>\<upsilon> (AOT_term_of_var u)))\<close>
      using 2
      by (metis \<kappa>.disc(9) \<kappa>\<upsilon>.simps(3) is_null\<upsilon>_def urrel_null_false)
    AOT_show \<open>\<exists>!\<^sub>Dv ([\<Pi>']v & [\<lambda>xy \<guillemotleft>\<epsilon>\<^sub>\<o> w. f (\<kappa>\<upsilon> x) = \<kappa>\<upsilon> y\<guillemotright>]uv)\<close>
      apply (subst model_ex1D)
      subgoal by "cqt:2"
      apply (safe intro!: ex1I[where a=\<open>f (\<kappa>\<upsilon> (AOT_term_of_var u))\<close>] 4 "&I" 3 "\<beta>\<leftarrow>C")
         apply (simp add: 0)
      apply (meson "3" "cqt:2"(1) "russell-axiom[exe,1].\<psi>_denotes_asm" AOT_sem_conj prod_denotesI)
      apply (simp add: AOT_model_proposition_choice_simp \<kappa>\<upsilon>_surj surj_f_inv_f)
      by (metis (mono_tags, lifting) "betaC:1:a" "con-dis-i-e:2:b" AOT_model_proposition_choice_simp \<kappa>\<upsilon>_surj old.prod.case surj_f_inv_f)
  next
    fix v
    AOT_assume \<open>[\<Pi>']v\<close>
    hence \<Pi>'v: \<open>AOT_model_valid_in w\<^sub>0 (Rep_urrel (rel_to_urrel \<Pi>') (\<kappa>\<upsilon> (AOT_term_of_var v)))\<close>
      unfolding AOT_sem_exe rel_to_urrel_def
      apply (subst Abs_urrel_inverse)
       apply simp
      apply (metis AOT_model_denotes_\<kappa>_def AOT_model_term_equiv_\<kappa>_def AOT_model_term_equiv_denotes AOT_sem_denotes AOT_sem_exe AOT_sem_exe_denoting \<kappa>.disc(9) \<kappa>\<upsilon>.simps(3) \<kappa>\<upsilon>_surj inv_def surj_f_inv_f)
      by (metis (full_types) AOT_model_denotes_rel.rep_eq AOT_model_term_equiv_\<kappa>_def AOT_sem_denotes \<kappa>\<upsilon>_surj inv_def surj_f_inv_f)
    hence 2: \<open>AOT_model_valid_in w\<^sub>0 (Rep_urrel (rel_to_urrel \<Pi>) (g (\<kappa>\<upsilon> (AOT_term_of_var v))))\<close>
      using 12[simplified] by metis
    AOT_hence 3: \<open>[\<Pi>]\<guillemotleft>inv \<kappa>\<upsilon> (g (\<kappa>\<upsilon> (AOT_term_of_var v)))\<guillemotright>\<close>
      unfolding AOT_sem_exe
      apply auto
        using \<Pi>_den apply blast
         apply (simp add: AOT_model_denotes_\<kappa>_def AOT_sem_denotes \<kappa>\<upsilon>_surj surj_f_inv_f urrel_null_false)
        unfolding rel_to_urrel_def
        apply (subst (asm) Abs_urrel_inverse)
        apply simp
         apply (metis AOT_model_denotes_\<kappa>_def AOT_model_term_equiv_\<kappa>_def
                      AOT_model_term_equiv_denotes AOT_sem_denotes AOT_sem_exe
                      AOT_sem_exe_denoting \<Pi>_den \<kappa>.disc(9) \<kappa>\<upsilon>.simps(3) \<kappa>\<upsilon>_surj
                      inv_def surj_f_inv_f)
        by (simp add: inv_def)
    have 4: \<open>\<not>is_null\<upsilon> (g (\<kappa>\<upsilon> (AOT_term_of_var v)))\<close>
      using 2
      by (metis \<kappa>.disc(9) \<kappa>\<upsilon>.simps(3) is_null\<upsilon>_def urrel_null_false)
    {
      fix u
      assume \<open>\<not>is_null\<upsilon> u\<close>
      AOT_assume \<open>[\<Pi>]\<guillemotleft>inv \<kappa>\<upsilon> u\<guillemotright> & [\<lambda>xy \<guillemotleft>\<epsilon>\<^sub>\<o> w. f (\<kappa>\<upsilon> x) = \<kappa>\<upsilon> y\<guillemotright>]\<guillemotleft>inv \<kappa>\<upsilon> u\<guillemotright>v\<close>
      AOT_hence 0: \<open>[\<Pi>]\<guillemotleft>inv \<kappa>\<upsilon> u\<guillemotright>\<close> and \<open>[\<lambda>xy \<guillemotleft>\<epsilon>\<^sub>\<o> w. f (\<kappa>\<upsilon> x) = \<kappa>\<upsilon> y\<guillemotright>]\<guillemotleft>inv \<kappa>\<upsilon> u\<guillemotright>v\<close>
        using "&E" by blast+
      AOT_hence \<open>\<guillemotleft>\<epsilon>\<^sub>\<o> w. f (\<kappa>\<upsilon> (inv \<kappa>\<upsilon> u)) = \<kappa>\<upsilon> (AOT_term_of_var v)\<guillemotright>\<close>
        using "\<beta>\<rightarrow>C" by fast
      hence 1: \<open>f (\<kappa>\<upsilon> (inv \<kappa>\<upsilon> u)) = \<kappa>\<upsilon> (AOT_term_of_var v)\<close>
        by (auto simp: AOT_model_proposition_choice_simp)
      have 2: \<open>[w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel \<Pi>) u\<guillemotright>]\<close>
        unfolding rel_to_urrel_def
        apply (subst Abs_urrel_inverse)
         apply simp
         apply (metis AOT_model_denotes_\<kappa>_def AOT_model_term_equiv_\<kappa>_def
                      AOT_model_term_equiv_denotes AOT_sem_denotes AOT_sem_exe
                      AOT_sem_exe_denoting \<Pi>_den \<kappa>.disc(9) \<kappa>\<upsilon>.simps(3) \<kappa>\<upsilon>_surj
                      inv_def surj_f_inv_f)
        using 0 unfolding inv_def AOT_sem_exe by auto
      have \<open>u = g (\<kappa>\<upsilon> (AOT_term_of_var v))\<close>
        unfolding g_def
        by (smt (verit, ccfv_threshold) "1" "12" "2" \<kappa>\<upsilon>_surj bij_betw_iff_bijections
                f_prop f_the_inv_into_f_bij_betw g_def mem_Collect_eq surj_f_inv_f)
    } note 5 = this
    AOT_show \<open>\<exists>!\<^sub>Du ([\<Pi>]u & [\<lambda>xy \<guillemotleft>\<epsilon>\<^sub>\<o> w. f (\<kappa>\<upsilon> x) = \<kappa>\<upsilon> y\<guillemotright>]uv)\<close>
      apply (subst model_ex1D)
      subgoal by "cqt:2"
      apply (safe intro!: ex1I[where a=\<open>g (\<kappa>\<upsilon> (AOT_term_of_var v))\<close>] 4 "&I" 3 "\<beta>\<leftarrow>C")
         apply (simp add: 0)
      apply (meson "3" "cqt:2"(1) "russell-axiom[exe,1].\<psi>_denotes_asm" AOT_sem_conj prod_denotesI)
       apply (simp add: AOT_model_proposition_choice_simp \<kappa>\<upsilon>_surj surj_f_inv_f)
      using g_def \<Pi>'v f_prop f_the_inv_into_f_bij_betw apply fastforce
      using 5 by simp
  qed
  ultimately AOT_have \<open>\<exists>R R |: \<Pi> \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D \<Pi>'\<close>
    using "\<exists>I" by fast
  AOT_thus \<open>\<Pi> \<approx>\<^sub>D \<Pi>'\<close>
    by (AOT_subst_def "equi:3")
qed

lemma indist_\<alpha>\<sigma>[AOT_no_atp, no_atp]:
  assumes Ax: \<open>[v \<Turnstile> A!x]\<close>
  shows \<open>[v \<Turnstile> \<forall>F ([F]x \<equiv> [F]y)] = (\<exists>a b . AOT_term_of_var x = \<alpha>\<kappa> a \<and> AOT_term_of_var y = \<alpha>\<kappa> b \<and> \<alpha>\<sigma> a = \<alpha>\<sigma> b)\<close>
proof
  AOT_world v
  AOT_assume indist: \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
  AOT_have \<open>A!y\<close>
    using indist[THEN "\<forall>E"(1), OF "oa-exist:2", THEN "\<equiv>E"(1), OF Ax].
  then obtain a b where a_prop: \<open>AOT_term_of_var x = \<alpha>\<kappa> a\<close>
                    and b_prop: \<open>AOT_term_of_var y = \<alpha>\<kappa> b\<close>
    using Ax AOT_model_abstract_\<alpha>\<kappa> by force
  moreover have \<open>\<alpha>\<sigma> a = \<alpha>\<sigma> b\<close>
  proof -
    AOT_have \<open>[\<lambda>x \<guillemotleft>\<epsilon>\<^sub>\<o> w . \<kappa>\<upsilon> x = \<sigma>\<upsilon> (\<alpha>\<sigma> a)\<guillemotright>]\<down>\<close>
      unfolding AOT_sem_denotes AOT_model_lambda_denotes AOT_model_proposition_choice_simp
      using AOT_model_term_equiv_\<kappa>_def by presburger
    moreover AOT_have \<open>[\<lambda>x \<guillemotleft>\<epsilon>\<^sub>\<o> w . \<kappa>\<upsilon> x = \<sigma>\<upsilon> (\<alpha>\<sigma> a)\<guillemotright>]x\<close>
      by (metis (mono_tags) "cqt:2"(1) AOT_model_proposition_choice_simp AOT_sem_lambda_beta \<kappa>\<upsilon>.simps(2) a_prop calculation)
    ultimately AOT_have \<open>[\<lambda>x \<guillemotleft>\<epsilon>\<^sub>\<o> w . \<kappa>\<upsilon> x = \<sigma>\<upsilon> (\<alpha>\<sigma> a)\<guillemotright>]y\<close>
      using indist[THEN "\<forall>E"(1), THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>\<guillemotleft>\<epsilon>\<^sub>\<o> w . \<kappa>\<upsilon> (AOT_term_of_var y) = \<sigma>\<upsilon> (\<alpha>\<sigma> a)\<guillemotright>\<close>
      using "betaC:1:a" by blast
    hence \<open>\<kappa>\<upsilon> (AOT_term_of_var y) = \<sigma>\<upsilon> (\<alpha>\<sigma> a)\<close>
      using AOT_model_proposition_choice_simp by auto
    thus \<open>\<alpha>\<sigma> a = \<alpha>\<sigma> b\<close>
      by (metis \<kappa>\<upsilon>.simps(2) \<upsilon>.inject(2) b_prop)
  qed
  ultimately show \<open>\<exists>a b . AOT_term_of_var x = \<alpha>\<kappa> a \<and> AOT_term_of_var y = \<alpha>\<kappa> b \<and> \<alpha>\<sigma> a = \<alpha>\<sigma> b\<close> by blast
next
  AOT_world v
    assume \<open>\<exists>a b . AOT_term_of_var x = \<alpha>\<kappa> a \<and> AOT_term_of_var y = \<alpha>\<kappa> b \<and> \<alpha>\<sigma> a = \<alpha>\<sigma> b\<close>
    then obtain a b where a_prop: \<open>AOT_term_of_var x = \<alpha>\<kappa> a\<close>
                      and b_prop: \<open>AOT_term_of_var y = \<alpha>\<kappa> b\<close>
                      and \<alpha>\<sigma>_eq: \<open>\<alpha>\<sigma> a = \<alpha>\<sigma> b\<close>
      by auto
    hence \<open>\<kappa>\<upsilon> (AOT_term_of_var x) = \<kappa>\<upsilon> (AOT_term_of_var y)\<close>
      by simp
    hence term_equiv: \<open>AOT_model_term_equiv (AOT_term_of_var x) (AOT_term_of_var y)\<close>
       by (metis AOT_model_term_equiv_\<kappa>_def)
    AOT_show \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
    proof(safe intro!: GEN "\<equiv>I" "\<rightarrow>I")
      fix F
      AOT_assume \<open>[F]x\<close>
      AOT_thus \<open>[F]y\<close>
        by (metis AOT_model_denotes_rel.rep_eq AOT_sem_denotes AOT_sem_exe term_equiv) 
    next
      fix F
      AOT_assume \<open>[F]y\<close>
      AOT_thus \<open>[F]x\<close>
        by (metis AOT_model_denotes_rel.rep_eq AOT_sem_denotes AOT_sem_exe term_equiv) 
    qed
qed


AOT_theorem num_den: \<open>[\<lambda>x Numbers(x,G)]\<down>\<close>
proof(safe intro!: "kirchner-thm:1"[THEN "\<equiv>E"(2)] RN GEN "\<rightarrow>I")
  AOT_modally_strict {
    fix x y
    AOT_assume indist: \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
    AOT_assume numxG: \<open>Numbers(x,G)\<close>

    AOT_obtain H where \<open>Rigidifies(H,G)\<close>
      by (metis "instantiation" "rigid-der:3")

    AOT_hence H_props: \<open>Rigid(H) & \<forall>x([H]x \<equiv> [G]x)\<close>
      by (AOT_subst_def (reverse) "df-rigid-rel:2")
    AOT_hence \<open>H \<equiv>\<^sub>D G\<close>
      by (AOT_subst_def eqD)
         (auto intro!: "&I" "F-u[den]" "cqt:2" dest: "&E"(2))
    AOT_hence H_approx_G: \<open>H \<approx>\<^sub>D G\<close>
      by (safe intro!: "apE-eqE:1"[THEN "\<rightarrow>E"])
    AOT_have H_approx_act_H: \<open>H \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[H]z]\<close>
      using "approx-nec:1"[THEN "\<rightarrow>E", OF H_props[THEN "&E"(1)]] by blast

    AOT_have 0: \<open>A!x & G\<down> & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>
      using numxG numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
    AOT_hence 1: \<open>x[H] \<equiv> [\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>D G\<close> for H
      using "&E" "\<forall>E"(2) by blast
    {
      fix F
      AOT_assume \<open>\<^bold>\<A>x[F]\<close>
      AOT_hence \<open>x[F]\<close>
        by (metis "en-eq:10[1]" "intro-elim:3:a")
      AOT_hence \<open>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G\<close>
        using 1 "\<equiv>E" "\<rightarrow>E" by blast
      AOT_hence \<open>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D H\<close>
        using H_approx_G
        by (metis "eq-part:2[terms]" "eq-part:3[terms]" "vdash-properties:10") 
      also AOT_have \<open>H \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[H]z]\<close>
        using "approx-nec:1"[THEN "\<rightarrow>E", OF H_props[THEN "&E"(1)]] by blast
      finally AOT_have \<open>\<^bold>\<A>(F \<approx>\<^sub>D H)\<close>
        using "intro-elim:3:a" act_approx_lem by blast
    }
    moreover {
      fix F
      AOT_assume \<open>\<^bold>\<A>(F \<approx>\<^sub>D H)\<close>
      AOT_hence \<open>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[H]z]\<close>
        using "intro-elim:3:b" act_approx_lem by blast
      also AOT_have \<open>[\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>D H\<close>
        using "approx-nec:1"[THEN "\<rightarrow>E", OF H_props[THEN "&E"(1)], symmetric] by blast
      also AOT_have \<open>H \<approx>\<^sub>D G\<close>
        using H_approx_G.
      finally AOT_have \<open>x[F]\<close>
        using 1 "\<equiv>E" "\<rightarrow>E" by blast
      AOT_hence \<open>\<^bold>\<A>x[F]\<close>
        by (metis "en-eq:10[1]" AOT_sem_equiv) 
    }
    ultimately AOT_have \<open>\<^bold>\<A>x[F] \<equiv> \<^bold>\<A>(F \<approx>\<^sub>D H)\<close> for F using "\<equiv>I" "\<rightarrow>I" by simp
    AOT_actually {
      AOT_hence \<open>x[F] \<equiv> (F \<approx>\<^sub>D H)\<close> for F
        by (metis AOT_sem_act AOT_sem_equiv)
    } note act_x\<^sub>1_prop = this

    AOT_have Ax: \<open>A!x\<close> using 0 "&E" by blast
    obtain a b where
      a_prop: \<open>(AOT_term_of_var x) = \<alpha>\<kappa> a\<close> and
      b_prop: \<open>(AOT_term_of_var y) = \<alpha>\<kappa> b\<close> and 
      \<alpha>\<sigma>_eq: \<open>\<alpha>\<sigma> a = \<alpha>\<sigma> b\<close>
      using indist_\<alpha>\<sigma>[OF Ax, THEN iffD1, OF indist]
      by blast

    have \<open>\<alpha>\<sigma>' a = \<alpha>\<sigma>' b\<close>
      using \<alpha>\<sigma>_eq
      by (metis \<alpha>\<sigma>_\<alpha>\<sigma>')
    hence \<alpha>disc_eq: \<open>\<alpha>disc a = \<alpha>disc b\<close>
      by (meson \<alpha>\<sigma>_disc)

    AOT_actually {
        fix r
        assume \<open>r \<in> a\<close>
        AOT_hence \<open>x[\<guillemotleft>urrel_to_rel r\<guillemotright>]\<close>
          by (metis (no_types, lifting) AOT_enc_\<kappa>_meta AOT_model.AOT_term_of_var AOT_model_enc_\<kappa>_def AOT_model_term_equiv_rel_def Quotient3_rel_rep Quotient_abs_rep \<kappa>.simps(11) a_prop urrel_quotient urrel_quotient3)
        AOT_hence \<open>\<guillemotleft>urrel_to_rel r\<guillemotright> \<approx>\<^sub>D H\<close>
          by (auto intro!: act_x\<^sub>1_prop[unvarify F, THEN "\<equiv>E"(1)] simp: AOT_sem_enc_denotes)
        hence \<open>\<exists>f. bij_betw f {u. [w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel (urrel_to_rel r)) u\<guillemotright>]} {u. [w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel (AOT_term_of_var H)) u\<guillemotright>]}\<close>
          using model_equinum_bij by blast
        moreover have \<open>{u. [w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel (urrel_to_rel r)) u\<guillemotright>]} = urrel_act_ext r\<close>
          by (metis Quotient3_def urrel_act_ext_def urrel_quotient3)
        moreover have \<open>{u. [w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel (AOT_term_of_var H)) u\<guillemotright>]} = urrel_act_ext (rel_to_urrel (AOT_term_of_var H))\<close>
          using urrel_act_ext_def by presburger
        ultimately have \<open>|urrel_act_ext r| =o |urrel_act_ext (rel_to_urrel (AOT_term_of_var H))|\<close>
          by (metis card_of_ordIso)
        moreover have \<open>|rep_cards (abs_cards (urrel_act_ext (rel_to_urrel (AOT_term_of_var H))))| =o |urrel_act_ext (rel_to_urrel (AOT_term_of_var H))|\<close>
          by (meson Quotient3_abs_rep Quotient3_cards cards.abs_eq_iff)
        ultimately have \<open>|urrel_act_ext r| =o |rep_cards (abs_cards (urrel_act_ext (rel_to_urrel (AOT_term_of_var H))))|\<close>
          by (metis cards.abs_eq_iff)
      }
      moreover AOT_actually {
        fix r
        assume \<open>|urrel_act_ext r| =o |rep_cards (abs_cards (urrel_act_ext (rel_to_urrel (AOT_term_of_var H))))|\<close>
        moreover have \<open>|rep_cards (abs_cards (urrel_act_ext (rel_to_urrel (AOT_term_of_var H))))| =o |urrel_act_ext (rel_to_urrel (AOT_term_of_var H))|\<close>
          by (meson Quotient3_abs_rep Quotient3_cards cards.abs_eq_iff)
        ultimately have \<open>|urrel_act_ext r| =o |urrel_act_ext (rel_to_urrel (AOT_term_of_var H))|\<close>
          using ordIso_transitive by blast
        moreover have \<open>{u. [w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel (urrel_to_rel r)) u\<guillemotright>]} = urrel_act_ext r\<close>
          by (metis Quotient3_def urrel_act_ext_def urrel_quotient3)
        moreover have \<open>{u. [w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel (AOT_term_of_var H)) u\<guillemotright>]} = urrel_act_ext (rel_to_urrel (AOT_term_of_var H))\<close>
          using urrel_act_ext_def by presburger
        hence \<open>\<exists>f. bij_betw f {u. [w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel (urrel_to_rel r)) u\<guillemotright>]} {u. [w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel (AOT_term_of_var H)) u\<guillemotright>]}\<close>
          by (metis calculation(1) calculation(2) card_of_ordIso)
        moreover have \<open>AOT_model_denotes (urrel_to_rel r)\<close>
          by (metis AOT_model_term_equiv_rel_def Quotient3_rep_reflp urrel_quotient3)
        moreover have \<open>AOT_model_denotes (AOT_term_of_var H)\<close>
          by (simp add: AOT_model.AOT_term_of_var)
        ultimately AOT_have \<open>\<guillemotleft>urrel_to_rel r\<guillemotright> \<approx>\<^sub>D H\<close>
          using model_equinum_bij by blast
        AOT_hence \<open>x[\<guillemotleft>urrel_to_rel r\<guillemotright>]\<close>
          by (metis AOT_model.AOT_term_of_var_cases AOT_sem_equiv act_x\<^sub>1_prop model_equinum_bij)
        hence \<open>r \<in> a\<close>
          unfolding a_prop
          by (smt (verit, best) AOT_enc_\<kappa>_meta AOT_model_enc_\<kappa>_def Quotient3_def \<kappa>.simps(11) urrel_quotient3) 
      }
      ultimately have \<open>is_cardinal a (abs_cards (urrel_act_ext (rel_to_urrel (AOT_term_of_var H))))\<close>
        unfolding is_cardinal_def by blast
      hence cardb: \<open>is_cardinal b (abs_cards (urrel_act_ext (rel_to_urrel (AOT_term_of_var H))))\<close>
        using card_\<alpha>disc_eq \<alpha>disc_eq by blast

      {
        fix F
        AOT_assume \<open>y[F]\<close>
        hence \<open>rel_to_urrel (AOT_term_of_var F) \<in> b\<close>
          by (metis AOT_enc_\<kappa>_meta AOT_model_enc_\<kappa>_def \<kappa>.simps(11) b_prop)
        hence \<open>|urrel_act_ext (rel_to_urrel (AOT_term_of_var F))| =o
               |rep_cards (abs_cards (urrel_act_ext (rel_to_urrel (AOT_term_of_var H))))|\<close>
          using cardb is_cardinal_def by meson
        moreover have \<open>|rep_cards (abs_cards (urrel_act_ext (rel_to_urrel (AOT_term_of_var H))))| =o |urrel_act_ext (rel_to_urrel (AOT_term_of_var H))|\<close>
          by (meson Quotient3_abs_rep Quotient3_cards cards.abs_eq_iff)
        ultimately have \<open>|urrel_act_ext (rel_to_urrel (AOT_term_of_var F))| =o |urrel_act_ext (rel_to_urrel (AOT_term_of_var H))|\<close>
          using ordIso_transitive by blast
        hence \<open>|{u. [w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel (AOT_term_of_var F)) u\<guillemotright>]}| =o |{u. [w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel (AOT_term_of_var H)) u\<guillemotright>]}|\<close>
          by (metis urrel_act_ext_def)
        hence \<open>\<exists>f . bij_betw f {u. [w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel (AOT_term_of_var F)) u\<guillemotright>]} {u. [w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel (AOT_term_of_var H)) u\<guillemotright>]}\<close>
          by (metis card_of_ordIso)
        AOT_hence \<open>\<^bold>\<A>(F \<approx>\<^sub>D H)\<close>
          by (metis AOT_model.AOT_term_of_var model_equinum_bij AOT_sem_act)
        AOT_hence \<open>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[H]z]\<close>
          by (metis AOT_sem_equiv act_approx_lem)
        AOT_hence \<open>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D H\<close>
          by (metis "eq-part:2[terms]" "eq-part:3[terms]" "vdash-properties:10" H_approx_act_H)
        AOT_hence \<open>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G\<close>
          by (smt (z3) "eq-part:3[terms]" H_approx_G)
      }
      moreover {
        fix F
        AOT_assume \<open>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G\<close>
        AOT_hence \<open>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D H\<close>
          by (metis "eq-part:2" "eq-part:3[terms]" AOT_sem_imp H_approx_G)
        AOT_hence \<open>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D [\<lambda>z \<^bold>\<A>[H]z]\<close>
          by (metis "eq-part:3[terms]" H_approx_act_H)
        AOT_hence \<open>\<^bold>\<A>(F \<approx>\<^sub>D H)\<close>
          by (metis AOT_sem_equiv act_approx_lem)
        hence \<open>\<exists>f . bij_betw f {u. [w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel (AOT_term_of_var F)) u\<guillemotright>]} {u. [w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel (AOT_term_of_var H)) u\<guillemotright>]}\<close>
          using model_equinum_bij AOT_sem_act by blast
        hence \<open>|{u. [w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel (AOT_term_of_var F)) u\<guillemotright>]}| =o |{u. [w\<^sub>0 \<Turnstile> \<guillemotleft>Rep_urrel (rel_to_urrel (AOT_term_of_var H)) u\<guillemotright>]}|\<close>
          by (metis card_of_ordIso)
        hence \<open>|urrel_act_ext (rel_to_urrel (AOT_term_of_var F))| =o |urrel_act_ext (rel_to_urrel (AOT_term_of_var H))|\<close>
          by (metis urrel_act_ext_def)
        moreover have \<open>|rep_cards (abs_cards (urrel_act_ext (rel_to_urrel (AOT_term_of_var H))))| =o |urrel_act_ext (rel_to_urrel (AOT_term_of_var H))|\<close>
          by (meson Quotient3_abs_rep Quotient3_cards cards.abs_eq_iff)
        ultimately have \<open>|urrel_act_ext (rel_to_urrel (AOT_term_of_var F))| =o
               |rep_cards (abs_cards (urrel_act_ext (rel_to_urrel (AOT_term_of_var H))))|\<close>
          by (metis cards.abs_eq_iff)
        hence \<open>rel_to_urrel (AOT_term_of_var F) \<in> b\<close>
          by (metis cardb is_cardinal_def)
        AOT_hence \<open>y[F]\<close>
          by (metis AOT_enc_\<kappa>_meta AOT_model.AOT_term_of_var AOT_model_enc_\<kappa>_def \<kappa>.simps(11) b_prop)
      }
      ultimately AOT_have \<open>\<forall>F (y[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>
        by (auto intro!: GEN "\<equiv>I" "\<rightarrow>I")
      AOT_hence \<open>A!y & G\<down> & \<forall>F (y[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>D G)\<close>
        by (safe intro!: indist[THEN "\<forall>E"(1), OF "oa-exist:2", THEN "\<equiv>E"(1), OF Ax] "&I" "cqt:2")
      AOT_hence \<open>Numbers(y,G)\<close>
        using numbers[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
  } note 1 = this
  AOT_modally_strict {
    fix x y
    AOT_assume \<open>\<forall>F ([F]x \<equiv> [F]y)\<close>
    moreover AOT_have \<open>\<forall>F ([F]y \<equiv> [F]x)\<close>
      by (metis "cqt-basic:11" "intro-elim:3:b" calculation)
    ultimately AOT_show \<open>Numbers(x,G) \<equiv> Numbers(y,G)\<close>
      using 1 "\<rightarrow>I" "\<equiv>I" by simp
  }
qed
declare num_den[AOT_no_atp, no_atp]

text\<open>The following is again part of PLM.\<close>

AOT_theorem pred: \<open>[\<lambda>xy \<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))]\<down>\<close>
proof(rule "safe-ext[2]"[axiom_inst, THEN "\<rightarrow>E", OF "&I"])
  AOT_show \<open>[\<lambda>xy \<exists>F\<exists>u ([F]u & [\<lambda>y Numbers(y,F)]y & [\<lambda>x Numbers(x,[F]\<^sup>-\<^sup>u)]x)]\<down>\<close>
    by "cqt:2"
next
  AOT_show \<open>\<box>\<forall>x \<forall>y (\<exists>F \<exists>u ([F]u & [\<lambda>y Numbers(y,F)]y & [\<lambda>x Numbers(x,[F]\<^sup>-\<^sup>u)]x) \<equiv> \<exists>F \<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u)))\<close>
  proof(safe intro!: GEN RN "\<equiv>I" "\<rightarrow>I")
    AOT_modally_strict {
      fix x y
      AOT_assume \<open>\<exists>F \<exists>u ([F]u & [\<lambda>y Numbers(y,F)]y & [\<lambda>x Numbers(x,[F]\<^sup>-\<^sup>u)]x)\<close>
      then AOT_obtain F where \<open>\<exists>u ([F]u & [\<lambda>y Numbers(y,F)]y & [\<lambda>x Numbers(x,[F]\<^sup>-\<^sup>u)]x)\<close>
        using "\<exists>E"[rotated] by blast
      then AOT_obtain u where \<open>[F]u & [\<lambda>y Numbers(y,F)]y & [\<lambda>x Numbers(x,[F]\<^sup>-\<^sup>u)]x\<close>
        using "\<exists>E"[rotated] by blast
      AOT_hence \<open>[F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u)\<close>
        using "\<beta>\<rightarrow>C"(1) "&E" "&I" by metis
      AOT_hence \<open>\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
        by (rule "\<exists>I")
      AOT_thus \<open>\<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
        by (rule "\<exists>I")
    }
  next
    AOT_modally_strict {
      fix x y
      AOT_assume \<open>\<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
      then AOT_obtain F where \<open>\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
        using "\<exists>E"[rotated] by blast
      then AOT_obtain u where \<open>[F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u)\<close>
        using "\<exists>E"[rotated] by blast
      AOT_hence \<open>[F]u & [\<lambda>y Numbers(y,F)]y & [\<lambda>x Numbers(x,[F]\<^sup>-\<^sup>u)]x\<close>
        by (safe intro!: "&I" "\<beta>\<leftarrow>C" num_den num_den[unvarify G, OF "F-u[den]"])
           (auto intro!: "cqt:2" dest: "&E")
      AOT_hence \<open>\<exists>u ([F]u & [\<lambda>y Numbers(y,F)]y & [\<lambda>x Numbers(x,[F]\<^sup>-\<^sup>u)]x)\<close>
        by (rule "\<exists>I")
      AOT_thus \<open>\<exists>F\<exists>u ([F]u & [\<lambda>y Numbers(y,F)]y & [\<lambda>x Numbers(x,[F]\<^sup>-\<^sup>u)]x)\<close>
        by (rule "\<exists>I")
    }
  qed
qed

AOT_define Predecessor :: \<open>\<Pi>\<close> (\<open>\<P>\<close>)
  "pred-thm:1":
  \<open>\<P> =\<^sub>d\<^sub>f [\<lambda>xy \<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))]\<close>

AOT_theorem "pred-thm:2": \<open>\<P>\<down>\<close>
  using pred "pred-thm:1" "rule-id-df:2:b[zero]" by blast


AOT_theorem "pred-thm:3":
  \<open>[\<P>]xy \<equiv> \<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
proof -
  AOT_have prod_den: \<open>\<^bold>\<turnstile>\<^sub>\<box> \<guillemotleft>(AOT_term_of_var x\<^sub>1,AOT_term_of_var x\<^sub>2)\<guillemotright>\<down>\<close>
    for x\<^sub>1 x\<^sub>2 :: \<open>\<kappa> AOT_var\<close>
    by (simp add: "&I" "ex:1:a" prod_denotesI "rule-ui:3")
  show ?thesis
    apply (rule "=\<^sub>d\<^sub>fI"(2)[OF "pred-thm:1"])
    apply (metis pred)
    by (rule "beta-C-meta"[unvarify \<nu>\<^sub>1\<nu>\<^sub>n, OF prod_den, THEN "\<rightarrow>E",
                           OF pred, simplified])
qed

AOT_theorem "id-nec3D:2": \<open>\<diamond>(x =\<^sub>D y) \<equiv> x =\<^sub>D y\<close>
  by (meson "RE\<diamond>" "S5Basic:2" "id-nec4:1" "\<equiv>E"(1,5) "Commutativity of \<equiv>")

AOT_theorem "id-nec5:1": \<open>x \<noteq>\<^sub>D y \<equiv> \<box>(x \<noteq>\<^sub>D y)\<close>
proof -
  AOT_have \<open>x \<noteq>\<^sub>D y \<equiv> \<not>(x =\<^sub>D y)\<close> using "thm-neg=D".
  also AOT_have \<open>\<dots> \<equiv> \<not>\<diamond>(x =\<^sub>D y)\<close>
    by (meson "id-nec3D:2" "\<equiv>E"(1) "Commutativity of \<equiv>" "oth-class-taut:4:b")
  also AOT_have \<open>\<dots> \<equiv> \<box>\<not>(x =\<^sub>D y)\<close>
    by (meson "KBasic2:1" "\<equiv>E"(2) "Commutativity of \<equiv>")
  also AOT_have \<open>\<dots> \<equiv> \<box>(x \<noteq>\<^sub>D y)\<close>
    by (AOT_subst (reverse) \<open>\<not>(x =\<^sub>D y)\<close> \<open>x \<noteq>\<^sub>D y\<close>)
       (auto simp: "thm-neg=D" "oth-class-taut:3:a")
  finally show ?thesis.
qed

AOT_theorem "pred-1-1:1": \<open>[\<P>]xy \<rightarrow> \<box>[\<P>]xy\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>[\<P>]xy\<close>
  AOT_hence 0: \<open>\<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    using "\<equiv>E"(1) "pred-thm:3" by fast
  AOT_have \<open>\<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    using 0 "&E" by blast
  then AOT_obtain F where \<open>\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    using "\<exists>E"[rotated] by blast
  then AOT_obtain u where props: \<open>[F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u)\<close>
    using "\<exists>E"[rotated] by blast
  AOT_obtain G where Ridigifies_G_F: \<open>Rigidifies(G, F)\<close>
    by (metis "instantiation" "rigid-der:3")
  AOT_hence \<xi>: \<open>\<box>\<forall>x([G]x \<rightarrow> \<box>[G]x)\<close> and \<zeta>: \<open>\<forall>x([G]x \<equiv> [F]x)\<close>
    using "df-rigid-rel:2"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(1),
                           THEN "\<equiv>\<^sub>d\<^sub>fE"[OF "df-rigid-rel:1"], THEN "&E"(2)]
          "df-rigid-rel:2"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2)] by blast+

  AOT_have rigid_num_nec: \<open>Numbers(x,F) & Rigidifies(G,F) \<rightarrow> \<box>Numbers(x,G)\<close>
    for x G F
  proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
    fix G F x
    AOT_assume Numbers_xF: \<open>Numbers(x,F)\<close>
    AOT_assume \<open>Rigidifies(G,F)\<close>
    AOT_hence \<xi>: \<open>Rigid(G)\<close> and \<zeta>: \<open>\<forall>x([G]x \<equiv> [F]x)\<close>
      using "df-rigid-rel:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
    AOT_thus \<open>\<box>Numbers(x,G)\<close>
    proof (safe intro!:
          "num-cont:2"[THEN "\<rightarrow>E", OF \<xi>, THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"],
                       THEN "\<forall>E"(2), THEN "\<rightarrow>E"]
          "num-tran:3"[THEN "\<rightarrow>E", THEN "\<equiv>E"(1), rotated, OF Numbers_xF]
          eqD[THEN "\<equiv>\<^sub>d\<^sub>fI"]
            "&I" "cqt:2[const_var]"[axiom_inst] GEN "\<rightarrow>I")
      AOT_show \<open>[F]u \<equiv> [G]u\<close> for u
        using \<zeta>[THEN "\<forall>E"(2)] by (metis "\<equiv>E"(6) "oth-class-taut:3:a") 
    qed
  qed
  AOT_have \<open>\<box>Numbers(y,G)\<close>
    using rigid_num_nec[THEN "\<rightarrow>E", OF "&I", OF props[THEN "&E"(1), THEN "&E"(2)],
                        OF Ridigifies_G_F].
  moreover {
    AOT_have \<open>Rigidifies([G]\<^sup>-\<^sup>u, [F]\<^sup>-\<^sup>u)\<close>
    proof (safe intro!: "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "df-rigid-rel:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"]
                        "&I" "F-u[den]" GEN "\<equiv>I" "\<rightarrow>I")
      AOT_have \<open>\<box>\<forall>x([G]x \<rightarrow> \<box>[G]x) \<rightarrow> \<box>\<forall>x([[G]\<^sup>-\<^sup>u]x \<rightarrow> \<box>[[G]\<^sup>-\<^sup>u]x)\<close>
      proof (rule RM; safe intro!: "\<rightarrow>I" GEN)
        AOT_modally_strict {
          fix x
          AOT_assume 0: \<open>\<forall>x([G]x \<rightarrow> \<box>[G]x)\<close>
          AOT_assume 1: \<open>[[G]\<^sup>-\<^sup>u]x\<close>
          AOT_have \<open>[\<lambda>x [G]x & x \<noteq>\<^sub>D u]x\<close>
            apply (rule "F-u"[THEN "=\<^sub>d\<^sub>fE"(1), where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", simplified])
             apply "cqt:2[lambda]"
            by (fact 1)
          AOT_hence A: \<open>[G]x & x \<noteq>\<^sub>D u\<close>
            by (rule "\<beta>\<rightarrow>C"(1))
          AOT_hence 2: \<open>\<box>[G]x\<close>
            using "&E" 0[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] "id-nec4:1" "\<equiv>E"(1)
            by blast
          AOT_have 3: \<open>\<box>x \<noteq>\<^sub>D u\<close>
            using A[THEN "&E"(2)] "id-nec5:1"[THEN "\<equiv>E"(1)] by blast
          AOT_show \<open>\<box>[[G]\<^sup>-\<^sup>u]x\<close>
            apply (AOT_subst \<open>[[G]\<^sup>-\<^sup>u]x\<close> \<open>[G]x & x \<noteq>\<^sub>D u\<close>)
             apply (rule "F-u"[THEN "=\<^sub>d\<^sub>fI"(1), where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", simplified])
              apply "cqt:2[lambda]"
             apply (rule "beta-C-meta"[THEN "\<rightarrow>E"])
            apply "cqt:2[lambda]"
            using 2 3 "KBasic:3" "\<equiv>S"(2) "\<equiv>E"(2) by blast
        }
      qed
      AOT_thus \<open>\<box>\<forall>x([[G]\<^sup>-\<^sup>u]x \<rightarrow> \<box>[[G]\<^sup>-\<^sup>u]x)\<close> using \<xi> "\<rightarrow>E" by blast
    next
      fix x
      AOT_assume \<open>[[G]\<^sup>-\<^sup>u]x\<close>
      AOT_hence \<open>[\<lambda>x [G]x & x \<noteq>\<^sub>D u]x\<close>
        by (auto intro: "F-u"[THEN "=\<^sub>d\<^sub>fE"(1), where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", simplified]
                intro!: "cqt:2")
      AOT_hence \<open>[G]x & x \<noteq>\<^sub>D u\<close>
        by (rule "\<beta>\<rightarrow>C"(1))
      AOT_hence \<open>[F]x & x \<noteq>\<^sub>D u\<close>
        using \<zeta> "&I" "&E"(1) "&E"(2) "\<equiv>E"(1) "rule-ui:3" by blast
      AOT_hence \<open>[\<lambda>x [F]x & x \<noteq>\<^sub>D u]x\<close>
        by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2")
      AOT_thus \<open>[[F]\<^sup>-\<^sup>u]x\<close>
        by (auto intro: "F-u"[THEN "=\<^sub>d\<^sub>fI"(1), where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", simplified]
                intro!: "cqt:2")
    next
      fix x
      AOT_assume \<open>[[F]\<^sup>-\<^sup>u]x\<close>
      AOT_hence \<open>[\<lambda>x [F]x & x \<noteq>\<^sub>D u]x\<close>
        by (auto intro: "F-u"[THEN "=\<^sub>d\<^sub>fE"(1), where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", simplified]
                intro!: "cqt:2")
      AOT_hence \<open>[F]x & x \<noteq>\<^sub>D u\<close>
        by (rule "\<beta>\<rightarrow>C"(1))
      AOT_hence \<open>[G]x & x \<noteq>\<^sub>D u\<close>
        using \<zeta> "&I" "&E"(1) "&E"(2) "\<equiv>E"(2) "rule-ui:3" by blast
      AOT_hence \<open>[\<lambda>x [G]x & x \<noteq>\<^sub>D u]x\<close>
        by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2")
      AOT_thus \<open>[[G]\<^sup>-\<^sup>u]x\<close>
        by (auto intro: "F-u"[THEN "=\<^sub>d\<^sub>fI"(1), where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", simplified]
                intro!: "cqt:2")
    qed
    AOT_hence \<open>\<box>Numbers(x,[G]\<^sup>-\<^sup>u)\<close>
      using rigid_num_nec[unvarify F G, OF "F-u[den]", OF "F-u[den]", THEN "\<rightarrow>E",
                          OF "&I", OF props[THEN "&E"(2)]] by blast
  }
  moreover AOT_have \<open>\<box>[G]u\<close>
    using props[THEN "&E"(1), THEN "&E"(1), THEN \<zeta>[THEN "\<forall>E"(2), THEN "\<equiv>E"(2)]]
          \<xi>[THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"], THEN "\<forall>E"(2), THEN "\<rightarrow>E"]
    by blast
  ultimately AOT_have \<open>\<box>([G]u & Numbers(y,G) & Numbers(x,[G]\<^sup>-\<^sup>u))\<close>
    by (metis "KBasic:3" "&I" "\<equiv>E"(2))
  AOT_hence \<open>\<exists>u (\<box>([G]u & Numbers(y,G) & Numbers(x,[G]\<^sup>-\<^sup>u)))\<close>
    by (rule "\<exists>I")
  AOT_hence \<open>\<box>\<exists>u ([G]u & Numbers(y,G) & Numbers(x,[G]\<^sup>-\<^sup>u))\<close>
    using "Buridan" "\<rightarrow>E" by fast
  AOT_hence \<open>\<exists>F \<box>\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    by (rule "\<exists>I")
  AOT_hence 0: \<open>\<box>\<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    using Buridan "vdash-properties:10" by fast
  AOT_hence \<open>\<box>(\<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u)))\<close>
    using "KBasic:3"[THEN "\<equiv>E"(2)] by blast
  AOT_thus \<open>\<box>[\<P>]xy\<close>
    by (AOT_subst \<open>[\<P>]xy\<close> \<open>\<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>)
       (auto simp add: "pred-thm:3" 0)
qed

AOT_theorem "pred-1-1:2": \<open>Rigid(\<P>)\<close>
  by (safe intro!: "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "pred-thm:2" "&I"
                   RN tuple_forall[THEN "\<equiv>\<^sub>d\<^sub>fI"];
      safe intro!: GEN "pred-1-1:1")

AOT_theorem "pred-1-1:3": \<open>1-1(\<P>)\<close>
proof (safe intro!: "df-1-1:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "pred-thm:2" "&I" GEN "\<rightarrow>I";
       frule "&E"(1); drule "&E"(2))
  fix x y z
  AOT_assume \<open>[\<P>]xz\<close>
  AOT_hence \<open>\<exists>F\<exists>u ([F]u & Numbers(z,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    using "pred-thm:3"[THEN "\<equiv>E"(1)] by blast
  AOT_hence \<open>\<exists>F\<exists>u ([F]u & Numbers(z,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    using "&E" by blast
  then AOT_obtain F where \<open>\<exists>u ([F]u & Numbers(z,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    using "\<exists>E"[rotated] by blast
  then AOT_obtain u where u_prop: \<open>[F]u & Numbers(z,F) & Numbers(x,[F]\<^sup>-\<^sup>u)\<close>
    using "\<exists>E"[rotated] by blast
  AOT_assume \<open>[\<P>]yz\<close>
  AOT_hence \<open>\<exists>F\<exists>u ([F]u & Numbers(z,F) & Numbers(y,[F]\<^sup>-\<^sup>u))\<close>
    using "pred-thm:3"[THEN "\<equiv>E"(1)] by blast
  AOT_hence \<open>\<exists>F\<exists>u ([F]u & Numbers(z,F) & Numbers(y,[F]\<^sup>-\<^sup>u))\<close>
    using "&E" by blast
  then AOT_obtain G where \<open>\<exists>u ([G]u & Numbers(z,G) & Numbers(y,[G]\<^sup>-\<^sup>u))\<close>
    using "\<exists>E"[rotated] by blast
  then AOT_obtain v where v_prop: \<open>[G]v & Numbers(z,G) & Numbers(y,[G]\<^sup>-\<^sup>v)\<close>
    using "\<exists>E"[rotated] by blast
  AOT_show \<open>x = y\<close>
  proof (rule "pre-Hume"[unvarify G H, OF "F-u[den]", OF "F-u[den]",
                         THEN "\<rightarrow>E", OF "&I", THEN "\<equiv>E"(2)])
    AOT_show \<open>Numbers(x, [F]\<^sup>-\<^sup>u)\<close>
      using u_prop "&E" by blast
  next
    AOT_show \<open>Numbers(y, [G]\<^sup>-\<^sup>v)\<close>
      using v_prop "&E" by blast
  next
    AOT_have \<open>F \<approx>\<^sub>D G\<close>
      using u_prop[THEN "&E"(1), THEN "&E"(2)]
      using v_prop[THEN "&E"(1), THEN "&E"(2)]
      using "num-tran:2"[THEN "\<rightarrow>E", OF "&I"] by blast
    AOT_thus \<open>[F]\<^sup>-\<^sup>u \<approx>\<^sub>D [G]\<^sup>-\<^sup>v\<close>
      using u_prop[THEN "&E"(1), THEN "&E"(1)]
      using v_prop[THEN "&E"(1), THEN "&E"(1)]
      using eqP'[THEN "\<rightarrow>E", OF "&I", OF "&I"]
      by blast
  qed
qed

AOT_theorem "pred-1-1:4": \<open>Rigid\<^sub>1\<^sub>-\<^sub>1(\<P>)\<close>
  by (meson "\<equiv>\<^sub>d\<^sub>fI" "&I" "df-1-1:2" "pred-1-1:2" "pred-1-1:3")

AOT_theorem "assume-anc:1":
  \<open>[\<P>]\<^sup>* = [\<lambda>xy \<forall>F((\<forall>z([\<P>]xz \<rightarrow> [F]z) & Hereditary(F,\<P>)) \<rightarrow> [F]y)]\<close>
  apply (rule "=\<^sub>d\<^sub>fI"(1)[OF "ances-df"])
   apply "cqt:2[lambda]"
  apply (rule "=I"(1))
  by "cqt:2[lambda]"

AOT_theorem "assume-anc:2": \<open>\<P>\<^sup>*\<down>\<close>
  using "t=t-proper:1" "assume-anc:1" "vdash-properties:10" by blast

AOT_theorem "assume-anc:3":
  \<open>[\<P>\<^sup>*]xy \<equiv> \<forall>F((\<forall>z([\<P>]xz \<rightarrow> [F]z) & \<forall>x'\<forall>y'([\<P>]x'y' \<rightarrow> ([F]x' \<rightarrow> [F]y'))) \<rightarrow> [F]y)\<close>
proof -
  AOT_have prod_den: \<open>\<^bold>\<turnstile>\<^sub>\<box> \<guillemotleft>(AOT_term_of_var x\<^sub>1,AOT_term_of_var x\<^sub>2)\<guillemotright>\<down>\<close>
    for x\<^sub>1 x\<^sub>2 :: \<open>\<kappa> AOT_var\<close>
    by (simp add: "&I" "ex:1:a" prod_denotesI "rule-ui:3")
  AOT_have den: \<open>[\<lambda>xy \<forall>F((\<forall>z([\<P>]xz \<rightarrow> [F]z) & Hereditary(F,\<P>)) \<rightarrow> [F]y)]\<down>\<close>
    by "cqt:2[lambda]"
  AOT_have 1: \<open>[\<P>\<^sup>*]xy \<equiv> \<forall>F((\<forall>z([\<P>]xz \<rightarrow> [F]z) & Hereditary(F,\<P>)) \<rightarrow> [F]y)\<close>
    apply (rule "rule=E"[rotated, OF "assume-anc:1"[symmetric]])
    by (rule "beta-C-meta"[unvarify \<nu>\<^sub>1\<nu>\<^sub>n, OF prod_den, THEN "\<rightarrow>E",
                           simplified, OF den, simplified])
  show ?thesis
    apply (AOT_subst (reverse) \<open>\<forall>x'\<forall>y' ([\<P>]x'y' \<rightarrow> ([F]x' \<rightarrow> [F]y'))\<close>
                               \<open>Hereditary(F,\<P>)\<close> for: F :: \<open><\<kappa>>\<close>)
    using "hered:1"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I", OF "pred-thm:2",
                    OF "cqt:2[const_var]"[axiom_inst]] apply blast
    by (fact 1)
qed

AOT_theorem "no-pred-0:1": \<open>\<not>\<exists>x [\<P>]x 0\<close>
proof(rule "raa-cor:2")
  AOT_assume \<open>\<exists>x [\<P>]x 0\<close>
  then AOT_obtain a where \<open>[\<P>]a 0\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<open>\<exists>F\<exists>u ([F]u & Numbers(0, F) & Numbers(a, [F]\<^sup>-\<^sup>u))\<close>
    using "pred-thm:3"[unvarify y, OF "zero:2", THEN "\<equiv>E"(1)] by blast
  AOT_hence \<open>\<exists>F\<exists>u ([F]u & Numbers(0, F) & Numbers(a, [F]\<^sup>-\<^sup>u))\<close>
    using "&E" by blast
  then AOT_obtain F where \<open>\<exists>u ([F]u & Numbers(0, F) & Numbers(a, [F]\<^sup>-\<^sup>u))\<close>
    using "\<exists>E"[rotated] by blast
  then AOT_obtain u where \<open>[F]u & Numbers(0, F) & Numbers(a, [F]\<^sup>-\<^sup>u)\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<open>[F]u\<close> and num0_F: \<open>Numbers(0, F)\<close>
    using "&E" "&I" by blast+
  AOT_hence \<open>\<exists>u [F]u\<close>
    using "\<exists>I" by fast
  moreover AOT_have \<open>\<not>\<exists>u [F]u\<close>
    using num0_F  "\<equiv>E"(2) "0F:1" by blast
  ultimately AOT_show \<open>p & \<not>p\<close> for p
    by (metis "raa-cor:3")
qed

AOT_theorem "no-pred-0:2": \<open>\<not>\<exists>x [\<P>\<^sup>*]x 0\<close>
proof(rule "raa-cor:2")
  AOT_assume \<open>\<exists>x [\<P>\<^sup>*]x 0\<close>
  then AOT_obtain a where \<open>[\<P>\<^sup>*]a 0\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<open>\<exists>z [\<P>]z 0\<close>
    using "anc-her:5"[unvarify R y, OF "zero:2",
                      OF "pred-thm:2", THEN "\<rightarrow>E"] by auto
  AOT_thus \<open>\<exists>z [\<P>]z 0 & \<not>\<exists>z [\<P>]z 0\<close>
    by (metis "no-pred-0:1" "raa-cor:3")
qed

AOT_theorem "no-pred-0:3": \<open>\<not>[\<P>\<^sup>*]0 0\<close>
  by (metis "existential:1" "no-pred-0:2" "reductio-aa:1" "zero:2")

AOT_theorem "assume1:1": \<open>(=\<^sub>\<P>) = [\<lambda>xy \<exists>z ([\<P>]xz & [\<P>]yz)]\<close>
  apply (rule "=\<^sub>d\<^sub>fI"(1)[OF "id-d-R"])
   apply "cqt:2[lambda]"
  apply (rule "=I"(1))
  by "cqt:2[lambda]"

AOT_theorem "assume1:2": \<open>x =\<^sub>\<P> y \<equiv> \<exists>z ([\<P>]xz & [\<P>]yz)\<close>
proof (rule "rule=E"[rotated, OF "assume1:1"[symmetric]])
  AOT_have prod_den: \<open>\<^bold>\<turnstile>\<^sub>\<box> \<guillemotleft>(AOT_term_of_var x\<^sub>1,AOT_term_of_var x\<^sub>2)\<guillemotright>\<down>\<close>
    for x\<^sub>1 x\<^sub>2 :: \<open>\<kappa> AOT_var\<close>
    by (simp add: "&I" "ex:1:a" prod_denotesI "rule-ui:3")
  AOT_have 1: \<open>[\<lambda>xy \<exists>z ([\<P>]xz & [\<P>]yz)]\<down>\<close>
    by "cqt:2"
  AOT_show \<open>[\<lambda>xy \<exists>z ([\<P>]xz & [\<P>]yz)]xy \<equiv> \<exists>z ([\<P>]xz & [\<P>]yz)\<close>
    using "beta-C-meta"[THEN "\<rightarrow>E", OF 1, unvarify \<nu>\<^sub>1\<nu>\<^sub>n,
                        OF prod_den, simplified] by blast
qed

AOT_theorem "assume1:3": \<open>[\<P>]\<^sup>+ = [\<lambda>xy [\<P>]\<^sup>*xy \<or> x =\<^sub>\<P> y]\<close>
  apply (rule "=\<^sub>d\<^sub>fI"(1)[OF "w-ances-df"])
   apply (simp add: "w-ances-df[den1]")
  apply (rule "rule=E"[rotated, OF "assume1:1"[symmetric]])
  apply (rule "=\<^sub>d\<^sub>fI"(1)[OF "id-d-R"])
   apply "cqt:2[lambda]"
  apply (rule "=I"(1))
  by "cqt:2[lambda]"

AOT_theorem "assume1:4": \<open>[\<P>]\<^sup>+\<down>\<close>
  using "w-ances-df[den2]".

AOT_theorem "assume1:5": \<open>[\<P>]\<^sup>+xy \<equiv> [\<P>]\<^sup>*xy \<or> x =\<^sub>\<P> y\<close>
proof -
  AOT_have 0: \<open>[\<lambda>xy [\<P>]\<^sup>*xy \<or> x =\<^sub>\<P> y]\<down>\<close> by "cqt:2"
  AOT_have prod_den: \<open>\<^bold>\<turnstile>\<^sub>\<box> \<guillemotleft>(AOT_term_of_var x\<^sub>1, AOT_term_of_var x\<^sub>2)\<guillemotright>\<down>\<close>
    for x\<^sub>1 x\<^sub>2 :: \<open>\<kappa> AOT_var\<close>
    by (simp add: "&I" "ex:1:a" prod_denotesI "rule-ui:3")
  show ?thesis
    apply (rule "rule=E"[rotated, OF "assume1:3"[symmetric]])
    using "beta-C-meta"[THEN "\<rightarrow>E", OF 0, unvarify \<nu>\<^sub>1\<nu>\<^sub>n, OF prod_den, simplified]
    by (simp add: cond_case_prod_eta)
qed

AOT_define NaturalNumber :: \<open>\<tau>\<close> (\<open>\<nat>\<close>)
  "nnumber:1": \<open>\<nat> =\<^sub>d\<^sub>f [\<lambda>x [\<P>]\<^sup>+0x]\<close>

AOT_theorem "nnumber:2": \<open>\<nat>\<down>\<close>
  by (rule "=\<^sub>d\<^sub>fI"(2)[OF "nnumber:1"]; "cqt:2[lambda]")

AOT_theorem "nnumber:3": \<open>[\<nat>]x \<equiv> [\<P>]\<^sup>+0x\<close>
  apply (rule "=\<^sub>d\<^sub>fI"(2)[OF "nnumber:1"])
   apply "cqt:2[lambda]"
  apply (rule "beta-C-meta"[THEN "\<rightarrow>E"])
  by "cqt:2[lambda]"

AOT_theorem zero_suc: \<open>\<exists>x [\<P>]0x\<close>
proof -
  fix u
  AOT_have den: \<open>[\<lambda>x x =\<^sub>D u]\<down>\<close> by "cqt:2[lambda]"
  AOT_obtain a where a_prop: \<open>Numbers(a, [\<lambda>x x =\<^sub>D u])\<close>
    using "num:1"[unvarify G, OF den] "\<exists>E"[rotated] by blast
  AOT_have \<open>[\<P>]0a\<close>
  proof (safe intro!: "pred-thm:3"[unvarify x, OF "zero:2", THEN "\<equiv>E"(2)]
                      "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>[\<lambda>x x =\<^sub>D u]\<guillemotright>\<close>]
                      "\<exists>I"(2)[where \<beta>=u] "&I" den
                      "0F:1"[unvarify F, OF "F-u[den]", unvarify F,
                             OF den, THEN "\<equiv>E"(1)])
    AOT_show \<open>[\<lambda>x  x =\<^sub>D u]u\<close>
      by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" "disc=Dequiv:1" Discernible.\<psi>)
  next
    AOT_show \<open>Numbers(a,[\<lambda>x x =\<^sub>D u])\<close>
      using a_prop.
  next
    AOT_show \<open>\<not>\<exists>v [[\<lambda>x x =\<^sub>D u]\<^sup>-\<^sup>u]v\<close>
    proof(rule "raa-cor:2")
      AOT_assume \<open>\<exists>v [[\<lambda>x x =\<^sub>D u]\<^sup>-\<^sup>u]v\<close>
      then AOT_obtain v where \<open>[[\<lambda>x x =\<^sub>D u]\<^sup>-\<^sup>u]v\<close>
        using "\<exists>E"[rotated] "&E" by blast
      AOT_hence \<open>[\<lambda>z [\<lambda>x x =\<^sub>D u]z & z \<noteq>\<^sub>D u]v\<close>
        apply (rule "F-u"[THEN "=\<^sub>d\<^sub>fE"(1), where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", simplified, rotated])
        by "cqt:2[lambda]"
      AOT_hence \<open>[\<lambda>x x =\<^sub>D u]v & v \<noteq>\<^sub>D u\<close>
        by (rule "\<beta>\<rightarrow>C"(1))
      AOT_hence \<open>v =\<^sub>D u\<close> and \<open>v \<noteq>\<^sub>D u\<close>
        using "\<beta>\<rightarrow>C"(1) "&E" by blast+
      AOT_hence \<open>v =\<^sub>D u & \<not>(v =\<^sub>D u)\<close>
        by (metis "\<equiv>E"(4) "reductio-aa:1" "thm-neg=D")
      AOT_thus \<open>p & \<not>p\<close> for p
        by (metis "raa-cor:1")
    qed
  qed
  thus ?thesis by (rule "\<exists>I")
qed

AOT_theorem "0-n": \<open>[\<nat>]0\<close>
proof (safe intro!: "nnumber:3"[unvarify x, OF "zero:2", THEN "\<equiv>E"(2)]
    "assume1:5"[unvarify x y, OF "zero:2", OF "zero:2", THEN "\<equiv>E"(2)]
    "\<or>I"(2) "assume1:2"[unvarify x y, OF "zero:2", OF "zero:2", THEN "\<equiv>E"(2)])
  fix u
  AOT_have den: \<open>[\<lambda>x x =\<^sub>D u]\<down>\<close> by "cqt:2[lambda]"
  AOT_obtain a where a_prop: \<open>[\<P>]0a\<close>
    using zero_suc  "\<exists>E"[rotated] by blast
  AOT_thus \<open>\<exists>z ([\<P>]0z & [\<P>]0z)\<close>
    by (safe intro!: "&I" "\<exists>I"(2)[where \<beta>=a])
qed

AOT_theorem "mod-col-num:1": \<open>[\<nat>]x \<rightarrow> \<box>[\<nat>]x\<close>
proof(rule "\<rightarrow>I")
  AOT_have nec0N: \<open>[\<lambda>x \<box>[\<nat>]x]0\<close>
    by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" simp: "zero:2" RN "0-n")
  AOT_have 1: \<open>[\<lambda>x \<box>[\<nat>]x]0 &
    \<forall>x\<forall>y ([[\<P>]\<^sup>+]0x & [[\<P>]\<^sup>+]0y \<rightarrow> ([\<P>]xy \<rightarrow> ([\<lambda>x \<box>[\<nat>]x]x \<rightarrow> [\<lambda>x \<box>[\<nat>]x]y))) \<rightarrow>
    \<forall>x ([[\<P>]\<^sup>+]0x \<rightarrow> [\<lambda>x \<box>[\<nat>]x]x)\<close>
    by (auto intro!: "cqt:2"
              intro: "pre-ind"[unconstrain \<R>, unvarify \<beta>, OF "pred-thm:2",
                               THEN "\<rightarrow>E", OF "pred-1-1:4", unvarify z, OF "zero:2",
                               unvarify F])
  AOT_have \<open>\<forall>x ([[\<P>]\<^sup>+]0x \<rightarrow> [\<lambda>x \<box>[\<nat>]x]x)\<close>
  proof (rule 1[THEN "\<rightarrow>E"]; safe intro!: "&I" GEN "\<rightarrow>I" nec0N;
         frule "&E"(1); drule "&E"(2))
    fix x y
    AOT_assume \<open>[\<P>]xy\<close>
    AOT_hence 0: \<open>\<box>[\<P>]xy\<close>
      by (metis "pred-1-1:1" "\<rightarrow>E")
    AOT_assume \<open>[\<lambda>x \<box>[\<nat>]x]x\<close>
    AOT_hence \<open>\<box>[\<nat>]x\<close>
      by (rule "\<beta>\<rightarrow>C"(1))
    AOT_hence \<open>\<box>([\<P>]xy & [\<nat>]x)\<close>
      by (metis "0" "KBasic:3" Adjunction "\<equiv>E"(2) "\<rightarrow>E")
    moreover AOT_have \<open>\<box>([\<P>]xy & [\<nat>]x) \<rightarrow> \<box>[\<nat>]y\<close>
    proof (rule RM; rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
      AOT_modally_strict {
        AOT_assume 0: \<open>[\<P>]xy\<close>
        AOT_assume \<open>[\<nat>]x\<close>
        AOT_hence 1: \<open>[[\<P>]\<^sup>+]0x\<close>
          by (metis "\<equiv>E"(1) "nnumber:3")
        AOT_show \<open>[\<nat>]y\<close>
          apply (rule "nnumber:3"[THEN "\<equiv>E"(2)])
          apply (rule "assume1:5"[unvarify x, OF "zero:2", THEN "\<equiv>E"(2)])
          apply (rule "\<or>I"(1))
          apply (rule "w-ances-her:3"[unconstrain \<R>, unvarify \<beta>, OF "pred-thm:2",
                                      THEN "\<rightarrow>E", OF "pred-1-1:4", unvarify x,
                                      OF "zero:2", THEN "\<rightarrow>E"])
          apply (rule "&I")
           apply (fact 1)
          by (fact 0)
      }
    qed
    ultimately AOT_have \<open>\<box>[\<nat>]y\<close>
      by (metis "\<rightarrow>E") 
    AOT_thus \<open>[\<lambda>x \<box>[\<nat>]x]y\<close>
      by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2")
  qed
  AOT_hence 0: \<open>[[\<P>]\<^sup>+]0x \<rightarrow> [\<lambda>x \<box>[\<nat>]x]x\<close>
    using "\<forall>E"(2) by blast
  AOT_assume \<open>[\<nat>]x\<close>
  AOT_hence \<open>[[\<P>]\<^sup>+]0x\<close>
    by (metis "\<equiv>E"(1) "nnumber:3")
  AOT_hence \<open>[\<lambda>x \<box>[\<nat>]x]x\<close>
    using 0[THEN "\<rightarrow>E"] by blast
  AOT_thus \<open>\<box>[\<nat>]x\<close>
    by (rule "\<beta>\<rightarrow>C"(1))
qed

AOT_theorem "mod-col-num:2": \<open>Rigid(\<nat>)\<close>
  by (safe intro!: "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" RN GEN
                   "mod-col-num:1" "nnumber:2")

AOT_register_rigid_restricted_type
  Number: \<open>[\<nat>]\<kappa>\<close>
proof
  AOT_modally_strict {
    AOT_show \<open>\<exists>x [\<nat>]x\<close>
      by (rule "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>0\<guillemotright>\<close>]; simp add: "0-n" "zero:2")
  }
next
  AOT_modally_strict {
    AOT_show \<open>[\<nat>]\<kappa> \<rightarrow> \<kappa>\<down>\<close> for \<kappa>
      by (simp add: "\<rightarrow>I" "cqt:5:a[1]"[axiom_inst, THEN "\<rightarrow>E", THEN "&E"(2)])
  }
next
  AOT_modally_strict {
    AOT_show \<open>\<box>([\<nat>]x \<rightarrow> \<box>[\<nat>]x)\<close> for x
      by (simp add: RN "mod-col-num:1")
  }
qed
AOT_register_variable_names
  Number: m n k i j

AOT_theorem "0-pred": \<open>\<not>\<exists>n [\<P>]n 0\<close>
proof (rule "raa-cor:2")
  AOT_assume \<open>\<exists>n [\<P>]n 0\<close>
  then AOT_obtain n where \<open>[\<P>]n 0\<close>
    using "Number.\<exists>E"[rotated] by meson
  AOT_hence \<open>\<exists>x [\<P>]x 0\<close>
    using "&E" "\<exists>I" by fast
  AOT_thus \<open>\<exists>x [\<P>]x 0 & \<not>\<exists>x [\<P>]x 0\<close>
    using "no-pred-0:1" "&I" by auto
qed

AOT_theorem "no-same-succ":
  \<open>\<forall>n\<forall>m\<forall>k([\<P>]nk & [\<P>]mk \<rightarrow> n = m)\<close>
proof(safe intro!: Number.GEN "\<rightarrow>I")
  fix n m k
  AOT_assume \<open>[\<P>]nk & [\<P>]mk\<close>
  AOT_thus \<open>n = m\<close>
    by (safe intro!: "cqt:2[const_var]"[axiom_inst] "df-1-1:3"[
          unvarify R, OF "pred-thm:2",
          THEN "\<rightarrow>E", OF "pred-1-1:4", THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"],
          THEN "\<equiv>\<^sub>d\<^sub>fE"[OF "df-1-1:1"], THEN "&E"(2), THEN "\<forall>E"(1), THEN "\<forall>E"(1),
          THEN "\<forall>E"(1)[where \<tau>=\<open>AOT_term_of_var (Number.Rep k)\<close>], THEN "\<rightarrow>E"])
qed

AOT_theorem induction:
  \<open>\<forall>F([F]0 & \<forall>n\<forall>m([\<P>]nm \<rightarrow> ([F]n \<rightarrow> [F]m)) \<rightarrow> \<forall>n[F]n)\<close>
proof (safe intro!: GEN[where 'a=\<open><\<kappa>>\<close>] Number.GEN "&I" "\<rightarrow>I";
       frule "&E"(1); drule "&E"(2))
  fix F n
  AOT_assume F0: \<open>[F]0\<close>
  AOT_assume 0: \<open>\<forall>n\<forall>m([\<P>]nm \<rightarrow> ([F]n \<rightarrow> [F]m))\<close>
  {
    fix x y
    AOT_assume \<open>[[\<P>]\<^sup>+]0x & [[\<P>]\<^sup>+]0y\<close>
    AOT_hence \<open>[\<nat>]x\<close> and \<open>[\<nat>]y\<close>
      using "&E" "\<equiv>E"(2) "nnumber:3" by blast+
    moreover AOT_assume \<open>[\<P>]xy\<close>
    moreover AOT_assume \<open>[F]x\<close>
    ultimately AOT_have \<open>[F]y\<close>
      using 0[THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<forall>E"(2), THEN "\<rightarrow>E",
              THEN "\<rightarrow>E", THEN "\<rightarrow>E"] by blast
  } note 1 = this
  AOT_have 0: \<open>[[\<P>]\<^sup>+]0n\<close>
    by (metis "\<equiv>E"(1) "nnumber:3" Number.\<psi>)
  AOT_show \<open>[F]n\<close>
    apply (rule "pre-ind"[unconstrain \<R>, unvarify \<beta>, THEN "\<rightarrow>E", OF "pred-thm:2",
                          OF "pred-1-1:4", unvarify z, OF "zero:2", THEN "\<rightarrow>E",
                          THEN "\<forall>E"(2), THEN "\<rightarrow>E"];
           safe intro!: 0 "&I" GEN "\<rightarrow>I" F0)
    using 1 by blast
qed

AOT_theorem "suc-num:1": \<open>[\<P>]nx \<rightarrow> [\<nat>]x\<close>
proof(rule "\<rightarrow>I")
  AOT_have \<open>[[\<P>]\<^sup>+]0 n\<close>
    by (meson Number.\<psi> "\<equiv>E"(1) "nnumber:3")
  moreover AOT_assume \<open>[\<P>]nx\<close>
  ultimately AOT_have \<open>[[\<P>]\<^sup>*]0 x\<close>
    using "w-ances-her:3"[unconstrain \<R>, unvarify \<beta>, OF "pred-thm:2", THEN "\<rightarrow>E",
                          OF "pred-1-1:4", unvarify x, OF "zero:2",
                          THEN "\<rightarrow>E", OF "&I"]
    by blast
  AOT_hence \<open>[[\<P>]\<^sup>+]0 x\<close> 
    using "assume1:5"[unvarify x, OF "zero:2", THEN "\<equiv>E"(2), OF "\<or>I"(1)]
    by blast
  AOT_thus \<open>[\<nat>]x\<close>
    by (metis "\<equiv>E"(2) "nnumber:3")
qed

AOT_theorem "suc-num:2": \<open>[[\<P>]\<^sup>*]nx \<rightarrow> [\<nat>]x\<close>
proof(rule "\<rightarrow>I")
  AOT_have \<open>[[\<P>]\<^sup>+]0 n\<close>
    using Number.\<psi> "\<equiv>E"(1) "nnumber:3" by blast
  AOT_assume \<open>[[\<P>]\<^sup>*]n x\<close>
  AOT_hence \<open>\<forall>F (\<forall>z ([\<P>]nz \<rightarrow> [F]z) & \<forall>x'\<forall>y' ([\<P>]x'y' \<rightarrow> ([F]x' \<rightarrow> [F]y')) \<rightarrow> [F]x)\<close>
    using "assume-anc:3"[THEN "\<equiv>E"(1)] by blast
  AOT_hence \<theta>: \<open>\<forall>z ([\<P>]nz \<rightarrow> [\<nat>]z) & \<forall>x'\<forall>y' ([\<P>]x'y' \<rightarrow> ([\<nat>]x' \<rightarrow> [\<nat>]y')) \<rightarrow> [\<nat>]x\<close>
    using "\<forall>E"(1) "nnumber:2" by blast
  AOT_show \<open>[\<nat>]x\<close>
  proof (safe intro!: \<theta>[THEN "\<rightarrow>E"] GEN "\<rightarrow>I" "&I")
    AOT_show \<open>[\<nat>]z\<close> if \<open>[\<P>]nz\<close> for z
      using Number.\<psi> "suc-num:1" that "\<rightarrow>E" by blast
  next
    AOT_show \<open>[\<nat>]y\<close> if \<open>[\<P>]xy\<close> and \<open>[\<nat>]x\<close> for x y
      using "suc-num:1"[unconstrain n, THEN "\<rightarrow>E"] that "\<rightarrow>E" by blast
  qed
qed

AOT_theorem "suc-num:3": \<open>[\<P>]\<^sup>+nx \<rightarrow> [\<nat>]x\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>[\<P>]\<^sup>+nx\<close>
  AOT_hence \<open>[\<P>]\<^sup>*nx \<or> n =\<^sub>\<P> x\<close>
    by (metis "assume1:5" "\<equiv>E"(1))
  moreover {
    AOT_assume \<open>[\<P>]\<^sup>*nx\<close>
    AOT_hence \<open>[\<nat>]x\<close>
      by (metis "suc-num:2" "\<rightarrow>E")
  }
  moreover {
    AOT_assume \<open>n =\<^sub>\<P> x\<close>
    AOT_hence \<open>n = x\<close>
      using "id-R-thm:3"[unconstrain \<R>, unvarify \<beta>, OF "pred-thm:2",
                         THEN "\<rightarrow>E", OF "pred-1-1:4", THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>[\<nat>]x\<close>
      by (metis "rule=E" Number.\<psi>)
  }
  ultimately AOT_show \<open>[\<nat>]x\<close>
    by (metis "\<or>E"(3) "reductio-aa:1")
qed

AOT_theorem "pred-num": \<open>[\<P>]xn \<rightarrow> [\<nat>]x\<close>
proof (rule "\<rightarrow>I")
  AOT_assume 0: \<open>[\<P>]xn\<close>
  AOT_have \<open>[[\<P>]\<^sup>+]0 n\<close>
    using Number.\<psi> "\<equiv>E"(1) "nnumber:3" by blast
  AOT_hence \<open>[[\<P>]\<^sup>*]0 n \<or> 0 =\<^sub>\<P> n\<close>
    using "assume1:5"[unvarify x, OF "zero:2"] by (metis "\<equiv>E"(1))
  moreover {
    AOT_assume \<open>0 =\<^sub>\<P> n\<close>
    AOT_hence \<open>\<exists>z ([\<P>]0z & [\<P>]nz)\<close>
      using "assume1:2"[unvarify x, OF "zero:2", THEN "\<equiv>E"(1)] by blast
    then AOT_obtain a where \<open>[\<P>]0a & [\<P>]na\<close> using "\<exists>E"[rotated] by blast
    AOT_hence \<open>0 = n\<close>
      using "pred-1-1:3"[THEN "df-1-1:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2),
                         THEN "\<forall>E"(1), OF "zero:2", THEN "\<forall>E"(2),
                         THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>[\<P>]x 0\<close>
      using 0 "rule=E" id_sym by fast
    AOT_hence \<open>\<exists>x [\<P>]x 0\<close>
      by (rule "\<exists>I")
    AOT_hence \<open>\<exists>x [\<P>]x 0 & \<not>\<exists>x [\<P>]x 0\<close>
      by (metis "no-pred-0:1" "raa-cor:3")
  }
  ultimately AOT_have \<open>[[\<P>]\<^sup>*]0n\<close>
    by (metis "\<or>E"(3) "raa-cor:1")
  AOT_hence \<open>\<exists>z ([[\<P>]\<^sup>+]0z & [\<P>]zn)\<close>
    using "w-ances-her:7"[unconstrain \<R>, unvarify \<beta>, OF "pred-thm:2",
                          THEN "\<rightarrow>E", OF "pred-1-1:4", unvarify x,
                          OF "zero:2", THEN "\<rightarrow>E"] by blast
  then AOT_obtain b where b_prop: \<open>[[\<P>]\<^sup>+]0b & [\<P>]bn\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<open>[\<nat>]b\<close>
    by (metis "&E"(1) "\<equiv>E"(2) "nnumber:3")
  moreover AOT_have \<open>x = b\<close>
    using "pred-1-1:3"[THEN "df-1-1:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2),
                       THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E",
                       OF "&I", OF 0, OF b_prop[THEN "&E"(2)]].
  ultimately AOT_show \<open>[\<nat>]x\<close>
    using "rule=E" id_sym by fast
qed

AOT_theorem "nat-card": \<open>[\<nat>]x \<rightarrow> NaturalCardinal(x)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>[\<nat>]x\<close>
  AOT_hence \<open>[[\<P>]\<^sup>+]0x\<close>
    by (metis "\<equiv>E"(1) "nnumber:3")
  AOT_hence \<open>[[\<P>]\<^sup>*]0x \<or> 0 =\<^sub>\<P> x\<close>
    using "assume1:5"[unvarify x, OF "zero:2", THEN "\<equiv>E"(1)] by blast
  moreover {
    AOT_assume \<open>[[\<P>]\<^sup>*]0x\<close>
    then AOT_obtain a where \<open>[\<P>]ax\<close>
      using "anc-her:5"[unvarify R x, OF "zero:2", OF "pred-thm:2", THEN "\<rightarrow>E"]
            "\<exists>E"[rotated] by blast
    AOT_hence \<open>\<exists>F\<exists>u ([F]u & Numbers(x,F) & Numbers(a,[F]\<^sup>-\<^sup>u))\<close>
      using "pred-thm:3"[THEN "\<equiv>E"(1)] by blast
    AOT_hence \<open>\<exists>F\<exists>u ([F]u & Numbers(x,F) & Numbers(a,[F]\<^sup>-\<^sup>u))\<close>
      using "&E" by blast
    then AOT_obtain F where \<open>\<exists>u ([F]u & Numbers(x,F) & Numbers(a,[F]\<^sup>-\<^sup>u))\<close>
      using "\<exists>E"[rotated] by blast
    then AOT_obtain u where \<open>[F]u & Numbers(x,F) & Numbers(a,[F]\<^sup>-\<^sup>u)\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>NaturalCardinal(x)\<close>
      using "eq-num:6"[THEN "\<rightarrow>E"] "&E" by blast
  }
  moreover {
    AOT_assume \<open>0 =\<^sub>\<P> x\<close>
    AOT_hence \<open>0 = x\<close>
      using "id-R-thm:3"[unconstrain \<R>, unvarify \<beta>, OF "pred-thm:2",
                         THEN "\<rightarrow>E", OF "pred-1-1:4", unvarify x,
                         OF "zero:2", THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>NaturalCardinal(x)\<close>
      by (metis "rule=E" "zero-card")
  }
  ultimately AOT_show \<open>NaturalCardinal(x)\<close>
    by (metis "\<or>E"(2) "raa-cor:1")
qed

AOT_theorem "pred-func:1": \<open>[\<P>]xy & [\<P>]xz \<rightarrow> y = z\<close>
proof (rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume \<open>[\<P>]xy\<close>
  AOT_hence \<open>\<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    using "pred-thm:3"[THEN "\<equiv>E"(1)] by blast
  AOT_hence \<open>\<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    using "&E" by blast
  then AOT_obtain F where \<open>\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    using "\<exists>E"[rotated] by blast
  then AOT_obtain a where
    a_prop: \<open>[F]a & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>a)\<close>
    using "\<exists>E"[rotated] "&E" by blast
  AOT_assume \<open>[\<P>]xz\<close>
  AOT_hence \<open> \<exists>F\<exists>u ([F]u & Numbers(z,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    using "pred-thm:3"[THEN "\<equiv>E"(1)] by blast
  AOT_hence \<open>\<exists>F\<exists>u ([F]u & Numbers(z,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    using "&E" by blast
  then AOT_obtain G where \<open>\<exists>u ([G]u & Numbers(z,G) & Numbers(x,[G]\<^sup>-\<^sup>u))\<close>
    using "\<exists>E"[rotated] by blast
  then AOT_obtain b where b_prop: \<open>[G]b & Numbers(z,G) & Numbers(x,[G]\<^sup>-\<^sup>b)\<close>
    using "\<exists>E"[rotated] "&E" by blast
  AOT_have \<open>[F]\<^sup>-\<^sup>a \<approx>\<^sub>D  [G]\<^sup>-\<^sup>b\<close>
    using "num-tran:2"[unvarify G H, OF "F-u[den]", OF "F-u[den]",
                       THEN "\<rightarrow>E", OF "&I", OF a_prop[THEN "&E"(2)],
                       OF b_prop[THEN "&E"(2)]].
  AOT_hence \<open>F \<approx>\<^sub>D G\<close>
    using "P'-eq"[THEN "\<rightarrow>E", OF "&I", OF "&I"]
          a_prop[THEN "&E"(1), THEN "&E"(1)]
          b_prop[THEN "&E"(1), THEN "&E"(1)] by blast
  AOT_thus \<open>y = z\<close>
    using "pre-Hume"[THEN "\<rightarrow>E", THEN "\<equiv>E"(2), OF "&I",
                     OF a_prop[THEN "&E"(1), THEN "&E"(2)],
                     OF b_prop[THEN "&E"(1), THEN "&E"(2)]]
    by blast
qed

AOT_theorem "pred-func:2": \<open>[\<P>]nm & [\<P>]nk \<rightarrow> m = k\<close>
  using "pred-func:1".



AOT_theorem
  CardinalSuc:
  assumes \<open>NaturalCardinal(x)\<close>
  assumes \<open>x \<noteq> 0\<close>
  shows \<open>\<exists>y [\<P>]yx\<close>
proof -
  AOT_have \<open>\<exists>G x = #G\<close>
    using card[THEN "\<equiv>\<^sub>d\<^sub>fE", OF assms(1)].
  AOT_hence \<open>\<exists>G Numbers(x,G)\<close>
    using "eq-df-num"[THEN "\<equiv>E"(1)] by blast
  then AOT_obtain G' where numxG': \<open>Numbers(x,G')\<close>
    using "\<exists>E"[rotated] by blast
  AOT_obtain G where \<open>Rigidifies(G,G')\<close>
    using "rigid-der:3" "\<exists>E"[rotated] by blast

  AOT_hence H: \<open>Rigid(G) & \<forall>x ([G]x \<equiv> [G']x)\<close>
    using "df-rigid-rel:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_have H_rigid: \<open>\<box>\<forall>x ([G]x \<rightarrow> \<box>[G]x)\<close>
    using H[THEN "&E"(1), THEN "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2)].
  AOT_hence \<open>\<forall>x \<box>([G]x \<rightarrow> \<box>[G]x)\<close>
    using "CBF" "vdash-properties:10" by blast
  AOT_hence R: \<open>\<box>([G]x \<rightarrow> \<box>[G]x)\<close> for x using "\<forall>E"(2) by blast
  AOT_hence rigid: \<open>[G]x \<equiv> \<^bold>\<A>[G]x\<close> for x
     by (metis "\<equiv>E"(6) "oth-class-taut:3:a" "sc-eq-fur:2" "\<rightarrow>E")
  AOT_have \<open>G \<equiv>\<^sub>D G'\<close>
  proof (safe intro!: eqD[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" GEN "\<rightarrow>I")
    AOT_show \<open>[G]u \<equiv> [G']u\<close> for u using H[THEN "&E"(2)] "\<forall>E"(2) by fast
  qed
  AOT_hence \<open>G \<approx>\<^sub>D G'\<close>
    by (rule "apE-eqE:2"[THEN "\<rightarrow>E", OF "&I", rotated])
       (simp add: "eq-part:1")
  AOT_hence numxG: \<open>Numbers(x,G)\<close>
    using "num-tran:1"[THEN "\<rightarrow>E", THEN "\<equiv>E"(2)] numxG' by blast

  {
    AOT_assume \<open>\<not>\<exists>y(y \<noteq> x & [\<P>]yx)\<close>
    AOT_hence \<open>\<forall>y \<not>(y \<noteq> x & [\<P>]yx)\<close>
      by (metis "cqt-further:4" "\<rightarrow>E")
    AOT_hence \<open>\<not>(y \<noteq> x & [\<P>]yx)\<close> for y using "\<forall>E"(2) by blast
    AOT_hence 0: \<open>\<not>y \<noteq> x \<or> \<not>[\<P>]yx\<close> for y  by (metis "\<not>\<not>E" "intro-elim:3:c" "oth-class-taut:5:a")
    {
      fix y
      AOT_assume \<open>[\<P>]yx\<close>
      AOT_hence \<open>\<not>y \<noteq> x\<close>
        using 0
        by (metis "\<not>\<not>I" "con-dis-i-e:4:c") 
      AOT_hence \<open>y = x\<close>
        using "=-infix" "\<equiv>\<^sub>d\<^sub>fI" "raa-cor:4" by blast
    } note Pxy_imp_eq = this
    AOT_have \<open>[\<P>]xx\<close>
    proof(rule "raa-cor:1")
      AOT_assume notPxx: \<open>\<not>[\<P>]xx\<close>
      AOT_hence \<open>\<not>\<exists>F\<exists>u([F]u & Numbers(x,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
        using "pred-thm:3" using "intro-elim:3:c" by blast
      AOT_hence \<open>\<forall>F \<not>\<exists>u([F]u & Numbers(x,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
        using "cqt-further:4"[THEN "\<rightarrow>E"] by blast
      AOT_hence \<open>\<not>\<exists>u([F]u & Numbers(x,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close> for F using "\<forall>E"(2) by blast
      AOT_hence \<open>\<forall>u \<not>([F]u & Numbers(x,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close> for F
        using "cqt-further:4"[THEN "\<rightarrow>E"] by blast
      AOT_hence 0: \<open>\<not>([F]u & Numbers(x,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close> for F u using "\<forall>E"(2) by blast
      AOT_have \<open>\<box>\<not>\<exists>u [G]u\<close>
      proof(rule "raa-cor:1")
        AOT_assume \<open>\<not>\<box>\<not>\<exists>u [G]u\<close>
        AOT_hence \<open>\<diamond>\<exists>u [G]u\<close>
          using "\<equiv>\<^sub>d\<^sub>fI" "conventions:5" by blast
        AOT_hence \<open>\<exists>u \<diamond>[G]u\<close>
          by (metis "BF\<diamond>" "vdash-properties:10")
        then AOT_obtain u where posGu: \<open>\<diamond>[G]u\<close>
          using "\<exists>E"[rotated] by blast
        AOT_hence Gu: \<open>[G]u\<close>
          by (meson "B\<diamond>" "K\<diamond>" "\<rightarrow>E" R)
        AOT_have \<open>\<not>([G]u & Numbers(x,G) & Numbers(x,[G]\<^sup>-\<^sup>u))\<close>
          using 0 by blast
        AOT_hence notnumx: \<open>\<not>Numbers(x,[G]\<^sup>-\<^sup>u)\<close>
          using Gu numxG "con-dis-i-e:1" "raa-cor:5" by metis
        AOT_obtain y where numy: \<open>Numbers(y,[G]\<^sup>-\<^sup>u)\<close>
          using "num:1"[unvarify G, OF "F-u[den]"] "\<exists>E"[rotated] by blast
        AOT_hence \<open>[G]u & Numbers(x,G) & Numbers(y,[G]\<^sup>-\<^sup>u)\<close>
          using Gu numxG "&I" by blast
        AOT_hence \<open>\<exists>u ([G]u & Numbers(x,G) & Numbers(y,[G]\<^sup>-\<^sup>u))\<close>
          by (rule "\<exists>I")
        AOT_hence \<open>\<exists>G\<exists>u ([G]u & Numbers(x,G) & Numbers(y,[G]\<^sup>-\<^sup>u))\<close>
          by (rule "\<exists>I")
        AOT_hence \<open>[\<P>]yx\<close>
          using "pred-thm:3"[THEN "\<equiv>E"(2)] by blast
        AOT_hence \<open>y = x\<close> using Pxy_imp_eq by blast
        AOT_hence \<open>Numbers(x,[G]\<^sup>-\<^sup>u)\<close>
          using numy "rule=E" by fast
        AOT_thus \<open>p & \<not>p\<close> for p using notnumx "reductio-aa:1" by blast
      qed
      AOT_hence \<open>\<not>\<exists>u [G]u\<close>
        using "qml:2"[axiom_inst, THEN "\<rightarrow>E"] by blast
      AOT_hence num0G: \<open>Numbers(0, G)\<close>
        using "0F:1"[THEN "\<equiv>E"(1)] by blast
      AOT_hence \<open>x = 0\<close>
        using "pre-Hume"[unvarify x, THEN "\<rightarrow>E", OF "zero:2", OF "&I", THEN "\<equiv>E"(2), OF num0G, OF numxG, OF "eq-part:1"]
          id_sym by blast
      moreover AOT_have \<open>\<not>x = 0\<close>
        using assms(2)
        using "=-infix" "\<equiv>\<^sub>d\<^sub>fE" by blast
      ultimately AOT_show \<open>p & \<not>p\<close> for p using "reductio-aa:1" by blast
    qed
  }
  AOT_hence \<open>[\<P>]xx \<or> \<exists>y (y \<noteq> x & [\<P>]yx)\<close>
    by (metis "con-dis-i-e:3:a" "con-dis-i-e:3:b" "raa-cor:1")
  moreover {
    AOT_assume \<open>[\<P>]xx\<close>
    AOT_hence \<open>\<exists>y [\<P>]yx\<close>
      by (rule "\<exists>I")
  }
  moreover {
    AOT_assume \<open>\<exists>y (y \<noteq> x & [\<P>]yx)\<close>
    then AOT_obtain y where \<open>y \<noteq> x & [\<P>]yx\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>[\<P>]yx\<close>
      using "&E" by blast
    AOT_hence \<open>\<exists>y [\<P>]yx\<close>
      by (rule "\<exists>I")
  }
  ultimately show ?thesis
    using "\<or>E"(1) "\<rightarrow>I" by blast
qed

AOT_theorem card_disc: \<open>NaturalCardinal(x) \<rightarrow> D!x\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_assume \<open>NaturalCardinal(x)\<close>
  AOT_hence \<open>\<box>NaturalCardinal(x)\<close>
    using "natcard-nec"[THEN "\<rightarrow>E"] by blast
  moreover AOT_have \<open>\<box>NaturalCardinal(x) \<rightarrow> \<box>\<forall>y (y \<noteq> x \<rightarrow> \<exists>F \<not>([F]y \<equiv> [F]x))\<close>
  proof(rule RM; safe intro!: "\<rightarrow>I" GEN)
    AOT_modally_strict {
      fix y
      AOT_assume 0: \<open>NaturalCardinal(x)\<close>
      AOT_assume \<open>y \<noteq> x\<close>
      AOT_hence noteq: \<open>\<not>y = x\<close>
        using "=-infix"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
      AOT_show \<open>\<exists>F \<not>([F]y \<equiv> [F]x)\<close>
      proof(rule "raa-cor:1")
        AOT_assume \<open>\<not>\<exists>F \<not>([F]y \<equiv> [F]x)\<close>
        AOT_hence indist: \<open>\<forall>F([F]y \<equiv> [F]x)\<close>
           by (metis "cqt-further:3" "intro-elim:3:b")
        {
          AOT_assume \<open>\<not>(x = 0)\<close>
          AOT_hence \<open>x \<noteq> 0\<close>
            by (metis "=-infix" "\<equiv>\<^sub>d\<^sub>fI")
          AOT_hence \<open>\<exists>y [\<P>]yx\<close>
            using CardinalSuc 0 by blast
          then AOT_obtain z where Pxz: \<open>[\<P>]zx\<close>
            using "\<exists>E"[rotated] by blast
          AOT_hence \<open>[\<lambda>y [\<P>]zy]x\<close>
            by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2")
          AOT_hence \<open>[\<lambda>y [\<P>]zy]y\<close>
            by (safe intro!: indist[THEN "\<forall>E"(1), THEN "\<equiv>E"(2)] "cqt:2")
          AOT_hence Pyz: \<open>[\<P>]zy\<close>
            by (metis "\<beta>\<rightarrow>C"(1))
          AOT_have \<open>x = y\<close>
            using "pred-func:1"[THEN "\<rightarrow>E", OF "&I", OF Pxz, OF Pyz].
        }
        moreover {
          AOT_assume x_is_zero: \<open>x = 0\<close>
          AOT_hence \<open>\<exists>z [\<P>]xz\<close>
            using zero_suc "rule=E" id_sym by fast
          then AOT_obtain z where Pxz: \<open>[\<P>]xz\<close>
            using "\<exists>E"[rotated] by blast
          AOT_hence \<open>[\<lambda>y [\<P>]yz]x\<close>
            by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2")
          AOT_hence \<open>[\<lambda>y [\<P>]yz]y\<close>
            by (safe intro!: indist[THEN "\<forall>E"(1), THEN "\<equiv>E"(2)] "cqt:2")
          AOT_hence Pyz: \<open>[\<P>]yz\<close>
            by (metis "betaC:1:a")
          AOT_hence \<open>x = y\<close>
            using "pred-1-1:3"[THEN "df-1-1:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"]
                  Pxz Pyz "&I" by blast
        }
        ultimately AOT_have \<open>x = y\<close> by (metis "reductio-aa:1")
        AOT_thus \<open>p & \<not>p\<close> for p using id_sym noteq "&I" "reductio-aa:1" by blast
      qed
    }
  qed
  ultimately AOT_show \<open>D!x\<close>
    apply (AOT_subst_thm Discernible_equiv)
    using "\<rightarrow>E" by blast
qed

AOT_define restr_rel :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<Pi>\<close> (\<open>_\<^sub>\<restriction>\<^sub>_\<close>)
 "dig-alt:1": \<open>R\<^sub>\<restriction>\<^sub>F =\<^sub>d\<^sub>f [\<lambda>xy [F]x & [R]xy]\<close>

AOT_theorem "dig-alt:2": \<open>R\<^sub>\<restriction>\<^sub>F\<down>\<close>
  by (rule "rule-id-df:2:b"[where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", OF "dig-alt:1", simplified])
     (safe intro!: "cqt:2")

AOT_theorem "dig-alt:3": \<open>[R\<^sub>\<restriction>\<^sub>F]xy \<equiv> [F]x & [R]xy\<close>
  apply (rule "rule-id-df:2:b"[where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", OF "dig-alt:1", simplified])
   apply (safe intro!: "cqt:2" "\<equiv>I"  "\<rightarrow>I" dest!: "\<beta>\<rightarrow>C")
  apply (safe_step intro!: "\<beta>\<leftarrow>C")
  by (safe intro!: "cqt:2" tuple_denotes[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I")



AOT_theorem "rigid-restrict": \<open>Rigid(R) & Rigid(F) \<rightarrow> Rigid(R\<^sub>\<restriction>\<^sub>F)\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume \<open>Rigid(R)\<close>
  AOT_hence \<open>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([R]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[R]x\<^sub>1...x\<^sub>n)\<close> using "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_hence \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n \<box>([R]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[R]x\<^sub>1...x\<^sub>n)\<close> using "BFs:2"[THEN "\<rightarrow>E"] by blast
  AOT_hence 0: \<open>\<forall>x\<forall>y \<box>([R]xy \<rightarrow> \<box>[R]xy)\<close> using tuple_forall[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_assume \<open>Rigid(F)\<close>
  AOT_hence \<open>\<box>\<forall>x ([F]x \<rightarrow> \<box>[F]x)\<close> using "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_hence 1: \<open>\<forall>x \<box>([F]x \<rightarrow> \<box>[F]x)\<close> using "BFs:2"[THEN "\<rightarrow>E"] by blast
  AOT_show \<open>Rigid(R\<^sub>\<restriction>\<^sub>F)\<close>
  proof (safe intro!: "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "dig-alt:2")
    AOT_have \<open>\<forall>x\<forall>y \<box>([\<lambda>xy [F]x & [R]xy]xy \<rightarrow> \<box>[\<lambda>xy [F]x & [R]xy]xy)\<close>
    proof(safe intro!: GEN)
      fix x y
      AOT_show \<open>\<box>([\<lambda>xy [F]x & [R]xy]xy \<rightarrow> \<box>[\<lambda>xy [F]x & [R]xy]xy)\<close>
      proof (AOT_subst \<open>[\<lambda>xy [F]x & [R]xy]xy\<close> \<open>[F]x & [R]xy\<close>)
        AOT_modally_strict {
          AOT_have 0: \<open>[\<lambda>xy [F]x & [R]xy]\<down>\<close> by "cqt:2"
          AOT_show \<open>[\<lambda>xy [F]x & [R]xy]xy \<equiv> [F]x & [R]xy\<close>
            by (safe intro!: "beta-C-meta"[THEN "\<rightarrow>E", OF 0, unvarify \<nu>\<^sub>1\<nu>\<^sub>n, where \<tau>=\<open>(_,_)\<close>, simplified] tuple_denotes[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2")
        }
      next
        AOT_have \<open>\<box>([R]xy \<rightarrow> \<box>[R]xy)\<close> using 0 "\<forall>E"(2) by blast
        moreover AOT_have \<open>\<box>([F]x \<rightarrow> \<box>[F]x)\<close> using 1 "\<forall>E"(2) by blast
        ultimately AOT_have \<open>\<box>(([R]xy \<rightarrow> \<box>[R]xy) & ([F]x \<rightarrow> \<box>[F]x))\<close>
          using  "KBasic:3" "con-dis-i-e:1" "intro-elim:3:c" "raa-cor:3" by metis
        moreover AOT_have \<open>\<box>((([R]xy \<rightarrow> \<box>[R]xy) & ([F]x \<rightarrow> \<box>[F]x)) \<rightarrow> ([F]x & [R]xy \<rightarrow> \<box>([F]x & [R]xy)))\<close>
        proof(rule RN; rule "\<rightarrow>I")
          AOT_modally_strict {
            AOT_assume \<open>([R]xy \<rightarrow> \<box>[R]xy) & ([F]x \<rightarrow> \<box>[F]x)\<close>
            AOT_thus \<open>[F]x & [R]xy \<rightarrow> \<box>([F]x & [R]xy)\<close>
              by (metis "KBasic:3" "con-dis-i-e:1" "con-dis-i-e:2:b" "con-dis-taut:1" "deduction-theorem" "intro-elim:3:b" "modus-tollens:1" "raa-cor:1")
          }
        qed
        ultimately AOT_show \<open>\<box>([F]x & [R]xy \<rightarrow> \<box>([F]x & [R]xy))\<close>
          using "qml:1"[axiom_inst, THEN "\<rightarrow>E", THEN "\<rightarrow>E"] by blast
      qed
    qed
    AOT_hence \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n \<box>([\<lambda>xy [F]x & [R]xy]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[\<lambda>xy [F]x & [R]xy]x\<^sub>1...x\<^sub>n)\<close>
      using tuple_forall[THEN "\<equiv>\<^sub>d\<^sub>fI"] by fast
    AOT_hence \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n \<box>([R\<^sub>\<restriction>\<^sub>F]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[R\<^sub>\<restriction>\<^sub>F]x\<^sub>1...x\<^sub>n)\<close>
      by (auto intro!: "cqt:2" "rule-id-df:2:b"[where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", OF "dig-alt:1", simplified])
    AOT_thus \<open>\<box>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([R\<^sub>\<restriction>\<^sub>F]x\<^sub>1...x\<^sub>n \<rightarrow> \<box>[R\<^sub>\<restriction>\<^sub>F]x\<^sub>1...x\<^sub>n)\<close>
      using "BFs:1"[THEN "\<rightarrow>E"] by fast
  qed
qed

AOT_define smaller :: \<open>\<Pi>\<close> (\<open>'(<')\<close>)
  "813:1": \<open>(<) =\<^sub>d\<^sub>f [\<P>\<^sup>*]\<^sub>\<restriction>\<^sub>\<nat>\<close>

AOT_define smaller_equal :: \<open>\<Pi>\<close> (\<open>'(\<le>')\<close>)
  "813:2": \<open>(\<le>) =\<^sub>d\<^sub>f [\<P>\<^sup>+]\<^sub>\<restriction>\<^sub>\<nat>\<close>

syntax "_AOT_less" :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl \<open><\<close> 50)
translations
  "_AOT_less \<kappa> \<kappa>'" == "CONST AOT_exe (CONST smaller) (CONST Pair \<kappa> \<kappa>')"
print_translation\<open>
AOT_syntax_print_translations
[(\<^const_syntax>\<open>AOT_exe\<close>, fn ctxt => fn [
  Const ("\<^const>AOT_PLM.smaller", _),
  Const (\<^const_syntax>\<open>Pair\<close>, _) $ lhs $ rhs
] => Const (\<^syntax_const>\<open>_AOT_less\<close>, dummyT) $ lhs $ rhs)]\<close>
syntax "_AOT_less_equal" :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl \<open>\<le>\<close> 50)
translations
  "_AOT_less_equal \<kappa> \<kappa>'" == "CONST AOT_exe (CONST smaller_equal) (CONST Pair \<kappa> \<kappa>')"
print_translation\<open>
AOT_syntax_print_translations
[(\<^const_syntax>\<open>AOT_exe\<close>, fn ctxt => fn [
  Const ("\<^const>AOT_PLM.smaller_equal", _),
  Const (\<^const_syntax>\<open>Pair\<close>, _) $ lhs $ rhs
] => Const (\<^syntax_const>\<open>_AOT_less_equal\<close>, dummyT) $ lhs $ rhs)]\<close>


AOT_define GreaterThan :: \<open>\<tau>\<close> (\<open>'(>')\<close>)
  "lt-gt:3": \<open>(>) =\<^sub>d\<^sub>f [\<lambda>xy y < x]\<close>

syntax "_GreaterThan" :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl \<open>>\<close> 90)
translations
   "_GreaterThan \<kappa> \<kappa>'" == "CONST AOT_exe (CONST GreaterThan) (\<kappa>, \<kappa>')"

AOT_define GreaterThanOrEqual :: \<open>\<tau>\<close> (\<open>'(\<ge>')\<close>)
  "lt-gt:4": \<open>(\<ge>) =\<^sub>d\<^sub>f [\<lambda>xy y \<le> x]\<close>

syntax "_GreaterThanOrEqual" :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl \<open>\<ge>\<close> 90)
translations
   "_GreaterThanOrEqual \<kappa> \<kappa>'" == "CONST AOT_exe (CONST GreaterThanOrEqual) (\<kappa>, \<kappa>')"

AOT_theorem "lt-basic:1": \<open>x < y \<equiv> [\<nat>]x & [\<nat>]y & [\<P>\<^sup>*]xy\<close>
  apply (rule "rule=E"[rotated, OF "rule-id-df:1[zero]"[OF "813:1", symmetric]])
   apply (safe intro!: "dig-alt:2"[unvarify R F] "nnumber:2" "assume-anc:2" )
  apply (AOT_subst \<open>[\<P>\<^sup>*\<^sub>\<restriction>\<^sub>\<nat>]xy\<close> \<open>[\<nat>]x & [\<P>\<^sup>*]xy\<close>)
   apply (safe intro!: "dig-alt:3"[unvarify R F] "nnumber:2" "assume-anc:2")
  by (auto intro!: "\<equiv>I" "\<rightarrow>I" "&I" dest: "&E" intro: "suc-num:2"[unconstrain n, THEN "\<rightarrow>E", THEN "\<rightarrow>E"])

AOT_theorem "lt-basic:2": \<open>x \<le> y \<equiv> [\<nat>]x & [\<nat>]y & [\<P>\<^sup>+]xy\<close>
  apply (rule "rule=E"[rotated, OF "rule-id-df:1[zero]"[OF "813:2", symmetric]])
   apply (safe intro!: "dig-alt:2"[unvarify R F] "nnumber:2" "assume-anc:2" "assume1:4")
  apply (AOT_subst \<open>[\<P>\<^sup>+\<^sub>\<restriction>\<^sub>\<nat>]xy\<close> \<open>[\<nat>]x & [\<P>\<^sup>+]xy\<close>)
    apply (safe intro!: "dig-alt:3"[unvarify R F] "nnumber:2" "assume1:4" "assume-anc:2")
  by (auto intro!: "\<equiv>I" "\<rightarrow>I" "&I" dest: "&E" intro: "suc-num:3"[unconstrain n, THEN "\<rightarrow>E", THEN "\<rightarrow>E"])



AOT_theorem "lt-conv:1": \<open>n < m \<equiv> [\<P>]\<^sup>*nm\<close>
  by (meson "con-dis-i-e:1" "df-simplify:1" "lt-basic:1" Number.restricted_var_condition)

AOT_theorem "lt-conv:2": \<open>n \<le> m \<equiv> [\<P>]\<^sup>+nm\<close>
  by (meson "con-dis-i-e:1" "df-simplify:1" "lt-basic:2" Number.restricted_var_condition)

AOT_theorem "lt-conv:3": \<open>n > m \<equiv> m < n\<close>
proof -
  AOT_have 0: \<open>[\<lambda>xy y < x]\<down>\<close> by "cqt:2"
  show ?thesis
    apply (rule "rule-id-df:2:b[zero]"[OF "lt-gt:3", simplified])
     apply "cqt:2"
    by (safe intro!: "beta-C-meta"[THEN "\<rightarrow>E", OF 0, unvarify \<nu>\<^sub>1\<nu>\<^sub>n, where \<tau>=\<open>(_,_)\<close>, simplified] tuple_denotes[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2")
qed

AOT_theorem "lt-conv:4": \<open>n \<ge> m \<equiv> m \<le> n\<close>
proof -
  AOT_have 0: \<open>[\<lambda>xy y \<le> x]\<down>\<close> by "cqt:2"
  show ?thesis
    apply (rule "rule-id-df:2:b[zero]"[OF "lt-gt:4", simplified])
     apply "cqt:2"
    by (safe intro!: "beta-C-meta"[THEN "\<rightarrow>E", OF 0, unvarify \<nu>\<^sub>1\<nu>\<^sub>n, where \<tau>=\<open>(_,_)\<close>, simplified] tuple_denotes[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2")
qed

AOT_theorem "lt-trans:1": \<open>[\<P>]nm \<rightarrow> n < m\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>[\<P>]nm\<close>
  AOT_hence \<open>[\<P>\<^sup>*]nm\<close>
    using "anc-her:1"[unvarify R, OF "pred-thm:2", THEN "\<rightarrow>E"] by blast
  AOT_thus \<open>n < m\<close>
    using "lt-conv:1"[THEN "\<equiv>E"(2)] by simp
qed

AOT_theorem "lt-trans:3": \<open>n < m \<rightarrow> n \<le> m\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>n < m\<close>
  AOT_hence \<open>[\<P>]\<^sup>*nm\<close> by (metis "intro-elim:3:a" "lt-conv:1")
  AOT_hence \<open>[\<P>]\<^sup>+nm\<close> by (metis "assume1:5" "con-dis-i-e:3:a" "intro-elim:3:b")
  AOT_thus \<open>n \<le> m\<close> by (metis "intro-elim:3:b" "lt-conv:2")
qed

AOT_theorem "lt-trans:4": \<open>n \<le> m & n \<noteq> m \<rightarrow> n < m\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume noteq: \<open>n \<noteq> m\<close>
  AOT_assume \<open>n \<le> m\<close>
  AOT_hence \<open>[\<P>]\<^sup>+nm\<close> by (metis "intro-elim:3:a" "lt-conv:2")
  AOT_hence \<open>[\<P>]\<^sup>*nm \<or> n =\<^sub>\<P> m\<close> by (metis "assume1:5" "intro-elim:3:a")
  moreover {
    AOT_assume \<open>[\<P>]\<^sup>*nm\<close>
    AOT_hence \<open>n < m\<close> by (metis "intro-elim:3:b" "lt-conv:1")
  }
  moreover {
    AOT_assume \<open>n =\<^sub>\<P> m\<close>
    AOT_hence \<open>n = m\<close>
      using "id-R-thm:3"[unconstrain \<R>, unvarify \<beta>, OF "pred-thm:2", THEN "\<rightarrow>E", OF "pred-1-1:4", THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>n = m & \<not>n = m\<close> using noteq "=-infix" "\<equiv>\<^sub>d\<^sub>fE" "con-dis-i-e:1" by blast
    AOT_hence \<open>n < m\<close> by (metis "raa-cor:1")
  }
  ultimately AOT_show \<open>n < m\<close>  by (metis "con-dis-i-e:4:c" "raa-cor:1")
qed

AOT_theorem "lt-trans:5": \<open>n < m & m < k \<rightarrow> n < k\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume \<open>n < m\<close>
  AOT_hence 1: \<open>[\<P>]\<^sup>*nm\<close> by (metis "intro-elim:3:a" "lt-conv:1") 
  AOT_assume \<open>m < k\<close>
  AOT_hence 2: \<open>[\<P>]\<^sup>*mk\<close> by (metis "intro-elim:3:a" "lt-conv:1") 
  AOT_have \<open>[\<P>]\<^sup>*nk\<close> using 1 2 "anc-her:6"[unvarify R, OF "pred-thm:2"] by (meson "con-dis-i-e:1" "\<rightarrow>E")
  AOT_thus \<open>n < k\<close> by (metis "intro-elim:3:b" "lt-conv:1")
qed

AOT_theorem "lt-trans:6": \<open>n \<le> m & m \<le> k \<rightarrow> n \<le> k\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume \<open>n \<le> m\<close>
  AOT_hence 1: \<open>[\<P>]\<^sup>+nm\<close> by (metis "intro-elim:3:a" "lt-conv:2") 
  AOT_assume \<open>m \<le> k\<close>
  AOT_hence 2: \<open>[\<P>]\<^sup>+mk\<close> by (metis "intro-elim:3:a" "lt-conv:2") 
  AOT_have \<open>[\<P>]\<^sup>+nk\<close>
    using "w-ances-her:6"[unconstrain \<R>, unvarify \<beta>, OF "pred-thm:2", THEN "\<rightarrow>E", OF "pred-1-1:4", THEN "\<rightarrow>E", OF "&I"] 1 2 by blast
  AOT_thus \<open>n \<le> k\<close>
    by (metis "intro-elim:3:b" "lt-conv:2")
qed

AOT_theorem "lt-trans:7": \<open>n < m & m \<le> k \<rightarrow> n < k\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume 1: \<open>n < m\<close>
  AOT_assume 2: \<open>m \<le> k\<close>
  {
    AOT_assume \<open>m = k\<close>
    AOT_hence \<open>n < k\<close> using "1" "rule=E" by fast
  }
  moreover {
    AOT_assume \<open>m \<noteq> k\<close>
    AOT_hence \<open>m < k\<close> using 2 by (metis "con-dis-taut:5" "lt-trans:4" "vdash-properties:10")
    AOT_hence \<open>n < k\<close> by (metis "1" "con-dis-taut:5" "lt-trans:5" "modus-tollens:1" "raa-cor:3")
  }
  ultimately AOT_show \<open>n < k\<close> by (metis "=-infix" "\<equiv>\<^sub>d\<^sub>fI" "reductio-aa:2")
qed

AOT_theorem "lt-trans:8": \<open>n \<le> m & m < k \<rightarrow> n < k\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume 1: \<open>n \<le> m\<close>
  AOT_assume 2: \<open>m < k\<close>
  {
    AOT_assume \<open>n = m\<close>
    AOT_hence \<open>n < k\<close> using 2 id_sym "rule=E" by fast
  }
  moreover {
    AOT_assume \<open>n \<noteq> m\<close>
    AOT_hence \<open>n < m\<close> using 1 by (metis "con-dis-taut:5" "lt-trans:4" "vdash-properties:10")
    AOT_hence \<open>n < k\<close> by (metis "2" "con-dis-taut:5" "lt-trans:5" "modus-tollens:1" "raa-cor:3")
  }
  ultimately AOT_show \<open>n < k\<close> by (metis "=-infix" "\<equiv>\<^sub>d\<^sub>fI" "reductio-aa:2")
qed

AOT_theorem "no-num-pred:1": \<open>\<not>(n < n)\<close>
proof(rule "raa-cor:2")
  AOT_assume \<open>n < n\<close>
  AOT_hence \<open>[\<P>\<^sup>*]nn\<close> using "lt-conv:1"[THEN "\<equiv>E"(1)] by blast
  moreover AOT_have \<open>\<not>[\<P>]\<^sup>*nn\<close> 
    by (rule "1-1-R:3"[unconstrain \<R>, unvarify \<beta>, OF "pred-thm:2", THEN "\<rightarrow>E",
                       OF "pred-1-1:4", unvarify x, OF "zero:2", THEN "\<rightarrow>E", THEN "\<rightarrow>E",
                      OF "no-pred-0:3"])
       (meson "intro-elim:3:a" "nnumber:3" Number.restricted_var_condition)
  ultimately AOT_show \<open>[\<P>\<^sup>*]nn & \<not>[\<P>\<^sup>*]nn\<close> by (rule "&I")
qed

AOT_theorem "no-num-pred:2": \<open>\<not>[\<P>]nn\<close>
  using "lt-trans:1" "modus-tollens:1" "no-num-pred:1" by blast

AOT_theorem \<open>[\<lambda>x x \<le> y]\<down>\<close>
  by "cqt:2"

AOT_theorem nat_prop_den: \<open>[\<lambda>x [\<nat>]x & \<phi>{x}]\<down>\<close>
proof(safe intro!: "kirchner-thm:1"[THEN "\<equiv>E"(2)] GEN RN "\<rightarrow>I")
  AOT_modally_strict {
    fix x y
    AOT_assume indist: \<open>\<forall>F([F]x \<equiv> [F]y)\<close>
    AOT_assume 0: \<open>[\<nat>]x & \<phi>{x}\<close>
    AOT_hence \<open>NaturalCardinal(x)\<close>
      using "nat-card"[THEN "\<rightarrow>E"] "&E" by blast
    AOT_hence \<open>[D!]x\<close> using card_disc[THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>\<box>\<forall>y (y \<noteq> x \<rightarrow> \<exists>F \<not>([F]y \<equiv> [F]x))\<close>
      using Discernible_equiv[THEN "\<equiv>E"(1)] by blast
    AOT_hence 1: \<open>\<forall>y (y \<noteq> x \<rightarrow> \<exists>F \<not>([F]y \<equiv> [F]x))\<close>
      using "qml:2"[axiom_inst, THEN "\<rightarrow>E"] by blast
    AOT_have \<open>y = x\<close>
    proof(rule "raa-cor:1")
      AOT_assume \<open>\<not>y = x\<close>
      AOT_hence \<open>y \<noteq> x\<close>
        using "=-infix"[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
      AOT_hence \<open>\<exists>F \<not>([F]y \<equiv> [F]x)\<close>
        using 1[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
      then AOT_obtain F where \<open>\<not>([F]y \<equiv> [F]x)\<close> using "\<exists>E"[rotated] by blast
      moreover AOT_have \<open>[F]y \<equiv> [F]x\<close> using indist[THEN "\<forall>E"(2), symmetric] by auto
      ultimately AOT_show \<open>p & \<not>p\<close> for p using "reductio-aa:1" by blast
    qed
    AOT_hence \<open>[\<nat>]y & \<phi>{y}\<close>
      using 0 "rule=E" id_sym by fast
  } note 0 = this
  AOT_modally_strict {
    fix x y
    AOT_assume \<open>\<forall>F([F]x \<equiv> [F]y)\<close>
    moreover AOT_have \<open>\<forall>F([F]y \<equiv> [F]x)\<close>
      by (metis calculation "cqt-basic:11" "intro-elim:3:b")
    ultimately AOT_show \<open>[\<nat>]x & \<phi>{x} \<equiv> [\<nat>]y & \<phi>{y}\<close>
      using 0 "\<rightarrow>I" "\<equiv>I" by auto
  }
qed

AOT_theorem \<open>[\<lambda>z [\<nat>]z & Numbers(z,[\<lambda>x x < z])]\<down>\<close>
  using nat_prop_den by auto

AOT_theorem "827:1": \<open>[F]u & Numbers(x,[F]\<^sup>-\<^sup>u) & [\<P>]xy \<rightarrow> Numbers(y, F)\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_assume 0: \<open>[F]u & Numbers(x,[F]\<^sup>-\<^sup>u) & [\<P>]xy\<close>
  AOT_hence \<open>\<exists>G\<exists>u([G]u & Numbers(y,G) & Numbers(x,[G]\<^sup>-\<^sup>u))\<close>
    using "pred-thm:3"[THEN "\<equiv>E"(1)] "&E" by blast
  then AOT_obtain G where \<open>\<exists>u([G]u & Numbers(y,G) & Numbers(x,[G]\<^sup>-\<^sup>u))\<close>
    using "\<exists>E"[rotated] by blast
  then AOT_obtain v where v_prop: \<open>[G]v & Numbers(y,G) & Numbers(x,[G]\<^sup>-\<^sup>v)\<close>
    using "\<exists>E"[rotated] by blast
  AOT_have \<open>[F]\<^sup>-\<^sup>u \<approx>\<^sub>D [G]\<^sup>-\<^sup>v\<close>
    by (auto intro!: "num-tran:2"[unvarify G H, THEN "\<rightarrow>E"] "&I" "F-u[den]" 0[THEN "&E"(1), THEN "&E"(2)] v_prop[THEN "&E"(2)])
  AOT_hence \<open>F \<approx>\<^sub>D G\<close>
    by (auto intro!: "P'-eq"[THEN "\<rightarrow>E"] "&I" 0[THEN "&E"(1), THEN "&E"(1)] v_prop[THEN "&E"(1), THEN "&E"(1)])
  AOT_thus \<open>Numbers(y,F)\<close>
    using v_prop[THEN "&E"(1), THEN "&E"(2)]
          "num-tran:1"[THEN "\<rightarrow>E", THEN "\<equiv>E"(2)] by blast
qed

AOT_theorem num_n_lt_n: \<open>Numbers(n, [\<lambda>x x < n])\<close>
proof -
  AOT_have \<open>[\<lambda>z [\<nat>]z & Numbers(z,[\<lambda>x x < z])]n\<close>
  proof(safe intro!: GEN "\<rightarrow>I" "cqt:2" induction[THEN "\<forall>E"(1), THEN "\<rightarrow>E", THEN "Number.\<forall>E"]
                     nat_prop_den "&I" "\<beta>\<leftarrow>C" "zero:2" "0-n")
    AOT_show \<open>Numbers(0, [\<lambda>x x < 0])\<close>
    proof (safe intro!: "0F:1"[unvarify F, THEN "\<equiv>E"(1)] "cqt:2"; rule "raa-cor:2")
      AOT_assume \<open>\<exists>u [\<lambda>x x < 0]u\<close>
      then AOT_obtain u where \<open>[\<lambda>x x < 0]u\<close> using "\<exists>E"[rotated] by blast
      AOT_hence \<open>u < 0\<close> using "\<beta>\<rightarrow>C" by blast
      AOT_hence \<open>[\<P>\<^sup>*]u 0\<close>
        using "lt-basic:1"[unvarify y, OF "zero:2", THEN "\<equiv>E"(1)] "&E" by blast
      AOT_hence \<open>\<exists>x [\<P>\<^sup>*]x 0\<close> by (rule "\<exists>I")
      AOT_thus \<open>\<exists>x [\<P>\<^sup>*]x 0 & \<not>\<exists>x [\<P>\<^sup>*]x 0\<close>
        using "no-pred-0:2" "&I" by blast
    qed
  next
    fix x y
    AOT_assume Nx: \<open>[\<nat>]x\<close>
    AOT_assume Ny: \<open>[\<nat>]y\<close>
    AOT_assume Pxy: \<open>[\<P>]xy\<close>
    AOT_hence x_lt_y: \<open>x < y\<close>
      using "lt-trans:1"[unconstrain n, unconstrain m, THEN "\<rightarrow>E", OF Ny, THEN "\<rightarrow>E", OF Nx, THEN "\<rightarrow>E"] by blast
    AOT_have \<open>\<exists>F \<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
      using Pxy "pred-thm:3"[THEN "\<equiv>E"(1)] by blast
    then AOT_obtain F where \<open>\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
      using "\<exists>E"[rotated] by blast
    then AOT_obtain u where u_prop: \<open>[F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u)\<close>
      using "\<exists>E"[rotated] by blast
    AOT_find_theorems \<open>[\<P>]xy\<close>
    AOT_assume \<open>[\<lambda>z [\<nat>]z & Numbers(z,[\<lambda>x x < z])]x\<close>
    AOT_hence x: \<open>Numbers(x,[\<lambda>z z < x])\<close> using "\<beta>\<rightarrow>C" "&E" by blast
    AOT_hence 1: \<open>[\<lambda>z z < x] \<approx>\<^sub>D [F]\<^sup>-\<^sup>u\<close>
      by (auto intro!: "hume-strict:1"[unvarify F G, THEN "\<equiv>E"(1)] "F-u[den]"
                       "cqt:2" "\<exists>I"(2)[where \<beta>=x] "&I" u_prop[THEN "&E"(2)])
    AOT_have \<open>F \<approx>\<^sub>D [\<lambda>z z < y]\<close>
    proof (safe intro!: "P'-eq"[unvarify G, THEN "\<rightarrow>E"] "cqt:2" "&I" "\<beta>\<leftarrow>C" "lt-basic:1"[THEN "\<equiv>E"(2)] Ny)
      AOT_have \<open>[\<lambda>z z < y]\<^sup>-\<^sup>x \<approx>\<^sub>D [\<lambda>z z < x]\<close>
      proof(safe intro!: "apE-eqE:1"[unvarify F G, THEN "\<rightarrow>E"] "cqt:2" "F-u[den]"[unvarify F]
                         "eqD"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" GEN "\<equiv>I" "\<rightarrow>I" "\<beta>\<leftarrow>C" "F-u[equiv]"[unvarify F, THEN "\<equiv>E"(2)])
        fix u
        AOT_assume \<open>[[\<lambda>z z < y]\<^sup>-\<^sup>x]u\<close>
        AOT_hence 0: \<open>[\<lambda>z z < y]u & u \<noteq>\<^sub>D x\<close>
          by (auto intro: "F-u[equiv]"[unvarify F, THEN "\<equiv>E"(1)] intro!: "cqt:2")
        AOT_hence \<open>u < y\<close> using "&E" "\<beta>\<rightarrow>C" by blast
        AOT_hence Nu: \<open>[\<nat>]u\<close> and "P\<^sup>*uy": \<open>[\<P>\<^sup>*]uy\<close>
          using "lt-basic:1"[THEN "\<equiv>E"(1)] "&E" by blast+
        AOT_hence 1: \<open>[\<P>\<^sup>+]ux\<close>
          using "1-1-R:1"[unconstrain \<R>, unvarify \<beta>, OF "pred-thm:2", THEN "\<rightarrow>E",
                      OF "pred-1-1:4", THEN "\<rightarrow>E", OF "&I", OF Pxy] by blast
        AOT_hence \<open>[\<P>\<^sup>*]ux \<or> u =\<^sub>\<P> x\<close>
          using "assume1:5"[THEN "\<equiv>E"(1), OF 1] by blast
        moreover AOT_have \<open>\<not>u =\<^sub>\<P> x\<close>
        proof(rule "raa-cor:2")
          AOT_assume \<open>u =\<^sub>\<P> x\<close>
          AOT_hence \<open>u = x\<close>
            using "id-R-thm:3"[unconstrain \<R>, unvarify \<beta>, OF "pred-thm:2", THEN "\<rightarrow>E",
                      OF "pred-1-1:4", THEN "\<rightarrow>E"] by blast
          AOT_hence \<open>u =\<^sub>D x\<close>
            using "disc=Dequiv:1" "rule=E" by fast
          moreover AOT_have \<open>\<not>(u =\<^sub>D x)\<close> using 0[THEN "&E"(2)] "thm-neg=D"[THEN "\<equiv>E"(1)] by blast
          ultimately AOT_show \<open>u =\<^sub>D x & \<not>u =\<^sub>D x\<close> using "&I" by blast
        qed
        ultimately AOT_have \<open>[\<P>\<^sup>*]ux\<close>
          by (metis "con-dis-i-e:4:c")
        AOT_thus \<open>u < x\<close>
          by (safe intro!: "lt-basic:1"[THEN "\<equiv>E"(2)] "&I" Nu Nx)
      next
        fix u
        AOT_assume \<open>[\<lambda>z z < x]u\<close>
        AOT_hence u_lt_x: \<open>u < x\<close>
          using "\<beta>\<rightarrow>C" by blast
        AOT_hence Nu: \<open>[\<nat>]u\<close>
          using "lt-basic:1"[THEN "\<equiv>E"(1)] "&E" by blast
        AOT_show \<open>u < y\<close>
          using x_lt_y "lt-trans:5"[unconstrain n, THEN "\<rightarrow>E", OF Nu, unconstrain m,
                THEN "\<rightarrow>E", OF Nx, unconstrain k, THEN "\<rightarrow>E", OF Ny, THEN "\<rightarrow>E", OF "&I"]
                u_lt_x x_lt_y by blast
      next
        fix u
        AOT_assume \<open>[\<lambda>z z < x]u\<close>
        AOT_hence u_lt_x: \<open>u < x\<close>
          using "\<beta>\<rightarrow>C" by blast
        AOT_show \<open>u \<noteq>\<^sub>D x\<close>
        proof (safe intro!: "thm-neg=D"[THEN "\<equiv>E"(2)] "raa-cor:2")
          AOT_assume \<open>u =\<^sub>D x\<close>
          AOT_hence \<open>u = x\<close>
            by (metis "=D-simple:2" "disc=Dequiv:2" "nat-card" "vdash-properties:10" Nx card_disc id_sym)
          AOT_hence \<open>x < x\<close>
            using u_lt_x "rule=E" by fast
          AOT_thus \<open>x < x & \<not>x < x\<close>
            using "&I" "no-num-pred:1"[unconstrain n, THEN "\<rightarrow>E", OF Nx] by blast
        qed
      qed
      AOT_thus \<open>[F]\<^sup>-\<^sup>u \<approx>\<^sub>D [\<lambda>z z < y]\<^sup>-\<^sup>x\<close>
        using 1 "eq-part:2[terms]" "eq-part:3[terms]" "\<rightarrow>E" by blast
    next
      AOT_show \<open>[\<nat>]x\<close> using Nx.
    next
      AOT_show \<open>[\<P>\<^sup>*]xy\<close>
        using "anc-her:1"[unvarify R, OF "pred-thm:2", THEN "\<rightarrow>E", OF Pxy].
    next
      AOT_show \<open>[F]u\<close> using u_prop "&E" by blast
    qed
    AOT_thus \<open>Numbers(y,[\<lambda>x x < y])\<close>
      by (auto intro: "num-tran:1"[unvarify H, THEN "\<rightarrow>E", THEN "\<equiv>E"(1)]
               intro!: u_prop[THEN "&E"(1), THEN "&E"(2)] "cqt:2")
  qed
  AOT_hence \<open>[\<nat>]n & Numbers(n,[\<lambda>x x < n])\<close> using "\<beta>\<rightarrow>C" by blast
  thus ?thesis using "&E" by blast
qed


AOT_theorem "th-succ'": \<open>\<forall>n\<exists>m [\<P>]nm\<close>
proof(rule "Number.\<forall>I")
  fix n
  AOT_have 0: \<open>[\<lambda>x x < n \<or> x =\<^sub>D n]\<down>\<close> by "cqt:2"
  AOT_obtain x where \<open>Numbers(x,[\<lambda>x x < n \<or> x =\<^sub>D n])\<close>
    using "num:1"[unvarify G, OF 0] "\<exists>E"[rotated] by blast
  AOT_hence \<open>[\<P>]nx\<close>
  proof(safe intro!: "pred-thm:3"[THEN "\<equiv>E"(2)] "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>[\<lambda>x x < n \<or> x =\<^sub>D n]\<guillemotright>\<close>]
      "\<exists>I"(2)[where \<beta>=\<open>Number.Rep n\<close>] "&I" "\<beta>\<leftarrow>C" "cqt:2" "\<or>I"(2) "disc=Dequiv:1")
    AOT_have \<open>[\<lambda>x x < n \<or> x=\<^sub>D n]\<^sup>-\<^sup>n \<equiv>\<^sub>D [\<lambda>x x < n]\<close>
    proof (safe intro!: eqD[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" "F-u[den]"[unvarify F] GEN "\<equiv>I" "\<rightarrow>I" "\<beta>\<leftarrow>C"
                          "F-u[equiv]"[unvarify F, THEN "\<equiv>E"(2)]
                dest!: "\<beta>\<rightarrow>C" "F-u[equiv]"[unvarify F, OF 0, THEN "\<equiv>E"(1)])
      fix u
      AOT_assume \<open>[\<lambda>x x < n \<or> x =\<^sub>D n]u & u \<noteq>\<^sub>D n\<close>
      AOT_hence \<open>u < n \<or> u =\<^sub>D n\<close> and \<open>\<not>u =\<^sub>D n\<close>
        using "\<beta>\<rightarrow>C" "&E" "thm-neg=D"[THEN "\<equiv>E"(1)] by blast+
      AOT_thus \<open>u < n\<close>
        by (metis "con-dis-i-e:4:c")
    next
      fix u
      AOT_assume \<open>u < n\<close>
      AOT_thus \<open>u < n  \<or> u =\<^sub>D n\<close> by (rule "\<or>I")
    next
      fix u
      AOT_assume 0: \<open>u < n\<close>
      AOT_show \<open>u \<noteq>\<^sub>D n\<close>
      proof (safe intro!: "thm-neg=D"[THEN "\<equiv>E"(2)] "raa-cor:2")
        AOT_assume \<open>u =\<^sub>D n\<close>
        moreover AOT_have \<open>D!n\<close>
          by (meson "nat-card" "vdash-properties:10" Number.restricted_var_condition card_disc)
        ultimately AOT_have \<open>u = n\<close>
          by (metis "=D-simple:2" "disc=Dequiv:2" "vdash-properties:10" id_sym)
        AOT_hence \<open>n < n\<close> using 0 "rule=E" by fast
        AOT_thus \<open>n < n & \<not>n < n\<close>
          by (metis "con-dis-i-e:1" "no-num-pred:1")
      qed
    qed
    AOT_thus \<open>Numbers(n,[\<lambda>x x < n \<or> x =\<^sub>D n]\<^sup>-\<^sup>n)\<close>
      by (safe_step intro!: "num-tran:3"[unvarify G H, THEN "\<rightarrow>E", THEN "\<equiv>E"(2)])
         (auto intro!: "F-u[den]"[unvarify F] "cqt:2" num_n_lt_n)
  qed
  moreover AOT_have \<open>[\<nat>]x\<close>
    using "suc-num:1" "vdash-properties:10" calculation by blast
  ultimately AOT_show \<open>\<exists>m [\<P>]nm\<close> using "&I" "\<exists>I"(2) by fast
qed


AOT_theorem "th-succ": \<open>\<forall>n\<exists>!m [\<P>]nm\<close>
proof(safe intro!: "Number.\<forall>I" "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  fix n
  AOT_obtain m where Pnm: \<open>[\<P>]nm\<close>
    using "th-succ'"[THEN "Number.\<forall>E"] "Number.\<exists>E"[rotated] by fast
  AOT_hence \<open>[\<nat>]m & [\<P>]nm & \<forall>z ([\<nat>]z & [\<P>]nz \<rightarrow> z = m)\<close>
  proof(safe intro!: "&I" "Number.\<psi>" GEN "\<rightarrow>I")
    fix z
    AOT_assume \<open>[\<nat>]z & [\<P>]nz\<close>
    AOT_thus \<open>z = m\<close>
      using Pnm "&E" "pred-func:2"[unconstrain k, THEN "\<rightarrow>E", THEN "\<rightarrow>E"]
       by (metis "con-dis-taut:5" "vdash-properties:10" id_sym)
  qed
  AOT_thus \<open>\<exists>\<alpha>([\<nat>]\<alpha> & [\<P>]n\<alpha> & \<forall>z ([\<nat>]z & [\<P>]nz \<rightarrow> z = \<alpha>))\<close>
    by (rule "\<exists>I")
qed

(* TODO: note the use of a bold ' *)
AOT_define Successor :: \<open>\<tau> \<Rightarrow> \<kappa>\<^sub>s\<close> (\<open>_\<^bold>''\<close> [100] 100)
  "def-suc": \<open>n\<^bold>' =\<^sub>d\<^sub>f \<^bold>\<iota>m([\<P>]nm)\<close>

text\<open>Note: not explicitly in PLM\<close>
AOT_theorem "def-suc[den1]": \<open>\<^bold>\<iota>m([\<P>]nm)\<down>\<close>
  using "A-Exists:2" "RA[2]" "\<equiv>E"(2) "th-succ"[THEN "Number.\<forall>E"] by blast
text\<open>Note: not explicitly in PLM\<close>
AOT_theorem "def-suc[den2]": shows \<open>n\<^bold>'\<down>\<close>
  by (rule "def-suc"[THEN "=\<^sub>d\<^sub>fI"(1)])
     (auto simp: "def-suc[den1]")

(* TODO: not in PLM *)
AOT_theorem suc_eq_desc: \<open>n\<^bold>' = \<^bold>\<iota>m([\<P>]nm)\<close>
  by (rule "def-suc"[THEN "=\<^sub>d\<^sub>fI"(1)])
     (auto simp: "def-suc[den1]" "rule=I:1")

AOT_theorem "suc-fact": \<open>n = m \<rightarrow> n\<^bold>' = m\<^bold>'\<close>
proof (rule "\<rightarrow>I")
  AOT_assume 0: \<open>n = m\<close>
  AOT_show \<open>n\<^bold>' = m\<^bold>'\<close>
    apply (rule "rule=E"[rotated, OF 0])
    by (rule "=I"(1)[OF "def-suc[den2]"])
qed

AOT_theorem "ind-gnd": \<open>m = 0 \<or> \<exists>n(m = n\<^bold>')\<close>
proof -
  AOT_have \<open>[[\<P>]\<^sup>+]0m\<close>
    using Number.\<psi> "\<equiv>E"(1) "nnumber:3" by blast
  AOT_hence \<open>[[\<P>]\<^sup>*]0m \<or> 0 =\<^sub>\<P> m\<close>
    using "assume1:5"[unvarify x, OF "zero:2", THEN "\<equiv>E"(1)] by blast
  moreover {
    AOT_assume \<open>[[\<P>]\<^sup>*]0m\<close>
    AOT_hence \<open>\<exists>z ([[\<P>]\<^sup>+]0z & [\<P>]zm)\<close>
      using "w-ances-her:7"[unconstrain \<R>, unvarify \<beta> x, OF "zero:2",
                            OF "pred-thm:2", THEN "\<rightarrow>E", OF "pred-1-1:4",
                            THEN "\<rightarrow>E"]
      by blast
    then AOT_obtain z where \<theta>: \<open>[[\<P>]\<^sup>+]0z\<close> and \<xi>: \<open>[\<P>]zm\<close>
      using "&E" "\<exists>E"[rotated] by blast
    AOT_have Nz: \<open>[\<nat>]z\<close>
      using \<theta> "\<equiv>E"(2) "nnumber:3" by blast
    moreover AOT_have \<open>m = z\<^bold>'\<close>
    proof (rule "def-suc"[THEN "=\<^sub>d\<^sub>fI"(1)];
           safe intro!: "def-suc[den1]"[unconstrain n, THEN "\<rightarrow>E", OF Nz]
                        "nec-hintikka-scheme"[THEN "\<equiv>E"(2)] "&I"
                        GEN "\<rightarrow>I" "Act-Basic:2"[THEN "\<equiv>E"(2)])
      AOT_show \<open>\<^bold>\<A>[\<nat>]m\<close> using Number.\<psi>
        by (meson "mod-col-num:1" "nec-imp-act" "\<rightarrow>E")
    next
      AOT_show \<open>\<^bold>\<A>[\<P>]zm\<close> using \<xi>
        by (meson "nec-imp-act" "pred-1-1:1" "\<rightarrow>E")
    next
      fix y
      AOT_assume \<open>\<^bold>\<A>([\<nat>]y & [\<P>]zy)\<close>
      AOT_hence \<open>\<^bold>\<A>[\<nat>]y\<close> and \<open>\<^bold>\<A>[\<P>]zy\<close>
        using "Act-Basic:2" "&E" "\<equiv>E"(1) by blast+
      AOT_hence 0: \<open>[\<P>]zy\<close>
        by (metis RN "\<equiv>E"(1) "pred-1-1:1" "sc-eq-fur:2" "\<rightarrow>E")
      AOT_thus \<open>y = m\<close>
        using "pred-func:1"[THEN "\<rightarrow>E", OF "&I"] \<xi> by metis
    qed
    ultimately AOT_have \<open>[\<nat>]z & m = z\<^bold>'\<close>
      by (rule "&I")
    AOT_hence \<open>\<exists>n m = n\<^bold>'\<close>
      by (rule "\<exists>I")
    hence ?thesis
      by (rule "\<or>I")
  }
  moreover {
    AOT_assume \<open>0 =\<^sub>\<P> m\<close>
    AOT_hence \<open>0 = m\<close>
      using "id-R-thm:3"[unconstrain \<R>, unvarify \<beta> x, OF "zero:2", OF "pred-thm:2",
                         THEN "\<rightarrow>E", OF "pred-1-1:4", THEN "\<rightarrow>E"]
      by auto
    hence ?thesis using id_sym "\<or>I" by blast
  }
  ultimately show ?thesis
    by (metis "\<or>E"(2) "raa-cor:1")
qed

AOT_theorem "suc-thm": \<open>[\<P>]n n\<^bold>'\<close>
proof -
  AOT_obtain x where m_is_n: \<open>x = n\<^bold>'\<close>
    using "free-thms:1"[THEN "\<equiv>E"(1), OF "def-suc[den2]"]
    using "\<exists>E" by metis
  AOT_have \<open>\<^bold>\<A>([\<nat>]n\<^bold>' & [\<P>]n n\<^bold>')\<close>
    apply (rule "rule=E"[rotated, OF suc_eq_desc[symmetric]])
    apply (rule "actual-desc:4"[THEN "\<rightarrow>E"])
    by (simp add:  "def-suc[den1]")
  AOT_hence \<open>\<^bold>\<A>[\<nat>]n\<^bold>'\<close> and \<open>\<^bold>\<A>[\<P>]n n\<^bold>'\<close>
    using "Act-Basic:2" "\<equiv>E"(1) "&E" by blast+
  AOT_hence \<open>\<^bold>\<A>[\<P>]nx\<close>
    using m_is_n[symmetric] "rule=E" by fast+
  AOT_hence \<open>[\<P>]nx\<close>
    by (metis RN "\<equiv>E"(1) "pred-1-1:1" "sc-eq-fur:2" "\<rightarrow>E")
  thus ?thesis
    using m_is_n "rule=E" by fast
qed

AOT_define Numeral1 :: \<open>\<kappa>\<^sub>s\<close> ("1")
  "numerals:1": \<open>1 =\<^sub>d\<^sub>f 0\<^bold>'\<close>

AOT_theorem "F-u[exe]": \<open>[[F]\<^sup>-\<^sup>u]v \<equiv> ([F]v & v \<noteq>\<^sub>D u)\<close>
proof -
  AOT_have 0: \<open>[\<lambda>z [F]z & z \<noteq>\<^sub>D u]\<down>\<close> by "cqt:2"
  AOT_have \<open>[\<lambda>z [F]z & z \<noteq>\<^sub>D u]v \<equiv> ([F]v & v \<noteq>\<^sub>D u)\<close>
    by (safe intro!: "beta-C-meta"[THEN "\<rightarrow>E"] "cqt:2")
  thus ?thesis
    using "rule-id-df:1"[OF "F-u", where \<tau>\<^sub>1\<tau>\<^sub>n=\<open>(_,_)\<close>, simplified, OF 0]
      "rule=E" id_sym by fast
qed


AOT_theorem "prec-facts:1": \<open>[\<P>]0 1\<close>
  by (auto intro: "numerals:1"[THEN "rule-id-df:2:b[zero]",
                               OF "def-suc[den2]"[unconstrain n, unvarify \<beta>,
                                                  OF "zero:2", THEN "\<rightarrow>E", OF "0-n"]]
                  "suc-thm"[unconstrain n, unvarify \<beta>, OF "zero:2",
                            THEN "\<rightarrow>E", OF "0-n"])


AOT_theorem \<open>[\<lambda>x Numbers(x,F)]\<down>\<close>
proof(safe intro!: "kirchner-thm:1"[THEN "\<equiv>E"(2)] RN "\<rightarrow>I" GEN)
  AOT_modally_strict {
    fix x y
    AOT_assume indist: \<open>\<forall>F([F]x \<equiv> [F]y)\<close>
    AOT_assume numxF: \<open>Numbers(x,F)\<close> 
    AOT_hence 0: \<open>NaturalCardinal(x)\<close>
      by (metis "eq-num:6" "vdash-properties:10")
    {
      AOT_assume \<open>\<not>(x = 0)\<close>
      AOT_hence \<open>x \<noteq> 0\<close>
        by (metis "=-infix" "\<equiv>\<^sub>d\<^sub>fI")
      AOT_hence \<open>\<exists>y [\<P>]yx\<close>
        using CardinalSuc 0 by blast
      then AOT_obtain z where Pxz: \<open>[\<P>]zx\<close>
        using "\<exists>E"[rotated] by blast
      AOT_hence \<open>[\<lambda>y [\<P>]zy]x\<close>
        by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2")
      AOT_hence \<open>[\<lambda>y [\<P>]zy]y\<close>
        by (safe intro!: indist[THEN "\<forall>E"(1), THEN "\<equiv>E"(1)] "cqt:2")
      AOT_hence Pyz: \<open>[\<P>]zy\<close>
        by (metis "\<beta>\<rightarrow>C"(1))
      AOT_have \<open>x = y\<close>
        using "pred-func:1"[THEN "\<rightarrow>E", OF "&I", OF Pxz, OF Pyz].
      AOT_hence \<open>Numbers(y,F)\<close>
        using numxF "rule=E" by fast
    }
    moreover {
      AOT_assume x_is_zero: \<open>x = 0\<close>
      AOT_hence Px1: \<open>[\<P>]x 1\<close>
        using "prec-facts:1" "rule=E" id_sym by fast
      AOT_hence \<open>[\<lambda>y [\<P>]y 1]x\<close>
        by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2")
      AOT_hence \<open>[\<lambda>y [\<P>]y 1]y\<close>
        by (safe intro!: indist[THEN "\<forall>E"(1), THEN "\<equiv>E"(1)] "cqt:2")
      AOT_hence Py1: \<open>[\<P>]y 1\<close>
        by (metis "betaC:1:a")
      AOT_find_theorems \<open>[\<nat>]0\<close>
      AOT_hence one_den: \<open>1\<down>\<close>
        by (metis "russell-axiom[exe,2,1,2].\<psi>_denotes_asm")
      AOT_hence \<open>x = y\<close>
        using "pred-1-1:3"[THEN "df-1-1:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2), THEN "\<forall>E"(2),
                           THEN "\<forall>E"(2), THEN "\<forall>E"(1), OF one_den, THEN "\<rightarrow>E"]
              Px1 Py1 "&I" by blast
      AOT_hence \<open>Numbers(y,F)\<close>
        using numxF "rule=E" by fast
    }
    ultimately AOT_have \<open>Numbers(y,F)\<close>
      using "\<or>E"(1) "\<rightarrow>I" "reductio-aa:1" by blast
  } note 0 = this
  AOT_modally_strict {
    fix x y
    AOT_assume \<open>\<forall>F([F]x \<equiv> [F]y)\<close>
    moreover AOT_have \<open>\<forall>F([F]y \<equiv> [F]x)\<close>
      using "cqt-basic:11"[THEN "\<equiv>E"(1)] calculation by fast
    ultimately AOT_show \<open>Numbers(x,F) \<equiv> Numbers(y,F)\<close>
      using 0 "\<equiv>I" "\<rightarrow>I" by blast
  }
qed

(* TODO: more theorems *)

(* Note: we forgo restricted variables for natural cardinals. *)
AOT_define Finite :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>Finite'(_')\<close>)
  "inf-card:1": \<open>Finite(x) \<equiv>\<^sub>d\<^sub>f NaturalCardinal(x) & [\<nat>]x\<close>
AOT_define Infinite :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>Infinite'(_')\<close>)
  "inf-card:2": \<open>Infinite(x) \<equiv>\<^sub>d\<^sub>f NaturalCardinal(x) & \<not>Finite(x)\<close>

AOT_theorem "inf-card-exist:1": \<open>NaturalCardinal(#O!)\<close>
  by (safe intro!: card[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>O!\<guillemotright>\<close>] "=I"
                   "num-def:2"[unvarify G] "oa-exist:1")

lemma \<open>True\<close>
  nitpick[user_axioms, satisfy, expect = genuine]
  ..

(*<*)
end
(*>*)
