(*<*)
theory AOT_NaturalNumbers
  imports AOT_PossibleWorlds AOT_ExtendedRelationComprehension
  abbrevs one-to-one = \<open>\<^sub>1\<^sub>-\<^sub>1\<close>
      and onto = \<open>\<^sub>o\<^sub>n\<^sub>t\<^sub>o\<close>
begin
(*>*)

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

text\<open>We have already introduced the restricted type of Ordinary objects in the
     Extended Relation Comprehension theory. However, make sure all variable names
     are defined as expected (avoiding conflicts with situations
     of possible world theory).\<close>
AOT_register_variable_names
  Ordinary: u v r t s

AOT_theorem "equi:1": \<open>\<exists>!u \<phi>{u} \<equiv> \<exists>u (\<phi>{u} & \<forall>v (\<phi>{v} \<rightarrow> v =\<^sub>E u))\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>\<exists>!u \<phi>{u}\<close>
  AOT_hence \<open>\<exists>!x (O!x & \<phi>{x})\<close>.
  AOT_hence \<open>\<exists>x (O!x & \<phi>{x} & \<forall>\<beta> (O!\<beta> & \<phi>{\<beta>} \<rightarrow> \<beta> = x))\<close>
    using "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain x where x_prop: \<open>O!x & \<phi>{x} & \<forall>\<beta> (O!\<beta> & \<phi>{\<beta>} \<rightarrow> \<beta> = x)\<close>
    using "\<exists>E"[rotated] by blast
  {
    fix \<beta>
    AOT_assume beta_ord: \<open>O!\<beta>\<close>
    moreover AOT_assume \<open>\<phi>{\<beta>}\<close>
    ultimately AOT_have \<open>\<beta> = x\<close>
      using x_prop[THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=\<beta>]] "&I" "\<rightarrow>E" by blast
    AOT_hence \<open>\<beta> =\<^sub>E x\<close>
      using "ord-=E=:1"[THEN "\<rightarrow>E", OF "\<or>I"(1)[OF beta_ord],
                        THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"],
                        THEN "\<equiv>E"(1)]
      by blast
  }
  AOT_hence \<open>(O!\<beta> \<rightarrow> (\<phi>{\<beta>} \<rightarrow> \<beta> =\<^sub>E x))\<close> for \<beta>
    using "\<rightarrow>I" by blast
  AOT_hence \<open>\<forall>\<beta>(O!\<beta> \<rightarrow> (\<phi>{\<beta>} \<rightarrow> \<beta> =\<^sub>E x))\<close>
    by (rule GEN)
  AOT_hence \<open>O!x & \<phi>{x} & \<forall>y (O!y \<rightarrow> (\<phi>{y} \<rightarrow> y =\<^sub>E x))\<close>
    using x_prop[THEN "&E"(1)] "&I" by blast
  AOT_hence \<open>O!x & (\<phi>{x} & \<forall>y (O!y \<rightarrow> (\<phi>{y} \<rightarrow> y =\<^sub>E x)))\<close>
    using "&E" "&I" by meson
  AOT_thus \<open>\<exists>u (\<phi>{u} & \<forall>v (\<phi>{v} \<rightarrow> v =\<^sub>E u))\<close>
    using "\<exists>I" by fast
next
  AOT_assume \<open>\<exists>u (\<phi>{u} & \<forall>v (\<phi>{v} \<rightarrow> v =\<^sub>E u))\<close>
  AOT_hence \<open>\<exists>x (O!x & (\<phi>{x} & \<forall>y (O!y \<rightarrow> (\<phi>{y} \<rightarrow> y =\<^sub>E x))))\<close>
    by blast
  then AOT_obtain x where x_prop: \<open>O!x & (\<phi>{x} & \<forall>y (O!y \<rightarrow> (\<phi>{y} \<rightarrow> y =\<^sub>E x)))\<close>
    using "\<exists>E"[rotated] by blast
  AOT_have \<open>\<forall>y ([O!]y & \<phi>{y} \<rightarrow> y = x)\<close>
  proof(rule GEN; rule "\<rightarrow>I")
    fix y
    AOT_assume \<open>O!y & \<phi>{y}\<close>
    AOT_hence \<open>y =\<^sub>E x\<close>
      using x_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=y]]
            "\<rightarrow>E" "&E" by blast
    AOT_thus \<open>y = x\<close>
      using "ord-=E=:1"[THEN "\<rightarrow>E", OF "\<or>I"(2)[OF x_prop[THEN "&E"(1)]],
                        THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"], THEN "\<equiv>E"(2)] by blast
  qed
  AOT_hence \<open>[O!]x & \<phi>{x} & \<forall>y ([O!]y & \<phi>{y} \<rightarrow> y = x)\<close>
    using x_prop "&E" "&I" by meson
  AOT_hence \<open>\<exists>x ([O!]x & \<phi>{x} & \<forall>y ([O!]y & \<phi>{y} \<rightarrow> y = x))\<close>
    by (rule "\<exists>I")
  AOT_hence \<open>\<exists>!x (O!x & \<phi>{x})\<close>
    by (rule "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  AOT_thus \<open>\<exists>!u \<phi>{u}\<close>.
qed

AOT_define CorrelatesEOneToOne :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>_ |: _ \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E _\<close>)
  "equi:2": \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G \<equiv>\<^sub>d\<^sub>f R\<down> & F\<down> & G\<down> &
                               \<forall>u ([F]u \<rightarrow> \<exists>!v([G]v & [R]uv)) &
                               \<forall>v ([G]v \<rightarrow> \<exists>!u([F]u & [R]uv))\<close>

AOT_define EquinumerousE :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl "\<approx>\<^sub>E" 50)
  "equi:3": \<open>F \<approx>\<^sub>E G \<equiv>\<^sub>d\<^sub>f \<exists>R (R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G)\<close>

text\<open>Note: not explicitly in PLM.\<close>
AOT_theorem eq_den_1: \<open>\<Pi>\<down>\<close> if \<open>\<Pi> \<approx>\<^sub>E \<Pi>'\<close>
proof -
  AOT_have \<open>\<exists>R (R |: \<Pi> \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E \<Pi>')\<close>
    using "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fE"] that by blast
  then AOT_obtain R where \<open>R |: \<Pi> \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E \<Pi>'\<close>
    using "\<exists>E"[rotated] by blast
  AOT_thus \<open>\<Pi>\<down>\<close>
    using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
qed

text\<open>Note: not explicitly in PLM.\<close>
AOT_theorem eq_den_2: \<open>\<Pi>'\<down>\<close> if \<open>\<Pi> \<approx>\<^sub>E \<Pi>'\<close>
proof -
  AOT_have \<open>\<exists>R (R |: \<Pi> \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E \<Pi>')\<close>
    using "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fE"] that by blast
  then AOT_obtain R where \<open>R |: \<Pi> \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E \<Pi>'\<close>
    using "\<exists>E"[rotated] by blast
  AOT_thus \<open>\<Pi>'\<down>\<close>
    using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
qed

AOT_theorem "eq-part:1": \<open>F \<approx>\<^sub>E F\<close>
proof (safe intro!: "&I" GEN "\<rightarrow>I" "cqt:2[const_var]"[axiom_inst]
                    "\<equiv>\<^sub>d\<^sub>fI"[OF "equi:3"] "\<equiv>\<^sub>d\<^sub>fI"[OF "equi:2"] "\<exists>I"(1))
  fix x
  AOT_assume 1: \<open>O!x\<close>
  AOT_assume 2: \<open>[F]x\<close>
  AOT_show \<open>\<exists>!v ([F]v & x =\<^sub>E v)\<close>
  proof(rule "equi:1"[THEN "\<equiv>E"(2)];
        rule "\<exists>I"(2)[where \<beta>=x];
        safe dest!: "&E"(2)
             intro!:  "&I" "\<rightarrow>I" 1 2 Ordinary.GEN "ord=Eequiv:1"[THEN "\<rightarrow>E", OF 1])
    AOT_show \<open>v =\<^sub>E x\<close> if \<open>x =\<^sub>E v\<close> for v
      by (metis that "ord=Eequiv:2"[THEN "\<rightarrow>E"])
  qed
next
  fix y
  AOT_assume 1: \<open>O!y\<close>
  AOT_assume 2: \<open>[F]y\<close>
  AOT_show \<open>\<exists>!u ([F]u & u =\<^sub>E y)\<close>
    by(safe dest!: "&E"(2)
            intro!: "equi:1"[THEN "\<equiv>E"(2)] "\<exists>I"(2)[where \<beta>=y]
                    "&I" "\<rightarrow>I" 1 2 GEN "ord=Eequiv:1"[THEN "\<rightarrow>E", OF 1])
qed(auto simp: "=E[denotes]")


AOT_theorem "eq-part:2": \<open>F \<approx>\<^sub>E G \<rightarrow> G \<approx>\<^sub>E F\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>F \<approx>\<^sub>E G\<close>
  AOT_hence \<open>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
    using "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain R where \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence 0: \<open>R\<down> & F\<down> & G\<down> & \<forall>u ([F]u \<rightarrow> \<exists>!v([G]v & [R]uv)) &
                            \<forall>v ([G]v \<rightarrow> \<exists>!u([F]u & [R]uv))\<close>
    using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast

  AOT_have \<open>[\<lambda>xy [R]yx]\<down> & G\<down> & F\<down> & \<forall>u ([G]u \<rightarrow> \<exists>!v([F]v & [\<lambda>xy [R]yx]uv)) &
                            \<forall>v ([F]v \<rightarrow> \<exists>!u([G]u & [\<lambda>xy [R]yx]uv))\<close>
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
  AOT_hence \<open>[\<lambda>xy [R]yx] |: G \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E F\<close>
    using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
  AOT_hence \<open>\<exists>R R |: G \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E F\<close>
    by (rule "\<exists>I"(1)) "cqt:2[lambda]"
  AOT_thus \<open>G \<approx>\<^sub>E F\<close>
    using "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
qed

text\<open>Note: not explicitly in PLM.\<close>
AOT_theorem "eq-part:2[terms]": \<open>\<Pi> \<approx>\<^sub>E \<Pi>' \<rightarrow> \<Pi>' \<approx>\<^sub>E \<Pi>\<close>
  using "eq-part:2"[unvarify F G] eq_den_1 eq_den_2 "\<rightarrow>I" by meson
declare "eq-part:2[terms]"[THEN "\<rightarrow>E", sym]

AOT_theorem "eq-part:3": \<open>(F \<approx>\<^sub>E G & G \<approx>\<^sub>E H) \<rightarrow> F \<approx>\<^sub>E H\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>F \<approx>\<^sub>E G & G \<approx>\<^sub>E H\<close>
  then AOT_obtain R\<^sub>1 and R\<^sub>2 where
       \<open>R\<^sub>1 |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
   and \<open>R\<^sub>2 |: G \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E H\<close>
    using "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" "\<exists>E"[rotated] by metis
  AOT_hence \<theta>: \<open>\<forall>u ([F]u \<rightarrow> \<exists>!v([G]v & [R\<^sub>1]uv)) & \<forall>v ([G]v \<rightarrow> \<exists>!u([F]u & [R\<^sub>1]uv))\<close>
        and \<xi>: \<open>\<forall>u ([G]u \<rightarrow> \<exists>!v([H]v & [R\<^sub>2]uv)) & \<forall>v ([H]v \<rightarrow> \<exists>!u([G]u & [R\<^sub>2]uv))\<close>
    using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2)]
          "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(1), THEN "&E"(2)]
          "&I" by blast+
  AOT_have \<open>\<exists>R R = [\<lambda>xy O!x & O!y & \<exists>v ([G]v & [R\<^sub>1]xv & [R\<^sub>2]vy)]\<close>
    by (rule "free-thms:3[lambda]") cqt_2_lambda_inst_prover
  then AOT_obtain R where R_def: \<open>R = [\<lambda>xy O!x & O!y & \<exists>v ([G]v & [R\<^sub>1]xv & [R\<^sub>2]vy)]\<close>
    using "\<exists>E"[rotated] by blast
  AOT_have 1: \<open>\<exists>!v (([H]v & [R]uv))\<close> if a: \<open>[O!]u\<close> and b: \<open>[F]u\<close> for u
  proof (rule "\<equiv>E"(2)[OF "equi:1"])
    AOT_obtain b where
      b_prop: \<open>[O!]b & ([G]b & [R\<^sub>1]ub & \<forall>v ([G]v & [R\<^sub>1]uv \<rightarrow> v =\<^sub>E b))\<close>
      using \<theta>[THEN "&E"(1), THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<rightarrow>E",
              OF a b, THEN "\<equiv>E"(1)[OF "equi:1"]]
            "\<exists>E"[rotated] by blast
    AOT_obtain c where
      c_prop: "[O!]c & ([H]c & [R\<^sub>2]bc & \<forall>v ([H]v & [R\<^sub>2]bv \<rightarrow> v =\<^sub>E c))"
      using \<xi>[THEN "&E"(1), THEN "\<forall>E"(2)[where \<beta>=b], THEN "\<rightarrow>E",
              OF b_prop[THEN "&E"(1)], THEN "\<rightarrow>E",
              OF b_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(1)],
              THEN "\<equiv>E"(1)[OF "equi:1"]]
    "\<exists>E"[rotated] by blast
    AOT_show \<open>\<exists>v ([H]v & [R]uv & \<forall>v' ([H]v' & [R]uv' \<rightarrow> v' =\<^sub>E v))\<close>
    proof (safe intro!: "&I" GEN "\<rightarrow>I" "\<exists>I"(2)[where \<beta>=c])
      AOT_show \<open>O!c\<close> using c_prop "&E" by blast
    next
      AOT_show \<open>[H]c\<close> using c_prop "&E" by blast
    next
      AOT_have 0: \<open>[O!]u & [O!]c & \<exists>v ([G]v & [R\<^sub>1]uv & [R\<^sub>2]vc)\<close>
        by (safe intro!: "&I" a c_prop[THEN "&E"(1)] "\<exists>I"(2)[where \<beta>=b]
                         b_prop[THEN "&E"(1)] b_prop[THEN "&E"(2), THEN "&E"(1)]
                         c_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(2)])
      AOT_show \<open>[R]uc\<close>
        by (auto intro: "rule=E"[rotated, OF R_def[symmetric]]
                 intro!: "\<beta>\<leftarrow>C"(1) "cqt:2"
                 simp: "&I" "ex:1:a" prod_denotesI "rule-ui:3" 0)
    next
      fix x
      AOT_assume ordx: \<open>O!x\<close>
      AOT_assume \<open>[H]x & [R]ux\<close>
      AOT_hence hx: \<open>[H]x\<close> and \<open>[R]ux\<close> using "&E" by blast+
      AOT_hence \<open>[\<lambda>xy O!x & O!y & \<exists>v ([G]v & [R\<^sub>1]xv & [R\<^sub>2]vy)]ux\<close>
        using "rule=E"[rotated, OF R_def] by fast
      AOT_hence \<open>O!u & O!x & \<exists>v ([G]v & [R\<^sub>1]uv & [R\<^sub>2]vx)\<close>
        by (rule "\<beta>\<rightarrow>C"(1)[where \<phi>="\<lambda>(\<kappa>,\<kappa>'). _ \<kappa> \<kappa>'" and \<kappa>\<^sub>1\<kappa>\<^sub>n="(_,_)", simplified])
      then AOT_obtain z where z_prop: \<open>O!z & ([G]z & [R\<^sub>1]uz & [R\<^sub>2]zx)\<close>
        using "&E" "\<exists>E"[rotated] by blast
      AOT_hence \<open>z =\<^sub>E b\<close>
        using b_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=z]]
        using "&E" "\<rightarrow>E" by metis
      AOT_hence \<open>z = b\<close>
        by (metis "=E-simple:2"[THEN "\<rightarrow>E"])
      AOT_hence \<open>[R\<^sub>2]bx\<close>
        using z_prop[THEN "&E"(2), THEN "&E"(2)] "rule=E" by fast
      AOT_thus \<open>x =\<^sub>E c\<close>
        using c_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=x],
                     THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF ordx]
              hx "&I" by blast
    qed
  qed
  AOT_have 2: \<open>\<exists>!u (([F]u & [R]uv))\<close> if a: \<open>[O!]v\<close> and b: \<open>[H]v\<close> for v
  proof (rule "\<equiv>E"(2)[OF "equi:1"])
    AOT_obtain b where
      b_prop: \<open>[O!]b & ([G]b & [R\<^sub>2]bv & \<forall>u ([G]u & [R\<^sub>2]uv \<rightarrow> u =\<^sub>E b))\<close>
      using \<xi>[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<rightarrow>E",
              OF a b, THEN "\<equiv>E"(1)[OF "equi:1"]]
            "\<exists>E"[rotated] by blast
    AOT_obtain c where
      c_prop: "[O!]c & ([F]c & [R\<^sub>1]cb & \<forall>v ([F]v & [R\<^sub>1]vb \<rightarrow> v =\<^sub>E c))"
      using \<theta>[THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=b], THEN "\<rightarrow>E",
              OF b_prop[THEN "&E"(1)], THEN "\<rightarrow>E",
              OF b_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(1)],
              THEN "\<equiv>E"(1)[OF "equi:1"]]
    "\<exists>E"[rotated] by blast
    AOT_show \<open>\<exists>u ([F]u & [R]uv & \<forall>v' ([F]v' & [R]v'v \<rightarrow> v' =\<^sub>E u))\<close>
    proof (safe intro!: "&I" GEN "\<rightarrow>I" "\<exists>I"(2)[where \<beta>=c])
      AOT_show \<open>O!c\<close> using c_prop "&E" by blast
    next
      AOT_show \<open>[F]c\<close> using c_prop "&E" by blast
    next
      AOT_have \<open>[O!]c & [O!]v & \<exists>u ([G]u & [R\<^sub>1]cu & [R\<^sub>2]uv)\<close>
        by (safe intro!: "&I" a "\<exists>I"(2)[where \<beta>=b] 
                     c_prop[THEN "&E"(1)] b_prop[THEN "&E"(1)]
                     b_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(1)]
                     b_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(2)]
                     c_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(2)])
      AOT_thus \<open>[R]cv\<close>
        by (auto intro: "rule=E"[rotated, OF R_def[symmetric]]
                 intro!: "\<beta>\<leftarrow>C"(1) "cqt:2"
                 simp: "&I" "ex:1:a" prod_denotesI "rule-ui:3")
    next
      fix x
      AOT_assume ordx: \<open>O!x\<close>
      AOT_assume \<open>[F]x & [R]xv\<close>
      AOT_hence hx: \<open>[F]x\<close> and \<open>[R]xv\<close> using "&E" by blast+
      AOT_hence \<open>[\<lambda>xy O!x & O!y & \<exists>v ([G]v & [R\<^sub>1]xv & [R\<^sub>2]vy)]xv\<close>
        using "rule=E"[rotated, OF R_def] by fast
      AOT_hence \<open>O!x & O!v & \<exists>u ([G]u & [R\<^sub>1]xu & [R\<^sub>2]uv)\<close>
        by (rule "\<beta>\<rightarrow>C"(1)[where \<phi>="\<lambda>(\<kappa>,\<kappa>'). _ \<kappa> \<kappa>'" and \<kappa>\<^sub>1\<kappa>\<^sub>n="(_,_)", simplified])
      then AOT_obtain z where z_prop: \<open>O!z & ([G]z & [R\<^sub>1]xz & [R\<^sub>2]zv)\<close>
        using "&E" "\<exists>E"[rotated] by blast
      AOT_hence \<open>z =\<^sub>E b\<close>
        using b_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=z]]
        using "&E" "\<rightarrow>E" "&I" by metis
      AOT_hence \<open>z = b\<close>
        by (metis "=E-simple:2"[THEN "\<rightarrow>E"])
      AOT_hence \<open>[R\<^sub>1]xb\<close>
        using z_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(2)] "rule=E" by fast
      AOT_thus \<open>x =\<^sub>E c\<close>
        using c_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=x],
                     THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF ordx]
              hx "&I" by blast
    qed
  qed
  AOT_show \<open>F \<approx>\<^sub>E H\<close>
    apply (rule "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
    apply (rule "\<exists>I"(2)[where \<beta>=R])
    by (auto intro!: 1 2 "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2[const_var]"[axiom_inst]
                     Ordinary.GEN "\<rightarrow>I" Ordinary.\<psi>)
qed

text\<open>Note: not explicitly in PLM.\<close>
AOT_theorem "eq-part:3[terms]": \<open>\<Pi> \<approx>\<^sub>E \<Pi>''\<close> if \<open>\<Pi> \<approx>\<^sub>E \<Pi>'\<close> and \<open>\<Pi>' \<approx>\<^sub>E \<Pi>''\<close>
  using "eq-part:3"[unvarify F G H, THEN "\<rightarrow>E"] eq_den_1 eq_den_2 "\<rightarrow>I" "&I"
  by (metis that(1) that(2))
declare "eq-part:3[terms]"[trans]

AOT_theorem "eq-part:4": \<open>F \<approx>\<^sub>E G \<equiv> \<forall>H (H \<approx>\<^sub>E F \<equiv> H \<approx>\<^sub>E G)\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume 0: \<open>F \<approx>\<^sub>E G\<close>
  AOT_hence 1: \<open>G \<approx>\<^sub>E F\<close> using "eq-part:2"[THEN "\<rightarrow>E"] by blast
  AOT_show \<open>\<forall>H (H \<approx>\<^sub>E F \<equiv> H \<approx>\<^sub>E G)\<close>
  proof (rule GEN; rule "\<equiv>I"; rule "\<rightarrow>I")
    AOT_show \<open>H \<approx>\<^sub>E G\<close> if \<open>H \<approx>\<^sub>E F\<close> for H using 0
      by (meson "&I" "eq-part:3" that "vdash-properties:6")
  next
    AOT_show \<open>H \<approx>\<^sub>E F\<close> if \<open>H \<approx>\<^sub>E G\<close> for H using 1
      by (metis "&I" "eq-part:3" that "vdash-properties:6")
  qed
next
  AOT_assume \<open>\<forall>H (H \<approx>\<^sub>E F \<equiv> H \<approx>\<^sub>E G)\<close>
  AOT_hence \<open>F \<approx>\<^sub>E F \<equiv> F \<approx>\<^sub>E G\<close> using "\<forall>E" by blast
  AOT_thus \<open>F \<approx>\<^sub>E G\<close> using "eq-part:1" "\<equiv>E" by blast
qed

AOT_define MapsE :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> ("_ |: _ \<longrightarrow>E _")
  "equi-rem:1":
  \<open>R |: F \<longrightarrow>E G \<equiv>\<^sub>d\<^sub>f R\<down> & F\<down> & G\<down> & \<forall>u ([F]u \<rightarrow> \<exists>!v ([G]v & [R]uv))\<close>

AOT_define MapsEOneToOne :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> ("_ |: _ \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>E _")
  "equi-rem:2":
  \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>E G \<equiv>\<^sub>d\<^sub>f
      R |: F \<longrightarrow>E G & \<forall>t\<forall>u\<forall>v (([F]t & [F]u & [G]v) \<rightarrow> ([R]tv & [R]uv \<rightarrow> t =\<^sub>E u))\<close>

AOT_define MapsEOnto :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> ("_ |: _ \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE _")
  "equi-rem:3":
  \<open>R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G \<equiv>\<^sub>d\<^sub>f R |: F \<longrightarrow>E G & \<forall>v ([G]v \<rightarrow> \<exists>u ([F]u & [R]uv))\<close>

AOT_define MapsEOneToOneOnto :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> ("_ |: _ \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE _")
  "equi-rem:4":
  \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G \<equiv>\<^sub>d\<^sub>f R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>E G & R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close>

AOT_theorem "equi-rem-thm":
  \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G \<equiv> R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close>
proof -
  AOT_have \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G \<equiv> R |: [\<lambda>x O!x & [F]x] \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> [\<lambda>x O!x & [G]x]\<close>
  proof(safe intro!: "\<equiv>I" "\<rightarrow>I" "&I")
    AOT_assume \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
    AOT_hence \<open>\<forall>u ([F]u \<rightarrow> \<exists>!v ([G]v & [R]uv))\<close>
          and \<open>\<forall>v ([G]v \<rightarrow> \<exists>!u ([F]u & [R]uv))\<close>
      using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
    AOT_hence a: \<open>([F]u \<rightarrow> \<exists>!v ([G]v & [R]uv))\<close>
          and b: \<open>([G]v \<rightarrow> \<exists>!u ([F]u & [R]uv))\<close> for u v
      using "Ordinary.\<forall>E" by fast+
    AOT_have \<open>([\<lambda>x [O!]x & [F]x]x \<rightarrow> \<exists>!y ([\<lambda>x [O!]x & [G]x]y & [R]xy))\<close> for x
      apply (AOT_subst \<open>[\<lambda>x [O!]x & [F]x]x\<close> \<open>[O!]x & [F]x\<close>)
       apply (rule "beta-C-meta"[THEN "\<rightarrow>E"])
       apply "cqt:2[lambda]"
      apply (AOT_subst \<open>[\<lambda>x [O!]x & [G]x]x\<close> \<open>[O!]x & [G]x\<close> for: x)
       apply (rule "beta-C-meta"[THEN "\<rightarrow>E"])
       apply "cqt:2[lambda]"
      apply (AOT_subst \<open>O!y & [G]y & [R]xy\<close> \<open>O!y & ([G]y & [R]xy)\<close> for: y)
       apply (meson "\<equiv>E"(6) "Associativity of &" "oth-class-taut:3:a")
      apply (rule "\<rightarrow>I") apply (frule "&E"(1)) apply (drule "&E"(2))
      by (fact a[unconstrain u, THEN "\<rightarrow>E", THEN "\<rightarrow>E", of x])
    AOT_hence A: \<open>\<forall>x ([\<lambda>x [O!]x & [F]x]x \<rightarrow> \<exists>!y ([\<lambda>x [O!]x & [G]x]y & [R]xy))\<close>
      by (rule GEN)
    AOT_have \<open>([\<lambda>x [O!]x & [G]x]y \<rightarrow> \<exists>!x ([\<lambda>x [O!]x & [F]x]x & [R]xy))\<close> for y
      apply (AOT_subst \<open>[\<lambda>x [O!]x & [G]x]y\<close> \<open>[O!]y & [G]y\<close>)
       apply (rule "beta-C-meta"[THEN "\<rightarrow>E"])
       apply "cqt:2[lambda]"
      apply (AOT_subst \<open>[\<lambda>x [O!]x & [F]x]x\<close> \<open>[O!]x & [F]x\<close> for: x)
       apply (rule "beta-C-meta"[THEN "\<rightarrow>E"])
       apply "cqt:2[lambda]"
      apply (AOT_subst \<open>O!x & [F]x & [R]xy\<close> \<open>O!x & ([F]x & [R]xy)\<close> for: x)
       apply (meson "\<equiv>E"(6) "Associativity of &" "oth-class-taut:3:a")
      apply (rule "\<rightarrow>I") apply (frule "&E"(1)) apply (drule "&E"(2))
      by (fact b[unconstrain v, THEN "\<rightarrow>E", THEN "\<rightarrow>E", of y])
    AOT_hence B: \<open>\<forall>y ([\<lambda>x [O!]x & [G]x]y \<rightarrow> \<exists>!x ([\<lambda>x [O!]x & [F]x]x & [R]xy))\<close>
      by (rule GEN)
    AOT_show \<open>R |: [\<lambda>x [O!]x & [F]x] \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> [\<lambda>x [O!]x & [G]x]\<close>
      by (safe intro!: "1-1-cor"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I"
                       "cqt:2[const_var]"[axiom_inst] A B)
          "cqt:2[lambda]"+
  next
    AOT_assume \<open>R |: [\<lambda>x [O!]x & [F]x] \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> [\<lambda>x [O!]x & [G]x]\<close>
    AOT_hence a: \<open>([\<lambda>x [O!]x & [F]x]x \<rightarrow> \<exists>!y ([\<lambda>x [O!]x & [G]x]y & [R]xy))\<close> and 
              b: \<open>([\<lambda>x [O!]x & [G]x]y \<rightarrow> \<exists>!x ([\<lambda>x [O!]x & [F]x]x & [R]xy))\<close> for x y
      using "1-1-cor"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" "\<forall>E"(2) by blast+
    AOT_have \<open>[F]u \<rightarrow> \<exists>!v ([G]v & [R]uv)\<close> for u
    proof (safe intro!: "\<rightarrow>I")
      AOT_assume fu: \<open>[F]u\<close>
      AOT_have 0: \<open>[\<lambda>x [O!]x & [F]x]u\<close>
        by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "cqt:2[const_var]"[axiom_inst]
                         Ordinary.\<psi> fu "&I")
      AOT_show \<open>\<exists>!v ([G]v & [R]uv)\<close>
        apply (AOT_subst \<open>[O!]x & ([G]x & [R]ux)\<close>
                         \<open>([O!]x & [G]x) & [R]ux\<close> for: x)
         apply (simp add: "Associativity of &")
        apply (AOT_subst (reverse) \<open>[O!]x & [G]x\<close>
                                   \<open>[\<lambda>x [O!]x & [G]x]x\<close> for: x)
         apply (rule "beta-C-meta"[THEN "\<rightarrow>E"])
         apply "cqt:2[lambda]"
        using a[THEN "\<rightarrow>E", OF 0] by blast
    qed
    AOT_hence A: \<open>\<forall>u ([F]u \<rightarrow> \<exists>!v ([G]v & [R]uv))\<close>
      by (rule Ordinary.GEN)
    AOT_have \<open>[G]v \<rightarrow> \<exists>!u ([F]u & [R]uv)\<close> for v
    proof (safe intro!: "\<rightarrow>I")
      AOT_assume gu: \<open>[G]v\<close>
      AOT_have 0: \<open>[\<lambda>x [O!]x & [G]x]v\<close>
        by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "cqt:2[const_var]"[axiom_inst]
                         Ordinary.\<psi> gu "&I")
      AOT_show \<open>\<exists>!u ([F]u & [R]uv)\<close>
        apply (AOT_subst \<open>[O!]x & ([F]x & [R]xv)\<close> \<open>([O!]x & [F]x) & [R]xv\<close> for: x)
         apply (simp add: "Associativity of &")
        apply (AOT_subst (reverse) \<open>[O!]x & [F]x\<close>\<open>[\<lambda>x [O!]x & [F]x]x\<close>  for: x)
         apply (rule "beta-C-meta"[THEN "\<rightarrow>E"])
         apply "cqt:2[lambda]"
        using b[THEN "\<rightarrow>E", OF 0] by blast
    qed
    AOT_hence B: \<open>\<forall>v ([G]v \<rightarrow> \<exists>!u ([F]u & [R]uv))\<close> by (rule Ordinary.GEN)
    AOT_show \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
      by (safe intro!: "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" A B "cqt:2[const_var]"[axiom_inst])
  qed
  also AOT_have \<open>\<dots> \<equiv> R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close>
  proof(safe intro!: "\<equiv>I" "\<rightarrow>I" "&I")
    AOT_assume \<open>R |: [\<lambda>x [O!]x & [F]x] \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> [\<lambda>x [O!]x & [G]x]\<close>
    AOT_hence a: \<open>([\<lambda>x [O!]x & [F]x]x \<rightarrow> \<exists>!y ([\<lambda>x [O!]x & [G]x]y & [R]xy))\<close> and 
              b: \<open>([\<lambda>x [O!]x & [G]x]y \<rightarrow> \<exists>!x ([\<lambda>x [O!]x & [F]x]x & [R]xy))\<close> for x y
      using "1-1-cor"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" "\<forall>E"(2) by blast+
    AOT_show \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close>
    proof (safe intro!: "equi-rem:4"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "equi-rem:3"[THEN "\<equiv>\<^sub>d\<^sub>fI"]
                        "equi-rem:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "equi-rem:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"]
                        "cqt:2[const_var]"[axiom_inst] Ordinary.GEN "\<rightarrow>I")
      fix u
      AOT_assume fu: \<open>[F]u\<close>
      AOT_have 0: \<open>[\<lambda>x [O!]x & [F]x]u\<close>
        by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "cqt:2[const_var]"[axiom_inst]
                         Ordinary.\<psi> fu "&I")
      AOT_hence 1: \<open>\<exists>!y ([\<lambda>x [O!]x & [G]x]y & [R]uy)\<close>
        using a[THEN "\<rightarrow>E"] by blast
      AOT_show \<open>\<exists>!v ([G]v & [R]uv)\<close>
        apply (AOT_subst \<open>[O!]x & ([G]x & [R]ux)\<close> \<open>([O!]x & [G]x) & [R]ux\<close> for: x)
         apply (simp add: "Associativity of &")
        apply (AOT_subst (reverse) \<open>[O!]x & [G]x\<close> \<open>[\<lambda>x [O!]x & [G]x]x\<close> for: x)
         apply (rule "beta-C-meta"[THEN "\<rightarrow>E"])
         apply "cqt:2[lambda]"
        by (fact 1)
    next
      fix t u v
      AOT_assume \<open>[F]t & [F]u & [G]v\<close> and rtv_tuv: \<open>[R]tv & [R]uv\<close>
      AOT_hence oft: \<open>[\<lambda>x O!x & [F]x]t\<close> and
                ofu: \<open>[\<lambda>x O!x & [F]x]u\<close> and
                ogv: \<open>[\<lambda>x O!x & [G]x]v\<close>
        by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I"
                 simp: Ordinary.\<psi> dest: "&E")
      AOT_hence \<open>\<exists>!x ([\<lambda>x [O!]x & [F]x]x & [R]xv)\<close>
        using b[THEN "\<rightarrow>E"] by blast
      then AOT_obtain a where
          a_prop: \<open>[\<lambda>x [O!]x & [F]x]a & [R]av &
                   \<forall>x (([\<lambda>x [O!]x & [F]x]x & [R]xv) \<rightarrow> x = a)\<close>
        using "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "\<exists>E"[rotated] by blast
      AOT_hence ua: \<open>u = a\<close>
        using ofu rtv_tuv[THEN "&E"(2)] "\<forall>E"(2) "\<rightarrow>E" "&I" "&E"(2) by blast
      moreover AOT_have ta: \<open>t = a\<close>
        using a_prop oft rtv_tuv[THEN "&E"(1)] "\<forall>E"(2) "\<rightarrow>E" "&I" "&E"(2) by blast
      ultimately AOT_have \<open>t = u\<close> by (metis "rule=E" id_sym)
      AOT_thus \<open>t =\<^sub>E u\<close>
        using "rule=E" id_sym "ord=Eequiv:1" Ordinary.\<psi> ta ua "\<rightarrow>E" by fast
    next
      fix u
      AOT_assume \<open>[F]u\<close>
      AOT_hence \<open>[\<lambda>x O!x & [F]x]u\<close>
        by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I"
                 simp: "cqt:2[const_var]"[axiom_inst]  Ordinary.\<psi>)
      AOT_hence \<open>\<exists>!y ([\<lambda>x [O!]x & [G]x]y & [R]uy)\<close>
        using a[THEN "\<rightarrow>E"] by blast
      then AOT_obtain a where
        a_prop: \<open>[\<lambda>x [O!]x & [G]x]a & [R]ua &
                 \<forall>x (([\<lambda>x [O!]x & [G]x]x & [R]ux) \<rightarrow> x = a)\<close>
        using "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "\<exists>E"[rotated] by blast
      AOT_have \<open>O!a & [G]a\<close>
        by (rule "\<beta>\<rightarrow>C"(1)) (auto simp: a_prop[THEN "&E"(1), THEN "&E"(1)])
      AOT_hence \<open>O!a\<close> and \<open>[G]a\<close> using "&E" by blast+
      moreover AOT_have \<open>\<forall>v ([G]v & [R]uv \<rightarrow> v =\<^sub>E a)\<close>
      proof(safe intro!: Ordinary.GEN "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
        fix v
        AOT_assume \<open>[G]v\<close> and ruv: \<open>[R]uv\<close>
        AOT_hence \<open>[\<lambda>x [O!]x & [G]x]v\<close>
          by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" simp: Ordinary.\<psi>)
        AOT_hence \<open>v = a\<close>
          using a_prop[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF "&I"] ruv by blast
        AOT_thus \<open>v =\<^sub>E a\<close>
          using "rule=E" "ord=Eequiv:1" Ordinary.\<psi> "\<rightarrow>E" by fast
      qed
      ultimately AOT_have \<open>O!a & ([G]a & [R]ua & \<forall>v' ([G]v' & [R]uv' \<rightarrow> v' =\<^sub>E a))\<close>
        using "\<exists>I" "&I" a_prop[THEN "&E"(1), THEN "&E"(2)] by simp
      AOT_hence \<open>\<exists>v ([G]v & [R]uv & \<forall>v' ([G]v' & [R]uv' \<rightarrow> v' =\<^sub>E v))\<close>
        by (rule "\<exists>I")
      AOT_thus \<open>\<exists>!v ([G]v & [R]uv)\<close>
        by (rule "equi:1"[THEN "\<equiv>E"(2)])
    next
      fix v
      AOT_assume \<open>[G]v\<close>
      AOT_hence \<open>[\<lambda>x O!x & [G]x]v\<close>
        by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" Ordinary.\<psi>)
      AOT_hence \<open>\<exists>!x ([\<lambda>x [O!]x & [F]x]x & [R]xv)\<close>
        using b[THEN "\<rightarrow>E"] by blast
      then AOT_obtain a where
        a_prop: \<open>[\<lambda>x [O!]x & [F]x]a & [R]av &
                 \<forall>y ([\<lambda>x [O!]x & [F]x]y & [R]yv \<rightarrow> y = a)\<close>
        using "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "\<exists>E"[rotated]] by blast
      AOT_have \<open>O!a & [F]a\<close>
        by (rule "\<beta>\<rightarrow>C"(1)) (auto simp: a_prop[THEN "&E"(1), THEN "&E"(1)])
      AOT_hence \<open>O!a & ([F]a & [R]av)\<close>
        using a_prop[THEN "&E"(1), THEN "&E"(2)] "&E" "&I" by metis
      AOT_thus \<open>\<exists>u ([F]u & [R]uv)\<close>
        by (rule "\<exists>I")
    qed
  next
    AOT_assume \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close>
    AOT_hence 1: \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>E G\<close>
          and 2: \<open>R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close>
      using "equi-rem:4"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
    AOT_hence 3: \<open>R |: F \<longrightarrow>E G\<close>
          and A: \<open>\<forall>t \<forall>u \<forall>v ([F]t & [F]u & [G]v \<rightarrow> ([R]tv & [R]uv \<rightarrow> t =\<^sub>E u))\<close>
      using "equi-rem:2"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF 1] "&E" by blast+
    AOT_hence B: \<open>\<forall>u ([F]u \<rightarrow> \<exists>!v ([G]v & [R]uv))\<close>
      using "equi-rem:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
    AOT_have C: \<open>\<forall>v ([G]v \<rightarrow> \<exists>u ([F]u & [R]uv))\<close>
      using "equi-rem:3"[THEN "\<equiv>\<^sub>d\<^sub>fE", OF 2] "&E" by blast
    AOT_show \<open>R |: [\<lambda>x [O!]x & [F]x] \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> [\<lambda>x [O!]x & [G]x]\<close>
    proof (rule "1-1-cor"[THEN "\<equiv>\<^sub>d\<^sub>fI"];
           safe intro!: "&I" "cqt:2" GEN "\<rightarrow>I")
      fix x
      AOT_assume 1: \<open>[\<lambda>x [O!]x & [F]x]x\<close>
      AOT_have \<open>O!x & [F]x\<close>
        by (rule "\<beta>\<rightarrow>C"(1)) (auto simp: 1)
      AOT_hence \<open>\<exists>!v ([G]v & [R]xv)\<close>
        using B[THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "&E" by blast
      then AOT_obtain y where
        y_prop: \<open>O!y & ([G]y & [R]xy & \<forall>u ([G]u & [R]xu \<rightarrow> u =\<^sub>E y))\<close>
        using "equi:1"[THEN "\<equiv>E"(1)] "\<exists>E"[rotated] by fastforce
      AOT_hence \<open>[\<lambda>x O!x & [G]x]y\<close>
        by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" dest: "&E")
      moreover AOT_have \<open>\<forall>z ([\<lambda>x O!x & [G]x]z & [R]xz \<rightarrow> z = y)\<close>
      proof(safe intro!: GEN "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
        fix z
        AOT_assume 1: \<open>[\<lambda>x [O!]x & [G]x]z\<close>
        AOT_have 2: \<open>O!z & [G]z\<close>
          by (rule "\<beta>\<rightarrow>C"(1)) (auto simp: 1)
        moreover AOT_assume \<open>[R]xz\<close>
        ultimately AOT_have \<open>z =\<^sub>E y\<close>
          using y_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2),
                       THEN "\<rightarrow>E", THEN "\<rightarrow>E", rotated, OF "&I"] "&E"
          by blast
        AOT_thus \<open>z = y\<close>
          using 2[THEN "&E"(1)] by (metis "=E-simple:2" "\<rightarrow>E")
      qed
      ultimately AOT_have \<open>[\<lambda>x O!x & [G]x]y & [R]xy &
                           \<forall>z ([\<lambda>x O!x & [G]x]z & [R]xz \<rightarrow> z = y)\<close>
        using y_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(2)] "&I" by auto
      AOT_hence \<open>\<exists>y ([\<lambda>x O!x & [G]x]y & [R]xy &
                    \<forall>z ([\<lambda>x O!x & [G]x]z & [R]xz \<rightarrow> z = y))\<close>
        by (rule "\<exists>I")
      AOT_thus \<open>\<exists>!y ([\<lambda>x [O!]x & [G]x]y & [R]xy)\<close>
        using "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] by fast
    next
      fix y
      AOT_assume 1: \<open>[\<lambda>x [O!]x & [G]x]y\<close>
      AOT_have oy_gy: \<open>O!y & [G]y\<close>
        by (rule "\<beta>\<rightarrow>C"(1)) (auto simp: 1)
      AOT_hence \<open>\<exists>u ([F]u & [R]uy)\<close>
        using C[THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "&E" by blast
      then AOT_obtain x where x_prop: \<open>O!x & ([F]x & [R]xy)\<close>
        using "\<exists>E"[rotated] by blast
      AOT_hence ofx: \<open>[\<lambda>x O!x & [F]x]x\<close>
        by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" dest: "&E")
      AOT_have \<open>\<exists>\<alpha> ([\<lambda>x [O!]x & [F]x]\<alpha> & [R]\<alpha>y &
                    \<forall>\<beta> ([\<lambda>x [O!]x & [F]x]\<beta> & [R]\<beta>y \<rightarrow> \<beta> = \<alpha>))\<close>
      proof (safe intro!: "\<exists>I"(2)[where \<beta>=x] "&I" GEN "\<rightarrow>I")
        AOT_show \<open>[\<lambda>x O!x & [F]x]x\<close> using ofx.
      next
        AOT_show \<open>[R]xy\<close> using x_prop[THEN "&E"(2), THEN "&E"(2)].
      next
        fix z
        AOT_assume 1: \<open>[\<lambda>x [O!]x & [F]x]z & [R]zy\<close>
        AOT_have oz_fz: \<open>O!z & [F]z\<close>
          by (rule "\<beta>\<rightarrow>C"(1)) (auto simp: 1[THEN "&E"(1)])
        AOT_have \<open>z =\<^sub>E x\<close>
          using A[THEN "\<forall>E"(2)[where \<beta>=z], THEN "\<rightarrow>E", THEN "\<forall>E"(2)[where \<beta>=x],
                  THEN "\<rightarrow>E", THEN "\<forall>E"(2)[where \<beta>=y], THEN "\<rightarrow>E",
                  THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF oz_fz[THEN "&E"(1)],
                  OF x_prop[THEN "&E"(1)], OF oy_gy[THEN "&E"(1)], OF "&I", OF "&I",
                  OF oz_fz[THEN "&E"(2)], OF x_prop[THEN "&E"(2), THEN "&E"(1)],
                  OF oy_gy[THEN "&E"(2)], OF "&I", OF 1[THEN "&E"(2)],
                  OF x_prop[THEN "&E"(2), THEN "&E"(2)]].
        AOT_thus \<open>z = x\<close>
          by (metis "=E-simple:2" "vdash-properties:10")
      qed
      AOT_thus \<open>\<exists>!x ([\<lambda>x [O!]x & [F]x]x & [R]xy)\<close>
        by (rule "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
    qed
  qed
  finally show ?thesis.
qed

AOT_theorem "empty-approx:1": \<open>(\<not>\<exists>u [F]u & \<not>\<exists>v [H]v) \<rightarrow> F \<approx>\<^sub>E H\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume 0: \<open>\<not>\<exists>u [F]u\<close> and 1: \<open>\<not>\<exists>v [H]v\<close>
  AOT_have \<open>\<forall>u ([F]u \<rightarrow> \<exists>!v ([H]v & [R]uv))\<close> for R
  proof(rule Ordinary.GEN; rule "\<rightarrow>I"; rule "raa-cor:1")
    fix u
    AOT_assume \<open>[F]u\<close>
    AOT_hence \<open>\<exists>u [F]u\<close> using "Ordinary.\<exists>I" "&I" by fast
    AOT_thus \<open>\<exists>u [F]u & \<not>\<exists>u [F]u\<close> using "&I" 0 by blast
  qed
  moreover AOT_have \<open>\<forall>v ([H]v \<rightarrow> \<exists>!u ([F]u & [R]uv))\<close> for R
  proof(rule Ordinary.GEN; rule "\<rightarrow>I"; rule "raa-cor:1")
    fix v
    AOT_assume \<open>[H]v\<close>
    AOT_hence \<open>\<exists>v [H]v\<close> using "Ordinary.\<exists>I" "&I" by fast
    AOT_thus \<open>\<exists>v [H]v & \<not>\<exists>v [H]v\<close> using 1 "&I" by blast
  qed
  ultimately AOT_have \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E H\<close> for R
    apply (safe intro!: "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" GEN "cqt:2[const_var]"[axiom_inst])
    using "\<forall>E" by blast+
  AOT_hence \<open>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E H\<close> by (rule "\<exists>I")
  AOT_thus \<open>F \<approx>\<^sub>E H\<close>
    by (rule "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
qed

AOT_theorem "empty-approx:2": \<open>(\<exists>u [F]u & \<not>\<exists>v [H]v) \<rightarrow> \<not>(F \<approx>\<^sub>E H)\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2); rule "raa-cor:2")
  AOT_assume 1: \<open>\<exists>u [F]u\<close> and 2: \<open>\<not>\<exists>v [H]v\<close>
  AOT_obtain b where b_prop: \<open>O!b & [F]b\<close>
    using 1 "\<exists>E"[rotated] by blast
  AOT_assume \<open>F \<approx>\<^sub>E H\<close>
  AOT_hence \<open>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E H\<close>
    by (rule "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fE"])
  then AOT_obtain R where \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E H\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<theta>: \<open>\<forall>u ([F]u \<rightarrow> \<exists>!v ([H]v & [R]uv))\<close>
    using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_have \<open>\<exists>!v ([H]v & [R]bv)\<close> for u
    using \<theta>[THEN "\<forall>E"(2)[where \<beta>=b], THEN "\<rightarrow>E", THEN "\<rightarrow>E",
            OF b_prop[THEN "&E"(1)], OF b_prop[THEN "&E"(2)]].
  AOT_hence \<open>\<exists>v ([H]v & [R]bv & \<forall>u ([H]u & [R]bu \<rightarrow> u =\<^sub>E v))\<close>
    by (rule "equi:1"[THEN "\<equiv>E"(1)])
  then AOT_obtain x where \<open>O!x & ([H]x & [R]bx & \<forall>u ([H]u & [R]bu \<rightarrow> u =\<^sub>E x))\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<open>O!x & [H]x\<close> using "&E" "&I" by blast
  AOT_hence \<open>\<exists>v [H]v\<close> by (rule "\<exists>I")
  AOT_thus \<open>\<exists>v [H]v & \<not>\<exists>v [H]v\<close> using 2 "&I" by blast
qed


AOT_define FminusU :: \<open>\<Pi> \<Rightarrow> \<tau> \<Rightarrow> \<Pi>\<close> ("_\<^sup>-\<^sup>_")
  "F-u": \<open>[F]\<^sup>-\<^sup>x =\<^sub>d\<^sub>f [\<lambda>z [F]z & z \<noteq>\<^sub>E x]\<close>

text\<open>Note: not explicitly in PLM.\<close>
AOT_theorem "F-u[den]": \<open>[F]\<^sup>-\<^sup>x\<down>\<close>
  by (rule "=\<^sub>d\<^sub>fI"(1)[OF "F-u", where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", simplified]; "cqt:2[lambda]")
AOT_theorem "F-u[equiv]": \<open>[[F]\<^sup>-\<^sup>x]y \<equiv> ([F]y & y \<noteq>\<^sub>E x)\<close>
  by (auto intro: "F-u"[THEN "=\<^sub>d\<^sub>fI"(1), where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", simplified]
           intro!: "cqt:2" "beta-C-cor:2"[THEN "\<rightarrow>E", THEN "\<forall>E"(2)])

AOT_theorem eqP': \<open>F \<approx>\<^sub>E G & [F]u & [G]v \<rightarrow> [F]\<^sup>-\<^sup>u \<approx>\<^sub>E [G]\<^sup>-\<^sup>v\<close>
proof (rule "\<rightarrow>I"; frule "&E"(2); drule "&E"(1); frule "&E"(2); drule "&E"(1))
  AOT_assume \<open>F \<approx>\<^sub>E G\<close>
  AOT_hence \<open>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
    using "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain R where R_prop: \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence A: \<open>\<forall>u ([F]u \<rightarrow> \<exists>!v ([G]v & [R]uv))\<close>
        and B: \<open>\<forall>v ([G]v \<rightarrow> \<exists>!u ([F]u & [R]uv))\<close>
    using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_have \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close>
    using "equi-rem-thm"[THEN "\<equiv>E"(1), OF R_prop].
  AOT_hence \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>E G & R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close>
    using "equi-rem:4"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_hence C: \<open>\<forall>t\<forall>u\<forall>v (([F]t & [F]u & [G]v) \<rightarrow> ([R]tv & [R]uv \<rightarrow> t =\<^sub>E u))\<close>
    using "equi-rem:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_assume fu: \<open>[F]u\<close>
  AOT_assume gv: \<open>[G]v\<close>
  AOT_have \<open>[\<lambda>z [\<Pi>]z & z \<noteq>\<^sub>E \<kappa>]\<down>\<close> for \<Pi> \<kappa>
    by "cqt:2[lambda]"
  note \<Pi>_minus_\<kappa>I = "rule-id-df:2:b[2]"[
      where \<tau>=\<open>(\<lambda>(\<Pi>, \<kappa>). \<guillemotleft>[\<Pi>]\<^sup>-\<^sup>\<kappa>\<guillemotright>)\<close>, simplified, OF "F-u", simplified, OF this]
   and \<Pi>_minus_\<kappa>E = "rule-id-df:2:a[2]"[
      where \<tau>=\<open>(\<lambda>(\<Pi>, \<kappa>). \<guillemotleft>[\<Pi>]\<^sup>-\<^sup>\<kappa>\<guillemotright>)\<close>, simplified, OF "F-u", simplified, OF this]
  AOT_have \<Pi>_minus_\<kappa>_den: \<open>[\<Pi>]\<^sup>-\<^sup>\<kappa>\<down>\<close> for \<Pi> \<kappa>
    by (rule \<Pi>_minus_\<kappa>I) "cqt:2[lambda]"+
  {
    fix R
    AOT_assume R_prop: \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
    AOT_hence A: \<open>\<forall>u ([F]u \<rightarrow> \<exists>!v ([G]v & [R]uv))\<close>
          and B: \<open>\<forall>v ([G]v \<rightarrow> \<exists>!u ([F]u & [R]uv))\<close>
      using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
    AOT_have \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close>
      using "equi-rem-thm"[THEN "\<equiv>E"(1), OF R_prop].
    AOT_hence \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>E G & R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close>
      using "equi-rem:4"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
    AOT_hence C: \<open>\<forall>t\<forall>u\<forall>v (([F]t & [F]u & [G]v) \<rightarrow> ([R]tv & [R]uv \<rightarrow> t =\<^sub>E u))\<close>
      using "equi-rem:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast

    AOT_assume Ruv: \<open>[R]uv\<close>
    AOT_have \<open>R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E [G]\<^sup>-\<^sup>v\<close>
    proof(safe intro!: "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2[const_var]"[axiom_inst]
                       \<Pi>_minus_\<kappa>_den Ordinary.GEN "\<rightarrow>I")
      fix u'
      AOT_assume \<open>[[F]\<^sup>-\<^sup>u]u'\<close>
      AOT_hence 0: \<open>[\<lambda>z [F]z & z \<noteq>\<^sub>E u]u'\<close>
        using \<Pi>_minus_\<kappa>E by fast
      AOT_have 0: \<open>[F]u' & u' \<noteq>\<^sub>E u\<close>
        by (rule "\<beta>\<rightarrow>C"(1)[where \<kappa>\<^sub>1\<kappa>\<^sub>n="AOT_term_of_var (Ordinary.Rep u')"]) (fact 0)
      AOT_have \<open>\<exists>!v ([G]v & [R]u'v)\<close>
        using A[THEN "Ordinary.\<forall>E"[where \<alpha>=u'], THEN "\<rightarrow>E", OF 0[THEN "&E"(1)]].
      then AOT_obtain v' where
        v'_prop: \<open>[G]v' & [R]u'v' & \<forall> t ([G]t & [R]u't \<rightarrow> t =\<^sub>E v')\<close>
        using "equi:1"[THEN "\<equiv>E"(1)] "Ordinary.\<exists>E"[rotated] by fastforce

      AOT_show \<open>\<exists>!v' ([[G]\<^sup>-\<^sup>v]v' & [R]u'v')\<close>
      proof (safe intro!: "equi:1"[THEN "\<equiv>E"(2)] "Ordinary.\<exists>I"[where \<beta>=v']
                          "&I" Ordinary.GEN "\<rightarrow>I")
        AOT_show \<open>[[G]\<^sup>-\<^sup>v]v'\<close>
        proof (rule \<Pi>_minus_\<kappa>I; 
               safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" "thm-neg=E"[THEN "\<equiv>E"(2)])
          AOT_show \<open>[G]v'\<close> using v'_prop "&E" by blast
        next
          AOT_show \<open>\<not>v' =\<^sub>E v\<close>
          proof (rule "raa-cor:2")
            AOT_assume \<open>v' =\<^sub>E v\<close>
            AOT_hence \<open>v' = v\<close> by (metis "=E-simple:2" "\<rightarrow>E")
            AOT_hence Ruv': \<open>[R]uv'\<close> using "rule=E" Ruv id_sym by fast
            AOT_have \<open>u' =\<^sub>E u\<close>
              by (rule C[THEN "Ordinary.\<forall>E", THEN "Ordinary.\<forall>E",
                         THEN "Ordinary.\<forall>E"[where \<alpha>=v'], THEN "\<rightarrow>E", THEN "\<rightarrow>E"])
                 (safe intro!: "&I" 0[THEN "&E"(1)] fu
                               v'_prop[THEN "&E"(1), THEN "&E"(1)]
                               Ruv' v'_prop[THEN "&E"(1), THEN "&E"(2)])
            moreover AOT_have \<open>\<not>(u' =\<^sub>E u)\<close>
              using "0" "&E"(2) "\<equiv>E"(1) "thm-neg=E" by blast
            ultimately AOT_show \<open>u' =\<^sub>E u & \<not>u' =\<^sub>E u\<close> using "&I" by blast
          qed
        qed
      next
        AOT_show \<open>[R]u'v'\<close> using v'_prop "&E" by blast
      next
        fix t
        AOT_assume t_prop: \<open>[[G]\<^sup>-\<^sup>v]t & [R]u't\<close>
        AOT_have gt_t_noteq_v: \<open>[G]t & t \<noteq>\<^sub>E v\<close>
          apply (rule "\<beta>\<rightarrow>C"(1)[where \<kappa>\<^sub>1\<kappa>\<^sub>n="AOT_term_of_var (Ordinary.Rep t)"])
          apply (rule \<Pi>_minus_\<kappa>E)
          by (fact t_prop[THEN "&E"(1)])
        AOT_show \<open>t =\<^sub>E v'\<close>
          using v'_prop[THEN "&E"(2), THEN "Ordinary.\<forall>E", THEN "\<rightarrow>E",
                        OF "&I", OF gt_t_noteq_v[THEN "&E"(1)],
                        OF t_prop[THEN "&E"(2)]].
      qed
    next
      fix v'
      AOT_assume G_minus_v_v': \<open>[[G]\<^sup>-\<^sup>v]v'\<close>
      AOT_have gt_t_noteq_v: \<open>[G]v' & v' \<noteq>\<^sub>E v\<close>
        apply (rule "\<beta>\<rightarrow>C"(1)[where \<kappa>\<^sub>1\<kappa>\<^sub>n="AOT_term_of_var (Ordinary.Rep v')"])
        apply (rule \<Pi>_minus_\<kappa>E)
        by (fact G_minus_v_v')
      AOT_have \<open>\<exists>!u([F]u & [R]uv')\<close>
        using B[THEN "Ordinary.\<forall>E", THEN "\<rightarrow>E", OF gt_t_noteq_v[THEN "&E"(1)]].
      then AOT_obtain u' where
        u'_prop: \<open>[F]u' & [R]u'v' & \<forall>t ([F]t & [R]tv' \<rightarrow> t =\<^sub>E u')\<close>
        using "equi:1"[THEN "\<equiv>E"(1)] "Ordinary.\<exists>E"[rotated] by fastforce
      AOT_show \<open>\<exists>!u' ([[F]\<^sup>-\<^sup>u]u' & [R]u'v')\<close>
      proof (safe intro!: "equi:1"[THEN "\<equiv>E"(2)] "Ordinary.\<exists>I"[where \<beta>=u'] "&I"
                          u'_prop[THEN "&E"(1), THEN "&E"(2)] Ordinary.GEN "\<rightarrow>I")
        AOT_show \<open>[[F]\<^sup>-\<^sup>u]u'\<close>
        proof (rule \<Pi>_minus_\<kappa>I;
               safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" "thm-neg=E"[THEN "\<equiv>E"(2)]
               u'_prop[THEN "&E"(1), THEN "&E"(1)]; rule "raa-cor:2")
          AOT_assume u'_eq_u: \<open>u' =\<^sub>E u\<close>
          AOT_hence \<open>u' = u\<close>
            using "=E-simple:2" "vdash-properties:10" by blast
          AOT_hence Ru'v: \<open>[R]u'v\<close> using "rule=E" Ruv id_sym by fast
          AOT_have \<open>v' \<noteq>\<^sub>E v\<close>
            using "&E"(2) gt_t_noteq_v by blast
          AOT_hence v'_noteq_v: \<open>\<not>(v' =\<^sub>E v)\<close> by (metis "\<equiv>E"(1) "thm-neg=E")
          AOT_have \<open>\<exists>u ([G]u & [R]u'u & \<forall>v ([G]v & [R]u'v \<rightarrow> v =\<^sub>E u))\<close>
            using A[THEN "Ordinary.\<forall>E", THEN "\<rightarrow>E",
                    OF u'_prop[THEN "&E"(1), THEN "&E"(1)],
                    THEN "equi:1"[THEN "\<equiv>E"(1)]].
          then AOT_obtain t where
            t_prop: \<open>[G]t & [R]u't & \<forall>v ([G]v & [R]u'v \<rightarrow> v =\<^sub>E t)\<close>
            using "Ordinary.\<exists>E"[rotated] by meson
          AOT_have \<open>v =\<^sub>E t\<close> if \<open>[G]v\<close> and \<open>[R]u'v\<close> for v
            using t_prop[THEN "&E"(2), THEN "Ordinary.\<forall>E", THEN "\<rightarrow>E",
                         OF "&I", OF that].
          AOT_hence \<open>v' =\<^sub>E t\<close> and \<open>v =\<^sub>E t\<close>
            by (auto simp: gt_t_noteq_v[THEN "&E"(1)] Ru'v gv
                           u'_prop[THEN "&E"(1), THEN "&E"(2)])
          AOT_hence \<open>v' =\<^sub>E v\<close>
            using "rule=E" "=E-simple:2" id_sym "\<rightarrow>E" by fast
          AOT_thus \<open>v' =\<^sub>E v & \<not>v' =\<^sub>E v\<close>
            using v'_noteq_v "&I" by blast
        qed
      next
        fix t
        AOT_assume 0: \<open>[[F]\<^sup>-\<^sup>u]t & [R]tv'\<close>
        moreover AOT_have \<open>[F]t & t \<noteq>\<^sub>E u\<close>
          apply (rule "\<beta>\<rightarrow>C"(1)[where \<kappa>\<^sub>1\<kappa>\<^sub>n="AOT_term_of_var (Ordinary.Rep t)"])
          apply (rule \<Pi>_minus_\<kappa>E)
          by (fact 0[THEN "&E"(1)])
        ultimately AOT_show \<open>t =\<^sub>E u'\<close>
          using u'_prop[THEN "&E"(2), THEN "Ordinary.\<forall>E", THEN "\<rightarrow>E", OF "&I"]
                "&E" by blast
      qed
    qed
    AOT_hence \<open>\<exists>R R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E [G]\<^sup>-\<^sup>v\<close>
      by (rule "\<exists>I")
  } note 1 = this
  moreover {
    AOT_assume not_Ruv: \<open>\<not>[R]uv\<close>
    AOT_have \<open>\<exists>!v ([G]v & [R]uv)\<close>
      using A[THEN "Ordinary.\<forall>E", THEN "\<rightarrow>E", OF fu].
    then AOT_obtain b where
      b_prop: \<open>O!b & ([G]b & [R]ub & \<forall>t([G]t & [R]ut \<rightarrow> t =\<^sub>E b))\<close>
      using "equi:1"[THEN "\<equiv>E"(1)] "\<exists>E"[rotated] by fastforce
    AOT_hence ob: \<open>O!b\<close> and gb: \<open>[G]b\<close> and Rub: \<open>[R]ub\<close>
      using "&E" by blast+
    AOT_have \<open>O!t \<rightarrow> ([G]t & [R]ut \<rightarrow> t =\<^sub>E b)\<close> for t
      using b_prop "&E"(2) "\<forall>E"(2) by blast
    AOT_hence b_unique: \<open>t =\<^sub>E b\<close> if \<open>O!t\<close> and \<open>[G]t\<close> and \<open>[R]ut\<close> for t
      by (metis Adjunction "modus-tollens:1" "reductio-aa:1" that)
    AOT_have not_v_eq_b: \<open>\<not>(v =\<^sub>E b)\<close>
    proof(rule "raa-cor:2")
      AOT_assume \<open>v =\<^sub>E b\<close>
      AOT_hence 0: \<open>v = b\<close>
        by (metis "=E-simple:2" "\<rightarrow>E")
      AOT_have \<open>[R]uv\<close>
        using b_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(2)]
              "rule=E"[rotated, OF 0[symmetric]] by fast
      AOT_thus \<open>[R]uv & \<not>[R]uv\<close>
        using not_Ruv "&I" by blast
    qed
    AOT_have not_b_eq_v: \<open>\<not>(b =\<^sub>E v)\<close>
      using "modus-tollens:1" not_v_eq_b "ord=Eequiv:2" by blast
    AOT_have \<open>\<exists>!u ([F]u & [R]uv)\<close>
      using B[THEN "Ordinary.\<forall>E", THEN "\<rightarrow>E", OF gv].
    then AOT_obtain a where
      a_prop: \<open>O!a & ([F]a & [R]av & \<forall>t([F]t & [R]tv \<rightarrow> t =\<^sub>E a))\<close>
      using "equi:1"[THEN "\<equiv>E"(1)] "\<exists>E"[rotated] by fastforce
    AOT_hence Oa: \<open>O!a\<close> and fa: \<open>[F]a\<close> and Rav: \<open>[R]av\<close>
      using "&E" by blast+
    AOT_have \<open>O!t \<rightarrow> ([F]t & [R]tv \<rightarrow> t =\<^sub>E a)\<close> for t
      using a_prop "&E" "\<forall>E"(2) by blast
    AOT_hence a_unique: \<open>t =\<^sub>E a\<close> if \<open>O!t\<close> and \<open>[F]t\<close> and \<open>[R]tv\<close> for t
      by (metis Adjunction "modus-tollens:1" "reductio-aa:1" that) 
    AOT_have not_u_eq_a: \<open>\<not>(u =\<^sub>E a)\<close>
    proof(rule "raa-cor:2")
      AOT_assume \<open>u =\<^sub>E a\<close>
      AOT_hence 0: \<open>u = a\<close>
        by (metis "=E-simple:2" "\<rightarrow>E")
      AOT_have \<open>[R]uv\<close>
        using a_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(2)]
              "rule=E"[rotated, OF 0[symmetric]] by fast
      AOT_thus \<open>[R]uv & \<not>[R]uv\<close>
        using not_Ruv "&I" by blast
    qed
    AOT_have not_a_eq_u: \<open>\<not>(a =\<^sub>E u)\<close>
      using "modus-tollens:1" not_u_eq_a "ord=Eequiv:2" by blast
    let ?R = \<open>\<guillemotleft>[\<lambda>u'v' (u' \<noteq>\<^sub>E u & v' \<noteq>\<^sub>E v & [R]u'v') \<or>
                      (u' =\<^sub>E a & v' =\<^sub>E b) \<or>
                      (u' =\<^sub>E u & v' =\<^sub>E v)]\<guillemotright>\<close>
    AOT_have \<open>[\<guillemotleft>?R\<guillemotright>]\<down>\<close> by "cqt:2[lambda]"
    AOT_hence \<open>\<exists> \<beta> \<beta> = [\<guillemotleft>?R\<guillemotright>]\<close>
      using "free-thms:1" "\<equiv>E"(1) by fast
    then AOT_obtain R\<^sub>1 where R\<^sub>1_def: \<open>R\<^sub>1 = [\<guillemotleft>?R\<guillemotright>]\<close>
      using "\<exists>E"[rotated] by blast
    AOT_have Rxy1: \<open>[R]xy\<close> if \<open>[R\<^sub>1]xy\<close> and \<open>x \<noteq>\<^sub>E u\<close> and \<open>x \<noteq>\<^sub>E a\<close> for x y
    proof -
      AOT_have 0: \<open>[\<guillemotleft>?R\<guillemotright>]xy\<close>
        by (rule "rule=E"[rotated, OF R\<^sub>1_def]) (fact that(1))
      AOT_have \<open>(x \<noteq>\<^sub>E u & y \<noteq>\<^sub>E v & [R]xy) \<or> (x =\<^sub>E a & y =\<^sub>E b) \<or> (x =\<^sub>E u & y =\<^sub>E v)\<close>
        using "\<beta>\<rightarrow>C"(1)[OF 0] by simp
      AOT_hence \<open>x \<noteq>\<^sub>E u & y \<noteq>\<^sub>E v & [R]xy\<close> using that(2,3)
        by (metis "\<or>E"(3) "Conjunction Simplification"(1) "\<equiv>E"(1)
                  "modus-tollens:1" "thm-neg=E")
      AOT_thus \<open>[R]xy\<close> using "&E" by blast+
    qed
    AOT_have Rxy2: \<open>[R]xy\<close>  if \<open>[R\<^sub>1]xy\<close> and \<open>y \<noteq>\<^sub>E v\<close> and \<open>y \<noteq>\<^sub>E b\<close> for x y
    proof -
      AOT_have 0: \<open>[\<guillemotleft>?R\<guillemotright>]xy\<close>
        by (rule "rule=E"[rotated, OF R\<^sub>1_def]) (fact that(1))
      AOT_have \<open>(x \<noteq>\<^sub>E u & y \<noteq>\<^sub>E v & [R]xy) \<or> (x =\<^sub>E a & y =\<^sub>E b) \<or> (x =\<^sub>E u & y =\<^sub>E v)\<close>
        using "\<beta>\<rightarrow>C"(1)[OF 0] by simp
      AOT_hence \<open>x \<noteq>\<^sub>E u & y \<noteq>\<^sub>E v & [R]xy\<close>
        using that(2,3)
        by (metis "\<or>E"(3) "Conjunction Simplification"(2) "\<equiv>E"(1)
                  "modus-tollens:1" "thm-neg=E")
      AOT_thus \<open>[R]xy\<close> using "&E" by blast+
    qed
    AOT_have R\<^sub>1xy: \<open>[R\<^sub>1]xy\<close> if \<open>[R]xy\<close> and \<open>x \<noteq>\<^sub>E u\<close> and \<open>y \<noteq>\<^sub>E v\<close> for x y
      by (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
         (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2"
                 simp: "&I" "ex:1:a" prod_denotesI "rule-ui:3" that "\<or>I"(1))
    AOT_have R\<^sub>1ab: \<open>[R\<^sub>1]ab\<close>
      apply (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
      apply (safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" prod_denotesI "&I")
      by (meson a_prop b_prop "&I" "&E"(1) "\<or>I"(1) "\<or>I"(2) "ord=Eequiv:1" "\<rightarrow>E")
    AOT_have R\<^sub>1uv: \<open>[R\<^sub>1]uv\<close>
      apply (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
      apply (safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" prod_denotesI "&I")
      by (meson "&I" "\<or>I"(2) "ord=Eequiv:1" Ordinary.\<psi> "\<rightarrow>E")
    moreover AOT_have \<open>R\<^sub>1 |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
    proof (safe intro!: "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" Ordinary.GEN "\<rightarrow>I")
      fix u'
      AOT_assume fu': \<open>[F]u'\<close>
      {
        AOT_assume not_u'_eq_u: \<open>\<not>(u' =\<^sub>E u)\<close> and not_u'_eq_a: \<open>\<not>(u' =\<^sub>E a)\<close>
        AOT_hence u'_noteq_u: \<open>u' \<noteq>\<^sub>E u\<close> and u'_noteq_a: \<open>u' \<noteq>\<^sub>E a\<close>
          by (metis "\<equiv>E"(2) "thm-neg=E")+
        AOT_have \<open>\<exists>!v ([G]v & [R]u'v)\<close>
          using A[THEN "Ordinary.\<forall>E", THEN "\<rightarrow>E", OF fu'].
        AOT_hence \<open>\<exists>v ([G]v & [R]u'v & \<forall>t ([G]t & [R]u't \<rightarrow> t =\<^sub>E v))\<close>
          using "equi:1"[THEN "\<equiv>E"(1)] by simp
        then AOT_obtain v' where
          v'_prop: \<open>[G]v' & [R]u'v' & \<forall>t ([G]t & [R]u't \<rightarrow> t =\<^sub>E v')\<close>
          using "Ordinary.\<exists>E"[rotated] by meson
        AOT_hence gv': \<open>[G]v'\<close> and Ru'v': \<open>[R]u'v'\<close>
          using "&E" by blast+
        AOT_have not_v'_eq_v: \<open>\<not>v' =\<^sub>E v\<close>
        proof (rule "raa-cor:2")
          AOT_assume \<open>v' =\<^sub>E v\<close>
          AOT_hence \<open>v' = v\<close>
            by (metis "=E-simple:2" "\<rightarrow>E")
          AOT_hence Ru'v: \<open>[R]u'v\<close>
            using "rule=E" Ru'v' by fast
          AOT_have \<open>u' =\<^sub>E a\<close>
            using a_unique[OF Ordinary.\<psi>, OF fu', OF Ru'v].
          AOT_thus \<open>u' =\<^sub>E a & \<not>u' =\<^sub>E a\<close>
            using not_u'_eq_a "&I" by blast
        qed
        AOT_hence v'_noteq_v: \<open>v' \<noteq>\<^sub>E v\<close>
          using "\<equiv>E"(2) "thm-neg=E" by blast
        AOT_have \<open>\<forall>t ([G]t & [R]u't \<rightarrow> t =\<^sub>E v')\<close>
          using v'_prop "&E" by blast
        AOT_hence \<open>[G]t & [R]u't \<rightarrow> t =\<^sub>E v'\<close> for t
          using "Ordinary.\<forall>E" by meson
        AOT_hence v'_unique: \<open>t =\<^sub>E v'\<close> if \<open>[G]t\<close> and \<open>[R]u't\<close> for t
          by (metis "&I" that "\<rightarrow>E")

        AOT_have \<open>[G]v' & [R\<^sub>1]u'v' & \<forall>t ([G]t & [R\<^sub>1]u't \<rightarrow> t =\<^sub>E v')\<close>
        proof (safe intro!: "&I" gv' R\<^sub>1xy Ru'v' u'_noteq_u u'_noteq_a "\<rightarrow>I"
                            Ordinary.GEN "thm-neg=E"[THEN "\<equiv>E"(2)] not_v'_eq_v)
          fix t
          AOT_assume 1: \<open>[G]t & [R\<^sub>1]u't\<close>
          AOT_have \<open>[R]u't\<close>
            using Rxy1[OF 1[THEN "&E"(2)], OF u'_noteq_u, OF u'_noteq_a].
          AOT_thus \<open>t =\<^sub>E v'\<close>
            using v'_unique 1[THEN "&E"(1)] by blast
        qed
        AOT_hence \<open>\<exists>v ([G]v & [R\<^sub>1]u'v & \<forall>t ([G]t & [R\<^sub>1]u't \<rightarrow> t =\<^sub>E v))\<close>
          by (rule "Ordinary.\<exists>I")
        AOT_hence \<open>\<exists>!v ([G]v & [R\<^sub>1]u'v)\<close>
          by (rule "equi:1"[THEN "\<equiv>E"(2)])
      }
      moreover {
        AOT_assume 0: \<open>u' =\<^sub>E u\<close>
        AOT_hence u'_eq_u: \<open>u' = u\<close>
          using "=E-simple:2" "\<rightarrow>E" by blast
        AOT_have \<open>\<exists>!v ([G]v & [R\<^sub>1]u'v)\<close>
        proof (safe intro!: "equi:1"[THEN "\<equiv>E"(2)] "Ordinary.\<exists>I"[where \<beta>=v]
                            "&I" Ordinary.GEN "\<rightarrow>I" gv)
          AOT_show \<open>[R\<^sub>1]u'v\<close>
            apply (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
            apply (safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" prod_denotesI)
            by (safe intro!: "\<or>I"(2) "&I" 0 "ord=Eequiv:1"[THEN "\<rightarrow>E", OF Ordinary.\<psi>])
        next
          fix v'
          AOT_assume \<open>[G]v' & [R\<^sub>1]u'v'\<close>
          AOT_hence 0: \<open>[R\<^sub>1]uv'\<close>
            using "rule=E"[rotated, OF u'_eq_u] "&E"(2) by fast
          AOT_have 1: \<open>[\<guillemotleft>?R\<guillemotright>]uv'\<close>
            by (rule "rule=E"[rotated, OF R\<^sub>1_def]) (fact 0)
          AOT_have 2: \<open>(u \<noteq>\<^sub>E u & v' \<noteq>\<^sub>E v & [R]uv') \<or>
                       (u =\<^sub>E a & v' =\<^sub>E b) \<or>
                       (u =\<^sub>E u & v' =\<^sub>E v)\<close>
            using "\<beta>\<rightarrow>C"(1)[OF 1] by simp
          AOT_have \<open>\<not>u \<noteq>\<^sub>E u\<close>
            using "\<equiv>E"(4) "modus-tollens:1" "ord=Eequiv:1" Ordinary.\<psi>
                  "reductio-aa:2" "thm-neg=E" by blast
          AOT_hence \<open>\<not>((u \<noteq>\<^sub>E u & v' \<noteq>\<^sub>E v & [R]uv') \<or> (u =\<^sub>E a & v' =\<^sub>E b))\<close>
            using not_u_eq_a
            by (metis "\<or>E"(2) "Conjunction Simplification"(1)
                      "modus-tollens:1" "reductio-aa:1")
          AOT_hence \<open>(u =\<^sub>E u & v' =\<^sub>E v)\<close>
            using 2 by (metis "\<or>E"(2))
          AOT_thus \<open>v' =\<^sub>E v\<close>
            using "&E" by blast
        qed
      }
      moreover {
        AOT_assume 0: \<open>u' =\<^sub>E a\<close>
        AOT_hence u'_eq_a: \<open>u' = a\<close>
          using "=E-simple:2" "\<rightarrow>E" by blast
        AOT_have \<open>\<exists>!v ([G]v & [R\<^sub>1]u'v)\<close>
        proof (safe intro!: "equi:1"[THEN "\<equiv>E"(2)] "\<exists>I"(2)[where \<beta>=b] "&I"
                            Ordinary.GEN "\<rightarrow>I" b_prop[THEN "&E"(1)]
                            b_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(1)])
          AOT_show \<open>[R\<^sub>1]u'b\<close>
            apply (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
            apply (safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" prod_denotesI)
            apply (rule "\<or>I"(1); rule "\<or>I"(2); rule "&I")
             apply (fact 0)
            using b_prop "&E"(1) "ord=Eequiv:1" "\<rightarrow>E" by blast
        next
          fix v'
          AOT_assume gv'_R1u'v': \<open>[G]v' & [R\<^sub>1]u'v'\<close>
          AOT_hence 0: \<open>[R\<^sub>1]av'\<close>
            using u'_eq_a by (meson "rule=E" "&E"(2))
          AOT_have 1: \<open>[\<guillemotleft>?R\<guillemotright>]av'\<close>
            by (rule "rule=E"[rotated, OF R\<^sub>1_def]) (fact 0)
          AOT_have \<open>(a \<noteq>\<^sub>E u & v' \<noteq>\<^sub>E v & [R]av') \<or>
                    (a =\<^sub>E a & v' =\<^sub>E b) \<or>
                    (a =\<^sub>E u & v' =\<^sub>E v)\<close>
            using "\<beta>\<rightarrow>C"(1)[OF 1] by simp
          moreover {
            AOT_assume 0: \<open>a \<noteq>\<^sub>E u & v' \<noteq>\<^sub>E v & [R]av'\<close>
            AOT_have \<open>\<exists>!v ([G]v & [R]u'v)\<close>
              using A[THEN "Ordinary.\<forall>E", THEN "\<rightarrow>E", OF fu'].
            AOT_hence \<open>\<exists>!v ([G]v & [R]av)\<close>
              using u'_eq_a "rule=E" by fast
            AOT_hence \<open>\<exists>v ([G]v & [R]av & \<forall>t ([G]t & [R]at \<rightarrow> t =\<^sub>E v))\<close>
              using "equi:1"[THEN "\<equiv>E"(1)] by fast
            then AOT_obtain s where
              s_prop: \<open>[G]s & [R]as & \<forall>t ([G]t & [R]at \<rightarrow> t =\<^sub>E s)\<close>
              using "Ordinary.\<exists>E"[rotated] by meson
            AOT_have \<open>v' =\<^sub>E s\<close>
              using s_prop[THEN "&E"(2), THEN "Ordinary.\<forall>E"]
                    gv'_R1u'v'[THEN "&E"(1)] 0[THEN "&E"(2)]
              by (metis "&I" "vdash-properties:10")
            moreover AOT_have \<open>v =\<^sub>E s\<close>
              using s_prop[THEN "&E"(2), THEN "Ordinary.\<forall>E"] gv Rav
              by (metis "&I" "\<rightarrow>E")
            ultimately AOT_have \<open>v' =\<^sub>E v\<close>
              by (metis "&I" "ord=Eequiv:2" "ord=Eequiv:3" "\<rightarrow>E")
            moreover AOT_have \<open>\<not>(v' =\<^sub>E v)\<close>
              using 0[THEN "&E"(1), THEN "&E"(2)]
              by (metis "\<equiv>E"(1) "thm-neg=E") 
            ultimately AOT_have \<open>v' =\<^sub>E b\<close>
              by (metis "raa-cor:3")
          }
          moreover {
            AOT_assume \<open>a =\<^sub>E u & v' =\<^sub>E v\<close>
            AOT_hence \<open>v' =\<^sub>E b\<close>
              by (metis "&E"(1) not_a_eq_u "reductio-aa:1")
          }
          ultimately AOT_show \<open>v' =\<^sub>E b\<close>
            by (metis "&E"(2) "\<or>E"(3) "reductio-aa:1") 
        qed
      }
      ultimately AOT_show \<open>\<exists>!v ([G]v & [R\<^sub>1]u'v)\<close>
        by (metis "raa-cor:1")
    next
      fix v'
      AOT_assume gv': \<open>[G]v'\<close>
      {
        AOT_assume not_v'_eq_v: \<open>\<not>(v' =\<^sub>E v)\<close>
               and not_v'_eq_b: \<open>\<not>(v' =\<^sub>E b)\<close>
        AOT_hence v'_noteq_v: \<open>v' \<noteq>\<^sub>E v\<close>
              and v'_noteq_b: \<open>v' \<noteq>\<^sub>E b\<close>
          by (metis "\<equiv>E"(2) "thm-neg=E")+
        AOT_have \<open>\<exists>!u ([F]u & [R]uv')\<close>
          using B[THEN "Ordinary.\<forall>E", THEN "\<rightarrow>E", OF gv'].
        AOT_hence \<open>\<exists>u ([F]u & [R]uv' & \<forall>t ([F]t & [R]tv' \<rightarrow> t =\<^sub>E u))\<close>
          using "equi:1"[THEN "\<equiv>E"(1)] by simp
        then AOT_obtain u' where
          u'_prop: \<open>[F]u' & [R]u'v' & \<forall>t ([F]t & [R]tv' \<rightarrow> t =\<^sub>E u')\<close>
          using "Ordinary.\<exists>E"[rotated] by meson
        AOT_hence fu': \<open>[F]u'\<close> and Ru'v': \<open>[R]u'v'\<close>
          using "&E" by blast+
        AOT_have not_u'_eq_u: \<open>\<not>u' =\<^sub>E u\<close>
        proof (rule "raa-cor:2")
          AOT_assume \<open>u' =\<^sub>E u\<close>
          AOT_hence \<open>u' = u\<close>
            by (metis "=E-simple:2" "\<rightarrow>E")
          AOT_hence Ruv': \<open>[R]uv'\<close>
            using "rule=E" Ru'v' by fast
          AOT_have \<open>v' =\<^sub>E b\<close>
            using b_unique[OF Ordinary.\<psi>, OF gv', OF Ruv'].
          AOT_thus \<open>v' =\<^sub>E b & \<not>v' =\<^sub>E b\<close>
            using not_v'_eq_b "&I" by blast
        qed
        AOT_hence u'_noteq_u: \<open>u' \<noteq>\<^sub>E u\<close>
          using "\<equiv>E"(2) "thm-neg=E" by blast
        AOT_have \<open>\<forall>t ([F]t & [R]tv' \<rightarrow> t =\<^sub>E u')\<close>
          using u'_prop "&E" by blast
        AOT_hence \<open>[F]t & [R]tv' \<rightarrow> t =\<^sub>E u'\<close> for t
          using "Ordinary.\<forall>E" by meson
        AOT_hence u'_unique: \<open>t =\<^sub>E u'\<close> if \<open>[F]t\<close> and \<open>[R]tv'\<close> for t
          by (metis "&I" that "\<rightarrow>E")

        AOT_have \<open>[F]u' & [R\<^sub>1]u'v' & \<forall>t ([F]t & [R\<^sub>1]tv' \<rightarrow> t =\<^sub>E u')\<close>
        proof (safe intro!: "&I" gv' R\<^sub>1xy Ru'v' u'_noteq_u Ordinary.GEN "\<rightarrow>I"
                            "thm-neg=E"[THEN "\<equiv>E"(2)] not_v'_eq_v fu')
          fix t
          AOT_assume 1: \<open>[F]t & [R\<^sub>1]tv'\<close>
          AOT_have \<open>[R]tv'\<close>
            using Rxy2[OF 1[THEN "&E"(2)], OF v'_noteq_v, OF v'_noteq_b].
          AOT_thus \<open>t =\<^sub>E u'\<close>
            using u'_unique 1[THEN "&E"(1)] by blast
        qed
        AOT_hence \<open>\<exists>u ([F]u & [R\<^sub>1]uv' & \<forall>t ([F]t & [R\<^sub>1]tv' \<rightarrow> t =\<^sub>E u))\<close>
          by (rule "Ordinary.\<exists>I")
        AOT_hence \<open>\<exists>!u ([F]u & [R\<^sub>1]uv')\<close>
          by (rule "equi:1"[THEN "\<equiv>E"(2)])
      }
      moreover {
        AOT_assume 0: \<open>v' =\<^sub>E v\<close>
        AOT_hence u'_eq_u: \<open>v' = v\<close>
          using "=E-simple:2" "\<rightarrow>E" by blast
        AOT_have \<open>\<exists>!u ([F]u & [R\<^sub>1]uv')\<close>
        proof (safe intro!: "equi:1"[THEN "\<equiv>E"(2)] "Ordinary.\<exists>I"[where \<beta>=u]
                            "&I" Ordinary.GEN "\<rightarrow>I" fu)
          AOT_show \<open>[R\<^sub>1]uv'\<close>
            by (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
               (safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" prod_denotesI Ordinary.\<psi>
                             "\<or>I"(2) 0 "ord=Eequiv:1"[THEN "\<rightarrow>E"])
        next
          fix u'
          AOT_assume \<open>[F]u' & [R\<^sub>1]u'v'\<close>
          AOT_hence 0: \<open>[R\<^sub>1]u'v\<close>
            using "rule=E"[rotated, OF u'_eq_u] "&E"(2) by fast
          AOT_have 1: \<open>[\<guillemotleft>?R\<guillemotright>]u'v\<close>
            by (rule "rule=E"[rotated, OF R\<^sub>1_def]) (fact 0)
          AOT_have 2: \<open>(u' \<noteq>\<^sub>E u & v \<noteq>\<^sub>E v & [R]u'v) \<or>
                       (u' =\<^sub>E a & v =\<^sub>E b) \<or>
                       (u' =\<^sub>E u & v =\<^sub>E v)\<close>
            using "\<beta>\<rightarrow>C"(1)[OF 1, simplified] by simp
          AOT_have \<open>\<not>v \<noteq>\<^sub>E v\<close>
            using "\<equiv>E"(4) "modus-tollens:1" "ord=Eequiv:1" Ordinary.\<psi>
                  "reductio-aa:2" "thm-neg=E" by blast
          AOT_hence \<open>\<not>((u' \<noteq>\<^sub>E u & v \<noteq>\<^sub>E v & [R]u'v) \<or> (u' =\<^sub>E a & v =\<^sub>E b))\<close>
            by (metis "&E"(1) "&E"(2) "\<or>E"(3) not_v_eq_b "raa-cor:3")
          AOT_hence \<open>(u' =\<^sub>E u & v =\<^sub>E v)\<close>
            using 2 by (metis "\<or>E"(2))
          AOT_thus \<open>u' =\<^sub>E u\<close>
            using "&E" by blast
        qed
      }
      moreover {
        AOT_assume 0: \<open>v' =\<^sub>E b\<close>
        AOT_hence v'_eq_b: \<open>v' = b\<close>
          using "=E-simple:2" "\<rightarrow>E" by blast
        AOT_have \<open>\<exists>!u ([F]u & [R\<^sub>1]uv')\<close>
        proof (safe intro!: "equi:1"[THEN "\<equiv>E"(2)] "\<exists>I"(2)[where \<beta>=a] "&I"
                            Ordinary.GEN "\<rightarrow>I" b_prop[THEN "&E"(1)] Oa fa
                            b_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(1)])
          AOT_show \<open>[R\<^sub>1]av'\<close>
            apply (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
            apply (safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" prod_denotesI)
            apply (rule "\<or>I"(1); rule "\<or>I"(2); rule "&I")
            using Oa "ord=Eequiv:1" "\<rightarrow>E" apply blast
            using "0" by blast
        next
          fix u'
          AOT_assume fu'_R1u'v': \<open>[F]u' & [R\<^sub>1]u'v'\<close>
          AOT_hence 0: \<open>[R\<^sub>1]u'b\<close>
            using v'_eq_b by (meson "rule=E" "&E"(2))
          AOT_have 1: \<open>[\<guillemotleft>?R\<guillemotright>]u'b\<close>
            by (rule "rule=E"[rotated, OF R\<^sub>1_def]) (fact 0)
          AOT_have \<open>(u' \<noteq>\<^sub>E u & b \<noteq>\<^sub>E v & [R]u'b) \<or>
                    (u' =\<^sub>E a & b =\<^sub>E b) \<or>
                    (u' =\<^sub>E u & b =\<^sub>E v)\<close>
            using "\<beta>\<rightarrow>C"(1)[OF 1, simplified] by simp
          moreover {
            AOT_assume 0: \<open>u' \<noteq>\<^sub>E u & b \<noteq>\<^sub>E v & [R]u'b\<close>
            AOT_have \<open>\<exists>!u ([F]u & [R]uv')\<close>
              using B[THEN "Ordinary.\<forall>E", THEN "\<rightarrow>E", OF gv'].
            AOT_hence \<open>\<exists>!u ([F]u & [R]ub)\<close>
              using v'_eq_b "rule=E" by fast
            AOT_hence \<open>\<exists>u ([F]u & [R]ub & \<forall>t ([F]t & [R]tb \<rightarrow> t =\<^sub>E u))\<close>
              using "equi:1"[THEN "\<equiv>E"(1)] by fast
            then AOT_obtain s where
              s_prop: \<open>[F]s & [R]sb & \<forall>t ([F]t & [R]tb \<rightarrow> t =\<^sub>E s)\<close>
              using "Ordinary.\<exists>E"[rotated] by meson
            AOT_have \<open>u' =\<^sub>E s\<close>
              using s_prop[THEN "&E"(2), THEN "Ordinary.\<forall>E"]
                    fu'_R1u'v'[THEN "&E"(1)] 0[THEN "&E"(2)]
              by (metis "&I" "\<rightarrow>E")
            moreover AOT_have \<open>u =\<^sub>E s\<close>
              using s_prop[THEN "&E"(2), THEN "Ordinary.\<forall>E"] fu Rub
              by (metis "&I" "\<rightarrow>E")
            ultimately AOT_have \<open>u' =\<^sub>E u\<close>
              by (metis "&I" "ord=Eequiv:2" "ord=Eequiv:3" "\<rightarrow>E")
            moreover AOT_have \<open>\<not>(u' =\<^sub>E u)\<close>
              using 0[THEN "&E"(1), THEN "&E"(1)] by (metis "\<equiv>E"(1) "thm-neg=E") 
            ultimately AOT_have \<open>u' =\<^sub>E a\<close>
              by (metis "raa-cor:3")
          }
          moreover {
            AOT_assume \<open>u' =\<^sub>E u & b =\<^sub>E v\<close>
            AOT_hence \<open>u' =\<^sub>E a\<close>
              by (metis "&E"(2) not_b_eq_v "reductio-aa:1")
          }
          ultimately AOT_show \<open>u' =\<^sub>E a\<close>
            by (metis "&E"(1) "\<or>E"(3) "reductio-aa:1") 
        qed
      }
      ultimately AOT_show \<open>\<exists>!u ([F]u & [R\<^sub>1]uv')\<close>
        by (metis "raa-cor:1")
    qed
    ultimately AOT_have \<open>\<exists>R R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E [G]\<^sup>-\<^sup>v\<close>
      using 1 by blast
  }
  ultimately AOT_have \<open>\<exists>R R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E [G]\<^sup>-\<^sup>v\<close>
    using R_prop by (metis "reductio-aa:2") 
  AOT_thus \<open>[F]\<^sup>-\<^sup>u \<approx>\<^sub>E [G]\<^sup>-\<^sup>v\<close>
    by (rule "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
qed


AOT_theorem "P'-eq": \<open>[F]\<^sup>-\<^sup>u \<approx>\<^sub>E [G]\<^sup>-\<^sup>v & [F]u & [G]v \<rightarrow> F \<approx>\<^sub>E G\<close>
proof(safe intro!: "\<rightarrow>I"; frule "&E"(1); drule "&E"(2);
      frule "&E"(1); drule "&E"(2))
  AOT_have \<open>[\<lambda>z [\<Pi>]z & z \<noteq>\<^sub>E \<kappa>]\<down>\<close> for \<Pi> \<kappa> by "cqt:2[lambda]"
  note \<Pi>_minus_\<kappa>I = "rule-id-df:2:b[2]"[
      where \<tau>=\<open>(\<lambda>(\<Pi>, \<kappa>). \<guillemotleft>[\<Pi>]\<^sup>-\<^sup>\<kappa>\<guillemotright>)\<close>, simplified, OF "F-u", simplified, OF this]
   and \<Pi>_minus_\<kappa>E = "rule-id-df:2:a[2]"[
   where \<tau>=\<open>(\<lambda>(\<Pi>, \<kappa>). \<guillemotleft>[\<Pi>]\<^sup>-\<^sup>\<kappa>\<guillemotright>)\<close>, simplified, OF "F-u", simplified, OF this]
  AOT_have \<Pi>_minus_\<kappa>_den: \<open>[\<Pi>]\<^sup>-\<^sup>\<kappa>\<down>\<close> for \<Pi> \<kappa>
    by (rule \<Pi>_minus_\<kappa>I) "cqt:2[lambda]"+

  AOT_have \<Pi>_minus_\<kappa>E1: \<open>[\<Pi>]\<kappa>'\<close>
       and \<Pi>_minus_\<kappa>E2: \<open>\<kappa>' \<noteq>\<^sub>E \<kappa>\<close> if \<open>[[\<Pi>]\<^sup>-\<^sup>\<kappa>]\<kappa>'\<close> for \<Pi> \<kappa> \<kappa>'
  proof -
    AOT_have \<open>[\<lambda>z [\<Pi>]z & z \<noteq>\<^sub>E \<kappa>]\<kappa>'\<close>
      using \<Pi>_minus_\<kappa>E that by fast
    AOT_hence \<open>[\<Pi>]\<kappa>' & \<kappa>' \<noteq>\<^sub>E \<kappa>\<close>
      by (rule "\<beta>\<rightarrow>C"(1))
    AOT_thus \<open>[\<Pi>]\<kappa>'\<close> and \<open>\<kappa>' \<noteq>\<^sub>E \<kappa>\<close>
      using "&E" by blast+
  qed
  AOT_have \<Pi>_minus_\<kappa>I': \<open>[[\<Pi>]\<^sup>-\<^sup>\<kappa>]\<kappa>'\<close> if \<open>[\<Pi>]\<kappa>'\<close> and \<open>\<kappa>' \<noteq>\<^sub>E \<kappa>\<close> for \<Pi> \<kappa> \<kappa>'
  proof -
    AOT_have \<kappa>'_den: \<open>\<kappa>'\<down>\<close>
      by (metis "russell-axiom[exe,1].\<psi>_denotes_asm" that(1))
    AOT_have \<open>[\<lambda>z [\<Pi>]z & z \<noteq>\<^sub>E \<kappa>]\<kappa>'\<close>
      by (safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" \<kappa>'_den "&I" that)
    AOT_thus \<open>[[\<Pi>]\<^sup>-\<^sup>\<kappa>]\<kappa>'\<close>
      using \<Pi>_minus_\<kappa>I by fast
  qed

  AOT_assume Gv: \<open>[G]v\<close>
  AOT_assume Fu: \<open>[F]u\<close>
  AOT_assume \<open>[F]\<^sup>-\<^sup>u \<approx>\<^sub>E [G]\<^sup>-\<^sup>v\<close>
  AOT_hence \<open>\<exists>R R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E [G]\<^sup>-\<^sup>v\<close>
    using "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain R where R_prop: \<open>R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E [G]\<^sup>-\<^sup>v\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence Fact1: \<open>\<forall>r([[F]\<^sup>-\<^sup>u]r \<rightarrow> \<exists>!s ([[G]\<^sup>-\<^sup>v]s & [R]rs))\<close>
        and Fact1': \<open>\<forall>s([[G]\<^sup>-\<^sup>v]s \<rightarrow> \<exists>!r ([[F]\<^sup>-\<^sup>u]r & [R]rs))\<close>
    using "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_have \<open>R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE [G]\<^sup>-\<^sup>v\<close>
    using "equi-rem-thm"[unvarify F G, OF \<Pi>_minus_\<kappa>_den, OF \<Pi>_minus_\<kappa>_den,
                         THEN "\<equiv>E"(1), OF R_prop].
  AOT_hence \<open>R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>E [G]\<^sup>-\<^sup>v & R |: [F]\<^sup>-\<^sup>u \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE [G]\<^sup>-\<^sup>v\<close>
    using "equi-rem:4"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_hence Fact2:
    \<open>\<forall>r\<forall>s\<forall>t(([[F]\<^sup>-\<^sup>u]r & [[F]\<^sup>-\<^sup>u]s & [[G]\<^sup>-\<^sup>v]t) \<rightarrow> ([R]rt & [R]st \<rightarrow> r =\<^sub>E s))\<close>
    using "equi-rem:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast

  let ?R = \<open>\<guillemotleft>[\<lambda>xy ([[F]\<^sup>-\<^sup>u]x & [[G]\<^sup>-\<^sup>v]y & [R]xy) \<or> (x =\<^sub>E u & y =\<^sub>E v)]\<guillemotright>\<close>
  AOT_have R_den: \<open>\<guillemotleft>?R\<guillemotright>\<down>\<close> by "cqt:2[lambda]"

  AOT_show \<open>F \<approx>\<^sub>E G\<close>
  proof(safe intro!: "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(1)[where \<tau>="?R"] R_den
                     "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" Ordinary.GEN "\<rightarrow>I")
    fix r
    AOT_assume Fr: \<open>[F]r\<close>
    {
      AOT_assume not_r_eq_u: \<open>\<not>(r =\<^sub>E u)\<close>
      AOT_hence r_noteq_u: \<open>r \<noteq>\<^sub>E u\<close>
        using "\<equiv>E"(2) "thm-neg=E" by blast
      AOT_have \<open>[[F]\<^sup>-\<^sup>u]r\<close>
        by(rule \<Pi>_minus_\<kappa>I; safe intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" Fr r_noteq_u)
      AOT_hence \<open>\<exists>!s ([[G]\<^sup>-\<^sup>v]s & [R]rs)\<close>
        using Fact1[THEN "\<forall>E"(2)] "\<rightarrow>E" Ordinary.\<psi> by blast
      AOT_hence \<open>\<exists>s ([[G]\<^sup>-\<^sup>v]s & [R]rs & \<forall>t ([[G]\<^sup>-\<^sup>v]t & [R]rt \<rightarrow> t =\<^sub>E s))\<close>
        using "equi:1"[THEN "\<equiv>E"(1)] by simp
      then AOT_obtain s where s_prop: \<open>[[G]\<^sup>-\<^sup>v]s & [R]rs & \<forall>t ([[G]\<^sup>-\<^sup>v]t & [R]rt \<rightarrow> t =\<^sub>E s)\<close>
        using "Ordinary.\<exists>E"[rotated] by meson
      AOT_hence G_minus_v_s: \<open>[[G]\<^sup>-\<^sup>v]s\<close> and Rrs: \<open>[R]rs\<close>
        using "&E" by blast+
      AOT_have s_unique: \<open>t =\<^sub>E s\<close> if \<open>[[G]\<^sup>-\<^sup>v]t\<close> and \<open>[R]rt\<close> for t
        using s_prop[THEN "&E"(2), THEN "Ordinary.\<forall>E", THEN "\<rightarrow>E", OF "&I", OF that].
      AOT_have Gs: \<open>[G]s\<close>
        using \<Pi>_minus_\<kappa>E1[OF G_minus_v_s].
      AOT_have s_noteq_v: \<open>s \<noteq>\<^sub>E v\<close>
        using \<Pi>_minus_\<kappa>E2[OF G_minus_v_s].
      AOT_have \<open>\<exists>s ([G]s & [\<guillemotleft>?R\<guillemotright>]rs & (\<forall>t ([G]t & [\<guillemotleft>?R\<guillemotright>]rt \<rightarrow> t =\<^sub>E s)))\<close>
      proof(safe intro!: "Ordinary.\<exists>I"[where \<beta>=s] "&I" Gs Ordinary.GEN "\<rightarrow>I")
        AOT_show \<open>[\<guillemotleft>?R\<guillemotright>]rs\<close>
          by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" "\<or>I"(1) \<Pi>_minus_\<kappa>I' Fr Gs
                           s_noteq_v Rrs r_noteq_u
                   simp: "&I" "ex:1:a" prod_denotesI "rule-ui:3")
      next
        fix t
        AOT_assume 0: \<open>[G]t & [\<guillemotleft>?R\<guillemotright>]rt\<close>
        AOT_hence \<open>([[F]\<^sup>-\<^sup>u]r & [[G]\<^sup>-\<^sup>v]t & [R]rt) \<or> (r =\<^sub>E u & t =\<^sub>E v)\<close>
          using "\<beta>\<rightarrow>C"(1)[OF 0[THEN "&E"(2)], simplified] by blast
        AOT_hence 1: \<open>[[F]\<^sup>-\<^sup>u]r & [[G]\<^sup>-\<^sup>v]t & [R]rt\<close>
          using not_r_eq_u by (metis "&E"(1) "\<or>E"(3) "reductio-aa:1")
        AOT_show \<open>t =\<^sub>E s\<close> using s_unique 1 "&E" by blast
      qed
    }
    moreover {
      AOT_assume r_eq_u: \<open>r =\<^sub>E u\<close>
      AOT_have \<open>\<exists>s ([G]s & [\<guillemotleft>?R\<guillemotright>]rs & (\<forall>t ([G]t & [\<guillemotleft>?R\<guillemotright>]rt \<rightarrow> t =\<^sub>E s)))\<close>
      proof(safe intro!: "Ordinary.\<exists>I"[where \<beta>=v] "&I" Gv Ordinary.GEN "\<rightarrow>I")
        AOT_show \<open>[\<guillemotleft>?R\<guillemotright>]rv\<close>
          by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" "\<or>I"(2) \<Pi>_minus_\<kappa>I' Fr r_eq_u
                           "ord=Eequiv:1"[THEN "\<rightarrow>E"] Ordinary.\<psi>
                   simp: "&I" "ex:1:a" prod_denotesI "rule-ui:3")
      next
        fix t
        AOT_assume 0: \<open>[G]t & [\<guillemotleft>?R\<guillemotright>]rt\<close>
        AOT_hence \<open>([[F]\<^sup>-\<^sup>u]r & [[G]\<^sup>-\<^sup>v]t & [R]rt) \<or> (r =\<^sub>E u & t =\<^sub>E v)\<close>
          using "\<beta>\<rightarrow>C"(1)[OF 0[THEN "&E"(2)], simplified] by blast
        AOT_hence \<open>r =\<^sub>E u & t =\<^sub>E v\<close>
          using r_eq_u \<Pi>_minus_\<kappa>E2
          by (metis "&E"(1) "\<or>E"(2) "\<equiv>E"(1) "reductio-aa:1" "thm-neg=E")
        AOT_thus \<open>t =\<^sub>E v\<close> using "&E" by blast
      qed
    }
    ultimately AOT_show \<open>\<exists>!s ([G]s & [\<guillemotleft>?R\<guillemotright>]rs)\<close>
      using "reductio-aa:2" "equi:1"[THEN "\<equiv>E"(2)] by fast
  next
    fix s
    AOT_assume Gs: \<open>[G]s\<close>

    {
      AOT_assume not_s_eq_v: \<open>\<not>(s =\<^sub>E v)\<close>
      AOT_hence s_noteq_v: \<open>s \<noteq>\<^sub>E v\<close>
        using "\<equiv>E"(2) "thm-neg=E" by blast
      AOT_have \<open>[[G]\<^sup>-\<^sup>v]s\<close>
        by (rule \<Pi>_minus_\<kappa>I; auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" Gs s_noteq_v)
      AOT_hence \<open>\<exists>!r ([[F]\<^sup>-\<^sup>u]r & [R]rs)\<close>
        using Fact1'[THEN "Ordinary.\<forall>E"] "\<rightarrow>E" by blast
      AOT_hence \<open>\<exists>r ([[F]\<^sup>-\<^sup>u]r & [R]rs & \<forall>t ([[F]\<^sup>-\<^sup>u]t & [R]ts \<rightarrow> t =\<^sub>E r))\<close>
        using "equi:1"[THEN "\<equiv>E"(1)] by simp
      then AOT_obtain r where
        r_prop: \<open>[[F]\<^sup>-\<^sup>u]r & [R]rs & \<forall>t ([[F]\<^sup>-\<^sup>u]t & [R]ts \<rightarrow> t =\<^sub>E r)\<close>
        using "Ordinary.\<exists>E"[rotated] by meson
      AOT_hence F_minus_u_r: \<open>[[F]\<^sup>-\<^sup>u]r\<close> and Rrs: \<open>[R]rs\<close>
        using "&E" by blast+
      AOT_have r_unique: \<open>t =\<^sub>E r\<close> if \<open>[[F]\<^sup>-\<^sup>u]t\<close> and \<open>[R]ts\<close> for t
        using r_prop[THEN "&E"(2), THEN "Ordinary.\<forall>E",
                     THEN "\<rightarrow>E", OF "&I", OF that].
      AOT_have Fr: \<open>[F]r\<close>
        using \<Pi>_minus_\<kappa>E1[OF F_minus_u_r].
      AOT_have r_noteq_u: \<open>r \<noteq>\<^sub>E u\<close>
        using \<Pi>_minus_\<kappa>E2[OF F_minus_u_r].
      AOT_have \<open>\<exists>r ([F]r & [\<guillemotleft>?R\<guillemotright>]rs & (\<forall>t ([F]t & [\<guillemotleft>?R\<guillemotright>]ts \<rightarrow> t =\<^sub>E r)))\<close>
      proof(safe intro!: "Ordinary.\<exists>I"[where \<beta>=r] "&I" Fr Ordinary.GEN "\<rightarrow>I")
        AOT_show \<open>[\<guillemotleft>?R\<guillemotright>]rs\<close>
          by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" "\<or>I"(1) \<Pi>_minus_\<kappa>I' Fr
                           Gs s_noteq_v Rrs r_noteq_u
                   simp: "&I" "ex:1:a" prod_denotesI "rule-ui:3")
      next
        fix t
        AOT_assume 0: \<open>[F]t & [\<guillemotleft>?R\<guillemotright>]ts\<close>
        AOT_hence \<open>([[F]\<^sup>-\<^sup>u]t & [[G]\<^sup>-\<^sup>v]s & [R]ts) \<or> (t =\<^sub>E u & s =\<^sub>E v)\<close>
          using "\<beta>\<rightarrow>C"(1)[OF 0[THEN "&E"(2)], simplified] by blast
        AOT_hence 1: \<open>[[F]\<^sup>-\<^sup>u]t & [[G]\<^sup>-\<^sup>v]s & [R]ts\<close>
          using not_s_eq_v by (metis "&E"(2) "\<or>E"(3) "reductio-aa:1")
        AOT_show \<open>t =\<^sub>E r\<close> using r_unique 1 "&E" by blast
      qed
    }
    moreover {
      AOT_assume s_eq_v: \<open>s =\<^sub>E v\<close>
      AOT_have \<open>\<exists>r ([F]r & [\<guillemotleft>?R\<guillemotright>]rs & (\<forall>t ([F]t & [\<guillemotleft>?R\<guillemotright>]ts \<rightarrow> t =\<^sub>E r)))\<close>
      proof(safe intro!: "Ordinary.\<exists>I"[where \<beta>=u] "&I" Fu Ordinary.GEN "\<rightarrow>I")
        AOT_show \<open>[\<guillemotleft>?R\<guillemotright>]us\<close>
          by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" prod_denotesI "\<or>I"(2)
                            \<Pi>_minus_\<kappa>I' Gs s_eq_v Ordinary.\<psi>
                            "ord=Eequiv:1"[THEN "\<rightarrow>E"])
      next
        fix t
        AOT_assume 0: \<open>[F]t & [\<guillemotleft>?R\<guillemotright>]ts\<close>
        AOT_hence 1: \<open>([[F]\<^sup>-\<^sup>u]t & [[G]\<^sup>-\<^sup>v]s & [R]ts) \<or> (t =\<^sub>E u & s =\<^sub>E v)\<close>
          using "\<beta>\<rightarrow>C"(1)[OF 0[THEN "&E"(2)], simplified] by blast
        moreover AOT_have \<open>\<not>([[F]\<^sup>-\<^sup>u]t & [[G]\<^sup>-\<^sup>v]s & [R]ts)\<close>
        proof (rule "raa-cor:2")
          AOT_assume \<open>([[F]\<^sup>-\<^sup>u]t & [[G]\<^sup>-\<^sup>v]s & [R]ts)\<close>
          AOT_hence \<open>[[G]\<^sup>-\<^sup>v]s\<close> using "&E" by blast
          AOT_thus \<open>s =\<^sub>E v & \<not>(s =\<^sub>E v)\<close>
            by (metis \<Pi>_minus_\<kappa>E2 "\<equiv>E"(4) "reductio-aa:1" s_eq_v "thm-neg=E")
        qed
        ultimately AOT_have \<open>t =\<^sub>E u & s =\<^sub>E v\<close>
          by (metis "\<or>E"(2))
        AOT_thus \<open>t =\<^sub>E u\<close> using "&E" by blast
      qed
    }
    ultimately AOT_show \<open>\<exists>!r ([F]r & [\<guillemotleft>?R\<guillemotright>]rs)\<close>
      using "\<equiv>E"(2) "equi:1" "reductio-aa:2" by fast
  qed
qed


AOT_theorem "approx-cont:1": \<open>\<exists>F\<exists>G \<diamond>(F \<approx>\<^sub>E G & \<diamond>\<not>F \<approx>\<^sub>E G)\<close>
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
    AOT_have \<open>\<diamond>[L]\<^sup>- \<approx>\<^sub>E [\<guillemotleft>?P\<guillemotright>] & \<diamond>\<not>[L]\<^sup>- \<approx>\<^sub>E [\<guillemotleft>?P\<guillemotright>]\<close>
    proof (rule "&I"; rule "RM\<diamond>"[THEN "\<rightarrow>E"]; (rule "\<rightarrow>I")?)
      AOT_modally_strict {
        AOT_assume A: \<open>\<not>\<exists>x [\<guillemotleft>?P\<guillemotright>]x\<close>
        AOT_show \<open>[L]\<^sup>- \<approx>\<^sub>E [\<guillemotleft>?P\<guillemotright>]\<close>
        proof (safe intro!: "empty-approx:1"[unvarify F H, THEN "\<rightarrow>E"]
                            "rel-neg-T:3" "&I")
          AOT_show \<open>[\<guillemotleft>?P\<guillemotright>]\<down>\<close> by "cqt:2[lambda]"
        next
          AOT_show \<open>\<not>\<exists>u [L\<^sup>-]u\<close>
          proof (rule "raa-cor:2")
            AOT_assume \<open>\<exists>u [L\<^sup>-]u\<close>
            then AOT_obtain u where \<open>[L\<^sup>-]u\<close>
              using "Ordinary.\<exists>E"[rotated] by blast
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
              using "Ordinary.\<exists>E"[rotated] by blast
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
        AOT_have B: \<open>\<not>[\<guillemotleft>?P\<guillemotright>] \<approx>\<^sub>E [L]\<^sup>-\<close>
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
          AOT_hence \<open>O!x & [\<guillemotleft>?P\<guillemotright>]x\<close>
            using Px "&I" by blast
          AOT_thus \<open>\<exists>u [\<guillemotleft>?P\<guillemotright>]u\<close>
            by (rule "\<exists>I")
        next
          AOT_show \<open>\<not>\<exists>u [L\<^sup>-]u\<close>
          proof (rule "raa-cor:2")
            AOT_assume \<open>\<exists>u [L\<^sup>-]u\<close>
            then AOT_obtain u where \<open>[L\<^sup>-]u\<close>
              using "Ordinary.\<exists>E"[rotated] by blast
            moreover AOT_have \<open>\<not>[L\<^sup>-]u\<close>
              using "thm-noncont-e-e:2"[THEN "contingent-properties:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"]]
              by (metis "qml:2"[axiom_inst] "rule-ui:3" "\<rightarrow>E" "&E"(2))
            ultimately AOT_show \<open>p & \<not>p\<close> for p
              by (metis "raa-cor:3")
          qed
        qed
        AOT_show \<open>\<not>[L]\<^sup>- \<approx>\<^sub>E [\<guillemotleft>?P\<guillemotright>]\<close>
        proof (rule "raa-cor:2")
          AOT_assume \<open>[L]\<^sup>- \<approx>\<^sub>E [\<guillemotleft>?P\<guillemotright>]\<close>
          AOT_hence \<open>[\<guillemotleft>?P\<guillemotright>] \<approx>\<^sub>E [L]\<^sup>-\<close>
            apply (rule "eq-part:2"[unvarify F G, THEN "\<rightarrow>E", rotated 2])
             apply "cqt:2[lambda]"
            by (simp add: "rel-neg-T:3")
          AOT_thus \<open>[\<guillemotleft>?P\<guillemotright>] \<approx>\<^sub>E [L]\<^sup>- & \<not>[\<guillemotleft>?P\<guillemotright>] \<approx>\<^sub>E [L]\<^sup>-\<close>
            using B "&I" by blast
        qed
      }
    next
      AOT_show \<open>\<diamond>\<exists>x [\<guillemotleft>?P\<guillemotright>]x\<close>
        using \<theta> "&E" by blast
    qed
    AOT_thus \<open>\<diamond>([L]\<^sup>- \<approx>\<^sub>E [\<guillemotleft>?P\<guillemotright>] & \<diamond>\<not>[L]\<^sup>- \<approx>\<^sub>E [\<guillemotleft>?P\<guillemotright>])\<close>
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
  \<open>\<exists>F\<exists>G \<diamond>([\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G & \<diamond>\<not>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close>
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
    AOT_have \<open>\<diamond>[\<lambda>z \<^bold>\<A>[L\<^sup>-]z] \<approx>\<^sub>E [\<guillemotleft>?P\<guillemotright>] & \<diamond>\<not>[\<lambda>z \<^bold>\<A>[L\<^sup>-]z] \<approx>\<^sub>E [\<guillemotleft>?P\<guillemotright>]\<close>
    proof (rule "&I"; rule "RM\<diamond>"[THEN "\<rightarrow>E"]; (rule "\<rightarrow>I")?)
      AOT_modally_strict {
        AOT_assume A: \<open>\<not>\<exists>x [\<guillemotleft>?P\<guillemotright>]x\<close>
        AOT_show \<open>[\<lambda>z \<^bold>\<A>[L\<^sup>-]z] \<approx>\<^sub>E [\<guillemotleft>?P\<guillemotright>]\<close>
        proof (safe intro!: "empty-approx:1"[unvarify F H, THEN "\<rightarrow>E"]
                            "rel-neg-T:3" "&I")
          AOT_show \<open>[\<guillemotleft>?P\<guillemotright>]\<down>\<close> by "cqt:2"
        next
          AOT_show \<open>\<not>\<exists>u [\<lambda>z \<^bold>\<A>[L\<^sup>-]z]u\<close>
          proof (rule "raa-cor:2")
            AOT_assume \<open>\<exists>u [\<lambda>z \<^bold>\<A>[L\<^sup>-]z]u\<close>
            then AOT_obtain u where \<open>[\<lambda>z \<^bold>\<A>[L\<^sup>-]z]u\<close>
              using "Ordinary.\<exists>E"[rotated] by blast
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
              using "Ordinary.\<exists>E"[rotated] by blast
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
        AOT_have B: \<open>\<not>[\<guillemotleft>?P\<guillemotright>] \<approx>\<^sub>E [\<lambda>z \<^bold>\<A>[L\<^sup>-]z]\<close>
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
          AOT_hence \<open>O!x & [\<guillemotleft>?P\<guillemotright>]x\<close>
            using Px "&I" by blast
          AOT_thus \<open>\<exists>u [\<guillemotleft>?P\<guillemotright>]u\<close>
            by (rule "\<exists>I")
        next
          AOT_show \<open>\<not>\<exists>u [\<lambda>z \<^bold>\<A>[L\<^sup>-]z]u\<close>
          proof (rule "raa-cor:2")
            AOT_assume \<open>\<exists>u [\<lambda>z \<^bold>\<A>[L\<^sup>-]z]u\<close>
            then AOT_obtain u where \<open>[\<lambda>z \<^bold>\<A>[L\<^sup>-]z]u\<close>
              using "Ordinary.\<exists>E"[rotated] by blast
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
        AOT_show \<open>\<not>[\<lambda>z \<^bold>\<A>[L\<^sup>-]z] \<approx>\<^sub>E [\<guillemotleft>?P\<guillemotright>]\<close>
        proof (rule "raa-cor:2")
          AOT_assume \<open>[\<lambda>z \<^bold>\<A>[L\<^sup>-]z] \<approx>\<^sub>E [\<guillemotleft>?P\<guillemotright>]\<close>
          AOT_hence \<open>[\<guillemotleft>?P\<guillemotright>] \<approx>\<^sub>E [\<lambda>z \<^bold>\<A>[L\<^sup>-]z]\<close>
            by (rule "eq-part:2"[unvarify F G, THEN "\<rightarrow>E", rotated 2])
               "cqt:2"+
          AOT_thus \<open>[\<guillemotleft>?P\<guillemotright>] \<approx>\<^sub>E [\<lambda>z \<^bold>\<A>[L\<^sup>-]z] & \<not>[\<guillemotleft>?P\<guillemotright>] \<approx>\<^sub>E [\<lambda>z \<^bold>\<A>[L\<^sup>-]z]\<close>
            using B "&I" by blast
        qed
      }
    next
      AOT_show \<open>\<diamond>\<exists>x [\<guillemotleft>?P\<guillemotright>]x\<close>
        using \<theta> "&E" by blast
    qed
    AOT_thus \<open>\<diamond>([\<lambda>z \<^bold>\<A>[L\<^sup>-]z] \<approx>\<^sub>E [\<guillemotleft>?P\<guillemotright>] & \<diamond>\<not>[\<lambda>z \<^bold>\<A>[L\<^sup>-]z] \<approx>\<^sub>E [\<guillemotleft>?P\<guillemotright>])\<close>
      using "S5Basic:11" "\<equiv>E"(2) by blast
  next
    AOT_show \<open>[\<lambda>x [E!]x & \<not>\<^bold>\<A>[E!]x]\<down>\<close> by "cqt:2"
  next
    AOT_show \<open>[L]\<^sup>-\<down>\<close>
      by (simp add: "rel-neg-T:3")
  qed
qed

notepad
begin
  text\<open>We already have defined being equivalent on the ordinary objects in the
       Extended Relation Comprehension theory.\<close>
  AOT_have \<open>F \<equiv>\<^sub>E G \<equiv>\<^sub>d\<^sub>f F\<down> & G\<down> & \<forall>u ([F]u \<equiv> [G]u)\<close> for F G
    using eqE by blast
end

AOT_theorem "apE-eqE:1": \<open>F \<equiv>\<^sub>E G \<rightarrow> F \<approx>\<^sub>E G\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>F \<equiv>\<^sub>E G\<close>
  AOT_have \<open>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
  proof (safe intro!: "\<exists>I"(1)[where \<tau>="\<guillemotleft>(=\<^sub>E)\<guillemotright>"] "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I"
                      "=E[denotes]" "cqt:2[const_var]"[axiom_inst] Ordinary.GEN
                      "\<rightarrow>I" "equi:1"[THEN "\<equiv>E"(2)])
    fix u
    AOT_assume Fu: \<open>[F]u\<close>
    AOT_hence Gu: \<open>[G]u\<close>
      using "\<equiv>\<^sub>d\<^sub>fE"[OF eqE, OF 0, THEN "&E"(2),
                   THEN "Ordinary.\<forall>E"[where \<alpha>=u], THEN "\<equiv>E"(1)]
            Ordinary.\<psi> Fu by blast
    AOT_show \<open>\<exists>v ([G]v & u =\<^sub>E v & \<forall>v' ([G]v' & u =\<^sub>E v' \<rightarrow> v' =\<^sub>E v))\<close>
      by (safe intro!: "Ordinary.\<exists>I"[where \<beta>=u] "&I" GEN "\<rightarrow>I" Ordinary.\<psi> Gu
                       "ord=Eequiv:1"[THEN "\<rightarrow>E", OF Ordinary.\<psi>]
                       "ord=Eequiv:2"[THEN "\<rightarrow>E"] dest!: "&E"(2))
  next
    fix v
    AOT_assume Gv: \<open>[G]v\<close>
    AOT_hence Fv: \<open>[F]v\<close>
      using "\<equiv>\<^sub>d\<^sub>fE"[OF eqE, OF 0, THEN "&E"(2),
                   THEN "Ordinary.\<forall>E"[where \<alpha>=v], THEN "\<equiv>E"(2)]
            Ordinary.\<psi> Gv by blast
    AOT_show \<open>\<exists>u ([F]u & u =\<^sub>E v & \<forall>v' ([F]v' & v' =\<^sub>E v \<rightarrow> v' =\<^sub>E u))\<close>
      by (safe intro!: "Ordinary.\<exists>I"[where \<beta>=v] "&I" GEN "\<rightarrow>I" Ordinary.\<psi> Fv
                       "ord=Eequiv:1"[THEN "\<rightarrow>E", OF Ordinary.\<psi>]
                       "ord=Eequiv:2"[THEN "\<rightarrow>E"] dest!: "&E"(2))
  qed
  AOT_thus \<open>F \<approx>\<^sub>E G\<close>
    by (rule "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
qed

AOT_theorem "apE-eqE:2": \<open>(F \<approx>\<^sub>E G & G \<equiv>\<^sub>E H) \<rightarrow> F \<approx>\<^sub>E H\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>F \<approx>\<^sub>E G & G \<equiv>\<^sub>E H\<close>
  AOT_hence \<open>F \<approx>\<^sub>E G\<close> and \<open>G \<approx>\<^sub>E H\<close>
    using "apE-eqE:1"[THEN "\<rightarrow>E"] "&E" by blast+
  AOT_thus \<open>F \<approx>\<^sub>E H\<close>
    by (metis Adjunction "eq-part:3" "vdash-properties:10")
qed


AOT_act_theorem "eq-part-act:1": \<open>[\<lambda>z \<^bold>\<A>[F]z] \<equiv>\<^sub>E F\<close>
proof (safe intro!: eqE[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" Ordinary.GEN "\<rightarrow>I")
  fix u
  AOT_have \<open>[\<lambda>z \<^bold>\<A>[F]z]u \<equiv> \<^bold>\<A>[F]u\<close>
    by (rule "beta-C-meta"[THEN "\<rightarrow>E"]) "cqt:2[lambda]"
  also AOT_have \<open>\<dots> \<equiv> [F]u\<close>
    using "act-conj-act:4" "logic-actual"[act_axiom_inst, THEN "\<rightarrow>E"] by blast
  finally AOT_show \<open>[\<lambda>z \<^bold>\<A>[F]z]u \<equiv> [F]u\<close>.
qed

AOT_act_theorem "eq-part-act:2": \<open>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E F\<close>
  by (safe intro!: "apE-eqE:1"[unvarify F, THEN "\<rightarrow>E"] "eq-part-act:1") "cqt:2"


AOT_theorem "actuallyF:1": \<open>\<^bold>\<A>(F \<approx>\<^sub>E [\<lambda>z \<^bold>\<A>[F]z])\<close>
proof -
  AOT_have 1: \<open>\<^bold>\<A>([F]x \<equiv> \<^bold>\<A>[F]x)\<close> for x
    by (meson "Act-Basic:5" "act-conj-act:4" "\<equiv>E"(2) "Commutativity of \<equiv>")
  AOT_have \<open>\<^bold>\<A>([F]x \<equiv> [\<lambda>z \<^bold>\<A>[F]z]x)\<close> for x
    apply (AOT_subst \<open>[\<lambda>z \<^bold>\<A>[F]z]x\<close> \<open>\<^bold>\<A>[F]x\<close>)
     apply (rule "beta-C-meta"[THEN "\<rightarrow>E"])
     apply "cqt:2[lambda]"
    by (fact 1)
  AOT_hence \<open>O!x \<rightarrow> \<^bold>\<A>([F]x \<equiv> [\<lambda>z \<^bold>\<A>[F]z]x)\<close> for x
    by (metis "\<rightarrow>I") 
  AOT_hence \<open>\<forall>u \<^bold>\<A>([F]u \<equiv> [\<lambda>z \<^bold>\<A>[F]z]u)\<close>
    using "\<forall>I" by fast
  AOT_hence 1: \<open>\<^bold>\<A>\<forall>u ([F]u \<equiv> [\<lambda>z \<^bold>\<A>[F]z]u)\<close>
    by (metis "Ordinary.res-var-bound-reas[2]" "\<rightarrow>E")
  AOT_modally_strict {
    AOT_have \<open>[\<lambda>z \<^bold>\<A>[F]z]\<down>\<close> by "cqt:2"
  } note 2 = this
  AOT_have \<open>\<^bold>\<A>(F \<equiv>\<^sub>E [\<lambda>z \<^bold>\<A>[F]z])\<close>
    apply (AOT_subst \<open>F \<equiv>\<^sub>E [\<lambda>z \<^bold>\<A>[F]z]\<close> \<open>\<forall>u ([F]u \<equiv> [\<lambda>z \<^bold>\<A>[F]z]u)\<close>)
    using eqE[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I",
              OF "cqt:2[const_var]"[axiom_inst], OF 2]
    by (auto simp: 1)
  moreover AOT_have \<open>\<^bold>\<A>(F \<equiv>\<^sub>E [\<lambda>z \<^bold>\<A>[F]z] \<rightarrow> F \<approx>\<^sub>E [\<lambda>z \<^bold>\<A>[F]z])\<close>
    using "apE-eqE:1"[unvarify G, THEN "RA[2]", OF 2] by metis
  ultimately AOT_show \<open>\<^bold>\<A>F \<approx>\<^sub>E [\<lambda>z \<^bold>\<A>[F]z]\<close>
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

AOT_theorem "approx-nec:1": \<open>Rigid(F) \<rightarrow> F \<approx>\<^sub>E [\<lambda>z \<^bold>\<A>[F]z]\<close>
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
  AOT_show \<open>F \<approx>\<^sub>E [\<lambda>z \<^bold>\<A>[F]z]\<close>
  proof (safe intro!: "apE-eqE:1"[unvarify G, THEN "\<rightarrow>E"] eqE[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I"
                      "cqt:2" act_F_den Ordinary.GEN "\<rightarrow>I" "\<equiv>I")
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
  \<open>F \<approx>\<^sub>E G \<equiv> \<forall>H ([\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E F \<equiv> [\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E G)\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume 0: \<open>F \<approx>\<^sub>E G\<close>
  AOT_assume 0: \<open>F \<approx>\<^sub>E G\<close>
  AOT_hence \<open>\<forall>H (H \<approx>\<^sub>E F \<equiv> H \<approx>\<^sub>E G)\<close>
    using "eq-part:4"[THEN "\<equiv>E"(1), OF 0] by blast
  AOT_have \<open>[\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E F \<equiv> [\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E G\<close> for H
    by (rule "\<forall>E"(1)[OF "eq-part:4"[THEN "\<equiv>E"(1), OF 0]]) "cqt:2"
  AOT_thus \<open>\<forall>H ([\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E F \<equiv> [\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E G)\<close>
    by (rule GEN)
next
  AOT_assume 0: \<open>\<forall>H ([\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E F \<equiv> [\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E G)\<close>
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
  AOT_have \<open>H \<equiv>\<^sub>E F\<close>
  proof (safe intro!: eqE[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" Ordinary.GEN "\<rightarrow>I")
    AOT_show \<open>[H]u \<equiv> [F]u\<close> for u using H[THEN "&E"(2)] "\<forall>E"(2) by fast
  qed
  AOT_hence \<open>H \<approx>\<^sub>E F\<close>
    by (rule "apE-eqE:2"[THEN "\<rightarrow>E", OF "&I", rotated])
       (simp add: "eq-part:1")
  AOT_hence F_approx_H: \<open>F \<approx>\<^sub>E H\<close>
    by (metis "eq-part:2" "\<rightarrow>E")
  moreover AOT_have H_eq_act_H: \<open>H \<equiv>\<^sub>E [\<lambda>z \<^bold>\<A>[H]z]\<close>
  proof (safe intro!: eqE[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" Ordinary.GEN "\<rightarrow>I")
    AOT_show \<open>[H]u \<equiv> [\<lambda>z \<^bold>\<A>[H]z]u\<close> for u
      apply (AOT_subst \<open>[\<lambda>z \<^bold>\<A>[H]z]u\<close> \<open>\<^bold>\<A>[H]u\<close>)
       apply (rule "beta-C-meta"[THEN "\<rightarrow>E"])
       apply "cqt:2[lambda]"
      using rigid by blast
  qed
  AOT_have a: \<open>F \<approx>\<^sub>E [\<lambda>z \<^bold>\<A>[H]z]\<close>
    apply (rule "apE-eqE:2"[unvarify H, THEN "\<rightarrow>E"])
     apply "cqt:2[lambda]"
    using F_approx_H H_eq_act_H "&I" by blast
  AOT_hence \<open>[\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E F\<close>
    apply (rule "eq-part:2"[unvarify G, THEN "\<rightarrow>E", rotated])
    by "cqt:2[lambda]"
  AOT_hence b: \<open>[\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E G\<close>
    by (rule 0[THEN "\<forall>E"(1), THEN "\<equiv>E"(1), rotated]) "cqt:2" 
  AOT_show \<open>F \<approx>\<^sub>E G\<close>
    by (rule "eq-part:3"[unvarify G, THEN "\<rightarrow>E", rotated, OF "&I", OF a, OF b])
       "cqt:2"
qed

AOT_theorem "approx-nec:3":
  \<open>(Rigid(F) & Rigid(G)) \<rightarrow> \<box>(F \<approx>\<^sub>E G \<rightarrow> \<box>F \<approx>\<^sub>E G)\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>Rigid(F) & Rigid(G)\<close>
  AOT_hence \<open>\<box>\<forall>x([F]x \<rightarrow> \<box>[F]x)\<close> and \<open>\<box>\<forall>x([G]x \<rightarrow> \<box>[G]x)\<close>
    using "df-rigid-rel:1"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2)] "&E" by blast+
  AOT_hence \<open>\<box>(\<box>\<forall>x([F]x \<rightarrow> \<box>[F]x) & \<box>\<forall>x([G]x \<rightarrow> \<box>[G]x))\<close>
    using "KBasic:3" "4" "&I" "\<equiv>E"(2) "vdash-properties:10" by meson
  moreover AOT_have \<open>\<box>(\<box>\<forall>x([F]x \<rightarrow> \<box>[F]x) & \<box>\<forall>x([G]x \<rightarrow> \<box>[G]x)) \<rightarrow>
                     \<box>(F \<approx>\<^sub>E G \<rightarrow> \<box>F \<approx>\<^sub>E G)\<close>
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
      AOT_assume \<open>F \<approx>\<^sub>E G\<close>
      AOT_hence \<open>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
        by (metis "\<equiv>\<^sub>d\<^sub>fE" "equi:3")
      then AOT_obtain R where \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
        using "\<exists>E"[rotated] by blast
      AOT_hence C1: \<open>\<forall>u ([F]u \<rightarrow> \<exists>!v ([G]v & [R]uv))\<close>
            and C2: \<open>\<forall>v ([G]v \<rightarrow> \<exists>!u ([F]u & [R]uv))\<close>
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
      AOT_have \<open>\<forall>u \<box>([F]u \<rightarrow> \<exists>!v ([G]v & [R']uv))\<close>
           and \<open>\<forall>v \<box>([G]v \<rightarrow> \<exists>!u ([F]u & [R']uv))\<close>
      proof (safe intro!: Ordinary.GEN "\<rightarrow>I")
        fix u
        AOT_show \<open>\<box>([F]u \<rightarrow> \<exists>!v ([G]v & [R']uv))\<close>
        proof (rule "raa-cor:1")
          AOT_assume \<open>\<not>\<box>([F]u \<rightarrow> \<exists>!v ([G]v & [R']uv))\<close>
          AOT_hence 1: \<open>\<diamond>\<not>([F]u \<rightarrow> \<exists>!v ([G]v & [R']uv))\<close>
            using "KBasic:11" "\<equiv>E"(1) by blast
          AOT_have \<open>\<diamond>([F]u & \<not>\<exists>!v ([G]v & [R']uv))\<close>
            apply (AOT_subst \<open>[F]u & \<not>\<exists>!v ([G]v & [R']uv)\<close>
                             \<open>\<not>([F]u \<rightarrow> \<exists>!v ([G]v & [R']uv))\<close>)
             apply (meson "\<equiv>E"(6) "oth-class-taut:1:b" "oth-class-taut:3:a")
            by (fact 1)
          AOT_hence A: \<open>\<diamond>[F]u & \<diamond>\<not>\<exists>!v ([G]v & [R']uv)\<close>
            using "KBasic2:3" "\<rightarrow>E" by blast
          AOT_hence \<open>\<box>[F]u\<close>
            using F_nec "&E"(1) "\<equiv>E"(1) "sc-eq-box-box:1" "\<rightarrow>E" by blast
          AOT_hence \<open>[F]u\<close>
            by (metis "qml:2"[axiom_inst] "\<rightarrow>E")
          AOT_hence \<open>\<exists>!v ([G]v & [R]uv)\<close>
            using C1[THEN "Ordinary.\<forall>E", THEN "\<rightarrow>E"] by blast
          AOT_hence \<open>\<exists>v ([G]v & [R]uv & \<forall>v' ([G]v' & [R]uv' \<rightarrow> v' =\<^sub>E v))\<close>
            using "equi:1"[THEN "\<equiv>E"(1)] by auto
          then AOT_obtain a where
            a_prop: \<open>O!a & ([G]a & [R]ua & \<forall>v' ([G]v' & [R]uv' \<rightarrow> v' =\<^sub>E a))\<close>
            using "\<exists>E"[rotated] by blast
          AOT_have \<open>\<exists>v \<box>([G]v & [R']uv & \<forall>v' ([G]v' & [R']uv' \<rightarrow> v' =\<^sub>E v))\<close>
          proof(safe intro!: "\<exists>I"(2)[where \<beta>=a] "&I" a_prop[THEN "&E"(1)]
                             "KBasic:3"[THEN "\<equiv>E"(2)])
            AOT_show \<open>\<box>[G]a\<close>
              using a_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(1)]
              by (metis G_nec "qml:2"[axiom_inst] "\<rightarrow>E")
          next
            AOT_show \<open>\<box>[R']ua\<close>
              using D[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"]
                    E[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<equiv>E"(2),
                      OF a_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(2)]]
              by (metis "T\<diamond>" "\<rightarrow>E")
          next
            AOT_have \<open>\<forall>v' \<box>([G]v' & [R']uv' \<rightarrow> v' =\<^sub>E a)\<close>
            proof (rule Ordinary.GEN; rule "raa-cor:1")
              fix v'
              AOT_assume \<open>\<not>\<box>([G]v' & [R']uv' \<rightarrow> v' =\<^sub>E a)\<close>
              AOT_hence \<open>\<diamond>\<not>([G]v' & [R']uv' \<rightarrow> v' =\<^sub>E a)\<close>
                by (metis "KBasic:11" "\<equiv>E"(1))
              AOT_hence \<open>\<diamond>([G]v' & [R']uv' & \<not>v' =\<^sub>E a)\<close>
                by (AOT_subst \<open>[G]v' & [R']uv' & \<not>v' =\<^sub>E a\<close>
                              \<open>\<not>([G]v' & [R']uv' \<rightarrow> v' =\<^sub>E a)\<close>)
                   (meson "\<equiv>E"(6) "oth-class-taut:1:b" "oth-class-taut:3:a")
              AOT_hence 1: \<open>\<diamond>[G]v'\<close> and 2: \<open>\<diamond>[R']uv'\<close> and 3: \<open>\<diamond>\<not>v' =\<^sub>E a\<close>
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
              AOT_hence \<open>v' =\<^sub>E a\<close>
                using a_prop[THEN "&E"(2), THEN "&E"(2), THEN "Ordinary.\<forall>E",
                             THEN "\<rightarrow>E", OF "&I", OF Gv'] by blast
              AOT_hence \<open>\<box>(v' =\<^sub>E a)\<close>
                by (metis "id-nec3:1" "\<equiv>E"(4) "raa-cor:3")
              moreover AOT_have \<open>\<not>\<box>(v' =\<^sub>E a)\<close>
                using 3 "KBasic:11" "\<equiv>E"(2) by blast
              ultimately AOT_show \<open>\<box>(v' =\<^sub>E a) & \<not>\<box>(v' =\<^sub>E a)\<close>
                using "&I" by blast
            qed
            AOT_thus \<open>\<box>\<forall>v'([G]v' & [R']uv' \<rightarrow> v' =\<^sub>E a)\<close>
              using "Ordinary.res-var-bound-reas[BF]" "\<rightarrow>E" by fast
          qed
          AOT_hence \<open>\<box>\<exists>v ([G]v & [R']uv & \<forall>v' ([G]v' & [R']uv' \<rightarrow> v' =\<^sub>E v))\<close>
            using "Ordinary.res-var-bound-reas[Buridan]" "\<rightarrow>E" by fast
          AOT_hence \<open>\<box>\<exists>!v ([G]v & [R']uv)\<close>
            by (AOT_subst_thm "equi:1")
          moreover AOT_have \<open>\<not>\<box>\<exists>!v ([G]v & [R']uv)\<close>
            using A[THEN "&E"(2)] "KBasic:11"[THEN "\<equiv>E"(2)] by blast
          ultimately AOT_show \<open>\<box>\<exists>!v ([G]v & [R']uv) & \<not>\<box>\<exists>!v ([G]v & [R']uv)\<close>
            by (rule "&I")
        qed
      next
        fix v
        AOT_show \<open>\<box>([G]v \<rightarrow> \<exists>!u ([F]u & [R']uv))\<close>
        proof (rule "raa-cor:1")
          AOT_assume \<open>\<not>\<box>([G]v \<rightarrow> \<exists>!u ([F]u & [R']uv))\<close>
          AOT_hence 1: \<open>\<diamond>\<not>([G]v \<rightarrow> \<exists>!u ([F]u & [R']uv))\<close>
            using "KBasic:11" "\<equiv>E"(1) by blast
          AOT_hence \<open>\<diamond>([G]v & \<not>\<exists>!u ([F]u & [R']uv))\<close>
            by (AOT_subst \<open>[G]v & \<not>\<exists>!u ([F]u & [R']uv)\<close>
                          \<open>\<not>([G]v \<rightarrow> \<exists>!u ([F]u & [R']uv))\<close>)
               (meson "\<equiv>E"(6) "oth-class-taut:1:b" "oth-class-taut:3:a")
          AOT_hence A: \<open>\<diamond>[G]v & \<diamond>\<not>\<exists>!u ([F]u & [R']uv)\<close>
            using "KBasic2:3" "\<rightarrow>E" by blast
          AOT_hence \<open>\<box>[G]v\<close>
            using G_nec "&E"(1) "\<equiv>E"(1) "sc-eq-box-box:1" "\<rightarrow>E" by blast
          AOT_hence \<open>[G]v\<close> by (metis "qml:2"[axiom_inst] "\<rightarrow>E")
          AOT_hence \<open>\<exists>!u ([F]u & [R]uv)\<close>
            using C2[THEN "Ordinary.\<forall>E", THEN "\<rightarrow>E"] by blast
          AOT_hence \<open>\<exists>u ([F]u & [R]uv & \<forall>u' ([F]u' & [R]u'v \<rightarrow> u' =\<^sub>E u))\<close>
            using "equi:1"[THEN "\<equiv>E"(1)] by auto
          then AOT_obtain a where
              a_prop: \<open>O!a & ([F]a & [R]av & \<forall>u' ([F]u' & [R]u'v \<rightarrow> u' =\<^sub>E a))\<close>
            using "\<exists>E"[rotated] by blast
          AOT_have \<open>\<exists>u \<box>([F]u & [R']uv & \<forall>u' ([F]u' & [R']u'v \<rightarrow> u' =\<^sub>E u))\<close>
          proof(safe intro!: "\<exists>I"(2)[where \<beta>=a] "&I" a_prop[THEN "&E"(1)]
                             "KBasic:3"[THEN "\<equiv>E"(2)])
            AOT_show \<open>\<box>[F]a\<close>
              using a_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(1)]
              by (metis F_nec "qml:2"[axiom_inst] "\<rightarrow>E")
          next
            AOT_show \<open>\<box>[R']av\<close>
              using D[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"]
                    E[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<equiv>E"(2),
                      OF a_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(2)]]
              by (metis "T\<diamond>" "\<rightarrow>E")
          next
            AOT_have \<open>\<forall>u' \<box>([F]u' & [R']u'v \<rightarrow> u' =\<^sub>E a)\<close>
            proof (rule Ordinary.GEN; rule "raa-cor:1")
              fix u'
              AOT_assume \<open>\<not>\<box>([F]u' & [R']u'v \<rightarrow> u' =\<^sub>E a)\<close>
              AOT_hence \<open>\<diamond>\<not>([F]u' & [R']u'v \<rightarrow> u' =\<^sub>E a)\<close>
                by (metis "KBasic:11" "\<equiv>E"(1))
              AOT_hence \<open>\<diamond>([F]u' & [R']u'v & \<not>u' =\<^sub>E a)\<close>
                by (AOT_subst \<open>[F]u' & [R']u'v & \<not>u' =\<^sub>E a\<close>
                              \<open>\<not>([F]u' & [R']u'v \<rightarrow> u' =\<^sub>E a)\<close>)
                   (meson "\<equiv>E"(6) "oth-class-taut:1:b" "oth-class-taut:3:a")
              AOT_hence 1: \<open>\<diamond>[F]u'\<close> and 2: \<open>\<diamond>[R']u'v\<close> and 3: \<open>\<diamond>\<not>u' =\<^sub>E a\<close>
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
              AOT_hence \<open>u' =\<^sub>E a\<close>
                using a_prop[THEN "&E"(2), THEN "&E"(2), THEN "Ordinary.\<forall>E",
                             THEN "\<rightarrow>E", OF "&I", OF Fu'] by blast
              AOT_hence \<open>\<box>(u' =\<^sub>E a)\<close>
                by (metis "id-nec3:1" "\<equiv>E"(4) "raa-cor:3")
              moreover AOT_have \<open>\<not>\<box>(u' =\<^sub>E a)\<close>
                using 3 "KBasic:11" "\<equiv>E"(2) by blast
              ultimately AOT_show \<open>\<box>(u' =\<^sub>E a) & \<not>\<box>(u' =\<^sub>E a)\<close>
                using "&I" by blast
            qed
            AOT_thus \<open>\<box>\<forall>u'([F]u' & [R']u'v \<rightarrow> u' =\<^sub>E a)\<close>
              using "Ordinary.res-var-bound-reas[BF]" "\<rightarrow>E" by fast
          qed
          AOT_hence 1: \<open>\<box>\<exists>u ([F]u & [R']uv & \<forall>u' ([F]u' & [R']u'v \<rightarrow> u' =\<^sub>E u))\<close>
            using "Ordinary.res-var-bound-reas[Buridan]" "\<rightarrow>E" by fast
          AOT_hence \<open>\<box>\<exists>!u ([F]u & [R']uv)\<close>
            by (AOT_subst_thm "equi:1")
          moreover AOT_have \<open>\<not>\<box>\<exists>!u ([F]u & [R']uv)\<close>
            using A[THEN "&E"(2)] "KBasic:11"[THEN "\<equiv>E"(2)] by blast
          ultimately AOT_show \<open>\<box>\<exists>!u ([F]u & [R']uv) & \<not>\<box>\<exists>!u ([F]u & [R']uv)\<close>
            by (rule "&I")
        qed
      qed
      AOT_hence \<open>\<box>\<forall>u ([F]u \<rightarrow> \<exists>!v ([G]v & [R']uv))\<close>
            and \<open>\<box>\<forall>v ([G]v \<rightarrow> \<exists>!u ([F]u & [R']uv))\<close>
        using "Ordinary.res-var-bound-reas[BF]"[THEN "\<rightarrow>E"] by auto
      moreover AOT_have \<open>\<box>[R']\<down>\<close> and \<open>\<box>[F]\<down>\<close> and \<open>\<box>[G]\<down>\<close>
        by (simp_all add: "ex:2:a")
      ultimately AOT_have \<open>\<box>([R']\<down> & [F]\<down> & [G]\<down> & \<forall>u ([F]u \<rightarrow> \<exists>!v ([G]v & [R']uv)) &
                                                   \<forall>v ([G]v \<rightarrow> \<exists>!u ([F]u & [R']uv)))\<close>
        using "KBasic:3" "&I" "\<equiv>E"(2) by meson
      AOT_hence \<open>\<box>R' |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
        by (AOT_subst_def "equi:2")
      AOT_hence \<open>\<exists>R \<box>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
        by (rule "\<exists>I"(2))
      AOT_hence \<open>\<box>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
        by (metis Buridan "\<rightarrow>E")
      AOT_thus \<open>\<box>F \<approx>\<^sub>E G\<close>
        by (AOT_subst_def "equi:3")
    }
  qed
  ultimately AOT_show \<open>\<box>(F \<approx>\<^sub>E G \<rightarrow> \<box>F \<approx>\<^sub>E G)\<close>
    using "\<rightarrow>E" by blast
qed


AOT_define numbers :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>Numbers'(_,_')\<close>)
  \<open>Numbers(x,G) \<equiv>\<^sub>d\<^sub>f A!x & G\<down> & \<forall>F(x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close>

AOT_theorem "numbers[den]":
  \<open>\<Pi>\<down> \<rightarrow> (Numbers(\<kappa>, \<Pi>) \<equiv> A!\<kappa> & \<forall>F(\<kappa>[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E \<Pi>))\<close>
  apply (safe intro!: numbers[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "\<equiv>I" "\<rightarrow>I" "cqt:2"
               dest!: numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"])
  using "&E" by blast+

AOT_theorem "num-tran:1":
  \<open>G \<approx>\<^sub>E H \<rightarrow> (Numbers(x, G) \<equiv> Numbers(x, H))\<close>
proof (safe intro!: "\<rightarrow>I" "\<equiv>I")
  AOT_assume 0: \<open>G \<approx>\<^sub>E H\<close>
  AOT_assume \<open>Numbers(x, G)\<close>
  AOT_hence Ax: \<open>A!x\<close> and \<theta>: \<open>\<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close>
    using numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_show \<open>Numbers(x, H)\<close>
  proof(safe intro!: numbers[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" Ax "cqt:2" GEN)
    fix F
    AOT_have \<open>x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G\<close>
      using \<theta>[THEN "\<forall>E"(2)].
    also AOT_have \<open>\<dots> \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E H\<close>
      using 0 "approx-nec:2"[THEN "\<equiv>E"(1), THEN "\<forall>E"(2)] by metis
    finally AOT_show \<open>x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E H\<close>.
  qed
next
  AOT_assume \<open>G \<approx>\<^sub>E H\<close>
  AOT_hence 0: \<open>H \<approx>\<^sub>E G\<close>
    by (metis "eq-part:2" "\<rightarrow>E")
  AOT_assume \<open>Numbers(x, H)\<close>
  AOT_hence Ax: \<open>A!x\<close> and \<theta>: \<open>\<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E H)\<close>
    using numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_show \<open>Numbers(x, G)\<close>
  proof(safe intro!: numbers[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" Ax "cqt:2"  GEN)
    fix F
    AOT_have \<open>x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E H\<close>
      using \<theta>[THEN "\<forall>E"(2)].
    also AOT_have \<open>\<dots> \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G\<close>
      using 0 "approx-nec:2"[THEN "\<equiv>E"(1), THEN "\<forall>E"(2)] by metis
    finally AOT_show \<open>x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G\<close>.
  qed
qed

AOT_theorem "num-tran:2":
  \<open>(Numbers(x, G) & Numbers(x,H)) \<rightarrow> G \<approx>\<^sub>E H\<close>
proof (rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume \<open>Numbers(x,G)\<close>
  AOT_hence \<open>\<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close>
    using numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_hence 1: \<open>x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G\<close> for F
    using "\<forall>E"(2) by blast
  AOT_assume \<open>Numbers(x,H)\<close>
  AOT_hence \<open>\<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E H)\<close>
    using numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_hence \<open>x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E H\<close> for F
    using "\<forall>E"(2) by blast
  AOT_hence \<open>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E H\<close> for F
    by (metis "1" "\<equiv>E"(6))
  AOT_thus \<open>G \<approx>\<^sub>E H\<close>
    using "approx-nec:2"[THEN "\<equiv>E"(2), OF GEN] by blast
qed

AOT_theorem "num-tran:3":
  \<open>G \<equiv>\<^sub>E H \<rightarrow> (Numbers(x, G) \<equiv> Numbers(x, H))\<close>
  using "apE-eqE:1" "Hypothetical Syllogism" "num-tran:1" by blast

AOT_theorem "pre-Hume":
  \<open>(Numbers(x,G) & Numbers(y,H)) \<rightarrow> (x = y \<equiv> G \<approx>\<^sub>E H)\<close>
proof(safe intro!: "\<rightarrow>I" "\<equiv>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume \<open>Numbers(x, G)\<close>
  moreover AOT_assume \<open>x = y\<close>
  ultimately AOT_have \<open>Numbers(y, G)\<close> by (rule "rule=E")
  moreover AOT_assume \<open>Numbers(y, H)\<close>
  ultimately AOT_show \<open>G \<approx>\<^sub>E H\<close> using "num-tran:2" "\<rightarrow>E" "&I" by blast
next
  AOT_assume \<open>Numbers(x, G)\<close>
  AOT_hence Ax: \<open>A!x\<close> and xF: \<open>\<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close>
    using numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_assume \<open>Numbers(y, H)\<close>
  AOT_hence Ay: \<open>A!y\<close> and yF: \<open>\<forall>F (y[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E H)\<close>
    using numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_assume G_approx_H: \<open>G \<approx>\<^sub>E H\<close>
  AOT_show \<open>x = y\<close>
  proof(rule "ab-obey:1"[THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF "&I", OF Ax, OF Ay]; rule GEN)
    fix F
    AOT_have \<open>x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G\<close>
      using xF[THEN "\<forall>E"(2)].
    also AOT_have \<open>\<dots> \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E H\<close>
      using "approx-nec:2"[THEN "\<equiv>E"(1), OF G_approx_H, THEN "\<forall>E"(2)].
    also AOT_have \<open>\<dots> \<equiv> y[F]\<close>
      using yF[THEN "\<forall>E"(2), symmetric].
    finally AOT_show \<open>x[F] \<equiv> y[F]\<close>.
  qed
qed

AOT_theorem "two-num-not":
  \<open>\<exists>u\<exists>v(u \<noteq> v) \<rightarrow> \<exists>x\<exists>G\<exists>H(Numbers(x,G) & Numbers(x, H) & \<not>G \<equiv>\<^sub>E H)\<close>
proof (rule "\<rightarrow>I")
  AOT_have eqE_den: \<open>[\<lambda>x x =\<^sub>E y]\<down>\<close> for y by "cqt:2"
  AOT_assume \<open>\<exists>u\<exists>v(u \<noteq> v)\<close>
  then AOT_obtain c where Oc: \<open>O!c\<close> and \<open>\<exists>v (c \<noteq> v)\<close>
    using "&E" "\<exists>E"[rotated] by blast
  then AOT_obtain d where Od: \<open>O!d\<close> and c_noteq_d: \<open>c \<noteq> d\<close>
    using "&E" "\<exists>E"[rotated] by blast
  AOT_hence c_noteqE_d: \<open>c \<noteq>\<^sub>E d\<close>
    using "=E-simple:2"[THEN "\<rightarrow>E"] "=E-simple:2" "\<equiv>E"(2) "modus-tollens:1"
          "=-infix" "\<equiv>\<^sub>d\<^sub>fE" "thm-neg=E" by fast
  AOT_hence not_c_eqE_d: \<open>\<not>c =\<^sub>E d\<close>
    using "\<equiv>E"(1) "thm-neg=E" by blast
  AOT_have \<open>\<exists>x (A!x & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E [\<lambda>x x =\<^sub>E c]))\<close>
    by (simp add: "A-objects"[axiom_inst])
  then AOT_obtain a where a_prop: \<open>A!a & \<forall>F (a[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E [\<lambda>x x =\<^sub>E c])\<close>
    using "\<exists>E"[rotated] by blast
  AOT_have \<open>\<exists>x (A!x & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E [\<lambda>x x =\<^sub>E d]))\<close>
    by (simp add: "A-objects" "vdash-properties:1[2]")
  then AOT_obtain b where b_prop: \<open>A!b & \<forall>F (b[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E [\<lambda>x x =\<^sub>E d])\<close>
    using "\<exists>E"[rotated] by blast
  AOT_have num_a_eq_c: \<open>Numbers(a, [\<lambda>x x =\<^sub>E c])\<close>
    by (safe intro!: numbers[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" a_prop[THEN "&E"(1)]
                     a_prop[THEN "&E"(2)]) "cqt:2"
  moreover AOT_have num_b_eq_d: \<open>Numbers(b, [\<lambda>x x =\<^sub>E d])\<close>
    by (safe intro!: numbers[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" b_prop[THEN "&E"(1)]
                     b_prop[THEN "&E"(2)]) "cqt:2"
  moreover AOT_have \<open>[\<lambda>x x =\<^sub>E c] \<approx>\<^sub>E [\<lambda>x x =\<^sub>E d]\<close>
  proof (rule "equi:3"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
    let ?R = \<open>\<guillemotleft>[\<lambda>xy (x =\<^sub>E c & y =\<^sub>E d)]\<guillemotright>\<close>
    AOT_have Rcd: \<open>[\<guillemotleft>?R\<guillemotright>]cd\<close>
      by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" prod_denotesI
                       "ord=Eequiv:1"[THEN "\<rightarrow>E"] Od Oc)
    AOT_show \<open>\<exists>R R |: [\<lambda>x x =\<^sub>E c] \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E [\<lambda>x x =\<^sub>E d]\<close>
    proof (safe intro!: "\<exists>I"(1)[where \<tau>=\<open>?R\<close>] "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I"
                        eqE_den Ordinary.GEN "\<rightarrow>I")
      AOT_show \<open>\<guillemotleft>?R\<guillemotright>\<down>\<close> by "cqt:2"
    next
      fix u
      AOT_assume \<open>[\<lambda>x x =\<^sub>E c]u\<close>
      AOT_hence \<open>u =\<^sub>E c\<close>
        by (metis "\<beta>\<rightarrow>C"(1))
      AOT_hence u_is_c: \<open>u = c\<close>
        by (metis "=E-simple:2" "\<rightarrow>E")
      AOT_show \<open>\<exists>!v ([\<lambda>x x =\<^sub>E d]v & [\<guillemotleft>?R\<guillemotright>]uv)\<close>
      proof (safe intro!: "equi:1"[THEN "\<equiv>E"(2)] "\<exists>I"(2)[where \<beta>=d] "&I"
                          Od Ordinary.GEN "\<rightarrow>I")
        AOT_show \<open>[\<lambda>x x =\<^sub>E d]d\<close>
          by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "ord=Eequiv:1"[THEN "\<rightarrow>E", OF Od])
      next
        AOT_show \<open>[\<guillemotleft>?R\<guillemotright>]ud\<close>
          using u_is_c[symmetric] Rcd "rule=E" by fast
      next
        fix v
        AOT_assume \<open>[\<lambda>x x =\<^sub>E d]v & [\<guillemotleft>?R\<guillemotright>]uv\<close>
        AOT_thus \<open>v =\<^sub>E d\<close>
          by (metis "\<beta>\<rightarrow>C"(1) "&E"(1))
      qed
    next
      fix v
      AOT_assume \<open>[\<lambda>x x =\<^sub>E d]v\<close>
      AOT_hence \<open>v =\<^sub>E d\<close>
        by (metis "\<beta>\<rightarrow>C"(1))
      AOT_hence v_is_d: \<open>v = d\<close>
        by (metis "=E-simple:2" "\<rightarrow>E")
      AOT_show \<open>\<exists>!u ([\<lambda>x x =\<^sub>E c]u & [\<guillemotleft>?R\<guillemotright>]uv)\<close>
      proof (safe intro!: "equi:1"[THEN "\<equiv>E"(2)] "\<exists>I"(2)[where \<beta>=c] "&I"
                          Oc Ordinary.GEN "\<rightarrow>I")
        AOT_show \<open>[\<lambda>x x =\<^sub>E c]c\<close>
          by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "ord=Eequiv:1"[THEN "\<rightarrow>E", OF Oc])
      next
        AOT_show \<open>[\<guillemotleft>?R\<guillemotright>]cv\<close>
          using v_is_d[symmetric] Rcd "rule=E" by fast
      next
        fix u
        AOT_assume \<open>[\<lambda>x x =\<^sub>E c]u & [\<guillemotleft>?R\<guillemotright>]uv\<close>
        AOT_thus \<open>u =\<^sub>E c\<close>
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
  AOT_hence num_a_eq_d: \<open>Numbers(a, [\<lambda>x x =\<^sub>E d])\<close>
    using num_b_eq_d "rule=E" id_sym by fast
  AOT_have not_equiv: \<open>\<not>[\<lambda>x x =\<^sub>E c] \<equiv>\<^sub>E [\<lambda>x x =\<^sub>E d]\<close>
  proof (rule "raa-cor:2")
    AOT_assume \<open>[\<lambda>x x =\<^sub>E c] \<equiv>\<^sub>E [\<lambda>x x =\<^sub>E d]\<close>
    AOT_hence \<open>[\<lambda>x x =\<^sub>E c]c \<equiv> [\<lambda>x x =\<^sub>E d]c\<close>
      using eqE[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E"] Oc by blast
    moreover AOT_have \<open>[\<lambda>x x =\<^sub>E c]c\<close>
      by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "ord=Eequiv:1"[THEN "\<rightarrow>E", OF Oc])
    ultimately AOT_have \<open>[\<lambda>x x =\<^sub>E d]c\<close>
      using "\<equiv>E"(1) by blast
    AOT_hence \<open>c =\<^sub>E d\<close>
      by (rule "\<beta>\<rightarrow>C"(1))
    AOT_thus \<open>c =\<^sub>E d & \<not>c =\<^sub>E d\<close>
      using not_c_eqE_d "&I" by blast
  qed
  AOT_show \<open>\<exists>x \<exists>G \<exists>H (Numbers(x,G) & Numbers(x,H) & \<not>G \<equiv>\<^sub>E H)\<close>
    apply (rule "\<exists>I"(2)[where \<beta>=a])
    apply (rule "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>[\<lambda>x x =\<^sub>E c]\<guillemotright>\<close>])
     apply (rule "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>[\<lambda>x x =\<^sub>E d]\<guillemotright>\<close>])
    by (safe intro!: eqE_den "&I" num_a_eq_c num_a_eq_d not_equiv)
qed

AOT_theorem "num:1": \<open>\<exists>x Numbers(x,G)\<close>
  by (AOT_subst \<open>Numbers(x,G)\<close> \<open>[A!]x & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close> for: x)
     (auto simp: "numbers[den]"[THEN "\<rightarrow>E", OF "cqt:2[const_var]"[axiom_inst]]
                 "A-objects"[axiom_inst])

AOT_theorem "num:2": \<open>\<exists>!x Numbers(x,G)\<close>
  by (AOT_subst \<open>Numbers(x,G)\<close> \<open>[A!]x & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close> for: x)
     (auto simp: "numbers[den]"[THEN "\<rightarrow>E", OF "cqt:2[const_var]"[axiom_inst]]
                 "A-objects!")

AOT_theorem "num-cont:1":
  \<open>\<exists>x\<exists>G(Numbers(x, G) & \<not>\<box>Numbers(x, G))\<close>
proof -
  AOT_have \<open>\<exists>F\<exists>G \<diamond>([\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G & \<diamond>\<not>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close>
    using "approx-cont:2".
  then AOT_obtain F where \<open>\<exists>G \<diamond>([\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G & \<diamond>\<not>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close>
    using "\<exists>E"[rotated] by blast
  then AOT_obtain G where \<open>\<diamond>([\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G & \<diamond>\<not>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<theta>: \<open>\<diamond>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G\<close> and \<zeta>: \<open>\<diamond>\<not>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G\<close>
    using "KBasic2:3"[THEN "\<rightarrow>E"] "&E" "4\<diamond>"[THEN "\<rightarrow>E"] by blast+
  AOT_obtain a where \<open>Numbers(a, G)\<close>
    using "num:1" "\<exists>E"[rotated] by blast
  moreover AOT_have \<open>\<not>\<box>Numbers(a, G)\<close>
  proof (rule "raa-cor:2")
    AOT_assume \<open>\<box>Numbers(a, G)\<close>
    AOT_hence \<open>\<box>([A!]a & G\<down> & \<forall>F (a[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G))\<close>
      by (AOT_subst_def (reverse) numbers)
    AOT_hence \<open>\<box>A!a\<close> and \<open>\<box>\<forall>F (a[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close>
      using "KBasic:3"[THEN "\<equiv>E"(1)] "&E" by blast+
    AOT_hence \<open>\<forall>F \<box>(a[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close>
      using CBF[THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>\<box>(a[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close>
      using "\<forall>E"(2) by blast
    AOT_hence A: \<open>\<box>(a[F] \<rightarrow> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close>
          and B: \<open>\<box>([\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G \<rightarrow> a[F])\<close>
      using "KBasic:4"[THEN "\<equiv>E"(1)] "&E" by blast+
    AOT_have \<open>\<box>(\<not>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G \<rightarrow> \<not>a[F])\<close>
      apply (AOT_subst \<open>\<not>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G \<rightarrow> \<not>a[F]\<close> \<open>a[F] \<rightarrow> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G\<close>)
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
      AOT_hence \<open>[A!]x & G\<down> & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close>
        using numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
      AOT_hence Ax: \<open>[A!]x\<close> and \<open>\<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close>
        using "&E" by blast+
      AOT_hence \<open>x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G\<close> for F
        using "\<forall>E"(2) by blast
      moreover AOT_have \<open>\<box>([\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G \<rightarrow> \<box>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close> for F
        using "approx-nec:3"[unvarify F, OF act_den, THEN "\<rightarrow>E", OF "&I",
                             OF "actuallyF:2", OF G_rigid].
      moreover AOT_have \<open>\<box>(x[F] \<rightarrow> \<box>x[F])\<close> for F
        by (simp add: RN "pre-en-eq:1[1]")
      ultimately AOT_have \<open>\<box>(x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close> for F
        using "sc-eq-box-box:5" "\<rightarrow>E" "qml:2"[axiom_inst] "&I" by meson
      AOT_hence \<open>\<forall>F \<box>(x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close>
        by (rule "\<forall>I")
      AOT_hence 1: \<open>\<box>\<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close>
        using BF[THEN "\<rightarrow>E"] by fast
      AOT_have \<open>\<box>G\<down>\<close>
        by (simp add: "ex:2:a")
      moreover AOT_have \<open>\<box>[A!]x\<close>
        using Ax "oa-facts:2" "\<rightarrow>E" by blast
      ultimately AOT_have \<open>\<box>(A!x & G\<down>)\<close>
        by (metis "KBasic:3" "&I" "\<equiv>E"(2))
      AOT_hence \<open>\<box>(A!x & G\<down> & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G))\<close>
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
  \<open>#G = \<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G))\<close>
proof -
  AOT_have \<open>\<box>\<forall>x(Numbers(x,G) \<equiv> [A!]x & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G))\<close>
    by (safe intro!: RN GEN "numbers[den]"[THEN "\<rightarrow>E"] "cqt:2")
  AOT_hence \<open>\<^bold>\<iota>x Numbers(x, G) = \<^bold>\<iota>x([A!]x & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G))\<close>
    using "num-uniq" "equiv-desc-eq:3"[THEN "\<rightarrow>E", OF "&I"] by auto
  thus ?thesis
    by (rule "=\<^sub>d\<^sub>fI"(1)[OF "num-def:1", OF "num-uniq"])
qed

AOT_theorem "num-can:2": \<open>#G = \<^bold>\<iota>x(A!x & \<forall>F (x[F] \<equiv> F \<approx>\<^sub>E G))\<close>
proof (rule id_trans[OF "num-can:1"]; rule "equiv-desc-eq:2"[THEN "\<rightarrow>E"];
       safe intro!: "&I" "A-descriptions" GEN "Act-Basic:5"[THEN "\<equiv>E"(2)]
                    "logic-actual-nec:3"[axiom_inst, THEN "\<equiv>E"(2)])
  AOT_have act_den: \<open>\<^bold>\<turnstile>\<^sub>\<box> [\<lambda>z \<^bold>\<A>[F]z]\<down>\<close> for F
    by "cqt:2"
  AOT_have "eq-part:3[terms]": \<open>\<^bold>\<turnstile>\<^sub>\<box> F \<approx>\<^sub>E G & F \<approx>\<^sub>E H \<rightarrow> G \<approx>\<^sub>E H\<close> for F G H
    by (metis "&I" "eq-part:2" "eq-part:3" "\<rightarrow>I" "&E" "\<rightarrow>E")
  fix x
  {
    fix F
    AOT_have \<open>\<^bold>\<A>(F \<approx>\<^sub>E [\<lambda>z \<^bold>\<A>[F]z])\<close>
      by (simp add: "actuallyF:1")
    moreover AOT_have \<open>\<^bold>\<A>((F \<approx>\<^sub>E [\<lambda>z \<^bold>\<A>[F]z]) \<rightarrow> ([\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G \<equiv> F \<approx>\<^sub>E G))\<close>
      by (auto intro!: "RA[2]" "\<rightarrow>I" "\<equiv>I"
               simp: "eq-part:3"[unvarify G, OF act_den, THEN "\<rightarrow>E", OF "&I"]
                     "eq-part:3[terms]"[unvarify G, OF act_den, THEN "\<rightarrow>E", OF "&I"])
    ultimately AOT_have \<open>\<^bold>\<A>([\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G \<equiv> F \<approx>\<^sub>E G)\<close>
      using "logic-actual-nec:2"[axiom_inst, THEN "\<equiv>E"(1), THEN "\<rightarrow>E"] by blast

    AOT_hence \<open>\<^bold>\<A>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G \<equiv> \<^bold>\<A>F \<approx>\<^sub>E G\<close>
      by (metis "Act-Basic:5" "\<equiv>E"(1))
    AOT_hence 0: \<open>(\<^bold>\<A>x[F] \<equiv> \<^bold>\<A>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G) \<equiv> (\<^bold>\<A>x[F] \<equiv> \<^bold>\<A>F \<approx>\<^sub>E G)\<close>
      by (auto intro!: "\<equiv>I" "\<rightarrow>I" elim: "\<equiv>E")
    AOT_have \<open>\<^bold>\<A>(x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G) \<equiv> (\<^bold>\<A>x[F] \<equiv> \<^bold>\<A>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close>
      by (simp add: "Act-Basic:5")
    also AOT_have \<open>\<dots> \<equiv> (\<^bold>\<A>x[F] \<equiv> \<^bold>\<A>F \<approx>\<^sub>E G)\<close> using 0.
    also AOT_have \<open>\<dots> \<equiv> \<^bold>\<A>((x[F] \<equiv> F \<approx>\<^sub>E G))\<close>
      by (meson "Act-Basic:5" "\<equiv>E"(6) "oth-class-taut:3:a")
    finally AOT_have 0: \<open>\<^bold>\<A>(x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G) \<equiv> \<^bold>\<A>((x[F] \<equiv> F \<approx>\<^sub>E G))\<close>.
  } note 0 = this
  AOT_have \<open>\<^bold>\<A>\<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G) \<equiv> \<forall>F \<^bold>\<A>(x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)\<close>
    using "logic-actual-nec:3" "vdash-properties:1[2]" by blast
  also AOT_have \<open>\<dots> \<equiv>  \<forall>F \<^bold>\<A>((x[F] \<equiv> F \<approx>\<^sub>E G))\<close>
    apply (safe intro!: "\<equiv>I" "\<rightarrow>I" GEN)
    using 0 "\<equiv>E"(1) "\<equiv>E"(2) "rule-ui:3" by blast+
  also AOT_have \<open>\<dots> \<equiv> \<^bold>\<A>(\<forall>F (x[F] \<equiv> F \<approx>\<^sub>E G))\<close>
    using "\<equiv>E"(6) "logic-actual-nec:3"[axiom_inst] "oth-class-taut:3:a" by fast
  finally AOT_have 0: \<open>\<^bold>\<A>\<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G) \<equiv> \<^bold>\<A>(\<forall>F (x[F] \<equiv> F \<approx>\<^sub>E G))\<close>.
  AOT_have \<open>\<^bold>\<A>([A!]x & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)) \<equiv>
            (\<^bold>\<A>A!x & \<^bold>\<A>\<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G))\<close>
    by (simp add: "Act-Basic:2")
  also AOT_have \<open>\<dots> \<equiv> \<^bold>\<A>[A!]x & \<^bold>\<A>(\<forall>F (x[F] \<equiv> F \<approx>\<^sub>E G))\<close>
    using 0 "oth-class-taut:4:f" "\<rightarrow>E" by blast
  also AOT_have \<open>\<dots> \<equiv> \<^bold>\<A>(A!x & \<forall>F (x[F] \<equiv> F \<approx>\<^sub>E G))\<close>
    using "Act-Basic:2" "\<equiv>E"(6) "oth-class-taut:3:a" by blast
  finally AOT_show \<open>\<^bold>\<A>([A!]x & \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)) \<equiv>
                    \<^bold>\<A>([A!]x & \<forall>F (x[F] \<equiv> F \<approx>\<^sub>E G))\<close>.
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

AOT_act_theorem "hume:2": \<open>#F = #G \<equiv> F \<approx>\<^sub>E G\<close>
  by (safe intro!: "pre-Hume"[unvarify x y, OF "num-def:2",
                              OF "num-def:2", THEN "\<rightarrow>E"] "&I" "hume:1")

AOT_act_theorem "hume:3": \<open>#F = #G \<equiv> \<exists>R (R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G)\<close>
  using "equi-rem-thm"
  apply (AOT_subst (reverse) \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close>
                             \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close> for: R :: \<open><\<kappa>\<times>\<kappa>>\<close>)
  using "equi:3" "hume:2" "\<equiv>E"(5) "\<equiv>Df" by blast

AOT_act_theorem "hume:4": \<open>F \<equiv>\<^sub>E G \<rightarrow> #F = #G\<close>
  by (metis "apE-eqE:1" "deduction-theorem" "hume:2" "\<equiv>E"(2) "\<rightarrow>E")

AOT_theorem "hume-strict:1":
  \<open>\<exists>x (Numbers(x, F) & Numbers(x, G)) \<equiv> F \<approx>\<^sub>E G\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>\<exists>x (Numbers(x, F) & Numbers(x, G))\<close>
  then AOT_obtain a where \<open>Numbers(a, F) & Numbers(a, G)\<close>
    using "\<exists>E"[rotated] by blast
  AOT_thus \<open>F \<approx>\<^sub>E G\<close>
    using "num-tran:2" "\<rightarrow>E" by blast
next
  AOT_assume 0: \<open>F \<approx>\<^sub>E G\<close>
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
   F \<approx>\<^sub>E G\<close>
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
  AOT_thus \<open>F \<approx>\<^sub>E G\<close>
    using "hume-strict:1"[THEN "\<equiv>E"(1)] by blast
next
  AOT_assume \<open>F \<approx>\<^sub>E G\<close>
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

AOT_theorem unotEu: \<open>\<not>\<exists>y[\<lambda>x O!x & x \<noteq>\<^sub>E x]y\<close>
proof(rule "raa-cor:2")
  AOT_assume \<open>\<exists>y[\<lambda>x O!x & x \<noteq>\<^sub>E x]y\<close>
  then AOT_obtain y where \<open>[\<lambda>x O!x & x \<noteq>\<^sub>E x]y\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence 0: \<open>O!y & y \<noteq>\<^sub>E y\<close>
    by (rule "\<beta>\<rightarrow>C"(1))
  AOT_hence \<open>\<not>(y =\<^sub>E y)\<close>
    using "&E"(2) "\<equiv>E"(1) "thm-neg=E" by blast
  moreover AOT_have \<open>y =\<^sub>E y\<close>
    by (metis 0[THEN "&E"(1)] "ord=Eequiv:1" "\<rightarrow>E")
  ultimately AOT_show \<open>p & \<not>p\<close> for p
    by (metis "raa-cor:3")
qed

AOT_define zero :: \<open>\<kappa>\<^sub>s\<close> (\<open>0\<close>)
  "zero:1": \<open>0 =\<^sub>d\<^sub>f #[\<lambda>x O!x & x \<noteq>\<^sub>E x]\<close>

AOT_theorem "zero:2": \<open>0\<down>\<close>
  by (rule "=\<^sub>d\<^sub>fI"(2)[OF "zero:1"]; rule "num-def:2"[unvarify G]; "cqt:2")

AOT_theorem "zero-card": \<open>NaturalCardinal(0)\<close>
  apply (rule "=\<^sub>d\<^sub>fI"(2)[OF "zero:1"])
   apply (rule "num-def:2"[unvarify G]; "cqt:2")
  apply (rule card[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  apply (rule "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>[\<lambda>x [O!]x & x \<noteq>\<^sub>E x]\<guillemotright>\<close>])
   apply (rule "rule=I:1"; rule "num-def:2"[unvarify G]; "cqt:2")
  by "cqt:2"

AOT_theorem "eq-num:1":
  \<open>\<^bold>\<A>Numbers(x, G) \<equiv> Numbers(x,[\<lambda>z \<^bold>\<A>[G]z])\<close>
proof -
  AOT_have act_den: \<open>\<^bold>\<turnstile>\<^sub>\<box> [\<lambda>z \<^bold>\<A>[F]z]\<down>\<close> for F by "cqt:2"
  AOT_have \<open>\<box>(\<exists>x(Numbers(x, G) & Numbers(x,[\<lambda>z \<^bold>\<A>[G]z])) \<equiv> G \<approx>\<^sub>E [\<lambda>z \<^bold>\<A>[G]z])\<close>
    using "hume-strict:1"[unvarify G, OF act_den, THEN RN].
  AOT_hence \<open>\<^bold>\<A>(\<exists>x(Numbers(x, G) & Numbers(x,[\<lambda>z \<^bold>\<A>[G]z])) \<equiv> G \<approx>\<^sub>E [\<lambda>z \<^bold>\<A>[G]z])\<close>
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
  \<open>A!#G & \<forall>F (#G[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E [\<lambda>z \<^bold>\<A>[G]z])\<close>
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
  AOT_hence \<open>F \<equiv>\<^sub>E G\<close>
    by (auto intro!: eqE[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" GEN "\<rightarrow>I" elim: "\<forall>E"(2))
  moreover AOT_assume \<open>Numbers(x, G)\<close>
  ultimately AOT_have \<open>Numbers(x, F)\<close>
    using "num-tran:3"[THEN "\<rightarrow>E", THEN "\<equiv>E"(2)] by blast
  moreover AOT_have \<open>F \<approx>\<^sub>E [\<lambda>z \<^bold>\<A>[F]z]\<close>
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
  AOT_have \<open>#P[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E [\<lambda>z \<^bold>\<A>[P]z]\<close>
    using "eq-num:4"[THEN "&E"(2), THEN "\<forall>E"(2)] by blast
  AOT_hence \<open>x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E [\<lambda>z \<^bold>\<A>[P]z]\<close>
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
  AOT_have unotEu_act_ord: \<open>\<not>\<exists>v[\<lambda>x O!x & \<^bold>\<A>x \<noteq>\<^sub>E x]v\<close>
  proof(rule "raa-cor:2")
    AOT_assume \<open>\<exists>v[\<lambda>x O!x & \<^bold>\<A>x \<noteq>\<^sub>E x]v\<close>
    then AOT_obtain y where \<open>[\<lambda>x O!x & \<^bold>\<A>x \<noteq>\<^sub>E x]y\<close>
      using "\<exists>E"[rotated] "&E" by blast
    AOT_hence 0: \<open>O!y & \<^bold>\<A>y \<noteq>\<^sub>E y\<close>
      by (rule "\<beta>\<rightarrow>C"(1))
    AOT_have \<open>\<^bold>\<A>\<not>(y =\<^sub>E y)\<close>
      apply (AOT_subst  \<open>\<not>(y =\<^sub>E y)\<close> \<open>y \<noteq>\<^sub>E y\<close>)
       apply (meson "\<equiv>E"(2) "Commutativity of \<equiv>" "thm-neg=E")
      by (fact 0[THEN "&E"(2)])
    AOT_hence \<open>\<not>(y =\<^sub>E y)\<close>
      by (metis "\<not>\<not>I" "Act-Sub:1" "id-act2:1" "\<equiv>E"(4))
    moreover AOT_have \<open>y =\<^sub>E y\<close>
      by (metis 0[THEN "&E"(1)] "ord=Eequiv:1" "\<rightarrow>E")
    ultimately AOT_show \<open>p & \<not>p\<close> for p
      by (metis "raa-cor:3")
  qed
  AOT_have \<open>Numbers(0, [\<lambda>y \<^bold>\<A>[\<lambda>x O!x & x \<noteq>\<^sub>E x]y])\<close>
    apply (rule "=\<^sub>d\<^sub>fI"(2)[OF "zero:1"])
     apply (rule "num-def:2"[unvarify G]; "cqt:2")
    apply (rule "eq-num:3"[unvarify G])
    by "cqt:2[lambda]"
  AOT_hence numbers0: \<open>Numbers(0, [\<lambda>x [O!]x & \<^bold>\<A>x \<noteq>\<^sub>E x])\<close>
  proof (rule "num-tran:3"[unvarify x G H, THEN "\<rightarrow>E", THEN "\<equiv>E"(1), rotated 4])
    AOT_show \<open>[\<lambda>y \<^bold>\<A>[\<lambda>x O!x & x \<noteq>\<^sub>E x]y] \<equiv>\<^sub>E [\<lambda>x [O!]x & \<^bold>\<A>x \<noteq>\<^sub>E x]\<close>
    proof (safe intro!: eqE[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" Ordinary.GEN "\<rightarrow>I" "cqt:2")
      fix u
      AOT_have \<open>[\<lambda>y \<^bold>\<A>[\<lambda>x O!x & x \<noteq>\<^sub>E x]y]u \<equiv> \<^bold>\<A>[\<lambda>x O!x & x \<noteq>\<^sub>E x]u\<close>
        by (rule "beta-C-meta"[THEN "\<rightarrow>E"]; "cqt:2[lambda]")
      also AOT_have \<open>\<dots> \<equiv> \<^bold>\<A>(O!u & u \<noteq>\<^sub>E u)\<close>
        apply (AOT_subst \<open>[\<lambda>x O!x & x \<noteq>\<^sub>E x]u\<close> \<open>O!u & u \<noteq>\<^sub>E u\<close>)
         apply (rule "beta-C-meta"[THEN "\<rightarrow>E"]; "cqt:2[lambda]")
        by (simp add: "oth-class-taut:3:a")
      also AOT_have \<open>\<dots> \<equiv> (\<^bold>\<A>O!u & \<^bold>\<A>u \<noteq>\<^sub>E u)\<close>
        by (simp add: "Act-Basic:2")
      also AOT_have \<open>\<dots> \<equiv> (O!u & \<^bold>\<A>u \<noteq>\<^sub>E u)\<close>
        by (metis Ordinary.\<psi> "&I" "&E"(2) "\<rightarrow>I" "\<equiv>I" "\<equiv>E"(1) "oa-facts:7")
      also AOT_have \<open>\<dots> \<equiv> [\<lambda>x [O!]x & \<^bold>\<A>x \<noteq>\<^sub>E x]u\<close>
        by (rule "beta-C-meta"[THEN "\<rightarrow>E", symmetric]; "cqt:2[lambda]")
      finally AOT_show \<open>[\<lambda>y \<^bold>\<A>[\<lambda>x O!x & x \<noteq>\<^sub>E x]y]u \<equiv> [\<lambda>x [O!]x & \<^bold>\<A>x \<noteq>\<^sub>E x]u\<close>.
    qed
  qed(fact "zero:2" | "cqt:2")+
  show ?thesis
  proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
    AOT_assume \<open>\<not>\<exists>u [F]u\<close>
    moreover AOT_have \<open>\<not>\<exists>v [\<lambda>x [O!]x & \<^bold>\<A>x \<noteq>\<^sub>E x]v\<close>
      using unotEu_act_ord.
    ultimately AOT_have 0: \<open>F \<approx>\<^sub>E [\<lambda>x [O!]x & \<^bold>\<A>x \<noteq>\<^sub>E x]\<close>
      by (rule "empty-approx:1"[unvarify H, THEN "\<rightarrow>E", rotated, OF "&I"]) "cqt:2"
    AOT_thus \<open>Numbers(0, F)\<close>
      by (rule "num-tran:1"[unvarify x H, THEN "\<rightarrow>E",
                            THEN "\<equiv>E"(2), rotated, rotated])
         (fact "zero:2" numbers0 | "cqt:2[lambda]")+
  next
    AOT_assume \<open>Numbers(0, F)\<close>
    AOT_hence 1: \<open>F \<approx>\<^sub>E [\<lambda>x [O!]x & \<^bold>\<A>x \<noteq>\<^sub>E x]\<close>
      by (rule "num-tran:2"[unvarify x H, THEN "\<rightarrow>E", rotated 2, OF "&I"])
         (fact numbers0 "zero:2" | "cqt:2[lambda]")+
    AOT_show \<open>\<not>\<exists>u [F]u\<close>
    proof(rule "raa-cor:2")
      AOT_have 0: \<open>[\<lambda>x [O!]x & \<^bold>\<A>x \<noteq>\<^sub>E x]\<down>\<close> by "cqt:2[lambda]"
      AOT_assume \<open>\<exists>u [F]u\<close>
      AOT_hence \<open>\<not>(F \<approx>\<^sub>E [\<lambda>x [O!]x & \<^bold>\<A>x \<noteq>\<^sub>E x])\<close>
        by (rule "empty-approx:2"[unvarify H, OF 0, THEN "\<rightarrow>E", OF "&I"])
           (rule unotEu_act_ord)
      AOT_thus \<open>F \<approx>\<^sub>E [\<lambda>x [O!]x & \<^bold>\<A>x \<noteq>\<^sub>E x] & \<not>(F \<approx>\<^sub>E [\<lambda>x [O!]x & \<^bold>\<A>x \<noteq>\<^sub>E x])\<close> 
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
      using "Ordinary.\<exists>E"[rotated] by blast
    AOT_hence \<open>\<^bold>\<A>[F]u\<close>
      by (metis "betaC:1:a")
    AOT_hence \<open>\<exists>u \<^bold>\<A>[F]u\<close>
      by (rule "Ordinary.\<exists>I")
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
      using "Ordinary.\<exists>E"[rotated] by meson
    AOT_hence \<open>[\<lambda>z \<^bold>\<A>[F]z]u\<close>
      by (auto intro!: "\<beta>\<leftarrow>C" "cqt:2")
    AOT_hence \<open>\<exists>u [\<lambda>z \<^bold>\<A>[F]z]u\<close>
      using "Ordinary.\<exists>I" by blast
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
      using "Ordinary.\<exists>E"[rotated] by blast
    AOT_hence \<open>\<^bold>\<A>[F]u\<close>
      by (metis "betaC:1:a")
    AOT_hence \<open>\<diamond>[F]u\<close>
      by (metis "Act-Sub:3" "\<rightarrow>E")
    AOT_hence \<open>\<exists>u \<diamond>[F]u\<close>
      by (rule "Ordinary.\<exists>I")
    AOT_hence \<open>\<diamond>\<exists>u [F]u\<close>
      using "Ordinary.res-var-bound-reas[CBF\<diamond>]"[THEN "\<rightarrow>E"] by blast
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
        using "Ordinary.\<exists>E"[rotated] by meson
      AOT_hence \<open>\<^bold>\<A>w \<Turnstile> [F]u\<close>
        by (AOT_subst (reverse) \<open>w \<Turnstile> [F]u\<close> \<open>[\<lambda>x w \<Turnstile> [F]x]u\<close>;
            safe intro!: "beta-C-meta"[THEN "\<rightarrow>E"] "w-rel:1"[THEN "\<rightarrow>E"])
           "cqt:2"
      AOT_hence 1: \<open>w \<Turnstile> [F]u\<close>
        using "rigid-truth-at:4"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(1)]
        by blast
      AOT_have \<open>\<box>([F]u \<rightarrow> \<exists>u [F]u)\<close>
        using "Ordinary.\<exists>I" "\<rightarrow>I" RN by simp
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
      AOT_hence \<open>\<exists>x w \<Turnstile> (O!x & [F]x)\<close>
        using "conj-dist-w:6"[THEN "\<equiv>E"(1)] by fast
      then AOT_obtain x where \<open>w \<Turnstile> (O!x & [F]x)\<close>
        using "\<exists>E"[rotated] by blast
      AOT_hence \<open>w \<Turnstile> O!x\<close> and Fx_in_w: \<open>w \<Turnstile> [F]x\<close>
        using "conj-dist-w:1"[unvarify p q] "\<equiv>E"(1) "log-prop-prop:2"
              "&E" by blast+
      AOT_hence \<open>\<diamond>O!x\<close>
        using "fund:1"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(2)]
              "PossibleWorld.\<exists>I" by simp
      AOT_hence ord_x: \<open>O!x\<close>
        using "oa-facts:3"[THEN "\<rightarrow>E"] by blast
      AOT_have \<open>\<^bold>\<A>w \<Turnstile> [F]x\<close>
        using "rigid-truth-at:4"[unvarify p, OF "log-prop-prop:2", THEN "\<equiv>E"(2)]
              Fx_in_w by blast
      AOT_hence \<open>\<^bold>\<A>[\<lambda>x w \<Turnstile> [F]x]x\<close>
        by (AOT_subst \<open>[\<lambda>x w \<Turnstile> [F]x]x\<close> \<open>w \<Turnstile> [F]x\<close>;
            safe intro!: "beta-C-meta"[THEN "\<rightarrow>E"] "w-rel:1"[THEN "\<rightarrow>E"]) "cqt:2"
      AOT_hence \<open>O!x & \<^bold>\<A>[\<lambda>x w \<Turnstile> [F]x]x\<close>
        using ord_x "&I" by blast
      AOT_hence \<open>\<exists>x (O!x & \<^bold>\<A>[\<lambda>x w \<Turnstile> [F]x]x)\<close>
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
  }
next
  AOT_modally_strict {
    AOT_show \<open>\<forall>F(Rigid\<^sub>1\<^sub>-\<^sub>1(F) \<rightarrow> \<box>Rigid\<^sub>1\<^sub>-\<^sub>1(F))\<close>
      by (safe intro!: GEN "df-1-1:4"[THEN "\<forall>E"(2)])
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

text\<open>The following is not part of PLM, but a theorem of AOT.
     It states that the predecessor relation coexists with numbering a property.
     We will use this fact to derive the predecessor axiom, which asserts that the
     predecessor relation denotes, from the fact that our models validate that
     numbering a property denotes.\<close>
AOT_theorem pred_coex:
  \<open>[\<lambda>xy \<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))]\<down> \<equiv> \<forall>F ([\<lambda>x Numbers(x,F)]\<down>)\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I" GEN)
  fix F
  let ?\<P> = \<open>\<guillemotleft>[\<lambda>xy \<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))]\<guillemotright>\<close>
  AOT_assume \<open>[\<guillemotleft>?\<P>\<guillemotright>]\<down>\<close>
  AOT_hence \<open>\<box>[\<guillemotleft>?\<P>\<guillemotright>]\<down>\<close>
    using "exist-nec" "\<rightarrow>E" by blast
  moreover AOT_have
    \<open>\<box>[\<guillemotleft>?\<P>\<guillemotright>]\<down> \<rightarrow> \<box>(\<forall>x\<forall>y(\<forall>F([F]x \<equiv> [F]y) \<rightarrow> (Numbers(x,F) \<equiv> Numbers(y,F))))\<close>
  proof(rule RM; safe intro!: "\<rightarrow>I" GEN)
    AOT_modally_strict {
      fix x y
      AOT_assume pred_den: \<open>[\<guillemotleft>?\<P>\<guillemotright>]\<down>\<close>
      AOT_hence pred_equiv:
        \<open>[\<guillemotleft>?\<P>\<guillemotright>]xy \<equiv> \<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close> for x y
        by (safe intro!: "beta-C-meta"[unvarify \<nu>\<^sub>1\<nu>\<^sub>n, where \<tau>=\<open>(_,_)\<close>, THEN "\<rightarrow>E",
                                       rotated, OF pred_den, simplified]
                         tuple_denotes[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2")
      text\<open>We show as a subproof that any natural cardinal that is not zero
           has a predecessor.\<close>
      AOT_have CardinalPredecessor:
        \<open>\<exists>y [\<guillemotleft>?\<P>\<guillemotright>]yx\<close> if card_x: \<open>NaturalCardinal(x)\<close> and x_nonzero: \<open>x \<noteq> 0\<close> for x
      proof -
        AOT_have \<open>\<exists>G x = #G\<close>
          using card[THEN "\<equiv>\<^sub>d\<^sub>fE", OF card_x].
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
          using "CBF" "\<rightarrow>E" by blast
        AOT_hence R: \<open>\<box>([G]x \<rightarrow> \<box>[G]x)\<close> for x using "\<forall>E"(2) by blast
        AOT_hence rigid: \<open>[G]x \<equiv> \<^bold>\<A>[G]x\<close> for x
           by (metis "\<equiv>E"(6) "oth-class-taut:3:a" "sc-eq-fur:2" "\<rightarrow>E")
        AOT_have \<open>G \<equiv>\<^sub>E G'\<close>
        proof (safe intro!: eqE[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" GEN "\<rightarrow>I")
          AOT_show \<open>[G]x \<equiv> [G']x\<close> for x using H[THEN "&E"(2)] "\<forall>E"(2) by fast
        qed
        AOT_hence \<open>G \<approx>\<^sub>E G'\<close>
          by (rule "apE-eqE:2"[THEN "\<rightarrow>E", OF "&I", rotated])
             (simp add: "eq-part:1")
        AOT_hence numxG: \<open>Numbers(x,G)\<close>
          using "num-tran:1"[THEN "\<rightarrow>E", THEN "\<equiv>E"(2)] numxG' by blast
      
        {
          AOT_assume \<open>\<not>\<exists>y(y \<noteq> x & [\<guillemotleft>?\<P>\<guillemotright>]yx)\<close>
          AOT_hence \<open>\<forall>y \<not>(y \<noteq> x & [\<guillemotleft>?\<P>\<guillemotright>]yx)\<close>
            using "cqt-further:4" "\<rightarrow>E" by blast
          AOT_hence \<open>\<not>(y \<noteq> x & [\<guillemotleft>?\<P>\<guillemotright>]yx)\<close> for y
            using "\<forall>E"(2) by blast
          AOT_hence 0: \<open>\<not>y \<noteq> x \<or> \<not>[\<guillemotleft>?\<P>\<guillemotright>]yx\<close> for y
            using "\<not>\<not>E" "intro-elim:3:c" "oth-class-taut:5:a" by blast
          {
            fix y
            AOT_assume \<open>[\<guillemotleft>?\<P>\<guillemotright>]yx\<close>
            AOT_hence \<open>\<not>y \<noteq> x\<close>
              using 0 "\<not>\<not>I" "con-dis-i-e:4:c" by blast
            AOT_hence \<open>y = x\<close>
              using "=-infix" "\<equiv>\<^sub>d\<^sub>fI" "raa-cor:4" by blast
          } note Pxy_imp_eq = this
          AOT_have \<open>[\<guillemotleft>?\<P>\<guillemotright>]xx\<close>
          proof(rule "raa-cor:1")
            AOT_assume notPxx: \<open>\<not>[\<guillemotleft>?\<P>\<guillemotright>]xx\<close>
            AOT_hence \<open>\<not>\<exists>F\<exists>u([F]u & Numbers(x,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
              using pred_equiv "intro-elim:3:c" by blast
            AOT_hence \<open>\<forall>F \<not>\<exists>u([F]u & Numbers(x,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
              using "cqt-further:4"[THEN "\<rightarrow>E"] by blast
            AOT_hence \<open>\<not>\<exists>u([F]u & Numbers(x,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close> for F
              using "\<forall>E"(2) by blast
            AOT_hence \<open>\<forall>y \<not>(O!y & ([F]y & Numbers(x,F) & Numbers(x,[F]\<^sup>-\<^sup>y)))\<close> for F
              using "cqt-further:4"[THEN "\<rightarrow>E"] by blast
            AOT_hence 0: \<open>\<not>(O!u & ([F]u & Numbers(x,F) & Numbers(x,[F]\<^sup>-\<^sup>u)))\<close> for F u
              using "\<forall>E"(2) by blast
            AOT_have \<open>\<box>\<not>\<exists>u [G]u\<close>
            proof(rule "raa-cor:1")
              AOT_assume \<open>\<not>\<box>\<not>\<exists>u [G]u\<close>
              AOT_hence \<open>\<diamond>\<exists>u [G]u\<close>
                using "\<equiv>\<^sub>d\<^sub>fI" "conventions:5" by blast
              AOT_hence \<open>\<exists>u \<diamond>[G]u\<close>
                by (metis "Ordinary.res-var-bound-reas[BF\<diamond>]"[THEN "\<rightarrow>E"])
              then AOT_obtain u where posGu: \<open>\<diamond>[G]u\<close>
                using "Ordinary.\<exists>E"[rotated] by meson
              AOT_hence Gu: \<open>[G]u\<close>
                by (meson "B\<diamond>" "K\<diamond>" "\<rightarrow>E" R)
              AOT_have \<open>\<not>([G]u & Numbers(x,G) & Numbers(x,[G]\<^sup>-\<^sup>u))\<close>
                using 0 Ordinary.\<psi>
                by (metis "con-dis-i-e:1" "raa-cor:1")
              AOT_hence notnumx: \<open>\<not>Numbers(x,[G]\<^sup>-\<^sup>u)\<close>
                using Gu numxG "con-dis-i-e:1" "raa-cor:5" by metis
              AOT_obtain y where numy: \<open>Numbers(y,[G]\<^sup>-\<^sup>u)\<close>
                using "num:1"[unvarify G, OF "F-u[den]"] "\<exists>E"[rotated] by blast
              AOT_hence \<open>[G]u & Numbers(x,G) & Numbers(y,[G]\<^sup>-\<^sup>u)\<close>
                using Gu numxG "&I" by blast
              AOT_hence \<open>\<exists>u ([G]u & Numbers(x,G) & Numbers(y,[G]\<^sup>-\<^sup>u))\<close>
                by (rule "Ordinary.\<exists>I")
              AOT_hence \<open>\<exists>G\<exists>u ([G]u & Numbers(x,G) & Numbers(y,[G]\<^sup>-\<^sup>u))\<close>
                by (rule "\<exists>I")
              AOT_hence \<open>[\<guillemotleft>?\<P>\<guillemotright>]yx\<close>
                using pred_equiv[THEN "\<equiv>E"(2)] by blast
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
              using "pre-Hume"[unvarify x, THEN "\<rightarrow>E", OF "zero:2", OF "&I",
                               THEN "\<equiv>E"(2), OF num0G, OF numxG, OF "eq-part:1"]
                id_sym by blast
            moreover AOT_have \<open>\<not>x = 0\<close>
              using x_nonzero
              using "=-infix" "\<equiv>\<^sub>d\<^sub>fE" by blast
            ultimately AOT_show \<open>p & \<not>p\<close> for p using "reductio-aa:1" by blast
          qed
        }
        AOT_hence \<open>[\<guillemotleft>?\<P>\<guillemotright>]xx \<or> \<exists>y (y \<noteq> x & [\<guillemotleft>?\<P>\<guillemotright>]yx)\<close>
          using "con-dis-i-e:3:a" "con-dis-i-e:3:b" "raa-cor:1" by blast
        moreover {
          AOT_assume \<open>[\<guillemotleft>?\<P>\<guillemotright>]xx\<close>
          AOT_hence \<open>\<exists>y [\<guillemotleft>?\<P>\<guillemotright>]yx\<close>
            by (rule "\<exists>I")
        }
        moreover {
          AOT_assume \<open>\<exists>y (y \<noteq> x & [\<guillemotleft>?\<P>\<guillemotright>]yx)\<close>
          then AOT_obtain y where \<open>y \<noteq> x & [\<guillemotleft>?\<P>\<guillemotright>]yx\<close>
            using "\<exists>E"[rotated] by blast
          AOT_hence \<open>[\<guillemotleft>?\<P>\<guillemotright>]yx\<close>
            using "&E" by blast
          AOT_hence \<open>\<exists>y [\<guillemotleft>?\<P>\<guillemotright>]yx\<close>
            by (rule "\<exists>I")
        }
        ultimately AOT_show \<open>\<exists>y [\<guillemotleft>?\<P>\<guillemotright>]yx\<close>
          using "\<or>E"(1) "\<rightarrow>I" by blast
      qed

      text\<open>Given above lemma, we can show that if one of two indistinguishable objects
           numbers a property, the other one numbers this property as well.\<close>
      AOT_assume indist: \<open>\<forall>F([F]x \<equiv> [F]y)\<close>
      AOT_assume numxF: \<open>Numbers(x,F)\<close> 
      AOT_hence 0: \<open>NaturalCardinal(x)\<close>
        by (metis "eq-num:6" "vdash-properties:10")
      text\<open>We show by case distinction that x equals y.
           As first case we consider x to be non-zero.\<close>
      {
        AOT_assume \<open>\<not>(x = 0)\<close>
        AOT_hence \<open>x \<noteq> 0\<close>
          by (metis "=-infix" "\<equiv>\<^sub>d\<^sub>fI")
        AOT_hence \<open>\<exists>y [\<guillemotleft>?\<P>\<guillemotright>]yx\<close>
          using CardinalPredecessor 0 by blast
        then AOT_obtain z where Pxz: \<open>[\<guillemotleft>?\<P>\<guillemotright>]zx\<close>
          using "\<exists>E"[rotated] by blast
        AOT_hence \<open>[\<lambda>y [\<guillemotleft>?\<P>\<guillemotright>]zy]x\<close>
          by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2")
        AOT_hence \<open>[\<lambda>y [\<guillemotleft>?\<P>\<guillemotright>]zy]y\<close>
          by (safe intro!: indist[THEN "\<forall>E"(1), THEN "\<equiv>E"(1)] "cqt:2")
        AOT_hence Pyz: \<open>[\<guillemotleft>?\<P>\<guillemotright>]zy\<close>
          using "\<beta>\<rightarrow>C"(1) by blast
        AOT_hence \<open>\<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(z,[F]\<^sup>-\<^sup>u))\<close>
          using Pyz pred_equiv[THEN "\<equiv>E"(1)] by blast
        then AOT_obtain F\<^sub>1 where \<open>\<exists>u ([F\<^sub>1]u & Numbers(y,F\<^sub>1) & Numbers(z,[F\<^sub>1]\<^sup>-\<^sup>u))\<close>
          using "\<exists>E"[rotated] by blast
        then AOT_obtain u where u_prop: \<open>[F\<^sub>1]u & Numbers(y,F\<^sub>1) & Numbers(z,[F\<^sub>1]\<^sup>-\<^sup>u)\<close>
          using "Ordinary.\<exists>E"[rotated] by meson
        AOT_have \<open>\<exists>F\<exists>u ([F]u & Numbers(x,F) & Numbers(z,[F]\<^sup>-\<^sup>u))\<close>
          using Pxz pred_equiv[THEN "\<equiv>E"(1)] by blast
        then AOT_obtain F\<^sub>2 where \<open>\<exists>u ([F\<^sub>2]u & Numbers(x,F\<^sub>2) & Numbers(z,[F\<^sub>2]\<^sup>-\<^sup>u))\<close>
          using "\<exists>E"[rotated] by blast
        then AOT_obtain v where v_prop: \<open>[F\<^sub>2]v & Numbers(x,F\<^sub>2) & Numbers(z,[F\<^sub>2]\<^sup>-\<^sup>v)\<close>
          using "Ordinary.\<exists>E"[rotated] by meson
        AOT_have \<open>[F\<^sub>2]\<^sup>-\<^sup>v \<approx>\<^sub>E [F\<^sub>1]\<^sup>-\<^sup>u\<close>
          using "hume-strict:1"[unvarify F G, THEN "\<equiv>E"(1), OF "F-u[den]",
                                OF "F-u[den]", OF "\<exists>I"(2)[where \<beta>=z], OF "&I"]
                  v_prop u_prop "&E" by blast
        AOT_hence \<open>F\<^sub>2 \<approx>\<^sub>E F\<^sub>1\<close>
          using "P'-eq"[THEN "\<rightarrow>E", OF "&I", OF "&I"] 
                 u_prop v_prop "&E" by meson
        AOT_hence \<open>x = y\<close>
          using "pre-Hume"[THEN "\<rightarrow>E", THEN "\<equiv>E"(2), OF "&I"]
                v_prop u_prop "&E" by blast
      }
      text\<open>The second case handles x being equal to zero.\<close>
      moreover {
        fix u
        AOT_assume x_is_zero: \<open>x = 0\<close>
        moreover AOT_have \<open>Numbers(0,[\<lambda>z z =\<^sub>E u]\<^sup>-\<^sup>u)\<close>
        proof (safe intro!: "0F:1"[unvarify F, THEN "\<equiv>E"(1)] "cqt:2" "raa-cor:2"
                            "F-u[den]"[unvarify F])
          AOT_assume \<open>\<exists>v [[\<lambda>z z =\<^sub>E u]\<^sup>-\<^sup>u]v\<close>
          then AOT_obtain v where \<open>[[\<lambda>z z =\<^sub>E u]\<^sup>-\<^sup>u]v\<close>
            using "Ordinary.\<exists>E"[rotated] by meson
          AOT_hence \<open>[\<lambda>z z =\<^sub>E u]v & v \<noteq>\<^sub>E u\<close>
            by (auto intro: "F-u"[THEN "=\<^sub>d\<^sub>fE"(1), where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", simplified]
                     intro!: "cqt:2" "F-u[equiv]"[unvarify F, THEN "\<equiv>E"(1)]
                             "F-u[den]"[unvarify F])
          AOT_thus \<open>p & \<not>p\<close> for p
            using "\<beta>\<rightarrow>C" "thm-neg=E"[THEN "\<equiv>E"(1)] "&E" "&I"
                  "raa-cor:3" by fast
        qed
        ultimately AOT_have 0: \<open>Numbers(x,[\<lambda>z z =\<^sub>E u]\<^sup>-\<^sup>u)\<close>
          using "rule=E" id_sym by fast
        AOT_have \<open>\<exists>y Numbers(y,[\<lambda>z z =\<^sub>E u])\<close>
          by (safe intro!: "num:1"[unvarify G] "cqt:2")
        then AOT_obtain z where \<open>Numbers(z,[\<lambda>z z =\<^sub>E u])\<close>
          using "\<exists>E" by metis
        moreover AOT_have \<open>[\<lambda>z z=\<^sub>E u]u\<close>
          by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2" "ord=Eequiv:1"[THEN "\<rightarrow>E"] Ordinary.\<psi>)
        ultimately AOT_have
          1: \<open>[\<lambda>z z=\<^sub>E u]u & Numbers(z,[\<lambda>z z=\<^sub>E u]) & Numbers(x,[\<lambda>z z=\<^sub>E u]\<^sup>-\<^sup>u)\<close>
          using 0 "&I" by auto
        AOT_hence \<open>\<exists>v([\<lambda>z z=\<^sub>E u]v & Numbers(z,[\<lambda>z z =\<^sub>E u]) & Numbers(x,[\<lambda>z z=\<^sub>E u]\<^sup>-\<^sup>v))\<close>
          by (rule "Ordinary.\<exists>I")
        AOT_hence \<open>\<exists>F\<exists>u([F]u & Numbers(z,[F]) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
          by (rule "\<exists>I"; "cqt:2")
        AOT_hence Px1: \<open>[\<guillemotleft>?\<P>\<guillemotright>]xz\<close>
          using "beta-C-cor:2"[THEN "\<rightarrow>E", OF pred_den,
                  THEN tuple_forall[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "\<forall>E"(2),
                  THEN "\<forall>E"(2), THEN "\<equiv>E"(2)] by simp
        AOT_hence \<open>[\<lambda>y [\<guillemotleft>?\<P>\<guillemotright>]yz]x\<close>
          by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2")
        AOT_hence \<open>[\<lambda>y [\<guillemotleft>?\<P>\<guillemotright>]yz]y\<close>
          by (safe intro!: indist[THEN "\<forall>E"(1), THEN "\<equiv>E"(1)] "cqt:2")
        AOT_hence Py1: \<open>[\<guillemotleft>?\<P>\<guillemotright>]yz\<close>
          using "\<beta>\<rightarrow>C" by blast
        AOT_hence \<open>\<exists>F\<exists>u([F]u & Numbers(z,[F]) & Numbers(y,[F]\<^sup>-\<^sup>u))\<close>
          using "\<beta>\<rightarrow>C" by fast
        then AOT_obtain G where \<open>\<exists>u([G]u & Numbers(z,[G]) & Numbers(y,[G]\<^sup>-\<^sup>u))\<close>
          using "\<exists>E"[rotated] by blast
        then AOT_obtain v where 2: \<open>[G]v & Numbers(z,[G]) & Numbers(y,[G]\<^sup>-\<^sup>v)\<close>
          using "Ordinary.\<exists>E"[rotated] by meson
        with 1 2 AOT_have \<open>[\<lambda>z z =\<^sub>E u] \<approx>\<^sub>E G\<close>
          by (auto intro!: "hume-strict:1"[unvarify F, THEN "\<equiv>E"(1), rotated,
                                OF "\<exists>I"(2)[where \<beta>=z], OF "&I"] "cqt:2"
                   dest: "&E")
        AOT_hence 3: \<open>[\<lambda>z z =\<^sub>E u]\<^sup>-\<^sup>u \<approx>\<^sub>E [G]\<^sup>-\<^sup>v\<close>
          using 1 2
          by (safe_step intro!: "eqP'"[unvarify F, THEN "\<rightarrow>E"])
             (auto dest: "&E" intro!: "cqt:2" "&I")
        with 1 2 AOT_have \<open>x = y\<close>
          by (auto intro!: "pre-Hume"[unvarify G H, THEN "\<rightarrow>E",
                                      THEN "\<equiv>E"(2), rotated 3, OF 3]
                           "F-u[den]"[unvarify F] "cqt:2" "&I"
                   dest: "&E")
      }
      ultimately AOT_have \<open>x = y\<close>
        using "\<or>E"(1) "\<rightarrow>I" "reductio-aa:1" by blast
      text\<open>Now since x numbers F, so does y.\<close>
      AOT_hence \<open>Numbers(y,F)\<close>
          using numxF "rule=E" by fast
    } note 0 = this
    text\<open>The only thing left is to generalize this result to a biconditional.\<close>
    AOT_modally_strict {
      fix x y
      AOT_assume \<open>[\<guillemotleft>?\<P>\<guillemotright>]\<down>\<close>
      moreover AOT_assume \<open>\<forall>F([F]x \<equiv> [F]y)\<close>
      moreover AOT_have \<open>\<forall>F([F]y \<equiv> [F]x)\<close>
        by (metis "cqt-basic:11" "intro-elim:3:a" calculation(2))
      ultimately AOT_show \<open>Numbers(x,F) \<equiv> Numbers(y,F)\<close>
        using 0 "\<equiv>I" "\<rightarrow>I" by auto
    }
  qed
  ultimately AOT_show \<open>[\<lambda>x Numbers(x,F)]\<down>\<close>
    using "kirchner-thm:1"[THEN "\<equiv>E"(2)] "\<rightarrow>E" by fast
next
  text\<open>The converse can be shown by coexistence.\<close>
  AOT_assume \<open>\<forall>F [\<lambda>x Numbers(x,F)]\<down>\<close>
  AOT_hence \<open>[\<lambda>x Numbers(x,F)]\<down>\<close> for F
    using "\<forall>E"(2) by blast
  AOT_hence \<open>\<box>[\<lambda>x Numbers(x,F)]\<down>\<close> for F
    using "exist-nec"[THEN "\<rightarrow>E"] by blast
  AOT_hence \<open>\<forall>F \<box>[\<lambda>x Numbers(x,F)]\<down>\<close>
    by (rule GEN)
  AOT_hence \<open>\<box>\<forall>F [\<lambda>x Numbers(x,F)]\<down>\<close>
    using BF[THEN "\<rightarrow>E"] by fast
  moreover AOT_have
    \<open>\<box>\<forall>F [\<lambda>x Numbers(x,F)]\<down> \<rightarrow>
     \<box>\<forall>x \<forall>y (\<exists>F \<exists>u ([F]u & [\<lambda>z Numbers(z,F)]y & [\<lambda>z Numbers(z,[F]\<^sup>-\<^sup>u)]x) \<equiv>
              \<exists>F \<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u)))\<close>
  proof(rule RM; safe intro!: "\<rightarrow>I" GEN)
    AOT_modally_strict {
      fix x y
      AOT_assume 0: \<open>\<forall>F [\<lambda>x Numbers(x,F)]\<down>\<close>
      AOT_show \<open>\<exists>F \<exists>u ([F]u & [\<lambda>z Numbers(z,F)]y & [\<lambda>z Numbers(z,[F]\<^sup>-\<^sup>u)]x) \<equiv>
              \<exists>F \<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
      proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
        AOT_assume \<open>\<exists>F \<exists>u ([F]u & [\<lambda>z Numbers(z,F)]y & [\<lambda>z Numbers(z,[F]\<^sup>-\<^sup>u)]x)\<close>
        then AOT_obtain F where
          \<open>\<exists>u ([F]u & [\<lambda>z Numbers(z,F)]y & [\<lambda>z Numbers(z,[F]\<^sup>-\<^sup>u)]x)\<close>
          using "\<exists>E"[rotated] by blast
        then AOT_obtain u where \<open>[F]u & [\<lambda>z Numbers(z,F)]y & [\<lambda>z Numbers(z,[F]\<^sup>-\<^sup>u)]x\<close>
          using "Ordinary.\<exists>E"[rotated] by meson
        AOT_hence \<open>[F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u)\<close>
          by (auto intro!: "&I" dest: "&E" "\<beta>\<rightarrow>C")
        AOT_thus \<open>\<exists>F \<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
          using "\<exists>I" "Ordinary.\<exists>I" by fast
      next
        AOT_assume \<open>\<exists>F \<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
        then AOT_obtain F where \<open>\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
          using "\<exists>E"[rotated] by blast
        then AOT_obtain u where \<open>[F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u)\<close>
          using "Ordinary.\<exists>E"[rotated] by meson
        AOT_hence \<open>[F]u & [\<lambda>z Numbers(z,F)]y & [\<lambda>z Numbers(z,[F]\<^sup>-\<^sup>u)]x\<close>
          by (auto intro!: "&I" "\<beta>\<leftarrow>C" 0[THEN "\<forall>E"(1)] "F-u[den]"
                   dest: "&E" intro: "cqt:2")
        AOT_hence \<open>\<exists>u([F]u & [\<lambda>z Numbers(z,F)]y & [\<lambda>z Numbers(z,[F]\<^sup>-\<^sup>u)]x)\<close>
          by (rule "Ordinary.\<exists>I")
        AOT_thus \<open>\<exists>F\<exists>u([F]u & [\<lambda>z Numbers(z,F)]y & [\<lambda>z Numbers(z,[F]\<^sup>-\<^sup>u)]x)\<close>
          by (rule "\<exists>I")
      qed
    }
  qed
  ultimately AOT_have
    \<open>\<box>\<forall>x \<forall>y (\<exists>F \<exists>u ([F]u & [\<lambda>z Numbers(z,F)]y & [\<lambda>z Numbers(z,[F]\<^sup>-\<^sup>u)]x) \<equiv>
              \<exists>F \<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u)))\<close>
    using "\<rightarrow>E" by blast
  AOT_thus \<open>[\<lambda>xy \<exists>F \<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))]\<down>\<close>
    by (rule "safe-ext[2]"[axiom_inst, THEN "\<rightarrow>E", OF "&I", rotated]) "cqt:2"
qed

text\<open>The following is not part of PLM, but a consequence of extended relation
     comprehension and can be used to @{emph \<open>derive\<close>} the predecessor axiom.\<close>
AOT_theorem numbers_prop_den: \<open>[\<lambda>x Numbers(x,G)]\<down>\<close>
proof (rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E", OF "&I"])
  AOT_show \<open>[\<lambda>x A!x & [\<lambda>x \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)]x]\<down>\<close>
    by "cqt:2"
next
  AOT_have 0: \<open>\<^bold>\<turnstile>\<^sub>\<box> [\<lambda>x \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)]\<down>\<close>
  proof(safe intro!: Comprehension_3[THEN "\<rightarrow>E"] "\<rightarrow>I" RN GEN)
      AOT_modally_strict {
        fix F H
        AOT_assume \<open>\<box>H \<equiv>\<^sub>E F\<close>
        AOT_hence \<open>\<box>\<forall>u ([H]u \<equiv> [F]u)\<close>
          by (AOT_subst (reverse) \<open>\<forall>u ([H]u \<equiv> [F]u)\<close> \<open>H \<equiv>\<^sub>E F\<close>)
              (safe intro!: "eqE"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I"] "cqt:2")
        AOT_hence \<open>\<forall>u \<box>([H]u \<equiv> [F]u)\<close>
          by (metis "Ordinary.res-var-bound-reas[CBF]" "\<rightarrow>E")
        AOT_hence \<open>\<box>([H]u \<equiv> [F]u)\<close> for u
          using "Ordinary.\<forall>E" by fast
        AOT_hence \<open>\<^bold>\<A>([H]u \<equiv> [F]u)\<close> for u
          by (metis "nec-imp-act" "\<rightarrow>E")
        AOT_hence \<open>\<^bold>\<A>([F]u \<equiv> [H]u)\<close> for u
          by (metis "Act-Basic:5" "Commutativity of \<equiv>" "intro-elim:3:b")
        AOT_hence \<open>[\<lambda>z \<^bold>\<A>[F]z] \<equiv>\<^sub>E [\<lambda>z \<^bold>\<A>[H]z]\<close>
          by (safe intro!: "eqE"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" Ordinary.GEN;
              AOT_subst \<open>[\<lambda>z \<^bold>\<A>[F]z]u\<close> \<open>\<^bold>\<A>[F]u\<close> for: u F)
             (auto intro!: "beta-C-meta"[THEN "\<rightarrow>E"] "cqt:2"
                           "Act-Basic:5"[THEN "\<equiv>E"(1)])
        AOT_hence \<open>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E [\<lambda>z \<^bold>\<A>[H]z]\<close>
          by (safe intro!: "apE-eqE:1"[unvarify F G, THEN "\<rightarrow>E"] "cqt:2")
        AOT_thus \<open>[\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G \<equiv> [\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E G\<close>
          using "\<equiv>I" "eq-part:2[terms]" "eq-part:3[terms]" "\<rightarrow>E" "\<rightarrow>I"
          by metis
      }
  qed
  AOT_show \<open>\<box>\<forall>x (A!x & [\<lambda>x \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)]x \<equiv> Numbers(x,G))\<close>
  proof (safe intro!: RN GEN)
    AOT_modally_strict {
      fix x
      AOT_show \<open>A!x & [\<lambda>x \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)]x \<equiv> Numbers(x,G)\<close>
        by (AOT_subst_def numbers; AOT_subst_thm "beta-C-meta"[THEN "\<rightarrow>E", OF 0])
           (auto intro!: "beta-C-meta"[THEN "\<rightarrow>E", OF 0] "\<equiv>I" "\<rightarrow>I" "&I" "cqt:2"
                   dest: "&E")
    }
  qed
qed

text\<open>The two theorems above allow us to derive
     the predecessor axiom of PLM as theorem.\<close>

AOT_theorem pred: \<open>[\<lambda>xy \<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))]\<down>\<close>
  using pred_coex numbers_prop_den["\<forall>I" G] "\<equiv>E" by blast

AOT_define Predecessor :: \<open>\<Pi>\<close> (\<open>\<P>\<close>)
  "pred-thm:1":
  \<open>\<P> =\<^sub>d\<^sub>f [\<lambda>xy \<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))]\<close>

AOT_theorem "pred-thm:2": \<open>\<P>\<down>\<close>
  using pred "pred-thm:1" "rule-id-df:2:b[zero]" by blast

AOT_theorem "pred-thm:3":
  \<open>[\<P>]xy \<equiv> \<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    by (auto intro!: "beta-C-meta"[unvarify \<nu>\<^sub>1\<nu>\<^sub>n, where \<tau>=\<open>(_,_)\<close>, THEN "\<rightarrow>E",
                                   rotated, OF pred, simplified]
                     tuple_denotes[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" pred
             intro: "=\<^sub>d\<^sub>fI"(2)[OF "pred-thm:1"])

AOT_theorem "pred-1-1:1": \<open>[\<P>]xy \<rightarrow> \<box>[\<P>]xy\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>[\<P>]xy\<close>
  AOT_hence \<open>\<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    using "\<equiv>E"(1) "pred-thm:3" by fast
  then AOT_obtain F where \<open>\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    using "\<exists>E"[rotated] by blast
  then AOT_obtain u where props: \<open>[F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u)\<close>
    using "Ordinary.\<exists>E"[rotated] by meson
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
          eqE[THEN "\<equiv>\<^sub>d\<^sub>fI"]
            "&I" "cqt:2[const_var]"[axiom_inst] Ordinary.GEN "\<rightarrow>I")
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
          AOT_have \<open>[\<lambda>x [G]x & x \<noteq>\<^sub>E u]x\<close>
            apply (rule "F-u"[THEN "=\<^sub>d\<^sub>fE"(1), where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", simplified])
             apply "cqt:2[lambda]"
            by (fact 1)
          AOT_hence \<open>[G]x & x \<noteq>\<^sub>E u\<close>
            by (rule "\<beta>\<rightarrow>C"(1))
          AOT_hence 2: \<open>\<box>[G]x\<close> and 3: \<open>\<box>x \<noteq>\<^sub>E u\<close>
            using "&E" 0[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] "id-nec4:1" "\<equiv>E"(1) by blast+
          AOT_show \<open>\<box>[[G]\<^sup>-\<^sup>u]x\<close>
            apply (AOT_subst \<open>[[G]\<^sup>-\<^sup>u]x\<close> \<open>[G]x & x \<noteq>\<^sub>E u\<close>)
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
      AOT_hence \<open>[\<lambda>x [G]x & x \<noteq>\<^sub>E u]x\<close>
        by (auto intro: "F-u"[THEN "=\<^sub>d\<^sub>fE"(1), where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", simplified]
                intro!: "cqt:2")
      AOT_hence \<open>[G]x & x \<noteq>\<^sub>E u\<close>
        by (rule "\<beta>\<rightarrow>C"(1))
      AOT_hence \<open>[F]x & x \<noteq>\<^sub>E u\<close>
        using \<zeta> "&I" "&E"(1) "&E"(2) "\<equiv>E"(1) "rule-ui:3" by blast
      AOT_hence \<open>[\<lambda>x [F]x & x \<noteq>\<^sub>E u]x\<close>
        by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2")
      AOT_thus \<open>[[F]\<^sup>-\<^sup>u]x\<close>
        by (auto intro: "F-u"[THEN "=\<^sub>d\<^sub>fI"(1), where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", simplified]
                intro!: "cqt:2")
    next
      fix x
      AOT_assume \<open>[[F]\<^sup>-\<^sup>u]x\<close>
      AOT_hence \<open>[\<lambda>x [F]x & x \<noteq>\<^sub>E u]x\<close>
        by (auto intro: "F-u"[THEN "=\<^sub>d\<^sub>fE"(1), where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", simplified]
                intro!: "cqt:2")
      AOT_hence \<open>[F]x & x \<noteq>\<^sub>E u\<close>
        by (rule "\<beta>\<rightarrow>C"(1))
      AOT_hence \<open>[G]x & x \<noteq>\<^sub>E u\<close>
        using \<zeta> "&I" "&E"(1) "&E"(2) "\<equiv>E"(2) "rule-ui:3" by blast
      AOT_hence \<open>[\<lambda>x [G]x & x \<noteq>\<^sub>E u]x\<close>
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
    by (rule "Ordinary.\<exists>I")
  AOT_hence \<open>\<box>\<exists>u ([G]u & Numbers(y,G) & Numbers(x,[G]\<^sup>-\<^sup>u))\<close>
    using "Ordinary.res-var-bound-reas[Buridan]" "\<rightarrow>E" by fast
  AOT_hence \<open>\<exists>F \<box>\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    by (rule "\<exists>I")
  AOT_hence 0: \<open>\<box>\<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    using Buridan "vdash-properties:10" by fast
  AOT_show \<open>\<box>[\<P>]xy\<close>
    by (AOT_subst \<open>[\<P>]xy\<close> \<open>\<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>;
        simp add: "pred-thm:3" 0)
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
  then AOT_obtain F where \<open>\<exists>u ([F]u & Numbers(z,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    using "\<exists>E"[rotated] by blast
  then AOT_obtain u where u_prop: \<open>[F]u & Numbers(z,F) & Numbers(x,[F]\<^sup>-\<^sup>u)\<close>
    using "Ordinary.\<exists>E"[rotated] by meson
  AOT_assume \<open>[\<P>]yz\<close>
  AOT_hence \<open>\<exists>F\<exists>u ([F]u & Numbers(z,F) & Numbers(y,[F]\<^sup>-\<^sup>u))\<close>
    using "pred-thm:3"[THEN "\<equiv>E"(1)] by blast
  then AOT_obtain G where \<open>\<exists>u ([G]u & Numbers(z,G) & Numbers(y,[G]\<^sup>-\<^sup>u))\<close>
    using "\<exists>E"[rotated] by blast
  then AOT_obtain v where v_prop: \<open>[G]v & Numbers(z,G) & Numbers(y,[G]\<^sup>-\<^sup>v)\<close>
    using "Ordinary.\<exists>E"[rotated] by meson
  AOT_show \<open>x = y\<close>
  proof (rule "pre-Hume"[unvarify G H, OF "F-u[den]", OF "F-u[den]",
                         THEN "\<rightarrow>E", OF "&I", THEN "\<equiv>E"(2)])
    AOT_show \<open>Numbers(x, [F]\<^sup>-\<^sup>u)\<close>
      using u_prop "&E" by blast
  next
    AOT_show \<open>Numbers(y, [G]\<^sup>-\<^sup>v)\<close>
      using v_prop "&E" by blast
  next
    AOT_have \<open>F \<approx>\<^sub>E G\<close>
      using u_prop[THEN "&E"(1), THEN "&E"(2)]
      using v_prop[THEN "&E"(1), THEN "&E"(2)]
      using "num-tran:2"[THEN "\<rightarrow>E", OF "&I"] by blast
    AOT_thus \<open>[F]\<^sup>-\<^sup>u \<approx>\<^sub>E [G]\<^sup>-\<^sup>v\<close>
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
  then AOT_obtain F where \<open>\<exists>u ([F]u & Numbers(0, F) & Numbers(a, [F]\<^sup>-\<^sup>u))\<close>
    using "\<exists>E"[rotated] by blast
  then AOT_obtain u where \<open>[F]u & Numbers(0, F) & Numbers(a, [F]\<^sup>-\<^sup>u)\<close>
    using "Ordinary.\<exists>E"[rotated] by meson
  AOT_hence \<open>[F]u\<close> and num0_F: \<open>Numbers(0, F)\<close>
    using "&E" "&I" by blast+
  AOT_hence \<open>\<exists>u [F]u\<close>
    using "Ordinary.\<exists>I" by fast
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

AOT_theorem "0-n": \<open>[\<nat>]0\<close>
proof (safe intro!: "nnumber:3"[unvarify x, OF "zero:2", THEN "\<equiv>E"(2)]
    "assume1:5"[unvarify x y, OF "zero:2", OF "zero:2", THEN "\<equiv>E"(2)]
    "\<or>I"(2) "assume1:2"[unvarify x y, OF "zero:2", OF "zero:2", THEN "\<equiv>E"(2)])
  fix u
  AOT_have den: \<open>[\<lambda>x O!x & x =\<^sub>E u]\<down>\<close> by "cqt:2[lambda]"
  AOT_obtain a where a_prop: \<open>Numbers(a, [\<lambda>x O!x & x =\<^sub>E u])\<close>
    using "num:1"[unvarify G, OF den] "\<exists>E"[rotated] by blast
  AOT_have \<open>[\<P>]0a\<close>
  proof (safe intro!: "pred-thm:3"[unvarify x, OF "zero:2", THEN "\<equiv>E"(2)]
                      "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>[\<lambda>x O!x & x =\<^sub>E u]\<guillemotright>\<close>]
                      "Ordinary.\<exists>I"[where \<beta>=u] "&I" den
                      "0F:1"[unvarify F, OF "F-u[den]", unvarify F,
                             OF den, THEN "\<equiv>E"(1)])
    AOT_show \<open>[\<lambda>x [O!]x & x =\<^sub>E u]u\<close>
      by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "&I" "ord=Eequiv:1"[THEN "\<rightarrow>E"]
                       Ordinary.\<psi>)
  next
    AOT_show \<open>Numbers(a,[\<lambda>x [O!]x & x =\<^sub>E u])\<close>
      using a_prop.
  next
    AOT_show \<open>\<not>\<exists>v [[\<lambda>x [O!]x & x =\<^sub>E u]\<^sup>-\<^sup>u]v\<close>
    proof(rule "raa-cor:2")
      AOT_assume \<open>\<exists>v [[\<lambda>x [O!]x & x =\<^sub>E u]\<^sup>-\<^sup>u]v\<close>
      then AOT_obtain v where \<open>[[\<lambda>x [O!]x & x =\<^sub>E u]\<^sup>-\<^sup>u]v\<close>
        using "Ordinary.\<exists>E"[rotated] "&E" by blast
      AOT_hence \<open>[\<lambda>z [\<lambda>x [O!]x & x =\<^sub>E u]z & z \<noteq>\<^sub>E u]v\<close>
        apply (rule "F-u"[THEN "=\<^sub>d\<^sub>fE"(1), where \<tau>\<^sub>1\<tau>\<^sub>n="(_,_)", simplified, rotated])
        by "cqt:2[lambda]"
      AOT_hence \<open>[\<lambda>x [O!]x & x =\<^sub>E u]v & v \<noteq>\<^sub>E u\<close>
        by (rule "\<beta>\<rightarrow>C"(1))
      AOT_hence \<open>v =\<^sub>E u\<close> and \<open>v \<noteq>\<^sub>E u\<close>
        using "\<beta>\<rightarrow>C"(1) "&E" by blast+
      AOT_hence \<open>v =\<^sub>E u & \<not>(v =\<^sub>E u)\<close>
        by (metis "\<equiv>E"(4) "reductio-aa:1" "thm-neg=E")
      AOT_thus \<open>p & \<not>p\<close> for p
        by (metis "raa-cor:1")
    qed
  qed
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
    AOT_show \<open>\<forall>x([\<nat>]x \<rightarrow> \<box>[\<nat>]x)\<close>
      by (simp add: GEN "mod-col-num:1")
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
    then AOT_obtain F where \<open>\<exists>u ([F]u & Numbers(x,F) & Numbers(a,[F]\<^sup>-\<^sup>u))\<close>
      using "\<exists>E"[rotated] by blast
    then AOT_obtain u where \<open>[F]u & Numbers(x,F) & Numbers(a,[F]\<^sup>-\<^sup>u)\<close>
      using "Ordinary.\<exists>E"[rotated] by meson
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
  then AOT_obtain F where \<open>\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    using "\<exists>E"[rotated] by blast
  then AOT_obtain a where
            Oa: \<open>O!a\<close>
    and a_prop: \<open>[F]a & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>a)\<close>
    using "\<exists>E"[rotated] "&E" by blast
  AOT_assume \<open>[\<P>]xz\<close>
  AOT_hence \<open>\<exists>F\<exists>u ([F]u & Numbers(z,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
    using "pred-thm:3"[THEN "\<equiv>E"(1)] by blast
  then AOT_obtain G where \<open>\<exists>u ([G]u & Numbers(z,G) & Numbers(x,[G]\<^sup>-\<^sup>u))\<close>
    using "\<exists>E"[rotated] by blast
  then AOT_obtain b where Ob: \<open>O!b\<close>
                  and b_prop: \<open>[G]b & Numbers(z,G) & Numbers(x,[G]\<^sup>-\<^sup>b)\<close>
    using "\<exists>E"[rotated] "&E" by blast
  AOT_have \<open>[F]\<^sup>-\<^sup>a \<approx>\<^sub>E  [G]\<^sup>-\<^sup>b\<close>
    using "num-tran:2"[unvarify G H, OF "F-u[den]", OF "F-u[den]",
                       THEN "\<rightarrow>E", OF "&I", OF a_prop[THEN "&E"(2)],
                       OF b_prop[THEN "&E"(2)]].
  AOT_hence \<open>F \<approx>\<^sub>E G\<close>
    using "P'-eq"[unconstrain u, THEN "\<rightarrow>E", OF Oa, unconstrain v, THEN "\<rightarrow>E",
                  OF Ob, THEN "\<rightarrow>E", OF "&I", OF "&I"]
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

AOT_theorem being_number_of_den: \<open>[\<lambda>x x = #G]\<down>\<close>
proof (rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E"]; safe intro!: "&I" GEN RN)
  AOT_show \<open>[\<lambda>x Numbers(x,[\<lambda>z \<^bold>\<A>[G]z])]\<down>\<close>
    by (rule numbers_prop_den[unvarify G]) "cqt:2[lambda]"
next
  AOT_modally_strict {
    AOT_show \<open>Numbers(x,[\<lambda>z \<^bold>\<A>[G]z]) \<equiv> x = #G\<close> for x
      using "eq-num:2".
  }
qed

axiomatization \<omega>_nat :: \<open>\<omega> \<Rightarrow> nat\<close> where \<omega>_nat: \<open>surj \<omega>_nat\<close>
text\<open>Unfortunately, since the axiom requires the type @{typ \<omega>}
     to have an infinite domain, @{command nitpick} can only find a potential model
     and no genuine model.
     However, since we could trivially choose @{typ \<omega>} as a copy of @{typ nat},
     we can still be assured that above axiom is consistent.\<close>
lemma \<open>True\<close> nitpick[satisfy, user_axioms, card nat=1, expect = potential] ..

AOT_axiom "modal-axiom":
  \<open>\<exists>x([\<nat>]x & x = #G) \<rightarrow> \<diamond>\<exists>y([E!]y & \<forall>u (\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E y))\<close>
proof(rule AOT_model_axiomI) AOT_modally_strict {
  text\<open>The actual extension on the ordinary objects of a property is the
       set of ordinary urelements that exemplifies the property in the
       designated actual world.\<close>
  define act_\<omega>ext :: \<open><\<kappa>> \<Rightarrow> \<omega> set\<close> where
    \<open>act_\<omega>ext \<equiv> \<lambda> \<Pi> . {x :: \<omega> . [w\<^sub>0 \<Turnstile> [\<Pi>]\<guillemotleft>\<omega>\<kappa> x\<guillemotright>]}\<close>
  text\<open>Encoding a property with infinite actual extension on the ordinary objects
       denotes a property by extended relation comprehension.\<close>
  AOT_have enc_finite_act_\<omega>ext_den:
    \<open>\<^bold>\<turnstile>\<^sub>\<box> [\<lambda>x \<exists>F(\<not>\<guillemotleft>\<epsilon>\<^sub>\<o> w. finite (act_\<omega>ext F)\<guillemotright> & x[F])]\<down>\<close>
  proof(safe intro!: Comprehension_1[THEN "\<rightarrow>E"] RN GEN "\<rightarrow>I")
    AOT_modally_strict {
      fix F G
      AOT_assume \<open>\<box>G \<equiv>\<^sub>E F\<close>
      AOT_hence \<open>\<^bold>\<A>G \<equiv>\<^sub>E F\<close>
        using "nec-imp-act"[THEN "\<rightarrow>E"] by blast
      AOT_hence \<open>\<^bold>\<A>(G\<down> & F\<down> & \<forall>u([G]u \<equiv> [F]u))\<close>
        by (AOT_subst_def (reverse) eqE)
      hence \<open>[w\<^sub>0 \<Turnstile> [G]\<guillemotleft>\<omega>\<kappa> x\<guillemotright>] = [w\<^sub>0 \<Turnstile> [F]\<guillemotleft>\<omega>\<kappa> x\<guillemotright>]\<close> for x
        by (auto dest!: "\<forall>E"(1) "\<rightarrow>E"
                 simp: AOT_model_denotes_\<kappa>_def AOT_sem_denotes AOT_sem_conj
                       AOT_model_\<omega>\<kappa>_ordinary AOT_sem_act AOT_sem_equiv)
      AOT_thus \<open>\<not>\<guillemotleft>\<epsilon>\<^sub>\<o> w. finite (act_\<omega>ext (AOT_term_of_var F))\<guillemotright> \<equiv>
                \<not>\<guillemotleft>\<epsilon>\<^sub>\<o> w. finite (act_\<omega>ext (AOT_term_of_var G))\<guillemotright>\<close>
        by (simp add: AOT_sem_not AOT_sem_equiv act_\<omega>ext_def
                      AOT_model_proposition_choice_simp)
    }
  qed
  text\<open>By coexistence, encoding only properties with finite actual extension
       on the ordinary objects denotes.\<close>
  AOT_have \<open>[\<lambda>x \<forall>F(x[F] \<rightarrow> \<guillemotleft>\<epsilon>\<^sub>\<o> w. finite (act_\<omega>ext F)\<guillemotright>)]\<down>\<close>
  proof(rule "safe-ext"[axiom_inst, THEN "\<rightarrow>E"]; safe intro!: "&I" RN GEN)
    AOT_show \<open>[\<lambda>x \<not>[\<lambda>x \<exists>F(\<not>\<guillemotleft>\<epsilon>\<^sub>\<o> w. finite (act_\<omega>ext F)\<guillemotright> & x[F])]x]\<down>\<close>
      by "cqt:2"
  next
    AOT_modally_strict {
      fix x
      AOT_show \<open>\<not>[\<lambda>x \<exists>F (\<not>\<guillemotleft>\<epsilon>\<^sub>\<o> w. finite (act_\<omega>ext F)\<guillemotright> & x[F])]x \<equiv>
                \<forall>F(x[F] \<rightarrow> \<guillemotleft>\<epsilon>\<^sub>\<o> w. finite (act_\<omega>ext F)\<guillemotright>)\<close>
        by (AOT_subst \<open>[\<lambda>x \<exists>F (\<not>\<guillemotleft>\<epsilon>\<^sub>\<o> w. finite (act_\<omega>ext F)\<guillemotright> & x[F])]x\<close>
                          \<open>\<exists>F (\<not>\<guillemotleft>\<epsilon>\<^sub>\<o> w. finite (act_\<omega>ext F)\<guillemotright> & x[F])\<close>;
            (rule "beta-C-meta"[THEN "\<rightarrow>E"])?)
           (auto simp: enc_finite_act_\<omega>ext_den AOT_sem_equiv AOT_sem_not
                       AOT_sem_forall AOT_sem_imp AOT_sem_conj AOT_sem_exists)
    }
  qed
  text\<open>We show by induction that any property encoded by a natural number
       has a finite actual extension on the ordinary objects.\<close>
  AOT_hence \<open>[\<lambda>x \<forall>F(x[F] \<rightarrow> \<guillemotleft>\<epsilon>\<^sub>\<o> w. finite (act_\<omega>ext F)\<guillemotright>)]n\<close> for n
  proof(rule induction[THEN "\<forall>E"(1), THEN "\<rightarrow>E", THEN "Number.\<forall>E"];
        safe intro!: "&I" "Number.GEN" "\<beta>\<leftarrow>C" "zero:2" "\<rightarrow>I" "cqt:2"
             dest!: "\<beta>\<rightarrow>C")
    AOT_show \<open>\<forall>F(0[F] \<rightarrow> \<guillemotleft>\<epsilon>\<^sub>\<o> w. finite (act_\<omega>ext F)\<guillemotright>)\<close>
    proof(safe intro!: GEN "\<rightarrow>I")
      fix F
      AOT_assume \<open>0[F]\<close>
      AOT_actually {
        AOT_hence \<open>\<not>\<exists>u [F]u\<close>
          using "zero=:2" "intro-elim:3:a" AOT_sem_enc_nec by blast
        AOT_hence \<open>\<forall>x \<not>(O!x & [F]x)\<close>
          using "cqt-further:4" "vdash-properties:10" by blast
        hence \<open>\<not>([w\<^sub>0 \<Turnstile> [F]\<guillemotleft>\<omega>\<kappa> x\<guillemotright>])\<close> for x
          by (auto dest!: "\<forall>E"(1)[where \<tau>=\<open>\<omega>\<kappa> x\<close>]
                    simp: AOT_sem_not AOT_sem_conj AOT_model_\<omega>\<kappa>_ordinary
                          "russell-axiom[exe,1].\<psi>_denotes_asm")
      }
      AOT_thus \<open>\<guillemotleft>\<epsilon>\<^sub>\<o> w. finite (act_\<omega>ext (AOT_term_of_var F))\<guillemotright>\<close>
        by (auto simp: AOT_model_proposition_choice_simp act_\<omega>ext_def)
    qed
  next
    fix n m
    AOT_assume \<open>[\<P>]nm\<close>
    AOT_hence \<open>\<exists>F\<exists>u ([F]u & Numbers(m,F) & Numbers(n,[F]\<^sup>-\<^sup>u))\<close>
      using "pred-thm:3"[THEN "\<equiv>E"(1)] by blast
    then AOT_obtain G where \<open>\<exists>u ([G]u & Numbers(m,G) & Numbers(n,[G]\<^sup>-\<^sup>u))\<close>
      using "\<exists>E"[rotated] by blast
    then AOT_obtain u where 0: \<open>[G]u & Numbers(m,G) & Numbers(n,[G]\<^sup>-\<^sup>u)\<close>
      using "Ordinary.\<exists>E"[rotated] by meson

    AOT_assume n_prop: \<open>\<forall>F(n[F] \<rightarrow> \<guillemotleft>\<epsilon>\<^sub>\<o> w. finite (act_\<omega>ext F)\<guillemotright>)\<close>
    AOT_show \<open>\<forall>F(m[F] \<rightarrow> \<guillemotleft>\<epsilon>\<^sub>\<o> w. finite (act_\<omega>ext F)\<guillemotright>)\<close>
    proof(safe intro!: GEN "\<rightarrow>I")
      fix F
      AOT_assume \<open>m[F]\<close>
      AOT_hence 1: \<open>[\<lambda>x \<^bold>\<A>[F]x] \<approx>\<^sub>E G\<close>
        using 0[THEN "&E"(1), THEN "&E"(2), THEN numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"],
                THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<equiv>E"(1)] by auto
      AOT_show \<open>\<guillemotleft>\<epsilon>\<^sub>\<o> w. finite (act_\<omega>ext (AOT_term_of_var F))\<guillemotright>\<close>
      proof(rule "raa-cor:1")
        AOT_assume \<open>\<not>\<guillemotleft>\<epsilon>\<^sub>\<o> w. finite (act_\<omega>ext (AOT_term_of_var F))\<guillemotright>\<close>
        hence inf: \<open>infinite (act_\<omega>ext (AOT_term_of_var F))\<close>
          by (auto simp: AOT_sem_not AOT_model_proposition_choice_simp)
        then AOT_obtain v where act_F_v: \<open>\<^bold>\<A>[F]v\<close>
          unfolding AOT_sem_act act_\<omega>ext_def
          by (metis AOT_term_of_var_cases AOT_model_\<omega>\<kappa>_ordinary
                    AOT_model_denotes_\<kappa>_def Ordinary.Rep_cases \<kappa>.disc(7)
                    mem_Collect_eq not_finite_existsD)
        AOT_hence \<open>[\<lambda>x \<^bold>\<A>[F]x]v\<close>
          by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2")
        AOT_hence \<open>[\<lambda>x \<^bold>\<A>[F]x]\<^sup>-\<^sup>v \<approx>\<^sub>E [G]\<^sup>-\<^sup>u\<close>
          by (safe intro!: eqP'[unvarify F, THEN "\<rightarrow>E"] "&I" "cqt:2" 1
                           0[THEN "&E"(1), THEN "&E"(1)])
        moreover AOT_have \<open>[\<lambda>x \<^bold>\<A>[F]x]\<^sup>-\<^sup>v \<approx>\<^sub>E [\<lambda>x \<^bold>\<A>[\<lambda>y [F]y & y \<noteq>\<^sub>E v]x]\<close>
        proof(safe intro!: "apE-eqE:1"[unvarify F G, THEN "\<rightarrow>E"] "cqt:2"
                           "F-u[den]"[unvarify F] eqE[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I"
                           Ordinary.GEN)
          fix u
          AOT_have \<open>[\<lambda>x [\<lambda>x \<^bold>\<A>[F]x]x & x \<noteq>\<^sub>E v]u \<equiv> [\<lambda>x \<^bold>\<A>[F]x]u & u \<noteq>\<^sub>E v\<close>
            by (safe intro!: "beta-C-meta"[THEN "\<rightarrow>E"] "cqt:2")
          also AOT_have \<open>[\<lambda>x \<^bold>\<A>[F]x]u & u \<noteq>\<^sub>E v \<equiv> \<^bold>\<A>[F]u & u \<noteq>\<^sub>E v\<close>
            by (AOT_subst \<open>[\<lambda>x \<^bold>\<A>[F]x]u\<close> \<open>\<^bold>\<A>[F]u\<close>)
               (safe intro!: "beta-C-meta"[THEN "\<rightarrow>E"] "cqt:2"
                             "oth-class-taut:3:a")
          also AOT_have \<open>\<^bold>\<A>[F]u & u \<noteq>\<^sub>E v \<equiv> \<^bold>\<A>([F]u & u \<noteq>\<^sub>E v)\<close>
            using "id-act2:2" AOT_sem_conj AOT_sem_equiv AOT_sem_act by auto
          also AOT_have \<open>\<^bold>\<A>([F]u & u \<noteq>\<^sub>E v) \<equiv> \<^bold>\<A>[\<lambda>y [F]y & y \<noteq>\<^sub>E v]u\<close>
            by (AOT_subst \<open>[\<lambda>y [F]y & y \<noteq>\<^sub>E v]u\<close> \<open>[F]u & u \<noteq>\<^sub>E v\<close>)
               (safe intro!: "beta-C-meta"[THEN "\<rightarrow>E"] "cqt:2"
                             "oth-class-taut:3:a")
          also AOT_have \<open>\<^bold>\<A>[\<lambda>y [F]y & y \<noteq>\<^sub>E v]u \<equiv> [\<lambda>x \<^bold>\<A>[\<lambda>y [F]y & y \<noteq>\<^sub>E v]x]u\<close>
            by (safe intro!: "beta-C-meta"[THEN "\<rightarrow>E", symmetric] "cqt:2")
          finally AOT_show \<open>[[\<lambda>x \<^bold>\<A>[F]x]\<^sup>-\<^sup>v]u \<equiv> [\<lambda>x \<^bold>\<A>[\<lambda>y [F]y & y \<noteq>\<^sub>E v]x]u\<close>
            by (auto intro!: "cqt:2"
                     intro: "rule-id-df:2:b"[OF "F-u", where \<tau>\<^sub>1\<tau>\<^sub>n=\<open>(_,_)\<close>, simplified])
        qed
        ultimately AOT_have \<open>[\<lambda>x \<^bold>\<A>[\<lambda>y [F]y & y \<noteq>\<^sub>E v]x] \<approx>\<^sub>E [G]\<^sup>-\<^sup>u\<close>
          using "eq-part:2[terms]" "eq-part:3[terms]" "\<rightarrow>E" by blast
        AOT_hence \<open>n[\<lambda>y [F]y & y \<noteq>\<^sub>E v]\<close>
          by (safe intro!: 0[THEN "&E"(2), THEN numbers[THEN "\<equiv>\<^sub>d\<^sub>fE"],
                THEN "&E"(2), THEN "\<forall>E"(1), THEN "\<equiv>E"(2)] "cqt:2")
        hence finite: \<open>finite (act_\<omega>ext \<guillemotleft>[\<lambda>y [F]y & y \<noteq>\<^sub>E v]\<guillemotright>)\<close>
          by (safe intro!: n_prop[THEN "\<forall>E"(1), THEN "\<rightarrow>E",
                                  simplified AOT_model_proposition_choice_simp]
                           "cqt:2")
        obtain y where y_def: \<open>\<omega>\<kappa> y = AOT_term_of_var (Ordinary.Rep v)\<close>
          by (metis AOT_model_ordinary_\<omega>\<kappa> Ordinary.restricted_var_condition)
        AOT_actually {
          fix x
          AOT_assume \<open>[\<lambda>y [F]y & y \<noteq>\<^sub>E v]\<guillemotleft>\<omega>\<kappa> x\<guillemotright>\<close>
          AOT_hence \<open>[F]\<guillemotleft>\<omega>\<kappa> x\<guillemotright>\<close>
            by (auto dest!: "\<beta>\<rightarrow>C" "&E"(1))
        }
        moreover AOT_actually {
          AOT_have \<open>[F]\<guillemotleft>\<omega>\<kappa> y\<guillemotright>\<close>
            unfolding y_def using act_F_v AOT_sem_act by blast
        }
        moreover AOT_actually {
          fix x
          assume noteq: \<open>x \<noteq> y\<close>
          AOT_assume \<open>[F]\<guillemotleft>\<omega>\<kappa> x\<guillemotright>\<close>
          moreover AOT_have \<omega>\<kappa>_x_den: \<open>\<guillemotleft>\<omega>\<kappa> x\<guillemotright>\<down>\<close>
            using AOT_sem_exe calculation by blast
          moreover {
            AOT_have \<open>\<not>(\<guillemotleft>\<omega>\<kappa> x\<guillemotright> =\<^sub>E v)\<close>
            proof(rule "raa-cor:2")
              AOT_assume \<open>\<guillemotleft>\<omega>\<kappa> x\<guillemotright> =\<^sub>E v\<close>
              AOT_hence \<open>\<guillemotleft>\<omega>\<kappa> x\<guillemotright> = v\<close>
                using "=E-simple:2"[unvarify x, THEN "\<rightarrow>E", OF \<omega>\<kappa>_x_den]
                by blast
              hence \<open>\<omega>\<kappa> x = \<omega>\<kappa> y\<close>
                unfolding y_def AOT_sem_eq
                by meson
              hence \<open>x = y\<close>
                by blast
              AOT_thus \<open>p & \<not>p\<close> for p using noteq by blast
            qed
            AOT_hence \<open>\<guillemotleft>\<omega>\<kappa> x\<guillemotright> \<noteq>\<^sub>E v\<close>
              by (safe intro!: "thm-neg=E"[unvarify x, THEN "\<equiv>E"(2)] \<omega>\<kappa>_x_den)
          }
          ultimately AOT_have \<open>[\<lambda>y [F]y & y \<noteq>\<^sub>E v]\<guillemotleft>\<omega>\<kappa> x\<guillemotright>\<close>
            by (auto intro!: "\<beta>\<leftarrow>C" "cqt:2" "&I")
        }
        ultimately have \<open>(insert y (act_\<omega>ext \<guillemotleft>[\<lambda>y [F]y & y \<noteq>\<^sub>E v]\<guillemotright>)) =
                         (act_\<omega>ext (AOT_term_of_var F))\<close>
          unfolding act_\<omega>ext_def
          by auto
        hence \<open>finite (act_\<omega>ext (AOT_term_of_var F))\<close>
          using finite finite.insertI by metis
        AOT_thus \<open>p & \<not>p\<close> for p
          using inf by blast
      qed
    qed
  qed
  AOT_hence nat_enc_finite: \<open>\<forall>F(n[F] \<rightarrow> \<guillemotleft>\<epsilon>\<^sub>\<o> w. finite (act_\<omega>ext F)\<guillemotright>)\<close> for n
    using "\<beta>\<rightarrow>C"(1) by blast

  text\<open>The main proof can now generate a witness, since we required
       the domain of ordinary objects to be infinite.\<close>
  AOT_show \<open>\<exists>x ([\<nat>]x & x = #G) \<rightarrow> \<diamond>\<exists>y (E!y & \<forall>u (\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E y))\<close>
  proof(safe intro!: "\<rightarrow>I")
    AOT_assume \<open>\<exists>x ([\<nat>]x & x = #G)\<close>
    then AOT_obtain n where \<open>n = #G\<close>
      using "Number.\<exists>E"[rotated] by meson
    AOT_hence \<open>Numbers(n,[\<lambda>x \<^bold>\<A>[G]x])\<close>
      using "eq-num:3" "rule=E" id_sym by fast
    AOT_hence \<open>n[G]\<close>
      by (auto intro!: numbers[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2),
                               THEN "\<forall>E"(2), THEN "\<equiv>E"(2)]
                       "eq-part:1"[unvarify F] "cqt:2")
    AOT_hence \<open>\<guillemotleft>\<epsilon>\<^sub>\<o> w. finite (act_\<omega>ext (AOT_term_of_var G))\<guillemotright>\<close>
      using nat_enc_finite[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
    hence finite: \<open>finite (act_\<omega>ext (AOT_term_of_var G))\<close>
      by (auto simp: AOT_model_proposition_choice_simp)
    AOT_have \<open>\<exists>u \<not>\<^bold>\<A>[G]u\<close>
    proof(rule "raa-cor:1")
      AOT_assume \<open>\<not>\<exists>u \<not>\<^bold>\<A>[G]u\<close>
      AOT_hence \<open>\<forall>x \<not>(O!x & \<not>\<^bold>\<A>[G]x)\<close>
        by (metis "cqt-further:4" "\<rightarrow>E")
      AOT_hence \<open>\<^bold>\<A>[G]x\<close> if \<open>O!x\<close> for x
        using "\<forall>E"(2) AOT_sem_conj AOT_sem_not that by blast
      hence \<open>[w\<^sub>0 \<Turnstile> [G]\<guillemotleft>\<omega>\<kappa> x\<guillemotright>]\<close> for x
        by (metis AOT_term_of_var_cases AOT_model_\<omega>\<kappa>_ordinary
                  AOT_model_denotes_\<kappa>_def AOT_sem_act \<kappa>.disc(7)) 
      hence \<open>(act_\<omega>ext (AOT_term_of_var G)) = UNIV\<close>
        unfolding act_\<omega>ext_def by auto
      moreover have \<open>infinite (UNIV::\<omega> set)\<close>
        by (metis \<omega>_nat finite_imageI infinite_UNIV_char_0)
      ultimately have \<open>infinite (act_\<omega>ext (AOT_term_of_var G))\<close>
        by simp
      AOT_thus \<open>p & \<not>p\<close> for p using finite by blast
    qed
    then AOT_obtain x where x_prop: \<open>O!x & \<not>\<^bold>\<A>[G]x\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>\<diamond>E!x\<close>
      by (metis "betaC:1:a" "con-dis-i-e:2:a" AOT_sem_ordinary)
    moreover AOT_have \<open>\<box>\<forall>u (\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E x)\<close>
    proof(safe intro!: RN GEN "\<rightarrow>I")
      AOT_modally_strict {
        fix y
        AOT_assume \<open>O!y\<close>
        AOT_assume 0: \<open>\<^bold>\<A>[G]y\<close>
        AOT_show \<open>y \<noteq>\<^sub>E x\<close>
        proof (safe intro!: "thm-neg=E"[THEN "\<equiv>E"(2)] "raa-cor:2")
          AOT_assume \<open>y =\<^sub>E x\<close>
          AOT_hence \<open>y = x\<close>
            by (metis "=E-simple:2" "vdash-properties:10")
          hence \<open>y = x\<close>
            by (simp add: AOT_sem_eq AOT_term_of_var_inject)
          AOT_hence \<open>\<not>\<^bold>\<A>[G]y\<close>
            using x_prop "&E" AOT_sem_not AOT_sem_act by metis
          AOT_thus \<open>\<^bold>\<A>[G]y & \<not>\<^bold>\<A>[G]y\<close>
            using 0 "&I" by blast
        qed
      }
    qed
    ultimately AOT_have \<open>\<diamond>(\<forall>u (\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E x) & E!x)\<close>
      using "KBasic:16"[THEN "\<rightarrow>E", OF "&I"] by blast
    AOT_hence \<open>\<diamond>(E!x & \<forall>u (\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E x))\<close>
      by (AOT_subst \<open>E!x & \<forall>u (\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E x)\<close> \<open>\<forall>u (\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E x) & E!x\<close>)
         (auto simp: "oth-class-taut:2:a")
    AOT_hence \<open>\<exists>y \<diamond>(E!y & \<forall>u (\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E y))\<close>
      using "\<exists>I" by fast
    AOT_thus \<open>\<diamond>\<exists>y (E!y & \<forall>u (\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E y))\<close>
      using "CBF\<diamond>"[THEN "\<rightarrow>E"] by fast
  qed
} qed

AOT_theorem "modal-lemma":
  \<open>\<diamond>\<forall>u(\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E v) \<rightarrow> \<forall>u(\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E v)\<close>
proof(safe intro!: "\<rightarrow>I" Ordinary.GEN)
  AOT_modally_strict {
    fix u
    AOT_assume act_Gu: \<open>\<^bold>\<A>[G]u\<close>
    AOT_have \<open>\<forall>u (\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E v) \<rightarrow> u \<noteq>\<^sub>E v\<close>
    proof(rule "\<rightarrow>I")
      AOT_assume \<open>\<forall>u (\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E v)\<close>
      AOT_hence \<open>\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E v\<close>
        using "Ordinary.\<forall>E" by fast
      AOT_thus \<open>u \<noteq>\<^sub>E v\<close>
        using act_Gu "\<rightarrow>E" by blast
    qed
  } note 0 = this
  AOT_have \<theta>: \<open>\<box>(\<forall>u (\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E v) \<rightarrow> u \<noteq>\<^sub>E v)\<close> if \<open>\<box>\<^bold>\<A>[G]u\<close> for u
  proof -
    AOT_have \<open>\<box>\<^bold>\<A>[G]u \<rightarrow> \<box>(\<forall>u (\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E v) \<rightarrow> u \<noteq>\<^sub>E v)\<close>
      apply (rule RM) using 0 "&E" "\<rightarrow>I" by blast
    thus ?thesis using that "\<rightarrow>E" by blast
  qed
  fix u
  AOT_assume 1: \<open>\<diamond>\<forall>u(\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E v)\<close>
  AOT_assume \<open>\<^bold>\<A>[G]u\<close>
  AOT_hence \<open>\<box>\<^bold>\<A>[G]u\<close>
    by (metis "Act-Basic:6" "\<equiv>E"(1))
  AOT_hence \<open>\<box>(\<forall>u (\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E v) \<rightarrow> u \<noteq>\<^sub>E v)\<close>
    using Ordinary.\<psi> \<theta> by blast
  AOT_hence \<open>\<diamond>u \<noteq>\<^sub>E v\<close>
    using 1 "K\<diamond>"[THEN "\<rightarrow>E", THEN "\<rightarrow>E"] by blast
  AOT_thus \<open>u \<noteq>\<^sub>E v\<close>
    by (metis "id-nec4:2" "\<equiv>E"(1)) 
qed

AOT_theorem "th-succ": \<open>\<forall>n\<exists>!m [\<P>]nm\<close>
proof(safe intro!: Number.GEN "\<rightarrow>I" "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"])
  fix n
  AOT_have \<open>NaturalCardinal(n)\<close>
    by (metis "nat-card" Number.\<psi> "\<rightarrow>E")
  AOT_hence \<open>\<exists>G(n = #G)\<close>
    by (metis "\<equiv>\<^sub>d\<^sub>fE" card)
  then AOT_obtain G where n_num_G: \<open>n = #G\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<open>\<exists>n (n = #G)\<close>
    by (rule "Number.\<exists>I")
  AOT_hence \<open>\<diamond>\<exists>y ([E!]y & \<forall>u(\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E y))\<close>
    using "modal-axiom"[axiom_inst, THEN "\<rightarrow>E"] by blast
  AOT_hence \<open>\<exists>y \<diamond>([E!]y & \<forall>u(\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E y))\<close>
    using "BF\<diamond>"[THEN "\<rightarrow>E"] by auto
  then AOT_obtain y where \<open>\<diamond>([E!]y & \<forall>u(\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E y))\<close>
    using "\<exists>E"[rotated] by blast
  AOT_hence \<open>\<diamond>E!y\<close> and 2: \<open>\<diamond>\<forall>u(\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E y)\<close>
    using "KBasic2:3" "&E" "\<rightarrow>E" by blast+
  AOT_hence Oy: \<open>O!y\<close>
    by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" intro: AOT_ordinary[THEN "=\<^sub>d\<^sub>fI"(2)])
  AOT_have 0: \<open>\<forall>u(\<^bold>\<A>[G]u \<rightarrow> u \<noteq>\<^sub>E y)\<close>
    using 2 "modal-lemma"[unconstrain v, THEN "\<rightarrow>E", OF Oy, THEN "\<rightarrow>E"] by simp
  AOT_have 1: \<open>[\<lambda>x \<^bold>\<A>[G]x \<or> x =\<^sub>E y]\<down>\<close>
    by "cqt:2"
  AOT_obtain b where b_prop: \<open>Numbers(b, [\<lambda>x \<^bold>\<A>[G]x \<or> x =\<^sub>E y])\<close>
    using "num:1"[unvarify G, OF 1] "\<exists>E"[rotated] by blast
  AOT_have Pnb: \<open>[\<P>]nb\<close>
  proof(safe intro!: "pred-thm:3"[THEN "\<equiv>E"(2)]
                     "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>[\<lambda>x \<^bold>\<A>[G]x \<or> x =\<^sub>E y]\<guillemotright>\<close>]
                     1 "\<exists>I"(2)[where \<beta>=y] "&I" Oy b_prop)
    AOT_show \<open>[\<lambda>x \<^bold>\<A>[G]x \<or> x =\<^sub>E y]y\<close>
      by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2" "\<or>I"(2)
                       "ord=Eequiv:1"[THEN "\<rightarrow>E", OF Oy])
  next
    AOT_have equinum: \<open>[\<lambda>x \<^bold>\<A>[G]x \<or> x =\<^sub>E y]\<^sup>-\<^sup>y \<approx>\<^sub>E [\<lambda>x \<^bold>\<A>[G]x]\<close>
    proof(rule "apE-eqE:1"[unvarify F G, THEN "\<rightarrow>E"];
          ("cqt:2[lambda]" | rule "F-u[den]"[unvarify F]; "cqt:2[lambda]")?)
      AOT_show \<open>[\<lambda>x \<^bold>\<A>[G]x \<or> x =\<^sub>E y]\<^sup>-\<^sup>y \<equiv>\<^sub>E [\<lambda>x \<^bold>\<A>[G]x]\<close>
      proof (safe intro!: eqE[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "F-u[den]"[unvarify F]
                          Ordinary.GEN "\<rightarrow>I"; "cqt:2"?)
        fix u
        AOT_have \<open>[[\<lambda>x \<^bold>\<A>[G]x \<or> [(=\<^sub>E)]xy]\<^sup>-\<^sup>y]u \<equiv> ([\<lambda>x \<^bold>\<A>[G]x \<or> x =\<^sub>E y]u) & u \<noteq>\<^sub>E y\<close>
          apply (rule "F-u"[THEN "=\<^sub>d\<^sub>fI"(1)[where \<tau>\<^sub>1\<tau>\<^sub>n=\<open>(_,_)\<close>], simplified]; "cqt:2"?)
          by (rule "beta-C-cor:2"[THEN "\<rightarrow>E", THEN "\<forall>E"(2)]; "cqt:2")
        also AOT_have \<open>\<dots> \<equiv>  (\<^bold>\<A>[G]u \<or> u =\<^sub>E y) & u \<noteq>\<^sub>E y\<close>
          apply (AOT_subst \<open>[\<lambda>x \<^bold>\<A>[G]x \<or> [(=\<^sub>E)]xy]u\<close> \<open>\<^bold>\<A>[G]u \<or> u =\<^sub>E y\<close>)
           apply (rule "beta-C-cor:2"[THEN "\<rightarrow>E", THEN "\<forall>E"(2)]; "cqt:2")
          using "oth-class-taut:3:a" by blast
        also AOT_have \<open>\<dots> \<equiv> \<^bold>\<A>[G]u\<close>
        proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
          AOT_assume \<open>(\<^bold>\<A>[G]u \<or> u =\<^sub>E y) & u \<noteq>\<^sub>E y\<close>
          AOT_thus \<open>\<^bold>\<A>[G]u\<close>
            by (metis "&E"(1) "&E"(2) "\<or>E"(3) "\<equiv>E"(1) "thm-neg=E")
        next
          AOT_assume \<open>\<^bold>\<A>[G]u\<close>
          AOT_hence \<open>u \<noteq>\<^sub>E y\<close> and \<open>\<^bold>\<A>[G]u \<or> u =\<^sub>E y\<close>
            using 0[THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF Ordinary.\<psi>, THEN "\<rightarrow>E"]
                  "\<or>I" by blast+
          AOT_thus \<open>(\<^bold>\<A>[G]u \<or> u =\<^sub>E y) & u \<noteq>\<^sub>E y\<close>
            using "&I" by simp
        qed
        also AOT_have \<open>\<dots> \<equiv> [\<lambda>x \<^bold>\<A>[G]x]u\<close>
          by (rule "beta-C-cor:2"[THEN "\<rightarrow>E", THEN "\<forall>E"(2), symmetric]; "cqt:2")
        finally AOT_show \<open>[[\<lambda>x \<^bold>\<A>[G]x \<or> [(=\<^sub>E)]xy]\<^sup>-\<^sup>y]u \<equiv> [\<lambda>x \<^bold>\<A>[G]x]u\<close>.
      qed
    qed
    AOT_have 2: \<open>[\<lambda>x \<^bold>\<A>[G]x]\<down>\<close> by "cqt:2[lambda]"
    AOT_show \<open>Numbers(n,[\<lambda>x \<^bold>\<A>[G]x \<or> x =\<^sub>E y]\<^sup>-\<^sup>y)\<close>
      using "num-tran:1"[unvarify G H, OF 2, OF "F-u[den]"[unvarify F, OF 1],
                       THEN "\<rightarrow>E", OF equinum, THEN "\<equiv>E"(2),
                       OF "eq-num:2"[THEN "\<equiv>E"(2), OF n_num_G]].
  qed
  AOT_show \<open>\<exists>\<alpha> ([\<nat>]\<alpha> & [\<P>]n\<alpha> & \<forall>\<beta> ([\<nat>]\<beta> & [\<P>]n\<beta> \<rightarrow> \<beta> = \<alpha>))\<close>
  proof(safe intro!: "\<exists>I"(2)[where \<beta>=b] "&I" Pnb "\<rightarrow>I" GEN)
    AOT_show \<open>[\<nat>]b\<close> using "suc-num:1"[THEN "\<rightarrow>E", OF Pnb].
  next
    fix y
    AOT_assume 0: \<open>[\<nat>]y & [\<P>]ny\<close>
    AOT_show \<open>y = b\<close>
      apply (rule "pred-func:1"[THEN "\<rightarrow>E"])
      using 0[THEN "&E"(2)] Pnb "&I" by blast
  qed
qed

(* Note the use of a bold '. *)
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

AOT_theorem "prec-facts:1": \<open>[\<P>]0 1\<close>
  by (auto intro: "numerals:1"[THEN "rule-id-df:2:b[zero]",
                               OF "def-suc[den2]"[unconstrain n, unvarify \<beta>,
                                                  OF "zero:2", THEN "\<rightarrow>E", OF "0-n"]]
                  "suc-thm"[unconstrain n, unvarify \<beta>, OF "zero:2",
                            THEN "\<rightarrow>E", OF "0-n"])

(* TODO: more theorems *)

(* Note: we forgo restricted variables for natural cardinals. *)
AOT_define Finite :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>Finite'(_')\<close>)
  "inf-card:1": \<open>Finite(x) \<equiv>\<^sub>d\<^sub>f NaturalCardinal(x) & [\<nat>]x\<close>
AOT_define Infinite :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>Infinite'(_')\<close>)
  "inf-card:2": \<open>Infinite(x) \<equiv>\<^sub>d\<^sub>f NaturalCardinal(x) & \<not>Finite(x)\<close>

AOT_theorem "inf-card-exist:1": \<open>NaturalCardinal(#O!)\<close>
  by (safe intro!: card[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>O!\<guillemotright>\<close>] "=I"
                   "num-def:2"[unvarify G] "oa-exist:1")

AOT_theorem "inf-card-exist:2": \<open>Infinite(#O!)\<close>
proof (safe intro!: "inf-card:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "inf-card-exist:1")
  AOT_show \<open>\<not>Finite(#O!)\<close>
  proof(rule "raa-cor:2")
    AOT_assume \<open>Finite(#O!)\<close>
    AOT_hence 0: \<open>[\<nat>]#O!\<close>
      using "inf-card:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E"(2) by blast
    AOT_have \<open>Numbers(#O!, [\<lambda>z \<^bold>\<A>O!z])\<close>
      using "eq-num:3"[unvarify G, OF "oa-exist:1"].
    AOT_hence \<open>#O! = #O!\<close>
      using "eq-num:2"[unvarify x G, THEN "\<equiv>E"(1), OF "oa-exist:1",
                       OF "num-def:2"[unvarify G], OF "oa-exist:1"]
      by blast
    AOT_hence \<open>[\<nat>]#O! & #O! = #O!\<close>
      using 0 "&I" by blast
    AOT_hence \<open>\<exists>x ([\<nat>]x & x = #O!)\<close>
      using "num-def:2"[unvarify G, OF "oa-exist:1"] "\<exists>I"(1) by fast
    AOT_hence \<open>\<diamond>\<exists>y ([E!]y & \<forall>u (\<^bold>\<A>[O!]u \<rightarrow> u \<noteq>\<^sub>E y))\<close>
      using "modal-axiom"[axiom_inst, unvarify G, THEN "\<rightarrow>E", OF "oa-exist:1"] by blast
    AOT_hence \<open>\<exists>y \<diamond>([E!]y & \<forall>u (\<^bold>\<A>[O!]u \<rightarrow> u \<noteq>\<^sub>E y))\<close>
      using "BF\<diamond>"[THEN "\<rightarrow>E"] by blast
    then AOT_obtain b where \<open>\<diamond>([E!]b & \<forall>u (\<^bold>\<A>[O!]u \<rightarrow> u \<noteq>\<^sub>E b))\<close>
      using "\<exists>E"[rotated] by blast
    AOT_hence \<open>\<diamond>[E!]b\<close> and 2: \<open>\<diamond>\<forall>u (\<^bold>\<A>[O!]u \<rightarrow> u \<noteq>\<^sub>E b)\<close>
      using "KBasic2:3"[THEN "\<rightarrow>E"] "&E" by blast+
    AOT_hence \<open>[\<lambda>x \<diamond>[E!]x]b\<close>
      by (auto intro!: "\<beta>\<leftarrow>C"(1) "cqt:2")
    moreover AOT_have \<open>O! = [\<lambda>x \<diamond>[E!]x]\<close>
      by (rule "rule-id-df:1[zero]"[OF "oa:1"]) "cqt:2"
    ultimately AOT_have b_ord: \<open>O!b\<close>
      using "rule=E" id_sym by fast
    AOT_hence \<open>\<^bold>\<A>O!b\<close>
      by (meson "\<equiv>E"(1) "oa-facts:7")
    moreover AOT_have 2: \<open>\<forall>u (\<^bold>\<A>[O!]u \<rightarrow> u \<noteq>\<^sub>E b)\<close>
      using "modal-lemma"[unvarify G, unconstrain v, OF "oa-exist:1",
                          THEN "\<rightarrow>E", OF b_ord, THEN "\<rightarrow>E", OF 2].
    ultimately AOT_have \<open>b \<noteq>\<^sub>E b\<close>
      using "Ordinary.\<forall>E"[OF 2, unconstrain \<alpha>, THEN "\<rightarrow>E",
                          OF b_ord, THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>\<not>(b =\<^sub>E b)\<close>
      by (metis "\<equiv>E"(1) "thm-neg=E")
    moreover AOT_have \<open>b =\<^sub>E b\<close>
      using "ord=Eequiv:1"[THEN "\<rightarrow>E", OF b_ord].
    ultimately AOT_show \<open>p & \<not>p\<close> for p
      by (metis "raa-cor:3")
  qed
qed



(*<*)
end
(*>*)
