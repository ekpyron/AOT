theory AOT_NaturalNumbers
  imports AOT_PLM AOT_PossibleWorlds
  abbrevs one-to-one = \<open>\<^sub>1\<^sub>-\<^sub>1\<close>
      and onto = \<open>\<^sub>o\<^sub>n\<^sub>t\<^sub>o\<close>
begin
 
AOT_define one_one_cor :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>_ |: _ \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> _\<close>)
  one_one_cor: \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> G \<equiv>\<^sub>d\<^sub>f R\<down> & F\<down> & G\<down> &
                                   \<forall>x ([F]x \<rightarrow> \<exists>!y([G]y & [R]xy)) &
                                   \<forall>y ([G]y \<rightarrow> \<exists>!x([F]x & [R]xy))\<close>

AOT_define fFG_1 :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>_ |: _ \<longrightarrow> _\<close>)
  fFG_1: \<open>R |: F \<longrightarrow> G \<equiv>\<^sub>d\<^sub>f R\<down> & F\<down> & G\<down> & \<forall>x ([F]x \<rightarrow> \<exists>!y([G]y & [R]xy))\<close>

AOT_define fFG_2 :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>_ |: _ \<^sub>1\<^sub>-\<^sub>1\<longrightarrow> _\<close>)
  fFG_2: \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow> G \<equiv>\<^sub>d\<^sub>f R |: F \<longrightarrow> G & \<forall>x\<forall>y\<forall>z (([F]x & [F]y & [G]z) \<rightarrow> ([R]xz & [R]yz \<rightarrow> x = y))\<close>

AOT_define fFG_3 :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>_ |: _ \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>o _\<close>)
  fFG_3: \<open>R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>o G \<equiv>\<^sub>d\<^sub>f R |: F \<longrightarrow> G & \<forall>y ([G]y \<rightarrow> \<exists>x([F]x & [R]xy))\<close>

AOT_define fFG_4 :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>_ |: _ \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>o _\<close>)
  fFG_4: \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>o G \<equiv>\<^sub>d\<^sub>f R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow> G & R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>o G\<close>

AOT_theorem eq_1_1: \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> G \<equiv> R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>o G\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> G\<close>
  AOT_hence A: \<open>\<forall>x ([F]x \<rightarrow> \<exists>!y([G]y & [R]xy))\<close> and B: \<open>\<forall>y ([G]y \<rightarrow> \<exists>!x([F]x & [R]xy))\<close>
    using "\<equiv>\<^sub>d\<^sub>fE"[OF one_one_cor] "&E" by blast+
  AOT_have C: \<open>R |: F \<longrightarrow> G\<close>
  proof (rule "\<equiv>\<^sub>d\<^sub>fI"[OF fFG_1]; rule "&I")
    AOT_show \<open>R\<down> & F\<down> & G\<down>\<close> using cqt_2_const_var[axiom_inst] "&I" by metis
  next
    AOT_show \<open>\<forall>x ([F]x \<rightarrow> \<exists>!y([G]y & [R]xy))\<close> by (rule A)
  qed
  AOT_show \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>o G\<close>
  proof (rule "\<equiv>\<^sub>d\<^sub>fI"[OF fFG_4]; rule "&I")
    AOT_show \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow> G\<close>
    proof (rule "\<equiv>\<^sub>d\<^sub>fI"[OF fFG_2]; rule "&I")
      AOT_show \<open>R |: F \<longrightarrow> G\<close> using C.
    next
      AOT_show \<open>\<forall>x\<forall>y\<forall>z ([F]x & [F]y & [G]z \<rightarrow> ([R]xz & [R]yz \<rightarrow> x = y))\<close>
      proof(rule GEN; rule GEN; rule GEN; rule "\<rightarrow>I"; rule "\<rightarrow>I")
        fix x y z
        AOT_assume 1: \<open>[F]x & [F]y & [G]z\<close>
        moreover AOT_assume 2: \<open>[R]xz & [R]yz\<close>
        ultimately AOT_have 3: \<open>\<exists>!x ([F]x & [R]xz)\<close> using B "&E" "\<forall>E" "\<rightarrow>E" by fast
        AOT_show \<open>x = y\<close>
          by (rule uni_most[THEN "\<rightarrow>E", OF 3, THEN "\<forall>E"(2)[where \<beta>=x],
                            THEN "\<forall>E"(2)[where \<beta>=y], THEN "\<rightarrow>E"])
             (metis "&I" "&E" 1 2)
      qed
    qed
  next
    AOT_show \<open>R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>o G\<close>
    proof (rule "\<equiv>\<^sub>d\<^sub>fI"[OF fFG_3]; rule "&I")
      AOT_show \<open>R |: F \<longrightarrow> G\<close> using C.
    next
      AOT_show \<open>\<forall>y ([G]y \<rightarrow> \<exists>x ([F]x & [R]xy))\<close>
      proof(rule GEN; rule "\<rightarrow>I")
        fix y
        AOT_assume \<open>[G]y\<close>
        AOT_hence \<open>\<exists>!x ([F]x & [R]xy)\<close> using B[THEN "\<forall>E"(2), THEN "\<rightarrow>E"] by blast
        AOT_hence \<open>\<exists>x ([F]x & [R]xy & \<forall>\<beta> (([F]\<beta> & [R]\<beta>y) \<rightarrow> \<beta> = x))\<close>
          using uniqueness_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
        then AOT_obtain x where \<open>[F]x & [R]xy\<close> using "\<exists>E"[rotated] "&E" by blast
        AOT_thus \<open>\<exists>x ([F]x & [R]xy)\<close> by (rule "\<exists>I")
      qed
    qed
  qed
next
  AOT_assume \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>o G\<close>
  AOT_hence \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow> G\<close> and \<open>R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>o G\<close> using "\<equiv>\<^sub>d\<^sub>fE"[OF fFG_4] "&E" by blast+
  AOT_hence C: \<open>R |: F \<longrightarrow> G\<close>
    and D: \<open>\<forall>x\<forall>y\<forall>z ([F]x & [F]y & [G]z \<rightarrow> ([R]xz & [R]yz \<rightarrow> x = y))\<close>
    and E: \<open>\<forall>y ([G]y \<rightarrow> \<exists>x ([F]x & [R]xy))\<close>
    using "\<equiv>\<^sub>d\<^sub>fE"[OF fFG_2] "\<equiv>\<^sub>d\<^sub>fE"[OF fFG_3] "&E" by blast+
  AOT_show \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> G\<close>
  proof(rule one_one_cor[THEN "\<equiv>\<^sub>d\<^sub>fI"]; safe intro!: "&I" cqt_2_const_var[axiom_inst])
    AOT_show \<open>\<forall>x ([F]x \<rightarrow> \<exists>!y ([G]y & [R]xy))\<close>
      using "\<equiv>\<^sub>d\<^sub>fE"[OF fFG_1, OF C] "&E" by blast
  next
    AOT_show \<open>\<forall>y ([G]y \<rightarrow> \<exists>!x ([F]x & [R]xy))\<close>
    proof (rule "GEN"; rule "\<rightarrow>I")
      fix y
      AOT_assume 0: \<open>[G]y\<close>
      AOT_hence \<open>\<exists>x ([F]x & [R]xy)\<close> using E "\<forall>E" "\<rightarrow>E" by fast
      then AOT_obtain a where a_prop: \<open>[F]a & [R]ay\<close> using "\<exists>E"[rotated] by blast
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
        using uniqueness_1[THEN "\<equiv>\<^sub>d\<^sub>fI"] by fast
    qed
  qed
qed


AOT_register_restricted_type
  Ordinary: \<open>O!\<kappa>\<close>
proof
  AOT_modally_strict {
    AOT_show \<open>\<exists>x O!x\<close>
      by (meson "B\<diamond>" T_S5_fund_1 o_objects_exist_1 vdash_properties_10)
  }
next
  AOT_modally_strict {
    AOT_show \<open>O!\<kappa> \<rightarrow> \<kappa>\<down>\<close> for \<kappa>
      by (simp add: deduction_theorem russell_axiom_exe_1.\<psi>_denotes_asm)
  }
qed
AOT_register_variable_names
  Ordinary: u v r t s

context AOT_restriction_condition
begin
end

AOT_theorem equi_1: \<open>\<exists>!u \<phi>{u} \<equiv>\<^sub>d\<^sub>f \<exists>u (\<phi>{u} & \<forall>v (\<phi>{v} \<rightarrow> v =\<^sub>E u))\<close>
proof(rule AOT_sem_equiv_defI) (* NOTE: appeal to semantics to accommodate PLMs double definition *)
  AOT_modally_strict {
    AOT_assume \<open>\<exists>!u \<phi>{u}\<close>
    AOT_hence \<open>\<exists>!x (O!x & \<phi>{x})\<close>.
    AOT_hence \<open>\<exists>x (O!x & \<phi>{x} & \<forall>\<beta> (O!\<beta> & \<phi>{\<beta>} \<rightarrow> \<beta> = x))\<close>
      using uniqueness_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
    then AOT_obtain x where x_prop: \<open>O!x & \<phi>{x} & \<forall>\<beta> (O!\<beta> & \<phi>{\<beta>} \<rightarrow> \<beta> = x)\<close> using "\<exists>E"[rotated] by blast
    {
      fix \<beta>
      AOT_assume beta_ord: \<open>O!\<beta>\<close>
      moreover AOT_assume \<open>\<phi>{\<beta>}\<close>
      ultimately AOT_have \<open>\<beta> = x\<close> using x_prop[THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=\<beta>]] "&I" "\<rightarrow>E" by blast
      AOT_hence \<open>\<beta> =\<^sub>E x\<close>
        using ord_eq_E_eq[THEN "\<rightarrow>E", OF "\<or>I"(1)[OF beta_ord], THEN qml_2[axiom_inst, THEN "\<rightarrow>E"], THEN "\<equiv>E"(1)]
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
  }
next
  AOT_modally_strict {
    AOT_assume \<open>\<exists>u (\<phi>{u} & \<forall>v (\<phi>{v} \<rightarrow> v =\<^sub>E u))\<close>
    AOT_hence \<open>\<exists>x (O!x & (\<phi>{x} & \<forall>y (O!y \<rightarrow> (\<phi>{y} \<rightarrow> y =\<^sub>E x))))\<close>
      by blast
    then AOT_obtain x where x_prop: \<open>O!x & (\<phi>{x} & \<forall>y (O!y \<rightarrow> (\<phi>{y} \<rightarrow> y =\<^sub>E x)))\<close>
      using "\<exists>E"[rotated] by blast
    AOT_have \<open>\<forall>y ([O!]y & \<phi>{y} \<rightarrow> y = x)\<close>
    proof(rule GEN; rule "\<rightarrow>I")
      fix y
      AOT_assume \<open>O!y & \<phi>{y}\<close>
      AOT_hence \<open>y =\<^sub>E x\<close> using x_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=y]]
        using "\<rightarrow>E" "&E" by blast
      AOT_thus \<open>y = x\<close>
        using ord_eq_E_eq[THEN "\<rightarrow>E", OF "\<or>I"(2)[OF x_prop[THEN "&E"(1)]], THEN qml_2[axiom_inst, THEN "\<rightarrow>E"], THEN "\<equiv>E"(2)] by blast
    qed
    AOT_hence \<open>[O!]x & \<phi>{x} & \<forall>y ([O!]y & \<phi>{y} \<rightarrow> y = x)\<close> using x_prop "&E" "&I" by meson
    AOT_hence \<open>\<exists>x ([O!]x & \<phi>{x} & \<forall>y ([O!]y & \<phi>{y} \<rightarrow> y = x))\<close> by (rule "\<exists>I")
    AOT_hence \<open>\<exists>!x (O!x & \<phi>{x})\<close>
      by (rule uniqueness_1[THEN "\<equiv>\<^sub>d\<^sub>fI"])
    AOT_thus \<open>\<exists>!u \<phi>{u}\<close>.
  }
qed

AOT_define equi_2 :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>_ |: _ \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E _\<close>)
  equi_2: \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G \<equiv>\<^sub>d\<^sub>f R\<down> & F\<down> & G\<down> &
                               \<forall>u ([F]u \<rightarrow> \<exists>!v([G]v & [R]uv)) &
                               \<forall>v ([G]v \<rightarrow> \<exists>!u([F]u & [R]uv))\<close>

AOT_define equi_3 :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl "\<approx>\<^sub>E" 50)
  equi_3: \<open>F \<approx>\<^sub>E G \<equiv>\<^sub>d\<^sub>f \<exists>R (R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G)\<close>

AOT_theorem eq_part_1: \<open>F \<approx>\<^sub>E F\<close>
proof (safe intro!: "&I" GEN "\<rightarrow>I" cqt_2_const_var[axiom_inst] "\<equiv>\<^sub>d\<^sub>fI"[OF equi_3] "\<equiv>\<^sub>d\<^sub>fI"[OF equi_2] "\<exists>I"(1))
  fix x
  AOT_assume 1: \<open>O!x\<close>
  AOT_assume 2: \<open>[F]x\<close>
  AOT_show \<open>\<exists>!v ([F]v & x =\<^sub>E v)\<close>
  proof(rule equi_1[THEN "\<equiv>\<^sub>d\<^sub>fI"]; rule "\<exists>I"(2)[where \<beta>=x]; safe dest!: "&E"(2) intro!:  "&I" "\<rightarrow>I" 1 2 GEN ord_eq_Eequiv_1[THEN "\<rightarrow>E", OF 1])
    AOT_show \<open>v =\<^sub>E x\<close> if \<open>x =\<^sub>E v\<close> for v
      by (metis that ord_eq_Eequiv_2[THEN "\<rightarrow>E"])
  qed
next
  fix y
  AOT_assume 1: \<open>O!y\<close>
  AOT_assume 2: \<open>[F]y\<close>
  AOT_show \<open>\<exists>!u ([F]u & u =\<^sub>E y)\<close>
    by(safe dest!: "&E"(2) intro!: equi_1[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(2)[where \<beta>=y]
            "&I" "\<rightarrow>I" 1 2 GEN ord_eq_Eequiv_1[THEN "\<rightarrow>E", OF 1])
qed(auto simp: eq_E_denotes)

AOT_theorem eq_part_2: \<open>F \<approx>\<^sub>E G \<rightarrow> G \<approx>\<^sub>E F\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>F \<approx>\<^sub>E G\<close>
  AOT_hence \<open>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close> using equi_3[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain R where \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close> using "\<exists>E"[rotated] by blast
  AOT_hence 0: \<open>R\<down> & F\<down> & G\<down> & \<forall>u ([F]u \<rightarrow> \<exists>!v([G]v & [R]uv)) &
                            \<forall>v ([G]v \<rightarrow> \<exists>!u([F]u & [R]uv))\<close> using equi_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast

  AOT_have \<open>[\<lambda>xy [R]yx]\<down> & G\<down> & F\<down> & \<forall>u ([G]u \<rightarrow> \<exists>!v([F]v & [\<lambda>xy [R]yx]uv)) &
                            \<forall>v ([F]v \<rightarrow> \<exists>!u([G]u & [\<lambda>xy [R]yx]uv))\<close>
  proof (AOT_subst \<open>\<lambda> \<kappa> \<kappa>' . \<guillemotleft>[\<lambda>xy [R]yx]\<kappa>\<kappa>'\<guillemotright>\<close> \<open>\<lambda> \<kappa> \<kappa>' . \<guillemotleft>[R]\<kappa>'\<kappa>\<guillemotright>\<close>;
         (safe intro!: "&I" cqt_2_const_var[axiom_inst] 0[THEN "&E"(2)] 0[THEN "&E"(1), THEN "&E"(2)]; cqt_2_lambda)?)
    AOT_modally_strict {
      AOT_have \<open>[\<lambda>xy [R]yx]xy\<close> if \<open>[R]yx\<close> for y x
        by(rule betaC_2_a; cqt_2_lambda ; simp add: con_dis_i_e_1 ex_1_a prod_denotesI rule_ui_3 that)
      moreover AOT_have \<open>[R]yx\<close> if \<open>[\<lambda>xy [R]yx]xy\<close> for y x
        using betaC_1_a[where \<phi>="\<lambda>(x,y). _ (x,y)" and \<kappa>\<^sub>1\<kappa>\<^sub>n="(_,_)", simplified, OF that, simplified].
      ultimately AOT_show \<open>[\<lambda>xy [R]yx]\<alpha>\<beta> \<equiv> [R]\<beta>\<alpha>\<close> for \<alpha> \<beta>
        by (metis deduction_theorem intro_elim_2)
    }
  qed
  AOT_hence \<open>[\<lambda>xy [R]yx] |: G \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E F\<close> using equi_2[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
  AOT_hence \<open>\<exists>R R |: G \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E F\<close> by (rule "\<exists>I"(1)) cqt_2_lambda
  AOT_thus \<open>G \<approx>\<^sub>E F\<close>
    using equi_3[THEN "\<equiv>\<^sub>d\<^sub>fI"] by blast
qed

AOT_theorem eq_part_3: \<open>(F \<approx>\<^sub>E G & G \<approx>\<^sub>E H) \<rightarrow> F \<approx>\<^sub>E H\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>F \<approx>\<^sub>E G & G \<approx>\<^sub>E H\<close>
  then AOT_obtain R\<^sub>1 and R\<^sub>2 where
       \<open>R\<^sub>1 |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
   and \<open>R\<^sub>2 |: G \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E H\<close>
    using equi_3[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" "\<exists>E"[rotated] by metis
  AOT_hence \<theta>: \<open>\<forall>u ([F]u \<rightarrow> \<exists>!v([G]v & [R\<^sub>1]uv)) & \<forall>v ([G]v \<rightarrow> \<exists>!u([F]u & [R\<^sub>1]uv))\<close>
        and \<xi>: \<open>\<forall>u ([G]u \<rightarrow> \<exists>!v([H]v & [R\<^sub>2]uv)) & \<forall>v ([H]v \<rightarrow> \<exists>!u([G]u & [R\<^sub>2]uv))\<close>
    using equi_2[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(2)]
          equi_2[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "&E"(1), THEN "&E"(2)]
          "&I" by blast+
  AOT_have \<open>\<exists>R R = [\<lambda>xy O!x & O!y & \<exists>v ([G]v & [R\<^sub>1]xv & [R\<^sub>2]vy)]\<close>
    by (rule free_thms_3_b) cqt_2_lambda_inst_prover
  then AOT_obtain R where R_def: \<open>R = [\<lambda>xy O!x & O!y & \<exists>v ([G]v & [R\<^sub>1]xv & [R\<^sub>2]vy)]\<close>
    using "\<exists>E"[rotated] by blast
  AOT_have 1: \<open>\<exists>!v (([H]v & [R]uv))\<close> if a: \<open>[O!]u\<close> and b: \<open>[F]u\<close> for u
  proof (rule "\<equiv>\<^sub>d\<^sub>fI"[OF equi_1])
    AOT_obtain b where b_prop: \<open>[O!]b & ([G]b & [R\<^sub>1]ub & \<forall>v ([G]v & [R\<^sub>1]uv \<rightarrow> v =\<^sub>E b))\<close>
      using \<theta>[THEN "&E"(1), THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF a b, THEN "\<equiv>\<^sub>d\<^sub>fE"[OF equi_1]]
            "\<exists>E"[rotated] by blast
    AOT_obtain c where c_prop: "[O!]c & ([H]c & [R\<^sub>2]bc & \<forall>v ([H]v & [R\<^sub>2]bv \<rightarrow> v =\<^sub>E c))"
      using \<xi>[THEN "&E"(1), THEN "\<forall>E"(2)[where \<beta>=b], THEN "\<rightarrow>E", OF b_prop[THEN "&E"(1)], THEN "\<rightarrow>E",
          OF b_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(1)], THEN "\<equiv>\<^sub>d\<^sub>fE"[OF equi_1]]
    "\<exists>E"[rotated] by blast
    AOT_show \<open>\<exists>v ([H]v & [R]uv & \<forall>v' ([H]v' & [R]uv' \<rightarrow> v' =\<^sub>E v))\<close>
    proof (rule_tac \<beta>=c in "\<exists>I"(2); safe intro!: "&I" GEN "\<rightarrow>I")
      AOT_show \<open>O!c\<close> using c_prop "&E" by blast
    next
      AOT_show \<open>[H]c\<close> using c_prop "&E" by blast
    next
      AOT_have 0: \<open>[O!]u & [O!]c & \<exists>v ([G]v & [R\<^sub>1]uv & [R\<^sub>2]vc)\<close>
        by (safe intro!: "&I" a c_prop[THEN "&E"(1)] "\<exists>I"(2)[where \<beta>=b] b_prop[THEN "&E"(1)]
                     b_prop[THEN "&E"(2), THEN "&E"(1)] c_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(2)])
      AOT_show \<open>[R]uc\<close>
        apply (rule "=E"[rotated, OF R_def[symmetric]])
        apply (rule betaC_2_a; cqt_2_lambda)
        by (auto simp: con_dis_i_e_1 ex_1_a prod_denotesI rule_ui_3 0)
    next
      fix x
      AOT_assume ordx: \<open>O!x\<close>
      AOT_assume \<open>[H]x & [R]ux\<close>
      AOT_hence hx: \<open>[H]x\<close> and \<open>[R]ux\<close> using "&E" by blast+
      AOT_hence \<open>[\<lambda>xy O!x & O!y & \<exists>v ([G]v & [R\<^sub>1]xv & [R\<^sub>2]vy)]ux\<close>
        using "=E"[rotated, OF R_def] by fast
      AOT_hence \<open>O!u & O!x & \<exists>v ([G]v & [R\<^sub>1]uv & [R\<^sub>2]vx)\<close>
        by (rule betaC_1_a[where \<phi>="\<lambda>(\<kappa>,\<kappa>'). _ \<kappa> \<kappa>'" and \<kappa>\<^sub>1\<kappa>\<^sub>n="(_,_)", simplified])
      then AOT_obtain z where z_prop: \<open>O!z & ([G]z & [R\<^sub>1]uz & [R\<^sub>2]zx)\<close>
        using "&E" "\<exists>E"[rotated] by blast
      AOT_hence \<open>z =\<^sub>E b\<close> using b_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=z]]
        using "&E" "\<rightarrow>E" by metis
      AOT_hence \<open>z = b\<close> by (metis eq_E_simple_2[THEN "\<rightarrow>E"])
      AOT_hence \<open>[R\<^sub>2]bx\<close> using z_prop[THEN "&E"(2), THEN "&E"(2)] "=E" by fast
      AOT_thus \<open>x =\<^sub>E c\<close>
        using c_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=x], THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF ordx]
              hx "&I" by blast
    qed
  qed
  AOT_have 2: \<open>\<exists>!u (([F]u & [R]uv))\<close> if a: \<open>[O!]v\<close> and b: \<open>[H]v\<close> for v
  proof (rule "\<equiv>\<^sub>d\<^sub>fI"[OF equi_1])
    AOT_obtain b where b_prop: \<open>[O!]b & ([G]b & [R\<^sub>2]bv & \<forall>u ([G]u & [R\<^sub>2]uv \<rightarrow> u =\<^sub>E b))\<close>
      using \<xi>[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF a b, THEN "\<equiv>\<^sub>d\<^sub>fE"[OF equi_1]]
            "\<exists>E"[rotated] by blast
    AOT_obtain c where c_prop: "[O!]c & ([F]c & [R\<^sub>1]cb & \<forall>v ([F]v & [R\<^sub>1]vb \<rightarrow> v =\<^sub>E c))"
      using \<theta>[THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=b], THEN "\<rightarrow>E", OF b_prop[THEN "&E"(1)], THEN "\<rightarrow>E",
          OF b_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(1)], THEN "\<equiv>\<^sub>d\<^sub>fE"[OF equi_1]]
    "\<exists>E"[rotated] by blast
    AOT_show \<open>\<exists>u ([F]u & [R]uv & \<forall>v' ([F]v' & [R]v'v \<rightarrow> v' =\<^sub>E u))\<close>
    proof (rule_tac \<beta>=c in "\<exists>I"(2); safe intro!: "&I" GEN "\<rightarrow>I")
      AOT_show \<open>O!c\<close> using c_prop "&E" by blast
    next
      AOT_show \<open>[F]c\<close> using c_prop "&E" by blast
    next
      AOT_have 0: \<open>[O!]c & [O!]v & \<exists>u ([G]u & [R\<^sub>1]cu & [R\<^sub>2]uv)\<close>
        by (safe intro!: "&I" a c_prop[THEN "&E"(1)] "\<exists>I"(2)[where \<beta>=b] b_prop[THEN "&E"(1)]
                     b_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(1)]
                     b_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(2)]
                     c_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(2)])
      AOT_show \<open>[R]cv\<close>
        apply (rule "=E"[rotated, OF R_def[symmetric]])
        apply (rule betaC_2_a; cqt_2_lambda)
        by (auto simp: con_dis_i_e_1 ex_1_a prod_denotesI rule_ui_3 0)
    next
      fix x
      AOT_assume ordx: \<open>O!x\<close>
      AOT_assume \<open>[F]x & [R]xv\<close>
      AOT_hence hx: \<open>[F]x\<close> and \<open>[R]xv\<close> using "&E" by blast+
      AOT_hence \<open>[\<lambda>xy O!x & O!y & \<exists>v ([G]v & [R\<^sub>1]xv & [R\<^sub>2]vy)]xv\<close>
        using "=E"[rotated, OF R_def] by fast
      AOT_hence \<open>O!x & O!v & \<exists>u ([G]u & [R\<^sub>1]xu & [R\<^sub>2]uv)\<close>
        by (rule betaC_1_a[where \<phi>="\<lambda>(\<kappa>,\<kappa>'). _ \<kappa> \<kappa>'" and \<kappa>\<^sub>1\<kappa>\<^sub>n="(_,_)", simplified])
      then AOT_obtain z where z_prop: \<open>O!z & ([G]z & [R\<^sub>1]xz & [R\<^sub>2]zv)\<close>
        using "&E" "\<exists>E"[rotated] by blast
      AOT_hence \<open>z =\<^sub>E b\<close> using b_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=z]]
        using "&E" "\<rightarrow>E" "&I" by metis
      AOT_hence \<open>z = b\<close> by (metis eq_E_simple_2[THEN "\<rightarrow>E"])
      AOT_hence \<open>[R\<^sub>1]xb\<close> using z_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(2)] "=E" by fast
      AOT_thus \<open>x =\<^sub>E c\<close>
        using c_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=x], THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF ordx]
              hx "&I" by blast
    qed
  qed
  AOT_show \<open>F \<approx>\<^sub>E H\<close>
    by (rule equi_3[THEN "\<equiv>\<^sub>d\<^sub>fI"];
        rule "\<exists>I"(2)[where \<beta>=R];
        cqt_2_lambda?;
        safe intro!: 1 2 "&I" equi_2[THEN "\<equiv>\<^sub>d\<^sub>fI"] cqt_2_const_var[axiom_inst] GEN "\<rightarrow>I";
        cqt_2_lambda?)
qed

AOT_theorem eq_part_4: \<open>F \<approx>\<^sub>E G \<equiv> \<forall>H (H \<approx>\<^sub>E F \<equiv> H \<approx>\<^sub>E G)\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume 0: \<open>F \<approx>\<^sub>E G\<close>
  AOT_hence 1: \<open>G \<approx>\<^sub>E F\<close> using eq_part_2[THEN "\<rightarrow>E"] by blast
  AOT_show \<open>\<forall>H (H \<approx>\<^sub>E F \<equiv> H \<approx>\<^sub>E G)\<close>
  proof (rule GEN; rule "\<equiv>I"; rule "\<rightarrow>I")
    AOT_show \<open>H \<approx>\<^sub>E G\<close> if \<open>H \<approx>\<^sub>E F\<close> for H using 0
      by (meson con_dis_i_e_1 eq_part_3 that vdash_properties_6)
  next
    AOT_show \<open>H \<approx>\<^sub>E F\<close> if \<open>H \<approx>\<^sub>E G\<close> for H using 1
      by (metis con_dis_i_e_1 eq_part_3 that vdash_properties_6)
  qed
next
  AOT_assume \<open>\<forall>H (H \<approx>\<^sub>E F \<equiv> H \<approx>\<^sub>E G)\<close>
  AOT_hence \<open>F \<approx>\<^sub>E F \<equiv> F \<approx>\<^sub>E G\<close> using "\<forall>E" by blast
  AOT_thus \<open>F \<approx>\<^sub>E G\<close> using eq_part_1 "\<equiv>E" by blast
qed

(* TODO_IMPORTANT: PLM states right-to-left direction as well without proof! *)
AOT_theorem eq_part_5: \<open>F \<approx>\<^sub>E G \<rightarrow> \<forall>H ([\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E F \<equiv> [\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E G)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>F \<approx>\<^sub>E G\<close>
  AOT_hence \<open>\<forall>H (H \<approx>\<^sub>E F \<equiv> H \<approx>\<^sub>E G)\<close>
    using eq_part_4[THEN "\<equiv>E"(1), OF 0] by blast
  AOT_have \<open>[\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E F \<equiv> [\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E G\<close> for H
    by (rule "\<forall>E"(1)[OF eq_part_4[THEN "\<equiv>E"(1), OF 0]]) cqt_2_lambda
  AOT_thus \<open>\<forall>H ([\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E F \<equiv> [\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E G)\<close> by (rule GEN)
qed

AOT_define equi_rem_1 :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> ("_ |: _ \<longrightarrow>E _")
  equi_rem_1: \<open>R |: F \<longrightarrow>E G \<equiv>\<^sub>d\<^sub>f R\<down> & F\<down> & G\<down> & \<forall>u ([F]u \<rightarrow> \<exists>!v ([G]v & [R]uv))\<close>

AOT_define equi_rem_2 :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> ("_ |: _ \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>E _")
  equi_rem_2: \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>E G \<equiv>\<^sub>d\<^sub>f R |: F \<longrightarrow>E G & \<forall>t\<forall>u\<forall>v (([F]t & [F]u & [G]v) \<rightarrow> ([R]tv & [R]uv \<rightarrow> t =\<^sub>E u))\<close>

AOT_define equi_rem_3 :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> ("_ |: _ \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE _")
  equi_rem_3: \<open>R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G \<equiv>\<^sub>d\<^sub>f R |: F \<longrightarrow>E G & \<forall>v ([G]v \<rightarrow> \<exists>u ([F]u & [R]uv))\<close>

AOT_define equi_rem_4 :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> ("_ |: _ \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE _")
  equi_rem_4: \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G \<equiv>\<^sub>d\<^sub>f R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>E G & R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close>

AOT_theorem equi_rem_thm: \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G \<equiv> R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close>
proof -
  AOT_have \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G \<equiv> R |: [\<lambda>x O!x & [F]x] \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> [\<lambda>x O!x & [G]x]\<close>
  proof(safe intro!: "\<equiv>I" "\<rightarrow>I" "&I")
    AOT_assume \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
    AOT_hence \<open>\<forall>u ([F]u \<rightarrow> \<exists>!v ([G]v & [R]uv))\<close> and \<open>\<forall>v ([G]v \<rightarrow> \<exists>!u ([F]u & [R]uv))\<close>
      using equi_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
    AOT_hence a: \<open>O!u \<rightarrow> ([F]u \<rightarrow> \<exists>!v ([G]v & [R]uv))\<close> and b: \<open>O!v \<rightarrow> ([G]v \<rightarrow> \<exists>!u ([F]u & [R]uv))\<close> for u v
      using "\<forall>E"(2) by blast+
    AOT_have \<open>([\<lambda>x [O!]x & [F]x]x \<rightarrow> \<exists>!y ([\<lambda>x [O!]x & [G]x]y & [R]xy))\<close> for x
      apply (AOT_subst \<open>\<guillemotleft>[\<lambda>x [O!]x & [F]x]x\<guillemotright>\<close> \<open>\<guillemotleft>[O!]x & [F]x\<guillemotright>\<close>)
       apply (rule beta_C_meta[THEN "\<rightarrow>E"])
       apply cqt_2_lambda
      apply (AOT_subst \<open>\<lambda> \<kappa> . \<guillemotleft>[\<lambda>x [O!]x & [G]x]\<kappa>\<guillemotright>\<close> \<open>\<lambda> \<kappa> . \<guillemotleft>[O!]\<kappa> & [G]\<kappa>\<guillemotright>\<close>)
       apply (rule beta_C_meta[THEN "\<rightarrow>E"])
       apply cqt_2_lambda
      apply (AOT_subst \<open>\<lambda>\<kappa> . \<guillemotleft>O!\<kappa> & [G]\<kappa> & [R]x\<kappa>\<guillemotright>\<close> \<open>\<lambda>\<kappa> .  \<guillemotleft>O!\<kappa> & ([G]\<kappa> & [R]x\<kappa>)\<guillemotright>\<close>)
       apply (meson intro_elim_3_f oth_class_taut_2_b oth_class_taut_3_a)
      apply (rule "\<rightarrow>I") apply (frule "&E"(1)) apply (drule "&E"(2))
      by (fact a[THEN "\<rightarrow>E", THEN "\<rightarrow>E", of x])
    AOT_hence A: \<open>\<forall>x ([\<lambda>x [O!]x & [F]x]x \<rightarrow> \<exists>!y ([\<lambda>x [O!]x & [G]x]y & [R]xy))\<close> by (rule GEN)
    AOT_have \<open>([\<lambda>x [O!]x & [G]x]y \<rightarrow> \<exists>!x ([\<lambda>x [O!]x & [F]x]x & [R]xy))\<close> for y
      apply (AOT_subst \<open>\<guillemotleft>[\<lambda>x [O!]x & [G]x]y\<guillemotright>\<close> \<open>\<guillemotleft>[O!]y & [G]y\<guillemotright>\<close>)
       apply (rule beta_C_meta[THEN "\<rightarrow>E"])
       apply cqt_2_lambda
      apply (AOT_subst \<open>\<lambda> \<kappa> . \<guillemotleft>[\<lambda>x [O!]x & [F]x]\<kappa>\<guillemotright>\<close> \<open>\<lambda> \<kappa> . \<guillemotleft>[O!]\<kappa> & [F]\<kappa>\<guillemotright>\<close>)
       apply (rule beta_C_meta[THEN "\<rightarrow>E"])
       apply cqt_2_lambda
      apply (AOT_subst \<open>\<lambda>\<kappa> . \<guillemotleft>O!\<kappa> & [F]\<kappa> & [R]\<kappa>y\<guillemotright>\<close> \<open>\<lambda>\<kappa> .  \<guillemotleft>O!\<kappa> & ([F]\<kappa> & [R]\<kappa>y)\<guillemotright>\<close>)
       apply (meson intro_elim_3_f oth_class_taut_2_b oth_class_taut_3_a)
      apply (rule "\<rightarrow>I") apply (frule "&E"(1)) apply (drule "&E"(2))
      by (fact b[THEN "\<rightarrow>E", THEN "\<rightarrow>E", of y])
    AOT_hence B: \<open>\<forall>y ([\<lambda>x [O!]x & [G]x]y \<rightarrow> \<exists>!x ([\<lambda>x [O!]x & [F]x]x & [R]xy))\<close> by (rule GEN)
    AOT_show \<open>R |: [\<lambda>x [O!]x & [F]x] \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> [\<lambda>x [O!]x & [G]x]\<close>
      by (safe intro!: one_one_cor[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" cqt_2_const_var[axiom_inst] A B)
          cqt_2_lambda+
  next
    AOT_assume \<open>R |: [\<lambda>x [O!]x & [F]x] \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> [\<lambda>x [O!]x & [G]x]\<close>
    AOT_hence a: \<open>([\<lambda>x [O!]x & [F]x]x \<rightarrow> \<exists>!y ([\<lambda>x [O!]x & [G]x]y & [R]xy))\<close> and 
              b: \<open>([\<lambda>x [O!]x & [G]x]y \<rightarrow> \<exists>!x ([\<lambda>x [O!]x & [F]x]x & [R]xy))\<close> for x y
      using one_one_cor[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" "\<forall>E"(2) by blast+
    AOT_have \<open>O!u \<rightarrow> ([F]u \<rightarrow> \<exists>!v ([G]v & [R]uv))\<close> for u
    proof (safe intro!: "\<rightarrow>I")
      AOT_assume ou: \<open>O!u\<close>
      AOT_assume fu: \<open>[F]u\<close>
      AOT_have 0: \<open>[\<lambda>x [O!]x & [F]x]u\<close>
        by (rule betaC_2_a; cqt_2_lambda; safe intro!: cqt_2_const_var[axiom_inst] ou fu "&I")
      AOT_show \<open>\<exists>!v ([G]v & [R]uv)\<close>
        apply (AOT_subst \<open>\<lambda>\<kappa>. \<guillemotleft>[O!]\<kappa> & ([G]\<kappa> & [R]u\<kappa>)\<guillemotright>\<close> \<open>\<lambda>\<kappa>. \<guillemotleft>([O!]\<kappa> & [G]\<kappa>) & [R]u\<kappa>\<guillemotright>\<close>)
         apply (simp add: oth_class_taut_2_b)
        apply (AOT_subst_rev \<open>\<lambda>\<kappa>. \<guillemotleft>[\<lambda>x [O!]x & [G]x]\<kappa>\<guillemotright>\<close> \<open>\<lambda>\<kappa>. \<guillemotleft>[O!]\<kappa> & [G]\<kappa>\<guillemotright>\<close>)
         apply (rule beta_C_meta[THEN "\<rightarrow>E"])
         apply cqt_2_lambda
        using a[THEN "\<rightarrow>E", OF 0] by blast
    qed
    AOT_hence A: \<open>\<forall>u ([F]u \<rightarrow> \<exists>!v ([G]v & [R]uv))\<close> by (rule GEN)
    AOT_have \<open>O!v \<rightarrow> ([G]v \<rightarrow> \<exists>!u ([F]u & [R]uv))\<close> for v
    proof (safe intro!: "\<rightarrow>I")
      AOT_assume ou: \<open>O!v\<close>
      AOT_assume gu: \<open>[G]v\<close>
      AOT_have 0: \<open>[\<lambda>x [O!]x & [G]x]v\<close>
        by (rule betaC_2_a; cqt_2_lambda; safe intro!: cqt_2_const_var[axiom_inst] ou gu "&I")
      AOT_show \<open>\<exists>!u ([F]u & [R]uv)\<close>
        apply (AOT_subst \<open>\<lambda>\<kappa>. \<guillemotleft>[O!]\<kappa> & ([F]\<kappa> & [R]\<kappa>v)\<guillemotright>\<close> \<open>\<lambda>\<kappa>. \<guillemotleft>([O!]\<kappa> & [F]\<kappa>) & [R]\<kappa>v\<guillemotright>\<close>)
         apply (simp add: oth_class_taut_2_b)
        apply (AOT_subst_rev \<open>\<lambda>\<kappa>. \<guillemotleft>[\<lambda>x [O!]x & [F]x]\<kappa>\<guillemotright>\<close> \<open>\<lambda>\<kappa>. \<guillemotleft>[O!]\<kappa> & [F]\<kappa>\<guillemotright>\<close>)
         apply (rule beta_C_meta[THEN "\<rightarrow>E"])
         apply cqt_2_lambda
        using b[THEN "\<rightarrow>E", OF 0] by blast
    qed
    AOT_hence B: \<open>\<forall>v ([G]v \<rightarrow> \<exists>!u ([F]u & [R]uv))\<close> by (rule GEN)
    AOT_show \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
      by (safe intro!: equi_2[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" A B cqt_2_const_var[axiom_inst])
  qed
  also AOT_have \<open>\<dots> \<equiv> R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close>
  proof(safe intro!: "\<equiv>I" "\<rightarrow>I" "&I")
    AOT_assume \<open>R |: [\<lambda>x [O!]x & [F]x] \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> [\<lambda>x [O!]x & [G]x]\<close>
    AOT_hence a: \<open>([\<lambda>x [O!]x & [F]x]x \<rightarrow> \<exists>!y ([\<lambda>x [O!]x & [G]x]y & [R]xy))\<close> and 
              b: \<open>([\<lambda>x [O!]x & [G]x]y \<rightarrow> \<exists>!x ([\<lambda>x [O!]x & [F]x]x & [R]xy))\<close> for x y
      using one_one_cor[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" "\<forall>E"(2) by blast+
    AOT_show \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close>
    proof (safe intro!: equi_rem_4[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" equi_rem_3[THEN "\<equiv>\<^sub>d\<^sub>fI"]
                        equi_rem_2[THEN "\<equiv>\<^sub>d\<^sub>fI"] equi_rem_1[THEN "\<equiv>\<^sub>d\<^sub>fI"]
                        cqt_2_const_var[axiom_inst] GEN "\<rightarrow>I")
      fix u
      AOT_assume ou: \<open>O!u\<close>
      AOT_assume fu: \<open>[F]u\<close>
      AOT_have 0: \<open>[\<lambda>x [O!]x & [F]x]u\<close>
        by (rule betaC_2_a; cqt_2_lambda; safe intro!: cqt_2_const_var[axiom_inst] ou fu "&I")
      AOT_hence 1: \<open>\<exists>!y ([\<lambda>x [O!]x & [G]x]y & [R]uy)\<close> using a[THEN "\<rightarrow>E"] by blast
      AOT_show \<open>\<exists>!v ([G]v & [R]uv)\<close>
        apply (AOT_subst \<open>\<lambda> \<kappa> . \<guillemotleft>[O!]\<kappa> & ([G]\<kappa> & [R]u\<kappa>)\<guillemotright>\<close> \<open>\<lambda> \<kappa> . \<guillemotleft>([O!]\<kappa> & [G]\<kappa>) & [R]u\<kappa>\<guillemotright>\<close>)
         apply (simp add: oth_class_taut_2_b)
        apply (AOT_subst_rev  \<open>\<lambda> \<kappa> . \<guillemotleft>[\<lambda>x [O!]x & [G]x]\<kappa>\<guillemotright>\<close>  \<open>\<lambda> \<kappa> . \<guillemotleft>[O!]\<kappa> & [G]\<kappa>\<guillemotright>\<close>)
         apply (rule beta_C_meta[THEN "\<rightarrow>E"])
         apply cqt_2_lambda
        by (fact 1)
    next
      fix t u v
      AOT_assume ot: \<open>O!t\<close> and ou: \<open>O!u\<close> and ov: \<open>O!v\<close> and ftu_gv: \<open>[F]t & [F]u & [G]v\<close> and rtv_tuv: \<open>[R]tv & [R]uv\<close>
      AOT_have oft: \<open>[\<lambda>x O!x & [F]x]t\<close>
        by (rule betaC_2_a; cqt_2_lambda)
           (auto simp: cqt_2_const_var[axiom_inst] ot ftu_gv[THEN "&E"(1), THEN "&E"(1)] intro!: "&I")
      AOT_have ofu: \<open>[\<lambda>x O!x & [F]x]u\<close>
        by (rule betaC_2_a; cqt_2_lambda)
           (auto simp: cqt_2_const_var[axiom_inst] ou ftu_gv[THEN "&E"(1), THEN "&E"(2)] intro!: "&I")
      AOT_have ogv: \<open>[\<lambda>x O!x & [G]x]v\<close>
        by (rule betaC_2_a; cqt_2_lambda)
           (auto simp: cqt_2_const_var[axiom_inst] ov ftu_gv[THEN "&E"(2)] intro!: "&I")
      AOT_hence \<open>\<exists>!x ([\<lambda>x [O!]x & [F]x]x & [R]xv)\<close>
        using b[THEN "\<rightarrow>E"] by blast
      then AOT_obtain a where a_prop: \<open>[\<lambda>x [O!]x & [F]x]a & [R]av & \<forall>x (([\<lambda>x [O!]x & [F]x]x & [R]xv) \<rightarrow> x = a)\<close>
        using uniqueness_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] "\<exists>E"[rotated] by blast
      AOT_hence ua: \<open>u = a\<close> using ofu rtv_tuv[THEN "&E"(2)] "\<forall>E"(2) "\<rightarrow>E" "&I" "&E"(2) by blast
      moreover AOT_have ta: \<open>t = a\<close> using a_prop oft rtv_tuv[THEN "&E"(1)] "\<forall>E"(2) "\<rightarrow>E" "&I" "&E"(2) by blast
      ultimately AOT_have \<open>t = u\<close> by (metis "rule=E" id_sym)
      AOT_thus \<open>t =\<^sub>E u\<close> using "rule=E" id_sym ord_eq_Eequiv_1 ou ta ua vdash_properties_10 by fast
    next
      fix u
      AOT_assume ou: \<open>O!u\<close> and fu: \<open>[F]u\<close>
      AOT_have \<open>[\<lambda>x O!x & [F]x]u\<close>
        by (rule betaC_2_a; cqt_2_lambda)
            (auto simp: cqt_2_const_var[axiom_inst] ou fu intro!: "&I")
      AOT_hence \<open>\<exists>!y ([\<lambda>x [O!]x & [G]x]y & [R]uy)\<close>
        using a[THEN "\<rightarrow>E"] by blast
      then AOT_obtain a where a_prop: \<open>[\<lambda>x [O!]x & [G]x]a & [R]ua & \<forall>x (([\<lambda>x [O!]x & [G]x]x & [R]ux) \<rightarrow> x = a)\<close>
        using uniqueness_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] "\<exists>E"[rotated] by blast
      AOT_have \<open>O!a & [G]a\<close>
        by (rule betaC_1_a) (auto simp: a_prop[THEN "&E"(1), THEN "&E"(1)])
      AOT_hence \<open>O!a\<close> and \<open>[G]a\<close> using "&E" by blast+
      moreover AOT_have \<open>\<forall>v ([G]v & [R]uv \<rightarrow> v =\<^sub>E a)\<close>
      proof(safe intro!: GEN "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
        fix v
        AOT_assume ov: \<open>O!v\<close> and gv: \<open>[G]v\<close> and ruv: \<open>[R]uv\<close>
        AOT_have \<open>[\<lambda>x [O!]x & [G]x]v\<close>
          by (rule betaC_2_a; cqt_2_lambda)
             (auto simp: cqt_2_const_var[axiom_inst] ov gv intro!: "&I")
        AOT_hence \<open>v = a\<close> using a_prop[THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF "&I"] ruv by blast
        AOT_thus \<open>v =\<^sub>E a\<close> using "rule=E" ord_eq_Eequiv_1 ov vdash_properties_10 by fast
      qed
      ultimately AOT_have \<open>O!a & ([G]a & [R]ua & \<forall>v' ([G]v' & [R]uv' \<rightarrow> v' =\<^sub>E a))\<close>
        using "\<exists>I" "&I" a_prop[THEN "&E"(1), THEN "&E"(2)] by simp
      AOT_hence \<open>\<exists>v ([G]v & [R]uv & \<forall>v' ([G]v' & [R]uv' \<rightarrow> v' =\<^sub>E v))\<close> by (rule "\<exists>I")
      AOT_thus \<open>\<exists>!v ([G]v & [R]uv)\<close>
        by (rule equi_1[THEN "\<equiv>\<^sub>d\<^sub>fI"])
    next
      fix v
      AOT_assume ov: \<open>O!v\<close> and gv: \<open>[G]v\<close>
      AOT_have \<open>[\<lambda>x O!x & [G]x]v\<close>
        by (rule betaC_2_a; cqt_2_lambda)
            (auto simp: cqt_2_const_var[axiom_inst] ov gv intro!: "&I")
      AOT_hence \<open>\<exists>!x ([\<lambda>x [O!]x & [F]x]x & [R]xv)\<close> using b[THEN "\<rightarrow>E"] by blast
      then AOT_obtain a where a_prop: \<open>[\<lambda>x [O!]x & [F]x]a & [R]av & \<forall>y ([\<lambda>x [O!]x & [F]x]y & [R]yv \<rightarrow> y = a)\<close>
        using "uniqueness_1"[THEN "\<equiv>\<^sub>d\<^sub>fE", THEN "\<exists>E"[rotated]] by blast
      AOT_have \<open>O!a & [F]a\<close>
        by (rule betaC_1_a) (auto simp: a_prop[THEN "&E"(1), THEN "&E"(1)])
      AOT_hence \<open>O!a & ([F]a & [R]av)\<close> using a_prop[THEN "&E"(1), THEN "&E"(2)] "&E" "&I" by metis
      AOT_thus \<open>\<exists>u ([F]u & [R]uv)\<close> by (rule "\<exists>I")
    qed
  next
    AOT_assume \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close>
    AOT_hence 1: \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>E G\<close> and 2: \<open>R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close> using equi_rem_4[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
    AOT_hence 3: \<open>R |: F \<longrightarrow>E G\<close> and A: \<open>\<forall>t \<forall>u \<forall>v ([F]t & [F]u & [G]v \<rightarrow> ([R]tv & [R]uv \<rightarrow> t =\<^sub>E u))\<close>
      using equi_rem_2[THEN "\<equiv>\<^sub>d\<^sub>fE", OF 1] "&E" by blast+
    AOT_hence B: \<open>\<forall>u ([F]u \<rightarrow> \<exists>!v ([G]v & [R]uv))\<close> using equi_rem_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
    AOT_have C: \<open>\<forall>v ([G]v \<rightarrow> \<exists>u ([F]u & [R]uv))\<close> using equi_rem_3[THEN "\<equiv>\<^sub>d\<^sub>fE", OF 2] "&E" by blast
    AOT_show \<open>R |: [\<lambda>x [O!]x & [F]x] \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> [\<lambda>x [O!]x & [G]x]\<close>
    proof (rule one_one_cor[THEN "\<equiv>\<^sub>d\<^sub>fI"]; safe intro!: "&I" cqt_2_const_var[axiom_inst] GEN "\<rightarrow>I")
      AOT_show \<open>[\<lambda>x [O!]x & [F]x]\<down>\<close> by cqt_2_lambda
    next
      AOT_show \<open>[\<lambda>x [O!]x & [G]x]\<down>\<close> by cqt_2_lambda
    next
      fix x
      AOT_assume 1: \<open>[\<lambda>x [O!]x & [F]x]x\<close>
      AOT_have \<open>O!x & [F]x\<close>
        by (rule betaC_1_a) (auto simp: 1)
      AOT_hence \<open>\<exists>!v ([G]v & [R]xv)\<close>
        using B[THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "&E" by blast
      then AOT_obtain y where y_prop: \<open>O!y & ([G]y & [R]xy & \<forall>u ([G]u & [R]xu \<rightarrow> u =\<^sub>E y))\<close>
        using equi_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] "\<exists>E"[rotated] by fastforce
      AOT_have \<open>[\<lambda>x O!x & [G]x]y\<close>
        by (rule betaC_2_a; cqt_2_lambda)
           (auto simp: cqt_2_const_var[axiom_inst] y_prop[THEN "&E"(1)]
                       y_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(1)] intro!: "&I")
      moreover AOT_have \<open>\<forall>z ([\<lambda>x O!x & [G]x]z & [R]xz \<rightarrow> z = y)\<close>
      proof(safe intro!: GEN "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
        fix z
        AOT_assume 1: \<open>[\<lambda>x [O!]x & [G]x]z\<close>
        AOT_have 2: \<open>O!z & [G]z\<close>
          by (rule betaC_1_a) (auto simp: 1)
        moreover AOT_assume \<open>[R]xz\<close>
        ultimately AOT_have \<open>z =\<^sub>E y\<close>
          using y_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<rightarrow>E", rotated, OF "&I"] "&E"
          by blast
        AOT_thus \<open>z = y\<close> using 2[THEN "&E"(1)] by (metis eq_E_simple_2 vdash_properties_10)
      qed
      ultimately AOT_have \<open>[\<lambda>x O!x & [G]x]y & [R]xy & \<forall>z ([\<lambda>x O!x & [G]x]z & [R]xz \<rightarrow> z = y)\<close>
        using y_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(2)] "&I" by auto
      AOT_hence \<open>\<exists>y ([\<lambda>x O!x & [G]x]y & [R]xy & \<forall>z ([\<lambda>x O!x & [G]x]z & [R]xz \<rightarrow> z = y))\<close>
        by (rule "\<exists>I")
      AOT_thus \<open>\<exists>!y ([\<lambda>x [O!]x & [G]x]y & [R]xy)\<close>
        using uniqueness_1[THEN "\<equiv>\<^sub>d\<^sub>fI"] by fast
    next
      fix y
      AOT_assume 1: \<open>[\<lambda>x [O!]x & [G]x]y\<close>
      AOT_have oy_gy: \<open>O!y & [G]y\<close>
        by (rule betaC_1_a) (auto simp: 1)
      AOT_hence \<open>\<exists>u ([F]u & [R]uy)\<close>
        using C[THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<rightarrow>E"] "&E" by blast
      then AOT_obtain x where x_prop: \<open>O!x & ([F]x & [R]xy)\<close>
        using "\<exists>E"[rotated] by blast
      AOT_have ofx: \<open>[\<lambda>x O!x & [F]x]x\<close>
        by (rule betaC_2_a; cqt_2_lambda)
           (auto simp: cqt_2_const_var[axiom_inst] x_prop[THEN "&E"(1)]
                       x_prop[THEN "&E"(2), THEN "&E"(1)] intro!: "&I")
      AOT_have \<open>\<exists>\<alpha> ([\<lambda>x [O!]x & [F]x]\<alpha> & [R]\<alpha>y & \<forall>\<beta> ([\<lambda>x [O!]x & [F]x]\<beta> & [R]\<beta>y \<rightarrow> \<beta> = \<alpha>))\<close>
      proof (safe intro!: "\<exists>I"(2)[where \<beta>=x] "&I" GEN "\<rightarrow>I")
        AOT_show \<open>[\<lambda>x O!x & [F]x]x\<close> using ofx.
      next
        AOT_show \<open>[R]xy\<close> using x_prop[THEN "&E"(2), THEN "&E"(2)].
      next
        fix z
        AOT_assume 1: \<open>[\<lambda>x [O!]x & [F]x]z & [R]zy\<close>
        AOT_have oz_fz: \<open>O!z & [F]z\<close>
          by (rule betaC_1_a) (auto simp: 1[THEN "&E"(1)])
        AOT_have \<open>z =\<^sub>E x\<close>
          using A[THEN "\<forall>E"(2)[where \<beta>=z], THEN "\<rightarrow>E", THEN "\<forall>E"(2)[where \<beta>=x], THEN "\<rightarrow>E", THEN "\<forall>E"(2)[where \<beta>=y], THEN "\<rightarrow>E",
                THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF oz_fz[THEN "&E"(1)], OF x_prop[THEN "&E"(1)], OF oy_gy[THEN "&E"(1)], OF "&I", OF "&I",
                OF oz_fz[THEN "&E"(2)], OF x_prop[THEN "&E"(2), THEN "&E"(1)], OF oy_gy[THEN "&E"(2)], OF "&I",
                OF 1[THEN "&E"(2)], OF x_prop[THEN "&E"(2), THEN "&E"(2)]].
        AOT_thus \<open>z = x\<close>
          by (metis eq_E_simple_2 vdash_properties_10)
      qed
      AOT_thus \<open>\<exists>!x ([\<lambda>x [O!]x & [F]x]x & [R]xy)\<close>
        by (rule uniqueness_1[THEN "\<equiv>\<^sub>d\<^sub>fI"])
    qed
  qed
  finally show ?thesis.
qed

AOT_define eqE :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl \<open>\<equiv>\<^sub>E\<close> 50)
  eqE: \<open>F \<equiv>\<^sub>E G \<equiv>\<^sub>d\<^sub>f F\<down> & G\<down> & \<forall>u ([F]u \<equiv> [G]u)\<close>

AOT_theorem apE_eqE_1: \<open>F \<equiv>\<^sub>E G \<rightarrow> F \<approx>\<^sub>E G\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>F \<equiv>\<^sub>E G\<close>
  AOT_have \<open>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
  proof (rule_tac \<tau>="\<guillemotleft>(=\<^sub>E)\<guillemotright>" in "\<exists>I"(1);
        safe intro!: equi_2[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" eq_E_denotes cqt_2_const_var[axiom_inst] GEN "\<rightarrow>I" equi_1[THEN "\<equiv>\<^sub>d\<^sub>fI"])
    fix u
    AOT_assume ordu: \<open>O!u\<close>
    AOT_assume Fu: \<open>[F]u\<close>
    AOT_hence Gu: \<open>[G]u\<close>
      using "\<equiv>\<^sub>d\<^sub>fE"[OF eqE, OF 0, THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=u], THEN "\<rightarrow>E", THEN "\<equiv>E"(1)]
            ordu Fu by blast
    AOT_show \<open>\<exists>v ([G]v & u =\<^sub>E v & \<forall>v' ([G]v' & u =\<^sub>E v' \<rightarrow> v' =\<^sub>E v))\<close>
      by (rule_tac \<beta>=u in "\<exists>I"(2); safe intro!: "&I" GEN "\<rightarrow>I" ordu Gu ord_eq_Eequiv_1[THEN "\<rightarrow>E", OF ordu] ord_eq_Eequiv_2[THEN "\<rightarrow>E"] dest!: "&E"(2))
  next
    fix v
    AOT_assume ordv: \<open>O!v\<close>
    AOT_assume Gv: \<open>[G]v\<close>
    AOT_hence Fv: \<open>[F]v\<close>
      using "\<equiv>\<^sub>d\<^sub>fE"[OF eqE, OF 0, THEN "&E"(2), THEN "\<forall>E"(2)[where \<beta>=v], THEN "\<rightarrow>E", THEN "\<equiv>E"(2)]
            ordv Gv by blast
    AOT_show \<open>\<exists>u ([F]u & u =\<^sub>E v & \<forall>v' ([F]v' & v' =\<^sub>E v \<rightarrow> v' =\<^sub>E u))\<close>
      by (rule_tac \<beta>=v in "\<exists>I"(2); safe intro!: "&I" GEN "\<rightarrow>I" ordv Fv ord_eq_Eequiv_1[THEN "\<rightarrow>E", OF ordv] ord_eq_Eequiv_2[THEN "\<rightarrow>E"] dest!: "&E"(2))
  qed
  AOT_thus \<open>F \<approx>\<^sub>E G\<close>
    by (rule equi_3[THEN "\<equiv>\<^sub>d\<^sub>fI"])
qed

AOT_theorem apE_eqE_2: \<open>(F \<approx>\<^sub>E G & G \<equiv>\<^sub>E H) \<rightarrow> F \<approx>\<^sub>E H\<close>
proof(rule "\<rightarrow>I")
  AOT_assume \<open>F \<approx>\<^sub>E G & G \<equiv>\<^sub>E H\<close>
  AOT_hence \<open>F \<approx>\<^sub>E G\<close> and \<open>G \<approx>\<^sub>E H\<close>
    using apE_eqE_1[THEN "\<rightarrow>E"] "&E" by blast+
  AOT_thus \<open>F \<approx>\<^sub>E H\<close>
    by (metis con_dis_taut_5 eq_part_3 vdash_properties_10)
qed

(* TODO_IMPORTANT: PLM states right-to-left direction as well without proof earlier than here! *)
AOT_theorem eq_part_5': \<open>F \<approx>\<^sub>E G \<equiv> \<forall>H ([\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E F \<equiv> [\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E G)\<close>
proof(rule "\<equiv>I"; rule "\<rightarrow>I")
  AOT_assume 0: \<open>F \<approx>\<^sub>E G\<close>
  AOT_thus \<open>\<forall>H ([\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E F \<equiv> [\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E G)\<close> by (rule eq_part_5[THEN "\<rightarrow>E"])
next
  AOT_assume 0: \<open>\<forall>H ([\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E F \<equiv> [\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E G)\<close>
  AOT_obtain H where \<open>Rigidifies([H],[F])\<close> using rigid_der_3 "\<exists>E" by metis
  AOT_hence H: \<open>Rigid([H]) & \<forall>x ([H]x \<equiv> [F]x)\<close>
    using df_rigid_rel_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_have H_rigid: \<open>\<box>\<forall>x ([H]x \<rightarrow> \<box>[H]x)\<close> using H[THEN "&E"(1), THEN df_rigid_rel_1[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2)].
  AOT_hence \<open>\<forall>x \<box>([H]x \<rightarrow> \<box>[H]x)\<close>
    using BFs_2 vdash_properties_10 by blast
  AOT_hence \<open>\<box>([H]x \<rightarrow> \<box>[H]x)\<close> for x using "\<forall>E"(2) by blast
  AOT_hence rigid: \<open>[H]x \<equiv> \<^bold>\<A>[H]x\<close> for x
     by (metis intro_elim_3_f oth_class_taut_3_a sc_eq_fur_2 vdash_properties_10)
  AOT_have \<open>H \<equiv>\<^sub>E F\<close>
  proof (safe intro!: eqE[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" cqt_2_const_var[axiom_inst] GEN "\<rightarrow>I")
    AOT_show \<open>[H]u \<equiv> [F]u\<close> for u using H[THEN "&E"(2)] "\<forall>E"(2) by fast
  qed
  AOT_hence \<open>H \<approx>\<^sub>E F\<close>
    by (rule apE_eqE_2[THEN "\<rightarrow>E", OF "&I", rotated])
       (simp add: eq_part_1)
  AOT_hence F_approx_H: \<open>F \<approx>\<^sub>E H\<close>
    by (metis eq_part_2 vdash_properties_10)
  moreover AOT_have H_eq_act_H: \<open>H \<equiv>\<^sub>E [\<lambda>z \<^bold>\<A>[H]z]\<close>
  proof (safe intro!: eqE[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" cqt_2_const_var[axiom_inst] GEN "\<rightarrow>I")
    AOT_show \<open>[\<lambda>z \<^bold>\<A>[H]z]\<down>\<close> by cqt_2_lambda
  next
    AOT_show \<open>[H]u \<equiv> [\<lambda>z \<^bold>\<A>[H]z]u\<close> for u
      apply (AOT_subst \<open>\<guillemotleft>[\<lambda>z \<^bold>\<A>[H]z]u\<guillemotright>\<close> \<open>\<guillemotleft>\<^bold>\<A>[H]u\<guillemotright>\<close>)
       apply (rule beta_C_meta[THEN "\<rightarrow>E"])
       apply cqt_2_lambda
      using rigid by blast
  qed
  AOT_have a: \<open>F \<approx>\<^sub>E [\<lambda>z \<^bold>\<A>[H]z]\<close>
    apply (rule apE_eqE_2[unvarify H, THEN "\<rightarrow>E"])
     apply cqt_2_lambda
    using F_approx_H H_eq_act_H "&I" by blast
  AOT_hence \<open>[\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E F\<close>
    apply (rule eq_part_2[unvarify G, THEN "\<rightarrow>E", rotated])
    by cqt_2_lambda
  AOT_hence b: \<open>[\<lambda>z \<^bold>\<A>[H]z] \<approx>\<^sub>E G\<close>
    by (rule 0[THEN "\<forall>E"(1), THEN "\<equiv>E"(1), rotated]) (rule cqt_2_const_var[axiom_inst]) 
  AOT_show \<open>F \<approx>\<^sub>E G\<close>
    by (rule eq_part_3[unvarify G, THEN "\<rightarrow>E", rotated, OF "&I", OF a, OF b])
       cqt_2_lambda
qed


AOT_theorem empty_approx_1: \<open>(\<not>\<exists>u [F]u & \<not>\<exists>v [H]v) \<rightarrow> F \<approx>\<^sub>E H\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
  AOT_assume 0: \<open>\<not>\<exists>u [F]u\<close> and 1: \<open>\<not>\<exists>v [H]v\<close>
  AOT_have \<open>\<forall>u ([F]u \<rightarrow> \<exists>!v ([H]v & [R]uv))\<close> for R
  proof(rule GEN; rule "\<rightarrow>I"; rule "\<rightarrow>I"; rule raa_cor_1)
    fix u
    AOT_assume \<open>O!u\<close> and \<open>[F]u\<close>
    AOT_hence \<open>\<exists>u [F]u\<close> using "\<exists>I"(2) "&I" by fast
    AOT_thus \<open>\<exists>u [F]u & \<not>\<exists>u [F]u\<close> using 0 "&I" by blast
  qed
  moreover AOT_have \<open>\<forall>v ([H]v \<rightarrow> \<exists>!u ([F]u & [R]uv))\<close> for R
  proof(rule GEN; rule "\<rightarrow>I"; rule "\<rightarrow>I"; rule raa_cor_1)
    fix v
    AOT_assume \<open>O!v\<close> and \<open>[H]v\<close>
    AOT_hence \<open>\<exists>v [H]v\<close> using "\<exists>I"(2) "&I" by fast
    AOT_thus \<open>\<exists>v [H]v & \<not>\<exists>v [H]v\<close> using 1 "&I" by blast
  qed
  (* TODO: PLM: incorrectly states R |: F \<longrightarrow> H instead *)
  ultimately AOT_have \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E H\<close> for R
    apply (safe intro!: equi_2[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" GEN cqt_2_const_var[axiom_inst])
    using "\<forall>E" by blast+
  AOT_hence \<open>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E H\<close> by (rule "\<exists>I")
  AOT_thus \<open>F \<approx>\<^sub>E H\<close>
    by (rule equi_3[THEN "\<equiv>\<^sub>d\<^sub>fI"])
qed

AOT_theorem empty_approx_2: \<open>(\<exists>u [F]u & \<not>\<exists>v [H]v) \<rightarrow> \<not>(F \<approx>\<^sub>E H)\<close>
proof(rule "\<rightarrow>I"; frule "&E"(1); drule "&E"(2); rule raa_cor_2)
  AOT_assume 1: \<open>\<exists>u [F]u\<close> and 2: \<open>\<not>\<exists>v [H]v\<close>
  AOT_obtain b where b_prop: \<open>O!b & [F]b\<close> using 1 "\<exists>E"[rotated] by blast
  AOT_assume \<open>F \<approx>\<^sub>E H\<close>
  AOT_hence \<open>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E H\<close>
    by (rule equi_3[THEN "\<equiv>\<^sub>d\<^sub>fE"])
  then AOT_obtain R where \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E H\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<theta>: \<open>\<forall>u ([F]u \<rightarrow> \<exists>!v ([H]v & [R]uv))\<close> and \<open>\<forall>v ([H]v \<rightarrow> \<exists>!u ([F]u & [R]uv))\<close>
    using equi_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_have \<open>\<exists>!v ([H]v & [R]bv)\<close> for u
    using \<theta>[THEN "\<forall>E"(2)[where \<beta>=b], THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF b_prop[THEN "&E"(1)], OF b_prop[THEN "&E"(2)]].
  AOT_hence \<open>\<exists>v ([H]v & [R]bv & \<forall>u ([H]u & [R]bu \<rightarrow> u =\<^sub>E v))\<close>
    by (rule equi_1[THEN "\<equiv>\<^sub>d\<^sub>fE"])
  then AOT_obtain x where \<open>O!x & ([H]x & [R]bx & \<forall>u ([H]u & [R]bu \<rightarrow> u =\<^sub>E x))\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<open>O!x & [H]x\<close> using "&E" "&I" by blast
  AOT_hence \<open>\<exists>v [H]v\<close> by (rule "\<exists>I")
  AOT_thus \<open>\<exists>v [H]v & \<not>\<exists>v [H]v\<close> using 2 "&I" by blast
qed

AOT_define F_minus_u :: \<open>\<Pi> \<Rightarrow> \<tau> \<Rightarrow> \<Pi>\<close> ("_\<^sup>-\<^sup>_")
  F_minus_u: \<open>[F]\<^sup>-\<^sup>x =\<^sub>d\<^sub>f [\<lambda>z [F]z & z \<noteq>\<^sub>E x]\<close>

AOT_theorem eqP':
  assumes ou: \<open>O!u\<close> and ov: \<open>O!v\<close>
  shows \<open>F \<approx>\<^sub>E G & [F]u & [G]v \<rightarrow> [F]\<^sup>-\<^sup>u \<approx>\<^sub>E [G]\<^sup>-\<^sup>v\<close>
proof (rule "\<rightarrow>I"; frule "&E"(2); drule "&E"(1); frule "&E"(2); drule "&E"(1))
  AOT_assume \<open>F \<approx>\<^sub>E G\<close>
  AOT_hence \<open>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
    using equi_3[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain R where R_prop: \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close> using "\<exists>E"[rotated] by blast
  AOT_hence A: \<open>\<forall>u ([F]u \<rightarrow> \<exists>!v ([G]v & [R]uv))\<close> and B: \<open>\<forall>v ([G]v \<rightarrow> \<exists>!u ([F]u & [R]uv))\<close>
    using equi_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_have \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close> using equi_rem_thm[THEN "\<equiv>E"(1), OF R_prop].
  AOT_hence \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>E G & R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close> using equi_rem_4[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_hence C: \<open>\<forall>t\<forall>u\<forall>v (([F]t & [F]u & [G]v) \<rightarrow> ([R]tv & [R]uv \<rightarrow> t =\<^sub>E u))\<close>
    using equi_rem_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  AOT_assume fu: \<open>[F]u\<close>
  AOT_assume gv: \<open>[G]v\<close>
  AOT_have \<open>[\<lambda>z [\<Pi>]z & z \<noteq>\<^sub>E \<kappa>]\<down>\<close> for \<Pi> \<kappa> by cqt_2_lambda
  note \<Pi>_minus_\<kappa>I = rule_id_def_2_b_2[where \<tau>=\<open>(\<lambda>(\<Pi>, \<kappa>). \<guillemotleft>[\<Pi>]\<^sup>-\<^sup>\<kappa>\<guillemotright>)\<close>, simplified, OF F_minus_u, simplified, OF this]
   and \<Pi>_minus_\<kappa>E = rule_id_def_2_a_2[where \<tau>=\<open>(\<lambda>(\<Pi>, \<kappa>). \<guillemotleft>[\<Pi>]\<^sup>-\<^sup>\<kappa>\<guillemotright>)\<close>, simplified, OF F_minus_u, simplified, OF this]
  AOT_have \<Pi>_minus_\<kappa>_den: \<open>[\<Pi>]\<^sup>-\<^sup>\<kappa>\<down>\<close> for \<Pi> \<kappa> (* TODO: PLM: quietly dismissed *)
    by (rule \<Pi>_minus_\<kappa>I) cqt_2_lambda+
  {
    fix R
    AOT_assume R_prop: \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
    AOT_hence A: \<open>\<forall>u ([F]u \<rightarrow> \<exists>!v ([G]v & [R]uv))\<close> and B: \<open>\<forall>v ([G]v \<rightarrow> \<exists>!u ([F]u & [R]uv))\<close>
      using equi_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
    AOT_have \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close> using equi_rem_thm[THEN "\<equiv>E"(1), OF R_prop].
    AOT_hence \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>E G & R |: F \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE G\<close> using equi_rem_4[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
    AOT_hence C: \<open>\<forall>t\<forall>u\<forall>v (([F]t & [F]u & [G]v) \<rightarrow> ([R]tv & [R]uv \<rightarrow> t =\<^sub>E u))\<close>
      using equi_rem_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast

    AOT_assume Ruv: \<open>[R]uv\<close>
    AOT_have \<open>R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E [G]\<^sup>-\<^sup>v\<close>
    proof(safe intro!: equi_2[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" cqt_2_const_var[axiom_inst] \<Pi>_minus_\<kappa>_den GEN "\<rightarrow>I")
      fix u'
      AOT_assume ou': \<open>O!u'\<close>
      AOT_assume \<open>[[F]\<^sup>-\<^sup>u]u'\<close>
      AOT_hence 0: \<open>[\<lambda>z [F]z & z \<noteq>\<^sub>E u]u'\<close> using \<Pi>_minus_\<kappa>E by fast
      AOT_have 0: \<open>[F]u' & u' \<noteq>\<^sub>E u\<close>
        by (rule betaC_1_a[where \<kappa>\<^sub>1\<kappa>\<^sub>n="AOT_term_of_var u'"]) (fact 0)
      AOT_have \<open>\<exists>!v ([G]v & [R]u'v)\<close>
        using A[THEN "\<forall>E"(2)[where \<beta>=u'], THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF ou', OF 0[THEN "&E"(1)]].
      then AOT_obtain v' where v'_prop: \<open>O!v' & ([G]v' & [R]u'v' & \<forall> t ([G]t & [R]u't \<rightarrow> t =\<^sub>E v'))\<close>
        using equi_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] "\<exists>E"[rotated] by fastforce

      AOT_show \<open>\<exists>!v' ([[G]\<^sup>-\<^sup>v]v' & [R]u'v')\<close>
      proof (rule equi_1[THEN "\<equiv>\<^sub>d\<^sub>fI"]; rule_tac \<beta>=v' in "\<exists>I"(2); safe intro!: "&I" GEN "\<rightarrow>I")
        AOT_show \<open>O!v'\<close> using v'_prop "&E" by blast
      next
        AOT_show \<open>[[G]\<^sup>-\<^sup>v]v'\<close>
        proof (rule \<Pi>_minus_\<kappa>I; rule betaC_2_a; cqt_2_lambda;
               safe intro!: cqt_2_const_var[axiom_inst] "&I" thm_neg_eq_E[THEN "\<equiv>E"(2)])
          AOT_show \<open>[G]v'\<close> using v'_prop "&E" by blast
        next
          AOT_show \<open>\<not>v' =\<^sub>E v\<close>
          proof (rule raa_cor_2)
            AOT_assume \<open>v' =\<^sub>E v\<close>
            AOT_hence \<open>v' = v\<close> by (metis eq_E_simple_2 vdash_properties_10)
            AOT_hence Ruv': \<open>[R]uv'\<close> using "rule=E" Ruv id_sym by fast
            AOT_have \<open>u' =\<^sub>E u\<close>
              by (rule C[THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<forall>E"(2),
                          THEN "\<rightarrow>E", THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF ou', OF ou, OF v'_prop[THEN "&E"(1)]];
                   safe intro!: "&I" 0[THEN "&E"(1)] fu v'_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(1)]
                                Ruv' v'_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(2)])
            moreover AOT_have \<open>\<not>(u' =\<^sub>E u)\<close>
              using "0" con_dis_i_e_2_b intro_elim_3_a thm_neg_eq_E by blast
            ultimately AOT_show \<open>u' =\<^sub>E u & \<not>u' =\<^sub>E u\<close> using "&I" by blast
          qed
        qed
      next
        AOT_show \<open>[R]u'v'\<close> using v'_prop "&E" by blast
      next
        fix t
        AOT_assume ot: \<open>O!t\<close> and t_prop: \<open>[[G]\<^sup>-\<^sup>v]t & [R]u't\<close>
        AOT_have gt_t_noteq_v: \<open>[G]t & t \<noteq>\<^sub>E v\<close>
          apply (rule betaC_1_a[where \<kappa>\<^sub>1\<kappa>\<^sub>n="AOT_term_of_var t"])
          apply (rule \<Pi>_minus_\<kappa>E)
          by (fact t_prop[THEN "&E"(1)])
        AOT_show \<open>t =\<^sub>E v'\<close>
          using v'_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF ot, THEN "\<rightarrow>E",
                        OF "&I", OF gt_t_noteq_v[THEN "&E"(1)], OF t_prop[THEN "&E"(2)]].
      qed
    next
      fix v'
      AOT_assume ov': \<open>O!v'\<close>
      AOT_assume G_minus_v_v': \<open>[[G]\<^sup>-\<^sup>v]v'\<close>
      AOT_have gt_t_noteq_v: \<open>[G]v' & v' \<noteq>\<^sub>E v\<close>
        apply (rule betaC_1_a[where \<kappa>\<^sub>1\<kappa>\<^sub>n="AOT_term_of_var v'"])
        apply (rule \<Pi>_minus_\<kappa>E)
        by (fact G_minus_v_v')
      AOT_have \<open>\<exists>!u([F]u & [R]uv')\<close> using B[THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF ov', OF gt_t_noteq_v[THEN "&E"(1)]].
      then AOT_obtain u' where u'_prop: \<open>O!u' & ([F]u' & [R]u'v' & \<forall>t ([F]t & [R]tv' \<rightarrow> t =\<^sub>E u'))\<close>
        using equi_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] "\<exists>E"[rotated] by fastforce
      AOT_show \<open>\<exists>!u' ([[F]\<^sup>-\<^sup>u]u' & [R]u'v')\<close>
      proof (rule equi_1[THEN "\<equiv>\<^sub>d\<^sub>fI"]; rule_tac \<beta>=u' in "\<exists>I"(2);
             safe intro!: "&I" GEN "\<rightarrow>I" u'_prop[THEN "&E"(1)] u'_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(2)])
        AOT_show \<open>[[F]\<^sup>-\<^sup>u]u'\<close>
        proof (rule \<Pi>_minus_\<kappa>I; rule betaC_2_a; cqt_2_lambda;
               safe intro!: cqt_2_const_var[axiom_inst] "&I" thm_neg_eq_E[THEN "\<equiv>E"(2)]
                            u'_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(1)];
               rule raa_cor_2)
          AOT_assume u'_eq_u: \<open>u' =\<^sub>E u\<close>
          AOT_hence \<open>u' = u\<close>
            using eq_E_simple_2 vdash_properties_10 by blast
          AOT_hence Ru'v: \<open>[R]u'v\<close> using "rule=E" Ruv id_sym by fast
          AOT_have \<open>v' \<noteq>\<^sub>E v\<close>
            using con_dis_i_e_2_b gt_t_noteq_v by blast
          AOT_hence v'_noteq_v: \<open>\<not>(v' =\<^sub>E v)\<close> by (metis intro_elim_3_a thm_neg_eq_E)
          AOT_have \<open>\<exists>u ([G]u & [R]u'u & \<forall>v ([G]v & [R]u'v \<rightarrow> v =\<^sub>E u))\<close>
            using A[THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF u'_prop[THEN "&E"(1)],
                             OF u'_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(1)],
                             THEN equi_1[THEN "\<equiv>\<^sub>d\<^sub>fE"]].
          then AOT_obtain t where t_prop: \<open>O!t & ([G]t & [R]u't & \<forall>v ([G]v & [R]u'v \<rightarrow> v =\<^sub>E t))\<close>
            using "\<exists>E"[rotated] by blast
          AOT_have \<open>v =\<^sub>E t\<close> if \<open>O!v\<close> and \<open>[G]v\<close> and \<open>[R]u'v\<close> for v
            using t_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF that(1), THEN "\<rightarrow>E", OF "&I", OF that(2), OF that(3)].
          AOT_hence \<open>v' =\<^sub>E t\<close> and \<open>v =\<^sub>E t\<close>
            by (auto simp: ov' gt_t_noteq_v[THEN "&E"(1)] u'_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(2)] Ru'v ov gv)
          AOT_hence \<open>v' =\<^sub>E v\<close> using "rule=E" eq_E_simple_2 id_sym vdash_properties_10 by fast
          AOT_thus \<open>v' =\<^sub>E v & \<not>v' =\<^sub>E v\<close> using v'_noteq_v "&I" by blast
        qed
      next
        fix t
        AOT_assume ot: \<open>O!t\<close>
        AOT_assume 0: \<open>[[F]\<^sup>-\<^sup>u]t & [R]tv'\<close>
        moreover AOT_have \<open>[F]t & t \<noteq>\<^sub>E u\<close>
          apply (rule betaC_1_a[where \<kappa>\<^sub>1\<kappa>\<^sub>n="AOT_term_of_var t"])
          apply (rule \<Pi>_minus_\<kappa>E)
          by (fact 0[THEN "&E"(1)])
        ultimately AOT_show \<open>t =\<^sub>E u'\<close>
          using u'_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF ot, THEN "\<rightarrow>E", OF "&I"]
                "&E" by blast
      qed
    qed
    AOT_hence \<open>\<exists>R R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E [G]\<^sup>-\<^sup>v\<close> by (rule "\<exists>I")
  } note 1 = this
  moreover {
    AOT_assume not_Ruv: \<open>\<not>[R]uv\<close>
    AOT_have \<open>\<exists>!v ([G]v & [R]uv)\<close> using A[THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF ou, OF fu].
    then AOT_obtain b where b_prop: \<open>O!b & ([G]b & [R]ub & \<forall>t([G]t & [R]ut \<rightarrow> t =\<^sub>E b))\<close>
      using equi_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] "\<exists>E"[rotated] by fastforce
    AOT_hence ob: \<open>O!b\<close> and gb: \<open>[G]b\<close> and Rub: \<open>[R]ub\<close> using "&E" by blast+
    AOT_have \<open>O!t \<rightarrow> ([G]t & [R]ut \<rightarrow> t =\<^sub>E b)\<close> for t using b_prop "&E"(2) "\<forall>E"(2) by blast
    AOT_hence b_unique: \<open>t =\<^sub>E b\<close> if \<open>O!t\<close> and \<open>[G]t\<close> and \<open>[R]ut\<close> for t
      by (metis con_dis_taut_5 modus_tollens_1 reductio_aa_1 that)
    AOT_have not_v_eq_b: \<open>\<not>(v =\<^sub>E b)\<close>
    proof(rule raa_cor_2)
      AOT_assume \<open>v =\<^sub>E b\<close>
      AOT_hence 0: \<open>v = b\<close> by (metis eq_E_simple_2 vdash_properties_10)
      AOT_have \<open>[R]uv\<close> using b_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(2)] "rule=E"[rotated, OF 0[symmetric]] by fast
      AOT_thus \<open>[R]uv & \<not>[R]uv\<close> using not_Ruv "&I" by blast
    qed
    AOT_have not_b_eq_v: \<open>\<not>(b =\<^sub>E v)\<close>
      using modus_tollens_1 not_v_eq_b ord_eq_Eequiv_2 by blast
    AOT_have \<open>\<exists>!u ([F]u & [R]uv)\<close> using B[THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF ov, OF gv].
    then AOT_obtain a where a_prop: \<open>O!a & ([F]a & [R]av & \<forall>t([F]t & [R]tv \<rightarrow> t =\<^sub>E a))\<close>
      using equi_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] "\<exists>E"[rotated] by fastforce
    AOT_hence oa: \<open>O!a\<close> and fa: \<open>[F]a\<close> and Rav: \<open>[R]av\<close> using "&E" by blast+
    AOT_have \<open>O!t \<rightarrow> ([F]t & [R]tv \<rightarrow> t =\<^sub>E a)\<close> for t using a_prop "&E" "\<forall>E"(2) by blast
    AOT_hence a_unique: \<open>t =\<^sub>E a\<close> if \<open>O!t\<close> and \<open>[F]t\<close> and \<open>[R]tv\<close> for t
      by (metis con_dis_taut_5 modus_tollens_1 reductio_aa_1 that) 
    AOT_have not_u_eq_a: \<open>\<not>(u =\<^sub>E a)\<close>
    proof(rule raa_cor_2)
      AOT_assume \<open>u =\<^sub>E a\<close>
      AOT_hence 0: \<open>u = a\<close> by (metis eq_E_simple_2 vdash_properties_10)
      AOT_have \<open>[R]uv\<close> using a_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(2)] "rule=E"[rotated, OF 0[symmetric]] by fast
      AOT_thus \<open>[R]uv & \<not>[R]uv\<close> using not_Ruv "&I" by blast
    qed
    AOT_have not_a_eq_u: \<open>\<not>(a =\<^sub>E u)\<close>
      using modus_tollens_1 not_u_eq_a ord_eq_Eequiv_2 by blast
    let ?R = \<open>\<guillemotleft>[\<lambda>u'v' (u' \<noteq>\<^sub>E u & v' \<noteq>\<^sub>E v & [R]u'v') \<or> (u' =\<^sub>E a & v' =\<^sub>E b) \<or> (u' =\<^sub>E u & v' =\<^sub>E v)]\<guillemotright>\<close>
    AOT_have \<open>[\<guillemotleft>?R\<guillemotright>]\<down>\<close> by cqt_2_lambda
    AOT_hence \<open>\<exists> \<beta> \<beta> = [\<guillemotleft>?R\<guillemotright>]\<close> using free_thms_1 intro_elim_3_a by fast
    then AOT_obtain R\<^sub>1 where R\<^sub>1_def: \<open>R\<^sub>1 = [\<guillemotleft>?R\<guillemotright>]\<close> using "\<exists>E"[rotated] by blast
    AOT_have Rxy1: \<open>[R]xy\<close> if \<open>[R\<^sub>1]xy\<close> and \<open>x \<noteq>\<^sub>E u\<close> and \<open>x \<noteq>\<^sub>E a\<close> for x y
    proof -
      AOT_have 0: \<open>[\<guillemotleft>?R\<guillemotright>]xy\<close>
        by (rule "rule=E"[rotated, OF R\<^sub>1_def]) (fact that(1))
      AOT_have \<open>(x \<noteq>\<^sub>E u & y \<noteq>\<^sub>E v & [R]xy) \<or> (x =\<^sub>E a & y =\<^sub>E b) \<or> (x =\<^sub>E u & y =\<^sub>E v)\<close>
        using betaC_1_a[OF 0] by simp
      AOT_hence \<open>x \<noteq>\<^sub>E u & y \<noteq>\<^sub>E v & [R]xy\<close> using that(2,3)
        by (metis con_dis_i_e_4_c con_dis_taut_1 intro_elim_3_a modus_tollens_1 thm_neg_eq_E)
      AOT_thus \<open>[R]xy\<close> using "&E" by blast+
    qed
    AOT_have Rxy2: \<open>[R]xy\<close>  if \<open>[R\<^sub>1]xy\<close> and \<open>y \<noteq>\<^sub>E v\<close> and \<open>y \<noteq>\<^sub>E b\<close> for x y
    proof -
      AOT_have 0: \<open>[\<guillemotleft>?R\<guillemotright>]xy\<close>
        by (rule "rule=E"[rotated, OF R\<^sub>1_def]) (fact that(1))
      AOT_have \<open>(x \<noteq>\<^sub>E u & y \<noteq>\<^sub>E v & [R]xy) \<or> (x =\<^sub>E a & y =\<^sub>E b) \<or> (x =\<^sub>E u & y =\<^sub>E v)\<close>
        using betaC_1_a[OF 0] by simp
      AOT_hence \<open>x \<noteq>\<^sub>E u & y \<noteq>\<^sub>E v & [R]xy\<close> using that(2,3)
        by (metis con_dis_i_e_4_c con_dis_taut_2 intro_elim_3_a modus_tollens_1 thm_neg_eq_E)
      AOT_thus \<open>[R]xy\<close> using "&E" by blast+
    qed
    AOT_have R\<^sub>1xy: \<open>[R\<^sub>1]xy\<close> if \<open>[R]xy\<close> and \<open>x \<noteq>\<^sub>E u\<close> and \<open>y \<noteq>\<^sub>E v\<close> for x y
      apply (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
      apply (rule betaC_2_a; cqt_2_lambda; simp add: con_dis_i_e_1 ex_1_a prod_denotesI rule_ui_3)
      using that con_dis_i_e_1 con_dis_i_e_3_a by presburger
    AOT_have R\<^sub>1ab: \<open>[R\<^sub>1]ab\<close>
      apply (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
      apply (rule betaC_2_a; cqt_2_lambda; simp add: con_dis_i_e_1 ex_1_a prod_denotesI rule_ui_3)
      by (meson a_prop b_prop con_dis_i_e_1 con_dis_i_e_2_a con_dis_i_e_3_a con_dis_i_e_3_b ord_eq_Eequiv_1 vdash_properties_10)
    AOT_have R\<^sub>1uv: \<open>[R\<^sub>1]uv\<close>
      apply (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
      apply (rule betaC_2_a; cqt_2_lambda; simp add: con_dis_i_e_1 ex_1_a prod_denotesI rule_ui_3)
      by (meson con_dis_i_e_1 con_dis_i_e_3_b ord_eq_Eequiv_1 ou ov vdash_properties_10)
    moreover AOT_have \<open>R\<^sub>1 |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
    proof (safe intro!: equi_2[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" cqt_2_const_var[axiom_inst] GEN "\<rightarrow>I")
      fix u'
      AOT_assume ou': \<open>O!u'\<close>
      AOT_assume fu': \<open>[F]u'\<close>
      {
        AOT_assume not_u'_eq_u: \<open>\<not>(u' =\<^sub>E u)\<close> and not_u'_eq_a: \<open>\<not>(u' =\<^sub>E a)\<close>
        AOT_hence u'_noteq_u: \<open>u' \<noteq>\<^sub>E u\<close> and u'_noteq_a: \<open>u' \<noteq>\<^sub>E a\<close> by (metis intro_elim_3_b thm_neg_eq_E)+
        AOT_have \<open>\<exists>!v ([G]v & [R]u'v)\<close> using A[THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF ou', OF fu'].
        AOT_hence \<open>\<exists>v ([G]v & [R]u'v & \<forall>t ([G]t & [R]u't \<rightarrow> t =\<^sub>E v))\<close>
          using equi_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] by simp
        then AOT_obtain v' where v'_prop: \<open>O!v' & ([G]v' & [R]u'v' & \<forall>t ([G]t & [R]u't \<rightarrow> t =\<^sub>E v'))\<close>
          using "\<exists>E"[rotated] by blast
        AOT_hence ov': \<open>O!v'\<close> and gv': \<open>[G]v'\<close> and Ru'v': \<open>[R]u'v'\<close>
          using "&E" by blast+
        AOT_have not_v'_eq_v: \<open>\<not>v' =\<^sub>E v\<close>
        proof (rule raa_cor_2)
          AOT_assume \<open>v' =\<^sub>E v\<close>
          AOT_hence \<open>v' = v\<close> by (metis eq_E_simple_2 vdash_properties_6)
          AOT_hence Ru'v: \<open>[R]u'v\<close> using "rule=E" Ru'v' by fast
          AOT_have \<open>u' =\<^sub>E a\<close> using a_unique[OF ou', OF fu', OF Ru'v].
          AOT_thus \<open>u' =\<^sub>E a & \<not>u' =\<^sub>E a\<close> using not_u'_eq_a "&I" by blast
        qed
        AOT_hence v'_noteq_v: \<open>v' \<noteq>\<^sub>E v\<close>
          using intro_elim_3_b thm_neg_eq_E by blast
        AOT_have \<open>\<forall>t ([G]t & [R]u't \<rightarrow> t =\<^sub>E v')\<close> using v'_prop "&E" by blast
        AOT_hence \<open>O!t \<rightarrow> ([G]t & [R]u't \<rightarrow> t =\<^sub>E v')\<close> for t using "\<forall>E"(2) by blast
        AOT_hence v'_unique: \<open>t =\<^sub>E v'\<close> if \<open>O!t\<close> and \<open>[G]t\<close> and \<open>[R]u't\<close> for t
          by (metis con_dis_i_e_1 that vdash_properties_10)

        AOT_have \<open>O!v' & ([G]v' & [R\<^sub>1]u'v' & \<forall>t ([G]t & [R\<^sub>1]u't \<rightarrow> t =\<^sub>E v'))\<close>
        proof (safe intro!: "&I" ov' gv' R\<^sub>1xy Ru'v' u'_noteq_u u'_noteq_a GEN "\<rightarrow>I" thm_neg_eq_E[THEN "\<equiv>E"(2)] not_v'_eq_v)
          fix t
          AOT_assume 0: \<open>O!t\<close>
          AOT_assume 1: \<open>[G]t & [R\<^sub>1]u't\<close>
          AOT_have \<open>[R]u't\<close> using Rxy1[OF 1[THEN "&E"(2)], OF u'_noteq_u, OF u'_noteq_a].
          AOT_thus \<open>t =\<^sub>E v'\<close>
            using v'_unique[OF 0] 1[THEN "&E"(1)] by blast
        qed
        AOT_hence \<open>\<exists>v ([G]v & [R\<^sub>1]u'v & \<forall>t ([G]t & [R\<^sub>1]u't \<rightarrow> t =\<^sub>E v))\<close>
          by (rule "\<exists>I")
        AOT_hence \<open>\<exists>!v ([G]v & [R\<^sub>1]u'v)\<close>
          by (rule equi_1[THEN "\<equiv>\<^sub>d\<^sub>fI"])
      }
      moreover {
        AOT_assume 0: \<open>u' =\<^sub>E u\<close>
        AOT_hence u'_eq_u: \<open>u' = u\<close>
          using eq_E_simple_2 vdash_properties_6 by blast
        AOT_have \<open>\<exists>!v ([G]v & [R\<^sub>1]u'v)\<close>
        proof (safe intro!: equi_1[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(2)[where \<beta>=v] "&I" GEN "\<rightarrow>I" ov gv)
          AOT_show \<open>[R\<^sub>1]u'v\<close>
            apply (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
            apply (rule betaC_2_a; cqt_2_lambda; simp add: con_dis_i_e_1 ex_1_a prod_denotesI rule_ui_3)
            by (safe intro!: "\<or>I"(2) "&I" 0 ord_eq_Eequiv_1[THEN "\<rightarrow>E", OF ov])
        next
          fix v'
          AOT_assume \<open>O!v'\<close>
          AOT_assume \<open>[G]v' & [R\<^sub>1]u'v'\<close>
          AOT_hence 0: \<open>[R\<^sub>1]uv'\<close> using "rule=E"[rotated, OF u'_eq_u] "&E"(2) by fast
          AOT_have 1: \<open>[\<guillemotleft>?R\<guillemotright>]uv'\<close>
            by (rule "rule=E"[rotated, OF R\<^sub>1_def]) (fact 0)
          AOT_have 2: \<open>(u \<noteq>\<^sub>E u & v' \<noteq>\<^sub>E v & [R]uv') \<or> (u =\<^sub>E a & v' =\<^sub>E b) \<or> (u =\<^sub>E u & v' =\<^sub>E v)\<close>
            using betaC_1_a[OF 1] by simp
          AOT_have \<open>\<not>u \<noteq>\<^sub>E u\<close>
            using intro_elim_3_d modus_tollens_1 ord_eq_Eequiv_1 ou reductio_aa_2 thm_neg_eq_E by blast
          AOT_hence \<open>\<not>((u \<noteq>\<^sub>E u & v' \<noteq>\<^sub>E v & [R]uv') \<or> (u =\<^sub>E a & v' =\<^sub>E b))\<close>
            using not_u_eq_a by (metis con_dis_i_e_4_b con_dis_taut_1 modus_tollens_1 reductio_aa_1)
          AOT_hence \<open>(u =\<^sub>E u & v' =\<^sub>E v)\<close> using 2 by (metis con_dis_i_e_4_b)
          AOT_thus \<open>v' =\<^sub>E v\<close> using "&E" by blast
        qed
      }
      moreover {
        AOT_assume 0: \<open>u' =\<^sub>E a\<close>
        AOT_hence u'_eq_a: \<open>u' = a\<close>
          using eq_E_simple_2 vdash_properties_10 by blast
        AOT_have \<open>\<exists>!v ([G]v & [R\<^sub>1]u'v)\<close>
        proof (safe intro!: equi_1[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(2)[where \<beta>=b] "&I" GEN "\<rightarrow>I" b_prop[THEN "&E"(1)]
                            b_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(1)])
          AOT_show \<open>[R\<^sub>1]u'b\<close>
            apply (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
            apply (rule betaC_2_a; cqt_2_lambda; simp add: con_dis_i_e_1 ex_1_a prod_denotesI rule_ui_3)
            apply (rule "\<or>I"(1); rule "\<or>I"(2); rule "&I")
             apply (fact 0)
            using b_prop con_dis_i_e_2_a ord_eq_Eequiv_1 vdash_properties_10 by blast
        next
          fix v'
          AOT_assume ov': \<open>O!v'\<close>
          AOT_assume gv'_R1u'v': \<open>[G]v' & [R\<^sub>1]u'v'\<close>
          AOT_hence 0: \<open>[R\<^sub>1]av'\<close> using u'_eq_a by (meson "rule=E" con_dis_i_e_2_b)
          AOT_have 1: \<open>[\<guillemotleft>?R\<guillemotright>]av'\<close>
            by (rule "rule=E"[rotated, OF R\<^sub>1_def]) (fact 0)
          AOT_have \<open>(a \<noteq>\<^sub>E u & v' \<noteq>\<^sub>E v & [R]av') \<or> (a =\<^sub>E a & v' =\<^sub>E b) \<or> (a =\<^sub>E u & v' =\<^sub>E v)\<close>
            using betaC_1_a[OF 1] by simp
          moreover {
            AOT_assume 0: \<open>a \<noteq>\<^sub>E u & v' \<noteq>\<^sub>E v & [R]av'\<close>
            AOT_have \<open>\<exists>!v ([G]v & [R]u'v)\<close> using A[THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF ou', THEN "\<rightarrow>E", OF fu'].
            AOT_hence \<open>\<exists>!v ([G]v & [R]av)\<close> using u'_eq_a "rule=E" by fast
            AOT_hence \<open>\<exists>v ([G]v & [R]av & \<forall>t ([G]t & [R]at \<rightarrow> t =\<^sub>E v))\<close>
              using equi_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] by fast
            then AOT_obtain s where s_prop: \<open>O!s & ([G]s & [R]as & \<forall>t ([G]t & [R]at \<rightarrow> t =\<^sub>E s))\<close> using "\<exists>E"[rotated] by blast
            AOT_have \<open>v' =\<^sub>E s\<close> using s_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF ov']
                                     gv'_R1u'v'[THEN "&E"(1)] 0[THEN "&E"(2)]
              by (metis con_dis_i_e_1 vdash_properties_10)
            moreover AOT_have \<open>v =\<^sub>E s\<close> using s_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF ov]
                                    gv Rav by (metis con_dis_i_e_1 vdash_properties_10)
            ultimately AOT_have \<open>v' =\<^sub>E v\<close>
              by (metis con_dis_i_e_1 ord_eq_Eequiv_2 ord_eq_Eequiv_3 vdash_properties_10)
            moreover AOT_have \<open>\<not>(v' =\<^sub>E v)\<close> using 0[THEN "&E"(1), THEN "&E"(2)] by (metis intro_elim_3_a thm_neg_eq_E) 
            ultimately AOT_have \<open>v' =\<^sub>E b\<close> by (metis raa_cor_3)
          }
          moreover {
            AOT_assume \<open>a =\<^sub>E u & v' =\<^sub>E v\<close>
            AOT_hence \<open>v' =\<^sub>E b\<close> by (metis con_dis_i_e_2_a not_a_eq_u reductio_aa_1)
          }
          ultimately AOT_show \<open>v' =\<^sub>E b\<close> by (metis con_dis_i_e_2_b con_dis_i_e_4_c reductio_aa_1) 
        qed
      }
      ultimately AOT_show \<open>\<exists>!v ([G]v & [R\<^sub>1]u'v)\<close> by (metis raa_cor_1)
    next
      fix v'
      AOT_assume ov': \<open>O!v'\<close>
      AOT_assume gv': \<open>[G]v'\<close>
      {
        AOT_assume not_v'_eq_v: \<open>\<not>(v' =\<^sub>E v)\<close> and not_v'_eq_b: \<open>\<not>(v' =\<^sub>E b)\<close>
        AOT_hence v'_noteq_v: \<open>v' \<noteq>\<^sub>E v\<close> and v'_noteq_b: \<open>v' \<noteq>\<^sub>E b\<close> by (metis intro_elim_3_b thm_neg_eq_E)+
        AOT_have \<open>\<exists>!u ([F]u & [R]uv')\<close> using B[THEN "\<forall>E"(2), THEN "\<rightarrow>E", THEN "\<rightarrow>E", OF ov', OF gv'].
        AOT_hence \<open>\<exists>u ([F]u & [R]uv' & \<forall>t ([F]t & [R]tv' \<rightarrow> t =\<^sub>E u))\<close>
          using equi_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] by simp
        then AOT_obtain u' where u'_prop: \<open>O!u' & ([F]u' & [R]u'v' & \<forall>t ([F]t & [R]tv' \<rightarrow> t =\<^sub>E u'))\<close>
          using "\<exists>E"[rotated] by blast
        AOT_hence ou': \<open>O!u'\<close> and fu': \<open>[F]u'\<close> and Ru'v': \<open>[R]u'v'\<close>
          using "&E" by blast+
        AOT_have not_u'_eq_u: \<open>\<not>u' =\<^sub>E u\<close>
        proof (rule raa_cor_2)
          AOT_assume \<open>u' =\<^sub>E u\<close>
          AOT_hence \<open>u' = u\<close> by (metis eq_E_simple_2 vdash_properties_6)
          AOT_hence Ruv': \<open>[R]uv'\<close> using "rule=E" Ru'v' by fast
          AOT_have \<open>v' =\<^sub>E b\<close> using b_unique[OF ov', OF gv', OF Ruv'].
          AOT_thus \<open>v' =\<^sub>E b & \<not>v' =\<^sub>E b\<close> using not_v'_eq_b "&I" by blast
        qed
        AOT_hence u'_noteq_u: \<open>u' \<noteq>\<^sub>E u\<close>
          using intro_elim_3_b thm_neg_eq_E by blast
        AOT_have \<open>\<forall>t ([F]t & [R]tv' \<rightarrow> t =\<^sub>E u')\<close> using u'_prop "&E" by blast
        AOT_hence \<open>O!t \<rightarrow> ([F]t & [R]tv' \<rightarrow> t =\<^sub>E u')\<close> for t using "\<forall>E"(2) by blast
        AOT_hence u'_unique: \<open>t =\<^sub>E u'\<close> if \<open>O!t\<close> and \<open>[F]t\<close> and \<open>[R]tv'\<close> for t
          by (metis con_dis_i_e_1 that vdash_properties_10)

        AOT_have \<open>O!u' & ([F]u' & [R\<^sub>1]u'v' & \<forall>t ([F]t & [R\<^sub>1]tv' \<rightarrow> t =\<^sub>E u'))\<close>
        proof (safe intro!: "&I" ov' gv' R\<^sub>1xy Ru'v' u'_noteq_u GEN "\<rightarrow>I" thm_neg_eq_E[THEN "\<equiv>E"(2)] not_v'_eq_v fu' ou')
          fix t
          AOT_assume 0: \<open>O!t\<close>
          AOT_assume 1: \<open>[F]t & [R\<^sub>1]tv'\<close>
          AOT_have \<open>[R]tv'\<close> using Rxy2[OF 1[THEN "&E"(2)], OF v'_noteq_v, OF v'_noteq_b].
          AOT_thus \<open>t =\<^sub>E u'\<close>
            using u'_unique[OF 0] 1[THEN "&E"(1)] by blast
        qed
        AOT_hence \<open>\<exists>u ([F]u & [R\<^sub>1]uv' & \<forall>t ([F]t & [R\<^sub>1]tv' \<rightarrow> t =\<^sub>E u))\<close>
          by (rule "\<exists>I")
        AOT_hence \<open>\<exists>!u ([F]u & [R\<^sub>1]uv')\<close>
          by (rule equi_1[THEN "\<equiv>\<^sub>d\<^sub>fI"])
      }
      moreover {
        AOT_assume 0: \<open>v' =\<^sub>E v\<close>
        AOT_hence u'_eq_u: \<open>v' = v\<close>
          using eq_E_simple_2 vdash_properties_6 by blast
        AOT_have \<open>\<exists>!u ([F]u & [R\<^sub>1]uv')\<close>
        proof (safe intro!: equi_1[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(2)[where \<beta>=u] "&I" GEN "\<rightarrow>I" ou fu)
          AOT_show \<open>[R\<^sub>1]uv'\<close>
            apply (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
            apply (rule betaC_2_a; cqt_2_lambda; simp add: con_dis_i_e_1 ex_1_a prod_denotesI rule_ui_3)
            by (safe intro!: "\<or>I"(2) "&I" 0 ord_eq_Eequiv_1[THEN "\<rightarrow>E", OF ou])
        next
          fix u'
          AOT_assume \<open>O!u'\<close>
          AOT_assume \<open>[F]u' & [R\<^sub>1]u'v'\<close>
          AOT_hence 0: \<open>[R\<^sub>1]u'v\<close> using "rule=E"[rotated, OF u'_eq_u] "&E"(2) by fast
          AOT_have 1: \<open>[\<guillemotleft>?R\<guillemotright>]u'v\<close>
            by (rule "rule=E"[rotated, OF R\<^sub>1_def]) (fact 0)
          AOT_have 2: \<open>(u' \<noteq>\<^sub>E u & v \<noteq>\<^sub>E v & [R]u'v) \<or> (u' =\<^sub>E a & v =\<^sub>E b) \<or> (u' =\<^sub>E u & v =\<^sub>E v)\<close>
            using betaC_1_a[OF 1, simplified] by simp
          AOT_have \<open>\<not>v \<noteq>\<^sub>E v\<close>
            using intro_elim_3_d modus_tollens_1 ord_eq_Eequiv_1 ov reductio_aa_2 thm_neg_eq_E by blast
          AOT_hence \<open>\<not>((u' \<noteq>\<^sub>E u & v \<noteq>\<^sub>E v & [R]u'v) \<or> (u' =\<^sub>E a & v =\<^sub>E b))\<close>
            by (metis con_dis_i_e_2_a con_dis_i_e_2_b con_dis_i_e_4_c not_v_eq_b raa_cor_3)
          AOT_hence \<open>(u' =\<^sub>E u & v =\<^sub>E v)\<close> using 2 by (metis con_dis_i_e_4_b)
          AOT_thus \<open>u' =\<^sub>E u\<close> using "&E" by blast
        qed
      }
      moreover {
        AOT_assume 0: \<open>v' =\<^sub>E b\<close>
        AOT_hence v'_eq_b: \<open>v' = b\<close>
          using eq_E_simple_2 vdash_properties_10 by blast
        AOT_have \<open>\<exists>!u ([F]u & [R\<^sub>1]uv')\<close>
        proof (safe intro!: equi_1[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(2)[where \<beta>=a] "&I" GEN "\<rightarrow>I" b_prop[THEN "&E"(1)]
                            b_prop[THEN "&E"(2), THEN "&E"(1), THEN "&E"(1)] oa fa)
          AOT_show \<open>[R\<^sub>1]av'\<close>
            apply (rule "rule=E"[rotated, OF R\<^sub>1_def[symmetric]])
            apply (rule betaC_2_a; cqt_2_lambda; simp add: con_dis_i_e_1 ex_1_a prod_denotesI rule_ui_3)
            apply (rule "\<or>I"(1); rule "\<or>I"(2); rule "&I")
            using Rav a_unique fa oa apply presburger
            by (fact 0)
        next
          fix u'
          AOT_assume ou': \<open>O!u'\<close>
          AOT_assume fu'_R1u'v': \<open>[F]u' & [R\<^sub>1]u'v'\<close>
          AOT_hence 0: \<open>[R\<^sub>1]u'b\<close> using v'_eq_b by (meson "rule=E" con_dis_i_e_2_b)
          AOT_have 1: \<open>[\<guillemotleft>?R\<guillemotright>]u'b\<close>
            by (rule "rule=E"[rotated, OF R\<^sub>1_def]) (fact 0)
          AOT_have \<open>(u' \<noteq>\<^sub>E u & b \<noteq>\<^sub>E v & [R]u'b) \<or> (u' =\<^sub>E a & b =\<^sub>E b) \<or> (u' =\<^sub>E u & b =\<^sub>E v)\<close>
            using betaC_1_a[OF 1, simplified] by simp
          moreover {
            AOT_assume 0: \<open>u' \<noteq>\<^sub>E u & b \<noteq>\<^sub>E v & [R]u'b\<close>
            AOT_have \<open>\<exists>!u ([F]u & [R]uv')\<close> using B[THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF ov', THEN "\<rightarrow>E", OF gv'].
            AOT_hence \<open>\<exists>!u ([F]u & [R]ub)\<close> using v'_eq_b "rule=E" by fast
            AOT_hence \<open>\<exists>u ([F]u & [R]ub & \<forall>t ([F]t & [R]tb \<rightarrow> t =\<^sub>E u))\<close>
              using equi_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] by fast
            then AOT_obtain s where s_prop: \<open>O!s & ([F]s & [R]sb & \<forall>t ([F]t & [R]tb \<rightarrow> t =\<^sub>E s))\<close> using "\<exists>E"[rotated] by blast
            AOT_have \<open>u' =\<^sub>E s\<close> using s_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF ou']
                                     fu'_R1u'v'[THEN "&E"(1)] 0[THEN "&E"(2)]
              by (metis con_dis_i_e_1 vdash_properties_10)
            moreover AOT_have \<open>u =\<^sub>E s\<close> using s_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF ou]
                                    fu Rub by (metis con_dis_i_e_1 vdash_properties_10)
            ultimately AOT_have \<open>u' =\<^sub>E u\<close>
              by (metis con_dis_i_e_1 ord_eq_Eequiv_2 ord_eq_Eequiv_3 vdash_properties_10)
            moreover AOT_have \<open>\<not>(u' =\<^sub>E u)\<close> using 0[THEN "&E"(1), THEN "&E"(1)] by (metis intro_elim_3_a thm_neg_eq_E) 
            ultimately AOT_have \<open>u' =\<^sub>E a\<close> by (metis raa_cor_3)
          }
          moreover {
            AOT_assume \<open>u' =\<^sub>E u & b =\<^sub>E v\<close>
            AOT_hence \<open>u' =\<^sub>E a\<close> by (metis con_dis_i_e_2_b not_b_eq_v reductio_aa_1)
          }
          ultimately AOT_show \<open>u' =\<^sub>E a\<close> by (metis con_dis_i_e_2_a con_dis_i_e_4_c reductio_aa_1) 
        qed
      }
      ultimately AOT_show \<open>\<exists>!u ([F]u & [R\<^sub>1]uv')\<close> by (metis raa_cor_1)
    qed
    ultimately AOT_have \<open>\<exists>R R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E [G]\<^sup>-\<^sup>v\<close> using 1 by blast
  }
  ultimately AOT_have \<open>\<exists>R R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E [G]\<^sup>-\<^sup>v\<close> using R_prop by (metis reductio_aa_2) 
  AOT_thus \<open>[F]\<^sup>-\<^sup>u \<approx>\<^sub>E [G]\<^sup>-\<^sup>v\<close>
    by (rule equi_3[THEN "\<equiv>\<^sub>d\<^sub>fI"])
qed

AOT_theorem P'_eq:
  assumes Ou: \<open>O!u\<close> and Ov: \<open>O!v\<close>
  shows \<open>[F]\<^sup>-\<^sup>u \<approx>\<^sub>E [G]\<^sup>-\<^sup>v & [F]u & [G]v \<rightarrow> F \<approx>\<^sub>E G\<close>
proof(safe intro!: "\<rightarrow>I"; frule "&E"(1); drule "&E"(2); frule "&E"(1); drule "&E"(2))
  AOT_have \<open>[\<lambda>z [\<Pi>]z & z \<noteq>\<^sub>E \<kappa>]\<down>\<close> for \<Pi> \<kappa> by cqt_2_lambda
  note \<Pi>_minus_\<kappa>I = rule_id_def_2_b_2[where \<tau>=\<open>(\<lambda>(\<Pi>, \<kappa>). \<guillemotleft>[\<Pi>]\<^sup>-\<^sup>\<kappa>\<guillemotright>)\<close>, simplified, OF F_minus_u, simplified, OF this]
   and \<Pi>_minus_\<kappa>E = rule_id_def_2_a_2[where \<tau>=\<open>(\<lambda>(\<Pi>, \<kappa>). \<guillemotleft>[\<Pi>]\<^sup>-\<^sup>\<kappa>\<guillemotright>)\<close>, simplified, OF F_minus_u, simplified, OF this]
  AOT_have \<Pi>_minus_\<kappa>_den: \<open>[\<Pi>]\<^sup>-\<^sup>\<kappa>\<down>\<close> for \<Pi> \<kappa> (* TODO: PLM: quietly dismissed *)
    by (rule \<Pi>_minus_\<kappa>I) cqt_2_lambda+

  AOT_have \<Pi>_minus_\<kappa>E1: \<open>[\<Pi>]\<kappa>'\<close> and \<Pi>_minus_\<kappa>E2: \<open>\<kappa>' \<noteq>\<^sub>E \<kappa>\<close> if \<open>[[\<Pi>]\<^sup>-\<^sup>\<kappa>]\<kappa>'\<close> for \<Pi> \<kappa> \<kappa>'
  proof -
    AOT_have \<open>[\<lambda>z [\<Pi>]z & z \<noteq>\<^sub>E \<kappa>]\<kappa>'\<close> using \<Pi>_minus_\<kappa>E that by fast
    AOT_hence \<open>[\<Pi>]\<kappa>' & \<kappa>' \<noteq>\<^sub>E \<kappa>\<close> by (rule betaC_1_a)
    AOT_thus \<open>[\<Pi>]\<kappa>'\<close> and \<open>\<kappa>' \<noteq>\<^sub>E \<kappa>\<close> using "&E" by blast+
  qed
  AOT_have \<Pi>_minus_\<kappa>I': \<open>[[\<Pi>]\<^sup>-\<^sup>\<kappa>]\<kappa>'\<close> if \<open>[\<Pi>]\<kappa>'\<close> and \<open>\<kappa>' \<noteq>\<^sub>E \<kappa>\<close> for \<Pi> \<kappa> \<kappa>'
  proof -
    AOT_have \<kappa>'_den: \<open>\<kappa>'\<down>\<close>  by (metis russell_axiom_exe_1.\<psi>_denotes_asm that(1))
    AOT_have \<open>[\<lambda>z [\<Pi>]z & z \<noteq>\<^sub>E \<kappa>]\<kappa>'\<close> by (rule betaC_2_a; cqt_2_lambda; safe intro!: \<kappa>'_den "&I" that)
    AOT_thus \<open>[[\<Pi>]\<^sup>-\<^sup>\<kappa>]\<kappa>'\<close> using \<Pi>_minus_\<kappa>I by fast
  qed

  AOT_assume Gv: \<open>[G]v\<close>
  AOT_assume Fu: \<open>[F]u\<close>
  AOT_assume \<open>[F]\<^sup>-\<^sup>u \<approx>\<^sub>E [G]\<^sup>-\<^sup>v\<close>
  AOT_hence \<open>\<exists>R R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E [G]\<^sup>-\<^sup>v\<close>
    using equi_3[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain R where R_prop: \<open>R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E [G]\<^sup>-\<^sup>v\<close> using "\<exists>E"[rotated] by blast
  AOT_hence Fact1: \<open>\<forall>r([[F]\<^sup>-\<^sup>u]r \<rightarrow> \<exists>!s ([[G]\<^sup>-\<^sup>v]s & [R]rs))\<close> and Fact1': \<open>\<forall>s([[G]\<^sup>-\<^sup>v]s \<rightarrow> \<exists>!r ([[F]\<^sup>-\<^sup>u]r & [R]rs))\<close>
    using equi_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
  AOT_have \<open>R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE [G]\<^sup>-\<^sup>v\<close>
    using equi_rem_thm[unvarify F G, OF \<Pi>_minus_\<kappa>_den, OF \<Pi>_minus_\<kappa>_den, THEN "\<equiv>E"(1), OF R_prop].
  AOT_hence \<open>R |: [F]\<^sup>-\<^sup>u \<^sub>1\<^sub>-\<^sub>1\<longrightarrow>E [G]\<^sup>-\<^sup>v & R |: [F]\<^sup>-\<^sup>u \<longrightarrow>\<^sub>o\<^sub>n\<^sub>t\<^sub>oE [G]\<^sup>-\<^sup>v\<close> using equi_rem_4[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  AOT_hence Fact2: \<open>\<forall>r\<forall>s\<forall>t(([[F]\<^sup>-\<^sup>u]r & [[F]\<^sup>-\<^sup>u]s & [[G]\<^sup>-\<^sup>v]t) \<rightarrow> ([R]rt & [R]st \<rightarrow> r =\<^sub>E s))\<close>
    using equi_rem_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast

  let ?R = \<open>\<guillemotleft>[\<lambda>xy ([[F]\<^sup>-\<^sup>u]x & [[G]\<^sup>-\<^sup>v]y & [R]xy) \<or> (x =\<^sub>E u & y =\<^sub>E v)]\<guillemotright>\<close>
  AOT_have R_den: \<open>\<guillemotleft>?R\<guillemotright>\<down>\<close> by cqt_2_lambda

  AOT_find_theorems \<open>F \<approx>\<^sub>E G\<close>
  AOT_show \<open>F \<approx>\<^sub>E G\<close>
  proof(safe intro!: equi_3[THEN "\<equiv>\<^sub>d\<^sub>fI"] "\<exists>I"(1)[where \<tau>="?R"] R_den equi_2[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" cqt_2_const_var[axiom_inst] GEN "\<rightarrow>I")
    fix r
    AOT_assume Or: \<open>O!r\<close>
    AOT_assume Fr: \<open>[F]r\<close>
    {
      AOT_assume not_r_eq_u: \<open>\<not>(r =\<^sub>E u)\<close>
      AOT_hence r_noteq_u: \<open>r \<noteq>\<^sub>E u\<close>
        using intro_elim_3_b thm_neg_eq_E by blast
      AOT_have \<open>[[F]\<^sup>-\<^sup>u]r\<close>
        by(rule \<Pi>_minus_\<kappa>I; rule betaC_2_a; cqt_2_lambda; safe intro!: cqt_2_const_var[axiom_inst] "&I" Fr r_noteq_u)
      AOT_hence \<open>\<exists>!s ([[G]\<^sup>-\<^sup>v]s & [R]rs)\<close> using Fact1[THEN "\<forall>E"(2)] "\<rightarrow>E" Or by blast
      AOT_hence \<open>\<exists>s ([[G]\<^sup>-\<^sup>v]s & [R]rs & \<forall>t ([[G]\<^sup>-\<^sup>v]t & [R]rt \<rightarrow> t =\<^sub>E s))\<close>
        using equi_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] by simp
      then AOT_obtain s where s_prop: \<open>O!s & ([[G]\<^sup>-\<^sup>v]s & [R]rs & \<forall>t ([[G]\<^sup>-\<^sup>v]t & [R]rt \<rightarrow> t =\<^sub>E s))\<close>
        using "\<exists>E"[rotated] by blast
      AOT_hence Os: \<open>O!s\<close> and G_minus_v_s: \<open>[[G]\<^sup>-\<^sup>v]s\<close> and Rrs: \<open>[R]rs\<close> using "&E" by blast+
      AOT_have s_unique: \<open>t =\<^sub>E s\<close> if \<open>O!t\<close> and \<open>[[G]\<^sup>-\<^sup>v]t\<close> and \<open>[R]rt\<close> for t
        using s_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF that(1), THEN "\<rightarrow>E", OF "&I", OF that(2,3)].
      AOT_have Gs: \<open>[G]s\<close> using \<Pi>_minus_\<kappa>E1[OF G_minus_v_s].
      AOT_have s_noteq_v: \<open>s \<noteq>\<^sub>E v\<close> using \<Pi>_minus_\<kappa>E2[OF G_minus_v_s].
      AOT_have \<open>\<exists>s ([G]s & [\<guillemotleft>?R\<guillemotright>]rs & (\<forall>t ([G]t & [\<guillemotleft>?R\<guillemotright>]rt \<rightarrow> t =\<^sub>E s)))\<close>
      proof(safe intro!: "\<exists>I"(2)[where \<beta>=s] "&I" Os Gs GEN "\<rightarrow>I")
        AOT_show \<open>[\<guillemotleft>?R\<guillemotright>]rs\<close>
          by (rule betaC_2_a; cqt_2_lambda; simp add: con_dis_i_e_1 ex_1_a prod_denotesI rule_ui_3;
              safe intro!: "&I" "\<or>I"(1) \<Pi>_minus_\<kappa>I' Fr Gs s_noteq_v Rrs r_noteq_u)
      next
        fix t
        AOT_assume Ot: \<open>O!t\<close>
        AOT_assume 0: \<open>[G]t & [\<guillemotleft>?R\<guillemotright>]rt\<close>
        AOT_hence \<open>([[F]\<^sup>-\<^sup>u]r & [[G]\<^sup>-\<^sup>v]t & [R]rt) \<or> (r =\<^sub>E u & t =\<^sub>E v)\<close>
          using betaC_1_a[OF 0[THEN "&E"(2)], simplified] by blast
        AOT_hence 1: \<open>[[F]\<^sup>-\<^sup>u]r & [[G]\<^sup>-\<^sup>v]t & [R]rt\<close>
          using not_r_eq_u by (metis con_dis_i_e_2_a con_dis_i_e_4_c reductio_aa_1)
        AOT_show \<open>t =\<^sub>E s\<close> using s_unique[OF Ot] 1 "&E" by blast
      qed
    }
    moreover {
      AOT_assume r_eq_u: \<open>r =\<^sub>E u\<close>
      AOT_have \<open>\<exists>s ([G]s & [\<guillemotleft>?R\<guillemotright>]rs & (\<forall>t ([G]t & [\<guillemotleft>?R\<guillemotright>]rt \<rightarrow> t =\<^sub>E s)))\<close>
      proof(safe intro!: "\<exists>I"(2)[where \<beta>=v] "&I" Ov Gv GEN "\<rightarrow>I")
        AOT_show \<open>[\<guillemotleft>?R\<guillemotright>]rv\<close>
          by (rule betaC_2_a; cqt_2_lambda; simp add: con_dis_i_e_1 ex_1_a prod_denotesI rule_ui_3)
             (safe intro!: "&I" "\<or>I"(2) \<Pi>_minus_\<kappa>I' Fr r_eq_u ord_eq_Eequiv_1[THEN "\<rightarrow>E", OF Ov])
      next
        fix t
        AOT_assume \<open>O!t\<close>
        AOT_assume 0: \<open>[G]t & [\<guillemotleft>?R\<guillemotright>]rt\<close>
        AOT_hence \<open>([[F]\<^sup>-\<^sup>u]r & [[G]\<^sup>-\<^sup>v]t & [R]rt) \<or> (r =\<^sub>E u & t =\<^sub>E v)\<close>
          using betaC_1_a[OF 0[THEN "&E"(2)], simplified] by blast
        AOT_hence \<open>r =\<^sub>E u & t =\<^sub>E v\<close>
          using r_eq_u \<Pi>_minus_\<kappa>E2 by (metis con_dis_i_e_2_a con_dis_i_e_4_b intro_elim_3_a reductio_aa_1 thm_neg_eq_E)
        AOT_thus \<open>t =\<^sub>E v\<close> using "&E" by blast
      qed
    }
    ultimately AOT_show \<open>\<exists>!s ([G]s & [\<guillemotleft>?R\<guillemotright>]rs)\<close> using reductio_aa_2 equi_1[THEN "\<equiv>\<^sub>d\<^sub>fI"] by fast
  next
    fix s
    AOT_assume Os: \<open>[O!]s\<close>
    AOT_assume Gs: \<open>[G]s\<close>

    {
      AOT_assume not_s_eq_v: \<open>\<not>(s =\<^sub>E v)\<close>
      AOT_hence s_noteq_v: \<open>s \<noteq>\<^sub>E v\<close>
        using intro_elim_3_b thm_neg_eq_E by blast
      AOT_have \<open>[[G]\<^sup>-\<^sup>v]s\<close>
        by (rule \<Pi>_minus_\<kappa>I; rule betaC_2_a; cqt_2_lambda; safe intro!: cqt_2_const_var[axiom_inst] "&I" Gs s_noteq_v)
      AOT_hence \<open>\<exists>!r ([[F]\<^sup>-\<^sup>u]r & [R]rs)\<close> using Fact1'[THEN "\<forall>E"(2)] "\<rightarrow>E" Os by blast
      AOT_hence \<open>\<exists>r ([[F]\<^sup>-\<^sup>u]r & [R]rs & \<forall>t ([[F]\<^sup>-\<^sup>u]t & [R]ts \<rightarrow> t =\<^sub>E r))\<close>
        using equi_1[THEN "\<equiv>\<^sub>d\<^sub>fE"] by simp
      then AOT_obtain r where r_prop: \<open>O!r & ([[F]\<^sup>-\<^sup>u]r & [R]rs & \<forall>t ([[F]\<^sup>-\<^sup>u]t & [R]ts \<rightarrow> t =\<^sub>E r))\<close>
        using "\<exists>E"[rotated] by blast
      AOT_hence Or: \<open>O!r\<close> and F_minus_u_r: \<open>[[F]\<^sup>-\<^sup>u]r\<close> and Rrs: \<open>[R]rs\<close> using "&E" by blast+
      AOT_have r_unique: \<open>t =\<^sub>E r\<close> if \<open>O!t\<close> and \<open>[[F]\<^sup>-\<^sup>u]t\<close> and \<open>[R]ts\<close> for t
        using r_prop[THEN "&E"(2), THEN "&E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF that(1), THEN "\<rightarrow>E", OF "&I", OF that(2,3)].
      AOT_have Fr: \<open>[F]r\<close> using \<Pi>_minus_\<kappa>E1[OF F_minus_u_r].
      AOT_have r_noteq_u: \<open>r \<noteq>\<^sub>E u\<close> using \<Pi>_minus_\<kappa>E2[OF F_minus_u_r].
      AOT_have \<open>\<exists>r ([F]r & [\<guillemotleft>?R\<guillemotright>]rs & (\<forall>t ([F]t & [\<guillemotleft>?R\<guillemotright>]ts \<rightarrow> t =\<^sub>E r)))\<close>
      proof(safe intro!: "\<exists>I"(2)[where \<beta>=r] "&I" Or Fr GEN "\<rightarrow>I")
        AOT_show \<open>[\<guillemotleft>?R\<guillemotright>]rs\<close>
          by (rule betaC_2_a; cqt_2_lambda; simp add: con_dis_i_e_1 ex_1_a prod_denotesI rule_ui_3;
              safe intro!: "&I" "\<or>I"(1) \<Pi>_minus_\<kappa>I' Fr Gs s_noteq_v Rrs r_noteq_u)
      next
        fix t
        AOT_assume Ot: \<open>O!t\<close>
        AOT_assume 0: \<open>[F]t & [\<guillemotleft>?R\<guillemotright>]ts\<close>
        AOT_hence \<open>([[F]\<^sup>-\<^sup>u]t & [[G]\<^sup>-\<^sup>v]s & [R]ts) \<or> (t =\<^sub>E u & s =\<^sub>E v)\<close>
          using betaC_1_a[OF 0[THEN "&E"(2)], simplified] by blast
        AOT_hence 1: \<open>[[F]\<^sup>-\<^sup>u]t & [[G]\<^sup>-\<^sup>v]s & [R]ts\<close>
          using not_s_eq_v by (metis con_dis_i_e_2_b con_dis_i_e_4_c reductio_aa_1)
        AOT_show \<open>t =\<^sub>E r\<close> using r_unique[OF Ot] 1 "&E" by blast
      qed
    }
    moreover {
      AOT_assume s_eq_v: \<open>s =\<^sub>E v\<close>
      AOT_have \<open>\<exists>r ([F]r & [\<guillemotleft>?R\<guillemotright>]rs & (\<forall>t ([F]t & [\<guillemotleft>?R\<guillemotright>]ts \<rightarrow> t =\<^sub>E r)))\<close>
      proof(safe intro!: "\<exists>I"(2)[where \<beta>=u] "&I" Ou Fu GEN "\<rightarrow>I")
        AOT_show \<open>[\<guillemotleft>?R\<guillemotright>]us\<close>
          by (rule betaC_2_a; cqt_2_lambda; simp add: con_dis_i_e_1 ex_1_a prod_denotesI rule_ui_3)
             (safe intro!: "&I" "\<or>I"(2) \<Pi>_minus_\<kappa>I' Gs s_eq_v ord_eq_Eequiv_1[THEN "\<rightarrow>E", OF Ou])
      next
        fix t
        AOT_assume \<open>O!t\<close>
        AOT_assume 0: \<open>[F]t & [\<guillemotleft>?R\<guillemotright>]ts\<close>
        AOT_hence 1: \<open>([[F]\<^sup>-\<^sup>u]t & [[G]\<^sup>-\<^sup>v]s & [R]ts) \<or> (t =\<^sub>E u & s =\<^sub>E v)\<close>
          using betaC_1_a[OF 0[THEN "&E"(2)], simplified] by blast
        moreover AOT_have \<open>\<not>([[F]\<^sup>-\<^sup>u]t & [[G]\<^sup>-\<^sup>v]s & [R]ts)\<close>
        proof (rule raa_cor_2)
          AOT_assume \<open>([[F]\<^sup>-\<^sup>u]t & [[G]\<^sup>-\<^sup>v]s & [R]ts)\<close>
          AOT_hence \<open>[[G]\<^sup>-\<^sup>v]s\<close> using "&E" by blast
          AOT_thus \<open>s =\<^sub>E v & \<not>(s =\<^sub>E v)\<close>
            by (metis \<Pi>_minus_\<kappa>E2 intro_elim_3_d reductio_aa_1 s_eq_v thm_neg_eq_E)
        qed
        ultimately AOT_have \<open>t =\<^sub>E u & s =\<^sub>E v\<close>
          by (metis con_dis_i_e_4_b)
        AOT_thus \<open>t =\<^sub>E u\<close> using "&E" by blast
      qed
    }
    ultimately AOT_show \<open>\<exists>!r ([F]r & [\<guillemotleft>?R\<guillemotright>]rs)\<close>
      using "\<equiv>\<^sub>d\<^sub>fI" equi_1 reductio_aa_2 by fast
  qed
qed

end
