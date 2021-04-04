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
  Ordinary: u v t s

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

AOT_theorem eqP': \<open>F \<approx>\<^sub>E G & [F]u & [G]v \<rightarrow> [F]\<^sup>-\<^sup>u \<approx>\<^sub>E [G]\<^sup>-\<^sup>v\<close>
proof (rule "\<rightarrow>I"; frule "&E"(2); drule "&E"(1); frule "&E"(2); drule "&E"(1))
  AOT_assume \<open>F \<approx>\<^sub>E G\<close>
  AOT_hence \<open>\<exists>R R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close>
    using equi_3[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  then AOT_obtain R where \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G\<close> using "\<exists>E"[rotated] by blast
  AOT_hence \<open>\<forall>u ([F]u \<rightarrow> \<exists>!v ([G]v & [R]uv))\<close> and \<open>\<forall>v ([G]v \<rightarrow> \<exists>!u ([F]u & [R]uv))\<close>
    using equi_2[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast+
(* TODO: proof equi_rem_thm  first *)
  AOT_assume \<open>[F]u\<close>
  AOT_assume \<open>[G]v\<close>
  AOT_show \<open>[F]\<^sup>-\<^sup>u \<approx>\<^sub>E [G]\<^sup>-\<^sup>v\<close>
    sorry
qed


end
