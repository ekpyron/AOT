theory AOT_BasicLogicalObjects
  imports AOT_PLM
begin

(* TODO: so far only the parts required for possible world theory *)

AOT_define TruthValueOf :: \<open>\<tau> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (\<open>TruthValueOf'(_,_')\<close>)
  tv_p: \<open>TruthValueOf(x,p) \<equiv>\<^sub>d\<^sub>f A!x & \<forall>F (x[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q]))\<close>

AOT_theorem p_has_tv_1: \<open>\<exists>x TruthValueOf(x,p)\<close>
  by (AOT_subst \<open>\<lambda> \<kappa> . \<guillemotleft>TruthValueOf(\<kappa>,p)\<guillemotright>\<close> \<open>\<lambda> \<kappa> . \<guillemotleft>A!\<kappa> & \<forall>F (\<kappa>[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q]))\<guillemotright>\<close>)
     (fact a_objects[where \<phi>=\<open>\<lambda> \<Pi> . \<guillemotleft>\<exists>q ((q \<equiv>p) & \<Pi> = [\<lambda>y q])\<guillemotright>\<close>, axiom_inst])

AOT_theorem p_has_tv_2: \<open>\<exists>!x TruthValueOf(x,p)\<close>
  by (AOT_subst \<open>\<lambda> \<kappa> . \<guillemotleft>TruthValueOf(\<kappa>,p)\<guillemotright>\<close> \<open>\<lambda> \<kappa> . \<guillemotleft>A!\<kappa> & \<forall>F (\<kappa>[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q]))\<guillemotright>\<close>)

AOT_theorem uni_tv: \<open>\<^bold>\<iota>x TruthValueOf(x,p)\<down>\<close>
  using A_Exists_2 RA_2 intro_elim_3_b p_has_tv_2 by blast

AOT_define the_tv_p :: \<open>\<phi> \<Rightarrow> \<tau>\<close> (\<open>\<circ>_\<close>)
  \<open>\<circ>p =\<^sub>d\<^sub>f \<^bold>\<iota>x TruthValueOf(x,p)\<close>

AOT_theorem tv_id: \<open>\<circ>p = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q])))\<close>
proof -
  AOT_have \<open>\<box>\<forall>x(TruthValueOf(x,p)  \<equiv> A!x & \<forall>F (x[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q])))\<close>
    by (rule RN; rule GEN; rule tv_p[THEN "\<equiv>Df"])
  AOT_hence \<open>\<^bold>\<iota>x TruthValueOf(x,p) = \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>q((q \<equiv> p) & F = [\<lambda>y q])))\<close>
    using equiv_desc_eq_3[THEN "\<rightarrow>E", OF "&I", OF uni_tv] by simp
  thus ?thesis
    using "=\<^sub>d\<^sub>fI"(1)[OF the_tv_p, OF uni_tv] by fast
qed

(* TODO more theorems *)

AOT_define TruthValue :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>TruthValue'(_')\<close>)
  T_value: \<open>TruthValue(x) \<equiv>\<^sub>d\<^sub>f \<exists>p (TruthValueOf(x,p))\<close>

(* TODO more theorems *)

AOT_define prop_enc :: \<open>\<tau> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (infixl \<open>\<^bold>\<Sigma>\<close> 40)
  \<open>x\<^bold>\<Sigma>p \<equiv>\<^sub>d\<^sub>f x\<down> & x[\<lambda>y p]\<close>

(* TODO more theorems *)

AOT_define TheTrue :: \<tau> (\<open>\<top>\<close>)
  the_true_1: \<open>\<top> =\<^sub>d\<^sub>f \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(p & F = [\<lambda>y p])))\<close>
AOT_define TheFalse :: \<tau> (\<open>\<bottom>\<close>)
  the_true_2: \<open>\<bottom> =\<^sub>d\<^sub>f \<^bold>\<iota>x (A!x & \<forall>F (x[F] \<equiv> \<exists>p(p & F = [\<lambda>y p])))\<close>

end