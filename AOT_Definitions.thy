theory AOT_Definitions
  imports AOT_semantics
begin

section\<open>Definitions of AOT\<close>

AOT_theorem "conventions:1": \<open>\<phi> & \<psi> \<equiv>\<^sub>d\<^sub>f \<not>(\<phi> \<rightarrow> \<not>\<psi>)\<close>
  using AOT_conj.
AOT_theorem "conventions:2": \<open>\<phi> \<or> \<psi> \<equiv>\<^sub>d\<^sub>f \<not>\<phi> \<rightarrow> \<psi>\<close>
  using AOT_disj.
AOT_theorem "conventions:3": \<open>\<phi> \<equiv> \<psi> \<equiv>\<^sub>d\<^sub>f (\<phi> \<rightarrow> \<psi>) & (\<psi> \<rightarrow> \<phi>)\<close>
  using AOT_equiv.
AOT_theorem "conventions:4": \<open>\<exists>\<alpha> \<phi>{\<alpha>} \<equiv>\<^sub>d\<^sub>f \<not>\<forall>\<alpha> \<not>\<phi>{\<alpha>}\<close>
  using AOT_exists.
AOT_theorem "conventions:5": \<open>\<diamond>\<phi> \<equiv>\<^sub>d\<^sub>f \<not>\<box>\<not>\<phi>\<close>
  using AOT_dia.

declare "conventions:1"[AOT_defs] "conventions:2"[AOT_defs]
        "conventions:3"[AOT_defs] "conventions:4"[AOT_defs]
        "conventions:5"[AOT_defs]

notepad
begin
  fix \<phi> \<psi> \<chi>
  text\<open>\linelabel{precedence}\<close>
  have "conventions3[1]": \<open>\<guillemotleft>\<phi> \<rightarrow> \<psi> \<equiv> \<not>\<psi> \<rightarrow> \<not>\<phi>\<guillemotright> = \<guillemotleft>(\<phi> \<rightarrow> \<psi>) \<equiv> (\<not>\<psi> \<rightarrow> \<not>\<phi>)\<guillemotright>\<close>
    by blast
  have "conventions3[2]": \<open>\<guillemotleft>\<phi> & \<psi> \<rightarrow> \<chi>\<guillemotright> = \<guillemotleft>(\<phi> & \<psi>) \<rightarrow> \<chi>\<guillemotright>\<close>
                   and \<open>\<guillemotleft>\<phi> \<or> \<psi> \<rightarrow> \<chi>\<guillemotright> = \<guillemotleft>(\<phi> \<or> \<psi>) \<rightarrow> \<chi>\<guillemotright>\<close>
    by blast+
  have "conventions3[3]": \<open>\<guillemotleft>\<phi> \<or> \<psi> & \<chi>\<guillemotright> = \<guillemotleft>(\<phi> \<or> \<psi>) & \<chi>\<guillemotright>\<close>
                   and \<open>\<guillemotleft>\<phi> & \<psi> \<or> \<chi>\<guillemotright> = \<guillemotleft>(\<phi> & \<psi>) \<or> \<chi>\<guillemotright>\<close>
     by blast+
end


AOT_theorem "existence:1": \<open>\<kappa>\<down> \<equiv>\<^sub>d\<^sub>f \<exists>F [F]\<kappa>\<close>
  by (simp add: AOT_sem_denotes AOT_sem_exists AOT_model_equiv_def)
     (metis AOT_sem_denotes AOT_sem_exe AOT_sem_lambda_beta AOT_sem_lambda_denotes)
AOT_theorem "existence:2": \<open>\<Pi>\<down> \<equiv>\<^sub>d\<^sub>f \<exists>x\<^sub>1...\<exists>x\<^sub>n x\<^sub>1...x\<^sub>n[\<Pi>]\<close>
  using AOT_sem_denotes AOT_sem_enc_denotes AOT_sem_universal_encoder
  by (simp add: AOT_sem_denotes AOT_sem_exists AOT_model_equiv_def) blast
AOT_theorem "existence:2[1]": \<open>\<Pi>\<down> \<equiv>\<^sub>d\<^sub>f \<exists>x x[\<Pi>]\<close>
  using "existence:2"[of \<Pi>] by simp
AOT_theorem "existence:2[2]": \<open>\<Pi>\<down> \<equiv>\<^sub>d\<^sub>f \<exists>x\<exists>y xy[\<Pi>]\<close>
  using "existence:2"[of \<Pi>]
  by (simp add: AOT_sem_denotes AOT_sem_exists AOT_model_equiv_def
                AOT_model_denotes_prod_def)
AOT_theorem "existence:2[3]": \<open>\<Pi>\<down> \<equiv>\<^sub>d\<^sub>f \<exists>x\<exists>y\<exists>z xyz[\<Pi>]\<close>
  using "existence:2"[of \<Pi>]
  by (simp add: AOT_sem_denotes AOT_sem_exists AOT_model_equiv_def
                AOT_model_denotes_prod_def)
AOT_theorem "existence:2[4]": \<open>\<Pi>\<down> \<equiv>\<^sub>d\<^sub>f \<exists>x\<^sub>1\<exists>x\<^sub>2\<exists>x\<^sub>3\<exists>x\<^sub>4 x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[\<Pi>]\<close>
  using "existence:2"[of \<Pi>]
  by (simp add: AOT_sem_denotes AOT_sem_exists AOT_model_equiv_def
                AOT_model_denotes_prod_def)

AOT_theorem "existence:3": \<open>\<phi>\<down> \<equiv>\<^sub>d\<^sub>f [\<lambda>x \<phi>]\<down>\<close>
  by (simp add: AOT_sem_denotes AOT_model_denotes_\<o>_def AOT_model_equiv_def
                AOT_model_lambda_denotes)

declare "existence:1"[AOT_defs] "existence:2"[AOT_defs] "existence:2[1]"[AOT_defs]
        "existence:2[2]"[AOT_defs] "existence:2[3]"[AOT_defs]
        "existence:2[4]"[AOT_defs] "existence:3"[AOT_defs]


AOT_theorem "oa:1": \<open>O! =\<^sub>d\<^sub>f [\<lambda>x \<diamond>E!x]\<close> using AOT_ordinary .
AOT_theorem "oa:2": \<open>A! =\<^sub>d\<^sub>f [\<lambda>x \<not>\<diamond>E!x]\<close> using AOT_abstract .

declare "oa:1"[AOT_defs] "oa:2"[AOT_defs]

AOT_theorem "identity:1":
  \<open>x = y \<equiv>\<^sub>d\<^sub>f ([O!]x & [O!]y & \<box>\<forall>F ([F]x \<equiv> [F]y)) \<or>
             ([A!]x & [A!]y & \<box>\<forall>F (x[F] \<equiv> y[F]))\<close>
  unfolding AOT_model_equiv_def
  using AOT_sem_ind_eq[of _ x y]
  by (simp add: AOT_sem_ordinary AOT_sem_abstract AOT_sem_conj
                AOT_sem_box AOT_sem_equiv AOT_sem_forall AOT_sem_disj AOT_sem_eq
                AOT_sem_denotes)

AOT_theorem "identity:2":
  \<open>F = G \<equiv>\<^sub>d\<^sub>f F\<down> & G\<down> & \<box>\<forall>x(x[F] \<equiv> x[G])\<close>
  using AOT_sem_enc_eq[of _ F G]
  by (auto simp: AOT_model_equiv_def AOT_sem_imp AOT_sem_denotes AOT_sem_eq
                 AOT_sem_conj AOT_sem_forall AOT_sem_box AOT_sem_equiv)

AOT_theorem "identity:3[2]":
  \<open>F = G \<equiv>\<^sub>d\<^sub>f F\<down> & G\<down> & \<forall>y([\<lambda>z [F]zy] = [\<lambda>z [G]zy] & [\<lambda>z [F]yz] = [\<lambda>z [G]yz])\<close>
  by (auto simp: AOT_model_equiv_def AOT_sem_proj_id_prop[of _ F G]
                 AOT_sem_proj_id_prod_def AOT_sem_conj AOT_sem_denotes
                 AOT_sem_forall AOT_sem_unary_proj_id AOT_model_denotes_prod_def)
AOT_theorem "identity:3[3]":
  \<open>F = G \<equiv>\<^sub>d\<^sub>f F\<down> & G\<down> & \<forall>y\<^sub>1\<forall>y\<^sub>2([\<lambda>z [F]zy\<^sub>1y\<^sub>2] = [\<lambda>z [G]zy\<^sub>1y\<^sub>2] &
                              [\<lambda>z [F]y\<^sub>1zy\<^sub>2] = [\<lambda>z [G]y\<^sub>1zy\<^sub>2] &
                              [\<lambda>z [F]y\<^sub>1y\<^sub>2z] = [\<lambda>z [G]y\<^sub>1y\<^sub>2z])\<close>
  by (auto simp: AOT_model_equiv_def AOT_sem_proj_id_prop[of _ F G]
                 AOT_sem_proj_id_prod_def AOT_sem_conj AOT_sem_denotes
                 AOT_sem_forall AOT_sem_unary_proj_id AOT_model_denotes_prod_def)
AOT_theorem "identity:3[4]":
  \<open>F = G \<equiv>\<^sub>d\<^sub>f F\<down> & G\<down> & \<forall>y\<^sub>1\<forall>y\<^sub>2\<forall>y\<^sub>3([\<lambda>z [F]zy\<^sub>1y\<^sub>2y\<^sub>3] = [\<lambda>z [G]zy\<^sub>1y\<^sub>2y\<^sub>3] &
                                [\<lambda>z [F]y\<^sub>1zy\<^sub>2y\<^sub>3] = [\<lambda>z [G]y\<^sub>1zy\<^sub>2y\<^sub>3] &
                                [\<lambda>z [F]y\<^sub>1y\<^sub>2zy\<^sub>3] = [\<lambda>z [G]y\<^sub>1y\<^sub>2zy\<^sub>3] &
                                [\<lambda>z [F]y\<^sub>1y\<^sub>2y\<^sub>3z] = [\<lambda>z [G]y\<^sub>1y\<^sub>2y\<^sub>3z])\<close>
  by (auto simp: AOT_model_equiv_def AOT_sem_proj_id_prop[of _ F G]
                 AOT_sem_proj_id_prod_def AOT_sem_conj AOT_sem_denotes
                 AOT_sem_forall AOT_sem_unary_proj_id AOT_model_denotes_prod_def)
AOT_theorem "identity:3":
  \<open>F = G \<equiv>\<^sub>d\<^sub>f F\<down> & G\<down> & \<forall>x\<^sub>1...\<forall>x\<^sub>n \<guillemotleft>AOT_sem_proj_id x\<^sub>1x\<^sub>n (\<lambda> \<tau> . AOT_exe F \<tau>)
                                                      (\<lambda> \<tau> . AOT_exe G \<tau>)\<guillemotright>\<close>
  by (auto simp: AOT_model_equiv_def AOT_sem_proj_id_prop[of _ F G]
                 AOT_sem_proj_id_prod_def AOT_sem_conj AOT_sem_denotes
                 AOT_sem_forall AOT_sem_unary_proj_id AOT_model_denotes_prod_def)

AOT_theorem "identity:4":
  \<open>p = q \<equiv>\<^sub>d\<^sub>f p\<down> & q\<down> & [\<lambda>x p] = [\<lambda>x q]\<close>
  by (auto simp: AOT_model_equiv_def AOT_sem_eq AOT_sem_denotes AOT_sem_conj
                 AOT_model_lambda_denotes AOT_sem_lambda_eq_prop_eq)

declare "identity:1"[AOT_defs] "identity:2"[AOT_defs] "identity:3[2]"[AOT_defs]
        "identity:3[3]"[AOT_defs] "identity:3[4]"[AOT_defs] "identity:3"[AOT_defs]
        "identity:4"[AOT_defs]

AOT_define AOT_nonidentical :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl "\<noteq>" 50)
  "=-infix": \<open>\<tau> \<noteq> \<sigma> \<equiv>\<^sub>d\<^sub>f \<not>(\<tau> = \<sigma>)\<close>

context AOT_meta_syntax
begin
notation AOT_nonidentical (infixl "\<^bold>\<noteq>" 50)
end
context AOT_no_meta_syntax
begin
no_notation AOT_nonidentical (infixl "\<^bold>\<noteq>" 50)
end


text\<open>The following are purely technical pseudo-definitions required due to
     our internal implementation of n-ary relations and ellipses using tuples.\<close>
AOT_theorem tuple_denotes: \<open>\<guillemotleft>(\<tau>,\<tau>')\<guillemotright>\<down> \<equiv>\<^sub>d\<^sub>f \<tau>\<down> & \<tau>'\<down>\<close>
  by (simp add: AOT_model_denotes_prod_def AOT_model_equiv_def
                AOT_sem_conj AOT_sem_denotes)
AOT_theorem tuple_identity_1: \<open>\<guillemotleft>(\<tau>,\<tau>')\<guillemotright> = \<guillemotleft>(\<sigma>, \<sigma>')\<guillemotright> \<equiv>\<^sub>d\<^sub>f (\<tau> = \<sigma>) & (\<tau>' = \<sigma>')\<close>
  by (auto simp: AOT_model_equiv_def AOT_sem_conj AOT_sem_eq
                 AOT_model_denotes_prod_def AOT_sem_denotes)
AOT_theorem tuple_forall: \<open>\<forall>\<alpha>\<^sub>1...\<forall>\<alpha>\<^sub>n \<phi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n} \<equiv>\<^sub>d\<^sub>f \<forall>\<alpha>\<^sub>1(\<forall>\<alpha>\<^sub>2...\<forall>\<alpha>\<^sub>n \<phi>{\<guillemotleft>(\<alpha>\<^sub>1, \<alpha>\<^sub>2\<alpha>\<^sub>n)\<guillemotright>})\<close>
  by (auto simp: AOT_model_equiv_def AOT_sem_forall AOT_sem_denotes
                 AOT_model_denotes_prod_def)
AOT_theorem tuple_exists: \<open>\<exists>\<alpha>\<^sub>1...\<exists>\<alpha>\<^sub>n \<phi>{\<alpha>\<^sub>1...\<alpha>\<^sub>n} \<equiv>\<^sub>d\<^sub>f \<exists>\<alpha>\<^sub>1(\<exists>\<alpha>\<^sub>2...\<exists>\<alpha>\<^sub>n \<phi>{\<guillemotleft>(\<alpha>\<^sub>1, \<alpha>\<^sub>2\<alpha>\<^sub>n)\<guillemotright>})\<close>
  by (auto simp: AOT_model_equiv_def AOT_sem_exists AOT_sem_denotes
                 AOT_model_denotes_prod_def)
declare tuple_denotes[AOT_defs] tuple_identity_1[AOT_defs] tuple_forall[AOT_defs]
        tuple_exists[AOT_defs]

end
