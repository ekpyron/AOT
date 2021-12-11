(*<*)
theory AOT_Axioms
  imports AOT_Definitions
begin
(*>*)

section\<open>Axioms of PLM\<close>

AOT_axiom "pl:1": \<open>\<phi> \<rightarrow> (\<psi> \<rightarrow> \<phi>)\<close>
  by (auto simp: AOT_sem_imp AOT_model_axiomI)
AOT_axiom "pl:2": \<open>(\<phi> \<rightarrow> (\<psi> \<rightarrow> \<chi>)) \<rightarrow> ((\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<phi> \<rightarrow> \<chi>))\<close>
  by (auto simp: AOT_sem_imp AOT_model_axiomI)
AOT_axiom "pl:3": \<open>(\<not>\<phi> \<rightarrow> \<not>\<psi>) \<rightarrow> ((\<not>\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>)\<close>
  by (auto simp: AOT_sem_imp AOT_sem_not AOT_model_axiomI)

AOT_axiom "cqt:1": \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> (\<tau>\<down> \<rightarrow> \<phi>{\<tau>})\<close>
  by (auto simp: AOT_sem_denotes AOT_sem_forall AOT_sem_imp AOT_model_axiomI)

AOT_axiom "cqt:2[const_var]": \<open>\<alpha>\<down>\<close>
  using AOT_sem_vars_denote by (rule AOT_model_axiomI)
AOT_axiom "cqt:2[lambda]":
  assumes \<open>INSTANCE_OF_CQT_2(\<phi>)\<close>
  shows \<open>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down>\<close>
  by (auto intro!: AOT_model_axiomI AOT_sem_cqt_2[OF assms])
AOT_axiom "cqt:2[lambda0]":
  shows \<open>[\<lambda> \<phi>]\<down>\<close>
  by (auto intro!: AOT_model_axiomI
           simp: AOT_sem_lambda_denotes "existence:3"[unfolded AOT_model_equiv_def])

AOT_axiom "cqt:3": \<open>\<forall>\<alpha> (\<phi>{\<alpha>} \<rightarrow> \<psi>{\<alpha>}) \<rightarrow> (\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> \<forall>\<alpha> \<psi>{\<alpha>})\<close>
  by (simp add: AOT_sem_forall AOT_sem_imp AOT_model_axiomI)
AOT_axiom "cqt:4": \<open>\<phi> \<rightarrow> \<forall>\<alpha> \<phi>\<close>
  by (simp add: AOT_sem_forall AOT_sem_imp AOT_model_axiomI)
AOT_axiom "cqt:5:a": \<open>[\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>)\<close>
  by (simp add: AOT_sem_conj AOT_sem_denotes AOT_sem_exe
                AOT_sem_imp AOT_model_axiomI)
AOT_axiom "cqt:5:a[1]": \<open>[\<Pi>]\<kappa> \<rightarrow> (\<Pi>\<down> & \<kappa>\<down>)\<close>
  using "cqt:5:a" AOT_model_axiomI by blast
AOT_axiom "cqt:5:a[2]": \<open>[\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2 \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1\<down> & \<kappa>\<^sub>2\<down>)\<close>
  by (rule AOT_model_axiomI)
     (metis AOT_model_denotes_prod_def AOT_sem_conj AOT_sem_denotes AOT_sem_exe
            AOT_sem_imp case_prodD)
AOT_axiom "cqt:5:a[3]": \<open>[\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3 \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1\<down> & \<kappa>\<^sub>2\<down> & \<kappa>\<^sub>3\<down>)\<close>
  by (rule AOT_model_axiomI)
     (metis AOT_model_denotes_prod_def AOT_sem_conj AOT_sem_denotes AOT_sem_exe
            AOT_sem_imp case_prodD)
AOT_axiom "cqt:5:a[4]": \<open>[\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4 \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1\<down> & \<kappa>\<^sub>2\<down> & \<kappa>\<^sub>3\<down> & \<kappa>\<^sub>4\<down>)\<close>
  by (rule AOT_model_axiomI)
     (metis AOT_model_denotes_prod_def AOT_sem_conj AOT_sem_denotes AOT_sem_exe
            AOT_sem_imp case_prodD)
AOT_axiom "cqt:5:b": \<open>\<kappa>\<^sub>1...\<kappa>\<^sub>n[\<Pi>] \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>)\<close>
  using AOT_sem_enc_denotes
  by (auto intro!: AOT_model_axiomI simp: AOT_sem_conj AOT_sem_denotes AOT_sem_imp)+
AOT_axiom "cqt:5:b[1]": \<open>\<kappa>[\<Pi>] \<rightarrow> (\<Pi>\<down> & \<kappa>\<down>)\<close>
  using "cqt:5:b" AOT_model_axiomI by blast
AOT_axiom "cqt:5:b[2]": \<open>\<kappa>\<^sub>1\<kappa>\<^sub>2[\<Pi>] \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1\<down> & \<kappa>\<^sub>2\<down>)\<close>
  by (rule AOT_model_axiomI)
     (metis AOT_model_denotes_prod_def AOT_sem_conj AOT_sem_denotes
            AOT_sem_enc_denotes AOT_sem_imp case_prodD)
AOT_axiom "cqt:5:b[3]": \<open>\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3[\<Pi>] \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1\<down> & \<kappa>\<^sub>2\<down> & \<kappa>\<^sub>3\<down>)\<close>
  by (rule AOT_model_axiomI)
     (metis AOT_model_denotes_prod_def AOT_sem_conj AOT_sem_denotes
            AOT_sem_enc_denotes AOT_sem_imp case_prodD)
AOT_axiom "cqt:5:b[4]": \<open>\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4[\<Pi>] \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1\<down> & \<kappa>\<^sub>2\<down> & \<kappa>\<^sub>3\<down> & \<kappa>\<^sub>4\<down>)\<close>
  by (rule AOT_model_axiomI)
     (metis AOT_model_denotes_prod_def AOT_sem_conj AOT_sem_denotes
            AOT_sem_enc_denotes AOT_sem_imp case_prodD)

AOT_axiom "l-identity": \<open>\<alpha> = \<beta> \<rightarrow> (\<phi>{\<alpha>} \<rightarrow> \<phi>{\<beta>})\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_eq AOT_sem_imp)

AOT_act_axiom "logic-actual": \<open>\<^bold>\<A>\<phi> \<rightarrow> \<phi>\<close>
  by (rule AOT_model_act_axiomI)
     (simp add: AOT_sem_act AOT_sem_imp)

AOT_axiom "logic-actual-nec:1": \<open>\<^bold>\<A>\<not>\<phi> \<equiv> \<not>\<^bold>\<A>\<phi>\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_act AOT_sem_equiv AOT_sem_not)
AOT_axiom "logic-actual-nec:2": \<open>\<^bold>\<A>(\<phi> \<rightarrow> \<psi>) \<equiv> (\<^bold>\<A>\<phi> \<rightarrow> \<^bold>\<A>\<psi>)\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_act AOT_sem_equiv AOT_sem_imp)

AOT_axiom "logic-actual-nec:3": \<open>\<^bold>\<A>(\<forall>\<alpha> \<phi>{\<alpha>}) \<equiv> \<forall>\<alpha> \<^bold>\<A>\<phi>{\<alpha>}\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_act AOT_sem_equiv AOT_sem_forall AOT_sem_denotes)
AOT_axiom "logic-actual-nec:4": \<open>\<^bold>\<A>\<phi> \<equiv> \<^bold>\<A>\<^bold>\<A>\<phi>\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_act AOT_sem_equiv)

AOT_axiom "qml:1": \<open>\<box>(\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<box>\<phi> \<rightarrow> \<box>\<psi>)\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_box AOT_sem_imp)
AOT_axiom "qml:2": \<open>\<box>\<phi> \<rightarrow> \<phi>\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_box AOT_sem_imp)
AOT_axiom "qml:3": \<open>\<diamond>\<phi> \<rightarrow> \<box>\<diamond>\<phi>\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_box AOT_sem_dia AOT_sem_imp)

AOT_axiom "qml:4": \<open>\<diamond>\<exists>x (E!x & \<not>\<^bold>\<A>E!x)\<close>
  using AOT_sem_concrete AOT_model_contingent
  by (auto intro!: AOT_model_axiomI
             simp: AOT_sem_box AOT_sem_dia AOT_sem_imp AOT_sem_exists
                   AOT_sem_denotes AOT_sem_conj AOT_sem_not AOT_sem_act
                   AOT_sem_exe)+

AOT_axiom "qml-act:1": \<open>\<^bold>\<A>\<phi> \<rightarrow> \<box>\<^bold>\<A>\<phi>\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_act AOT_sem_box AOT_sem_imp)
AOT_axiom "qml-act:2": \<open>\<box>\<phi> \<equiv> \<^bold>\<A>\<box>\<phi>\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_act AOT_sem_box AOT_sem_equiv)

AOT_axiom descriptions: \<open>x = \<^bold>\<iota>x(\<phi>{x}) \<equiv> \<forall>z(\<^bold>\<A>\<phi>{z} \<equiv> z = x)\<close>
proof (rule AOT_model_axiomI)
  AOT_modally_strict {
    AOT_show \<open>x = \<^bold>\<iota>x(\<phi>{x}) \<equiv> \<forall>z(\<^bold>\<A>\<phi>{z} \<equiv> z = x)\<close>
      by (induct; simp add: AOT_sem_equiv AOT_sem_forall AOT_sem_act AOT_sem_eq)
         (metis (no_types, hide_lams) AOT_sem_desc_denotes AOT_sem_desc_prop
                                      AOT_sem_denotes)
  }
qed

AOT_axiom "lambda-predicates:1":
  \<open>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down> \<rightarrow> [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}] = [\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<mu>\<^sub>1...\<mu>\<^sub>n}]\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_denotes AOT_sem_eq AOT_sem_imp)
AOT_axiom "lambda-predicates:1[zero]": \<open>[\<lambda> p]\<down> \<rightarrow> [\<lambda> p] = [\<lambda> p]\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_denotes AOT_sem_eq AOT_sem_imp)
AOT_axiom "lambda-predicates:2":
  \<open>[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]\<down> \<rightarrow> ([\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]x\<^sub>1...x\<^sub>n \<equiv> \<phi>{x\<^sub>1...x\<^sub>n})\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_equiv AOT_sem_imp AOT_sem_lambda_beta AOT_sem_vars_denote)
AOT_axiom "lambda-predicates:3": \<open>[\<lambda>x\<^sub>1...x\<^sub>n [F]x\<^sub>1...x\<^sub>n] = F\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_lambda_eta AOT_sem_vars_denote)
AOT_axiom "lambda-predicates:3[zero]": \<open>[\<lambda> p] = p\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_eq AOT_sem_lambda0 AOT_sem_vars_denote)

AOT_axiom "safe-ext":
  \<open>([\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down> & \<box>\<forall>\<nu>\<^sub>1...\<forall>\<nu>\<^sub>n (\<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n} \<equiv> \<psi>{\<nu>\<^sub>1...\<nu>\<^sub>n})) \<rightarrow>
   [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<psi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down>\<close>
  using AOT_sem_lambda_coex
  by (auto intro!: AOT_model_axiomI simp: AOT_sem_imp AOT_sem_denotes AOT_sem_conj
                   AOT_sem_equiv AOT_sem_box AOT_sem_forall)
AOT_axiom "safe-ext[2]":
  \<open>([\<lambda>\<nu>\<^sub>1\<nu>\<^sub>2 \<phi>{\<nu>\<^sub>1,\<nu>\<^sub>2}]\<down> & \<box>\<forall>\<nu>\<^sub>1\<forall>\<nu>\<^sub>2 (\<phi>{\<nu>\<^sub>1, \<nu>\<^sub>2} \<equiv> \<psi>{\<nu>\<^sub>1, \<nu>\<^sub>2})) \<rightarrow>
   [\<lambda>\<nu>\<^sub>1\<nu>\<^sub>2 \<psi>{\<nu>\<^sub>1,\<nu>\<^sub>2}]\<down>\<close>
  using "safe-ext"[where \<phi>="\<lambda>(x,y). \<phi> x y"]
  by (simp add: AOT_model_axiom_def AOT_sem_denotes AOT_model_denotes_prod_def
                AOT_sem_forall AOT_sem_imp AOT_sem_conj AOT_sem_equiv AOT_sem_box)
AOT_axiom "safe-ext[3]":
  \<open>([\<lambda>\<nu>\<^sub>1\<nu>\<^sub>2\<nu>\<^sub>3 \<phi>{\<nu>\<^sub>1,\<nu>\<^sub>2,\<nu>\<^sub>3}]\<down> & \<box>\<forall>\<nu>\<^sub>1\<forall>\<nu>\<^sub>2\<forall>\<nu>\<^sub>3 (\<phi>{\<nu>\<^sub>1, \<nu>\<^sub>2, \<nu>\<^sub>3} \<equiv> \<psi>{\<nu>\<^sub>1, \<nu>\<^sub>2, \<nu>\<^sub>3})) \<rightarrow>
   [\<lambda>\<nu>\<^sub>1\<nu>\<^sub>2\<nu>\<^sub>3 \<psi>{\<nu>\<^sub>1,\<nu>\<^sub>2,\<nu>\<^sub>3}]\<down>\<close>
  using "safe-ext"[where \<phi>="\<lambda>(x,y,z). \<phi> x y z"]
  by (simp add: AOT_model_axiom_def AOT_model_denotes_prod_def AOT_sem_forall
                AOT_sem_denotes AOT_sem_imp AOT_sem_conj AOT_sem_equiv AOT_sem_box)
AOT_axiom "safe-ext[4]":
  \<open>([\<lambda>\<nu>\<^sub>1\<nu>\<^sub>2\<nu>\<^sub>3\<nu>\<^sub>4 \<phi>{\<nu>\<^sub>1,\<nu>\<^sub>2,\<nu>\<^sub>3,\<nu>\<^sub>4}]\<down> &
    \<box>\<forall>\<nu>\<^sub>1\<forall>\<nu>\<^sub>2\<forall>\<nu>\<^sub>3\<forall>\<nu>\<^sub>4 (\<phi>{\<nu>\<^sub>1, \<nu>\<^sub>2, \<nu>\<^sub>3, \<nu>\<^sub>4} \<equiv> \<psi>{\<nu>\<^sub>1, \<nu>\<^sub>2, \<nu>\<^sub>3, \<nu>\<^sub>4})) \<rightarrow>
   [\<lambda>\<nu>\<^sub>1\<nu>\<^sub>2\<nu>\<^sub>3\<nu>\<^sub>4 \<psi>{\<nu>\<^sub>1,\<nu>\<^sub>2,\<nu>\<^sub>3,\<nu>\<^sub>4}]\<down>\<close>
  using "safe-ext"[where \<phi>="\<lambda>(x,y,z,w). \<phi> x y z w"]
  by (simp add: AOT_model_axiom_def AOT_model_denotes_prod_def AOT_sem_forall
                AOT_sem_denotes AOT_sem_imp AOT_sem_conj AOT_sem_equiv AOT_sem_box)

AOT_axiom "nary-encoding[2]":
  \<open>x\<^sub>1x\<^sub>2[F] \<equiv> x\<^sub>1[\<lambda>y [F]yx\<^sub>2] & x\<^sub>2[\<lambda>y [F]x\<^sub>1y]\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_conj AOT_sem_equiv AOT_enc_prod_def AOT_proj_enc_prod_def
                AOT_sem_unary_proj_enc AOT_sem_vars_denote)
AOT_axiom "nary-encoding[3]":
  \<open>x\<^sub>1x\<^sub>2x\<^sub>3[F] \<equiv> x\<^sub>1[\<lambda>y [F]yx\<^sub>2x\<^sub>3] & x\<^sub>2[\<lambda>y [F]x\<^sub>1yx\<^sub>3] & x\<^sub>3[\<lambda>y [F]x\<^sub>1x\<^sub>2y]\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_conj AOT_sem_equiv AOT_enc_prod_def AOT_proj_enc_prod_def
                AOT_sem_unary_proj_enc AOT_sem_vars_denote)
AOT_axiom "nary-encoding[4]":
  \<open>x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4[F] \<equiv> x\<^sub>1[\<lambda>y [F]yx\<^sub>2x\<^sub>3x\<^sub>4] &
                 x\<^sub>2[\<lambda>y [F]x\<^sub>1yx\<^sub>3x\<^sub>4] &
                 x\<^sub>3[\<lambda>y [F]x\<^sub>1x\<^sub>2yx\<^sub>4] &
                 x\<^sub>4[\<lambda>y [F]x\<^sub>1x\<^sub>2x\<^sub>3y]\<close>
  by (rule AOT_model_axiomI)
     (simp add: AOT_sem_conj AOT_sem_equiv AOT_enc_prod_def AOT_proj_enc_prod_def
                AOT_sem_unary_proj_enc AOT_sem_vars_denote)

AOT_axiom encoding: \<open>x[F] \<rightarrow> \<box>x[F]\<close>
  using AOT_sem_enc_nec 
  by (auto intro!: AOT_model_axiomI simp: AOT_sem_imp AOT_sem_box)

AOT_axiom nocoder: \<open>O!x \<rightarrow> \<not>\<exists>F x[F]\<close>
  by (auto intro!: AOT_model_axiomI
           simp: AOT_sem_imp AOT_sem_not AOT_sem_exists AOT_sem_ordinary
                 AOT_sem_dia
                AOT_sem_lambda_beta[OF AOT_sem_ordinary_def_denotes,
                                    OF AOT_sem_vars_denote])
     (metis AOT_sem_nocoder)

AOT_axiom "A-objects": \<open>\<exists>x (A!x & \<forall>F(x[F] \<equiv> \<phi>{F}))\<close>
proof(rule AOT_model_axiomI)
  AOT_modally_strict {
    AOT_obtain \<kappa> where \<open>\<kappa>\<down> & \<box>\<not>E!\<kappa> & \<forall>F (\<kappa>[F] \<equiv> \<phi>{F})\<close>
      using AOT_sem_A_objects[of _ \<phi>]
      by (auto simp: AOT_sem_imp AOT_sem_box AOT_sem_forall AOT_sem_exists
                     AOT_sem_conj AOT_sem_not AOT_sem_dia AOT_sem_denotes
                     AOT_sem_equiv) blast
    AOT_thus \<open>\<exists>x (A!x & \<forall>F(x[F] \<equiv> \<phi>{F}))\<close>
      unfolding AOT_sem_exists
      by (auto intro!: exI[where x=\<kappa>]
               simp: AOT_sem_lambda_beta[OF AOT_sem_abstract_def_denotes]
                     AOT_sem_box AOT_sem_dia AOT_sem_not AOT_sem_denotes
                     AOT_var_of_term_inverse AOT_sem_conj
                     AOT_sem_equiv AOT_sem_forall AOT_sem_abstract)
  }
qed

AOT_theorem universal_closure:
  assumes \<open>for arbitrary \<alpha>: \<phi>{\<alpha>} \<in> \<Lambda>\<^sub>\<box>\<close>
  shows \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<in> \<Lambda>\<^sub>\<box>\<close>
  using assms
  by (metis AOT_term_of_var_cases AOT_model_axiom_def AOT_sem_denotes AOT_sem_forall)

AOT_theorem act_closure:
  assumes \<open>\<phi> \<in> \<Lambda>\<^sub>\<box>\<close>
  shows \<open>\<^bold>\<A>\<phi> \<in> \<Lambda>\<^sub>\<box>\<close>
  using assms by (simp add: AOT_model_axiom_def AOT_sem_act)

AOT_theorem nec_closure:
  assumes \<open>\<phi> \<in> \<Lambda>\<^sub>\<box>\<close>
  shows \<open>\<box>\<phi> \<in> \<Lambda>\<^sub>\<box>\<close>
  using assms by (simp add: AOT_model_axiom_def AOT_sem_box)

AOT_theorem universal_closure_act:
  assumes \<open>for arbitrary \<alpha>: \<phi>{\<alpha>} \<in> \<Lambda>\<close>
  shows \<open>\<forall>\<alpha> \<phi>{\<alpha>} \<in> \<Lambda>\<close>
  using assms
  by (metis AOT_term_of_var_cases AOT_model_act_axiom_def AOT_sem_denotes
            AOT_sem_forall)

AOT_theorem act_closure_act:
  assumes \<open>\<phi> \<in> \<Lambda>\<close>
  shows \<open>\<^bold>\<A>\<phi> \<in> \<Lambda>\<close>
  using assms by (simp add: AOT_model_act_axiom_def AOT_sem_act)

text\<open>The following are not part of PLM and only hold in the extended models.
     They are a generalization of the predecessor axiom.\<close>

locale AOT_ExtendedModel =
  assumes AOT_ExtendedModel: \<open>AOT_ExtendedModel\<close>
begin

AOT_axiom indistinguishable_ord_enc_all:
  \<open>\<Pi>\<down> & A!x & A!y & \<forall>F \<box>([F]x \<equiv> [F]y) \<rightarrow>
  ((\<forall>G(\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) \<rightarrow> x[G])) \<equiv>
    \<forall>G(\<forall>z(O!z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) \<rightarrow> y[G]))\<close>
proof (rule AOT_model_axiomI)
  AOT_modally_strict {
    {
      AOT_assume \<Pi>_den: \<open>[\<Pi>]\<down>\<close>
      AOT_assume \<open>A!x\<close>
      AOT_hence 0: \<open>[\<lambda>x \<not>\<diamond>[E!]x]x\<close>
        by (simp add: AOT_sem_abstract)
      AOT_assume \<open>A!y\<close>
      AOT_hence 1: \<open>[\<lambda>x \<not>\<diamond>[E!]x]y\<close>
        by (simp add: AOT_sem_abstract)
      AOT_assume 2: \<open>\<forall>F \<box>([F]x \<equiv> [F]y)\<close>
      {
        AOT_assume \<open>\<forall>G(\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) \<rightarrow> x[G])\<close>
        AOT_hence 3: \<open>\<forall>G(\<forall>z([\<lambda>x \<diamond>[E!]x]z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) \<rightarrow> x[G])\<close>
          by (simp add: AOT_sem_ordinary)
        {
          fix \<Pi>' :: \<open><\<kappa>>\<close>
          AOT_assume 1: \<open>\<Pi>'\<down>\<close>
          AOT_assume 2: \<open>[\<lambda>x \<diamond>[E!]x]z \<rightarrow> \<box>([\<Pi>']z \<equiv> [\<Pi>]z)\<close> for z
          AOT_have \<open>x[\<Pi>']\<close>
            using 3
            by (auto simp: AOT_sem_forall AOT_sem_imp AOT_sem_box AOT_sem_denotes)
               (metis (no_types, lifting) 1 2 AOT_term_of_var_cases AOT_sem_box
                                          AOT_sem_denotes AOT_sem_imp)
        } note 3 = this
        fix \<Pi>' :: \<open><\<kappa>>\<close>
        AOT_assume \<Pi>_den: \<open>\<Pi>'\<down>\<close>
        AOT_assume 4: \<open>\<forall>z (O!z \<rightarrow> \<box>([\<Pi>']z \<equiv> [\<Pi>]z))\<close>
        {
          fix \<kappa>\<^sub>0
          AOT_assume \<open>[\<lambda>x \<diamond>[E!]x]\<kappa>\<^sub>0\<close>
          AOT_hence \<open>O!\<kappa>\<^sub>0\<close>
            using AOT_sem_ordinary by metis
          moreover AOT_have \<open>\<kappa>\<^sub>0\<down>\<close>
            using calculation by (simp add: AOT_sem_exe)
          ultimately AOT_have \<open>\<box>([\<Pi>']\<kappa>\<^sub>0 \<equiv> [\<Pi>]\<kappa>\<^sub>0)\<close>
            using 4 by (auto simp: AOT_sem_forall AOT_sem_imp)
        } note 4 = this
        AOT_have \<open>y[\<Pi>']\<close>
          apply (rule AOT_sem_enc_indistinguishable_all[OF AOT_ExtendedModel])
          apply (fact 0)
               apply (auto simp: 0 1 \<Pi>_den 2[simplified AOT_sem_forall
                                 AOT_sem_box AOT_sem_equiv])
          apply (rule 3)
           apply auto[1]
          using 4
          by (auto simp: AOT_sem_imp AOT_sem_equiv AOT_sem_box)
      }
      AOT_hence \<open>\<forall>G (\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) \<rightarrow> y[G])\<close>
        if \<open>\<forall>G (\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) \<rightarrow> x[G])\<close>
        using that
        by (auto simp: AOT_sem_forall AOT_sem_imp)
      moreover {
      {
        AOT_assume \<open>\<forall>G(\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) \<rightarrow> y[G])\<close>
        AOT_hence 3: \<open>\<forall>G(\<forall>z ([\<lambda>x \<diamond>[E!]x]z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) \<rightarrow> y[G])\<close>
          by (simp add: AOT_sem_ordinary)
        {
          fix \<Pi>' :: \<open><\<kappa>>\<close>
          AOT_assume 1: \<open>\<Pi>'\<down>\<close>
          AOT_assume 2: \<open>[\<lambda>x \<diamond>[E!]x]z \<rightarrow> \<box>([\<Pi>']z \<equiv> [\<Pi>]z)\<close> for z
          AOT_have \<open>y[\<Pi>']\<close>
            using 3
            apply (auto simp: AOT_sem_forall AOT_sem_imp AOT_sem_box AOT_sem_denotes)
            by (metis (no_types, lifting) 1 2 AOT_model.AOT_term_of_var_cases
                                          AOT_sem_box AOT_sem_denotes AOT_sem_imp)
        } note 3 = this
        fix \<Pi>' :: \<open><\<kappa>>\<close>
        AOT_assume \<Pi>_den: \<open>\<Pi>'\<down>\<close>
        AOT_assume 4: \<open>\<forall>z (O!z \<rightarrow> \<box>([\<Pi>']z \<equiv> [\<Pi>]z))\<close>
        {
          fix \<kappa>\<^sub>0
          AOT_assume \<open>[\<lambda>x \<diamond>[E!]x]\<kappa>\<^sub>0\<close>
          AOT_hence \<open>O!\<kappa>\<^sub>0\<close>
            using AOT_sem_ordinary by metis
          moreover AOT_hence \<open>\<kappa>\<^sub>0\<down>\<close>
            by (simp add: AOT_sem_exe)
          ultimately AOT_have \<open>\<box>([\<Pi>']\<kappa>\<^sub>0 \<equiv> [\<Pi>]\<kappa>\<^sub>0)\<close>
            using 4 by (auto simp: AOT_sem_forall AOT_sem_imp)
        } note 4 = this
        AOT_have \<open>x[\<Pi>']\<close>
          apply (rule AOT_sem_enc_indistinguishable_all[OF AOT_ExtendedModel])
                apply (fact 1)
               apply (auto simp: 0 1 \<Pi>_den 2[simplified AOT_sem_forall
                                 AOT_sem_box AOT_sem_equiv])
          apply (rule 3)
           apply auto[1]
          using 4
          by (auto simp: AOT_sem_imp AOT_sem_equiv AOT_sem_box)
      }

      AOT_hence \<open>\<forall>G (\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) \<rightarrow> x[G])\<close>
        if \<open>\<forall>G (\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) \<rightarrow> y[G])\<close>
        using that
        by (auto simp: AOT_sem_forall AOT_sem_imp)
      }
      ultimately AOT_have \<open>\<forall>G (\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) \<rightarrow> x[G]) \<equiv>
                           \<forall>G (\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) \<rightarrow> y[G])\<close>
        by (auto simp: AOT_sem_equiv)
    }
    AOT_thus \<open>\<Pi>\<down> & A!x & A!y & \<forall>F \<box>([F]x \<equiv> [F]y) \<rightarrow>
       (\<forall>G (\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) \<rightarrow> x[G]) \<equiv>
        \<forall>G (\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) \<rightarrow> y[G]))\<close>
      by (auto simp: AOT_sem_imp AOT_sem_conj)
  }
qed

AOT_axiom indistinguishable_ord_enc_ex:
  \<open>\<Pi>\<down> & A!x & A!y & \<forall>F \<box>([F]x \<equiv> [F]y) \<rightarrow>
  ((\<exists>G(\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) & x[G])) \<equiv>
    \<exists>G(\<forall>z(O!z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) & y[G]))\<close>
proof (rule AOT_model_axiomI)
  have Aux: \<open>[v \<Turnstile> [\<lambda>x \<diamond>[E!]x]\<kappa>] = ([v \<Turnstile> [\<lambda>x \<diamond>[E!]x]\<kappa>] \<and> [v \<Turnstile> \<kappa>\<down>])\<close> for v \<kappa>
    using AOT_sem_exe by blast
  AOT_modally_strict {
    fix x y
    AOT_assume \<Pi>_den: \<open>[\<Pi>]\<down>\<close>
    AOT_assume 2: \<open>\<forall>F \<box>([F]x \<equiv> [F]y)\<close>
    AOT_assume \<open>A!x\<close>
    AOT_hence 0: \<open>[\<lambda>x \<not>\<diamond>[E!]x]x\<close>
      by (simp add: AOT_sem_abstract)
    AOT_assume \<open>A!y\<close>
    AOT_hence 1: \<open>[\<lambda>x \<not>\<diamond>[E!]x]y\<close>
      by (simp add: AOT_sem_abstract)
    {
      AOT_assume \<open>\<exists>G(\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) & x[G])\<close>
      then AOT_obtain \<Pi>'
        where \<Pi>'_den: \<open>\<Pi>'\<down>\<close>
          and \<Pi>'_indist: \<open>\<forall>z (O!z \<rightarrow> \<box>([\<Pi>']z \<equiv> [\<Pi>]z))\<close>
          and x_enc_\<Pi>': \<open>x[\<Pi>']\<close>
        by (meson AOT_sem_conj AOT_sem_exists)
      {
        fix \<kappa>\<^sub>0
        AOT_assume \<open>[\<lambda>x \<diamond>[E!]x]\<kappa>\<^sub>0\<close>
        AOT_hence \<open>\<box>([\<Pi>']\<kappa>\<^sub>0 \<equiv> [\<Pi>]\<kappa>\<^sub>0)\<close>
          using \<Pi>'_indist
          by (auto simp: AOT_sem_exe AOT_sem_imp AOT_sem_exists AOT_sem_conj
                         AOT_sem_ordinary AOT_sem_forall)
      } note 3 = this
      AOT_have \<open>\<forall>z ([\<lambda>x \<diamond>[E!]x]z \<rightarrow> \<box>([\<Pi>']z \<equiv> [\<Pi>]z))\<close>
        using \<Pi>'_indist by (simp add: AOT_sem_ordinary)
      AOT_obtain \<Pi>'' where
          \<Pi>''_den: \<open>\<Pi>''\<down>\<close> and
          \<Pi>''_indist: \<open>[\<lambda>x \<diamond>[E!]x]\<kappa>\<^sub>0 \<rightarrow> \<box>([\<Pi>'']\<kappa>\<^sub>0 \<equiv> [\<Pi>]\<kappa>\<^sub>0)\<close> and
          y_enc_\<Pi>'': \<open>y[\<Pi>'']\<close> for \<kappa>\<^sub>0
        using AOT_sem_enc_indistinguishable_ex[OF AOT_ExtendedModel,
                OF 0, OF 1, rotated, OF \<Pi>_den,
                OF exI[where x=\<Pi>'], OF conjI, OF \<Pi>'_den, OF conjI,
                OF x_enc_\<Pi>', OF allI, OF impI,
                OF 3[simplified AOT_sem_box AOT_sem_equiv], simplified, OF
                2[simplified AOT_sem_forall AOT_sem_equiv AOT_sem_box,
                  THEN spec, THEN mp, THEN spec], simplified]
        unfolding AOT_sem_imp AOT_sem_box AOT_sem_equiv by blast
      {
        AOT_have \<open>\<Pi>''\<down>\<close>
            and \<open>\<forall>x ([\<lambda>x \<diamond>[E!]x]x \<rightarrow> \<box>([\<Pi>'']x \<equiv> [\<Pi>]x))\<close>
            and \<open>y[\<Pi>'']\<close>
          apply (simp add: \<Pi>''_den)
          apply (simp add: AOT_sem_forall \<Pi>''_indist)
          by (simp add: y_enc_\<Pi>'')
      } note 2 = this
      AOT_have \<open>\<exists>G(\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) & y[G])\<close>
        apply (auto simp: AOT_sem_exists AOT_sem_ordinary
            AOT_sem_imp AOT_sem_box AOT_sem_forall AOT_sem_equiv AOT_sem_conj)
        using 2[simplified AOT_sem_box AOT_sem_equiv AOT_sem_imp AOT_sem_forall]
        by blast
    }
  } note 0 = this
  AOT_modally_strict {
    {
      fix x y
      AOT_assume \<Pi>_den: \<open>[\<Pi>]\<down>\<close>
      moreover AOT_assume \<open>\<forall>F \<box>([F]x \<equiv> [F]y)\<close>
      moreover AOT_have \<open>\<forall>F \<box>([F]y \<equiv> [F]x)\<close>
        using calculation(2)
        by (auto simp: AOT_sem_forall AOT_sem_box AOT_sem_equiv)
      moreover AOT_assume \<open>A!x\<close>
      moreover AOT_assume \<open>A!y\<close>
      ultimately AOT_have \<open>\<exists>G (\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) & x[G]) \<equiv>
                           \<exists>G (\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) & y[G])\<close>
        using 0 by (auto simp: AOT_sem_equiv)
    }
    AOT_thus \<open>\<Pi>\<down> & A!x & A!y & \<forall>F \<box>([F]x \<equiv> [F]y) \<rightarrow>
       (\<exists>G (\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) & x[G]) \<equiv>
        \<exists>G (\<forall>z (O!z \<rightarrow> \<box>([G]z \<equiv> [\<Pi>]z)) & y[G]))\<close>
      by (auto simp: AOT_sem_imp AOT_sem_conj)
  }
qed
end

(*<*)
end
(*>*)