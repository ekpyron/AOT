(*<*)
theory AOT_semantics
  imports AOT_syntax
begin
(*>*)

section\<open>Abstract Semantics for AOT\<close>

(* To enable meta syntax: *)
(* interpretation AOT_meta_syntax. *)
(* To disable meta syntax: *)
interpretation AOT_no_meta_syntax.

(* To enable AOT syntax (takes precedence over meta syntax;
                         can be done locally using "including" or "include"): *)
unbundle AOT_syntax
(* To disable AOT syntax (restoring meta syntax or no syntax;
                          can be done locally using "including" or "include"): *)
(* unbundle AOT_no_syntax *)

specification(AOT_denotes)
  AOT_sem_denotes: \<open>[w \<Turnstile> \<tau>\<down>] = AOT_model_denotes \<tau>\<close>
  by (rule exI[where x=\<open>\<lambda> \<tau> . \<epsilon>\<^sub>\<o> w . AOT_model_denotes \<tau>\<close>])
     (simp add: AOT_model_proposition_choice_simp)

lemma AOT_sem_var_induct[induct type: AOT_var]:
  assumes AOT_denoting_term_case: \<open>\<And> \<tau> . [v \<Turnstile> \<tau>\<down>] \<Longrightarrow> [v \<Turnstile> \<phi>{\<tau>}]\<close>
  shows \<open>[v \<Turnstile> \<phi>{\<alpha>}]\<close>
  by (simp add: AOT_denoting_term_case AOT_sem_denotes AOT_term_of_var)

specification(AOT_imp)
  AOT_sem_imp: \<open>[w \<Turnstile> \<phi> \<rightarrow> \<psi>] = ([w \<Turnstile> \<phi>] \<longrightarrow> [w \<Turnstile> \<psi>])\<close>
  by (rule exI[where x=\<open>\<lambda> \<phi> \<psi> . \<epsilon>\<^sub>\<o> w . ([w \<Turnstile> \<phi>] \<longrightarrow> [w \<Turnstile> \<psi>])\<close>])
    (simp add: AOT_model_proposition_choice_simp)

specification(AOT_not)
  AOT_sem_not: \<open>[w \<Turnstile> \<not>\<phi>] = (\<not>[w \<Turnstile> \<phi>])\<close>
  by (rule exI[where x=\<open>\<lambda> \<phi> . \<epsilon>\<^sub>\<o> w . \<not>[w \<Turnstile> \<phi>]\<close>])
     (simp add: AOT_model_proposition_choice_simp)

specification(AOT_box)
  AOT_sem_box: \<open>[w \<Turnstile> \<box>\<phi>] = (\<forall> w . [w \<Turnstile> \<phi>])\<close>
  by (rule exI[where x=\<open>\<lambda> \<phi> . \<epsilon>\<^sub>\<o> w . \<forall> w . [w \<Turnstile> \<phi>]\<close>])
     (simp add: AOT_model_proposition_choice_simp)

specification(AOT_act)
  AOT_sem_act: \<open>[w \<Turnstile> \<^bold>\<A>\<phi>] = [w\<^sub>0 \<Turnstile> \<phi>]\<close>
  by (rule exI[where x=\<open>\<lambda> \<phi> . \<epsilon>\<^sub>\<o> w . [w\<^sub>0 \<Turnstile> \<phi>]\<close>])
     (simp add: AOT_model_proposition_choice_simp)

lemma AOT_sem_conj: \<open>[w \<Turnstile> \<phi> & \<psi>] = ([w \<Turnstile> \<phi>] \<and> [w \<Turnstile> \<psi>])\<close>
  using AOT_conj AOT_model_equiv_def AOT_sem_imp AOT_sem_not by auto

lemma AOT_sem_equiv: \<open>[w \<Turnstile> \<phi> \<equiv> \<psi>] = ([w \<Turnstile> \<phi>] = [w \<Turnstile> \<psi>])\<close>
  using AOT_equiv AOT_sem_conj AOT_model_equiv_def AOT_sem_imp by auto

lemma AOT_sem_disj: \<open>[w \<Turnstile> \<phi> \<or> \<psi>] = ([w \<Turnstile> \<phi>] \<or> [w \<Turnstile> \<psi>])\<close>
  using AOT_disj AOT_model_equiv_def AOT_sem_imp AOT_sem_not by auto

lemma AOT_sem_dia: \<open>[w \<Turnstile> \<diamond>\<phi>] = (\<exists> w . [w \<Turnstile> \<phi>])\<close>
  using AOT_dia AOT_sem_box AOT_model_equiv_def AOT_sem_not by auto

specification(AOT_forall)
  AOT_sem_forall: \<open>[w \<Turnstile> \<forall>\<alpha> \<phi>{\<alpha>}] = (\<forall> \<tau> . [w \<Turnstile> \<tau>\<down>] \<longrightarrow> [w \<Turnstile> \<phi>{\<tau>}])\<close>
  by (rule exI[where x=\<open>\<lambda> op . \<epsilon>\<^sub>\<o> w . \<forall> \<tau> . [w \<Turnstile> \<tau>\<down>] \<longrightarrow> [w \<Turnstile> \<guillemotleft>op \<tau>\<guillemotright>]\<close>])
     (simp add: AOT_model_proposition_choice_simp)

lemma AOT_sem_exists: \<open>[w \<Turnstile> \<exists>\<alpha> \<phi>{\<alpha>}] = (\<exists> \<tau> . [w \<Turnstile> \<tau>\<down>] \<and> [w \<Turnstile> \<phi>{\<tau>}])\<close>
  unfolding AOT_exists[unfolded AOT_model_equiv_def, THEN spec]
  by (simp add: AOT_sem_forall AOT_sem_not)

specification(AOT_eq)
  AOT_sem_eq: \<open>[w \<Turnstile> \<tau> = \<tau>'] = ([w \<Turnstile> \<tau>\<down>] \<and> [w \<Turnstile> \<tau>'\<down>] \<and> \<tau> = \<tau>')\<close>
  by (rule exI[where x=\<open>\<lambda> \<tau> \<tau>' . \<epsilon>\<^sub>\<o> w . [w \<Turnstile> \<tau>\<down>] \<and> [w \<Turnstile> \<tau>'\<down>] \<and> \<tau> = \<tau>'\<close>])
     (simp add: AOT_model_proposition_choice_simp)

specification(AOT_desc)
  AOT_sem_desc_denotes: \<open>[w \<Turnstile> \<^bold>\<iota>x(\<phi>{x})\<down>] = (\<exists>! \<kappa> . [w\<^sub>0 \<Turnstile> \<kappa>\<down>] \<and> [w\<^sub>0 \<Turnstile> \<phi>{\<kappa>}])\<close>
  AOT_sem_desc_prop: \<open>[w \<Turnstile> \<^bold>\<iota>x(\<phi>{x})\<down>] \<Longrightarrow> [w\<^sub>0 \<Turnstile> \<phi>{\<^bold>\<iota>x(\<phi>{x})}]\<close>
  AOT_sem_desc_unique: \<open>[w \<Turnstile> \<^bold>\<iota>x(\<phi>{x})\<down>] \<Longrightarrow> [w \<Turnstile> \<kappa>\<down>] \<Longrightarrow> [w\<^sub>0 \<Turnstile> \<phi>{\<kappa>}] \<Longrightarrow>
                        [w \<Turnstile> \<^bold>\<iota>x(\<phi>{x}) = \<kappa>]\<close>
proof -
  have \<open>\<exists>x::'a . \<not>AOT_model_denotes x\<close>
    using AOT_model_nondenoting_ex
    by blast
  text\<open>Note that we may choose a distinct non-denoting object for each matrix.\<close>
  then obtain nondenoting :: \<open>('a \<Rightarrow> \<o>) \<Rightarrow> 'a\<close> where
    nondenoting: \<open>\<forall> \<phi> . \<not>AOT_model_denotes (nondenoting \<phi>)\<close>
    by fast
  obtain desc where desc_def:
    \<open>desc = (\<lambda> \<phi> . if (\<exists>! \<kappa> . [w\<^sub>0 \<Turnstile> \<kappa>\<down>] \<and> [w\<^sub>0 \<Turnstile> \<phi>{\<kappa>}])
                   then (THE \<kappa> . [w\<^sub>0 \<Turnstile> \<kappa>\<down>] \<and> [w\<^sub>0 \<Turnstile> \<phi>{\<kappa>}])
                   else nondenoting \<phi>)\<close> by blast
  {
    fix \<phi> :: \<open>'a \<Rightarrow> \<o>\<close>
    assume ex1: \<open>\<exists>! \<kappa> . [w\<^sub>0 \<Turnstile> \<kappa>\<down>] \<and> [w\<^sub>0 \<Turnstile> \<phi>{\<kappa>}]\<close>
    then obtain \<kappa> where x_prop: "[w\<^sub>0 \<Turnstile> \<kappa>\<down>] \<and> [w\<^sub>0 \<Turnstile> \<phi>{\<kappa>}]"
      unfolding AOT_sem_denotes by blast
    moreover have "(desc \<phi>) = \<kappa>"
      unfolding desc_def using x_prop ex1 by fastforce
    ultimately have "[w\<^sub>0 \<Turnstile> \<guillemotleft>desc \<phi>\<guillemotright>\<down>] \<and> [w\<^sub>0 \<Turnstile> \<guillemotleft>\<phi> (desc \<phi>)\<guillemotright>]"
      by blast
  } note 1 = this
  moreover {
    fix \<phi> :: \<open>'a \<Rightarrow> \<o>\<close>
    assume nex1: \<open>\<nexists>! \<kappa> . [w\<^sub>0 \<Turnstile> \<kappa>\<down>] \<and> [w\<^sub>0 \<Turnstile> \<phi>{\<kappa>}]\<close>
    hence "(desc \<phi>) = nondenoting \<phi>" by (simp add: desc_def AOT_sem_denotes)
    hence "[w \<Turnstile> \<not>\<guillemotleft>desc \<phi>\<guillemotright>\<down>]" for w
      by (simp add: AOT_sem_denotes nondenoting AOT_sem_not)
  }
  ultimately have desc_denotes_simp:
    \<open>[w \<Turnstile> \<guillemotleft>desc \<phi>\<guillemotright>\<down>] = (\<exists>! \<kappa> . [w\<^sub>0 \<Turnstile> \<kappa>\<down>] \<and> [w\<^sub>0 \<Turnstile> \<phi>{\<kappa>}])\<close> for \<phi> w
    by (simp add: AOT_sem_denotes desc_def nondenoting)
  have \<open>(\<forall>\<phi> w. [w \<Turnstile> \<guillemotleft>desc \<phi>\<guillemotright>\<down>] = (\<exists>!\<kappa>. [w\<^sub>0 \<Turnstile> \<kappa>\<down>] \<and> [w\<^sub>0 \<Turnstile> \<phi>{\<kappa>}])) \<and>
    (\<forall>\<phi> w. [w \<Turnstile> \<guillemotleft>desc \<phi>\<guillemotright>\<down>] \<longrightarrow> [w\<^sub>0 \<Turnstile> \<guillemotleft>\<phi> (desc \<phi>)\<guillemotright>]) \<and>
    (\<forall>\<phi> w \<kappa>. [w \<Turnstile> \<guillemotleft>desc \<phi>\<guillemotright>\<down>] \<longrightarrow> [w \<Turnstile> \<kappa>\<down>] \<longrightarrow> [w\<^sub>0 \<Turnstile> \<phi>{\<kappa>}] \<longrightarrow>
             [w \<Turnstile> \<guillemotleft>desc \<phi>\<guillemotright> = \<kappa>])\<close>
    by (insert 1; auto simp: desc_denotes_simp AOT_sem_eq AOT_sem_denotes
                             desc_def nondenoting)
  thus ?thesis
    by (safe intro!: exI[where x=desc]; presburger)
qed

specification(AOT_exe AOT_lambda)
  AOT_sem_exe: \<open>[w \<Turnstile> [\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n] = ([w \<Turnstile> \<Pi>\<down>] \<and> [w \<Turnstile> \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>] \<and>
                                     [w \<Turnstile> \<guillemotleft>Rep_rel \<Pi> \<kappa>\<^sub>1\<kappa>\<^sub>n\<guillemotright>])\<close>
  AOT_sem_lambda_eta: \<open>[w \<Turnstile> \<Pi>\<down>] \<Longrightarrow> [w \<Turnstile> [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n [\<Pi>]\<nu>\<^sub>1...\<nu>\<^sub>n] = \<Pi>]\<close>
  AOT_sem_lambda_beta: \<open>[w \<Turnstile> [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down>] \<Longrightarrow> [w \<Turnstile> \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>] \<Longrightarrow>
                        [w \<Turnstile> [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<kappa>\<^sub>1...\<kappa>\<^sub>n] = [w \<Turnstile> \<phi>{\<kappa>\<^sub>1...\<kappa>\<^sub>n}]\<close>
  AOT_sem_lambda_denotes: \<open>[w \<Turnstile> [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down>] =
    (\<forall> v \<kappa>\<^sub>1\<kappa>\<^sub>n \<kappa>\<^sub>1'\<kappa>\<^sub>n' . [v \<Turnstile> \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>] \<and> [v \<Turnstile> \<kappa>\<^sub>1'...\<kappa>\<^sub>n'\<down>] \<and>
        (\<forall> \<Pi> v . [v \<Turnstile> \<Pi>\<down>] \<longrightarrow> [v \<Turnstile> [\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n] = [v \<Turnstile> [\<Pi>]\<kappa>\<^sub>1'...\<kappa>\<^sub>n']) \<longrightarrow>
                 [v \<Turnstile> \<phi>{\<kappa>\<^sub>1...\<kappa>\<^sub>n}] = [v \<Turnstile> \<phi>{\<kappa>\<^sub>1'...\<kappa>\<^sub>n'}])\<close>
  AOT_sem_lambda_coex: \<open>[w \<Turnstile> [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down>] \<Longrightarrow>
    (\<forall> w \<kappa>\<^sub>1\<kappa>\<^sub>n . [w \<Turnstile> \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>] \<longrightarrow> [w \<Turnstile> \<phi>{\<kappa>\<^sub>1...\<kappa>\<^sub>n}] = [w \<Turnstile> \<psi>{\<kappa>\<^sub>1...\<kappa>\<^sub>n}]) \<Longrightarrow>
    [w \<Turnstile> [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<psi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down>]\<close>
  AOT_sem_lambda_denoting:
    \<open>[w \<Turnstile> \<guillemotleft>Abs_rel \<phi>\<guillemotright>\<down>] \<Longrightarrow> \<guillemotleft>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<guillemotright> = Abs_rel \<phi>\<close>
  AOT_sem_exe_denoting: \<open>[w \<Turnstile> \<Pi>\<down>] \<Longrightarrow> AOT_exe \<Pi> \<kappa>s = Rep_rel \<Pi> \<kappa>s\<close>
  AOT_sem_lambda_eq_prop_eq: \<open>\<guillemotleft>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>]\<guillemotright> = \<guillemotleft>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<psi>]\<guillemotright> \<Longrightarrow> \<phi> = \<psi>\<close>
proof -
  have \<open>\<exists> x :: <'a> . \<not>AOT_model_denotes x\<close>
    by (rule exI[where x=\<open>Abs_rel (\<lambda> x . \<epsilon>\<^sub>\<o> w. True)\<close>])
       (meson AOT_model_denotes_rel.abs_eq AOT_model_nondenoting_ex
              AOT_model_proposition_choice_simp)
  then obtain nondenoting_rel :: \<open><'a>\<close> where
    nondenoting_rel: \<open>\<not>AOT_model_denotes nondenoting_rel\<close> by blast
  obtain exe :: \<open><'a> \<Rightarrow> 'a \<Rightarrow> \<o>\<close> where
    exe_def: \<open>exe \<equiv> \<lambda> \<Pi> \<kappa>s . if AOT_model_denotes \<Pi>
                              then Rep_rel \<Pi> \<kappa>s
                              else (\<epsilon>\<^sub>\<o> w . False)\<close> by blast
  obtain lambda :: \<open>('a\<Rightarrow>\<o>) \<Rightarrow> <'a>\<close> where
    lambda_def: \<open>lambda \<equiv> \<lambda> \<phi> . if AOT_model_denotes (Abs_rel \<phi>)
      then (Abs_rel \<phi>)
      else
        if (\<forall> \<kappa> \<kappa>' w . (AOT_model_denotes \<kappa> \<and> AOT_model_term_equiv \<kappa> \<kappa>') \<longrightarrow>
                       [w \<Turnstile> \<guillemotleft>\<phi> \<kappa>\<guillemotright>] = [w \<Turnstile> \<guillemotleft>\<phi> \<kappa>'\<guillemotright>])
        then
          Abs_rel (fix_special (\<lambda> x . if AOT_model_denotes x
                                      then \<phi> (SOME y . AOT_model_term_equiv x y)
                                      else  (\<epsilon>\<^sub>\<o> w . False)))
        else 
          nondenoting_rel\<close> by blast
  have fix_special_denoting_simp[simp]:
    \<open>fix_special (\<lambda>x. if AOT_model_denotes x then \<phi> x else \<psi> x) \<kappa> = \<phi> \<kappa>\<close>
    if \<open>AOT_model_denotes \<kappa>\<close>
    for \<kappa> :: 'a and \<phi> \<psi>
    by (simp add: that fix_special_denoting)
  have denoting_eps_cong[cong]:
    \<open>[w \<Turnstile> \<guillemotleft>\<phi> (Eps (AOT_model_term_equiv \<kappa>))\<guillemotright>] = [w \<Turnstile> \<guillemotleft>\<phi> \<kappa>\<guillemotright>]\<close>
    if \<open>AOT_model_denotes \<kappa>\<close>
    and \<open>\<forall> \<kappa> \<kappa>'. AOT_model_denotes \<kappa> \<and> AOT_model_term_equiv \<kappa> \<kappa>' \<longrightarrow>
                 (\<forall>w. [w \<Turnstile> \<guillemotleft>\<phi> \<kappa>\<guillemotright>] = [w \<Turnstile> \<guillemotleft>\<phi> \<kappa>'\<guillemotright>])\<close>
    for w :: w and \<kappa> :: 'a and \<phi> :: \<open>'a\<Rightarrow>\<o>\<close>
    using that AOT_model_term_equiv_eps(2) by blast
  have exe_rep_rel: \<open>[w \<Turnstile> \<guillemotleft>exe \<Pi> \<kappa>\<^sub>1\<kappa>\<^sub>n\<guillemotright>] = ([w \<Turnstile> \<Pi>\<down>] \<and> [w \<Turnstile> \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>] \<and>
                                            [w \<Turnstile> \<guillemotleft>Rep_rel \<Pi> \<kappa>\<^sub>1\<kappa>\<^sub>n\<guillemotright>])\<close> for w \<Pi> \<kappa>\<^sub>1\<kappa>\<^sub>n
    by (metis AOT_model_denotes_rel.rep_eq exe_def AOT_sem_denotes
              AOT_model_proposition_choice_simp)
  moreover have \<open>[w \<Turnstile> \<guillemotleft>\<Pi>\<guillemotright>\<down>] \<Longrightarrow> [w \<Turnstile> \<guillemotleft>lambda (exe \<Pi>)\<guillemotright> = \<guillemotleft>\<Pi>\<guillemotright>]\<close> for \<Pi> w
    by (auto simp: Rep_rel_inverse lambda_def AOT_sem_denotes AOT_sem_eq
                   AOT_model_denotes_rel_def Abs_rel_inverse exe_def)
  moreover have lambda_denotes_beta:
    \<open>[w \<Turnstile> \<guillemotleft>exe (lambda \<phi>) \<kappa> \<guillemotright>] = [w \<Turnstile> \<guillemotleft>\<phi> \<kappa>\<guillemotright>]\<close>
    if \<open>[w \<Turnstile> \<guillemotleft>lambda \<phi>\<guillemotright>\<down>]\<close> and \<open>[w \<Turnstile> \<guillemotleft>\<kappa>\<guillemotright>\<down>]\<close>
    for \<phi> \<kappa> w
    using that unfolding exe_def AOT_sem_denotes
    by (auto simp: lambda_def Abs_rel_inverse nondenoting_rel split: if_split_asm)
  moreover have lambda_denotes_simp:
    \<open>[w \<Turnstile> \<guillemotleft>lambda \<phi>\<guillemotright>\<down>] = (\<forall> v \<kappa>\<^sub>1\<kappa>\<^sub>n \<kappa>\<^sub>1'\<kappa>\<^sub>n' . [v \<Turnstile> \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>] \<and> [v \<Turnstile> \<kappa>\<^sub>1'...\<kappa>\<^sub>n'\<down>] \<and>
        (\<forall> \<Pi> v . [v \<Turnstile> \<Pi>\<down>] \<longrightarrow> [v \<Turnstile> \<guillemotleft>exe \<Pi> \<kappa>\<^sub>1\<kappa>\<^sub>n\<guillemotright>] = [v \<Turnstile> \<guillemotleft>exe \<Pi> \<kappa>\<^sub>1'\<kappa>\<^sub>n'\<guillemotright>]) \<longrightarrow>
        [v \<Turnstile> \<phi>{\<kappa>\<^sub>1...\<kappa>\<^sub>n}] = [v \<Turnstile> \<phi>{\<kappa>\<^sub>1'...\<kappa>\<^sub>n'}])\<close> for \<phi> w
  proof
    assume \<open>[w \<Turnstile> \<guillemotleft>lambda \<phi>\<guillemotright>\<down>]\<close>
    hence \<open>AOT_model_denotes (lambda \<phi>)\<close>
      unfolding AOT_sem_denotes by simp
    moreover have \<open>[w \<Turnstile> \<guillemotleft>\<phi> \<kappa>\<guillemotright>] \<Longrightarrow> [w \<Turnstile> \<guillemotleft>\<phi> \<kappa>'\<guillemotright>]\<close>
      and \<open>[w \<Turnstile> \<guillemotleft>\<phi> \<kappa>'\<guillemotright>] \<Longrightarrow> [w \<Turnstile> \<guillemotleft>\<phi> \<kappa>\<guillemotright>]\<close>
      if \<open>AOT_model_denotes \<kappa>\<close> and \<open>AOT_model_term_equiv \<kappa> \<kappa>'\<close>
      for w \<kappa> \<kappa>'
      by (metis (no_types, lifting) AOT_model_denotes_rel.abs_eq lambda_def
                                    that calculation nondenoting_rel)+
    ultimately show \<open>\<forall> v \<kappa>\<^sub>1\<kappa>\<^sub>n \<kappa>\<^sub>1'\<kappa>\<^sub>n' . [v \<Turnstile> \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>] \<and> [v \<Turnstile> \<kappa>\<^sub>1'...\<kappa>\<^sub>n'\<down>] \<and>
        (\<forall> \<Pi> v . [v \<Turnstile> \<Pi>\<down>] \<longrightarrow> [v \<Turnstile> \<guillemotleft>exe \<Pi> \<kappa>\<^sub>1\<kappa>\<^sub>n\<guillemotright>] = [v \<Turnstile> \<guillemotleft>exe \<Pi> \<kappa>\<^sub>1'\<kappa>\<^sub>n'\<guillemotright>]) \<longrightarrow>
        [v \<Turnstile> \<phi>{\<kappa>\<^sub>1...\<kappa>\<^sub>n}] = [v \<Turnstile> \<phi>{\<kappa>\<^sub>1'...\<kappa>\<^sub>n'}]\<close>
      unfolding AOT_sem_denotes
      by (metis (no_types) AOT_sem_denotes lambda_denotes_beta)
  next
    assume \<open>\<forall> v \<kappa>\<^sub>1\<kappa>\<^sub>n \<kappa>\<^sub>1'\<kappa>\<^sub>n' . [v \<Turnstile> \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>] \<and> [v \<Turnstile> \<kappa>\<^sub>1'...\<kappa>\<^sub>n'\<down>] \<and>
      (\<forall> \<Pi> v . [v \<Turnstile> \<Pi>\<down>] \<longrightarrow> [v \<Turnstile> \<guillemotleft>exe \<Pi> \<kappa>\<^sub>1\<kappa>\<^sub>n\<guillemotright>] = [v \<Turnstile> \<guillemotleft>exe \<Pi> \<kappa>\<^sub>1'\<kappa>\<^sub>n'\<guillemotright>]) \<longrightarrow>
      [v \<Turnstile> \<phi>{\<kappa>\<^sub>1...\<kappa>\<^sub>n}] = [v \<Turnstile> \<phi>{\<kappa>\<^sub>1'...\<kappa>\<^sub>n'}]\<close>
    hence \<open>[w \<Turnstile> \<guillemotleft>\<phi> \<kappa>\<guillemotright>] = [w \<Turnstile> \<guillemotleft>\<phi> \<kappa>'\<guillemotright>]\<close>
      if \<open>AOT_model_denotes \<kappa> \<and> AOT_model_denotes \<kappa>' \<and> AOT_model_term_equiv \<kappa> \<kappa>'\<close>
      for w \<kappa> \<kappa>'
      using that
      by (auto simp: AOT_sem_denotes)
         (meson AOT_model_term_equiv_rel_equiv AOT_sem_denotes exe_rep_rel)+
    hence \<open>[w \<Turnstile> \<guillemotleft>\<phi> \<kappa>\<guillemotright>] = [w \<Turnstile> \<guillemotleft>\<phi> \<kappa>'\<guillemotright>]\<close>
      if \<open>AOT_model_denotes \<kappa> \<and> AOT_model_term_equiv \<kappa> \<kappa>'\<close>
      for w \<kappa> \<kappa>'
      using that AOT_model_term_equiv_denotes by blast
    hence \<open>AOT_model_denotes (lambda \<phi>)\<close>
      by (auto simp: lambda_def Abs_rel_inverse AOT_model_denotes_rel.abs_eq
                     AOT_model_irregular_equiv AOT_model_term_equiv_eps(3)
                     AOT_model_term_equiv_regular fix_special_def AOT_sem_denotes
                     AOT_model_term_equiv_denotes AOT_model_proposition_choice_simp
                     AOT_model_irregular_false
               split: if_split_asm
               intro: AOT_model_irregular_eqI)
    thus \<open>[w \<Turnstile> \<guillemotleft>lambda \<phi>\<guillemotright>\<down>]\<close>
      by (simp add: AOT_sem_denotes)
  qed
  moreover have \<open>[w \<Turnstile> \<guillemotleft>lambda \<psi>\<guillemotright>\<down>]\<close>
    if \<open>[w \<Turnstile> \<guillemotleft>lambda \<phi>\<guillemotright>\<down>]\<close>
    and \<open>\<forall> w \<kappa>\<^sub>1\<kappa>\<^sub>n . [w \<Turnstile> \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>] \<longrightarrow> [w \<Turnstile> \<phi>{\<kappa>\<^sub>1...\<kappa>\<^sub>n}] = [w \<Turnstile> \<psi>{\<kappa>\<^sub>1...\<kappa>\<^sub>n}]\<close>
    for \<phi> \<psi> w using that unfolding lambda_denotes_simp by auto
  moreover have \<open>[w \<Turnstile> \<guillemotleft>Abs_rel \<phi>\<guillemotright>\<down>] \<Longrightarrow> lambda \<phi> = Abs_rel \<phi>\<close> for w \<phi>
    by (simp add: AOT_sem_denotes lambda_def)
  moreover have \<open>[w \<Turnstile> \<Pi>\<down>] \<Longrightarrow> exe \<Pi> \<kappa>s = Rep_rel \<Pi> \<kappa>s\<close> for \<Pi> \<kappa>s w
    by (simp add: exe_def AOT_sem_denotes)
  moreover have \<open>lambda (\<lambda>x. p) = lambda (\<lambda>x. q) \<Longrightarrow> p = q\<close> for p q
    unfolding lambda_def
    by (auto split: if_split_asm simp: Abs_rel_inject fix_special_def)
       (meson AOT_model_irregular_nondenoting AOT_model_denoting_ex)+
  note calculation = calculation this
  show ?thesis
    apply (safe intro!: exI[where x=exe] exI[where x=lambda])
    using calculation apply simp_all
    using lambda_denotes_simp by blast+
qed

lemma AOT_model_lambda_denotes:
  \<open>AOT_model_denotes (AOT_lambda \<phi>) = (\<forall> v \<kappa> \<kappa>' .
    AOT_model_denotes \<kappa> \<and> AOT_model_denotes \<kappa>' \<and> AOT_model_term_equiv \<kappa> \<kappa>' \<longrightarrow>
    [v \<Turnstile> \<guillemotleft>\<phi> \<kappa>\<guillemotright>] = [v \<Turnstile> \<guillemotleft>\<phi> \<kappa>'\<guillemotright>])\<close>
proof(safe)
  fix v and \<kappa> \<kappa>' :: 'a
  assume \<open>AOT_model_denotes (AOT_lambda \<phi>)\<close>
  hence 1: \<open>AOT_model_denotes \<kappa>\<^sub>1\<kappa>\<^sub>n \<and>
        AOT_model_denotes \<kappa>\<^sub>1'\<kappa>\<^sub>n' \<and>
        (\<forall>\<Pi> v. AOT_model_denotes \<Pi> \<longrightarrow> [v \<Turnstile> [\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n] = [v \<Turnstile> [\<Pi>]\<kappa>\<^sub>1'...\<kappa>\<^sub>n']) \<longrightarrow>
        [v \<Turnstile> \<phi>{\<kappa>\<^sub>1...\<kappa>\<^sub>n}] = [v \<Turnstile> \<phi>{\<kappa>\<^sub>1'...\<kappa>\<^sub>n'}]\<close> for \<kappa>\<^sub>1\<kappa>\<^sub>n \<kappa>\<^sub>1'\<kappa>\<^sub>n' v
    using AOT_sem_lambda_denotes[simplified AOT_sem_denotes] by blast
  {
    fix v and \<kappa>\<^sub>1\<kappa>\<^sub>n \<kappa>\<^sub>1'\<kappa>\<^sub>n' :: 'a
    assume d: \<open>AOT_model_denotes \<kappa>\<^sub>1\<kappa>\<^sub>n \<and> AOT_model_denotes \<kappa>\<^sub>1'\<kappa>\<^sub>n' \<and>
               AOT_model_term_equiv \<kappa>\<^sub>1\<kappa>\<^sub>n \<kappa>\<^sub>1'\<kappa>\<^sub>n'\<close>
    hence \<open>\<forall>\<Pi> w. AOT_model_denotes \<Pi> \<longrightarrow> [w \<Turnstile> [\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n] = [w \<Turnstile> [\<Pi>]\<kappa>\<^sub>1'...\<kappa>\<^sub>n']\<close>
      using AOT_model_term_equiv_rel_equiv
      using AOT_sem_exe_denoting
      by (metis AOT_sem_exe)
    hence \<open>[v \<Turnstile> \<phi>{\<kappa>\<^sub>1...\<kappa>\<^sub>n}] = [v \<Turnstile> \<phi>{\<kappa>\<^sub>1'...\<kappa>\<^sub>n'}]\<close> using d 1 by auto
  }
  moreover assume \<open>AOT_model_denotes \<kappa>\<close>
  moreover assume \<open>AOT_model_denotes \<kappa>'\<close>
  moreover assume \<open>AOT_model_term_equiv \<kappa> \<kappa>'\<close>
  ultimately show \<open>[v \<Turnstile> \<guillemotleft>\<phi> \<kappa>\<guillemotright>] \<Longrightarrow> [v \<Turnstile> \<guillemotleft>\<phi> \<kappa>'\<guillemotright>]\<close>
              and \<open>[v \<Turnstile> \<guillemotleft>\<phi> \<kappa>'\<guillemotright>] \<Longrightarrow> [v \<Turnstile> \<guillemotleft>\<phi> \<kappa>\<guillemotright>]\<close>
    by auto
next
  assume 0: \<open>\<forall> v \<kappa> \<kappa>' . AOT_model_denotes \<kappa> \<and> AOT_model_denotes \<kappa>' \<and>
                        AOT_model_term_equiv \<kappa> \<kappa>' \<longrightarrow> [v \<Turnstile> \<guillemotleft>\<phi> \<kappa>\<guillemotright>] = [v \<Turnstile> \<guillemotleft>\<phi> \<kappa>'\<guillemotright>]\<close>
  {
    fix \<kappa>\<^sub>1\<kappa>\<^sub>n \<kappa>\<^sub>1'\<kappa>\<^sub>n' :: 'a
    assume den: \<open>AOT_model_denotes \<kappa>\<^sub>1\<kappa>\<^sub>n\<close>
    moreover assume den': \<open>AOT_model_denotes \<kappa>\<^sub>1'\<kappa>\<^sub>n'\<close>
    assume \<open>\<forall>\<Pi> v . AOT_model_denotes \<Pi> \<longrightarrow>
                   [v \<Turnstile> [\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n] = [v \<Turnstile> [\<Pi>]\<kappa>\<^sub>1'...\<kappa>\<^sub>n']\<close>
    hence \<open>\<forall>\<Pi> v . AOT_model_denotes \<Pi> \<longrightarrow>
                   [v \<Turnstile> \<guillemotleft>Rep_rel \<Pi> \<kappa>\<^sub>1\<kappa>\<^sub>n\<guillemotright>] = [v \<Turnstile> \<guillemotleft>Rep_rel \<Pi> \<kappa>\<^sub>1'\<kappa>\<^sub>n'\<guillemotright>]\<close>
      by (metis AOT_sem_denotes AOT_sem_exe_denoting)
    hence "AOT_model_term_equiv \<kappa>\<^sub>1\<kappa>\<^sub>n \<kappa>\<^sub>1'\<kappa>\<^sub>n'"
      unfolding AOT_model_term_equiv_rel_equiv[OF den, OF den']
      by argo
    hence \<open>[v \<Turnstile> \<phi>{\<kappa>\<^sub>1...\<kappa>\<^sub>n}] = [v \<Turnstile> \<phi>{\<kappa>\<^sub>1'...\<kappa>\<^sub>n'}]\<close> for v
      using den den' 0 by blast
  }
  thus \<open>AOT_model_denotes (AOT_lambda \<phi>)\<close>
    unfolding AOT_sem_lambda_denotes[simplified AOT_sem_denotes]
    by blast
qed

specification (AOT_lambda0)
  AOT_sem_lambda0: "AOT_lambda0 \<phi> = \<phi>"
  by (rule exI[where x=\<open>\<lambda>x. x\<close>]) simp

consts AOT_sem_concrete :: \<open><'a::AOT_UnaryIndividualTerm>\<close>
specification(AOT_sem_concrete)
  AOT_sem_concrete: \<open>AOT_model_valid_in w (AOT_exe AOT_sem_concrete \<kappa>) =
                     AOT_model_concrete w \<kappa>\<close>
  AOT_sem_concrete_denotes: \<open>AOT_model_valid_in w (AOT_denotes AOT_sem_concrete)\<close>
  by (rule exI[where x=\<open>Abs_rel (\<lambda> x . \<epsilon>\<^sub>\<o> w . AOT_model_concrete w x)\<close>])
     (auto simp: AOT_model_no_special_nondenoting AOT_model_concrete_denotes
                 AOT_model_concrete_equiv AOT_model_regular_\<kappa>_def
                 AOT_model_proposition_choice_simp AOT_sem_exe Abs_rel_inverse
                 AOT_model_denotes_rel_def AOT_sem_denotes)
specification(AOT_concrete)
  AOT_concrete_sem: \<open>\<guillemotleft>E!\<guillemotright> = AOT_sem_concrete\<close>
  by simp


lemma AOT_sem_equiv_defI:
  assumes \<open>\<And> v . [v \<Turnstile> \<phi>] \<Longrightarrow> [v \<Turnstile> \<psi>]\<close>
      and \<open>\<And> v . [v \<Turnstile> \<psi>] \<Longrightarrow> [v \<Turnstile> \<phi>]\<close>
    shows "AOT_model_equiv_def \<phi> \<psi>"
  using AOT_model_equiv_def assms by blast

lemma AOT_sem_id_defI:
  assumes \<open>\<And> \<alpha> v . [v \<Turnstile> \<guillemotleft>\<sigma> \<alpha>\<guillemotright>\<down>] \<Longrightarrow> [v \<Turnstile> \<guillemotleft>\<tau> \<alpha>\<guillemotright> = \<guillemotleft>\<sigma> \<alpha>\<guillemotright>]\<close>
  assumes \<open>\<And> \<alpha> v . \<not>[v \<Turnstile> \<guillemotleft>\<sigma> \<alpha>\<guillemotright>\<down>] \<Longrightarrow> [v \<Turnstile> \<not>\<guillemotleft>\<tau> \<alpha>\<guillemotright>\<down>]\<close>
  shows \<open>AOT_model_id_def \<tau> \<sigma>\<close>
  using assms
  unfolding AOT_sem_denotes AOT_sem_eq AOT_sem_not
  using AOT_model_id_def[THEN iffD2]
  by metis

lemma AOT_sem_id_def2I:
  assumes \<open>\<And> \<alpha> \<beta> v . [v \<Turnstile> \<guillemotleft>\<sigma> \<alpha> \<beta>\<guillemotright>\<down>] \<Longrightarrow> [v \<Turnstile> \<guillemotleft>\<tau> \<alpha> \<beta>\<guillemotright> = \<guillemotleft>\<sigma> \<alpha> \<beta>\<guillemotright>]\<close>
  assumes \<open>\<And> \<alpha> \<beta> v . \<not>[v \<Turnstile> \<guillemotleft>\<sigma> \<alpha> \<beta>\<guillemotright>\<down>] \<Longrightarrow> [v \<Turnstile> \<not>\<guillemotleft>\<tau> \<alpha> \<beta>\<guillemotright>\<down>]\<close>
  shows \<open>AOT_model_id_def (case_prod \<tau>) (case_prod \<sigma>)\<close>
  apply (rule AOT_sem_id_defI)
  using assms by (auto simp: AOT_sem_conj AOT_sem_not AOT_sem_eq AOT_sem_denotes
      AOT_model_denotes_prod_def)

lemma AOT_sem_id_defE1:
  assumes \<open>AOT_model_id_def \<tau> \<sigma>\<close>
      and \<open>[v \<Turnstile> \<guillemotleft>\<sigma> \<alpha>\<guillemotright>\<down>]\<close>
    shows \<open>[v \<Turnstile> \<guillemotleft>\<tau> \<alpha>\<guillemotright> = \<guillemotleft>\<sigma> \<alpha>\<guillemotright>]\<close>
  using assms by (simp add: AOT_model_id_def AOT_sem_denotes AOT_sem_eq)

lemma AOT_sem_id_defE2:
  assumes \<open>AOT_model_id_def \<tau> \<sigma>\<close>
      and \<open>\<not>[v \<Turnstile> \<guillemotleft>\<sigma> \<alpha>\<guillemotright>\<down>]\<close>
    shows \<open>\<not>[v \<Turnstile> \<guillemotleft>\<tau> \<alpha>\<guillemotright>\<down>]\<close>
  using assms by (simp add: AOT_model_id_def AOT_sem_denotes AOT_sem_eq)

lemma AOT_sem_id_def0I:
  assumes \<open>\<And> v . [v \<Turnstile> \<sigma>\<down>] \<Longrightarrow> [v \<Turnstile> \<tau> = \<sigma>]\<close>
      and \<open>\<And> v . \<not>[v \<Turnstile> \<sigma>\<down>] \<Longrightarrow> [v \<Turnstile> \<not>\<tau>\<down>]\<close>
  shows \<open>AOT_model_id_def (case_unit \<tau>) (case_unit \<sigma>)\<close>
  apply (rule AOT_sem_id_defI)
  using assms
  by (simp_all add: AOT_sem_conj AOT_sem_eq AOT_sem_not AOT_sem_denotes
                    AOT_model_denotes_unit_def case_unit_Unity)

lemma AOT_sem_id_def0E1:
  assumes \<open>AOT_model_id_def (case_unit \<tau>) (case_unit \<sigma>)\<close>
      and \<open>[v \<Turnstile> \<sigma>\<down>]\<close>
    shows \<open>[v \<Turnstile> \<tau> = \<sigma>]\<close>
  by (metis (full_types) AOT_sem_id_defE1 assms(1) assms(2) case_unit_Unity)

lemma AOT_sem_id_def0E2:
  assumes \<open>AOT_model_id_def (case_unit \<tau>) (case_unit \<sigma>)\<close>
      and \<open>\<not>[v \<Turnstile> \<sigma>\<down>]\<close>
    shows \<open>\<not>[v \<Turnstile> \<tau>\<down>]\<close>
  by (metis AOT_sem_id_defE2 assms(1) assms(2) case_unit_Unity)

lemma AOT_sem_id_def0E3:
  assumes \<open>AOT_model_id_def (case_unit \<tau>) (case_unit \<sigma>)\<close>
      and \<open>[v \<Turnstile> \<sigma>\<down>]\<close>
    shows \<open>[v \<Turnstile> \<tau>\<down>]\<close>
  using AOT_sem_id_def0E1[OF assms]
  by (simp add: AOT_sem_eq AOT_sem_denotes)

lemma AOT_sem_ordinary_def_denotes: \<open>[w \<Turnstile> [\<lambda>x \<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<down>]\<close>
  unfolding AOT_sem_denotes AOT_model_lambda_denotes
  by (auto simp: AOT_sem_dia AOT_concrete_sem AOT_model_concrete_equiv
                 AOT_sem_concrete AOT_sem_denotes)
lemma AOT_sem_abstract_def_denotes: \<open>[w \<Turnstile> [\<lambda>x \<not>\<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<down>]\<close>
  unfolding AOT_sem_denotes AOT_model_lambda_denotes
  by (auto simp: AOT_sem_dia AOT_concrete_sem AOT_model_concrete_equiv
                 AOT_sem_concrete AOT_sem_denotes AOT_sem_not)

class AOT_Individual = 
  fixes AOT_sem_proj_id :: \<open>'a::AOT_IndividualTerm \<Rightarrow> ('a \<Rightarrow> \<o>) \<Rightarrow> ('a \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close>
  assumes AOT_sem_proj_id_prop:
    \<open>[v \<Turnstile> \<Pi> = \<Pi>'] =
     [v \<Turnstile> \<Pi>\<down> & \<Pi>'\<down> & \<forall>\<alpha> (\<guillemotleft>AOT_sem_proj_id \<alpha> (\<lambda> \<tau> . \<guillemotleft>[\<Pi>]\<tau>\<guillemotright>) (\<lambda> \<tau> . \<guillemotleft>[\<Pi>']\<tau>\<guillemotright>)\<guillemotright>)]\<close>
      and AOT_sem_proj_id_refl:
    \<open>[v \<Turnstile> \<tau>\<down>] \<Longrightarrow> [v \<Turnstile> [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}] = [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]] \<Longrightarrow>
     [v \<Turnstile> \<guillemotleft>AOT_sem_proj_id \<tau> \<phi> \<phi>\<guillemotright>]\<close>

class AOT_UnaryIndividual = AOT_Individual +
  assumes AOT_sem_unary_proj_id:
    \<open>AOT_sem_proj_id \<kappa> \<phi> \<psi> = \<guillemotleft>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}] = [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<psi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<guillemotright>\<close>

instantiation \<kappa> :: AOT_UnaryIndividual
begin
definition AOT_sem_proj_id_\<kappa> :: \<open>\<kappa> \<Rightarrow> (\<kappa> \<Rightarrow> \<o>) \<Rightarrow> (\<kappa> \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close> where
  \<open>AOT_sem_proj_id_\<kappa> \<kappa> \<phi> \<psi> = \<guillemotleft>[\<lambda>z \<phi>{z}] = [\<lambda>z \<psi>{z}]\<guillemotright>\<close>
instance proof
  show \<open>[v \<Turnstile> \<Pi> = \<Pi>'] =
        [v \<Turnstile> \<Pi>\<down> & \<Pi>'\<down> & \<forall>\<alpha> (\<guillemotleft>AOT_sem_proj_id \<alpha> (\<lambda> \<tau> . \<guillemotleft>[\<Pi>]\<tau>\<guillemotright>) (\<lambda> \<tau> . \<guillemotleft>[\<Pi>']\<tau>\<guillemotright>)\<guillemotright>)]\<close>
    for v and \<Pi> \<Pi>' :: \<open><\<kappa>>\<close>
    unfolding AOT_sem_proj_id_\<kappa>_def
    by (simp add: AOT_sem_eq AOT_sem_conj AOT_sem_denotes AOT_sem_forall)
       (metis AOT_sem_denotes AOT_model_denoting_ex AOT_sem_eq AOT_sem_lambda_eta)
next
  show \<open>AOT_sem_proj_id \<kappa> \<phi> \<psi> = \<guillemotleft>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}] = [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<psi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<guillemotright>\<close>
    for \<kappa> :: \<kappa> and \<phi> \<psi>
    unfolding AOT_sem_proj_id_\<kappa>_def ..
next
  show \<open>[v \<Turnstile> \<guillemotleft>AOT_sem_proj_id \<tau> \<phi> \<phi>\<guillemotright>]\<close>
    if \<open>[v \<Turnstile> \<tau>\<down>]\<close> and \<open>[v \<Turnstile> [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}] = [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]]\<close>
    for \<tau> :: \<kappa> and v \<phi>
    using that by (simp add: AOT_sem_proj_id_\<kappa>_def AOT_sem_eq)
qed
end

instantiation prod ::
  ("{AOT_UnaryIndividual, AOT_UnaryIndividualTerm}", AOT_Individual) AOT_Individual
begin
definition AOT_sem_proj_id_prod :: \<open>'a\<times>'b \<Rightarrow> ('a\<times>'b \<Rightarrow> \<o>) \<Rightarrow> ('a\<times>'b \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close> where
  \<open>AOT_sem_proj_id_prod \<equiv> \<lambda> (x,y) \<phi> \<psi> . \<guillemotleft>[\<lambda>z \<guillemotleft>\<phi> (z,y)\<guillemotright>] = [\<lambda>z \<guillemotleft>\<psi> (z,y)\<guillemotright>] &
    \<guillemotleft>AOT_sem_proj_id y (\<lambda> a . \<phi> (x,a)) (\<lambda> a . \<psi> (x,a))\<guillemotright>\<guillemotright>\<close>
instance proof
  fix v and \<Pi> \<Pi>' :: \<open><'a\<times>'b>\<close>
  have AOT_meta_proj_denotes1: \<open>AOT_model_denotes (Abs_rel (\<lambda>z. AOT_exe \<Pi> (z, \<beta>)))\<close>
    if \<open>AOT_model_denotes \<Pi>\<close> for \<Pi> :: \<open><'a\<times>'b>\<close> and \<beta>
    using that unfolding AOT_model_denotes_rel.rep_eq
    (* TODO *)
    apply (auto simp: Abs_rel_inverse AOT_meta_prod_equivI(2) AOT_sem_denotes
                      AOT_sem_exe_denoting that)
    apply (metis AOT_model_denotes_prod_def case_prodD)
    using AOT_model_no_special_nondenoting by blast
  {
    fix \<kappa> :: 'a and \<Pi> :: \<open><'a\<times>'b>\<close>
    assume \<Pi>_denotes: \<open>AOT_model_denotes \<Pi>\<close>
    assume \<alpha>_denotes: \<open>AOT_model_denotes \<kappa>\<close>
    hence \<open>AOT_exe \<Pi> (\<kappa>, x) = AOT_exe \<Pi> (\<kappa>, y)\<close>
       if \<open>AOT_model_term_equiv x y\<close> for x y :: 'b
      by (metis that AOT_meta_prod_equivI(1) AOT_model_denotes_rel.rep_eq
                AOT_sem_denotes AOT_sem_exe_denoting \<Pi>_denotes)
    moreover have \<open>AOT_model_denotes \<kappa>\<^sub>1'\<kappa>\<^sub>n'\<close>
               if \<open>[w \<Turnstile> [\<Pi>]\<kappa> \<kappa>\<^sub>1'...\<kappa>\<^sub>n']\<close> for w \<kappa>\<^sub>1'\<kappa>\<^sub>n'
      by (metis that AOT_model_denotes_prod_def AOT_sem_exe
                AOT_sem_denotes case_prodD)
    moreover {
      fix x :: 'b
      assume x_special: \<open>\<not>AOT_model_regular x\<close>
      hence prod_special: \<open>\<not>AOT_model_regular (\<kappa>, x)\<close>
        by (metis (no_types, lifting) AOT_model_irregular_nondenoting
                                      AOT_model_regular_prod_def case_prodD)
      hence \<open>(\<not>AOT_model_denotes \<kappa> \<or> \<not>AOT_model_regular x) \<and>
             (AOT_model_denotes \<kappa> \<or> \<not>AOT_model_denotes x)\<close>
        unfolding AOT_model_regular_prod_def by blast
      hence x_nonden: \<open>\<not>AOT_model_regular x\<close>
        by (simp add: \<alpha>_denotes)
      have \<open>Rep_rel \<Pi> (\<kappa>, x) = AOT_model_irregular (Rep_rel \<Pi>) (\<kappa>, x)\<close>
        using AOT_model_denotes_rel.rep_eq \<Pi>_denotes prod_special by blast
      moreover have \<open>AOT_model_irregular (Rep_rel \<Pi>) (\<kappa>, x) =
                     AOT_model_irregular (\<lambda>z. Rep_rel \<Pi> (\<kappa>, z)) x\<close>
        using \<Pi>_denotes x_special prod_special x_nonden
        using AOT_model_irregular_prod_generic
        apply (induct arbitrary: \<Pi> x rule: AOT_model_irregular_prod.induct)
        by (auto simp: \<alpha>_denotes AOT_model_irregular_nondenoting
                       AOT_model_regular_prod_def AOT_meta_prod_equivI(2)
                       AOT_model_denotes_rel.rep_eq AOT_model_term_equiv_eps(1)
                 intro!: AOT_model_irregular_eqI)
      ultimately have
        \<open>AOT_exe \<Pi> (\<kappa>, x) = AOT_model_irregular (\<lambda>z. AOT_exe \<Pi> (\<kappa>, z)) x\<close>
        unfolding AOT_sem_exe_denoting[simplified AOT_sem_denotes, OF \<Pi>_denotes]
        by auto
    }
    ultimately have "AOT_model_denotes (Abs_rel (\<lambda>z. AOT_exe \<Pi> (\<kappa>, z)))"
      by (simp add: Abs_rel_inverse AOT_model_denotes_rel.rep_eq)
  } note AOT_meta_proj_denotes2 = this
  {
    assume \<Pi>_denotes: \<open>AOT_model_denotes \<Pi>\<close>
    assume \<Pi>'_denotes: \<open>AOT_model_denotes \<Pi>'\<close>
    have \<Pi>_proj2_den: \<open>AOT_model_denotes (Abs_rel (\<lambda>z. Rep_rel \<Pi> (\<alpha>, z)))\<close>
      if \<open>AOT_model_denotes \<alpha>\<close> for \<alpha>
      using that AOT_meta_proj_denotes2[OF \<Pi>_denotes]
            AOT_sem_exe_denoting[simplified AOT_sem_denotes,OF \<Pi>_denotes] by simp
    have \<Pi>'_proj2_den: \<open>AOT_model_denotes (Abs_rel (\<lambda>z. Rep_rel \<Pi>' (\<alpha>, z)))\<close>
      if \<open>AOT_model_denotes \<alpha>\<close> for \<alpha>
      using that AOT_meta_proj_denotes2[OF \<Pi>'_denotes]
            AOT_sem_exe_denoting[simplified AOT_sem_denotes,OF \<Pi>'_denotes] by simp
    {
      fix \<kappa> :: 'a and \<kappa>\<^sub>1'\<kappa>\<^sub>n' :: 'b
      assume \<open>\<Pi> = \<Pi>'\<close>
      assume \<open>AOT_model_denotes (\<kappa>,\<kappa>\<^sub>1'\<kappa>\<^sub>n')\<close>
      hence \<open>AOT_model_denotes \<kappa>\<close> and beta_denotes: \<open>AOT_model_denotes \<kappa>\<^sub>1'\<kappa>\<^sub>n'\<close>
        by (auto simp: AOT_model_denotes_prod_def)
      have \<open>AOT_model_denotes \<guillemotleft>[\<lambda>z [\<Pi>]z \<kappa>\<^sub>1'...\<kappa>\<^sub>n']\<guillemotright>\<close>
        by (rule AOT_model_lambda_denotes[THEN iffD2])
           (metis AOT_sem_exe_denoting AOT_meta_prod_equivI(2)
                  AOT_model_denotes_rel.rep_eq AOT_sem_denotes
                  AOT_sem_exe_denoting \<Pi>_denotes)
      moreover have \<open>\<guillemotleft>[\<lambda>z [\<Pi>]z \<kappa>\<^sub>1'...\<kappa>\<^sub>n']\<guillemotright> = \<guillemotleft>[\<lambda>z [\<Pi>']z \<kappa>\<^sub>1'...\<kappa>\<^sub>n']\<guillemotright>\<close>
        by (simp add: \<open>\<Pi> = \<Pi>'\<close>)
      moreover have \<open>[v \<Turnstile> \<guillemotleft>AOT_sem_proj_id \<kappa>\<^sub>1'\<kappa>\<^sub>n' (\<lambda>\<kappa>\<^sub>1'\<kappa>\<^sub>n'. \<guillemotleft>[\<Pi>]\<kappa> \<kappa>\<^sub>1'...\<kappa>\<^sub>n'\<guillemotright>)
                                                  (\<lambda>\<kappa>\<^sub>1'\<kappa>\<^sub>n'. \<guillemotleft>[\<Pi>']\<kappa> \<kappa>\<^sub>1'...\<kappa>\<^sub>n'\<guillemotright>)\<guillemotright>]\<close>
        unfolding \<open>\<Pi> = \<Pi>'\<close> using beta_denotes
        by (rule AOT_sem_proj_id_refl[unfolded AOT_sem_denotes];
            simp add: AOT_sem_denotes AOT_sem_eq AOT_model_lambda_denotes)
           (metis AOT_meta_prod_equivI(1) AOT_model_denotes_rel.rep_eq
                  AOT_sem_exe AOT_sem_exe_denoting \<Pi>'_denotes)
      ultimately have \<open>[v \<Turnstile> \<guillemotleft>AOT_sem_proj_id (\<kappa>,\<kappa>\<^sub>1'\<kappa>\<^sub>n') (\<lambda> \<kappa>\<^sub>1\<kappa>\<^sub>n . \<guillemotleft>[\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n\<guillemotright>)
                                                         (\<lambda> \<kappa>\<^sub>1\<kappa>\<^sub>n . \<guillemotleft>[\<Pi>']\<kappa>\<^sub>1...\<kappa>\<^sub>n\<guillemotright>)\<guillemotright>]\<close>
        unfolding AOT_sem_proj_id_prod_def
        by (simp add: AOT_sem_denotes AOT_sem_conj AOT_sem_eq)
    }
    moreover {
      assume \<open>\<And> \<alpha> . AOT_model_denotes \<alpha> \<Longrightarrow>
        [v \<Turnstile> \<guillemotleft>AOT_sem_proj_id \<alpha> (\<lambda> \<kappa>\<^sub>1\<kappa>\<^sub>n . \<guillemotleft>[\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n\<guillemotright>) (\<lambda> \<kappa>\<^sub>1\<kappa>\<^sub>n . \<guillemotleft>[\<Pi>']\<kappa>\<^sub>1...\<kappa>\<^sub>n\<guillemotright>)\<guillemotright>]\<close>
      hence 0: \<open>AOT_model_denotes \<kappa> \<Longrightarrow> AOT_model_denotes \<kappa>\<^sub>1'\<kappa>\<^sub>n' \<Longrightarrow>
             AOT_model_denotes \<guillemotleft>[\<lambda>z [\<Pi>]z \<kappa>\<^sub>1'...\<kappa>\<^sub>n']\<guillemotright> \<and>
             AOT_model_denotes \<guillemotleft>[\<lambda>z [\<Pi>']z \<kappa>\<^sub>1'...\<kappa>\<^sub>n']\<guillemotright> \<and>
             \<guillemotleft>[\<lambda>z [\<Pi>]z \<kappa>\<^sub>1'...\<kappa>\<^sub>n']\<guillemotright> = \<guillemotleft>[\<lambda>z [\<Pi>']z \<kappa>\<^sub>1'...\<kappa>\<^sub>n']\<guillemotright> \<and>
             [v \<Turnstile> \<guillemotleft>AOT_sem_proj_id \<kappa>\<^sub>1'\<kappa>\<^sub>n' (\<lambda>\<kappa>\<^sub>1\<kappa>\<^sub>n. \<guillemotleft>[\<Pi>]\<kappa> \<kappa>\<^sub>1...\<kappa>\<^sub>n\<guillemotright>)
                                          (\<lambda>\<kappa>\<^sub>1\<kappa>\<^sub>n. \<guillemotleft>[\<Pi>']\<kappa> \<kappa>\<^sub>1...\<kappa>\<^sub>n\<guillemotright>)\<guillemotright>]\<close> for \<kappa> \<kappa>\<^sub>1'\<kappa>\<^sub>n'
        unfolding AOT_sem_proj_id_prod_def
        by (auto simp: AOT_sem_denotes AOT_sem_conj AOT_sem_eq
                       AOT_model_denotes_prod_def)
      obtain \<alpha>den :: 'a and \<beta>den :: 'b where
        \<alpha>den: \<open>AOT_model_denotes \<alpha>den\<close> and \<beta>den: \<open>AOT_model_denotes \<beta>den\<close>
        using AOT_model_denoting_ex by metis
      {
        fix \<kappa> :: 'a
        assume \<alpha>denotes: \<open>AOT_model_denotes \<kappa>\<close>
        have 1: \<open>[v \<Turnstile> \<guillemotleft>AOT_sem_proj_id \<kappa>\<^sub>1'\<kappa>\<^sub>n' (\<lambda>\<kappa>\<^sub>1'\<kappa>\<^sub>n'. \<guillemotleft>[\<Pi>]\<kappa> \<kappa>\<^sub>1'...\<kappa>\<^sub>n'\<guillemotright>)
                                              (\<lambda>\<kappa>\<^sub>1'\<kappa>\<^sub>n'. \<guillemotleft>[\<Pi>']\<kappa> \<kappa>\<^sub>1'...\<kappa>\<^sub>n'\<guillemotright>)\<guillemotright>]\<close>
          if \<open>AOT_model_denotes \<kappa>\<^sub>1'\<kappa>\<^sub>n'\<close> for \<kappa>\<^sub>1'\<kappa>\<^sub>n'
          using that 0 using \<alpha>denotes by blast
        hence \<open>[v \<Turnstile> \<guillemotleft>AOT_sem_proj_id \<beta> (\<lambda>z. Rep_rel \<Pi> (\<kappa>, z))
                                        (\<lambda>z. Rep_rel \<Pi>' (\<kappa>, z))\<guillemotright>]\<close>
          if \<open>AOT_model_denotes \<beta>\<close> for \<beta>
          using that
          unfolding AOT_sem_exe_denoting[simplified AOT_sem_denotes, OF \<Pi>_denotes]
                    AOT_sem_exe_denoting[simplified AOT_sem_denotes, OF \<Pi>'_denotes]
          by blast
        hence \<open>Abs_rel (\<lambda>z. Rep_rel \<Pi> (\<kappa>, z)) = Abs_rel (\<lambda>z. Rep_rel \<Pi>' (\<kappa>, z))\<close>
          using AOT_sem_proj_id_prop[of v \<open>Abs_rel (\<lambda>z. Rep_rel \<Pi> (\<kappa>, z))\<close>
                                          \<open>Abs_rel (\<lambda>z. Rep_rel \<Pi>' (\<kappa>, z))\<close>,
                  simplified AOT_sem_eq AOT_sem_conj AOT_sem_forall
                             AOT_sem_denotes, THEN iffD2]
                \<Pi>_proj2_den[OF \<alpha>denotes] \<Pi>'_proj2_den[OF \<alpha>denotes]
          unfolding AOT_sem_exe_denoting[simplified AOT_sem_denotes, OF \<Pi>_denotes]
                    AOT_sem_exe_denoting[simplified AOT_sem_denotes,
                                         OF \<Pi>_proj2_den[OF \<alpha>denotes]]
                    AOT_sem_exe_denoting[simplified AOT_sem_denotes,
                                         OF \<Pi>'_proj2_den[OF \<alpha>denotes]]
          by (metis Abs_rel_inverse UNIV_I)
        hence "Rep_rel \<Pi> (\<kappa>,\<beta>) = Rep_rel \<Pi>' (\<kappa>,\<beta>)" for \<beta>
          by (simp add: Abs_rel_inject[simplified]) meson
      } note \<alpha>denotes = this
      {
        fix \<kappa>\<^sub>1'\<kappa>\<^sub>n' :: 'b
        assume \<beta>den: \<open>AOT_model_denotes \<kappa>\<^sub>1'\<kappa>\<^sub>n'\<close>
        have \<open>Abs_rel (\<lambda>x. AOT_exe \<Pi> (x, \<kappa>\<^sub>1'\<kappa>\<^sub>n')) = Abs_rel (\<lambda>\<kappa>. \<guillemotleft>[\<Pi>']\<kappa> \<kappa>\<^sub>1'...\<kappa>\<^sub>n'\<guillemotright>)\<close>
          using AOT_sem_lambda_denoting[of v \<open>\<lambda>\<kappa>. \<guillemotleft>[\<Pi>]\<kappa> \<kappa>\<^sub>1'...\<kappa>\<^sub>n'\<guillemotright>\<close>]
          using AOT_sem_lambda_denoting[of v \<open>\<lambda>\<kappa>. \<guillemotleft>[\<Pi>']\<kappa> \<kappa>\<^sub>1'...\<kappa>\<^sub>n'\<guillemotright>\<close>]
          using AOT_meta_proj_denotes1[OF \<Pi>_denotes]
                AOT_meta_proj_denotes1[OF \<Pi>'_denotes] 0[OF \<alpha>den, OF \<beta>den]
          by (simp add: AOT_sem_denotes)
        hence \<open>Rep_rel \<Pi> (x,\<kappa>\<^sub>1'\<kappa>\<^sub>n') = Rep_rel \<Pi>' (x,\<kappa>\<^sub>1'\<kappa>\<^sub>n')\<close> for x
          by (simp add: Abs_rel_inject)
             (metis AOT_sem_exe_denoting AOT_sem_denotes \<Pi>'_denotes \<Pi>_denotes)
      } note \<beta>denotes = this
      {
        fix \<alpha> :: 'a and \<beta> :: 'b
        assume nospecial_\<alpha>\<beta>: \<open>AOT_model_regular (\<alpha>, \<beta>)\<close>
        thm AOT_model_regular_prod_def
        moreover {
          assume \<open>AOT_model_denotes \<alpha> \<and> AOT_model_regular \<beta>\<close>
          hence \<open>Rep_rel \<Pi> (\<alpha>,\<beta>) = Rep_rel \<Pi>' (\<alpha>,\<beta>)\<close>
            using \<alpha>denotes by presburger
        }
        moreover {
          assume \<open>\<not>AOT_model_denotes \<alpha> \<and> AOT_model_denotes \<beta>\<close>
          hence \<open>Rep_rel \<Pi> (\<alpha>,\<beta>) = Rep_rel \<Pi>' (\<alpha>,\<beta>)\<close>
            by (simp add: \<beta>denotes)
        }
        ultimately have \<open>Rep_rel \<Pi> (\<alpha>,\<beta>) = Rep_rel \<Pi>' (\<alpha>,\<beta>)\<close>
          by (metis (no_types, lifting) AOT_model_regular_prod_def case_prodD)
      }
      hence \<open>Rep_rel \<Pi> = Rep_rel \<Pi>'\<close>
        using \<Pi>_denotes[unfolded AOT_model_denotes_rel.rep_eq,
                        THEN conjunct2, THEN conjunct2, THEN spec, THEN mp]
        using \<Pi>'_denotes[unfolded AOT_model_denotes_rel.rep_eq,
                         THEN conjunct2, THEN conjunct2, THEN spec, THEN mp]
        using AOT_model_irregular_eqI[of \<open>Rep_rel \<Pi>\<close> \<open>Rep_rel \<Pi>'\<close> \<open>(_,_)\<close>]
        using AOT_model_irregular_nondenoting by fastforce
      hence \<open>\<Pi> = \<Pi>'\<close>
        by (rule Rep_rel_inject[THEN iffD1])
    }
    ultimately have \<open>\<Pi> = \<Pi>' = (\<forall> \<kappa> . AOT_model_denotes \<kappa> \<longrightarrow>
        [v \<Turnstile> \<guillemotleft>AOT_sem_proj_id \<kappa> (\<lambda> \<kappa>\<^sub>1\<kappa>\<^sub>n . \<guillemotleft>[\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n\<guillemotright>)
                                (\<lambda> \<kappa>\<^sub>1\<kappa>\<^sub>n . \<guillemotleft>[\<Pi>']\<kappa>\<^sub>1...\<kappa>\<^sub>n\<guillemotright>)\<guillemotright>])\<close>
      by auto
  }
  thus \<open>[v \<Turnstile> \<Pi> = \<Pi>'] = [v \<Turnstile> \<Pi>\<down> & \<Pi>'\<down> &
      \<forall>\<alpha> (\<guillemotleft>AOT_sem_proj_id \<alpha> (\<lambda> \<kappa>\<^sub>1\<kappa>\<^sub>n . \<guillemotleft>[\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n\<guillemotright>) (\<lambda> \<kappa>\<^sub>1\<kappa>\<^sub>n . \<guillemotleft>[\<Pi>']\<kappa>\<^sub>1...\<kappa>\<^sub>n\<guillemotright>)\<guillemotright>)]\<close>
    by (auto simp: AOT_sem_eq AOT_sem_denotes AOT_sem_forall AOT_sem_conj)
next
  fix v and \<phi> :: \<open>'a\<times>'b\<Rightarrow>\<o>\<close> and \<tau> :: \<open>'a\<times>'b\<close>
  assume \<open>[v \<Turnstile> \<tau>\<down>]\<close>
  moreover assume \<open>[v \<Turnstile> [\<lambda>z\<^sub>1...z\<^sub>n \<guillemotleft>\<phi> z\<^sub>1z\<^sub>n\<guillemotright>] = [\<lambda>z\<^sub>1...z\<^sub>n \<guillemotleft>\<phi> z\<^sub>1z\<^sub>n\<guillemotright>]]\<close>
  ultimately show \<open>[v \<Turnstile> \<guillemotleft>AOT_sem_proj_id \<tau> \<phi> \<phi>\<guillemotright>]\<close>
    unfolding AOT_sem_proj_id_prod_def
    using AOT_sem_proj_id_refl[of v "snd \<tau>" "\<lambda>b. \<phi> (fst \<tau>, b)"]
    by (auto simp: AOT_sem_eq AOT_sem_conj AOT_sem_denotes
                   AOT_model_denotes_prod_def AOT_model_lambda_denotes
                   AOT_meta_prod_equivI)
qed
end

lemma \<open>[v \<Turnstile> \<Pi> = \<Pi>'] = [v \<Turnstile> \<Pi>\<down> & \<Pi>'\<down> & \<forall>x\<forall>y([\<lambda>z [\<Pi>]z y] = [\<lambda>z [\<Pi>']z y] &
                                              [\<lambda>z [\<Pi>]x z] = [\<lambda>z [\<Pi>']x z])]\<close>
  for \<Pi> :: \<open><\<kappa>\<times>\<kappa>>\<close>
  by (auto simp: AOT_sem_proj_id_prop[of v \<Pi> \<Pi>'] AOT_sem_proj_id_prod_def
                 AOT_sem_conj AOT_sem_denotes AOT_sem_forall AOT_sem_unary_proj_id
                 AOT_model_denotes_prod_def)
lemma \<open>[v \<Turnstile> \<Pi> = \<Pi>'] = [v \<Turnstile> \<Pi>\<down> & \<Pi>'\<down> & \<forall>x\<^sub>1\<forall>x\<^sub>2\<forall>x\<^sub>3 (
  [\<lambda>z [\<Pi>]z x\<^sub>2 x\<^sub>3] = [\<lambda>z [\<Pi>']z x\<^sub>2 x\<^sub>3] &
  [\<lambda>z [\<Pi>]x\<^sub>1 z x\<^sub>3] = [\<lambda>z [\<Pi>']x\<^sub>1 z x\<^sub>3] &
  [\<lambda>z [\<Pi>]x\<^sub>1 x\<^sub>2 z] = [\<lambda>z [\<Pi>']x\<^sub>1 x\<^sub>2 z])]\<close>
  for \<Pi> :: \<open><\<kappa>\<times>\<kappa>\<times>\<kappa>>\<close>
  by (auto simp: AOT_sem_proj_id_prop[of v \<Pi> \<Pi>'] AOT_sem_proj_id_prod_def
                 AOT_sem_conj AOT_sem_denotes AOT_sem_forall AOT_sem_unary_proj_id
                 AOT_model_denotes_prod_def)
lemma \<open>[v \<Turnstile> \<Pi> = \<Pi>'] = [v \<Turnstile> \<Pi>\<down> & \<Pi>'\<down> & \<forall>x\<^sub>1\<forall>x\<^sub>2\<forall>x\<^sub>3\<forall>x\<^sub>4 (
    [\<lambda>z [\<Pi>]z x\<^sub>2 x\<^sub>3 x\<^sub>4] = [\<lambda>z [\<Pi>']z x\<^sub>2 x\<^sub>3 x\<^sub>4] &
    [\<lambda>z [\<Pi>]x\<^sub>1 z x\<^sub>3 x\<^sub>4] = [\<lambda>z [\<Pi>']x\<^sub>1 z x\<^sub>3 x\<^sub>4] &
    [\<lambda>z [\<Pi>]x\<^sub>1 x\<^sub>2 z x\<^sub>4] = [\<lambda>z [\<Pi>']x\<^sub>1 x\<^sub>2 z x\<^sub>4] &
    [\<lambda>z [\<Pi>]x\<^sub>1 x\<^sub>2 x\<^sub>3 z] = [\<lambda>z [\<Pi>']x\<^sub>1 x\<^sub>2 x\<^sub>3 z])]\<close>
  for \<Pi> :: \<open><\<kappa>\<times>\<kappa>\<times>\<kappa>\<times>\<kappa>>\<close>
  by (auto simp: AOT_sem_proj_id_prop[of v \<Pi> \<Pi>'] AOT_sem_proj_id_prod_def
                 AOT_sem_conj AOT_sem_denotes AOT_sem_forall AOT_sem_unary_proj_id
                 AOT_model_denotes_prod_def)

class AOT_Enc =
  fixes AOT_enc :: \<open>'a \<Rightarrow> <'a::AOT_IndividualTerm> \<Rightarrow> \<o>\<close>
    and AOT_proj_enc :: \<open>'a \<Rightarrow> ('a \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close>
  assumes AOT_sem_enc_denotes:
    \<open>[v \<Turnstile> \<guillemotleft>AOT_enc \<kappa>\<^sub>1\<kappa>\<^sub>n \<Pi>\<guillemotright>] \<Longrightarrow> [v \<Turnstile> \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>] \<and> [v \<Turnstile> \<Pi>\<down>]\<close>
  assumes AOT_sem_enc_proj_enc:
    \<open>[v \<Turnstile> \<guillemotleft>AOT_enc \<kappa>\<^sub>1\<kappa>\<^sub>n \<Pi>\<guillemotright>] =
     [v \<Turnstile> \<Pi>\<down> & \<guillemotleft>AOT_proj_enc \<kappa>\<^sub>1\<kappa>\<^sub>n (\<lambda> \<kappa>\<^sub>1\<kappa>\<^sub>n.  \<guillemotleft>[\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n\<guillemotright>)\<guillemotright>]\<close>
  assumes AOT_sem_proj_enc_denotes:
    \<open>[v \<Turnstile> \<guillemotleft>AOT_proj_enc \<kappa>\<^sub>1\<kappa>\<^sub>n \<phi>\<guillemotright>] \<Longrightarrow> [v \<Turnstile> \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>]\<close>
  assumes AOT_sem_enc_nec:
    \<open>[v \<Turnstile> \<guillemotleft>AOT_enc \<kappa>\<^sub>1\<kappa>\<^sub>n \<Pi>\<guillemotright>] \<Longrightarrow> [w \<Turnstile> \<guillemotleft>AOT_enc \<kappa>\<^sub>1\<kappa>\<^sub>n \<Pi>\<guillemotright>]\<close>
  assumes AOT_sem_proj_enc_nec:
    \<open>[v \<Turnstile> \<guillemotleft>AOT_proj_enc \<kappa>\<^sub>1\<kappa>\<^sub>n \<phi>\<guillemotright>] \<Longrightarrow> [w \<Turnstile> \<guillemotleft>AOT_proj_enc \<kappa>\<^sub>1\<kappa>\<^sub>n \<phi>\<guillemotright>]\<close>
  assumes AOT_sem_universal_encoder:
    \<open>\<exists> \<kappa>\<^sub>1\<kappa>\<^sub>n. [v \<Turnstile> \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>] \<and> (\<forall> \<Pi> . [v \<Turnstile> \<Pi>\<down>] \<longrightarrow> [v \<Turnstile> \<guillemotleft>AOT_enc \<kappa>\<^sub>1\<kappa>\<^sub>n \<Pi>\<guillemotright>]) \<and>
             (\<forall> \<phi> . [v \<Turnstile> [\<lambda>z\<^sub>1...z\<^sub>n \<phi>{z\<^sub>1...z\<^sub>n}]\<down>] \<longrightarrow> [v \<Turnstile> \<guillemotleft>AOT_proj_enc \<kappa>\<^sub>1\<kappa>\<^sub>n \<phi>\<guillemotright>])\<close>

(* TODO: unfortunate that this is not in AOT_syntax *)
AOT_syntax_print_translations
  "_AOT_enc (_AOT_individual_term \<kappa>) (_AOT_relation_term \<Pi>)" <= "CONST AOT_enc \<kappa> \<Pi>"

context AOT_meta_syntax
begin
notation AOT_enc ("\<^bold>\<lbrace>_,_\<^bold>\<rbrace>")
end
context AOT_no_meta_syntax
begin
no_notation AOT_enc ("\<^bold>\<lbrace>_,_\<^bold>\<rbrace>")
end

class AOT_UnaryEnc = AOT_UnaryIndividualTerm +
  assumes AOT_sem_enc_eq: \<open>[v \<Turnstile> \<Pi>\<down> & \<Pi>'\<down> & \<box>\<forall>\<nu> (\<nu>[\<Pi>] \<equiv> \<nu>[\<Pi>']) \<rightarrow> \<Pi> = \<Pi>']\<close>
      and AOT_sem_A_objects: \<open>[v \<Turnstile> \<exists>x (\<not>\<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x & \<forall>F (x[F] \<equiv> \<phi>{F}))]\<close>
      and AOT_sem_unary_proj_enc: \<open>AOT_proj_enc x \<psi> = AOT_enc x \<guillemotleft>[\<lambda>z \<psi>{z}]\<guillemotright>\<close>
      and AOT_sem_nocoder: \<open>[v \<Turnstile> [\<guillemotleft>AOT_sem_concrete\<guillemotright>]\<kappa>] \<Longrightarrow> \<not>[w \<Turnstile> \<guillemotleft>AOT_enc \<kappa> \<Pi>\<guillemotright>]\<close>
      and AOT_sem_ind_eq: \<open>([v \<Turnstile> \<kappa>\<down>] \<and> [v \<Turnstile> \<kappa>'\<down>] \<and> \<kappa> = \<kappa>') =
       (([v \<Turnstile> [\<lambda>x \<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>] \<and>
         [v \<Turnstile> [\<lambda>x \<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>'] \<and>
         (\<forall> v \<Pi> . [v \<Turnstile> \<Pi>\<down>] \<longrightarrow> [v \<Turnstile> [\<Pi>]\<kappa>] = [v \<Turnstile> [\<Pi>]\<kappa>']))
        \<or> ([v \<Turnstile> [\<lambda>x \<not>\<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>] \<and>
           [v \<Turnstile> [\<lambda>x \<not>\<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>'] \<and>
           (\<forall> v \<Pi> . [v \<Turnstile> \<Pi>\<down>] \<longrightarrow> [v \<Turnstile> \<kappa>[\<Pi>]] = [v \<Turnstile> \<kappa>'[\<Pi>]])))\<close>

      (* only extended models *)
      and AOT_sem_enc_indistinguishable_all:
          \<open>AOT_ExtendedModel \<Longrightarrow>
           [v \<Turnstile> [\<lambda>x \<not>\<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>] \<Longrightarrow>
           [v \<Turnstile> [\<lambda>x \<not>\<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>'] \<Longrightarrow>
           (\<And> \<Pi>' . [v \<Turnstile> \<Pi>'\<down>] \<Longrightarrow> (\<And> w . [w \<Turnstile> [\<Pi>']\<kappa>] = [w \<Turnstile> [\<Pi>']\<kappa>'])) \<Longrightarrow>
           [v \<Turnstile> \<Pi>\<down>] \<Longrightarrow>
           (\<And> \<Pi>' . [v \<Turnstile> \<Pi>'\<down>] \<Longrightarrow> (\<And> \<kappa>\<^sub>0 . [v \<Turnstile> [\<lambda>x \<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>\<^sub>0] \<Longrightarrow>
              (\<And> w . [w \<Turnstile> [\<Pi>']\<kappa>\<^sub>0] = [w \<Turnstile> [\<Pi>]\<kappa>\<^sub>0])) \<Longrightarrow> [v \<Turnstile> \<kappa>[\<Pi>']]) \<Longrightarrow>
           (\<And> \<Pi>' . [v \<Turnstile> \<Pi>'\<down>] \<Longrightarrow> (\<And> \<kappa>\<^sub>0 . [v \<Turnstile> [\<lambda>x \<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>\<^sub>0] \<Longrightarrow>
              (\<And> w . [w \<Turnstile> [\<Pi>']\<kappa>\<^sub>0] = [w \<Turnstile> [\<Pi>]\<kappa>\<^sub>0])) \<Longrightarrow> [v \<Turnstile> \<kappa>'[\<Pi>']])\<close>
      and AOT_sem_enc_indistinguishable_ex:
          \<open>AOT_ExtendedModel \<Longrightarrow>
           [v \<Turnstile> [\<lambda>x \<not>\<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>] \<Longrightarrow>
           [v \<Turnstile> [\<lambda>x \<not>\<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>'] \<Longrightarrow>
           (\<And> \<Pi>' . [v \<Turnstile> \<Pi>'\<down>] \<Longrightarrow> (\<And> w . [w \<Turnstile> [\<Pi>']\<kappa>] = [w \<Turnstile> [\<Pi>']\<kappa>'])) \<Longrightarrow>
           [v \<Turnstile> \<Pi>\<down>] \<Longrightarrow>
           \<exists> \<Pi>' . [v \<Turnstile> \<Pi>'\<down>] \<and> [v \<Turnstile> \<kappa>[\<Pi>']] \<and>
                  (\<forall> \<kappa>\<^sub>0 . [v \<Turnstile> [\<lambda>x \<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>\<^sub>0] \<longrightarrow>
                          (\<forall> w . [w \<Turnstile> [\<Pi>']\<kappa>\<^sub>0] = [w \<Turnstile> [\<Pi>]\<kappa>\<^sub>0])) \<Longrightarrow>
           \<exists> \<Pi>' . [v \<Turnstile> \<Pi>'\<down>] \<and> [v \<Turnstile> \<kappa>'[\<Pi>']] \<and>
                  (\<forall> \<kappa>\<^sub>0 . [v \<Turnstile> [\<lambda>x \<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>\<^sub>0] \<longrightarrow>
                          (\<forall> w . [w \<Turnstile> [\<Pi>']\<kappa>\<^sub>0] = [w \<Turnstile> [\<Pi>]\<kappa>\<^sub>0]))\<close>
instantiation \<kappa> :: AOT_Enc
begin
definition AOT_enc_\<kappa> :: \<open>\<kappa> \<Rightarrow> <\<kappa>> \<Rightarrow> \<o>\<close> where
  \<open>AOT_enc_\<kappa> \<equiv> SOME \<phi> . \<forall> v \<kappa> \<Pi> . [v \<Turnstile> \<guillemotleft>\<phi> \<kappa> \<Pi>\<guillemotright>] =
                                   (AOT_model_denotes \<Pi> \<and> AOT_model_enc \<kappa> \<Pi>)\<close>
definition AOT_proj_enc_\<kappa> :: \<open>\<kappa> \<Rightarrow> (\<kappa> \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close> where
  \<open>AOT_proj_enc_\<kappa> \<equiv> \<lambda> \<kappa> \<phi> . AOT_enc \<kappa> \<guillemotleft>[\<lambda>z \<guillemotleft>\<phi> z\<guillemotright>]\<guillemotright>\<close>
lemma AOT_enc_\<kappa>_meta:
  \<open>[v \<Turnstile> \<kappa>[\<Pi>]] = (AOT_model_denotes \<kappa> \<and> AOT_model_denotes \<Pi> \<and> AOT_model_enc \<kappa> \<Pi>)\<close>
  for \<kappa>::\<kappa>
proof -
  have AOT_enc_\<kappa>_ex:
    \<open>\<exists> \<phi> . \<forall> v (\<kappa>::\<kappa>) \<Pi> . [v \<Turnstile> \<guillemotleft>\<phi> \<kappa> \<Pi>\<guillemotright>] =
                           (AOT_model_denotes \<Pi> \<and> AOT_model_enc \<kappa> \<Pi>)\<close>
    by (rule exI[where x=\<open>\<lambda> \<kappa> \<Pi> . \<epsilon>\<^sub>\<o> w . AOT_model_enc \<kappa> \<Pi>\<close>])
       (simp add: AOT_model_proposition_choice_simp
                  AOT_model_enc_\<kappa>_def \<kappa>.case_eq_if)
  show ?thesis
    using someI_ex[OF AOT_enc_\<kappa>_ex] unfolding AOT_enc_\<kappa>_def
    by (simp add: AOT_model_denotes_\<kappa>_def AOT_model_enc_\<kappa>_def
                  \<kappa>.case_eq_if \<kappa>.distinct_disc(5))
qed
instance proof
  fix v and \<kappa> :: \<kappa> and \<Pi>
  show \<open>[v \<Turnstile> \<guillemotleft>AOT_enc \<kappa> \<Pi>\<guillemotright>] \<Longrightarrow> [v \<Turnstile> \<kappa>\<down>] \<and> [v \<Turnstile> \<Pi>\<down>]\<close>
    unfolding AOT_sem_denotes
    using AOT_enc_\<kappa>_meta by blast
next
  fix v and \<kappa> :: \<kappa> and \<Pi>
  show \<open>[v \<Turnstile> \<kappa>[\<Pi>]] = [v \<Turnstile> \<Pi>\<down> & \<guillemotleft>AOT_proj_enc \<kappa> (\<lambda> \<kappa>'.  \<guillemotleft>[\<Pi>]\<kappa>'\<guillemotright>)\<guillemotright>]\<close>
  proof
    assume enc: \<open>[v \<Turnstile> \<kappa>[\<Pi>]]\<close>
    hence \<Pi>_denotes: \<open>AOT_model_denotes \<Pi>\<close>
      by (simp add: AOT_enc_\<kappa>_meta)
    hence \<Pi>_eta_denotes: \<open>AOT_model_denotes \<guillemotleft>[\<lambda>z [\<Pi>]z]\<guillemotright>\<close>
      using AOT_sem_denotes AOT_sem_eq AOT_sem_lambda_eta by metis
    show \<open>[v \<Turnstile> \<Pi>\<down> & \<guillemotleft>AOT_proj_enc \<kappa> (\<lambda> \<kappa>.  \<guillemotleft>[\<Pi>]\<kappa>\<guillemotright>)\<guillemotright>]\<close>
      using AOT_sem_lambda_eta[simplified AOT_sem_denotes AOT_sem_eq, OF \<Pi>_denotes]
      using \<Pi>_eta_denotes \<Pi>_denotes
      by (simp add: AOT_sem_conj AOT_sem_denotes AOT_proj_enc_\<kappa>_def enc)
  next
    assume \<open>[v \<Turnstile> \<Pi>\<down> & \<guillemotleft>AOT_proj_enc \<kappa> (\<lambda> \<kappa>.  \<guillemotleft>[\<Pi>]\<kappa>\<guillemotright>)\<guillemotright>]\<close>
    hence \<Pi>_denotes: "AOT_model_denotes \<Pi>" and eta_enc: "[v \<Turnstile> \<kappa>[\<lambda>z [\<Pi>]z]]" 
      by (auto simp: AOT_sem_conj AOT_sem_denotes AOT_proj_enc_\<kappa>_def)
    thus \<open>[v \<Turnstile> \<kappa>[\<Pi>]]\<close>
      using AOT_sem_lambda_eta[simplified AOT_sem_denotes AOT_sem_eq, OF \<Pi>_denotes]
      by auto
  qed
next
  show \<open>[v \<Turnstile> \<guillemotleft>AOT_proj_enc \<kappa> \<phi>\<guillemotright>] \<Longrightarrow> [v \<Turnstile> \<kappa>\<down>]\<close> for v and \<kappa> :: \<kappa> and \<phi>
    by (simp add: AOT_enc_\<kappa>_meta AOT_sem_denotes AOT_proj_enc_\<kappa>_def)
next
  fix v w and \<kappa> :: \<kappa> and \<Pi>
  assume \<open>[v \<Turnstile> \<kappa>[\<Pi>]]\<close>
  thus \<open>[w \<Turnstile> \<kappa>[\<Pi>]]\<close>
    by (simp add: AOT_enc_\<kappa>_meta)
next
  fix v w and \<kappa> :: \<kappa> and \<phi>
  assume \<open>[v \<Turnstile> \<guillemotleft>AOT_proj_enc \<kappa> \<phi>\<guillemotright>]\<close>
  thus \<open>[w \<Turnstile> \<guillemotleft>AOT_proj_enc \<kappa> \<phi>\<guillemotright>]\<close>
    by (simp add: AOT_enc_\<kappa>_meta AOT_proj_enc_\<kappa>_def)
next
  show \<open>\<exists>\<kappa>::\<kappa>. [v \<Turnstile> \<kappa>\<down>] \<and> (\<forall> \<Pi> . [v \<Turnstile> \<Pi>\<down>] \<longrightarrow>  [v \<Turnstile> \<kappa>[\<Pi>]]) \<and>
               (\<forall> \<phi> . [v \<Turnstile> [\<lambda>z \<phi>{z}]\<down>] \<longrightarrow>  [v \<Turnstile> \<guillemotleft>AOT_proj_enc \<kappa> \<phi>\<guillemotright>])\<close> for v
    by (rule exI[where x=\<open>\<alpha>\<kappa> UNIV\<close>])
       (simp add: AOT_sem_denotes AOT_enc_\<kappa>_meta AOT_model_enc_\<kappa>_def
                  AOT_model_denotes_\<kappa>_def  AOT_proj_enc_\<kappa>_def)
qed
end

instantiation \<kappa> :: AOT_UnaryEnc
begin
instance proof
  fix v and \<Pi> \<Pi>' :: \<open><\<kappa>>\<close>
  show \<open>[v \<Turnstile> \<Pi>\<down> & \<Pi>'\<down> & \<box>\<forall>\<nu> (\<nu>[\<Pi>] \<equiv> \<nu>[\<Pi>']) \<rightarrow> \<Pi> = \<Pi>']\<close>
    apply (simp add: AOT_sem_forall AOT_sem_eq AOT_sem_imp AOT_sem_equiv
                     AOT_enc_\<kappa>_meta AOT_sem_conj AOT_sem_denotes AOT_sem_box)
    using AOT_meta_A_objects_\<kappa> by fastforce
next
  fix v and \<phi>:: \<open><\<kappa>> \<Rightarrow> \<o>\<close>
  show \<open>[v \<Turnstile> \<exists>x (\<not>\<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x & \<forall>F (x[F] \<equiv> \<phi>{F}))]\<close>
    using AOT_model_A_objects[of "\<lambda> \<Pi> . [v \<Turnstile> \<phi>{\<Pi>}]"]
    by (auto simp: AOT_sem_denotes AOT_sem_exists AOT_sem_conj AOT_sem_not
                   AOT_sem_dia AOT_sem_concrete AOT_enc_\<kappa>_meta AOT_sem_equiv
                   AOT_sem_forall)
next
  show \<open>AOT_proj_enc x \<psi> = AOT_enc x (AOT_lambda \<psi>)\<close> for x :: \<kappa> and \<psi>
    by (simp add: AOT_proj_enc_\<kappa>_def)
next
  show \<open>[v \<Turnstile> [\<guillemotleft>AOT_sem_concrete\<guillemotright>]\<kappa>] \<Longrightarrow> \<not> [w \<Turnstile> \<kappa>[\<Pi>]]\<close> for v w and \<kappa> :: \<kappa> and \<Pi>
    by (simp add: AOT_enc_\<kappa>_meta AOT_sem_concrete AOT_model_nocoder)
next
  fix v and \<kappa> \<kappa>' :: \<kappa>
  show \<open>([v \<Turnstile> \<kappa>\<down>] \<and> [v \<Turnstile> \<kappa>'\<down>] \<and> \<kappa> = \<kappa>') =
         (([v \<Turnstile> [\<lambda>x \<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>] \<and>
           [v \<Turnstile> [\<lambda>x \<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>'] \<and>
           (\<forall> v \<Pi> . [v \<Turnstile> \<Pi>\<down>] \<longrightarrow> [v \<Turnstile> [\<Pi>]\<kappa>] = [v \<Turnstile> [\<Pi>]\<kappa>']))
          \<or> ([v \<Turnstile> [\<lambda>x \<not>\<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>] \<and>
             [v \<Turnstile> [\<lambda>x \<not>\<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>'] \<and>
             (\<forall> v \<Pi> . [v \<Turnstile> \<Pi>\<down>] \<longrightarrow> [v \<Turnstile> \<kappa>[\<Pi>]] = [v \<Turnstile> \<kappa>'[\<Pi>]])))\<close>
    (is \<open>?lhs = (?ordeq \<or> ?abseq)\<close>)
  proof -
  {
    assume 0: \<open>[v \<Turnstile> \<kappa>\<down>] \<and> [v \<Turnstile> \<kappa>'\<down>] \<and> \<kappa> = \<kappa>'\<close>
    {
      assume \<open>is_\<omega>\<kappa> \<kappa>'\<close>
      hence \<open>[v \<Turnstile> [\<lambda>x \<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>']\<close>
        apply (subst AOT_sem_lambda_beta[OF AOT_sem_ordinary_def_denotes, of v \<kappa>'])
         apply (simp add: "0")
        apply (simp add: AOT_sem_dia)
        using AOT_sem_concrete AOT_model_\<omega>_concrete_in_some_world is_\<omega>\<kappa>_def by force
      hence \<open>?ordeq\<close> unfolding 0[THEN conjunct2, THEN conjunct2] by auto
    }
    moreover {
      assume \<open>is_\<alpha>\<kappa> \<kappa>'\<close>
      hence \<open>[v \<Turnstile> [\<lambda>x \<not>\<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>']\<close>
        apply (subst AOT_sem_lambda_beta[OF AOT_sem_abstract_def_denotes, of v \<kappa>'])
         apply (simp add: "0")
        apply (simp add: AOT_sem_not AOT_sem_dia)
        using AOT_sem_concrete is_\<alpha>\<kappa>_def by force
      hence \<open>?abseq\<close> unfolding 0[THEN conjunct2, THEN conjunct2] by auto
    }
    ultimately have \<open>?ordeq \<or> ?abseq\<close>
      by (meson "0" AOT_sem_denotes AOT_model_denotes_\<kappa>_def \<kappa>.exhaust_disc)
  }
  moreover {
    assume ordeq: \<open>?ordeq\<close>
    hence \<kappa>_denotes: \<open>[v \<Turnstile> \<kappa>\<down>]\<close> and \<kappa>'_denotes: \<open>[v \<Turnstile> \<kappa>'\<down>]\<close> 
      by (simp add: AOT_sem_denotes AOT_sem_exe)+
    hence \<open>is_\<omega>\<kappa> \<kappa>\<close> and \<open>is_\<omega>\<kappa> \<kappa>'\<close>
      by (metis AOT_model_concrete_\<kappa>.simps(2) AOT_model_denotes_\<kappa>_def
                AOT_sem_concrete AOT_sem_denotes AOT_sem_dia AOT_sem_lambda_beta
                AOT_sem_ordinary_def_denotes \<kappa>.collapse(2) \<kappa>.exhaust_disc ordeq)+
    have denotes: \<open>[v \<Turnstile> [\<lambda>z \<guillemotleft>\<epsilon>\<^sub>\<o> w . \<kappa>\<upsilon> z = \<kappa>\<upsilon> \<kappa>\<guillemotright>]\<down>]\<close>
      unfolding AOT_sem_denotes AOT_model_lambda_denotes
      by (simp add: AOT_model_term_equiv_\<kappa>_def)
    hence "[v \<Turnstile> [\<lambda>z \<guillemotleft>\<epsilon>\<^sub>\<o> w . \<kappa>\<upsilon> z = \<kappa>\<upsilon> \<kappa>\<guillemotright>]\<kappa>] = [v \<Turnstile> [\<lambda>z \<guillemotleft>\<epsilon>\<^sub>\<o> w . \<kappa>\<upsilon> z = \<kappa>\<upsilon> \<kappa>\<guillemotright>]\<kappa>']"
      using ordeq by (simp add: AOT_sem_denotes)
    hence \<open>[v \<Turnstile> \<guillemotleft>\<kappa>\<guillemotright>\<down>] \<and> [v \<Turnstile> \<guillemotleft>\<kappa>'\<guillemotright>\<down>] \<and> \<kappa> = \<kappa>'\<close>
      unfolding AOT_sem_lambda_beta[OF denotes, OF \<kappa>_denotes]
                AOT_sem_lambda_beta[OF denotes, OF \<kappa>'_denotes]
      using \<kappa>'_denotes \<open>is_\<omega>\<kappa> \<kappa>'\<close> \<open>is_\<omega>\<kappa> \<kappa>\<close> is_\<omega>\<kappa>_def
            AOT_model_proposition_choice_simp by force
  }
  moreover {
    assume 0: \<open>?abseq\<close>
    hence \<kappa>_denotes: \<open>[v \<Turnstile> \<kappa>\<down>]\<close> and \<kappa>'_denotes: \<open>[v \<Turnstile> \<kappa>'\<down>]\<close> 
      by (simp add: AOT_sem_denotes AOT_sem_exe)+
    hence \<open>\<not>is_\<omega>\<kappa> \<kappa>\<close> and \<open>\<not>is_\<omega>\<kappa> \<kappa>'\<close>
      by (metis AOT_model_\<omega>_concrete_in_some_world AOT_model_concrete_\<kappa>.simps(1)
                AOT_sem_concrete AOT_sem_dia AOT_sem_exe AOT_sem_lambda_beta
                AOT_sem_not \<kappa>.collapse(1) 0)+
    hence \<open>is_\<alpha>\<kappa> \<kappa>\<close> and \<open>is_\<alpha>\<kappa> \<kappa>'\<close>
      by (meson AOT_sem_denotes AOT_model_denotes_\<kappa>_def \<kappa>.exhaust_disc
                \<kappa>_denotes \<kappa>'_denotes)+
    then obtain x y where \<kappa>_def: \<open>\<kappa> = \<alpha>\<kappa> x\<close> and \<kappa>'_def: \<open>\<kappa>' = \<alpha>\<kappa> y\<close>
      using is_\<alpha>\<kappa>_def by auto
    {
      fix r
      assume \<open>r \<in> x\<close>
      hence \<open>[v \<Turnstile> \<kappa>[\<guillemotleft>urrel_to_rel r\<guillemotright>]]\<close>
        unfolding \<kappa>_def
        unfolding AOT_enc_\<kappa>_meta
        unfolding AOT_model_enc_\<kappa>_def
        apply (simp add: AOT_model_denotes_\<kappa>_def)
        by (metis (mono_tags) AOT_rel_equiv_def Quotient_def urrel_quotient)
      hence \<open>[v \<Turnstile> \<kappa>'[\<guillemotleft>urrel_to_rel r\<guillemotright>]]\<close>
        using AOT_enc_\<kappa>_meta 0 by (metis AOT_sem_enc_denotes)
      hence \<open>r \<in> y\<close>
        unfolding \<kappa>'_def
        unfolding AOT_enc_\<kappa>_meta
        unfolding AOT_model_enc_\<kappa>_def
        apply (simp add: AOT_model_denotes_\<kappa>_def)
        using Quotient_abs_rep urrel_quotient by fastforce
    }
    moreover {
      fix r
      assume \<open>r \<in> y\<close>
      hence \<open>[v \<Turnstile> \<kappa>'[\<guillemotleft>urrel_to_rel r\<guillemotright>]]\<close>
        unfolding \<kappa>'_def
        unfolding AOT_enc_\<kappa>_meta
        unfolding AOT_model_enc_\<kappa>_def
        apply (simp add: AOT_model_denotes_\<kappa>_def)
        by (metis (mono_tags) AOT_rel_equiv_def Quotient_def urrel_quotient)
      hence \<open>[v \<Turnstile> \<kappa>[\<guillemotleft>urrel_to_rel r\<guillemotright>]]\<close>
        using AOT_enc_\<kappa>_meta 0 by (metis AOT_sem_enc_denotes)
      hence \<open>r \<in> x\<close>
        unfolding \<kappa>_def
        unfolding AOT_enc_\<kappa>_meta
        unfolding AOT_model_enc_\<kappa>_def
        apply (simp add: AOT_model_denotes_\<kappa>_def)
        using Quotient_abs_rep urrel_quotient by fastforce
    }
    ultimately have "x = y" by blast
    hence \<open>[v \<Turnstile> \<kappa>\<down>] \<and> [v \<Turnstile> \<kappa>'\<down>] \<and> \<kappa> = \<kappa>'\<close>
      using \<kappa>'_def \<kappa>'_denotes \<kappa>_def by blast
  }
  ultimately show ?thesis
    unfolding AOT_sem_denotes
    by auto
  qed
(* Only extended model *)
next
  fix v and \<kappa> \<kappa>' :: \<kappa> and \<Pi> \<Pi>' :: \<open><\<kappa>>\<close>
  assume ext: \<open>AOT_ExtendedModel\<close>
  assume \<open>[v \<Turnstile> [\<lambda>x \<not>\<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>]\<close>
  hence \<open>is_\<alpha>\<kappa> \<kappa>\<close>
    by (metis AOT_model_\<omega>_concrete_in_some_world AOT_model_concrete_\<kappa>.simps(1)
              AOT_model_denotes_\<kappa>_def AOT_sem_concrete AOT_sem_denotes AOT_sem_dia
              AOT_sem_exe AOT_sem_lambda_beta AOT_sem_not \<kappa>.collapse(1) \<kappa>.exhaust_disc)
  hence \<kappa>_abs: \<open>\<not>(\<exists> w . AOT_model_concrete w \<kappa>)\<close>
    using is_\<alpha>\<kappa>_def by fastforce
  have \<kappa>_den: \<open>AOT_model_denotes \<kappa>\<close>
    by (simp add: AOT_model_denotes_\<kappa>_def \<kappa>.distinct_disc(5) \<open>is_\<alpha>\<kappa> \<kappa>\<close>)
  assume \<open>[v \<Turnstile> [\<lambda>x \<not>\<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>']\<close>
  hence \<open>is_\<alpha>\<kappa> \<kappa>'\<close>
    by (metis AOT_model_\<omega>_concrete_in_some_world AOT_model_concrete_\<kappa>.simps(1)
              AOT_model_denotes_\<kappa>_def AOT_sem_concrete AOT_sem_denotes AOT_sem_dia
              AOT_sem_exe AOT_sem_lambda_beta AOT_sem_not \<kappa>.collapse(1)
              \<kappa>.exhaust_disc)
  hence \<kappa>'_abs: \<open>\<not>(\<exists> w . AOT_model_concrete w \<kappa>')\<close>
    using is_\<alpha>\<kappa>_def by fastforce
  have \<kappa>'_den: \<open>AOT_model_denotes \<kappa>'\<close>
    by (meson AOT_model_denotes_\<kappa>_def \<kappa>.distinct_disc(6) \<open>is_\<alpha>\<kappa> \<kappa>'\<close>)
  assume \<open>[v \<Turnstile> \<Pi>'\<down>] \<Longrightarrow> [w \<Turnstile> [\<Pi>']\<kappa>] = [w \<Turnstile> [\<Pi>']\<kappa>']\<close> for \<Pi>' w
  hence indist: \<open>[v \<Turnstile> \<guillemotleft>Rep_rel \<Pi>' \<kappa>\<guillemotright>] = [v \<Turnstile> \<guillemotleft>Rep_rel \<Pi>' \<kappa>'\<guillemotright>]\<close>
    if \<open>AOT_model_denotes \<Pi>'\<close> for \<Pi>' v
    by (simp add: that AOT_sem_denotes AOT_sem_exe_denoting)
  assume \<kappa>_enc_cond: \<open>[v \<Turnstile> \<Pi>'\<down>] \<Longrightarrow>
    (\<And> \<kappa>\<^sub>0 w. [v \<Turnstile> [\<lambda>x \<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>\<^sub>0] \<Longrightarrow>
             [w \<Turnstile> [\<Pi>']\<kappa>\<^sub>0] = [w \<Turnstile> [\<Pi>]\<kappa>\<^sub>0]) \<Longrightarrow>
    [v \<Turnstile> \<kappa>[\<Pi>']]\<close> for \<Pi>'
  assume \<Pi>_den': \<open>[v \<Turnstile> \<Pi>\<down>]\<close>
  hence \<Pi>_den: \<open>AOT_model_denotes \<Pi>\<close>
    using AOT_sem_denotes by blast
  {
    fix \<Pi>' :: \<open><\<kappa>>\<close>
    assume \<Pi>'_den: \<open>AOT_model_denotes \<Pi>'\<close>
    hence \<Pi>'_den': \<open>[v \<Turnstile> \<Pi>'\<down>]\<close>
      by (simp add: AOT_sem_denotes)
    assume 1: \<open>\<exists>w. AOT_model_concrete w x \<Longrightarrow>
               [v \<Turnstile> \<guillemotleft>Rep_rel \<Pi>' x\<guillemotright>] = [v \<Turnstile> \<guillemotleft>Rep_rel \<Pi> x\<guillemotright>]\<close> for v x
    {
      fix \<kappa>\<^sub>0 :: \<kappa> and w
      assume \<open>[v \<Turnstile> [\<lambda>x \<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>\<^sub>0]\<close>
      hence \<open>is_\<omega>\<kappa> \<kappa>\<^sub>0\<close>
        by (smt (z3) AOT_model_concrete_\<kappa>.simps(2) AOT_model_denotes_\<kappa>_def
                     AOT_sem_concrete AOT_sem_denotes AOT_sem_dia AOT_sem_exe
                     AOT_sem_lambda_beta \<kappa>.exhaust_disc is_\<alpha>\<kappa>_def)
      then obtain x where x_prop: \<open>\<kappa>\<^sub>0 = \<omega>\<kappa> x\<close>
        using is_\<omega>\<kappa>_def by blast
      have \<open>\<exists>w . AOT_model_concrete w (\<omega>\<kappa> x)\<close>
        by (simp add: AOT_model_\<omega>_concrete_in_some_world)
      hence \<open>[v \<Turnstile> \<guillemotleft>Rep_rel \<Pi>' (\<omega>\<kappa> x)\<guillemotright>] = [v \<Turnstile> \<guillemotleft>Rep_rel \<Pi> (\<omega>\<kappa> x)\<guillemotright>]\<close> for v
        using 1 by blast
      hence \<open>[w \<Turnstile> [\<Pi>']\<kappa>\<^sub>0] = [w \<Turnstile> [\<Pi>]\<kappa>\<^sub>0]\<close> unfolding x_prop
        by (simp add: AOT_sem_exe AOT_sem_denotes AOT_model_denotes_\<kappa>_def
                      \<Pi>'_den \<Pi>_den)
    } note 2 = this
    have \<open>[v \<Turnstile> \<kappa>[\<Pi>']]\<close>
      using \<kappa>_enc_cond[OF \<Pi>'_den', OF 2]
      by metis
    hence \<open>AOT_model_enc \<kappa> \<Pi>'\<close>
      using AOT_enc_\<kappa>_meta by blast
  } note \<kappa>_enc_cond = this
  hence \<open>AOT_model_denotes \<Pi>' \<Longrightarrow>
       (\<And>v x. \<exists>w. AOT_model_concrete w x \<Longrightarrow>
              [v \<Turnstile> \<guillemotleft>Rep_rel \<Pi>' x\<guillemotright>] = [v \<Turnstile> \<guillemotleft>Rep_rel \<Pi> x\<guillemotright>]) \<Longrightarrow>
       AOT_model_enc \<kappa> \<Pi>'\<close> for \<Pi>'
    by blast
  assume \<Pi>'_den': \<open>[v \<Turnstile> \<Pi>'\<down>]\<close>
  hence \<Pi>'_den: \<open>AOT_model_denotes \<Pi>'\<close>
    using AOT_sem_denotes by blast
  assume ord_indist: \<open>[v \<Turnstile> [\<lambda>x \<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>\<^sub>0] \<Longrightarrow>
                      [w \<Turnstile> [\<Pi>']\<kappa>\<^sub>0] = [w \<Turnstile> [\<Pi>]\<kappa>\<^sub>0]\<close> for \<kappa>\<^sub>0 w
  {
    fix w and \<kappa>\<^sub>0 :: \<kappa>
    assume \<open>\<exists>w. AOT_model_concrete w \<kappa>\<^sub>0\<close>
    hence \<open>[v \<Turnstile> [\<lambda>x \<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>\<^sub>0]\<close>
      using AOT_model_concrete_denotes AOT_sem_concrete AOT_sem_denotes AOT_sem_dia
            AOT_sem_lambda_beta AOT_sem_ordinary_def_denotes by blast
    hence \<open>[w \<Turnstile> [\<Pi>']\<kappa>\<^sub>0] = [w \<Turnstile> [\<Pi>]\<kappa>\<^sub>0]\<close>
      using ord_indist by metis 
    hence \<open>[w \<Turnstile> \<guillemotleft>Rep_rel \<Pi>' \<kappa>\<^sub>0\<guillemotright>] = [w \<Turnstile> \<guillemotleft>Rep_rel \<Pi> \<kappa>\<^sub>0\<guillemotright>]\<close>
      by (metis AOT_sem_exe_denoting \<Pi>'_den' \<Pi>_den')
  } note ord_indist = this
  have \<open>AOT_model_enc \<kappa>' \<Pi>'\<close>
    using AOT_model_enc_indistinguishable_all
            [OF ext, OF \<kappa>_den, OF \<kappa>_abs, OF \<kappa>'_den, OF \<kappa>'_abs, OF \<Pi>_den]
          indist \<kappa>_enc_cond \<Pi>'_den ord_indist by blast
  thus \<open>[v \<Turnstile> \<kappa>'[\<Pi>']]\<close>
    using AOT_enc_\<kappa>_meta \<Pi>'_den \<kappa>'_den by blast
next
  fix v and \<kappa> \<kappa>' :: \<kappa> and \<Pi> \<Pi>' :: \<open><\<kappa>>\<close>
  assume ext: \<open>AOT_ExtendedModel\<close>
  assume \<open>[v \<Turnstile> [\<lambda>x \<not>\<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>]\<close>
  hence \<open>is_\<alpha>\<kappa> \<kappa>\<close>
    by (metis AOT_model_\<omega>_concrete_in_some_world AOT_model_concrete_\<kappa>.simps(1)
              AOT_model_denotes_\<kappa>_def AOT_sem_concrete AOT_sem_denotes AOT_sem_dia
              AOT_sem_exe AOT_sem_lambda_beta AOT_sem_not \<kappa>.collapse(1)
              \<kappa>.exhaust_disc)
  hence \<kappa>_abs: \<open>\<not>(\<exists> w . AOT_model_concrete w \<kappa>)\<close>
    using is_\<alpha>\<kappa>_def by fastforce
  have \<kappa>_den: \<open>AOT_model_denotes \<kappa>\<close>
    by (simp add: AOT_model_denotes_\<kappa>_def \<kappa>.distinct_disc(5) \<open>is_\<alpha>\<kappa> \<kappa>\<close>)
  assume \<open>[v \<Turnstile> [\<lambda>x \<not>\<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>']\<close>
  hence \<open>is_\<alpha>\<kappa> \<kappa>'\<close>
    by (metis AOT_model_\<omega>_concrete_in_some_world AOT_model_concrete_\<kappa>.simps(1)
              AOT_model_denotes_\<kappa>_def AOT_sem_concrete AOT_sem_denotes AOT_sem_dia
              AOT_sem_exe AOT_sem_lambda_beta AOT_sem_not \<kappa>.collapse(1)
              \<kappa>.exhaust_disc)
  hence \<kappa>'_abs: \<open>\<not>(\<exists> w . AOT_model_concrete w \<kappa>')\<close>
    using is_\<alpha>\<kappa>_def by fastforce
  have \<kappa>'_den: \<open>AOT_model_denotes \<kappa>'\<close>
    by (meson AOT_model_denotes_\<kappa>_def \<kappa>.distinct_disc(6) \<open>is_\<alpha>\<kappa> \<kappa>'\<close>)
  assume \<open>[v \<Turnstile> \<Pi>'\<down>] \<Longrightarrow> [w \<Turnstile> [\<Pi>']\<kappa>] = [w \<Turnstile> [\<Pi>']\<kappa>']\<close> for \<Pi>' w
  hence indist: \<open>[v \<Turnstile> \<guillemotleft>Rep_rel \<Pi>' \<kappa>\<guillemotright>] = [v \<Turnstile> \<guillemotleft>Rep_rel \<Pi>' \<kappa>'\<guillemotright>]\<close>
    if \<open>AOT_model_denotes \<Pi>'\<close> for \<Pi>' v
    by (simp add: that AOT_sem_denotes AOT_sem_exe_denoting)
  assume \<Pi>_den': \<open>[v \<Turnstile> \<Pi>\<down>]\<close>
  hence \<Pi>_den: \<open>AOT_model_denotes \<Pi>\<close>
    using AOT_sem_denotes by blast
  assume \<open>\<exists>\<Pi>'. [v \<Turnstile> \<Pi>'\<down>] \<and> [v \<Turnstile> \<kappa>[\<Pi>']] \<and>
               (\<forall>\<kappa>\<^sub>0. [v \<Turnstile> [\<lambda>x \<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>\<^sub>0] \<longrightarrow>
                     (\<forall>w. [w \<Turnstile> [\<Pi>']\<kappa>\<^sub>0] = [w \<Turnstile> [\<Pi>]\<kappa>\<^sub>0]))\<close>
  then obtain \<Pi>' where
      \<Pi>'_den: \<open>[v \<Turnstile> \<Pi>'\<down>]\<close> and
      \<Pi>'_enc: \<open>[v \<Turnstile> \<kappa>[\<Pi>']]\<close> and
      \<Pi>'_prop: \<open>\<forall>\<kappa>\<^sub>0. [v \<Turnstile> [\<lambda>x \<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>\<^sub>0] \<longrightarrow>
                     (\<forall>w. [w \<Turnstile> [\<Pi>']\<kappa>\<^sub>0] = [w \<Turnstile> [\<Pi>]\<kappa>\<^sub>0])\<close>
    by blast
  have \<open>AOT_model_denotes \<Pi>'\<close>
    using AOT_enc_\<kappa>_meta \<Pi>'_enc by force
  moreover have \<open>AOT_model_enc \<kappa> \<Pi>'\<close>
    using AOT_enc_\<kappa>_meta \<Pi>'_enc by blast
  moreover have \<open>(\<exists>w. AOT_model_concrete w \<kappa>\<^sub>0) \<Longrightarrow>
                 [v \<Turnstile> \<guillemotleft>Rep_rel \<Pi>' \<kappa>\<^sub>0\<guillemotright>] = [v \<Turnstile> \<guillemotleft>Rep_rel \<Pi> \<kappa>\<^sub>0\<guillemotright>]\<close> for \<kappa>\<^sub>0 v
  proof -
    assume \<open>(\<exists>w. AOT_model_concrete w \<kappa>\<^sub>0)\<close>
    hence \<open>[v \<Turnstile> [\<lambda>x \<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>\<^sub>0]\<close> for v
      using AOT_model_concrete_denotes AOT_sem_concrete AOT_sem_denotes AOT_sem_dia
            AOT_sem_lambda_beta AOT_sem_ordinary_def_denotes by blast
    hence \<open>\<forall>w. [w \<Turnstile> [\<Pi>']\<kappa>\<^sub>0] = [w \<Turnstile> [\<Pi>]\<kappa>\<^sub>0]\<close> using \<Pi>'_prop by blast
    thus \<open>[v \<Turnstile> \<guillemotleft>Rep_rel \<Pi>' \<kappa>\<^sub>0\<guillemotright>] = [v \<Turnstile> \<guillemotleft>Rep_rel \<Pi> \<kappa>\<^sub>0\<guillemotright>]\<close>
      by (metis AOT_sem_exe_denoting \<Pi>'_den \<Pi>_den')
  qed
  ultimately have \<open>\<exists>\<Pi>'. AOT_model_denotes \<Pi>' \<and> AOT_model_enc \<kappa> \<Pi>' \<and>
                        (\<forall>v x. (\<exists>w. AOT_model_concrete w x) \<longrightarrow>
                         [v \<Turnstile> \<guillemotleft>Rep_rel \<Pi>' x\<guillemotright>] = [v \<Turnstile> \<guillemotleft>Rep_rel \<Pi> x\<guillemotright>])\<close>
    by blast
  hence \<open>\<exists>\<Pi>'. AOT_model_denotes \<Pi>' \<and> AOT_model_enc \<kappa>' \<Pi>' \<and>
              (\<forall>v x. (\<exists>w. AOT_model_concrete w x) \<longrightarrow>
               [v \<Turnstile> \<guillemotleft>Rep_rel \<Pi>' x\<guillemotright>] = [v \<Turnstile> \<guillemotleft>Rep_rel \<Pi> x\<guillemotright>])\<close>
    using AOT_model_enc_indistinguishable_ex
            [OF ext, OF \<kappa>_den, OF \<kappa>_abs, OF \<kappa>'_den, OF \<kappa>'_abs, OF \<Pi>_den]
          indist by blast
  then obtain \<Pi>'' where
      \<Pi>''_den: \<open>AOT_model_denotes \<Pi>''\<close>
      and \<Pi>''_enc: \<open>AOT_model_enc \<kappa>' \<Pi>''\<close>
      and \<Pi>''_prop: \<open>(\<exists>w. AOT_model_concrete w x) \<Longrightarrow>
                      [v \<Turnstile> \<guillemotleft>Rep_rel \<Pi>'' x\<guillemotright>] = [v \<Turnstile> \<guillemotleft>Rep_rel \<Pi> x\<guillemotright>]\<close> for v x
    by blast
  have \<open>[v \<Turnstile> \<Pi>''\<down>]\<close>
    by (simp add: AOT_sem_denotes \<Pi>''_den)
  moreover have \<open>[v \<Turnstile> \<kappa>'[\<Pi>'']]\<close>
    by (simp add: AOT_enc_\<kappa>_meta \<Pi>''_den \<Pi>''_enc \<kappa>'_den)
  moreover have \<open>[v \<Turnstile> [\<lambda>x \<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>\<^sub>0] \<Longrightarrow>
                 (\<forall>w. [w \<Turnstile> [\<Pi>'']\<kappa>\<^sub>0] = [w \<Turnstile> [\<Pi>]\<kappa>\<^sub>0])\<close> for \<kappa>\<^sub>0
  proof -
    assume \<open>[v \<Turnstile> [\<lambda>x \<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>\<^sub>0]\<close>
    hence \<open>\<exists>w. AOT_model_concrete w \<kappa>\<^sub>0\<close>
      by (metis AOT_sem_concrete AOT_sem_dia AOT_sem_exe AOT_sem_lambda_beta)
    thus \<open>\<forall>w. [w \<Turnstile> [\<Pi>'']\<kappa>\<^sub>0] = [w \<Turnstile> [\<Pi>]\<kappa>\<^sub>0]\<close>
      using \<Pi>''_prop by (metis AOT_sem_exe_denoting \<Pi>_den' calculation(1)) 
  qed
  ultimately show \<open>\<exists>\<Pi>'. [v \<Turnstile> \<Pi>'\<down>] \<and> [v \<Turnstile> \<kappa>'[\<Pi>']] \<and>
                         (\<forall>\<kappa>\<^sub>0. [v \<Turnstile> [\<lambda>x \<diamond>[\<guillemotleft>AOT_sem_concrete\<guillemotright>]x]\<kappa>\<^sub>0] \<longrightarrow>
                               (\<forall>w. [w \<Turnstile> [\<Pi>']\<kappa>\<^sub>0] = [w \<Turnstile> [\<Pi>]\<kappa>\<^sub>0]))\<close>
    by (safe intro!: exI[where x=\<Pi>'']) blast+
qed
end

instantiation prod :: (AOT_UnaryEnc, AOT_Enc) AOT_Enc
begin
definition AOT_proj_enc_prod :: \<open>'a\<times>'b \<Rightarrow> ('a\<times>'b \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close> where
  \<open>AOT_proj_enc_prod \<equiv> \<lambda> (\<kappa>,\<kappa>') \<phi> . \<guillemotleft>\<kappa>[\<lambda>\<nu> \<guillemotleft>\<phi> (\<nu>,\<kappa>')\<guillemotright>] &
                                     \<guillemotleft>AOT_proj_enc \<kappa>' (\<lambda>\<nu>. \<phi> (\<kappa>,\<nu>))\<guillemotright>\<guillemotright>\<close>
definition AOT_enc_prod :: \<open>'a\<times>'b \<Rightarrow> <'a\<times>'b> \<Rightarrow> \<o>\<close> where
  \<open>AOT_enc_prod \<equiv> \<lambda> \<kappa> \<Pi> . \<guillemotleft>\<Pi>\<down> & \<guillemotleft>AOT_proj_enc \<kappa> (\<lambda> \<kappa>\<^sub>1'\<kappa>\<^sub>n'.  \<guillemotleft>[\<Pi>]\<kappa>\<^sub>1'...\<kappa>\<^sub>n'\<guillemotright>)\<guillemotright>\<guillemotright>\<close>
instance proof
  show \<open>[v \<Turnstile> \<kappa>\<^sub>1...\<kappa>\<^sub>n[\<Pi>]] \<Longrightarrow> [v \<Turnstile> \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>] \<and> [v \<Turnstile> \<Pi>\<down>]\<close>
    for v and \<kappa>\<^sub>1\<kappa>\<^sub>n :: \<open>'a\<times>'b\<close> and \<Pi>
    unfolding AOT_enc_prod_def
    apply (induct \<kappa>\<^sub>1\<kappa>\<^sub>n; simp add: AOT_sem_conj AOT_sem_denotes AOT_proj_enc_prod_def)
    by (metis AOT_sem_denotes AOT_model_denotes_prod_def AOT_sem_enc_denotes
              AOT_sem_proj_enc_denotes case_prodI)
next
  show \<open>[v \<Turnstile> \<kappa>\<^sub>1...\<kappa>\<^sub>n[\<Pi>]] =
        [v \<Turnstile> \<guillemotleft>\<Pi>\<guillemotright>\<down> & \<guillemotleft>AOT_proj_enc \<kappa>\<^sub>1\<kappa>\<^sub>n (\<lambda> \<kappa>\<^sub>1\<kappa>\<^sub>n.  \<guillemotleft>[\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n\<guillemotright>)\<guillemotright>]\<close>
    for v and \<kappa>\<^sub>1\<kappa>\<^sub>n :: \<open>'a\<times>'b\<close> and \<Pi>
    unfolding AOT_enc_prod_def ..
next
  show \<open>[v \<Turnstile> \<guillemotleft>AOT_proj_enc \<kappa>s \<phi>\<guillemotright>] \<Longrightarrow> [v \<Turnstile> \<guillemotleft>\<kappa>s\<guillemotright>\<down>]\<close>
    for v and \<kappa>s :: \<open>'a\<times>'b\<close> and \<phi>
    by (metis (mono_tags, lifting)
          AOT_sem_conj AOT_sem_denotes AOT_model_denotes_prod_def
          AOT_sem_enc_denotes AOT_sem_proj_enc_denotes
          AOT_proj_enc_prod_def case_prod_unfold)
next
  fix v w \<Pi> and \<kappa>\<^sub>1\<kappa>\<^sub>n :: \<open>'a\<times>'b\<close>
  show \<open>[w \<Turnstile> \<kappa>\<^sub>1...\<kappa>\<^sub>n[\<Pi>]]\<close> if \<open>[v \<Turnstile> \<kappa>\<^sub>1...\<kappa>\<^sub>n[\<Pi>]]\<close> for v w \<Pi> and \<kappa>\<^sub>1\<kappa>\<^sub>n :: \<open>'a\<times>'b\<close>
    by (metis (mono_tags, lifting)
          AOT_enc_prod_def AOT_sem_enc_proj_enc AOT_sem_conj AOT_sem_denotes
          AOT_sem_proj_enc_nec AOT_proj_enc_prod_def case_prod_unfold that)
next
  show \<open>[w \<Turnstile> \<guillemotleft>AOT_proj_enc \<kappa>\<^sub>1\<kappa>\<^sub>n \<phi>\<guillemotright>]\<close> if \<open>[v \<Turnstile> \<guillemotleft>AOT_proj_enc \<kappa>\<^sub>1\<kappa>\<^sub>n \<phi>\<guillemotright>]\<close>
    for v w \<phi> and \<kappa>\<^sub>1\<kappa>\<^sub>n :: \<open>'a\<times>'b\<close>
    by (metis (mono_tags, lifting)
          that AOT_sem_enc_proj_enc AOT_sem_conj AOT_sem_denotes
          AOT_sem_proj_enc_nec AOT_proj_enc_prod_def case_prod_unfold)
next
  fix v
  obtain \<kappa> :: 'a where a_prop: \<open>[v \<Turnstile> \<kappa>\<down>] \<and> (\<forall> \<Pi> . [v \<Turnstile> \<Pi>\<down>] \<longrightarrow>  [v \<Turnstile> \<kappa>[\<Pi>]])\<close>
    using AOT_sem_universal_encoder by blast
  obtain \<kappa>\<^sub>1'\<kappa>\<^sub>n' :: 'b where b_prop:
    \<open>[v \<Turnstile> \<kappa>\<^sub>1'...\<kappa>\<^sub>n'\<down>] \<and> (\<forall> \<phi> . [v \<Turnstile> [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<guillemotleft>\<phi> \<nu>\<^sub>1\<nu>\<^sub>n\<guillemotright>]\<down>] \<longrightarrow>
                                [v \<Turnstile> \<guillemotleft>AOT_proj_enc \<kappa>\<^sub>1'\<kappa>\<^sub>n' \<phi>\<guillemotright>])\<close>
    using AOT_sem_universal_encoder by blast
  have \<open>AOT_model_denotes \<guillemotleft>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n [\<guillemotleft>\<Pi>\<guillemotright>]\<nu>\<^sub>1...\<nu>\<^sub>n \<kappa>\<^sub>1'...\<kappa>\<^sub>n']\<guillemotright>\<close>
    if \<open>AOT_model_denotes \<Pi>\<close> for \<Pi> :: \<open><'a\<times>'b>\<close>
    unfolding AOT_model_lambda_denotes
    by (metis (no_types, hide_lams)
          that AOT_meta_prod_equivI(2) AOT_model_denotes_rel.abs_eq
          AOT_sem_exe AOT_sem_exe_denoting Rep_rel_inverse)
  moreover have \<open>AOT_model_denotes  \<guillemotleft>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n [\<guillemotleft>\<Pi>\<guillemotright>]\<kappa> \<nu>\<^sub>1...\<nu>\<^sub>n]\<guillemotright>\<close>
    if \<open>AOT_model_denotes \<Pi>\<close> for \<Pi> :: \<open><'a\<times>'b>\<close>
    unfolding AOT_model_lambda_denotes
    by (metis that AOT_meta_prod_equivI(1) AOT_model_denotes_rel.rep_eq
              AOT_sem_denotes AOT_sem_exe_denoting)
  ultimately have 1: \<open>[v \<Turnstile> \<guillemotleft>(\<kappa>,\<kappa>\<^sub>1'\<kappa>\<^sub>n')\<guillemotright>\<down>]\<close>
              and 2: \<open>(\<forall> \<Pi> . [v \<Turnstile> \<Pi>\<down>] \<longrightarrow>  [v \<Turnstile> \<kappa> \<kappa>\<^sub>1'...\<kappa>\<^sub>n'[\<Pi>]])\<close>
    using a_prop b_prop
    by (auto simp: AOT_sem_denotes AOT_enc_\<kappa>_meta AOT_model_enc_\<kappa>_def
                   AOT_model_denotes_\<kappa>_def AOT_model_denotes_prod_def
                   AOT_enc_prod_def AOT_proj_enc_prod_def AOT_sem_conj)
  have \<open>AOT_model_denotes \<guillemotleft>[\<lambda>z\<^sub>1...z\<^sub>n \<guillemotleft>\<phi> (z\<^sub>1z\<^sub>n, \<kappa>\<^sub>1'\<kappa>\<^sub>n')\<guillemotright>]\<guillemotright>\<close>
    if \<open>AOT_model_denotes \<guillemotleft>[\<lambda>z\<^sub>1...z\<^sub>m \<phi>{z\<^sub>1...z\<^sub>m}]\<guillemotright>\<close> for \<phi> :: \<open>'a\<times>'b \<Rightarrow> \<o>\<close>
    using that
    unfolding AOT_model_lambda_denotes
    by (metis (no_types, lifting) AOT_sem_denotes AOT_model_denotes_prod_def
                                  AOT_meta_prod_equivI(2) b_prop case_prodI)
  moreover have \<open>AOT_model_denotes \<guillemotleft>[\<lambda>z\<^sub>1...z\<^sub>n \<guillemotleft>\<phi> (\<kappa>, z\<^sub>1z\<^sub>n)\<guillemotright>]\<guillemotright>\<close>
    if \<open>AOT_model_denotes \<guillemotleft>[\<lambda>z\<^sub>1...z\<^sub>m \<phi>{z\<^sub>1...z\<^sub>m}]\<guillemotright>\<close> for \<phi> :: \<open>'a\<times>'b \<Rightarrow> \<o>\<close>
    using that
    unfolding AOT_model_lambda_denotes
    by (metis (no_types, lifting) AOT_sem_denotes AOT_model_denotes_prod_def
                                  AOT_meta_prod_equivI(1) a_prop case_prodI)
  ultimately have 3:
    \<open>[v \<Turnstile> \<guillemotleft>(\<kappa>,\<kappa>\<^sub>1'\<kappa>\<^sub>n')\<guillemotright>\<down>] \<and> (\<forall> \<phi> . [v \<Turnstile> [\<lambda>z\<^sub>1...z\<^sub>n \<phi>{z\<^sub>1...z\<^sub>n}]\<down>] \<longrightarrow>
                                   [v \<Turnstile> \<guillemotleft>AOT_proj_enc (\<kappa>,\<kappa>\<^sub>1'\<kappa>\<^sub>n') \<phi>\<guillemotright>])\<close>
    using a_prop b_prop
    by (auto simp: AOT_sem_denotes AOT_enc_\<kappa>_meta AOT_model_enc_\<kappa>_def
                   AOT_model_denotes_\<kappa>_def AOT_enc_prod_def AOT_proj_enc_prod_def
                   AOT_sem_conj AOT_model_denotes_prod_def)
  show \<open>\<exists>\<kappa>\<^sub>1\<kappa>\<^sub>n::'a\<times>'b. [v \<Turnstile> \<kappa>\<^sub>1...\<kappa>\<^sub>n\<down>] \<and> (\<forall> \<Pi> . [v \<Turnstile> \<Pi>\<down>] \<longrightarrow> [v \<Turnstile> \<kappa>\<^sub>1...\<kappa>\<^sub>n[\<Pi>]]) \<and>
                      (\<forall> \<phi> . [v \<Turnstile> [\<lambda>z\<^sub>1...z\<^sub>n \<guillemotleft>\<phi> z\<^sub>1z\<^sub>n\<guillemotright>]\<down>] \<longrightarrow>
                             [v \<Turnstile> \<guillemotleft>AOT_proj_enc \<kappa>\<^sub>1\<kappa>\<^sub>n \<phi>\<guillemotright>])\<close>
    apply (rule exI[where x=\<open>(\<kappa>,\<kappa>\<^sub>1'\<kappa>\<^sub>n')\<close>]) using 1 2 3 by blast
qed
end

lemma \<open>[v \<Turnstile> \<kappa>\<^sub>1\<kappa>\<^sub>2[\<Pi>]] = [v \<Turnstile> \<Pi>\<down> & \<kappa>\<^sub>1[\<lambda>\<nu> [\<Pi>]\<nu>\<kappa>\<^sub>2] & \<kappa>\<^sub>2[\<lambda>\<nu> [\<Pi>]\<kappa>\<^sub>1\<nu>]]\<close>
  for \<kappa>\<^sub>1 :: "'a::AOT_UnaryEnc" and \<kappa>\<^sub>2 :: "'b::AOT_UnaryEnc"
  by (simp add: AOT_sem_conj AOT_enc_prod_def AOT_proj_enc_prod_def
                AOT_sem_unary_proj_enc)

lemma \<open>[v \<Turnstile> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3[\<Pi>]] =
       [v \<Turnstile> \<Pi>\<down> & \<kappa>\<^sub>1[\<lambda>\<nu> [\<Pi>]\<nu>\<kappa>\<^sub>2\<kappa>\<^sub>3] & \<kappa>\<^sub>2[\<lambda>\<nu> [\<Pi>]\<kappa>\<^sub>1\<nu>\<kappa>\<^sub>3] & \<kappa>\<^sub>3[\<lambda>\<nu> [\<Pi>]\<kappa>\<^sub>1\<kappa>\<^sub>2\<nu>]]\<close>
  for \<kappa>\<^sub>1 \<kappa>\<^sub>2 \<kappa>\<^sub>3 :: "'a::AOT_UnaryEnc"
  by (simp add: AOT_sem_conj AOT_enc_prod_def AOT_proj_enc_prod_def
                AOT_sem_unary_proj_enc)

lemma AOT_sem_vars_denote: \<open>[v \<Turnstile> \<alpha>\<^sub>1...\<alpha>\<^sub>n\<down>]\<close>
  by induct simp

class AOT_\<kappa>s = AOT_IndividualTerm + AOT_Individual + AOT_Enc
class AOT_\<kappa> = AOT_\<kappa>s + AOT_UnaryIndividualTerm + AOT_UnaryIndividual + AOT_UnaryEnc

instance \<kappa> :: AOT_\<kappa> by standard
instance prod :: (AOT_\<kappa>, AOT_\<kappa>s) AOT_\<kappa>s by standard

AOT_register_type_constraints
  Individual: \<open>_::AOT_\<kappa>\<close> \<open>_::AOT_\<kappa>s\<close> and
  Relation: \<open><_::AOT_\<kappa>s>\<close>

AOT_define AOT_ordinary :: \<open>\<Pi>\<close> (\<open>O!\<close>) \<open>O! =\<^sub>d\<^sub>f [\<lambda>x \<diamond>E!x]\<close>
declare AOT_ordinary[AOT del, AOT_defs del]
AOT_define AOT_abstract :: \<open>\<Pi>\<close> (\<open>A!\<close>) \<open>A! =\<^sub>d\<^sub>f [\<lambda>x \<not>\<diamond>E!x]\<close>
declare AOT_abstract[AOT del, AOT_defs del]

context AOT_meta_syntax
begin
notation AOT_ordinary ("\<^bold>O\<^bold>!")
notation AOT_abstract ("\<^bold>A\<^bold>!")
end
context AOT_no_meta_syntax
begin
no_notation AOT_ordinary ("\<^bold>O\<^bold>!")
no_notation AOT_abstract ("\<^bold>A\<^bold>!")
end

lemma AOT_sem_ordinary: "\<guillemotleft>O!\<guillemotright> = \<guillemotleft>[\<lambda>x \<diamond>E!x]\<guillemotright>"
  using AOT_ordinary[THEN AOT_sem_id_def0E1] AOT_sem_ordinary_def_denotes
  by (auto simp: AOT_sem_eq AOT_concrete_sem)
lemma AOT_sem_abstract: "\<guillemotleft>A!\<guillemotright> = \<guillemotleft>[\<lambda>x \<not>\<diamond>E!x]\<guillemotright>"
  using AOT_abstract[THEN AOT_sem_id_def0E1]  AOT_sem_abstract_def_denotes
  by (auto simp: AOT_sem_eq AOT_concrete_sem)
lemma AOT_sem_ordinary_denotes: \<open>[w \<Turnstile> O!\<down>]\<close>
  by (simp add: AOT_sem_ordinary AOT_sem_ordinary_def_denotes AOT_concrete_sem)
lemma AOT_meta_abstract_denotes: \<open>[w \<Turnstile> A!\<down>]\<close>
  by (simp add: AOT_sem_abstract AOT_sem_abstract_def_denotes AOT_concrete_sem)
lemma AOT_model_abstract_\<alpha>\<kappa>: \<open>\<exists> a . \<kappa> = \<alpha>\<kappa> a\<close> if \<open>[v \<Turnstile> A!\<kappa>]\<close>
  using that[unfolded AOT_sem_abstract, simplified
      AOT_meta_abstract_denotes[unfolded AOT_sem_abstract, THEN AOT_sem_lambda_beta,
          OF that[simplified AOT_sem_exe, THEN conjunct2, THEN conjunct1]]]
  apply (simp add: AOT_sem_not AOT_sem_dia AOT_sem_concrete AOT_concrete_sem)
  by (metis AOT_model_\<omega>_concrete_in_some_world AOT_model_concrete_\<kappa>.simps(1)
            AOT_model_denotes_\<kappa>_def AOT_sem_denotes AOT_sem_exe \<kappa>.exhaust_disc
            is_\<alpha>\<kappa>_def is_\<omega>\<kappa>_def that)
lemma AOT_model_ordinary_\<omega>\<kappa>: \<open>\<exists> a . \<kappa> = \<omega>\<kappa> a\<close> if \<open>[v \<Turnstile> O!\<kappa>]\<close>
  using that[unfolded AOT_sem_ordinary, simplified
      AOT_sem_ordinary_denotes[unfolded AOT_sem_ordinary, THEN AOT_sem_lambda_beta,
        OF that[simplified AOT_sem_exe, THEN conjunct2, THEN conjunct1]]]
  apply (simp add: AOT_sem_dia AOT_sem_concrete AOT_concrete_sem)
  by (metis AOT_model_concrete_\<kappa>.simps(2) AOT_model_concrete_\<kappa>.simps(3)
            \<kappa>.exhaust_disc is_\<alpha>\<kappa>_def is_\<omega>\<kappa>_def is_null\<kappa>_def)
lemma AOT_model_\<omega>\<kappa>_ordinary: \<open>[v \<Turnstile> O!\<guillemotleft>\<omega>\<kappa> x\<guillemotright>]\<close>
  by (metis AOT_concrete_sem AOT_model_\<omega>_concrete_in_some_world AOT_sem_ordinary
            AOT_sem_exe AOT_sem_ordinary_denotes[unfolded AOT_sem_ordinary]
            AOT_sem_lambda_beta AOT_model_concrete_\<kappa>.simps(1) AOT_sem_concrete
            AOT_sem_denotes AOT_sem_dia) 
lemma AOT_model_\<alpha>\<kappa>_ordinary: \<open>[v \<Turnstile> A!\<guillemotleft>\<alpha>\<kappa> x\<guillemotright>]\<close>
  by (metis AOT_sem_abstract AOT_meta_abstract_denotes[unfolded AOT_sem_abstract]
            AOT_concrete_sem AOT_model_concrete_\<kappa>.simps(2) AOT_model_denotes_\<kappa>_def
            AOT_sem_lambda_beta AOT_sem_concrete AOT_sem_denotes AOT_sem_dia
            AOT_sem_not \<kappa>.disc(8))

  
definition AOT_instance_of_cqt_2 :: \<open>('a::AOT_\<kappa>s \<Rightarrow> \<o>) \<Rightarrow> bool\<close> where
  \<open>AOT_instance_of_cqt_2 \<equiv> \<lambda> \<phi> . \<forall> v . [v \<Turnstile> [\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<down>]\<close>
definition AOT_instance_of_cqt_2_exe_arg :: \<open>('a::AOT_\<kappa>s \<Rightarrow> 'b::AOT_\<kappa>s) \<Rightarrow> bool\<close> where
  \<open>AOT_instance_of_cqt_2_exe_arg \<equiv> \<lambda> \<phi> . \<forall> x y .
      AOT_model_denotes x \<and> AOT_model_term_equiv x y \<longrightarrow>
      (AOT_model_term_equiv (\<phi> x) (\<phi> y) \<or>
       (\<not>AOT_model_denotes (\<phi> x) \<and> \<not>AOT_model_denotes (\<phi> y)))\<close>
definition AOT_instance_of_cqt_2_exe_rel :: \<open>('a::AOT_\<kappa>s \<Rightarrow> <'b::AOT_\<kappa>s>) \<Rightarrow> bool\<close> where
  \<open>AOT_instance_of_cqt_2_exe_rel \<equiv> \<lambda> \<phi> . \<forall> x y z v .
      AOT_model_denotes x \<and> AOT_model_denotes y \<and>
      AOT_model_denotes z \<and> AOT_model_term_equiv x y \<longrightarrow>
      [v \<Turnstile> \<guillemotleft>AOT_exe (\<phi> x) z\<guillemotright>] = [v \<Turnstile> \<guillemotleft>AOT_exe (\<phi> y) z\<guillemotright>]\<close>
definition AOT_instance_of_cqt_2_enc_arg :: \<open>('a::AOT_\<kappa>s \<Rightarrow> 'b::AOT_\<kappa>s) \<Rightarrow> bool\<close> where
  \<open>AOT_instance_of_cqt_2_enc_arg \<equiv> \<lambda> \<phi> . \<forall> x y z .
      AOT_model_term_equiv x y \<longrightarrow> AOT_enc (\<phi> x) z = AOT_enc (\<phi> y) z\<close>
definition AOT_instance_of_cqt_2_enc_rel :: \<open>('a::AOT_\<kappa>s \<Rightarrow> <'b::AOT_\<kappa>s>) \<Rightarrow> bool\<close> where
  \<open>AOT_instance_of_cqt_2_enc_rel \<equiv> \<lambda> \<phi> . \<forall> x y z .
      AOT_model_term_equiv x y \<longrightarrow> AOT_enc z (\<phi> x) = AOT_enc z (\<phi> y)\<close>

syntax AOT_instance_of_cqt_2 :: \<open>id_position \<Rightarrow> AOT_prop\<close>
  ("INSTANCE'_OF'_CQT'_2'(_')")

named_theorems AOT_instance_of_cqt_2_intro
lemma AOT_instance_of_cqt_2_intros_const[AOT_instance_of_cqt_2_intro]:
  \<open>AOT_instance_of_cqt_2 (\<lambda>\<alpha>. \<phi>)\<close>
  by (simp add: AOT_instance_of_cqt_2_def AOT_sem_denotes AOT_model_lambda_denotes)
lemma AOT_instance_of_cqt_2_intros_not[AOT_instance_of_cqt_2_intro]:
  assumes \<open>AOT_instance_of_cqt_2 \<phi>\<close>
  shows \<open>AOT_instance_of_cqt_2 (\<lambda>\<tau>. \<guillemotleft>\<not>\<phi>{\<tau>}\<guillemotright>)\<close>
  using assms
  by (simp add: AOT_instance_of_cqt_2_def AOT_sem_denotes
                AOT_model_lambda_denotes AOT_sem_not)
lemma AOT_instance_of_cqt_2_intros_imp[AOT_instance_of_cqt_2_intro]:
  assumes \<open>AOT_instance_of_cqt_2 \<phi>\<close> and \<open>AOT_instance_of_cqt_2 \<psi>\<close>
  shows \<open>AOT_instance_of_cqt_2 (\<lambda>\<tau>. \<guillemotleft>\<phi>{\<tau>} \<rightarrow> \<psi>{\<tau>}\<guillemotright>)\<close>
  using assms
  by (auto simp: AOT_instance_of_cqt_2_def AOT_sem_denotes
                 AOT_model_lambda_denotes AOT_sem_imp)
lemma AOT_instance_of_cqt_2_intros_box[AOT_instance_of_cqt_2_intro]:
  assumes \<open>AOT_instance_of_cqt_2 \<phi>\<close>
  shows \<open>AOT_instance_of_cqt_2 (\<lambda>\<tau>. \<guillemotleft>\<box>\<phi>{\<tau>}\<guillemotright>)\<close>
  using assms
  by (auto simp: AOT_instance_of_cqt_2_def AOT_sem_denotes
                 AOT_model_lambda_denotes AOT_sem_box)
lemma AOT_instance_of_cqt_2_intros_act[AOT_instance_of_cqt_2_intro]:
  assumes \<open>AOT_instance_of_cqt_2 \<phi>\<close>
  shows \<open>AOT_instance_of_cqt_2 (\<lambda>\<tau>. \<guillemotleft>\<^bold>\<A>\<phi>{\<tau>}\<guillemotright>)\<close>
  using assms
  by (auto simp: AOT_instance_of_cqt_2_def AOT_sem_denotes
                 AOT_model_lambda_denotes AOT_sem_act)
lemma AOT_instance_of_cqt_2_intros_diamond[AOT_instance_of_cqt_2_intro]:
  assumes \<open>AOT_instance_of_cqt_2 \<phi>\<close>
  shows \<open>AOT_instance_of_cqt_2 (\<lambda>\<tau>. \<guillemotleft>\<diamond>\<phi>{\<tau>}\<guillemotright>)\<close>
  using assms
  by (auto simp: AOT_instance_of_cqt_2_def AOT_sem_denotes
                 AOT_model_lambda_denotes AOT_sem_dia)
lemma AOT_instance_of_cqt_2_intros_conj[AOT_instance_of_cqt_2_intro]:
  assumes \<open>AOT_instance_of_cqt_2 \<phi>\<close> and \<open>AOT_instance_of_cqt_2 \<psi>\<close>
  shows \<open>AOT_instance_of_cqt_2 (\<lambda>\<tau>. \<guillemotleft>\<phi>{\<tau>} & \<psi>{\<tau>}\<guillemotright>)\<close>
  using assms
  by (auto simp: AOT_instance_of_cqt_2_def AOT_sem_denotes
                 AOT_model_lambda_denotes AOT_sem_conj)
lemma AOT_instance_of_cqt_2_intros_disj[AOT_instance_of_cqt_2_intro]:
  assumes \<open>AOT_instance_of_cqt_2 \<phi>\<close> and \<open>AOT_instance_of_cqt_2 \<psi>\<close>
  shows \<open>AOT_instance_of_cqt_2 (\<lambda>\<tau>. \<guillemotleft>\<phi>{\<tau>} \<or> \<psi>{\<tau>}\<guillemotright>)\<close>
  using assms
  by (auto simp: AOT_instance_of_cqt_2_def AOT_sem_denotes
                 AOT_model_lambda_denotes AOT_sem_disj)
lemma AOT_instance_of_cqt_2_intros_equib[AOT_instance_of_cqt_2_intro]:
  assumes \<open>AOT_instance_of_cqt_2 \<phi>\<close> and \<open>AOT_instance_of_cqt_2 \<psi>\<close>
  shows \<open>AOT_instance_of_cqt_2 (\<lambda>\<tau>. \<guillemotleft>\<phi>{\<tau>} \<equiv> \<psi>{\<tau>}\<guillemotright>)\<close>
  using assms
  by (auto simp: AOT_instance_of_cqt_2_def AOT_sem_denotes
                 AOT_model_lambda_denotes AOT_sem_equiv)
lemma AOT_instance_of_cqt_2_intros_forall[AOT_instance_of_cqt_2_intro]:
  assumes \<open>\<And> \<alpha> . AOT_instance_of_cqt_2 (\<Phi> \<alpha>)\<close>
  shows \<open>AOT_instance_of_cqt_2 (\<lambda>\<tau>. \<guillemotleft>\<forall>\<alpha> \<Phi>{\<alpha>,\<tau>}\<guillemotright>)\<close>
  using assms
  by (auto simp: AOT_instance_of_cqt_2_def AOT_sem_denotes
                 AOT_model_lambda_denotes AOT_sem_forall)
lemma AOT_instance_of_cqt_2_intros_exists[AOT_instance_of_cqt_2_intro]:
  assumes \<open>\<And> \<alpha> . AOT_instance_of_cqt_2 (\<Phi> \<alpha>)\<close>
  shows \<open>AOT_instance_of_cqt_2 (\<lambda>\<tau>. \<guillemotleft>\<exists>\<alpha> \<Phi>{\<alpha>,\<tau>}\<guillemotright>)\<close>
  using assms
  by (auto simp: AOT_instance_of_cqt_2_def AOT_sem_denotes
                 AOT_model_lambda_denotes AOT_sem_exists)

lemma AOT_instance_of_cqt_2_intros_exe_rel[AOT_instance_of_cqt_2_intro]:
  \<open>AOT_instance_of_cqt_2_exe_rel (\<lambda> x . \<Pi>)\<close>
  by (simp add: AOT_instance_of_cqt_2_exe_rel_def)
lemma AOT_instance_of_cqt_2_intros_exe_lambda[AOT_instance_of_cqt_2_intro]:
  assumes \<open>\<And> z . AOT_instance_of_cqt_2 (\<lambda>x. \<phi> z x)\<close>
      and \<open>\<And> z . AOT_instance_of_cqt_2 (\<lambda>x. \<phi> x z)\<close>
  shows \<open>AOT_instance_of_cqt_2_exe_rel (\<lambda> \<kappa>\<^sub>1\<kappa>\<^sub>n. \<guillemotleft>[\<lambda>z\<^sub>1...z\<^sub>n \<phi>{\<kappa>\<^sub>1...\<kappa>\<^sub>n, z\<^sub>1...z\<^sub>n}]\<guillemotright>)\<close>
  using assms
  unfolding AOT_instance_of_cqt_2_exe_rel_def AOT_instance_of_cqt_2_def
  by (simp add: AOT_sem_lambda_beta AOT_model_lambda_denotes AOT_sem_denotes)
lemma AOT_instance_of_cqt_2_intros_exe_arg_self[AOT_instance_of_cqt_2_intro]:
   \<open>AOT_instance_of_cqt_2_exe_arg (\<lambda>x. x)\<close>
  unfolding AOT_instance_of_cqt_2_exe_arg_def AOT_instance_of_cqt_2_def
            AOT_sem_lambda_denotes
  by (auto simp: AOT_model_term_equiv_part_equivp equivp_reflp AOT_sem_denotes)
lemma AOT_instance_of_cqt_2_intros_exe_arg_fst[AOT_instance_of_cqt_2_intro]:
   \<open>AOT_instance_of_cqt_2_exe_arg fst\<close>
  unfolding AOT_instance_of_cqt_2_exe_arg_def AOT_instance_of_cqt_2_def
  by (simp add: AOT_model_term_equiv_prod_def AOT_sem_denotes AOT_sem_lambda_denotes)
lemma AOT_instance_of_cqt_2_intros_exe_arg_snd[AOT_instance_of_cqt_2_intro]:
   \<open>AOT_instance_of_cqt_2_exe_arg snd\<close>
  unfolding AOT_instance_of_cqt_2_exe_arg_def AOT_instance_of_cqt_2_def
  by (simp add: AOT_model_term_equiv_prod_def AOT_sem_denotes AOT_sem_lambda_denotes)
lemma AOT_instance_of_cqt_2_intros_exe_arg_var[AOT_instance_of_cqt_2_intro]:
     \<open>AOT_instance_of_cqt_2_exe_arg (\<lambda>x. \<kappa>)\<close>
  unfolding AOT_instance_of_cqt_2_exe_arg_def AOT_instance_of_cqt_2_def
  by (auto simp: AOT_model_term_equiv_part_equivp equivp_reflp
                 AOT_sem_denotes AOT_sem_lambda_denotes)
lemma AOT_instance_of_cqt_2_intros_exe_arg_Pair[AOT_instance_of_cqt_2_intro]:
  assumes \<open>AOT_instance_of_cqt_2_exe_arg \<phi>\<close> and \<open>AOT_instance_of_cqt_2_exe_arg \<psi>\<close>
  shows \<open>AOT_instance_of_cqt_2_exe_arg (\<lambda>\<tau>. Pair (\<phi> \<tau>) (\<psi> \<tau>))\<close>
  using assms
  unfolding AOT_instance_of_cqt_2_exe_arg_def AOT_instance_of_cqt_2_def
            AOT_sem_denotes AOT_sem_lambda_denotes AOT_model_term_equiv_prod_def
            AOT_model_denotes_prod_def
  by auto
lemma AOT_instance_of_cqt_2_intros_desc[AOT_instance_of_cqt_2_intro]:
  assumes \<open>\<And>z :: 'a::AOT_\<kappa>. AOT_instance_of_cqt_2 (\<Phi> z)\<close>
  shows \<open>AOT_instance_of_cqt_2_exe_arg (\<lambda> \<kappa> :: 'b::AOT_\<kappa> . \<guillemotleft>\<^bold>\<iota>z(\<Phi>{z,\<kappa>})\<guillemotright>)\<close>
proof -
  have 0: \<open>\<forall> \<kappa> \<kappa>'. AOT_model_denotes \<kappa> \<and> AOT_model_denotes \<kappa>' \<and>
                   AOT_model_term_equiv \<kappa> \<kappa>' \<longrightarrow>
                   [w\<^sub>0 \<Turnstile> \<guillemotleft>\<Phi> z \<kappa>\<guillemotright>] = [w\<^sub>0 \<Turnstile> \<guillemotleft>\<Phi> z \<kappa>'\<guillemotright>]\<close> for z
    using assms
    unfolding AOT_instance_of_cqt_2_def
              AOT_sem_denotes AOT_model_lambda_denotes by simp
  {
    fix \<kappa> \<kappa>' :: 'b
    assume 1: \<open>AOT_model_denotes \<kappa> \<and> AOT_model_term_equiv \<kappa> \<kappa>'\<close>
    {
      assume \<open>\<not>AOT_model_denotes \<guillemotleft>\<^bold>\<iota>z(\<Phi>{z,\<kappa>})\<guillemotright>\<close>
      moreover have \<open>\<not>AOT_model_denotes \<guillemotleft>\<^bold>\<iota>z(\<Phi>{z,\<kappa>'})\<guillemotright>\<close>
        using calculation 0 1 AOT_model_term_equiv_denotes
        unfolding AOT_sem_desc_denotes[unfolded AOT_sem_denotes]
        by blast
      ultimately have \<open>\<not>AOT_model_denotes \<guillemotleft>\<^bold>\<iota>z(\<Phi>{z,\<kappa>})\<guillemotright> \<and>
                       \<not>AOT_model_denotes \<guillemotleft>\<^bold>\<iota>z(\<Phi>{z,\<kappa>'})\<guillemotright>\<close>
        by simp
    }
    moreover {
      assume \<open>AOT_model_denotes \<guillemotleft>\<^bold>\<iota>z(\<Phi>{z,\<kappa>})\<guillemotright>\<close>
      moreover have \<open>AOT_model_denotes \<guillemotleft>\<^bold>\<iota>z(\<Phi>{z,\<kappa>'})\<guillemotright>\<close>
        using calculation 0 1 AOT_model_term_equiv_denotes
        unfolding AOT_sem_desc_denotes[unfolded AOT_sem_denotes]
        by blast
      ultimately have \<open>AOT_model_term_equiv \<guillemotleft>\<^bold>\<iota>z(\<Phi>{z,\<kappa>})\<guillemotright> \<guillemotleft>\<^bold>\<iota>z(\<Phi>{z,\<kappa>'})\<guillemotright>\<close>
        by (smt (verit) "0" "1" AOT_model_term_equiv_denotes
                        AOT_model_term_equiv_rel_equiv AOT_sem_denotes
                        AOT_sem_desc_denotes AOT_sem_desc_prop) 
    }
    ultimately have \<open>AOT_model_term_equiv \<guillemotleft>\<^bold>\<iota>z(\<Phi>{z,\<kappa>})\<guillemotright> \<guillemotleft>\<^bold>\<iota>z(\<Phi>{z,\<kappa>'})\<guillemotright> \<or>
                     (\<not>AOT_model_denotes \<guillemotleft>\<^bold>\<iota>z(\<Phi>{z,\<kappa>})\<guillemotright> \<and>
                      \<not>AOT_model_denotes \<guillemotleft>\<^bold>\<iota>z(\<Phi>{z,\<kappa>'})\<guillemotright>)\<close> by blast
  }
  thus ?thesis
    unfolding AOT_instance_of_cqt_2_exe_arg_def by simp
qed

lemma AOT_instance_of_cqt_2_intros_exe[AOT_instance_of_cqt_2_intro]:
  assumes \<open>AOT_instance_of_cqt_2_exe_rel \<Pi>\<close> and \<open>AOT_instance_of_cqt_2_exe_arg \<kappa>s\<close>
  shows \<open>AOT_instance_of_cqt_2 (\<lambda>x :: 'b::AOT_\<kappa>s. AOT_exe \<guillemotleft>[\<guillemotleft>\<Pi> x\<guillemotright>]\<guillemotright> (\<kappa>s x))\<close>
  using assms
  unfolding AOT_instance_of_cqt_2_def AOT_sem_denotes AOT_model_lambda_denotes
            AOT_instance_of_cqt_2_exe_rel_def AOT_sem_disj AOT_sem_conj
            AOT_sem_not AOT_sem_box AOT_sem_act AOT_instance_of_cqt_2_exe_arg_def
            AOT_sem_equiv AOT_sem_imp AOT_sem_forall AOT_sem_exists AOT_sem_dia
  by (meson AOT_model_term_equiv_denotes AOT_model_term_equiv_rel_equiv
            AOT_sem_denotes AOT_sem_exe)
lemma AOT_instance_of_cqt_2_intros_enc[AOT_instance_of_cqt_2_intro]:
  assumes \<open>AOT_instance_of_cqt_2_enc_rel \<Pi>\<close> and \<open>AOT_instance_of_cqt_2_enc_arg \<kappa>s\<close>
  shows \<open>AOT_instance_of_cqt_2 (\<lambda>x . AOT_enc (\<kappa>s x) \<guillemotleft>[\<guillemotleft>\<Pi> x\<guillemotright>]\<guillemotright>)\<close>
  using assms
  unfolding AOT_instance_of_cqt_2_def AOT_sem_denotes AOT_model_lambda_denotes
            AOT_instance_of_cqt_2_enc_rel_def AOT_sem_not AOT_sem_box AOT_sem_act
            AOT_sem_dia AOT_sem_conj AOT_sem_disj AOT_sem_equiv AOT_sem_imp
            AOT_sem_forall AOT_sem_exists AOT_instance_of_cqt_2_enc_arg_def
  by fastforce+
lemma [AOT_instance_of_cqt_2_intro]:
  assumes \<open>\<And> x . AOT_instance_of_cqt_2 (\<phi> x)\<close>
      and \<open>\<And> x . AOT_instance_of_cqt_2 (\<lambda> z . \<phi> z x)\<close>
  shows \<open>AOT_instance_of_cqt_2 (\<lambda>(x,y) . \<phi> x y)\<close>
  using assms unfolding AOT_instance_of_cqt_2_def
  by (simp add: AOT_model_lambda_denotes AOT_sem_denotes AOT_model_denotes_prod_def
                AOT_model_term_equiv_prod_def) blast

AOT_theorem prod_denotesE: assumes \<open>\<guillemotleft>(\<kappa>\<^sub>1,\<kappa>\<^sub>2)\<guillemotright>\<down>\<close> shows \<open>\<kappa>\<^sub>1\<down> & \<kappa>\<^sub>2\<down>\<close>
  using assms by (simp add: AOT_sem_denotes AOT_sem_conj AOT_model_denotes_prod_def)
declare prod_denotesE[AOT del]
AOT_theorem prod_denotesI: assumes \<open>\<kappa>\<^sub>1\<down> & \<kappa>\<^sub>2\<down>\<close> shows \<open>\<guillemotleft>(\<kappa>\<^sub>1,\<kappa>\<^sub>2)\<guillemotright>\<down>\<close>
  using assms by (simp add: AOT_sem_denotes AOT_sem_conj AOT_model_denotes_prod_def)
declare prod_denotesI[AOT del]

AOT_register_type_constraints
  Individual: \<open>\<kappa>\<close> \<open>_::AOT_\<kappa>s\<close>

(*<*)
end
(*>*)