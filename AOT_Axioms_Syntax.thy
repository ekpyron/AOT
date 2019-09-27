theory AOT_Axioms_Syntax
  imports AOT_Syntax_next
begin        

named_theorems Axioms

section\<open> Axioms \<close>

lemma ax44_1: "[v \<Turnstile> \<phi> \<rightarrow> (\<psi> \<rightarrow> \<phi>)]" using AOT_Axioms.ax44_1 .
lemma ax44_2: "[v \<Turnstile> (\<phi> \<rightarrow> (\<psi> \<rightarrow> \<chi>)) \<rightarrow> ((\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<phi> \<rightarrow> \<chi>))]" using AOT_Axioms.ax44_2 .
lemma ax44_3: "[v \<Turnstile> (\<not>\<phi> \<rightarrow> \<not>\<psi>) \<rightarrow> ((\<not>\<phi> \<rightarrow> \<psi>) \<rightarrow> \<phi>)]" using AOT_Axioms.ax44_3 .

lemma ax45_1: "[v \<Turnstile> (\<forall> \<alpha> \<phi>{free:\<alpha>}) \<rightarrow> (\<tau>\<down> \<rightarrow> \<phi>{free: \<tau>})]" using AOT_Axioms.ax45_1 .
(* TODO: lemma ax45_2: "[v \<Turnstile> \<langle>\<tau>\<rangle>\<down>]" by (simp add: AOT_var_denotes) *)
lemma ax45_2: "[v \<Turnstile> \<tau>\<down>]" oops (* TODO: verify that this works for all description-free lambda expressions without encoding subformulas *)

lemma ax45_2_lambda_prop_denotes: "[v \<Turnstile> [\<lambda>x p]\<down>]" by (rule AOT_lambda_denotes_intros)+

lemma ax45_2_lambda_exe_denotes: "[v \<Turnstile> [\<lambda>x Fx]\<down>]"
  by (rule AOT_lambda_denotes_intros)
(* TODO: complete this *)
lemma ax45_2_lambda_exe_denotes1: "[v \<Turnstile> [\<lambda>x Fxy]\<down>]"
  oops(*  including AOT_induct
  by (induct F; induct y; rule AOT_lambda_denotesI)
     (simp add: AOT_equiv_prodI AOT_equiv_rel.simps(1) AOT_meta_equiv_indistinguishableI)*)
lemma ax45_2_lambda_exe_denotes2: "[v \<Turnstile> [\<lambda>x Fyx]\<down>]"
  oops (*  including AOT_induct
  by (induct F; induct y; rule AOT_lambda_denotesI)
     (simp add: AOT_equiv_prodI AOT_equiv_rel.simps(1) AOT_meta_equiv_indistinguishableI)*)

lemma ax45_2_lambda_neg_denotes:
  assumes "[v \<Turnstile> [\<lambda>x \<phi>{free:x}]\<down>]"
  shows "[v \<Turnstile> [\<lambda>x \<not>\<phi>{free:x}]\<down>]"
  using assms by (rule AOT_lambda_denotes_intros)
lemma ax45_2_lambda_impl_denotes:
  assumes "[v \<Turnstile> [\<lambda>x \<phi>{free:x}]\<down>]" and "[v \<Turnstile> [\<lambda>x \<psi>{free:x}]\<down>]"
  shows "[v \<Turnstile> [\<lambda>x \<phi>{free:x} \<rightarrow> \<psi>{free:x}]\<down>]"
  using assms by (rule AOT_lambda_denotes_intros)
lemma ax45_2_lambda_box_denotes:
  assumes "[v \<Turnstile> [\<lambda>x \<phi>{free:x}]\<down>]"
  shows "[v \<Turnstile> [\<lambda>x \<box>\<phi>{free:x}]\<down>]"
  using assms by (rule AOT_lambda_denotes_intros)
lemma ax45_2_lambda_actual_denotes:
  assumes "[v \<Turnstile> [\<lambda>x \<phi>{free:x}]\<down>]"
  shows "[v \<Turnstile> [\<lambda>x \<^bold>\<A>\<phi>{free:x}]\<down>]"
  using assms by (rule AOT_lambda_denotes_intros)
lemma ax45_2_lambda_all_denotes:
  assumes "[v \<Turnstile> \<forall>y [\<lambda>x \<phi>{free:xy}]\<down>]"
  shows "[v \<Turnstile> [\<lambda>x \<forall>y \<phi>{free:xy}]\<down>]"
  using assms by (clarify intro!: AOT_lambda_denotes_intros; auto simp: AOT_meta_simp)
lemma ax45_2_lambda_all_denotes_alt:
  assumes "\<And>y. [v \<Turnstile> [\<lambda>x \<phi>{free:xy}]\<down>]"
  shows "[v \<Turnstile> [\<lambda>x \<forall>y \<phi>{free:xy}]\<down>]"
  oops (*
  using assms
  by (clarify intro!: AOT_lambda_denotes_intros; simp add: AOT_meta_simp)
     (insert Rep_var_cases; auto)*)

lemma ax45_3: "[v \<Turnstile> \<forall> \<alpha> (\<phi>{free:\<alpha>} \<rightarrow> \<psi>{free:\<alpha>}) \<rightarrow> (\<forall> \<alpha> \<phi>{free:\<alpha>} \<rightarrow> \<forall> \<alpha> \<psi>{free:\<alpha>})]"
  by (auto simp: AOT_meta_simp)
lemma ax45_4: "[v \<Turnstile> \<phi> \<rightarrow> \<forall> \<alpha> \<phi>]" by (auto simp: AOT_meta_simp)
lemma ax45_5_1: "[v \<Turnstile> \<Pi>\<kappa> \<or> \<kappa>\<Pi> \<rightarrow> \<Pi>\<down> & \<kappa>\<down>]"
  by (simp add: AOT_meta_simp) (meson AOT_denotesS AOT_exeE1 AOT_exeE2)

lemma ax45_5_2: "[v \<Turnstile> \<Pi>\<kappa>\<^sub>1\<kappa>\<^sub>2 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<Pi> \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1\<down> & \<kappa>\<^sub>2\<down>)]"
  using ax45_5_1[of v \<Pi> "(\<kappa>\<^sub>1, \<kappa>\<^sub>2)"] by (simp add: AOT_meta_simp)
lemma ax45_5_3: "[v \<Turnstile> (\<Pi>\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<Pi>) \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1\<down> & \<kappa>\<^sub>2\<down> & \<kappa>\<^sub>3\<down>)]"
  using ax45_5_1[of v \<Pi> "(\<kappa>\<^sub>1, \<kappa>\<^sub>2, \<kappa>\<^sub>3)"] by (simp add: AOT_meta_simp)
lemma ax45_5_4: "[v \<Turnstile> (\<Pi>\<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4 \<or> \<kappa>\<^sub>1\<kappa>\<^sub>2\<kappa>\<^sub>3\<kappa>\<^sub>4\<Pi>) \<rightarrow> (\<Pi>\<down> & \<kappa>\<^sub>1\<down> & \<kappa>\<^sub>2\<down> & \<kappa>\<^sub>3\<down> & \<kappa>\<^sub>4\<down>)]"
  using ax45_5_1[of v \<Pi> "(\<kappa>\<^sub>1, \<kappa>\<^sub>2, \<kappa>\<^sub>3, \<kappa>\<^sub>4)"] by (simp add: AOT_meta_simp)


lemma ax46: "[v \<Turnstile> \<alpha> = \<beta> \<rightarrow> (\<phi>{free: \<alpha>} \<rightarrow> \<phi>{free: \<beta>})]"
  by (simp add: AOT_meta_simp)

lemma ax48: "[dw \<Turnstile> \<^bold>\<A>\<phi> \<equiv> \<phi>]" by (simp add: AOT_meta_simp)

lemma ax49_1: "[v \<Turnstile> \<^bold>\<A>\<not>\<phi> \<equiv> \<not>\<^bold>\<A>\<phi>]" by (simp add: AOT_meta_simp)
lemma ax49_2: "[v \<Turnstile> \<^bold>\<A>(\<phi> \<rightarrow> \<psi>) \<equiv> (\<^bold>\<A>\<phi> \<rightarrow> \<^bold>\<A>\<psi>)]" by (simp add: AOT_meta_simp)
lemma ax49_3: "[v \<Turnstile> \<^bold>\<A>(\<forall> \<alpha>  \<phi>{free: \<alpha>}) \<equiv> \<forall> \<alpha> \<^bold>\<A>\<phi>{free: \<alpha>}]" by (simp add: AOT_meta_simp)
lemma ax49_4: "[v \<Turnstile> \<^bold>\<A>\<phi> \<equiv> \<^bold>\<A>\<^bold>\<A>\<phi>]" by (simp add: AOT_meta_simp)

lemma ax50_1: "[v \<Turnstile> \<box>(\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<box>\<phi> \<rightarrow> \<box>\<psi>)]" by (simp add: AOT_meta_simp)
lemma ax50_2: "[v \<Turnstile> \<box>\<phi> \<rightarrow> \<phi>]" by (simp add: AOT_meta_simp)
lemma ax50_3: "[v \<Turnstile> \<diamond>\<phi> \<rightarrow> \<box>\<diamond>\<phi>]" by (simp add: AOT_meta_simp)
lemma ax50_4: "[v \<Turnstile> \<diamond>(\<exists>x (\<^bold>E!x & \<not>\<^bold>\<A>\<^bold>E!x))]"
  oops (*
  using AOT_denotesS AOT_exeE2 AOT_meta_contingently_concrete_object
  by (simp add: AOT_meta_simp) blast
*)

lemma ax51_1: "[v \<Turnstile> \<^bold>\<A>\<phi> \<rightarrow> \<box>\<^bold>\<A>\<phi>]" by (simp add: AOT_meta_simp)
lemma ax51_2: "[v \<Turnstile> \<box>\<phi> \<equiv> \<^bold>\<A>(\<box>\<phi>)]" by (simp add: AOT_meta_simp)


lemma ax52: "[v \<Turnstile> (x = \<iota>x(\<phi>{free:x})) \<equiv> (\<forall> z (\<^bold>\<A>\<phi>{free:z} \<equiv> z = x))]"
  oops (*
  using AOT_meta_descriptions[of "\<langle>x\<rangle>" v \<phi>]
  using Rep_var by (auto simp: AOT_meta_simp Rep_var)
*)
  

(* axiom 53.1 is implicitly true, since alphabetic variant are meta-logically identical in Isabelle/HOL already *)

lemma ax53_2: "[v \<Turnstile> [\<lambda>x \<phi>{free: x}]\<down> \<rightarrow> [\<lambda>x \<phi>{free: x}]x \<equiv> \<phi>{free:x}]"
  oops (*  by (simp add: AOT_meta_beta AOT_iffS AOT_impS AOT_var_denotes) *)

lemma ax53_3: "[v \<Turnstile> [\<lambda>x Fx] = F]"
  oops (*  by (simp add: AOT_meta_eta AOT_idS AOT_var_equiv) *)

lemma ax54_1: "[v \<Turnstile> ([\<lambda>y \<phi>{free: y}]\<down> & \<box>(\<forall> y (\<phi>{free: y} \<equiv> \<psi>{free: y}))) \<rightarrow> [\<lambda>y \<psi>{free: y}]\<down>]"
  by (simp add: AOT_impS AOT_conjS AOT_boxS AOT_allS AOT_iffS)
     (metis (full_types) AOT_lambda_denotesE AOT_lambda_denotesI AOT_meta_equiv_indistinguishable)

lemma ax54_2: "[v \<Turnstile> [\<lambda>() \<phi>]\<down> \<equiv> \<phi>\<down>]"
  by (simp add: AOT_meta_simp)

lemma ax54_3_stronger[AOT_meta]: "[v \<Turnstile> [\<lambda>() \<forall>x \<phi>{free: x}]\<down>]" (* TODO: note: this is stronger than the actual axiom *)
  by (simp add: AOT_meta_simp AOT_equiv_\<o>_def)
lemma ax54_3: "[v \<Turnstile> [\<lambda>() \<phi>{free: x}]\<down> \<rightarrow> [\<lambda>() \<forall>x \<phi>{free: x}]\<down>]"
  by (simp add: AOT_meta_simp AOT_equiv_\<o>_def)

lemma ax55_1: "Rigid(F) \<equiv>\<^sub>d\<^sub>f F\<^bold>\<down> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>x. \<lparr>F,x\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>F,x\<rparr>)"
  by (simp add: AOT_Rigid_def equivalent_by_definitionI)
lemma ax55_2: "Rigidifies(F,G) \<equiv>\<^sub>d\<^sub>f Rigid(F) \<^bold>& (\<^bold>\<forall> x . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>G,x\<rparr>)"
  by (simp add: AOT_Rigidifies_def equivalent_by_definitionI)

syntax AOT_Rigidifies :: "\<phi> \<Rightarrow> \<phi> \<Rightarrow> \<phi>" ("Rigidifies'(_, _')")

(* TODO: simplify proof *)
lemma ax56: "[v \<Turnstile> \<exists>F Rigidifies( F , G )]"
  oops

lemma ax57_2: "[v \<Turnstile> x\<^sub>1x\<^sub>2F \<equiv> x\<^sub>1[\<lambda>y Fyx\<^sub>2] & x\<^sub>2[\<lambda>y Fx\<^sub>1y]]"
  oops

lemma ax57_3: "[v \<Turnstile> x\<^sub>1x\<^sub>2x\<^sub>3F \<equiv> x\<^sub>1[\<lambda>y Fyx\<^sub>2x\<^sub>3] & x\<^sub>2[\<lambda>y Fx\<^sub>1yx\<^sub>3] & x\<^sub>3[\<lambda>y Fx\<^sub>1x\<^sub>2y]]"
  oops

lemma ax57_4: "[v \<Turnstile> x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4F \<equiv> x\<^sub>1[\<lambda>y Fyx\<^sub>2x\<^sub>3x\<^sub>4] & x\<^sub>2[\<lambda>y Fx\<^sub>1yx\<^sub>3x\<^sub>4] & x\<^sub>3[\<lambda>y Fx\<^sub>1x\<^sub>2yx\<^sub>4] & x\<^sub>4[\<lambda>y Fx\<^sub>1x\<^sub>2x\<^sub>3y]]"
  oops

lemma ax57_5: "[v \<Turnstile> x\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4x\<^sub>5F \<equiv>
                                  x\<^sub>1[\<lambda>y Fyx\<^sub>2x\<^sub>3x\<^sub>4x\<^sub>5]
                                & x\<^sub>2[\<lambda>y Fx\<^sub>1yx\<^sub>3x\<^sub>4x\<^sub>5]
                                & x\<^sub>3[\<lambda>y Fx\<^sub>1x\<^sub>2yx\<^sub>4x\<^sub>5]
                                & x\<^sub>4[\<lambda>y Fx\<^sub>1x\<^sub>2x\<^sub>3yx\<^sub>5]
                                & x\<^sub>5[\<lambda>y Fx\<^sub>1x\<^sub>2x\<^sub>3x\<^sub>4y]]"
  oops

lemma ax58: "[v \<Turnstile> xF \<rightarrow> \<box>xF]"
  by (simp add: AOT_boxS AOT_impS AOT_enc_metaS) 

lemma ax59: "[v \<Turnstile> \<^bold>O!x \<rightarrow> \<not>(\<exists> F xF)]"
  oops

lemma ax60: "[v \<Turnstile> \<exists>x (\<^bold>A!x & \<forall> F (xF \<equiv> \<phi>{free:F}))]"
  oops

end
