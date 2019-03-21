theory AOT_Example
  imports AOT_Axioms AOT_Instantiation
begin

(* In AOT's language: \<exists>p \<box>(p \<equiv> \<phi>) *)
lemma extended_prop: "[v \<Turnstile> \<^bold>\<exists> p . \<^bold>\<box>(\<lparr>p\<rparr> \<^bold>\<equiv> \<phi>)]"
  apply AOT_meta_simp
  (* sledgehammer *)
  by (metis AOT_lambda_applyE1 AOT_lambda_applyI AOT_lambda_const_exists AOT_logical_existsI AOT_meta_equiv_unit_def)

(* In AOT's language: \<Pi>\<down> \<equiv> \<exists>x x\<Pi> *)
lemma "[v \<Turnstile> \<Pi>\<^bold>\<down> \<^bold>\<equiv> (\<^bold>\<exists>x . \<lbrace>x,\<Pi>\<rbrace>)]"
  (* sledgehammer *)
  using AOT_iffI exists_relation_def by blast

(* In AOT's language: \<Pi>\<down> \<equiv> \<exists>x\<exists>y xy\<Pi> *)
lemma "[v \<Turnstile> \<Pi>\<^bold>\<down> \<^bold>\<equiv> (\<^bold>\<exists>x y . \<lbrace>x,y,\<Pi>\<rbrace>)]"
  (* sledgehammer *)
  by (simp add: AOT_iffS exists_relation2_def)

lemma General_Property_Existence:
  (* In AOT's language: \<box>\<forall>x\<forall>y (\<forall>F (Fx \<equiv> Fy) \<rightarrow> \<phi> \<equiv> \<phi>\<^sup>y\<^sub>x) \<rightarrow> [\<lambda>x \<phi>]\<down>  *)
  "[v \<Turnstile> \<^bold>\<box>(\<^bold>\<forall> x y . (\<^bold>\<forall>F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>) \<^bold>\<rightarrow> (\<phi> x \<^bold>\<equiv> \<phi> y)) \<^bold>\<rightarrow> [\<^bold>\<lambda>x . \<phi> x]\<^bold>\<down>]"
proof (rule AOT_impI; rule AOT_lambda_existsI)
  fix x y w
  assume "[v \<Turnstile> \<^bold>\<box>(\<^bold>\<forall> x y . (\<^bold>\<forall>F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>) \<^bold>\<rightarrow> (\<phi> x \<^bold>\<equiv> \<phi> y))]"
  hence "[w \<Turnstile> \<^bold>\<forall> x y . (\<^bold>\<forall>F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>) \<^bold>\<rightarrow> (\<phi> x \<^bold>\<equiv> \<phi> y)]"
    using AOT_boxE by blast
  (* x ~ y is the semantic notion of "x and y share the same Urelement" *)
  thus "[w \<Turnstile> x \<^bold>~ y] \<Longrightarrow> [w \<Turnstile> \<phi> x] = [w \<Turnstile> \<phi> y]"
    apply AOT_meta_simp
    (* sledgehammer *)
    by (metis (mono_tags, hide_lams) AOT_equivE2 AOT_equiv_existsE AOT_equiv_relE1 AOT_equiv_sym)
qed

end
