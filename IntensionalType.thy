theory IntensionalType
  imports Main
  keywords "intensional_type" :: thy_decl
       and "\<supseteq>"
begin

definition int_set :: "('int \<times> 'a) set" where
  \<open>int_set \<equiv> SOME set . \<exists> f :: 'int\<times>'a \<Rightarrow> 'a . \<forall> x :: 'a . \<exists> y \<in> set . x = f y\<close>

lemma int_set_exists: \<open>\<exists> set . \<exists> f :: 'int\<times>'a \<Rightarrow> 'a . \<forall> x :: 'a . \<exists> y \<in> set . x = f y\<close>
  by (rule_tac x=\<open>range (Pair undefined)\<close> in exI; rule_tac x=\<open>snd\<close> in exI) auto

lemma ext_fun_exists: \<open>\<exists> f :: 'int\<times>'a \<Rightarrow> 'a . \<forall> x :: 'a . \<exists> y \<in> int_set . x = f y\<close>
  using someI_ex[OF int_set_exists] unfolding int_set_def by blast

lemma int_set_nonempty: \<open>\<exists> x . x \<in> int_set\<close>
  by (meson ext_fun_exists)

lemma
  int_type_surjection:
  assumes \<open>type_definition (Rep :: 'a \<Rightarrow> 'int \<times> 'b) (Abs :: 'int \<times> 'b \<Rightarrow> 'a) int_set\<close>
  shows "\<exists> f :: 'a \<Rightarrow> 'b . surj f"
proof -
  interpret type_definition Rep Abs int_set using assms .
  obtain f :: \<open>'int\<times>'b \<Rightarrow> 'b\<close> where \<open>\<forall> x :: 'b . \<exists> y \<in> int_set . x = f y\<close>
    using ext_fun_exists by auto
  then obtain g :: \<open>'b \<Rightarrow> 'int \<times> 'b\<close> where
    g_int_set: \<open>\<And> x . g x \<in> int_set\<close> and
    f_g_inv: "\<And> x . f (g x) = x"
    by metis
  show ?thesis
    by (rule_tac x="f o Rep" in exI; rule_tac f="\<lambda> x . Abs (g x)" in surjI)
       (auto simp: g_int_set f_g_inv Abs_inverse)
qed

ML\<open>

fun intensional_type overloaded (bnd,raw_args,mixfix) raw_ext_typ lthy = let

val ext_typ = Syntax.read_typ lthy raw_ext_typ
val tmp_ctxt = lthy |> Variable.declare_typ ext_typ;
val args' = raw_args |> map (apsnd (Typedecl.read_constraint lthy))
val args = args' |> map (Proof_Context.check_tfree tmp_ctxt)
val args_tys = map ((Syntax.read_typ tmp_ctxt) o fst) args
val int_bnd = Binding.concealed (Binding.qualify true ((*Name.internal*) "internal") bnd)
val bnds = {Rep_name = Binding.qualify true "Rep" int_bnd,
            Abs_name = Binding.qualify true "Abs" int_bnd,
            type_definition_name = Binding.qualify true "type_definition" int_bnd}

val (int_typ, lthy) = Local_Theory.background_theory_result
 (Typedecl.typedecl_global {final = true} (Binding.name (Binding.name_of bnd ^ "_int"), args', Mixfix.NoSyn)) lthy
val (int_tyname,_) = Term.dest_Type int_typ

val ((_, info), lthy) = Typedef.add_typedef {overloaded = overloaded} (bnd, args, mixfix)
  (Const (\<^const_name>\<open>int_set\<close>, Type (\<^type_name>\<open>set\<close>, [Type (\<^type_name>\<open>prod\<close>, [Type (int_tyname, args_tys), ext_typ])])))
  (SOME bnds)
  (fn ctxt => Proof_Context.fact_tac ctxt [@{thm int_set_nonempty}] 1)
  lthy

val abs_type = #abs_type (fst info)
val type_definition = #type_definition (snd info)

val choice_thm = type_definition RS @{thm int_type_surjection}

val ext_name = Binding.qualify_name true bnd "ext"

val (surj_fun, lthy) = Local_Theory.background_theory_result
  (Sign.declare_const_global ((ext_name, Type (\<^type_name>\<open>fun\<close>, [abs_type, ext_typ])), Mixfix.NoSyn)) lthy

val lthy' = lthy
val (thm, lthy) = Local_Theory.background_theory_result (fn thy =>
let
val extdef_name = Thm.def_name (Binding.name_of bnd ^ "_ext")
val (thy, thm) = Choice_Specification.add_specification [(extdef_name,fst (Term.dest_Const surj_fun),false)] (thy, choice_thm)
in (thm, thy) end) (Proof_Context.concealed lthy)
val lthy = Proof_Context.restore_naming lthy' lthy
val (_, lthy) = Local_Theory.notes [((ext_name, []), [([thm], [])])] lthy
val lthy = Spec_Rules.add ext_name Spec_Rules.Unknown [surj_fun] [thm] lthy
in lthy end

val _ =
  Outer_Syntax.local_theory
  \<^command_keyword>\<open>intensional_type\<close>
  "declare intensional type as super type of an extension type"
    (Parse_Spec.overloaded -- Parse.type_args_constrained -- Parse.binding -- Parse.opt_mixfix' --
      (\<^keyword>\<open>\<supseteq>\<close> |-- Parse.!!! Parse.typ)
      >> (fn ((((overloaded, args), a), mx), rhs) => intensional_type overloaded (a, args, mx) rhs));
\<close>

end
