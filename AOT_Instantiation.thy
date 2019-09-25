theory AOT_Instantiation
  imports AOT_Individual
begin

typedecl \<omega>
typedecl \<sigma>
datatype \<upsilon> = \<omega>\<upsilon> \<omega> | \<sigma>\<upsilon> \<sigma>
type_synonym \<alpha> = "(\<upsilon>\<Rightarrow>\<o>) set"
datatype \<nu> = \<omega>\<nu> \<omega> | \<alpha>\<nu> \<alpha>
typedecl null\<kappa>
datatype \<kappa> = \<nu>\<kappa> \<nu> | null\<kappa> null\<kappa>

consts null\<kappa>_choice :: "'a \<Rightarrow> null\<kappa>"

consts \<alpha>\<sigma> :: "\<alpha> \<Rightarrow> \<sigma>"
specification (\<alpha>\<sigma>)
  \<alpha>\<sigma>_surj[AOT_meta]: "surj \<alpha>\<sigma>"
  by (
      rule_tac x="\<lambda> a . THE s . a = { \<lambda> u . if (u = \<sigma>\<upsilon> s) then (\<epsilon>\<^sub>\<o> v . True) else (\<epsilon>\<^sub>\<o> v . False)}" in exI;
      rule_tac f="\<lambda> s . { \<lambda> u . if (u = \<sigma>\<upsilon> s) then (\<epsilon>\<^sub>\<o> v . True) else (\<epsilon>\<^sub>\<o> v . False)}" in surjI;
      rule the_equality;
      simp
     )
     (metis AOT_proposition_choice \<upsilon>.inject(2))
declare \<alpha>\<sigma>_def[AOT_meta]

primrec \<nu>\<upsilon> :: "\<nu>\<Rightarrow>\<upsilon>" where
  [AOT_meta_simp]: "\<nu>\<upsilon> (\<omega>\<nu> x) = \<omega>\<upsilon> x"
| [AOT_meta_simp]: "\<nu>\<upsilon> (\<alpha>\<nu> x) = \<sigma>\<upsilon> (\<alpha>\<sigma> x)"
(* TODO: theorems and simp rules! *)
declare \<nu>\<upsilon>.simps[AOT_meta, simp del]

lemma \<nu>\<upsilon>_surj[AOT_meta]: "surj \<nu>\<upsilon>"
  by (metis \<alpha>\<sigma>_surj \<nu>\<upsilon>.simps(1) \<nu>\<upsilon>.simps(2) \<upsilon>.exhaust surj_def)

primrec \<kappa>\<upsilon> :: "\<kappa>\<Rightarrow>\<upsilon> option" where
  [AOT_meta_simp]: "\<kappa>\<upsilon> (\<nu>\<kappa> x) = Some (\<nu>\<upsilon> x)"
| [AOT_meta_simp]: "\<kappa>\<upsilon> (null\<kappa> _) = None"
(* TODO: theorems and simp rules! *)
declare \<kappa>\<upsilon>.simps[AOT_meta, simp del]

lemma \<kappa>\<upsilon>_surj[AOT_meta]: "surj \<kappa>\<upsilon>"
  by (rule_tac f="\<lambda> \<kappa> . if \<kappa> = None then null\<kappa> undefined else \<nu>\<kappa> ((inv \<nu>\<upsilon>) (the \<kappa>))" in surjI)
     (simp add: AOT_meta surj_f_inv_f)
                               
instantiation \<kappa> :: AOT_Term
begin
definition AOT_equiv_\<kappa> where
  [AOT_meta, AOT_meta_simp]: "(\<kappa>\<^sub>1 \<approx> \<kappa>\<^sub>2) \<equiv> (\<exists> u . \<kappa>\<upsilon> \<kappa>\<^sub>1 = Some u \<and> \<kappa>\<upsilon> \<kappa>\<^sub>2 = Some u)"
instance proof(standard; rule part_equivpI; (rule exI | rule sympI | rule transpI))
  show "\<nu>\<kappa> (\<omega>\<nu> undefined) \<approx> \<nu>\<kappa> (\<omega>\<nu> undefined)" by (simp add: AOT_meta_simp)
next
  show "x \<approx> y \<Longrightarrow> y \<approx> x" for x y :: \<kappa>
    by (induct x; induct y) (auto simp: AOT_meta_simp)
next
  show "x \<approx> y \<Longrightarrow> y \<approx> z \<Longrightarrow> x \<approx> z" for x y z :: \<kappa>
    by (induct x; induct y; induct z) (auto simp: AOT_meta_simp)
qed
end

definition \<kappa>\<upsilon>_\<upsilon> where [AOT_meta_simp]: "\<kappa>\<upsilon>_\<upsilon> \<equiv> \<lambda> u . the (\<kappa>\<upsilon> (rep_\<upsilon> u))"
definition \<upsilon>_\<kappa>\<upsilon> where [AOT_meta_simp]: "\<upsilon>_\<kappa>\<upsilon> \<equiv> \<lambda> u . abs_\<upsilon> (SOME x . \<kappa>\<upsilon> x = Some u)"

lemma \<upsilon>_\<kappa>\<upsilon>_inverse[AOT_meta, AOT_meta_simp]: "\<kappa>\<upsilon>_\<upsilon> (\<upsilon>_\<kappa>\<upsilon> x) = x"
proof -
  have "\<kappa>\<upsilon> (SOME x . \<kappa>\<upsilon> x = Some u) = Some u" for u
    by (meson \<kappa>\<upsilon>_surj someI_ex surj_f_inv_f)
  thus ?thesis
    by (metis (no_types, lifting) AOT_equiv_\<kappa>_def Quotient_\<upsilon> Quotient_rep_abs_fold_unmap
                                  \<kappa>\<upsilon>_\<upsilon>_def \<upsilon>_\<kappa>\<upsilon>_def option.sel)
qed

lemma \<kappa>\<upsilon>_\<upsilon>_inverse[AOT_meta, AOT_meta_simp]: "\<upsilon>_\<kappa>\<upsilon> (\<kappa>\<upsilon>_\<upsilon> x) = x"
  by (induct x; simp add: AOT_meta_simp)
     (metis (full_types) AOT_equiv_\<kappa>_def Quotient3_\<upsilon> Quotient3_def \<kappa>\<upsilon>_\<upsilon>_def \<upsilon>_\<kappa>\<upsilon>_def
                         \<upsilon>_\<kappa>\<upsilon>_inverse option.distinct(1) option.exhaust_sel)

consts AOT_meta_concrete :: "\<omega> \<Rightarrow> i \<Rightarrow> bool"

specification (AOT_meta_concrete)
  AOT_meta_possibly_concrete: "\<exists> v . AOT_meta_concrete x v"
  AOT_meta_contingent_object: "\<exists> x v . \<not>AOT_meta_concrete x dw \<and> AOT_meta_concrete x v"
proof -
  obtain v where "v \<noteq> dw" using AOT_nonactual_world by auto
  thus ?thesis by (rule_tac x="\<lambda> x w . w = v" in exI) auto
qed

instantiation \<kappa> :: AOT_Concrete
begin
definition AOT_dconcrete_\<kappa> where
  [AOT_meta, AOT_meta_simp]: "AOT_dconcrete_\<kappa> \<equiv> (\<lambda> u . \<epsilon>\<^sub>\<o> v .
    case (\<kappa>\<upsilon>_\<upsilon> u) of (\<omega>\<upsilon> x) \<Rightarrow> AOT_meta_concrete x v
                        | _ \<Rightarrow> False)"
definition AOT_concrete_\<kappa> :: "<\<kappa>>" where
  [AOT_meta, AOT_meta_simp]: "AOT_concrete_\<kappa> \<equiv> drel AOT_dconcrete_\<kappa>"
instance proof
  show "[v \<Turnstile> (E!::<\<kappa>>)\<^bold>\<down>]" for v
    unfolding AOT_concrete_\<kappa>_def
    by (simp add: AOT_meta_simp)
qed
end

lemma AOT_concrete_ordinary: "[w \<Turnstile> \<lparr>E!, \<kappa>\<rparr>] \<Longrightarrow> (\<exists> o\<^sub>1 . \<kappa> = \<nu>\<kappa> (\<omega>\<nu> o\<^sub>1))"
proof (induct \<kappa>)
  case (\<nu>\<kappa> x)
  hence "[w \<Turnstile> AOT_dconcrete_\<kappa> (abs_\<upsilon> (\<nu>\<kappa> x))]"
    unfolding AOT_concrete_\<kappa>_def
    using AOT_exeE3 by fastforce
  thus ?case
    apply (induct x; simp add: AOT_meta_simp)
    by (metis AOT_equiv_\<kappa>_def Quotient_\<upsilon> Quotient_rep_abs
              \<kappa>\<upsilon>.simps(1) \<kappa>\<upsilon>_\<upsilon>_def \<nu>\<upsilon>.simps(2) \<upsilon>.simps(6) option.sel)
qed (simp add: AOT_meta_simp)

lemma AOT_ordinary_concrete: "\<exists> w . [w \<Turnstile> \<lparr>E!, \<nu>\<kappa> (\<omega>\<nu> o\<^sub>1)\<rparr>]"
  unfolding AOT_concrete_\<kappa>_def
  apply (simp add: AOT_meta_simp)
  by (metis AOT_abs_\<upsilon>_inverse AOT_denotesS AOT_equiv_\<kappa>_def AOT_meta_possibly_concrete
            \<kappa>\<upsilon>.simps(1) \<nu>\<upsilon>.simps(1) \<upsilon>.case(1) option.sel)

instantiation \<kappa> :: AOT_Individual
begin
function AOT_meta_enc_\<kappa> :: "\<kappa> \<Rightarrow> (\<kappa> AOT_Term.\<upsilon> \<Rightarrow> \<o>) \<Rightarrow> bool" where
  [AOT_meta_simp]: "AOT_meta_enc_\<kappa> (\<nu>\<kappa> (\<alpha>\<nu> x)) \<phi> = ((\<lambda> u . \<phi> (\<upsilon>_\<kappa>\<upsilon> u)) \<in> x)"
| [AOT_meta_simp]: "AOT_meta_enc_\<kappa> (\<nu>\<kappa> (\<omega>\<nu> x)) \<phi> = False"
| [AOT_meta_simp]: "AOT_meta_enc_\<kappa> (null\<kappa> \<kappa>) \<phi> = False"
  by (metis \<kappa>.exhaust \<nu>.exhaust surj_pair) auto
termination using "termination" by blast
declare AOT_meta_enc_\<kappa>.simps[simp del] (* TODO rest of stuff *)
instance proof
  show "\<exists> \<kappa> :: \<kappa> . \<kappa> \<approx> \<kappa> \<and> AOT_meta_enc \<kappa> \<phi>" for \<phi>
    by (rule_tac x="\<nu>\<kappa> (\<alpha>\<nu> UNIV)" in exI) (auto simp: AOT_meta_simp)
qed
end

instantiation \<kappa> :: AOT_UnaryIndividual
begin
definition AOT_that_\<kappa> :: "(\<kappa> \<Rightarrow> \<o>) \<Rightarrow> \<kappa>" where
  [AOT_meta]: "AOT_that_\<kappa> \<equiv> \<lambda> \<phi> .
  if
    (\<exists>!x . [dw \<Turnstile> \<phi> (\<nu>\<kappa> x)])
  then
    \<nu>\<kappa> (THE x . [dw \<Turnstile> \<phi> (\<nu>\<kappa> x)])
  else
    null\<kappa> (null\<kappa>_choice \<phi>)"

instance proof
  fix \<kappa> :: \<kappa> and w v :: i and \<phi> :: "\<kappa> AOT_Term.\<upsilon> \<Rightarrow> \<o>"
  assume "[w \<Turnstile> \<lparr>E!, \<kappa>\<rparr>]"
  moreover hence "\<kappa> \<approx> \<kappa>" using AOT_denotesS AOT_exeE2 by blast
  ultimately obtain o\<^sub>1 where \<kappa>_def: "\<kappa> = \<nu>\<kappa> (\<omega>\<nu> o\<^sub>1)"
    using AOT_concrete_ordinary by blast
  show "\<not> AOT_meta_enc \<kappa> \<phi>" by (auto simp: \<kappa>_def AOT_meta_simp)
next
  obtain x :: \<omega> and v :: i where
    "\<not> AOT_meta_concrete x dw \<and> AOT_meta_concrete x v"
    using AOT_meta_contingent_object by blast
  thus "\<exists> (\<kappa> :: \<kappa>) v . \<not>[dw \<Turnstile> \<lparr>E!, \<kappa>\<rparr>] \<and> [v \<Turnstile> \<lparr>E!, \<kappa>\<rparr>]"
    by (rule_tac x="\<nu>\<kappa> (\<omega>\<nu> x)" in exI; rule_tac x=v in exI; simp add: AOT_meta_simp)
       (metis (no_types, lifting) AOT_abs_\<upsilon>_inverse AOT_exeE2 AOT_equiv_\<kappa>_def
              AOT_ordinary_concrete \<kappa>\<upsilon>.simps(1) \<nu>\<upsilon>.simps(1) \<upsilon>.simps(5) option.sel)
next
  fix v \<phi>
  {
    fix \<psi> :: "\<kappa> AOT_Term.\<upsilon> \<Rightarrow> \<o>"
    have "(\<lambda>u. \<psi> (abs_\<upsilon> (SOME x. \<kappa>\<upsilon> x = Some (the (\<kappa>\<upsilon> (rep_\<upsilon> u)))))) = \<psi>"
      by (rule ext) (metis \<kappa>\<upsilon>_\<upsilon>_def \<kappa>\<upsilon>_\<upsilon>_inverse \<upsilon>_\<kappa>\<upsilon>_def)
    hence "AOT_meta_enc (\<nu>\<kappa> (\<alpha>\<nu> {r. [v \<Turnstile> \<phi> (\<lambda>u. r (\<kappa>\<upsilon>_\<upsilon> u))]})) \<psi> = [v \<Turnstile> \<phi> \<psi>]"
      by (simp add: AOT_meta_simp)
  } note 0 = this
  show "\<exists> \<kappa> :: \<kappa> . [v \<Turnstile> \<lparr>A!,\<kappa>\<rparr>] \<and> (\<forall>F. AOT_meta_enc \<kappa> F = [v \<Turnstile> \<phi> F])"
    apply (rule_tac x="\<nu>\<kappa> (\<alpha>\<nu> { r . [v \<Turnstile> \<phi> (\<lambda> u . r (\<kappa>\<upsilon>_\<upsilon> u))] })" in exI; rule conjI)
    unfolding AOT_abstract_def
     apply (rule AOT_meta_beta[OF AOT_abstract_denotes[unfolded AOT_abstract_def], THEN iffD2])
      apply (simp add: AOT_meta_simp)
      apply (simp add: AOT_notS AOT_diaS AOT_boxS)
    using AOT_concrete_ordinary AOT_equiv_\<kappa>_def \<kappa>\<upsilon>.simps(1) apply blast
    using 0 by blast
next
  fix \<phi> :: "\<kappa> \<Rightarrow> \<o>" and \<kappa> :: \<kappa> and v :: i
  assume "\<kappa> \<approx> \<kappa>"
  then obtain x where \<kappa>_def: "\<kappa> = \<nu>\<kappa> x"
    by (metis AOT_equiv_\<kappa>_def \<kappa>.exhaust \<kappa>\<upsilon>.simps(2) option.distinct(1))
  {
    assume "[v \<Turnstile> \<kappa> \<^bold>= (\<^bold>\<iota>x::\<kappa>. \<phi> x)]"
    hence "\<kappa> = (\<^bold>\<iota>x::\<kappa>. \<phi> x)"
      by (auto simp: AOT_meta_simp)
    hence unique: "\<exists>!x . [dw \<Turnstile> \<phi> (\<nu>\<kappa> x)]" and "\<kappa> = \<nu>\<kappa> (THE x . [dw \<Turnstile> \<phi> (\<nu>\<kappa> x)])"
      unfolding \<kappa>_def by (metis AOT_that_\<kappa>_def \<kappa>.distinct(1))+
    hence \<phi>x: "[dw \<Turnstile> \<phi> (\<nu>\<kappa> x)]" unfolding \<kappa>_def by (metis the_equality)
    {
      fix \<kappa>' :: \<kappa>
      assume "\<kappa>' \<approx> \<kappa>'"
      then obtain y where z_def: "\<kappa>' = \<nu>\<kappa> y"
        by (metis AOT_equiv_\<kappa>_def \<kappa>.exhaust \<kappa>\<upsilon>.simps(2) option.discI)
      {
        assume "[dw \<Turnstile> \<phi> \<kappa>']"
        hence "y = x" unfolding z_def using unique \<phi>x by auto
        hence "[v \<Turnstile> \<kappa>' \<^bold>= \<kappa>]" unfolding z_def \<kappa>_def by (simp add: AOT_meta_simp)
      }
      moreover {
        assume "[v \<Turnstile> \<kappa>' \<^bold>= \<kappa>]"
        hence "y = x" unfolding z_def \<kappa>_def by (simp add: AOT_meta_simp)
        hence "[dw \<Turnstile> \<phi> \<kappa>']" using \<phi>x unfolding z_def by simp
      }
      ultimately have "[dw \<Turnstile> \<phi> \<kappa>'] = [v \<Turnstile> \<kappa>' \<^bold>= \<kappa>]" by blast
    }
    hence "\<forall>\<kappa>'::\<kappa>. \<kappa>' \<approx> \<kappa>' \<longrightarrow> [dw \<Turnstile> \<phi> \<kappa>'] = [v \<Turnstile> \<kappa>' \<^bold>= \<kappa>]" by simp
  }
  moreover {
    assume 0: "\<forall>\<kappa>'::\<kappa>. \<kappa>' \<approx> \<kappa>' \<longrightarrow> [dw \<Turnstile> \<phi> \<kappa>'] = [v \<Turnstile> \<kappa>' \<^bold>= \<kappa>]"
    hence \<phi>x: "[dw \<Turnstile> \<phi> (\<nu>\<kappa> x)]" unfolding \<kappa>_def by (simp add: AOT_meta_simp)
    have "\<exists>!x . [dw \<Turnstile> \<phi> (\<nu>\<kappa> x)]"
      by (rule_tac a=x in ex1I) 
         (auto simp: "0" AOT_idS AOT_equiv_\<kappa>_def \<kappa>\<upsilon>.simps(1) \<kappa>_def)
    hence "[v \<Turnstile> \<kappa> \<^bold>= (\<^bold>\<iota>x::\<kappa>. \<phi> x)]"
      apply (simp add: AOT_meta_simp AOT_that_\<kappa>_def \<kappa>_def)
      using \<phi>x theI by fastforce
  }
  ultimately show "[v \<Turnstile> \<kappa> \<^bold>= (\<^bold>\<iota>x::\<kappa>. \<phi> x)] = (\<forall>\<kappa>'::\<kappa>. \<kappa>' \<approx> \<kappa>' \<longrightarrow> [dw \<Turnstile> \<phi> \<kappa>'] = [v \<Turnstile> \<kappa>' \<^bold>= \<kappa>])"
    by blast
next
  fix F G :: "\<kappa> AOT_Term.\<upsilon> \<Rightarrow> \<o>" and v :: i
  {
    let ?\<kappa> = "\<nu>\<kappa> (\<alpha>\<nu> { (\<lambda> u . F (\<upsilon>_\<kappa>\<upsilon> u)) })"
    assume "\<forall>\<kappa>::\<kappa> . \<kappa> \<approx> \<kappa> \<longrightarrow> AOT_meta_enc \<kappa> F = AOT_meta_enc \<kappa> G"
    hence "AOT_meta_enc ?\<kappa> F = AOT_meta_enc ?\<kappa> G"
      using AOT_equiv_\<kappa>_def \<kappa>\<upsilon>.simps(1) by blast
    hence "(\<lambda>u. G (\<upsilon>_\<kappa>\<upsilon> u)) = (\<lambda>u. F (\<upsilon>_\<kappa>\<upsilon> u))"
      by (simp add: AOT_meta_simp)
    hence "(G (\<upsilon>_\<kappa>\<upsilon> u)) = (F (\<upsilon>_\<kappa>\<upsilon> u))" for u
      by meson
    hence "(G (abs_\<upsilon> u)) = (F (abs_\<upsilon> u))" for u
      by (metis \<kappa>\<upsilon>_\<upsilon>_inverse)
    hence "(G u) = (F u)" for u by (metis \<kappa>\<upsilon>_\<upsilon>_inverse \<upsilon>_\<kappa>\<upsilon>_def)
    hence "G = F" by blast
  }
  thus "(F = G) = (\<forall>\<kappa>::\<kappa>. \<kappa> \<approx> \<kappa> \<longrightarrow> AOT_meta_enc \<kappa> F = AOT_meta_enc \<kappa> G)"
    by auto
next
  fix \<kappa>\<^sub>1 \<kappa>\<^sub>2 :: \<kappa> and v :: i
  assume 0: "[v \<Turnstile> \<lparr>O!, \<kappa>\<^sub>1\<rparr>]"
  then obtain x\<^sub>1 where \<kappa>\<^sub>1_def: "\<kappa>\<^sub>1 = \<nu>\<kappa> (\<omega>\<nu> x\<^sub>1)"
    unfolding AOT_ordinary_def AOT_meta_beta[OF AOT_ordinary_denotes[unfolded AOT_ordinary_def], OF 0[THEN AOT_exeE2]]
    apply (simp add: AOT_diaS AOT_notS AOT_boxS)
    using AOT_concrete_ordinary by blast
  assume 0: "[v \<Turnstile> \<lparr>O!, \<kappa>\<^sub>2\<rparr>]"
  then obtain x\<^sub>2 where \<kappa>\<^sub>2_def: "\<kappa>\<^sub>2 = \<nu>\<kappa> (\<omega>\<nu> x\<^sub>2)"
    unfolding AOT_ordinary_def AOT_meta_beta[OF AOT_ordinary_denotes[unfolded AOT_ordinary_def], OF 0[THEN AOT_exeE2]]
    apply (simp add: AOT_diaS AOT_notS AOT_boxS)
    using AOT_concrete_ordinary by blast
  show "\<kappa>\<^sub>1 \<approx> \<kappa>\<^sub>2 = (\<kappa>\<^sub>1 = \<kappa>\<^sub>2)"
    unfolding \<kappa>\<^sub>1_def \<kappa>\<^sub>2_def by (auto simp: AOT_meta_simp)
next
  fix v :: i and \<kappa>\<^sub>1 \<kappa>\<^sub>2 :: "\<kappa>"
  assume 0: "[v \<Turnstile> \<lparr>A!, \<kappa>\<^sub>1\<rparr>]"
  then obtain x\<^sub>1 where \<kappa>\<^sub>1_def: "\<kappa>\<^sub>1 = \<nu>\<kappa> (\<alpha>\<nu> x\<^sub>1)"
    unfolding AOT_abstract_def AOT_meta_beta[OF AOT_abstract_denotes[unfolded AOT_abstract_def], OF 0[THEN AOT_exeE2]]
    apply (simp add: AOT_diaS AOT_notS AOT_boxS)
    using AOT_concrete_ordinary AOT_ordinary_concrete
    by (metis (full_types) "0" AOT_denotesS AOT_exeE2 AOT_equiv_\<kappa>_def \<kappa>.exhaust \<kappa>\<upsilon>.simps(2) \<nu>.exhaust option.distinct(1))
  assume 0: "[v \<Turnstile> \<lparr>A!, \<kappa>\<^sub>2\<rparr>]"
  then obtain x\<^sub>2 where \<kappa>\<^sub>2_def: "\<kappa>\<^sub>2 = \<nu>\<kappa> (\<alpha>\<nu> x\<^sub>2)"
    unfolding AOT_abstract_def AOT_meta_beta[OF AOT_abstract_denotes[unfolded AOT_abstract_def], OF 0[THEN AOT_exeE2]]
    apply (simp add: AOT_diaS AOT_notS AOT_boxS)
    using AOT_concrete_ordinary AOT_ordinary_concrete
    by (metis (full_types) "0" AOT_denotesS AOT_exeE2 AOT_equiv_\<kappa>_def \<kappa>.exhaust \<kappa>\<upsilon>.simps(2) \<nu>.exhaust option.distinct(1))
  {
    let ?\<upsilon>u = "\<lambda> u . (abs_\<upsilon> (SOME x. \<kappa>\<upsilon> x = Some u))"
    assume 0: "((\<lambda>u. \<Pi> (?\<upsilon>u u)) \<in> x\<^sub>1) = ((\<lambda>u. \<Pi> (?\<upsilon>u u)) \<in> x\<^sub>2)" for \<Pi>
    {
      fix r :: "\<upsilon> \<Rightarrow> \<o>"
      have "\<exists> \<Pi> . \<forall> u . r u = (\<Pi> (?\<upsilon>u u))"
        by (rule_tac x="\<lambda> x . r ((inv ?\<upsilon>u) x)" in exI)
           (metis (no_types, lifting) \<kappa>\<upsilon>_\<upsilon>_inverse \<upsilon>_\<kappa>\<upsilon>_def \<upsilon>_\<kappa>\<upsilon>_inverse inv_equality)
      then obtain \<Pi> where "r = (\<lambda>u. \<Pi> (?\<upsilon>u u))" by blast
      hence "(r \<in> x\<^sub>1) = (r \<in> x\<^sub>2)" using 0 by simp
    }
    hence "x\<^sub>1 = x\<^sub>2" by blast
  }
  hence "(\<forall> \<phi> . AOT_meta_enc \<kappa>\<^sub>1 \<phi> = AOT_meta_enc \<kappa>\<^sub>2 \<phi>) = (\<kappa>\<^sub>1 = \<kappa>\<^sub>2)"
    by (auto simp: AOT_meta_simp \<kappa>\<^sub>1_def \<kappa>\<^sub>2_def)
  thus "(AOT_meta_enc \<kappa>\<^sub>1 = AOT_meta_enc \<kappa>\<^sub>2) = (\<kappa>\<^sub>1 = \<kappa>\<^sub>2)" by auto
qed

(* Verify that there's still a model. *)
lemma "True" nitpick[user_axioms, satisfy, expect = genuine] oops
lemma "False" nitpick[user_axioms, expect = genuine] oops

end
