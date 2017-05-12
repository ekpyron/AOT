theory Scott
imports Main
begin

typedecl i
typedecl j
consts dj :: j
consts dw :: i

typedecl D\<^sub>0
type_synonym D\<^sub>1_1 = "bool\<times>(D\<^sub>0\<Rightarrow>bool)"
type_synonym predicates = "j\<Rightarrow>i\<Rightarrow>D\<^sub>1_1"
type_synonym D\<^sub>2 = "predicates\<Rightarrow>bool"

datatype individuals = real D\<^sub>0 | abstract D\<^sub>2

abbreviation (input) scott_exe_base :: "D\<^sub>1_1\<Rightarrow>individuals\<Rightarrow>bool" where
  "scott_exe_base \<equiv> (\<lambda> F x . case x of
    (real a) \<Rightarrow>
        ((snd (F)) a)
    | (abstract a) \<Rightarrow>
        (fst (F))
  )"

abbreviation (input) scott_exe :: "predicates\<Rightarrow>individuals\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool" where
  "scott_exe \<equiv> (\<lambda> F x s w . scott_exe_base (F s w) x)"

abbreviation (input) scott_enc :: "individuals\<Rightarrow>predicates\<Rightarrow>bool" where
  "scott_enc \<equiv> (\<lambda> x F . case x of
      (real y) \<Rightarrow> False
    | (abstract y) \<Rightarrow> y F)"
  

typedef \<o> = "UNIV::(j\<Rightarrow>i\<Rightarrow>bool) set" morphisms eval\<o> make\<o> ..
type_synonym \<nu> = individuals
type_synonym \<Pi>\<^sub>0 = \<o>
typedef \<Pi>\<^sub>1 = "UNIV::(predicates) set" morphisms eval\<Pi>\<^sub>1 make\<Pi>\<^sub>1 ..

typedef \<kappa> = "UNIV::(\<nu> option) set" morphisms eval\<kappa> make\<kappa> ..

setup_lifting type_definition_\<o>
setup_lifting type_definition_\<Pi>\<^sub>1
setup_lifting type_definition_\<kappa>

lift_definition \<nu>\<kappa> :: "\<nu>\<Rightarrow>\<kappa>" ("_\<^sup>P" [90] 90) is Some .
lift_definition proper :: "\<kappa>\<Rightarrow>bool" is "op\<noteq> None" .
lift_definition rep :: "\<kappa>\<Rightarrow>\<nu>" is the .

lift_definition that::"(\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<kappa>" (binder "\<^bold>\<iota>" [8] 9) is
  "\<lambda> \<phi> . if (\<exists>! x . (\<phi> x) dj dw)
         then Some (THE x . (\<phi> x) dj dw)
         else None" .

lift_definition exe0::"\<Pi>\<^sub>0\<Rightarrow>\<o>" ("\<lparr>_\<rparr>") is id .
lift_definition exe1::"\<Pi>\<^sub>1\<Rightarrow>\<kappa>\<Rightarrow>\<o>" ("\<lparr>_,_\<rparr>") is
  "\<lambda> F x s w . (proper x) \<and> scott_exe F (rep x) s w" .
(*
lift_definition exe2::"\<Pi>\<^sub>2\<Rightarrow>\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<o>" ("\<lparr>_,_,_\<rparr>") is
  "\<lambda> F x y w s . (proper x) \<and> (proper y) \<and>
     F (\<nu>\<upsilon> (rep x)) (\<nu>\<upsilon> (rep y)) w s" .
lift_definition exe3::"\<Pi>\<^sub>3\<Rightarrow>\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<o>" ("\<lparr>_,_,_,_\<rparr>") is
"\<lambda> F x y z w s . (proper x) \<and> (proper y) \<and> (proper z) \<and>
   F (\<nu>\<upsilon> (rep x)) (\<nu>\<upsilon> (rep y)) (\<nu>\<upsilon> (rep z)) w s" .
*)

lift_definition enc :: "\<kappa>\<Rightarrow>\<Pi>\<^sub>1\<Rightarrow>\<o>" ("\<lbrace>_,_\<rbrace>") is
  "\<lambda> x F w s . (proper x) \<and> scott_enc (rep x) F" .

    consts I_NOT :: "(j\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>(j\<Rightarrow>i\<Rightarrow>bool)"
consts I_IMPL :: "(j\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>(j\<Rightarrow>i\<Rightarrow>bool)\<Rightarrow>(j\<Rightarrow>i\<Rightarrow>bool)"

lift_definition not :: "\<o>\<Rightarrow>\<o>" ("\<^bold>\<not>_" [54] 70) is
  "\<lambda> p s w . s = dj \<and> \<not>p dj w \<or> s \<noteq> dj \<and> (I_NOT p s w)" .
lift_definition impl :: "\<o>\<Rightarrow>\<o>\<Rightarrow>\<o>" (infixl "\<^bold>\<rightarrow>" 51) is
  "\<lambda> p q s w . s = dj \<and> (p dj w \<longrightarrow> q dj w) \<or> s \<noteq> dj \<and> (I_IMPL p q s w)" .
lift_definition forall\<^sub>\<nu> :: "(\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>\<nu>" [8] 9) is
  "\<lambda> \<phi> s w . \<forall> x :: \<nu> . (\<phi> x) s w" .
lift_definition forall\<^sub>0 :: "(\<Pi>\<^sub>0\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>0" [8] 9) is
  "\<lambda> \<phi> s w . \<forall> x :: \<Pi>\<^sub>0 . (\<phi> x) s w" .
lift_definition forall\<^sub>1 :: "(\<Pi>\<^sub>1\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>1" [8] 9) is
  "\<lambda> \<phi> s w . \<forall> x :: \<Pi>\<^sub>1  . (\<phi> x) s w" .
(*
lift_definition forall\<^sub>2 :: "(\<Pi>\<^sub>2\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>2" [8] 9) is
  "\<lambda> \<phi> s w . \<forall> x :: \<Pi>\<^sub>2  . (\<phi> x) s w" .
lift_definition forall\<^sub>3 :: "(\<Pi>\<^sub>3\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>3" [8] 9) is
  "\<lambda> \<phi> s w . \<forall> x :: \<Pi>\<^sub>3  . (\<phi> x) s w" .
*)
lift_definition forall\<^sub>\<o> :: "(\<o>\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>\<o>" [8] 9) is
  "\<lambda> \<phi> s w . \<forall> x :: \<o>  . (\<phi> x) s w" .
lift_definition box :: "\<o>\<Rightarrow>\<o>" ("\<^bold>\<box>_" [62] 63) is
  "\<lambda> p s w . \<forall> v . p s v" .
lift_definition actual :: "\<o>\<Rightarrow>\<o>" ("\<^bold>\<A>_" [64] 65) is
  "\<lambda> p s w . p dj dw" .

lift_definition lambdabinder0 :: "\<o>\<Rightarrow>\<Pi>\<^sub>0" ("\<^bold>\<lambda>\<^sup>0") is id .
lift_definition lambdabinder1 :: "(\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<Pi>\<^sub>1" (binder "\<^bold>\<lambda>" [8] 9) is
  "\<lambda> \<phi> . SOME F . (\<forall> x s w. scott_exe F x s w \<longleftrightarrow> \<phi> x s w)" .

(*
lift_definition lambdabinder1 :: "(\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<Pi>\<^sub>1" (binder "\<^bold>\<lambda>" [8] 9) is
  "\<lambda> \<phi> s w . plus (\<lambda> x . False)" .
lift_definition lambdabinder2 :: "(\<nu>\<Rightarrow>\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<Pi>\<^sub>2" ("\<^bold>\<lambda>\<^sup>2") is
  "\<lambda> \<phi> u v . \<phi> (\<upsilon>\<nu> u) (\<upsilon>\<nu> v)" .
lift_definition lambdabinder3 :: "(\<nu>\<Rightarrow>\<nu>\<Rightarrow>\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<Pi>\<^sub>3" ("\<^bold>\<lambda>\<^sup>3") is
  "\<lambda> \<phi> u v w .  \<phi> (\<upsilon>\<nu> u) (\<upsilon>\<nu> v) (\<upsilon>\<nu> w)" .
*)

lift_definition valid_in :: "i\<Rightarrow>\<o>\<Rightarrow>bool" (infixl "\<Turnstile>" 5) is
  "\<lambda> v \<phi> . \<phi> dj v" .
    
consts ConcreteInWorld :: "D\<^sub>0\<Rightarrow>i\<Rightarrow>bool"

abbreviation (input) OrdinaryObjectsPossiblyConcrete where
  "OrdinaryObjectsPossiblyConcrete \<equiv> \<forall> x . \<exists> v . ConcreteInWorld x v"
abbreviation (input) PossiblyContingentObjectExists where
  "PossiblyContingentObjectExists \<equiv> \<exists> x v . ConcreteInWorld x v
                                        \<and> (\<exists> w . \<not> ConcreteInWorld x w)"
abbreviation (input) PossiblyNoContingentObjectExists where
  "PossiblyNoContingentObjectExists \<equiv> \<exists> w . \<forall> x . ConcreteInWorld x w
                                        \<longrightarrow> (\<forall> v . ConcreteInWorld x v)"

axiomatization where
  OrdinaryObjectsPossiblyConcreteAxiom:
    "OrdinaryObjectsPossiblyConcrete"
  and PossiblyContingentObjectExistsAxiom:
    "PossiblyContingentObjectExists"
  and PossiblyNoContingentObjectExistsAxiom:
    "PossiblyNoContingentObjectExists"

lift_definition Concrete :: "\<Pi>\<^sub>1" ("E!") is
  "\<lambda> s w . (False, \<lambda> x . ConcreteInWorld x w)" .

named_theorems meta_defs

declare not_def[meta_defs] impl_def[meta_defs] forall\<^sub>\<nu>_def[meta_defs]
        forall\<^sub>0_def[meta_defs] forall\<^sub>1_def[meta_defs]
        (*forall\<^sub>2_def[meta_defs] forall\<^sub>3_def[meta_defs]*) forall\<^sub>\<o>_def[meta_defs]
        box_def[meta_defs] actual_def[meta_defs] that_def[meta_defs]
        lambdabinder0_def[meta_defs] lambdabinder1_def[meta_defs]
        (*lambdabinder2_def[meta_defs] lambdabinder3_def[meta_defs]*)
        exe0_def[meta_defs] exe1_def[meta_defs] (*exe2_def[meta_defs]
        exe3_def[meta_defs]*) enc_def[meta_defs] inv_def[meta_defs]
        that_def[meta_defs] valid_in_def[meta_defs] Concrete_def[meta_defs]

abbreviation validity_in :: "\<o>\<Rightarrow>i\<Rightarrow>bool" ("[_ in _]" [1]) where
  "validity_in \<equiv> \<lambda> \<phi> v . v \<Turnstile> \<phi>"

    

lemma pl_1:
    "[\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<phi>) in v]"
    apply transfer by blast
lemma pl_2:
  "[(\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<chi>)) \<^bold>\<rightarrow> ((\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<chi>)) in v]"
  apply transfer by blast
lemma pl_3:
  "[(\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi>) \<^bold>\<rightarrow> ((\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> \<phi>) in v]"
  apply transfer by blast

definition exists_nu :: "(\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<exists>\<^sub>\<nu>" [8] 9) 
  where "exists_nu \<equiv> (\<lambda> \<phi> . \<^bold>\<not>(\<^bold>\<forall>\<^sub>\<nu> x . \<^bold>\<not>\<phi> x))"
definition exists_1 :: "(\<Pi>\<^sub>1\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<exists>\<^sub>1" [8] 9) 
  where "exists_1 \<equiv> (\<lambda> \<phi> . \<^bold>\<not>(\<^bold>\<forall>\<^sub>1 x . \<^bold>\<not>\<phi> x))"
definition diamond::"\<o>\<Rightarrow>\<o>" ("\<^bold>\<diamond>_" [62] 63) where
  "diamond \<equiv> \<lambda> \<phi> . \<^bold>\<not>\<^bold>\<box>\<^bold>\<not>\<phi>"
definition conj::"\<o>\<Rightarrow>\<o>\<Rightarrow>\<o>" (infixl "\<^bold>&" 53) where
  "conj \<equiv> \<lambda> x y . \<^bold>\<not>(x \<^bold>\<rightarrow> \<^bold>\<not>y)"
definition disj::"\<o>\<Rightarrow>\<o>\<Rightarrow>\<o>" (infixl "\<^bold>\<or>" 52) where
  "disj \<equiv> \<lambda> x y . \<^bold>\<not>x \<^bold>\<rightarrow> y"
definition equiv::"\<o>\<Rightarrow>\<o>\<Rightarrow>\<o>" (infixl "\<^bold>\<equiv>" 51) where
  "equiv \<equiv> \<lambda> x y . (x \<^bold>\<rightarrow> y) \<^bold>& (y \<^bold>\<rightarrow> x)"

definition Ordinary :: "\<Pi>\<^sub>1" ("O!") where "Ordinary \<equiv> \<^bold>\<lambda>x. \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>"
definition Abstract :: "\<Pi>\<^sub>1" ("A!") where "Abstract \<equiv> \<^bold>\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>"

lemma ImplI: "([\<phi> in v] \<Longrightarrow> [\<psi> in v]) \<Longrightarrow> ([\<phi> \<^bold>\<rightarrow> \<psi> in v])"
    apply transfer by auto
lemma ImplE: "([\<phi> \<^bold>\<rightarrow> \<psi> in v]) \<Longrightarrow> ([\<phi> in v] \<longrightarrow> [\<psi> in v])"
    apply transfer by auto
lemma ImplS: "([\<phi> \<^bold>\<rightarrow> \<psi> in v]) = ([\<phi> in v] \<longrightarrow> [\<psi> in v])"
    apply transfer by auto
lemma NotI: "\<not>[\<phi> in v] \<Longrightarrow> [\<^bold>\<not>\<phi> in v]"
  apply transfer by auto
lemma NotE: "[\<^bold>\<not>\<phi> in v] \<Longrightarrow> \<not>[\<phi> in v]"
  apply transfer by auto
lemma NotS: "[\<^bold>\<not>\<phi> in v] = (\<not>[\<phi> in v])"
  apply transfer by auto
lemma ConjI: "([\<phi> in v] \<and> [\<psi> in v]) \<Longrightarrow> [\<phi> \<^bold>& \<psi> in v]"
  unfolding conj_def
  apply transfer by auto
lemma ConjE: "[\<phi> \<^bold>& \<psi> in v] \<Longrightarrow> ([\<phi> in v] \<and> [\<psi> in v])"
  unfolding conj_def
  apply transfer by auto
lemma ConjS: "[\<phi> \<^bold>& \<psi> in v] = ([\<phi> in v] \<and> [\<psi> in v])"
  unfolding conj_def
  apply transfer by auto
lemma EquivI: "([\<phi> in v] \<longleftrightarrow> [\<psi> in v]) \<Longrightarrow> [\<phi> \<^bold>\<equiv> \<psi> in v]"
  unfolding equiv_def conj_def
  apply transfer by auto
lemma EquivE: "[\<phi> \<^bold>\<equiv> \<psi> in v] \<Longrightarrow> ([\<phi> in v] \<longleftrightarrow> [\<psi> in v])"
  unfolding equiv_def conj_def
  apply transfer by auto
lemma EquivS: "[\<phi> \<^bold>\<equiv> \<psi> in v] = ([\<phi> in v] \<longleftrightarrow> [\<psi> in v])"
  unfolding equiv_def conj_def
  apply transfer by auto
lemma DisjI: "([\<phi> in v] \<or> [\<psi> in v]) \<Longrightarrow> [\<phi> \<^bold>\<or> \<psi> in v]"
  unfolding disj_def
  apply transfer by auto
lemma DisjE: "[\<phi> \<^bold>\<or> \<psi> in v] \<Longrightarrow> ([\<phi> in v] \<or> [\<psi> in v])"
  unfolding disj_def
  apply transfer by auto
lemma DisjS: "[\<phi> \<^bold>\<or> \<psi> in v] = ([\<phi> in v] \<or> [\<psi> in v])"
  unfolding disj_def
  apply transfer by auto
lemma BoxI: "(\<And>v.[\<phi> in v]) \<Longrightarrow> [\<^bold>\<box>\<phi> in v]"
  apply transfer by auto
lemma BoxE: "[\<^bold>\<box>\<phi> in v] \<Longrightarrow> (\<And>v.[\<phi> in v])"
  apply transfer by auto
lemma BoxS: "[\<^bold>\<box>\<phi> in v] = (\<forall> v.[\<phi> in v])"
  apply transfer by auto
lemma DiaI: "(\<exists>v.[\<phi> in v]) \<Longrightarrow> [\<^bold>\<diamond>\<phi> in v]"
  unfolding diamond_def
  apply transfer by auto
lemma DiaE: "[\<^bold>\<diamond>\<phi> in v] \<Longrightarrow> (\<exists>v.[\<phi> in v])"
  unfolding diamond_def
  apply transfer by auto
lemma DiaS: "[\<^bold>\<diamond>\<phi> in v] = (\<exists> v.[\<phi> in v])"
  unfolding diamond_def
  apply transfer by auto
lemma All\<^sub>\<nu>I: "(\<And>x::\<nu>. [\<phi> x in v]) \<Longrightarrow> [\<^bold>\<forall>\<^sub>\<nu> x. \<phi> x in v]"
  apply transfer by auto
lemma All\<^sub>\<nu>E: "[\<^bold>\<forall>\<^sub>\<nu>x. \<phi> x in v] \<Longrightarrow> (\<And>x::\<nu>.[\<phi> x in v])"
  apply transfer by auto
lemma All\<^sub>\<nu>S: "[\<^bold>\<forall>\<^sub>\<nu>x. \<phi> x in v] = (\<forall>x::\<nu>.[\<phi> x in v])"
  apply transfer by auto
lemma All\<^sub>0I: "(\<And>x::\<Pi>\<^sub>0. [\<phi> x in v]) \<Longrightarrow> [\<^bold>\<forall>\<^sub>0 x. \<phi> x in v]"
  apply transfer by auto
lemma All\<^sub>0E: "[\<^bold>\<forall>\<^sub>0 x. \<phi> x in v] \<Longrightarrow> (\<And>x::\<Pi>\<^sub>0 .[\<phi> x in v])"
  apply transfer by auto
lemma All\<^sub>0S: "[\<^bold>\<forall>\<^sub>0 x. \<phi> x in v] = (\<forall>x::\<Pi>\<^sub>0.[\<phi> x in v])"
  apply auto apply transfer apply simp
  apply transfer by simp
lemma All\<^sub>1I: "(\<And>x::\<Pi>\<^sub>1. [\<phi> x in v]) \<Longrightarrow> [\<^bold>\<forall>\<^sub>1 x. \<phi> x in v]"
  apply transfer by auto
lemma All\<^sub>1E: "[\<^bold>\<forall>\<^sub>1 x. \<phi> x in v] \<Longrightarrow> (\<And>x::\<Pi>\<^sub>1 .[\<phi> x in v])"
  apply transfer by auto
lemma All\<^sub>1S: "[\<^bold>\<forall>\<^sub>1 x. \<phi> x in v] = (\<forall>x::\<Pi>\<^sub>1.[\<phi> x in v])"
  apply auto apply transfer apply simp
  apply transfer by simp

named_theorems meta_aux

declare make\<kappa>_inverse[meta_aux] eval\<kappa>_inverse[meta_aux]
        make\<o>_inverse[meta_aux] eval\<o>_inverse[meta_aux]
        make\<Pi>\<^sub>1_inverse[meta_aux] eval\<Pi>\<^sub>1_inverse[meta_aux]
(*        make\<Pi>\<^sub>2_inverse[meta_aux] eval\<Pi>\<^sub>2_inverse[meta_aux]
        make\<Pi>\<^sub>3_inverse[meta_aux] eval\<Pi>\<^sub>3_inverse[meta_aux]*)

lemma [meta_aux]: "proper (x\<^sup>P)" apply transfer by auto
lemma [meta_aux]: "rep (x\<^sup>P) = x" apply transfer by auto

end
  