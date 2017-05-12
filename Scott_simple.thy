theory Scott_simple
imports Main
begin

typedecl i
consts dw :: i

typedecl D\<^sub>0
datatype D\<^sub>1 = plus "D\<^sub>0\<Rightarrow>bool" | minus "D\<^sub>0\<Rightarrow>bool"
type_synonym predicates = "i\<Rightarrow>D\<^sub>1"
type_synonym D\<^sub>2 = "predicates\<Rightarrow>bool"
  
datatype individuals = real D\<^sub>0 | abstract D\<^sub>2

abbreviation (input) scott_exe_base :: "D\<^sub>1\<Rightarrow>individuals\<Rightarrow>bool" where
  "scott_exe_base \<equiv> (\<lambda> F x . case x of
    (real a) \<Rightarrow>
        (case F of (plus G) \<Rightarrow> G a | (minus G) \<Rightarrow> G a)
    | (abstract a) \<Rightarrow>
        (case F of (plus G) \<Rightarrow> True | (minus G) \<Rightarrow> False)
  )"

abbreviation (input) scott_exe :: "predicates\<Rightarrow>individuals\<Rightarrow>i\<Rightarrow>bool" where
  "scott_exe \<equiv> (\<lambda> F x w . scott_exe_base (F w) x)"

abbreviation (input) scott_enc :: "individuals\<Rightarrow>predicates\<Rightarrow>bool" where
  "scott_enc \<equiv> (\<lambda> x F . case x of
      (real y) \<Rightarrow> False
    | (abstract y) \<Rightarrow> y F)"
  

type_synonym \<o> = "i\<Rightarrow>bool"
type_synonym \<nu> = individuals
type_synonym \<Pi>\<^sub>0 = \<o>
type_synonym \<Pi>\<^sub>1 = predicates

lift_definition exe0::"\<Pi>\<^sub>0\<Rightarrow>\<o>" ("\<lparr>_\<rparr>") is id .
definition exe1::"\<Pi>\<^sub>1\<Rightarrow>\<nu>\<Rightarrow>\<o>" ("\<lparr>_,_\<rparr>") where
  "exe1 \<equiv> \<lambda> F x w . scott_exe F x w"

definition enc :: "\<nu>\<Rightarrow>\<Pi>\<^sub>1\<Rightarrow>\<o>" ("\<lbrace>_,_\<rbrace>") where
  "enc \<equiv> \<lambda> x F w . scott_enc x F"

definition not :: "\<o>\<Rightarrow>\<o>" ("\<^bold>\<not>_" [54] 70) where
  "not \<equiv> \<lambda> p w . \<not>p w"
definition impl :: "\<o>\<Rightarrow>\<o>\<Rightarrow>\<o>" (infixl "\<^bold>\<rightarrow>" 51) where
  "impl \<equiv> \<lambda> p q w . p w \<longrightarrow> q w"
definition forall\<^sub>\<nu> :: "(\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>\<nu>" [8] 9) where
  "forall\<^sub>\<nu> \<equiv> \<lambda> \<phi> w . \<forall> x :: \<nu> . (\<phi> x) w"
definition forall\<^sub>0 :: "(\<Pi>\<^sub>0\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>0" [8] 9) where
  "forall\<^sub>0 \<equiv> \<lambda> \<phi> w . \<forall> x :: \<Pi>\<^sub>0 . (\<phi> x) w"
definition forall\<^sub>1 :: "(\<Pi>\<^sub>1\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>1" [8] 9) where
  "forall\<^sub>1 \<equiv> \<lambda> \<phi> w . \<forall> x :: \<Pi>\<^sub>1  . (\<phi> x) w"
definition box :: "\<o>\<Rightarrow>\<o>" ("\<^bold>\<box>_" [62] 63) where
  "box \<equiv> \<lambda> p w . \<forall> v . p v"
definition actual :: "\<o>\<Rightarrow>\<o>" ("\<^bold>\<A>_" [64] 65) where
  "actual \<equiv> \<lambda> p w . p dw"

definition lambdabinder0 :: "\<o>\<Rightarrow>\<Pi>\<^sub>0" ("\<^bold>\<lambda>\<^sup>0") where "lambdabinder0 \<equiv> id"
definition lambdabinder1 :: "(\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<Pi>\<^sub>1" (binder "\<^bold>\<lambda>" [8] 9) where
  "lambdabinder1 \<equiv> \<lambda> \<phi> w . if (\<exists> x . \<phi> (abstract x) w) then (plus (\<lambda> x . \<phi> (real x) w)) else (minus (\<lambda> x . \<phi> (real x) w))"

lift_definition valid_in :: "i\<Rightarrow>\<o>\<Rightarrow>bool" (infixl "\<Turnstile>" 5) is
  "\<lambda> v \<phi> . \<phi> v" .
    
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
  "\<lambda> w . minus (\<lambda> x . ConcreteInWorld x w)" .

named_theorems meta_defs

declare not_def[meta_defs] impl_def[meta_defs] forall\<^sub>\<nu>_def[meta_defs]
        forall\<^sub>0_def[meta_defs] forall\<^sub>1_def[meta_defs]
        (*forall\<^sub>2_def[meta_defs] forall\<^sub>3_def[meta_defs] forall\<^sub>\<o>_def[meta_defs]*)
        box_def[meta_defs] actual_def[meta_defs] (*that_def[meta_defs]*)
        lambdabinder0_def[meta_defs] lambdabinder1_def[meta_defs]
        (*lambdabinder2_def[meta_defs] lambdabinder3_def[meta_defs]*)
        exe0_def[meta_defs] exe1_def[meta_defs] (*exe2_def[meta_defs]
        exe3_def[meta_defs]*) enc_def[meta_defs] inv_def[meta_defs]
        valid_in_def[meta_defs] Concrete_def[meta_defs]

abbreviation validity_in :: "\<o>\<Rightarrow>i\<Rightarrow>bool" ("[_ in _]" [1]) where
  "validity_in \<equiv> \<lambda> \<phi> v . v \<Turnstile> \<phi>"

    

lemma pl_1:
    "[\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<phi>) in v]"
    by (simp add: meta_defs)
lemma pl_2:
  "[(\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<chi>)) \<^bold>\<rightarrow> ((\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<chi>)) in v]"
    by (simp add: meta_defs)
lemma pl_3:
  "[(\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi>) \<^bold>\<rightarrow> ((\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> \<phi>) in v]"
    by (simp add: meta_defs)

named_theorems conn_defs
      
definition exists_nu :: "(\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<exists>\<^sub>\<nu>" [8] 9) 
  where [conn_defs]: "exists_nu \<equiv> (\<lambda> \<phi> . \<^bold>\<not>(\<^bold>\<forall>\<^sub>\<nu> x . \<^bold>\<not>\<phi> x))"
definition exists_1 :: "(\<Pi>\<^sub>1\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<exists>\<^sub>1" [8] 9) 
  where [conn_defs]: "exists_1 \<equiv> (\<lambda> \<phi> . \<^bold>\<not>(\<^bold>\<forall>\<^sub>1 x . \<^bold>\<not>\<phi> x))"
definition diamond::"\<o>\<Rightarrow>\<o>" ("\<^bold>\<diamond>_" [62] 63) where
  [conn_defs]: "diamond \<equiv> \<lambda> \<phi> . \<^bold>\<not>\<^bold>\<box>\<^bold>\<not>\<phi>"
definition conj::"\<o>\<Rightarrow>\<o>\<Rightarrow>\<o>" (infixl "\<^bold>&" 53) where
  [conn_defs]: "conj \<equiv> \<lambda> x y . \<^bold>\<not>(x \<^bold>\<rightarrow> \<^bold>\<not>y)"
definition disj::"\<o>\<Rightarrow>\<o>\<Rightarrow>\<o>" (infixl "\<^bold>\<or>" 52) where
  [conn_defs]: "disj \<equiv> \<lambda> x y . \<^bold>\<not>x \<^bold>\<rightarrow> y"
definition equiv::"\<o>\<Rightarrow>\<o>\<Rightarrow>\<o>" (infixl "\<^bold>\<equiv>" 51) where
  [conn_defs]: "equiv \<equiv> \<lambda> x y . (x \<^bold>\<rightarrow> y) \<^bold>& (y \<^bold>\<rightarrow> x)"

definition Ordinary :: "\<Pi>\<^sub>1" ("O!") where "Ordinary \<equiv> \<^bold>\<lambda>x. \<^bold>\<diamond>\<lparr>E!,x\<rparr>"
definition Abstract :: "\<Pi>\<^sub>1" ("A!") where "Abstract \<equiv> \<^bold>\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<rparr>"

lemma ImplI: "([\<phi> in v] \<Longrightarrow> [\<psi> in v]) \<Longrightarrow> ([\<phi> \<^bold>\<rightarrow> \<psi> in v])"
    by (simp add: meta_defs conn_defs)
lemma ImplE: "([\<phi> \<^bold>\<rightarrow> \<psi> in v]) \<Longrightarrow> ([\<phi> in v] \<longrightarrow> [\<psi> in v])"
    by (simp add: meta_defs conn_defs)
lemma ImplS: "([\<phi> \<^bold>\<rightarrow> \<psi> in v]) = ([\<phi> in v] \<longrightarrow> [\<psi> in v])"
    by (simp add: meta_defs conn_defs)
lemma NotI: "\<not>[\<phi> in v] \<Longrightarrow> [\<^bold>\<not>\<phi> in v]"
    by (simp add: meta_defs conn_defs)
lemma NotE: "[\<^bold>\<not>\<phi> in v] \<Longrightarrow> \<not>[\<phi> in v]"
    by (simp add: meta_defs conn_defs)
lemma NotS: "[\<^bold>\<not>\<phi> in v] = (\<not>[\<phi> in v])"
    by (simp add: meta_defs conn_defs)
lemma ConjI: "([\<phi> in v] \<and> [\<psi> in v]) \<Longrightarrow> [\<phi> \<^bold>& \<psi> in v]"
    by (simp add: meta_defs conn_defs)
lemma ConjE: "[\<phi> \<^bold>& \<psi> in v] \<Longrightarrow> ([\<phi> in v] \<and> [\<psi> in v])"
    by (simp add: meta_defs conn_defs)
lemma ConjS: "[\<phi> \<^bold>& \<psi> in v] = ([\<phi> in v] \<and> [\<psi> in v])"
    by (simp add: meta_defs conn_defs)
lemma EquivI: "([\<phi> in v] \<longleftrightarrow> [\<psi> in v]) \<Longrightarrow> [\<phi> \<^bold>\<equiv> \<psi> in v]"
    by (simp add: meta_defs conn_defs)
lemma EquivE: "[\<phi> \<^bold>\<equiv> \<psi> in v] \<Longrightarrow> ([\<phi> in v] \<longleftrightarrow> [\<psi> in v])"
    by (auto simp: meta_defs conn_defs)
lemma EquivS: "[\<phi> \<^bold>\<equiv> \<psi> in v] = ([\<phi> in v] \<longleftrightarrow> [\<psi> in v])"
    by (auto simp: meta_defs conn_defs)
lemma DisjI: "([\<phi> in v] \<or> [\<psi> in v]) \<Longrightarrow> [\<phi> \<^bold>\<or> \<psi> in v]"
    by (auto simp: meta_defs conn_defs)
lemma DisjE: "[\<phi> \<^bold>\<or> \<psi> in v] \<Longrightarrow> ([\<phi> in v] \<or> [\<psi> in v])"
    by (auto simp: meta_defs conn_defs)
lemma DisjS: "[\<phi> \<^bold>\<or> \<psi> in v] = ([\<phi> in v] \<or> [\<psi> in v])"
    by (auto simp: meta_defs conn_defs)
lemma BoxI: "(\<And>v.[\<phi> in v]) \<Longrightarrow> [\<^bold>\<box>\<phi> in v]"
    by (auto simp: meta_defs conn_defs)
lemma BoxE: "[\<^bold>\<box>\<phi> in v] \<Longrightarrow> (\<And>v.[\<phi> in v])"
    by (auto simp: meta_defs conn_defs)
lemma BoxS: "[\<^bold>\<box>\<phi> in v] = (\<forall> v.[\<phi> in v])"
    by (auto simp: meta_defs conn_defs)
lemma DiaI: "(\<exists>v.[\<phi> in v]) \<Longrightarrow> [\<^bold>\<diamond>\<phi> in v]"
    by (auto simp: meta_defs conn_defs)
lemma DiaE: "[\<^bold>\<diamond>\<phi> in v] \<Longrightarrow> (\<exists>v.[\<phi> in v])"
    by (auto simp: meta_defs conn_defs)
lemma DiaS: "[\<^bold>\<diamond>\<phi> in v] = (\<exists> v.[\<phi> in v])"
    by (auto simp: meta_defs conn_defs)
lemma All\<^sub>\<nu>I: "(\<And>x::\<nu>. [\<phi> x in v]) \<Longrightarrow> [\<^bold>\<forall>\<^sub>\<nu> x. \<phi> x in v]"
    by (auto simp: meta_defs conn_defs)
lemma All\<^sub>\<nu>E: "[\<^bold>\<forall>\<^sub>\<nu>x. \<phi> x in v] \<Longrightarrow> (\<And>x::\<nu>.[\<phi> x in v])"
    by (auto simp: meta_defs conn_defs)
lemma All\<^sub>\<nu>S: "[\<^bold>\<forall>\<^sub>\<nu>x. \<phi> x in v] = (\<forall>x::\<nu>.[\<phi> x in v])"
    by (auto simp: meta_defs conn_defs)
lemma All\<^sub>0I: "(\<And>x::\<Pi>\<^sub>0. [\<phi> x in v]) \<Longrightarrow> [\<^bold>\<forall>\<^sub>0 x. \<phi> x in v]"
    by (auto simp: meta_defs conn_defs)
lemma All\<^sub>0E: "[\<^bold>\<forall>\<^sub>0 x. \<phi> x in v] \<Longrightarrow> (\<And>x::\<Pi>\<^sub>0 .[\<phi> x in v])"
    by (auto simp: meta_defs conn_defs)
lemma All\<^sub>0S: "[\<^bold>\<forall>\<^sub>0 x. \<phi> x in v] = (\<forall>x::\<Pi>\<^sub>0.[\<phi> x in v])"
    by (auto simp: meta_defs conn_defs)
lemma All\<^sub>1I: "(\<And>x::\<Pi>\<^sub>1. [\<phi> x in v]) \<Longrightarrow> [\<^bold>\<forall>\<^sub>1 x. \<phi> x in v]"
    by (auto simp: meta_defs conn_defs)
lemma All\<^sub>1E: "[\<^bold>\<forall>\<^sub>1 x. \<phi> x in v] \<Longrightarrow> (\<And>x::\<Pi>\<^sub>1 .[\<phi> x in v])"
    by (auto simp: meta_defs conn_defs)
lemma All\<^sub>1S: "[\<^bold>\<forall>\<^sub>1 x. \<phi> x in v] = (\<forall>x::\<Pi>\<^sub>1.[\<phi> x in v])"
    by (auto simp: meta_defs conn_defs)

lemma ExI: "[\<phi> x in v] \<Longrightarrow> [\<^bold>\<exists>\<^sub>\<nu> x . \<phi> x in v]" unfolding exists_nu_def
    by (auto simp: meta_defs)
lemma ExE: assumes "[\<^bold>\<exists>\<^sub>\<nu> x . \<phi> x in v]" obtains x where "[\<phi> x in v]"
    using assms unfolding exists_nu_def
    by (auto simp: meta_defs)

      
lemma "[\<^bold>\<exists>\<^sub>1 G . \<^bold>\<forall>\<^sub>\<nu> x . \<lparr>G,x\<rparr> \<^bold>\<equiv> \<phi> x in v]"
proof -
  obtain F :: "i\<Rightarrow>D\<^sub>0\<Rightarrow>bool" where F_def: "F = (\<lambda> w x . \<phi> (real x) w)" by auto
  obtain G :: "\<Pi>\<^sub>1" where G_def: "G = (\<lambda> w . (if (\<exists> x . \<phi> (abstract x) w) then (plus (F w)) else (minus (F w))))" by auto
  oops
    
lemma "[\<lparr>\<^bold>\<lambda>x . \<phi> x, y\<rparr> \<^bold>\<equiv> (\<^bold>\<exists>\<^sub>\<nu> z . (\<^bold>\<forall>\<^sub>1 F . \<lparr>F,y\<rparr> \<^bold>\<equiv> \<lparr>F,z\<rparr>) \<^bold>& \<phi> z) in v]"
proof (rule EquivI; rule)
  assume "[\<lparr>\<^bold>\<lambda>x. \<phi> x,y\<rparr> in v]"
  hence 1: "case y of real x \<Rightarrow> (case ((\<^bold>\<lambda>x. \<phi> x) v) of plus G \<Rightarrow> G x | minus G \<Rightarrow> G x) | abstract a \<Rightarrow> (case ((\<^bold>\<lambda>x. \<phi> x) v) of plus G \<Rightarrow> True | minus G \<Rightarrow> False)"
    unfolding valid_in_def exe1_def by simp
  fix d
  {
    assume "\<exists> x . y = real x" 
    then obtain x where x_def: "y = real x" by auto
    have "[(\<^bold>\<forall>\<^sub>1 F . \<lparr>F,y\<rparr> \<^bold>\<equiv> \<lparr>F,real x\<rparr>) \<^bold>& \<phi> (real x) in v]"
      using 1 apply (simp add: meta_defs conn_defs x_def)
      by (metis (mono_tags, lifting) D\<^sub>1.simps(5) D\<^sub>1.simps(6))
    hence "[\<^bold>\<exists>\<^sub>\<nu>z. (\<^bold>\<forall>\<^sub>1F. \<lparr>F,y\<rparr> \<^bold>\<equiv> \<lparr>F,z\<rparr>) \<^bold>& \<phi> z in v]" using ExI by fast
  }
  moreover {
    assume "\<not> (\<exists> x . y = real x)"
    then obtain x where x_def: "y = abstract x"
      using individuals.exhaust by blast
    {
      assume "\<not>(\<exists> x . \<phi> (abstract x) v)"
      moreover hence "\<not>\<phi> y v" unfolding x_def by simp
      ultimately have "False" using 1 x_def by (auto simp: meta_defs conn_defs)
    }
    hence 1: "\<exists> x . \<phi> (abstract x) v" by auto
    then obtain a where a_def: "\<phi> (abstract a) v" by auto
    obtain G where "((\<^bold>\<lambda>x. \<phi> x) v) = plus G" using 1
      unfolding lambdabinder1_def by simp
    have "[(\<^bold>\<forall>\<^sub>1 F . \<lparr>F,y\<rparr> \<^bold>\<equiv> \<lparr>F, abstract a\<rparr>) in v]"
      unfolding x_def by (simp add: meta_defs conn_defs)
    hence "[(\<^bold>\<forall>\<^sub>1 F . \<lparr>F,y\<rparr> \<^bold>\<equiv> \<lparr>F, abstract a\<rparr>) \<^bold>& \<phi> (abstract a) in v]"
      using a_def apply (simp add: meta_defs conn_defs) by blast
    hence "[\<^bold>\<exists>\<^sub>\<nu>z. (\<^bold>\<forall>\<^sub>1F. \<lparr>F,y\<rparr> \<^bold>\<equiv> \<lparr>F,z\<rparr>) \<^bold>& \<phi> z in v]" using ExI by fast
  }
  ultimately show "[\<^bold>\<exists>\<^sub>\<nu>z. (\<^bold>\<forall>\<^sub>1F. \<lparr>F,y\<rparr> \<^bold>\<equiv> \<lparr>F,z\<rparr>) \<^bold>& \<phi> z in v]"
    by blast
next
  assume "[\<^bold>\<exists>\<^sub>\<nu>z. (\<^bold>\<forall>\<^sub>1F. \<lparr>F,y\<rparr> \<^bold>\<equiv> \<lparr>F,z\<rparr>) \<^bold>& \<phi> (z) in v]"
  then obtain z where z_def: "[(\<^bold>\<forall>\<^sub>1F. \<lparr>F,y\<rparr> \<^bold>\<equiv> \<lparr>F,z\<rparr>) \<^bold>& \<phi> (z) in v]" by (rule ExE)
  hence 1: "[(\<^bold>\<forall>\<^sub>1F. \<lparr>F,y\<rparr> \<^bold>\<equiv> \<lparr>F,z\<rparr>) in v]" using ConjE by blast
  hence "[\<lparr>O!,y\<rparr> \<^bold>\<equiv> \<lparr>O!,z\<rparr> in v]" using All\<^sub>1S by fast
  hence "[\<lparr>O!,y\<rparr> in v] = [\<lparr>O!,z\<rparr> in v]" using EquivS by auto
  hence 2: "(\<exists> x . y = real x) \<longleftrightarrow> (\<exists> x . z = real x)" unfolding Ordinary_def Concrete_def
    apply (auto simp: meta_defs conn_defs) 
    apply (metis (mono_tags) D\<^sub>1.simps(6) individuals.exhaust individuals.simps(6))
    apply (metis (mono_tags) D\<^sub>1.simps(6) individuals.exhaust individuals.simps(6))
    using OrdinaryObjectsPossiblyConcreteAxiom apply blast
    using OrdinaryObjectsPossiblyConcreteAxiom by blast
  {
    assume 3: "\<exists> x . y = real x" 
    hence "\<exists> xx . z = real xx" using 2 by blast
    then obtain xx where xx_def: "z = real xx" by auto
    obtain x where x_def: "y = real x" using 3 by auto
    obtain F :: "D\<^sub>0\<Rightarrow>bool" where F_def: "F = (\<lambda> z . z = x)" by auto
    have "[\<lparr>(\<lambda> w . plus F),y\<rparr> \<^bold>\<equiv> \<lparr>(\<lambda> w . plus F),z\<rparr> in v]" using 1 All\<^sub>1E by blast
    moreover have "[\<lparr>(\<lambda> w . plus F),y\<rparr> in v]" using x_def  unfolding F_def by (simp add: meta_defs)
    ultimately have "[\<lparr>(\<lambda> w . plus F),z\<rparr> in v]" using EquivE by blast
    hence "xx = x" unfolding F_def xx_def by (simp add: meta_defs)
    hence 4: "z = y" using xx_def x_def by fast
    have "[\<phi> z in v]" using z_def ConjE by blast
    hence "[\<lparr>\<^bold>\<lambda>x. \<phi> x,z\<rparr> in v]" unfolding xx_def by (simp add: meta_defs)
    hence "[\<lparr>\<^bold>\<lambda>x. \<phi> x,y\<rparr> in v]" using 4 by auto
  }
  moreover {
    assume 5: "\<not>(\<exists> x . y = real x)"
    hence "\<exists> x . y = abstract x" using individuals.exhaust by blast
    then obtain x where x_def: "y = abstract x" by auto
    obtain xx where "z = abstract xx" using 5 2
      using individuals.exhaust by blast
    moreover have "[\<phi> z in v]" using z_def ConjE by blast
    ultimately have "\<exists> x . \<phi> (abstract x) v" by (auto simp: meta_defs)
    hence "[\<lparr>\<^bold>\<lambda>x. \<phi> x,y\<rparr> in v]" unfolding x_def by (simp add: meta_defs)
  }
  ultimately show "[\<lparr>\<^bold>\<lambda>x. \<phi> x,y\<rparr> in v]" by blast
qed

end
  