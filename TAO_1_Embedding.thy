(*<*)
theory TAO_1_Embedding
imports Main
begin
(*>*)

section{* Embedding *}

subsection{* Primitives *}

typedecl i --{* possible worlds *}
typedecl j --{* states *}
typedef \<o> = "UNIV::(j\<Rightarrow>i\<Rightarrow>bool) set" morphisms eval\<o> make\<o> .. --{* truth values *}

consts dw :: i --{* actual world *}
consts dj :: j --{* actual state *}

typedecl \<omega> --{* ordinary objects *}
typedecl \<sigma> --{* special Urelements *}
datatype \<upsilon> = \<omega>\<upsilon> \<omega> | \<sigma>\<upsilon> \<sigma> --{* Urelements *}

type_synonym \<Pi>\<^sub>0 = \<o> --{* zero place relations *}
typedef \<Pi>\<^sub>1 = "UNIV::(\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool) set" morphisms eval\<Pi>\<^sub>1 make\<Pi>\<^sub>1 .. --{* one place relations *}
typedef \<Pi>\<^sub>2 = "UNIV::(\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool) set" morphisms eval\<Pi>\<^sub>2 make\<Pi>\<^sub>2 .. --{* two place relations *}
typedef \<Pi>\<^sub>3 = "UNIV::(\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool) set" morphisms eval\<Pi>\<^sub>3 make\<Pi>\<^sub>3 .. --{* three place relations *}

type_synonym \<alpha> = "\<Pi>\<^sub>1 set" --{* abstract objects *}

datatype \<nu> = \<omega>\<nu> \<omega> | \<alpha>\<nu> \<alpha> --{* individuals *}

text{* Individual terms can be definite descriptions which may not denote.
       The condition under which an individual term denotes is stored as
       a boolean. Note that relation terms on the other hand always denote,
       so there is no need for a distinction between relation terms and
       relation variables. *}
typedef \<kappa> = "UNIV::(bool\<times>\<nu>) set" morphisms eval\<kappa> make\<kappa> ..

setup_lifting type_definition_\<o>
setup_lifting type_definition_\<kappa>
setup_lifting type_definition_\<Pi>\<^sub>1
setup_lifting type_definition_\<Pi>\<^sub>2
setup_lifting type_definition_\<Pi>\<^sub>3

text{* Individual terms can be explicitely marked to represent
       only denoting resp. logically proper objects. *}

lift_definition \<nu>\<kappa> :: "\<nu>\<Rightarrow>\<kappa>" ("_\<^sup>P" [90] 90) is "Pair True" .
lift_definition meta_denotes :: "\<kappa>\<Rightarrow>bool" is fst .
lift_definition denotation :: "\<kappa>\<Rightarrow>\<nu>" is snd .

subsection{* Mapping from abstract objects to special Urelements *}

consts \<alpha>\<sigma> :: "\<alpha>\<Rightarrow>\<sigma>"
axiomatization where \<alpha>\<sigma>_surj: "surj \<alpha>\<sigma>"

subsection{* Conversion between objects and Urelements *}

definition \<nu>\<upsilon> :: "\<nu>\<Rightarrow>\<upsilon>" where "\<nu>\<upsilon> \<equiv> case_\<nu> \<omega>\<upsilon> (\<sigma>\<upsilon> \<circ> \<alpha>\<sigma>)"
definition \<upsilon>\<nu> :: "\<upsilon>\<Rightarrow>\<nu>" where "\<upsilon>\<nu> \<equiv> case_\<upsilon> \<omega>\<nu> (\<alpha>\<nu> \<circ> (inv \<alpha>\<sigma>))"

subsection{* Exemplification of n-place relations. *}

text{* An exemplification formula is only true if all individual variables denote.
       Furthermore exemplification only depends on the Urelement corresponding to
       the individual. *}

lift_definition exe0::"\<Pi>\<^sub>0\<Rightarrow>\<o>" ("\<lparr>_\<rparr>") is id .
lift_definition exe1::"\<Pi>\<^sub>1\<Rightarrow>\<kappa>\<Rightarrow>\<o>" ("\<lparr>_,_\<rparr>") is
  "\<lambda> F x . (\<lambda> w s . (meta_denotes x) \<and> F (\<nu>\<upsilon> (denotation x)) w s)" .
lift_definition exe2::"\<Pi>\<^sub>2\<Rightarrow>\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<o>" ("\<lparr>_,_,_\<rparr>") is
  "\<lambda> F x y . (\<lambda> w s . (meta_denotes x) \<and> (meta_denotes y)
              \<and> F (\<nu>\<upsilon> (denotation x)) (\<nu>\<upsilon> (denotation y)) w s)" .
lift_definition exe3::"\<Pi>\<^sub>3\<Rightarrow>\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<o>" ("\<lparr>_,_,_,_\<rparr>") is
  "\<lambda> F x y z . (\<lambda> w s . (meta_denotes x) \<and> (meta_denotes y) \<and> (meta_denotes z)
                \<and> F (\<nu>\<upsilon> (denotation x)) (\<nu>\<upsilon> (denotation y)) (\<nu>\<upsilon> (denotation z)) w s)" .

subsection{* Encoding *}

text{* An encoding formula is again only true if the individual term denotes.
       Furthermore ordinary objects never encode, whereas abstract objects encode
       a property if and only if the property is contained in it as per
       the Aczel Model. *}

lift_definition enc :: "\<kappa>\<Rightarrow>\<Pi>\<^sub>1\<Rightarrow>\<o>" ("\<lbrace>_,_\<rbrace>") is
  "\<lambda> x F . (\<lambda> w s . (meta_denotes x) \<and> case_\<nu> (\<lambda> ord . False) (\<lambda> abs . F \<in> abs) (denotation x))" .

subsection{* Connectives and Quantifiers *}

text{* The connectives behave classically if evaluated for the actual state dj,
       whereas their behavior is governed by uninterpreted constants for any
       other state. *}

consts I_NOT :: "j\<Rightarrow>(i\<Rightarrow>bool)\<Rightarrow>(i\<Rightarrow>bool)"
consts I_IMPL :: "j\<Rightarrow>(i\<Rightarrow>bool)\<Rightarrow>(i\<Rightarrow>bool)\<Rightarrow>(i\<Rightarrow>bool)"

lift_definition not :: "\<o>\<Rightarrow>\<o>" ("\<^bold>\<not>_" [54] 70) is
  "\<lambda> p s w . s = dj \<and> \<not>p dj w \<or> s \<noteq> dj \<and> (I_NOT s (p s) w)" .
lift_definition impl :: "\<o>\<Rightarrow>\<o>\<Rightarrow>\<o>" (infixl "\<^bold>\<rightarrow>" 51) is
  "\<lambda> p q s w . s = dj \<and> (p dj w \<longrightarrow> q dj w) \<or> s \<noteq> dj \<and> (I_IMPL s (p s) (q s)) w" .
lift_definition forall\<^sub>\<nu> :: "(\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>\<nu>" [8] 9) is
  "\<lambda> \<phi> s w . \<forall> x :: \<nu> . (\<phi> x) s w" .
lift_definition forall\<^sub>0 :: "(\<Pi>\<^sub>0\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>0" [8] 9) is
  "\<lambda> \<phi> s w . \<forall> x :: \<Pi>\<^sub>0 . (\<phi> x) s w" .
lift_definition forall\<^sub>1 :: "(\<Pi>\<^sub>1\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>1" [8] 9) is
  "\<lambda> \<phi> s w . \<forall> x :: \<Pi>\<^sub>1  . (\<phi> x) s w" .
lift_definition forall\<^sub>2 :: "(\<Pi>\<^sub>2\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>2" [8] 9) is
  "\<lambda> \<phi> s w . \<forall> x :: \<Pi>\<^sub>2  . (\<phi> x) s w" .
lift_definition forall\<^sub>3 :: "(\<Pi>\<^sub>3\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>3" [8] 9) is
  "\<lambda> \<phi> s w . \<forall> x :: \<Pi>\<^sub>3  . (\<phi> x) s w" .
lift_definition forall\<^sub>\<o> :: "(\<o>\<Rightarrow>\<o>)\<Rightarrow>\<o>" (binder "\<^bold>\<forall>\<^sub>\<o>" [8] 9) is
  "\<lambda> \<phi> s w . \<forall> x :: \<o>  . (\<phi> x) s w" .
lift_definition box :: "\<o>\<Rightarrow>\<o>" ("\<^bold>\<box>_" [62] 63) is
  "\<lambda> p s w . \<forall> v . p s v" .
lift_definition actual :: "\<o>\<Rightarrow>\<o>" ("\<^bold>\<A>_" [64] 65) is
  "\<lambda> p s w . p dj dw" .

subsection{* Definite Description *}

text{* Definite descriptions map conditions on individual variables
       to individual terms. Whether the condition is satisfied by
       a unique individual (and therefore the definite description denotes)
       is stored as a boolean. *}

lift_definition that::"(\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<kappa>" (binder "\<^bold>\<iota>" [8] 9) is
  "\<lambda> \<phi> . (\<exists>! x . (\<phi> x) dj dw, THE x . (\<phi> x) dj dw)" .

subsection{* Lambda Expressions *}

text{* Lambda expressions map functions acting on individual variables
       to functions acting on Urelements (i.e. relations). Note that
       the inverse mapping @{text "\<upsilon>\<nu>"} is injective only for ordinary
       objects. As propositional formulas, which are the only terms PM
       allows inside lambda expressions, do not contain encoding
       subformulas, they only depends on Urelements, though. For
       propositional formulas the lambda expressions therefore exactly
       correspond to the lambda expressions in PM.
       Lambda expressions with non-propositional formulas, which are not
       allowed in PM, because in general they lead to inconsistencies,
       have a non-standard semantics. @{text "\<^bold>\<lambda> x . \<lbrace>x\<^sup>P,F\<rbrace>"} can be
       translated to "being @{text "x"} such that there exists an abstract
       object, which encodes @{text "F"}, that is mapped to the same Urelement
       as @{text "x"}" instead of "being @{text "x"} such that @{text "x"}
       encodes @{text "F"}". This construction avoids the aforementioned
       inconsistencies. *}

lift_definition lambdabinder0 :: "\<o>\<Rightarrow>\<Pi>\<^sub>0" ("\<^bold>\<lambda>\<^sup>0") is id .
lift_definition lambdabinder1 :: "(\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<Pi>\<^sub>1" (binder "\<^bold>\<lambda>" [8] 9) is
  "\<lambda> \<phi> u . \<phi> (\<upsilon>\<nu> u)" .
lift_definition lambdabinder2 :: "(\<nu>\<Rightarrow>\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<Pi>\<^sub>2" ("\<^bold>\<lambda>\<^sup>2") is
  "\<lambda> \<phi> u v . \<phi> (\<upsilon>\<nu> u) (\<upsilon>\<nu> v)" .
lift_definition lambdabinder3 :: "(\<nu>\<Rightarrow>\<nu>\<Rightarrow>\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<Pi>\<^sub>3" ("\<^bold>\<lambda>\<^sup>3") is
  "\<lambda> \<phi> u v w .  \<phi> (\<upsilon>\<nu> u) (\<upsilon>\<nu> v) (\<upsilon>\<nu> w)" .

subsection{* Validity *} 

text{* A formula is considered semantically valid for a possible world,
       if it evaluates to @{text "True"} for the actual state and the given
       possible world. *}

lift_definition valid_in :: "i\<Rightarrow>\<o>\<Rightarrow>bool" (infixl "\<Turnstile>" 5) is
  "\<lambda> v \<phi> . \<phi> dj v" .

subsection{* Concreteness *}

text{* In order to define concreteness, care has to be taken that the defined
       notion of concreteness coincides with the meta-logical distinction between
       abstract objects and ordinary objects. Furthermore the axioms about
       concreteness have to be satisfied. This is achieved by introducing an
       uninterpreted that determines whether an ordinary object is concrete
       in a given possible world. This constant is axiomatized, such that
       all ordinary objects are possibly concrete, contingent objects possibly
       exist and possibly no contingent objects exist. *}

consts ConcreteInWorld :: "\<omega>\<Rightarrow>i\<Rightarrow>bool"

abbreviation OrdinaryObjectsPossiblyConcrete where
  "OrdinaryObjectsPossiblyConcrete \<equiv> \<forall> x . \<exists> v . ConcreteInWorld x v"
abbreviation PossiblyContingentObjectExists where
  "PossiblyContingentObjectExists \<equiv> \<exists> x v . ConcreteInWorld x v
                                        \<and> (\<exists> w . \<not> ConcreteInWorld x w)"
abbreviation PossiblyNoContingentObjectExists where
  "PossiblyNoContingentObjectExists \<equiv> \<exists> w . \<forall> x . ConcreteInWorld x w
                                        \<longrightarrow> (\<forall> v . ConcreteInWorld x v)"
axiomatization where
  OrdinaryObjectsPossiblyConcreteAxiom:
    "OrdinaryObjectsPossiblyConcrete"
  and PossiblyContingentObjectExistsAxiom:
    "PossiblyContingentObjectExists"
  and PossiblyNoContingentObjectExistsAxiom:
    "PossiblyNoContingentObjectExists"

text{* Concreteness of ordinary objects can now be defined using this
       axiomatized uninterpreted constant. Abstract objects on the other
       hand are never concrete. *}

lift_definition Concrete::"\<Pi>\<^sub>1" ("E!") is
  "\<lambda> u s w . case u of \<omega>\<upsilon> x \<Rightarrow> ConcreteInWorld x w | _ \<Rightarrow> False" .

subsection{* Automation *}

named_theorems meta_defs

declare not_def[meta_defs] impl_def[meta_defs] forall\<^sub>\<nu>_def[meta_defs]
        forall\<^sub>0_def[meta_defs] forall\<^sub>1_def[meta_defs]
        forall\<^sub>2_def[meta_defs] forall\<^sub>3_def[meta_defs] forall\<^sub>\<o>_def[meta_defs]
        box_def[meta_defs] actual_def[meta_defs] that_def[meta_defs]
        lambdabinder0_def[meta_defs] lambdabinder1_def[meta_defs]
        lambdabinder2_def[meta_defs] lambdabinder3_def[meta_defs]
        exe0_def[meta_defs] exe1_def[meta_defs] exe2_def[meta_defs]
        exe3_def[meta_defs] enc_def[meta_defs] inv_def[meta_defs]
        that_def[meta_defs] valid_in_def[meta_defs] Concrete_def[meta_defs]

declare [[smt_solver = cvc4]]
declare [[simp_depth_limit = 10]] (* prevent the simplifier from running forever *)
declare [[unify_search_bound = 40]] (* prevent unification bound errors *)

subsection{* Auxiliary Lemmata *}

named_theorems meta_aux

declare make\<kappa>_inverse[meta_aux] eval\<kappa>_inverse[meta_aux]
        make\<o>_inverse[meta_aux] eval\<o>_inverse[meta_aux]
        make\<Pi>\<^sub>1_inverse[meta_aux] eval\<Pi>\<^sub>1_inverse[meta_aux]
        make\<Pi>\<^sub>2_inverse[meta_aux] eval\<Pi>\<^sub>2_inverse[meta_aux]
        make\<Pi>\<^sub>3_inverse[meta_aux] eval\<Pi>\<^sub>3_inverse[meta_aux]
lemma proper_denotes: "meta_denotes (x\<^sup>P) = True" by (simp add: meta_aux \<nu>\<kappa>_def meta_denotes_def)
lemma proper_denotation: "denotation (x\<^sup>P) = x" by (simp add: meta_aux \<nu>\<kappa>_def denotation_def)
lemma \<nu>\<upsilon>_\<omega>\<nu>_is_\<omega>\<upsilon>[meta_aux]: "\<nu>\<upsilon> (\<omega>\<nu> x) = \<omega>\<upsilon> x" by (simp add: \<nu>\<upsilon>_def)
lemma \<upsilon>\<nu>_\<omega>\<upsilon>_is_\<omega>\<nu>[meta_aux]: "\<upsilon>\<nu> (\<omega>\<upsilon> x) = \<omega>\<nu> x" by (simp add: \<upsilon>\<nu>_def)
lemma denotation_proper[meta_aux]: "denotation (x\<^sup>P) = x" by (simp add: meta_aux \<nu>\<kappa>_def denotation_def)
lemma proper_meta_denotes[meta_aux]: "meta_denotes (x\<^sup>P)" by (simp add: meta_aux \<nu>\<kappa>_def meta_denotes_def)
lemma \<nu>\<upsilon>_\<upsilon>\<nu>_id[meta_aux]: "\<nu>\<upsilon> (\<upsilon>\<nu> (x)) = x" by (simp add: \<nu>\<upsilon>_def \<upsilon>\<nu>_def \<alpha>\<sigma>_surj surj_f_inv_f split: \<upsilon>.split)
lemma no_\<alpha>\<omega>[meta_aux]: "\<not>(\<nu>\<upsilon> (\<alpha>\<nu> x) = \<omega>\<upsilon> y)" by (simp add: \<nu>\<upsilon>_def)
lemma no_\<sigma>\<omega>[meta_aux]: "\<not>(\<sigma>\<upsilon> x = \<omega>\<upsilon> y)" by blast
lemma \<nu>\<upsilon>_surj[meta_aux]: "surj \<nu>\<upsilon>" using \<nu>\<upsilon>_\<upsilon>\<nu>_id surjI by blast

(*<*)
end
(*>*)
