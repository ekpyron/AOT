(*<*)
theory TAO_1_Embedding
imports Main
begin
(*>*)

section{* Embedding *}
text{* \label{TAO_Embedding} *}

subsection{* Primitives *}
text{* \label{TAO_Embedding_Primitives} *}

typedecl i --{* possible worlds *}
typedecl j --{* states *}
typedef \<o> = "UNIV::(j\<Rightarrow>i\<Rightarrow>bool) set"
  morphisms eval\<o> make\<o> .. --{* truth values *}

consts dw :: i --{* actual world *}
consts dj :: j --{* actual state *}

typedecl \<omega> --{* ordinary objects *}
typedecl \<sigma> --{* special urelements *}
datatype \<upsilon> = \<omega>\<upsilon> \<omega> | \<sigma>\<upsilon> \<sigma> --{* urelements *}

type_synonym \<Pi>\<^sub>0 = \<o> --{* zero place relations *}
typedef \<Pi>\<^sub>1 = "UNIV::(\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool) set"
  morphisms eval\<Pi>\<^sub>1 make\<Pi>\<^sub>1 .. --{* one place relations *}
typedef \<Pi>\<^sub>2 = "UNIV::(\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool) set"
  morphisms eval\<Pi>\<^sub>2 make\<Pi>\<^sub>2 .. --{* two place relations *}
typedef \<Pi>\<^sub>3 = "UNIV::(\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool) set"
  morphisms eval\<Pi>\<^sub>3 make\<Pi>\<^sub>3 .. --{* three place relations *}

type_synonym \<alpha> = "\<Pi>\<^sub>1 set" --{* abstract objects *}

datatype \<nu> = \<omega>\<nu> \<omega> | \<alpha>\<nu> \<alpha> --{* individuals *}

setup_lifting type_definition_\<o>
setup_lifting type_definition_\<Pi>\<^sub>1
setup_lifting type_definition_\<Pi>\<^sub>2
setup_lifting type_definition_\<Pi>\<^sub>3

subsection{* Individual Terms and Definite Descriptions *}
text{* \label{TAO_Embedding_IndividualTerms} *}

typedef \<kappa> = "UNIV::(\<nu> option) set" morphisms eval\<kappa> make\<kappa> ..

setup_lifting type_definition_\<kappa>

text{*
\begin{remark}
  Individual terms can be definite descriptions which may not denote.
  Therefore the type for individual terms @{type "\<kappa>"} is defined as
  @{typ "\<nu> option"}. Individuals are represented by @{term "Some x"}
  for an individual @{term "x"} of type @{type \<nu>}, whereas non-denoting
  individual terms are represented by @{term "None"}.
  Note that relation terms on the other hand always denote,
  so there is no need for a similar distinction between relation terms and
  relations.
\end{remark}
*}

lift_definition \<nu>\<kappa> :: "\<nu>\<Rightarrow>\<kappa>" ("_\<^sup>P" [90] 90) is Some .
lift_definition proper :: "\<kappa>\<Rightarrow>bool" is "op\<noteq> None" .
lift_definition rep :: "\<kappa>\<Rightarrow>\<nu>" is the .

text{*
\begin{remark}
  Individual terms can be explicitly marked to only range over
  logically proper objects (e.g. @{term "x\<^sup>P"}). Their logical propriety
  and (in case they are logically proper) the represented individual can
  be extracted from the internal representation as @{typ "\<nu> option"}.
\end{remark}
*}


lift_definition that::"(\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<kappa>" (binder "\<^bold>\<iota>" [8] 9) is
  "\<lambda> \<phi> . if (\<exists>! x . (\<phi> x) dj dw)
         then Some (THE x . (\<phi> x) dj dw)
         else None" .

text{*
\begin{remark}
  Definite descriptions map conditions on individuals to individual terms.
  If no unique object satisfying the condition exists (and therefore the definite
  description is not logically proper), the individual term is set to @{term "None"}.
\end{remark}
*}

subsection{* Mapping from abstract objects to special urelements *}
text{* \label{TAO_Embedding_AbstractObjectsToSpecialUrelements} *}

consts \<alpha>\<sigma> :: "j\<Rightarrow>\<alpha>\<Rightarrow>\<sigma>"
axiomatization where \<alpha>\<sigma>_surj: "surj (\<alpha>\<sigma> j)"

subsection{* Conversion between objects and urelements *}
text{* \label{TAO_IndToUr} *}

definition \<nu>\<upsilon> :: "j\<Rightarrow>\<nu>\<Rightarrow>\<upsilon>" where "\<nu>\<upsilon> \<equiv> \<lambda> s . case_\<nu> \<omega>\<upsilon> (\<sigma>\<upsilon> \<circ> (\<alpha>\<sigma> s))"

subsection{* Exemplification of n-place relations. *}
text{* \label{TAO_Embedding_Exemplification} *}

lift_definition exe0::"\<Pi>\<^sub>0\<Rightarrow>\<o>" ("\<lparr>_\<rparr>") is id .
lift_definition exe1::"\<Pi>\<^sub>1\<Rightarrow>\<kappa>\<Rightarrow>\<o>" ("\<lparr>_,_\<rparr>") is
  "\<lambda> F x s w . (proper x) \<and> F (\<nu>\<upsilon> s (rep x)) s w" .
lift_definition exe2::"\<Pi>\<^sub>2\<Rightarrow>\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<o>" ("\<lparr>_,_,_\<rparr>") is
  "\<lambda> F x y s w . (proper x) \<and> (proper y) \<and>
     F (\<nu>\<upsilon> s (rep x)) (\<nu>\<upsilon> s (rep y)) s w" .
lift_definition exe3::"\<Pi>\<^sub>3\<Rightarrow>\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<o>" ("\<lparr>_,_,_,_\<rparr>") is
"\<lambda> F x y z s w . (proper x) \<and> (proper y) \<and> (proper z) \<and>
   F (\<nu>\<upsilon> s (rep x)) (\<nu>\<upsilon> s (rep y)) (\<nu>\<upsilon> s (rep z)) s w" .

text{*
\begin{remark}
  An exemplification formula can only be true if all individual terms are logically proper.
  Furthermore exemplification depends on the urelement corresponding to
  the individual, not the individual itself.
\end{remark}
*}

subsection{* Encoding *}
text{* \label{TAO_Embedding_Encoding} *}

lift_definition enc :: "\<kappa>\<Rightarrow>\<Pi>\<^sub>1\<Rightarrow>\<o>" ("\<lbrace>_,_\<rbrace>") is
  "\<lambda> x F w s . (proper x) \<and> case_\<nu> (\<lambda> \<omega> . False) (\<lambda> \<alpha> . F \<in> \<alpha>) (rep x)" .

text{*
\begin{remark}
  An encoding formula can again only be true if the individual term is logically proper.
  Furthermore ordinary objects never encode, whereas abstract objects encode
  a property if and only if the property is contained in it as per
  the Aczel Model.
\end{remark}
*}

subsection{* Connectives and Quantifiers *}
text{* \label{TAO_Embedding_Connectives} *}

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

text{*
\begin{remark}
  The connectives behave classically if evaluated for the actual state @{term "dj"},
  whereas their behavior is governed by uninterpreted constants for any
  other state.
\end{remark}
*}

subsection{* Lambda Expressions *}
text{* \label{TAO_Embedding_Lambda} *}

lift_definition lambdabinder0 :: "\<o>\<Rightarrow>\<Pi>\<^sub>0" ("\<^bold>\<lambda>\<^sup>0") is id .
lift_definition lambdabinder1 :: "(\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<Pi>\<^sub>1" (binder "\<^bold>\<lambda>" [8] 9) is
  "\<lambda> \<phi> u s w . \<exists> x . \<nu>\<upsilon> s x = u \<and> \<phi> x s w" .
lift_definition lambdabinder2 :: "(\<nu>\<Rightarrow>\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<Pi>\<^sub>2" ("\<^bold>\<lambda>\<^sup>2") is
  "\<lambda> \<phi> u v s w . \<exists> x y . \<nu>\<upsilon> s x = u \<and> \<nu>\<upsilon> s y = v \<and> \<phi> x y s w" .
lift_definition lambdabinder3 :: "(\<nu>\<Rightarrow>\<nu>\<Rightarrow>\<nu>\<Rightarrow>\<o>)\<Rightarrow>\<Pi>\<^sub>3" ("\<^bold>\<lambda>\<^sup>3") is
  "\<lambda> \<phi> u v r s w . \<exists> x y z . \<nu>\<upsilon> s x = u \<and> \<nu>\<upsilon> s y = v \<and> \<nu>\<upsilon> s z = r \<and> \<phi> x y z s w" .

text{*
\begin{remark}
  Lambda expressions map functions acting on individuals
  to functions acting on urelements (i.e. relations). Note that
  the inverse mapping @{term "\<upsilon>\<nu>"} is injective only for ordinary
  objects. As propositional formulas, which are the only terms PM
  allows inside lambda expressions, do not contain encoding
  subformulas, they only depends on urelements, though. For
  propositional formulas the lambda expressions therefore exactly
  correspond to the lambda expressions in PM.
  Lambda expressions with non-propositional formulas, which are not
  allowed in PM, because in general they lead to inconsistencies,
  have a non-standard semantics. @{term "\<^bold>\<lambda> x . \<lbrace>x\<^sup>P,F\<rbrace>"} can be
  translated to "being @{term "x"} such that there exists an abstract
  object, which encodes @{term "F"}, that is mapped to the same urelement
  as @{term "x"}" instead of "being @{term "x"} such that @{term "x"}
  encodes @{term "F"}". This construction avoids the aforementioned
  inconsistencies.
\end{remark}
*}

subsection{* Validity *} 
text{* \label{TAO_Embedding_Validity} *}

lift_definition valid_in :: "i\<Rightarrow>\<o>\<Rightarrow>bool" (infixl "\<Turnstile>" 5) is
  "\<lambda> v \<phi> . \<phi> dj v" .

text{*
\begin{remark}
  A formula is considered semantically valid for a possible world,
  if it evaluates to @{term "True"} for the actual state @{term "dj"}
  and the given possible world.
\end{remark}
*}

subsection{* Concreteness *}
text{* \label{TAO_Embedding_Concreteness} *}

consts ConcreteInWorld :: "\<omega>\<Rightarrow>i\<Rightarrow>bool"

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

text{*
\begin{remark}
  In order to define concreteness, care has to be taken that the defined
  notion of concreteness coincides with the meta-logical distinction between
  abstract objects and ordinary objects. Furthermore the axioms about
  concreteness have to be satisfied. This is achieved by introducing an
  uninterpreted constant @{term "ConcreteInWorld"} that determines whether
  an ordinary object is concrete in a given possible world. This constant is
  axiomatized, such that all ordinary objects are possibly concrete, contingent
  objects possibly exist and possibly no contingent objects exist.
\end{remark}
*}


lift_definition Concrete::"\<Pi>\<^sub>1" ("E!") is
  "\<lambda> u s w . case u of \<omega>\<upsilon> x \<Rightarrow> ConcreteInWorld x w | _ \<Rightarrow> False" .

text{*
\begin{remark}
  Concreteness of ordinary objects is now defined using this
  axiomatized uninterpreted constant. Abstract objects on the other
  hand are never concrete.
\end{remark}
*}

subsection{* Automation *}
text{* \label{TAO_Embedding_Automation} *}

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
text{* \label{TAO_Embedding_Aux} *}

named_theorems meta_aux

declare make\<kappa>_inverse[meta_aux] eval\<kappa>_inverse[meta_aux]
        make\<o>_inverse[meta_aux] eval\<o>_inverse[meta_aux]
        make\<Pi>\<^sub>1_inverse[meta_aux] eval\<Pi>\<^sub>1_inverse[meta_aux]
        make\<Pi>\<^sub>2_inverse[meta_aux] eval\<Pi>\<^sub>2_inverse[meta_aux]
        make\<Pi>\<^sub>3_inverse[meta_aux] eval\<Pi>\<^sub>3_inverse[meta_aux]
lemma \<nu>\<upsilon>_\<omega>\<nu>_is_\<omega>\<upsilon>[meta_aux]: "\<nu>\<upsilon> s (\<omega>\<nu> x) = \<omega>\<upsilon> x" by (simp add: \<nu>\<upsilon>_def)
lemma rep_proper_id[meta_aux]: "rep (x\<^sup>P) = x"
  by (simp add: meta_aux \<nu>\<kappa>_def rep_def)
lemma \<nu>\<kappa>_proper[meta_aux]: "proper (x\<^sup>P)"
  by (simp add: meta_aux \<nu>\<kappa>_def proper_def)
lemma no_\<alpha>\<omega>[meta_aux]: "\<not>(\<nu>\<upsilon> s (\<alpha>\<nu> x) = \<omega>\<upsilon> y)" by (simp add: \<nu>\<upsilon>_def)
lemma no_\<sigma>\<omega>[meta_aux]: "\<not>(\<sigma>\<upsilon> x = \<omega>\<upsilon> y)" by blast
lemma \<nu>\<upsilon>_surj[meta_aux]: "surj (\<nu>\<upsilon> s)"
  using \<alpha>\<sigma>_surj unfolding \<nu>\<upsilon>_def surj_def
  by (metis \<nu>.simps(5) \<nu>.simps(6) \<upsilon>.exhaust comp_apply)
(*
lemma \<upsilon>\<nu>\<kappa>_aux1[meta_aux]:
  "None \<noteq> (eval\<kappa> (\<upsilon>\<nu> s (\<nu>\<upsilon> s (the (eval\<kappa> x)))\<^sup>P))"
  apply transfer
  by simp
lemma \<upsilon>\<nu>\<kappa>_aux2[meta_aux]:
  "(\<nu>\<upsilon> s (the (eval\<kappa> (\<upsilon>\<nu> s (\<nu>\<upsilon> s (the (eval\<kappa> x)))\<^sup>P)))) = (\<nu>\<upsilon> s (the (eval\<kappa> x)))"
  apply transfer
  using \<nu>\<upsilon>_\<upsilon>\<nu>_id by auto
lemma \<upsilon>\<nu>\<kappa>_aux3[meta_aux]:
  "Some o\<^sub>1 = eval\<kappa> x \<Longrightarrow> (None \<noteq> eval\<kappa> (\<upsilon>\<nu> s (\<nu>\<upsilon> s o\<^sub>1)\<^sup>P)) = (None \<noteq> eval\<kappa> x)"
  apply transfer by (auto simp: meta_aux)
lemma \<upsilon>\<nu>\<kappa>_aux4[meta_aux]:
  "Some o\<^sub>1 = eval\<kappa> x \<Longrightarrow> (\<nu>\<upsilon> s (the (eval\<kappa> (\<upsilon>\<nu> s (\<nu>\<upsilon> s o\<^sub>1)\<^sup>P)))) = \<nu>\<upsilon> s (the (eval\<kappa> x))"
  apply transfer by (auto simp: meta_aux)
*)

(*<*)
end
(*>*)
