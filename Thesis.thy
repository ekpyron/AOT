(*<*)
theory Thesis
imports TAO_98_ArtificialTheorems TAO_99_SanityTests "~~/src/HOL/Library/LaTeXsugar" "~~/src/HOL/Library/OptionalSugar"
begin
(*>*)

(*<*)
(* Pretty printing settings for antiquotations. *)
notation (latex output)
  validity_in ("[\<^raw:\embeddedstyle{>_\<^raw:}> in _]")
definition embedded_style where "embedded_style \<equiv> id"
lemma embedded_def: "A = B \<Longrightarrow> (embedded_style A) = B" unfolding embedded_style_def by auto
notation (latex output)
  embedded_style ("\<^raw:\embeddedstyle{>_\<^raw:}>")
notation (latex output)
  make\<kappa> ("")
notation (latex output)
  make\<o> ("")
notation (latex output)
  make\<Pi>\<^sub>1 ("")
notation (latex output)
  make\<Pi>\<^sub>2 ("")
notation (latex output)
  make\<Pi>\<^sub>3 ("")
notation (latex output)
  eval\<kappa> ("")
notation (latex output)
  eval\<o> ("")
notation (latex output)
  eval\<Pi>\<^sub>1 ("")
notation (latex output)
  eval\<Pi>\<^sub>2 ("")
notation (latex output)
  eval\<Pi>\<^sub>3 ("")
notation (latex output)
  that ("\<^bold>\<iota>x . _ x")
notation (latex output)
  forall\<^sub>\<nu> ("\<^bold>\<forall>\<^sub>\<nu> x . _ x")
notation (latex output)
  forall\<^sub>0 ("\<^bold>\<forall>\<^sub>0 p . _ p")
notation (latex output)
  forall\<^sub>1 ("\<^bold>\<forall>\<^sub>1 F . _ F")
notation (latex output)
  forall\<^sub>2 ("\<^bold>\<forall>\<^sub>2 F . _ F")
notation (latex output)
  forall\<^sub>3 ("\<^bold>\<forall>\<^sub>3 F . _ F")
notation (latex output)
  lambdabinder1 ("\<^bold>\<lambda>x. _ x")
translations
  (type) "\<alpha>" <= (type) "\<Pi>\<^sub>1 set"
(*>*)

chapter{* Introduction *}

section{* Overview *}

text{*
  \begin{TODO}
    Improve and adjust.
  \end{TODO}

  The overall structure of this document is the following:

  \begin{itemize}
    \item This first chapter provides a brief introduction to the background of
          automated reasoning and semantical representations of logical systems
          and describes the motivation, challenges and results of our work.
  
    \item The second chapter gives an overview of the motivation and structure of
          the target theory of our embedding, the Theory of Abstract Objects.
  
    \item The third chapter is a detailed documentation of the concepts and
          technical structure of our embedding. This chapter references the
          Isabelle theory that can be found in the appendix.
  
    \item The fourth chapter discusses the philosophical implications of our embedding
          and its relation to the target theory of PLM. Furthermore it describes 
          our meta-logical results achieved using the embedding and states interesting
          open questions future research may address.
  
    \item The last chapter consists of a technical discussion about some issues encountered
          during the construction of our embedding due to limitations of the logical framework
          of Isabelle/HOL and our solutions.
  \end{itemize}

  Note that this entire document is generated from an Isabelle theory file and thereby all formal
  statements throughout the document are well-formed terms, resp. verified valid theorems in our
  constructed embedding.
*}

section{* Universal Logical Reasoning *}

text{*

\begin{TODO}
  Add references throughout the section.
\end{TODO}

The concept of understanding rational argumentation and reasoning using formal logical systems
has a long tradition and can already be found in the study of syllogistic arguments by Aristotle.
Since then a large variety of formal systems has evolved, each using different syntactical
and semantical structures to capture specific aspects of logical reasoning (e.g. propositional logic,
first-order/higher-order logic, modal logic, free logic, etc.). This diversity of formal systems
gives rise to the question, whether a \emph{universal} logic can be devised, that would be capable
of expressing statements of all existing specialized logical systems and provide a basis for
meta-logical considerations like the equivalence of or relations between those systems.

The idea of a universal logical framework is very prominent in the works of Gottfried Wilhelm Leibniz
(1646-1716) with his concept of a \emph{characteristica universalis}, i.e. a universal formal language
able to express metaphysical, scientific and mathematical concepts. Based thereupon he envisioned 
the \emph{calculus ratiocinator}, a universal logical calculus with which the truth of statements
formulated in the characteristica universalis could be decided purely by formal calculation and thereby
in an automated fashion. 

Nowadays with the rise of powerful computer systems such a universal logical framework could have
repercussions throughout the sciences (TODO: change this?) and may be a vital part of machine-computer interaction in
the future. In this spirit Leibniz' ideas have inspired recent efforts to use functional higher-order logic (HOL)
as such a universal logical language and to represent various logical systems by the use of
\emph{shallow semantical embeddings} (TODO: reference \url{https://arxiv.org/abs/1703.09620}).

Notably this approach recently received attention due to the formalisation, validation and analysis
of G\"odel's ontological proof of the existence of God by Christoph Benzm\"uller (TODO: reference),
for which a modal higher-order logic was embedded in the computerized logic framework Isabelle/HOL.

The concept of this approach that is adapted for our work is outlined in the next section.
*}

section{* Shallow Semantical Embeddings in HOL *}

text{*
\begin{TODO}
  Think about terminology: background logic, target logic, embedded logic.
\end{TODO}

A semantic embedding of a target logical system defines the syntactical elements of the target language
in a background logic (e.g. in a framework like Isabelle/HOL) based on their semantics.
This way the background logic can be used to argue about the semantic truth of syntactic statements
in the embedded logic.

A \emph{deep} embedding represents the complete syntactical structure of the target language
separately from the background logic, i.e. every term, variable symbol, connective, etc. of the
target language is represented as a syntactical object and then the background logic is used to
evaluate a syntactic expression by quantifying over all models that can be associated with the
syntax. Variable symbols of the target logic for instance would be represented as constants in
the background logic and a proposition would be considered semantically valid if it holds for
all possible denotations an interpretation function can assign to these variables.

While this approach will work for most target logics, it has several drawbacks. There are likely
principles that are shared between the target logic and the background logic, such as alpha-conversion
for lambda expressions or the equivalence of terms with renamed variables in general. In a deep
embedding these principles have to be explicitly shown to hold for the syntactic representation
of the target logic, which is usually connected with significant complexity. Furthermore if the
framework used for the background logic allows automated reasoning, the degree of automation that
can be achieved in the embedded logic is limited, as any reasoning in the target logic will have
to consider the syntactical translation process that will usually be complex.

A \emph{shallow} embedding uses a different approach based on the idea that most contemporary
logical systems are semantically characterized by the means of set theory. A shallow embedding
now defines primitive syntactical objects of the target language such as variables or propositions
using a set theoretic representation. For example propositions in a modal logic can be represented
as functions from possible worlds to truth values in a non-modal logic. The shallow embedding aims
to equationally define only the syntactical elements of the target logic that are not already
present in the background logic or whose semantics behave differently than in the background logic,
while preserving as much of the logical structure of the background logic as possible.
The modal box operator for example can be represented as a quantification over all possible worlds
satisfying an accessibility relation, while negation and quantification can be directly represented
using the negation and quantification of the background logic (preserving the dependency on possible worlds).

This way basic principles of the background logic (such as alpha conversion) can often be directly
applied to the embedded logic and the equational, definitional nature of the representation preverses
a larger degree of automation. Furthermore axioms in the embedded logic can often be equivalently
stated in the background logic, which makes model finding for the system easier and again increases
the degree of retained automation.

The approach of shallow semantical embeddings of modal logic was for example used in the analysis of
G\"odel's onthological argument and has shown great potential as a universal tool for logical embeddings
while retaining the existing infrastructure for automation as for example present in a framework like
Isabelle/HOL.

*}

(* TODO: no new section? *)
section{* Relational Type Theory vs. Functional Type Theory *}

text{*
The universality of this approach has since been challenged by Paul Oppenheimer and Edward Zalta
who argue in the paper \emph{Relations Versus Functions at the Foundations of Logic: Type-Theoretic
Considerations}(\ref{rtt}) that relational type theory is more general than functional type theory.
In particular they argue that the Theory of Abstract Objects, which is founded in relational type
theory, can not be properly characterized in functional type theory.

This has led to the question whether a shallow semantical embedding of the Theory of Abstract Objects
in a functional logical framework as Isabelle/HOL is at all possible, which is the core question
of the work presented here.

One of their main arguments is that unrestricted lambda expressions as present in functional type
theory lead to an inconsistency when combined with one of the axioms of the theory and indeed it
has been shown for early attempts on embedding the theory that despite significant efforts
to avoid the aforementioned inconsistency by excluding problematic lambda expressions in the embedded
logic, it could still be reproduced using an appropriate construction in the background logic.

Our solution circumvents this problem by identifying lambda expressions as one element of the
target language that behaves differently than their counterparts in the background logic and
consequently by representing lambda expressions of the target logic using a new \emph{defined}
kind of lambda expressions. This forces lambda expressions in the embedded logic to have a particular
semantics that is inspired by the \emph{Aczel-model} of the target theory and avoids prior inconsistencies.
*}

section{* Our Contribution *}

text{*
\begin{TODO}
  Embedding of second order fragment of PLM. Complex semantics, term-based syntax,
  scope of the embedding, technical challenges.
\end{TODO}
*}

chapter{* The Theory of Abstract Objects *}

section{* Motivation *}

text{*

\textquote[{\cite{MallyTheory}}]{
The theory of abstract objects is a metaphysical theory. Whereas physics attempts a systematic
description of fundamental and complex concrete objects, metaphysics attempts a systematic
description of fundamental and complex abstract objects. Abstract objects are the objects that are
presupposed by our scientific conceptual framework. For example, when doing natural science, we
presuppose that we can use the natural numbers to count concrete objects, and that we can use the
real numbers to measure them in various ways. It is part of our understanding of science that natural
laws exist (even if no one were around to discover them) and that the states of affairs that obtain
in the natural world are governed by such laws. As part of our scientific investigations, we
presuppose that objects behave in certain ways because they have certain properties, and that
natural laws govern not just actual objects that have certain properties, but any physically
possible object having those properties. So metaphysics investigates numbers, laws, properties,
possibilities, etc., as entities in their own right, since they seem to be presupposed by our very
understanding of the scientific enterprise. The theory of abstract objects attempts to organize
these objects within a systematic and axiomatic framework.

It would be a mistake to think that a theory postulating abstract objects is incompatible with our
theories of natural science, which seem to presuppose that the only things that exist are the things
governed by our true scientific theories. To see that the theory of abstract objects is compatible
with natural scientific theories, we only have to think of abstract objects as possible and actual
property-patterns. These patterns of properties objectify a group of properties that satisfy a
certain pattern. For example, it will turn out that the real number @{text "\<pi>"} can be thought of as the
pattern of properties satisfying the open sentence "According to the axioms of real number theory,
@{text "\<pi>"} has the property F" (where "F" is a variable ranging over properties). There are an
infinite number of properties satisfying this pattern (and an infinite number that don't).
Our theory of abstract objects will "objectify" or "reify" the group of properties satisfying this
pattern. So, on this view of what abstract objects are, we need not think of them as some ghostly,
imperceptible kind of nonspatiotemporal substances. Instead, they are possible and actual patterns
that are grounded in the arrangement of particles in the natural world and in the systematic behavior
and linguistic usage of mathematicians and scientists as they discover, state, and apply theories
of the natural world. 
}
*}

section{* The Language of PLM *}

text{*
The target of our embedding is the second order fragment of Object Theory as described
in chapter 7 of Edward Zalta's upcoming \emph{Principia Logico Metaphysica} (PLM) \cite{PM}.
The logical foundation of the target theory uses second-order modal relational type theory
as logical foundation.

The used language can be described in Backus-Naur Form (BNF)\cite[p. 170]{PM}. The following
grammatical categories are used:

\begin{tabular}[h]{ll}
  @{text "\<delta>"}   & individual constants \\
  @{text "\<nu>"}   & individual variables \\
  @{text "\<Sigma>\<^sup>n"}  & $n$-place relation constants ($n \geq 0$) \\
  @{text "\<Omega>\<^sup>n"}  & $n$-place relation variables ($n \geq 0$) \\
  @{text "\<alpha>"}   & variables \\
  @{text "\<kappa>"}   & individual terms \\
  @{text "\<Pi>\<^sup>n"}  & $n$-place relation terms ($n \geq 0$) \\
  @{text "\<Phi>\<^sup>*"}  & propositional formulas \\
  @{text "\<Phi>"}   & formulas \\
  @{text "\<tau>"}   & terms
\end{tabular}

The syntax of the target theory can now be described as BNF grammar\cite[ibid.]{PM}:

\includegraphics{BNF.pdf}

\begin{TODO}
  
\end{TODO}

*}

chapter{* Embedding *}

section{* Background *}

text{*
The background theory for the embedding is Isabelle/HOL, that provides a higher order logic
that serves as our meta-logic. For a short overview of the extents of the background theory
see \cite{WhatsInMain}.
*}

section{* Primitives *}

text{*
The following primitive types are the basis of the embedding:

\begin{itemize}
  \item Type @{type i} represents possible worlds in the Kripke semantics.
  \item Type @{type j} represents \emph{states} that are used for different interpretations
        of relations and connectives to achieve a hyper-intensional logic (see below).
  \item Type @{type bool} represents meta-logical truth values (@{text "True"} or @{text "False"})
        and is inherited from Isabelle/HOL.
  \item Type @{type \<omega>} represents ordinary urelements.
  \item Type @{type \<sigma>} represents special urelements.
\end{itemize}

Two constants are introduced:

\begin{itemize}
  \item The constant @{term dw} of type @{typeof dw} represents the designated actual world.
  \item The constant @{term dj} of type @{typeof dj} represents the designated actual state.
\end{itemize}

Based on the primitive types above the following types are defined:

\begin{itemize}
  \item Type @{type \<o>} is defined as the set of all functions of type @{typ "j\<Rightarrow>i\<Rightarrow>bool"} and
        represents truth values in the embedded logic.
  \item Type @{type \<upsilon>} is defined as @{datatype \<upsilon>}. This type represents urelements and an object
        of this type can be either an ordinary or a special urelement (with the respective type
        constructors @{term \<omega>\<upsilon>} and @{term \<sigma>\<upsilon>}).
  \item Type @{type \<Pi>\<^sub>0} is defined as a synonym for type @{type \<o>} and represents zero-place
        relations.
  \item Type @{type \<Pi>\<^sub>1} is defined as the set of all functions of type \mbox{@{typ "\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool"}}
        and represents one-place relations (for an urelement a one-place relation evaluates
        to a truth value in the embedded logic; for an urelement, a state and a possible world
        it evaluates to a meta-logical truth value).
  \item Type @{type \<Pi>\<^sub>2} is defined as the set of all functions of type \mbox{@{typ "\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool"}}
        and represents two-place relations.
  \item Type @{type \<Pi>\<^sub>3} is defined as the set of all functions of type \mbox{@{typ "\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool"}}
        and represents three-place relations.
  \item Type @{type \<alpha>} is defined as a synonym of the type of sets of one-place relations @{text "\<Pi>\<^sub>1 set"},
        i.e. every set of one-place relations constitutes an object of type @{type \<alpha>}. This type
        represents abstract objects.
  \item Type @{type \<nu>} is defined as @{datatype \<nu>}. This type represents individuals and can
        be either an ordinary urelement @{type \<omega>} or an abstract object @{type \<alpha>} (with the
        respective type constructors @{term \<omega>\<nu>} and @{term \<alpha>\<nu>}).
  \item Type @{type \<kappa>} is defined as the set of all objects of type @{typ "\<nu> option"} and
        represents individual terms. The type @{typ "'a option"} is part of Isabelle/HOL and
        consists of a type constructor @{term "Some x"} for an object @{term "x"} of type @{typ 'a}
        (in our case type @{type \<nu>}) and an additional special element called @{term "None"}.
        @{term "None"} is used to represent individual terms that are definite descriptions
        that are not logically proper (i.e. they do not denote an individual).
\end{itemize}

\begin{remark}
  The Isabelle syntax @{text "typedef \<o> = UNIV::(j\<Rightarrow>i\<Rightarrow>bool) set morphisms eval\<o> make\<o> .."}
  introduces a new abstract type @{type \<o>} that is represented by the full set (@{term UNIV})
  of objects of type @{typ "j\<Rightarrow>i\<Rightarrow>bool"}. The morphism @{text "eval\<o>"} maps an object of
  abstract type @{type \<o>} to its representative of type @{typ "j\<Rightarrow>i\<Rightarrow>bool"}, whereas 
  the morphism @{text "make\<o>"} maps an object of type @{typ "j\<Rightarrow>i\<Rightarrow>bool"} to the object
  of type @{type \<o>} that is represented by it. Defining these abstract types makes it
  possible to consider the defined types as primitives in later stages of the embedding,
  once their meta-logical properties are derived from the underlying representation.
  For a theoretical analysis of the representation layer the type @{type \<o>} can be considered
  a synonym of @{typ "j\<Rightarrow>i\<Rightarrow>bool"}.

  The Isabelle syntax @{text "setup_lifting type_definition_\<o>"} allows definitions for the
  abstract type @{type \<o>} to be stated directly for its representation type @{typ "j\<Rightarrow>i\<Rightarrow>bool"}
  using the syntax @{text "lift_definition"}.

  In the remainder of this document these morphisms are omitted and definitions are stated
  directly for the representation types.
\end{remark}

*}

section{* Individual Terms and Definite Descriptions *}

text{*
There are two basic types of individual terms in PLM: definite descriptions and individual variables.
For any logically proper definite description there is an individual variable that denotes
the same object.

In the embedding the type @{type \<kappa>} encompasses all individual terms, i.e. individual variables
\emph{and} definite descriptions. To use a pure individual variable (of type @{type \<nu>}) as an
object of type @{type \<kappa>} the decoration @{term "embedded_style (DUMMY\<^sup>P)"} is introduced:

@{thm[display] \<nu>\<kappa>.rep_eq[where x=x, THEN embedded_def]}

The expression @{term "embedded_style (x\<^sup>P)"} (of type @{typeof "x\<^sup>P"}) is now marked to always be
logically proper (it can only be substituted by objects that are internally of the form @{term "Some x"})
and to always denote the same object as the individual variable @{term "x"}.

It is now possible to define definite descriptions as follows:

@{thm[display] that.rep_eq[where x=\<phi>, THEN embedded_def]}

If the propriety condition of a definite description @{prop "\<exists>!x. \<phi> x dj dw"} holds,
i.e. \emph{there exists a unique @{term "x"}, such that @{term "\<phi> x"} holds for the actual state and
the actual world}, the term @{term "\<^bold>\<iota>x . \<phi> x"} is represented by @{term "Some (THE x . \<phi> x dj dw)"}.
Isabelle's \emph{THE} operator evaluates to the unique object, for which the given condition holds,
if there is a unique such object, and is undefined otherwise. If the propriety condition does not hold,
the term is represented by @{term "None"}.

The following meta-logical functions are defined to aid in handling individual terms:

@{thm[display] proper.rep_eq}

@{thm[display] rep.rep_eq}

@{term "the"} maps an object of type @{typ "'a option"} that is of the form @{term "Some x"} to
@{term "x"} and is undefined for @{term "None"}. For an object of type @{type \<kappa>} the expression
@{term "proper x"} is therefore true, if the term is logically proper, and if this is the case,
the expression @{term "rep x"} evaluates to the individual of type @{type \<nu>} that the term denotes.
*}

section{* Mapping from abstract objects to special Urelements *}

text{*
To map abstract objects to urelements (for which relations can be evaluated), a constant
@{term \<alpha>\<sigma>} of type @{typeof \<alpha>\<sigma>} is introduced, which maps abstract objects (of type @{type \<alpha>})
to special urelements (of type @{type \<sigma>}).

To assure that every object in the full domain of urelements actually is an urelement for (one or more)
individual objects, the constant @{term \<alpha>\<sigma>} is axiomatized to be surjective.

*}

section{* Conversion between objects and Urelements *}
(*
text{*

In order to represent relation exemplification as the function application of the meta-logical
representative of a relation, individual variables have to be converted to urelements (see below).
In order to define lambda expressions the inverse mapping is defined as well:

@{thm[display] \<nu>\<upsilon>_def}

@{thm[display] \<upsilon>\<nu>_def}

\begin{remark}
  The Isabelle notation @{term "case_\<nu>"} is used to define a function acting on objects of type
  @{type \<nu>} using the underlying types @{type \<omega>} and @{type \<alpha>}. Every object of type @{type \<nu>}
  is (by definition) either of the form @{term "\<omega>\<nu> x"} or of the form @{term "\<alpha>\<nu> x"}.
  The expression @{term "case_\<nu> \<omega>\<upsilon> (\<sigma>\<upsilon> \<circ> \<alpha>\<sigma>)"} for an argument @{term "y"} now evaluates to
  @{term "\<omega>\<upsilon> x"} if @{term "y"} is of the form @{term "\<omega>\<nu> x"} and to @{term "(\<sigma>\<upsilon> \<circ> \<alpha>\<sigma>) x"}
  (i.e. @{term "\<sigma>\<upsilon> (\<alpha>\<sigma> x)"}) if @{term "y"} is of the form @{term "\<alpha>\<nu> x"}.

  In the definition of @{term "\<upsilon>\<nu>"} the expression @{term "inv \<alpha>\<sigma>"} is part of the logic of
  Isabelle/HOL and defined as some (arbitrary) object in the preimage under @{term \<alpha>\<sigma>}, i.e. it
  holds that @{lemma "\<alpha>\<sigma> ((inv \<alpha>\<sigma>) x) = x" by (simp add: \<alpha>\<sigma>_surj surj_f_inv_f)},
  as @{term \<alpha>\<sigma>} is axiomatized to be surjective.
\end{remark}
*}
*)
section{* Exemplification of n-place relations *}

text{*
  Exemplification of n-place relations can now be defined. Exemplification of zero-place
  relations is simply defined as the identity, whereas exemplification of n-place relations
  for @{text "n \<ge> 1"} is defined to be true, if all individual terms are logically proper and
  the function application of the relation to the urelements corresponding to the individuals
  yields true for a given possible world and state:
  \begin{itemize}
    \item @{thm[display] exe0.rep_eq[where x=p, THEN embedded_def]}
    \item @{thm[display] exe1.rep_eq[where x=F and xa=x, THEN embedded_def]}
    \item @{thm[display] exe2.rep_eq[where x=F and xa=x and xb=y, THEN embedded_def]}
    \item @{thm[display] exe3.rep_eq[where x=F and xa=x and xb=y and xc=z, THEN embedded_def]}
  \end{itemize}
*}

section{* Encoding *}

text{*
  Encoding can now be defined as follows:

  @{thm enc.rep_eq[of x F, THEN embedded_def]}

  That is for a given state @{term s} and a given possible world @{term w} it holds that
  an individual term @{term x} encodes @{term F}, if @{term x} is logically proper,
  the representative individual variable of @{term x} is of the form @{term "\<alpha>\<nu> \<alpha>"} for
  some abstract object @{term \<alpha>} and @{term F} is contained in @{term \<alpha>} (remember that
  abstract objects are defined to be sets of one-place relations). Also note that encoding
  is a represented as a function of possible worlds and states to ensure type-correctness,
  but its evaluation does not depend on either.
*}

section{* Connectives and Quantifiers *}

text{*
  The reason to make truth values depend on the additional primitive type of \emph{states}
  is to achieve hyper-intensionality. The connectives and quantifiers are defined in such a
  way that they behave classically if evaluated for the designated actual state @{term "dj"},
  whereas their behavior is governed by uninterpreted constants in any other state.

  For this purpose the following uninterpreted constants are introduced:
  \begin{itemize}
    \item @{const I_NOT} of type @{typeof I_NOT}
    \item @{const I_IMPL} of type @{typeof I_IMPL}
  \end{itemize}

  Modality is represented using the dependency on primitive possible worlds using
  a standard Kripke semantics for a S5 modal logic.

  The basic connectives and quantifiers are now defined as follows:
  \begin{itemize}
    \item @{thm[display] not.rep_eq[of p, THEN embedded_def]}
    \item @{thm[display] impl.rep_eq[of p q, THEN embedded_def]}
    \item @{thm[display] forall\<^sub>\<nu>.rep_eq[of \<phi>, rename_abs s w x, THEN embedded_def]}
    \item @{thm[display] forall\<^sub>0.rep_eq[of \<phi>, rename_abs s w p, THEN embedded_def]}
    \item @{thm[display] forall\<^sub>1.rep_eq[of \<phi>, rename_abs s w F, THEN embedded_def]}
    \item @{thm[display] forall\<^sub>2.rep_eq[of \<phi>, rename_abs s w F, THEN embedded_def]}
    \item @{thm[display] forall\<^sub>3.rep_eq[of \<phi>, rename_abs s w F, THEN embedded_def]}
    \item @{thm[display] box.rep_eq[of p, THEN embedded_def]}
    \item @{thm[display] actual.rep_eq[of p, THEN embedded_def]}
  \end{itemize}

  Note in particular that the definition of negation and implication behaves
  classically if evaluated for the actual state @{term "s = dj"}, but
  is governed by the uninterpreted constants @{term I_NOT} and @{term I_IMPL} for
  @{term "s \<noteq> dj"}.
*}

section{* Lambda Expressions *}
(*
text{*
  The bound variables of the lambda expressions of the embedded logic are individual
  variables, whereas relations are represented as functions acting on urelements.
  Therefore the lambda expressions of the embedded logic are defined as follows:

  \begin{itemize}
    \item @{thm[display] lambdabinder0.rep_eq[of p, THEN embedded_def]}
    \item @{thm[display] lambdabinder1.rep_eq[of \<phi>, THEN embedded_def]}
    \item @{thm[display] lambdabinder2.rep_eq[of \<phi>, THEN embedded_def]}
    \item @{thm[display] lambdabinder3.rep_eq[of \<phi>, THEN embedded_def]}
  \end{itemize}

\begin{remark}
  For technical reasons Isabelle only allows lambda expressions for one-place relations
  to use a nice binder notation. For two- and three-place relations the following notation
  is used instead: \mbox{@{term[eta_contract=false] "embedded_style (\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<phi> x y))"}},
  \mbox{@{term[eta_contract=false] "embedded_style (\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<phi> x y z))"}}.
\end{remark}

  The representation of zero-place lambda expressions as the identity is straight-forward,
  the representation of n-place lambda expressions for @{text "n \<ge> 1"} is illustrated
  for the case @{text "n = 1"}:

  The matrix of the lambda expression @{term \<phi>} is a function from individual variables
  (of type @{type \<nu>}) to truth values (of type @{type \<o>}, resp. @{typ "j\<Rightarrow>i\<Rightarrow>bool"}).
  One-place relations are represented as functions of type @{typ "\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool"}, though,
  where @{type \<upsilon>} is the type of urelements.

  The evaluation of a lambda expression @{term "embedded_style (\<^bold>\<lambda>x. \<phi> x)"} for an urelment @{term u}
  therefore has to be defined as @{term "\<phi> (\<upsilon>\<nu> u)"}. Remember that @{term "\<upsilon>\<nu>"} maps an urelement
  to some (arbitrary) individual variable in its preimage. Note that this mapping is injective
  only for ordinary objects, not for abstract objects. The expression @{term "embedded_style (\<^bold>\<lambda>x. \<phi> x)"}
  only implies \emph{being @{text "x"}, such that there exists some @{text "y"} that is mapped
  to the same urelement as @{text "x"}, and it holds that @{text "\<phi> y"}}.
  Conversely, only \emph{for all @{text "y"} that are mapped to the same
  urelement as @{text "x"} it holds that @{text "\<phi> y"}} is a sufficient condition to conclude
  that @{text "x"} exemplifies @{term "embedded_style (\<^bold>\<lambda>x. \<phi> x)"}.
  \begin{remark}
    Formally the following statements hold, where @{term "[p in v]"} is the evaluation
    of the formula @{term "embedded_style p"} in the embedded logic to its meta-logical representation for
    a possible world @{text v} (and the actual state @{term dj}, for details refer to the next
    subsection):

    \begin{itemize}
      \item @{thm SanityTests.lambda_impl_meta}
      \item @{thm SanityTests.meta_impl_lambda}
    \end{itemize}
  \end{remark}

  Principia defines lambda expressions only for propositional formulas, though, i.e.
  for formulas that do \emph{not} contain encoding subformulas. The only other kind
  of formulas in which the bound variable @{term x} could be used in the matrix @{term \<phi>},
  however, are exemplication subformulas, which are defined to only depend on urelmements.
  Consider the following simple lambda-expression and the evaluation to its meta-logical
  representation:
  
  @{lemma[display] "embedded_style (\<^bold>\<lambda> x . \<lparr>F,x\<^sup>P\<rparr>) = make\<Pi>\<^sub>1 (\<lambda>u w s. eval\<Pi>\<^sub>1 F (\<nu>\<upsilon> (\<upsilon>\<nu> u)) w s)"
    by (simp add: embedded_style_def meta_defs meta_aux)}

  Further note that the following identity holds: \mbox{@{lemma "\<nu>\<upsilon> (\<upsilon>\<nu> u) = u" by (simp add: \<nu>\<upsilon>_\<upsilon>\<nu>_id)}}
  and therefore \mbox{@{lemma "embedded_style (\<^bold>\<lambda> x . \<lparr>F,x\<^sup>P\<rparr>) = F" by (simp add: embedded_style_def meta_defs meta_aux)}}, as desired.

  Therefore the defined lambda-expressions can accurately represent the lambda-expressions of the
  Principia. However the embedding still allows for lambda expressions that contain encoding
  subformulas. @{term "embedded_style \<lparr>\<^bold>\<lambda>x. \<lbrace>x\<^sup>P, F\<rbrace>, y\<^sup>P\<rparr>"} does \emph{not} imply
  @{term "embedded_style \<lbrace>y\<^sup>P, F\<rbrace>"}, but only that
  there exists an abstract object @{term z}, that is mapped to the same urelement as @{term x}
  and it holds that @{text "embedded_style \<lbrace>z\<^sup>P, F\<rbrace>"}. The former would lead to well-known
  inconsistencies, which the latter avoids.

  \begin{remark}
    Formally the following statements are true:
    \begin{itemize}
      \item @{thm[display] ArtificialTheorems.lambda_enc_4}
      \item @{thm[display] ArtificialTheorems.lambda_enc_5}
    \end{itemize}
  \end{remark}

  An example of a statement containing lambda-expressions that contain encoding subformulas
  that becomes derivable using the meta-logic is the following:

  @{lemma "[\<^bold>\<forall> F y . \<lparr>\<^bold>\<lambda>x. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>x\<^sup>P,F\<rbrace>, y\<^sup>P\<rparr> in v]" by (simp add: meta_aux meta_defs conn_defs forall_\<nu>_def forall_\<Pi>\<^sub>1_def)}

*}
*)
section{* Validity *}

text{*
  A formula is considered semantically valid for a possible world @{term v} if it evaluates
  to @{term True} for the actual state @{term dj} and the given possible world @{term v}.
  Semantic validity is defined as follows:
  
    @{thm[display] valid_in.rep_eq[of v \<phi>]}
  
  This way the truth evaluation of a proposition only depends on the evaluation of its representation
  for the actual state @{term dj}. Remember that for the actual state the connectives and quantifiers
  are defined to behave classically. In fact the only formulas of the embedded logic whose truth
  evaluation \emph{does} depend on all states are formulas containing encoding subformulas.
*}

section{* Concreteness *}

text{*
  Principia defines concreteness as a one-place relation constant. For the embedding care has to
  be taken that concreteness actually matches the primitive distinction between ordinary and
  abstract objects. The following requirements have to be satisfied by the introduced notion of
  concreteness:
  \begin{itemize}
    \item Ordinary objects are possibly concrete. In the meta-logic this means that for every
          ordinary object there exists at least one possible world, in which the object is concrete.
    \item Abstract objects are never concrete.
  \end{itemize}

  An additional requirement is enforced by axiom (\ref{PM-qml}.4)\cite{PM}. To satisfy this
  axiom the following has to be assured:
  \begin{itemize}
    \item Possibly contingent objects exist. In the meta-logic this means that there exists
          an ordinary object and two possible worlds, such that the ordinary object is
          concrete in one of the worlds, but not concrete in the other.
    \item Possibly no contingent objects exist. In the meta-logic this means that there exists
          a possible world, such that all objects that are concrete in this world, are concrete
          in all possible worlds.
  \end{itemize}

  In order to satisfy these requirements a constant @{const ConcreteInWorld} is introduced,
  that maps ordinary objects (of type @{type \<omega>}) and possible worlds (of type @{type i})
  to meta-logical truth values (of type @{type bool}). This constant is axiomatized in the
  following way:
  \begin{itemize}
    \item @{thm OrdinaryObjectsPossiblyConcreteAxiom}
    \item @{thm PossiblyContingentObjectExistsAxiom}
    \item @{thm PossiblyNoContingentObjectExistsAxiom}
  \end{itemize}

  Concreteness can now be defined as a one-place relation:

  @{thm[display] Concrete.rep_eq[THEN embedded_def]}

  The equivalence of the axioms stated in the meta-logic and the notion of concreteness in Principia
  can now be verified:

  \begin{itemize}
    \item @{thm[display] SanityTests.OrdAxiomCheck[rename_abs x v y u z z]}
    \item @{thm[display] SanityTests.AbsAxiomCheck[rename_abs x v y u z z]}
    \item @{thm[display] SanityTests.PossiblyContingentObjectExistsCheck}
    \item @{thm[display] SanityTests.PossiblyNoContingentObjectExistsCheck}
  \end{itemize}
*}

(*<*)
end
(*>*)
