(*<*)
theory Thesis
  imports AOT_PLM AOT_RestrictedVariables "HOL-Library.LaTeXsugar" (* "HOL-Library.OptionalSugar" *)
begin
(*>*)


chapter\<open>Introduction\<close>

section\<open>Motivation\<close>
text\<open>

Automated reasoning environments are already a vital part of the modern analysis
of mathematics and formal systems in general and their importance can only be expected
to increase in the future. However, building up a sound reasoning environment from scratch is a highly
non-trivial task. Consequently, there is only a limited number of trusted systems that can offer sophisticated
interactive and automated reasoning tools like Coq, HOL-Light or Isabelle/HOL (TODO: cite).
Furthermore, most of these systems have at least parts of their logical foundation in common,
for example they are all based on some variation of functional type theory (TODO: make sure this
can actually be stated as such in particular towards Coq).

On the other hand, there is still an ongoing debate about the most suitable foundational
system for mathematics (TODO: cite). While higher-order functional type
theory (HOL) is closely tied to set theory (see \cite{HigherOrderLogicSetTheoryFalseDilemma}, TODO: rethink this point and the citation;
also note e.g. the opposite statement \url{https://kwarc.info/people/frabe/Research/RI_isabelle_10.pdf})
and set theory has long been the prime choice for a common denominator of mathematical disciplines
(TODO: cite), its modern paradox-free axiomatization following Zermelo-Fraenkel is often viewed as
complex and counter-intuitive, respectively lacking in philosophical grounding and justification.
This sentiment was already expressed by Quine whose assessment is still commonly shared in present days:\footnote{TODO: precise quote.
in \url{https://plato.stanford.edu/entries/computational-philosophy/} Quine 1951 153; ideally also a reference
to a present formulation of the same sentiment.}

\blockquote{Whatever the inconveniences of type theory, contradictions such as \textins{the Russell paradox}
show clearly enough that the previous naive logic needs reforming.\textelp{} There have been other proposals
to the same end - one of them coeval with the theory of types. \textins{Quine cites Zermelo 1908. TODO: add reference}
But a striking circumstance is that none of these proposals, type theory included, has any intuitive foundation.
None has the backing of common sense. Common sense is bankrupt, for it wound up in contradiction.}

While there is prominent research into alternative foundational approaches (e.g. homotopy type
theory; topos theory; TODO: cite - maybe something else/more examples), independently of the question of whether
they have \emph{the backing of common sense}, a practical problem for such approaches
and a pragmatic defense of the use of set theory or HOL as foundation is the effort required in building up automated
reasoning systems that are on par with the existing tools that are available for processing theories
grounded in set theory or traditional functional higher-order type theory.

The following represents an attempt at overcoming this issue. We utilize the concept of a
@{emph \<open>shallow semantic embedding\<close>} (SSE) with abstraction layers (TODO: cite) to transfer the merits of
the sophisticated interactive and automated reasoning system Isabelle/HOL to a fundamentally
different foundational system, namely to Abstract Object Theory (AOT) (TODO: cite).

While it is not a requirement for our proposed general method, we demonstrate that
we can extend Isabelle/HOL by a customized reasoning infrastructure written in Isabelle/ML
that allows for an almost entirely transparent transfer of reasoning in our target logic and
abstracts the syntactic and inferential differences between Isabelle/HOL and AOT, while still
internally using the verified core logic of Isabelle/HOL as semantic backend. This means we
effectively construct a dedicated theorem proving environment for AOT that (1) is immediately guaranteed
to be sound, (2) can be used to explore the safety of axiomatic extensions to the system and (3) allows
for the reuse of the automation infrastructure available for Isabelle/HOL.

While our method can potentially be applied to a multitude of logical systems, Abstract Object Theory
is a particularly well-suited target. On the one hand, it aims to be a foundational metaphysical system
that can serve as the basis for mathematics and thereby stands in the tradition of Russell and
Whitehead's Principia Mathematica (TODO: cite), while in fact extending its scope to e.g. linguistics and
the sciences in general (TODO: rethink, cite). Furthermore, it attempts to overcome the dilemma noted
by Quine by basing its analysis on an intuitive distinction between \emph{ordinary} and \emph{abstract} objects
and equipping the latter with a very general and yet natural comprehension principle.(TODO: rethink, refer to later sections). On the other hand, it is based on logical foundations that significantly differ
from classical functional higher-order type-theory and were even argued to be incompatible (see \cite{rtt}).
Initial results of our research (see \cite{MScThesis}) demonstrated how our method for formally analyzing
models and semantics for such a system can be beneficial and vital for its soundness (TODO: refer to section with details).
During our continued work we could contribute to the evolution of Abstract Object Theory and
simultaneously arrived at a faithful representation of its model structure, semantics and
deductive system in Isabelle/HOL that can utilize the existing automated reasoning infrastructure.\footnote{Note,
however, that our embedding currently only extends to the second-order fragment of AOT, which is the subject
of PLM chapters (TODO: cite). We briefly discuss the challenges of representing full higher-order
object theory in chapter~\ref{HigherOrderAOT}.}

As a prime result, we can show that the construction of Natural Numbers and the derivation
of the Peano-Dedekind postulates, including Mathematical Induction, described in Principia
Logico-Metaphysica (TODO: cite) are verifiably sound. Furthermore, we can suggest the generalization of
an additional axiom required for this construction, that we believe strengthens
the argument that the construction does not require any inherently mathematical axioms.
\<close>

section\<open>Prior Work\<close>

text\<open>
The development of automated theorem provers has always been tied to the analysis of foundational formal
systems. Already in the middle of the last century, Betrand Russell was quick to recognize the potential
of computational methods, when confronted with the \emph{Logic Theorist}\footnote{A system developed by
Allen Newell and Herbert Simon at Carnegie Mellon and programmed by J. C. Shaw using the vacuum tubes of
the JOHNNIAC computer at the Institute for Advanced Study; TODO: cite.}, commonly regarded as the first
automated theorem prover (TODO: cite \url{https://plato.stanford.edu/entries/computational-philosophy/}),
and its ability to prove 38 out of 52 theorems from chapter two of Whitehead and Russell’s
Principia Mathematica (TODO: cite), including a proof more elegant than one of
Whitehead and Russell’s own (TODO: cite MacKenzie 1995, Loveland 1984, Davis 1957):\footnote{TODO: precise quote.
Letter from Russell to Simon; source reference in \url{https://plato.stanford.edu/entries/computational-philosophy/}
more text in \url{https://www.cl.cam.ac.uk/~jrh13/slides/lyon-04feb14/slides.pdf}. TODO: Verify primary source.}

\blockquote{I am delighted to know that Principia Mathematica can now be done by machinery \textelp{} I am quite
willing to believe that everything in deductive logic can be done by machinery. \textelp{} I wish
Whitehead and I had known of this possibility before we wasted 10 years doing it by hand.}

Since then there has been significant progress both in the development of automated theorem provers
in general and in the application of computational methods to logical theories in particular. Some
of the more recent developments in this area are outlined in the following sections.
\<close>

subsection\<open>Prior Computational Analysis of Abstract Object Theory\<close>

text\<open>

The computational analysis of Abstract Object Theory (AOT) was pioneered by Fitelson and Zalta in
\cite{FitelsonZalta}. They used the first-order system Prover9 (TODO: cite) for their work and were able to 
verify the proofs of the theorems in AOT's analysis of situations and possible worlds in
\cite{zalta1993}. Furthermore, they discovered an error in a theorem about Platonic Forms in~\cite{PelletierZalta}
that was left as an exercise.
Other work with Prover9 that does not target AOT includes the simplification of the reconstruction
of Anselm's ontological argument (in \cite{OppenheimerZalta2011}, Oppenheimer and Zalta show that
only one of the three premises they used in \cite{OppenheimerZalta1991} is sufficient) or the
reconstruction of theorems in Spinoza's @{emph \<open>Ethics\<close>} in \cite{SpinozaProver9}.

However, there are inherent limitations to the approach of analyzing higher-order theories like AOT
with the help of first-order provers. While it is possible to reason about the first-order truth
conditions of statements by introducing sort predicates and using a number of special techniques
to translate the statements into the less-expressive language of multi-sorted first-order logic
(a detailed account of such techniques is given in \cite{AlamaZalta2015}), the complexity of the
resulting representation increases for expressive, higher-order philosophical claims.
In general, this approach may be sufficient for analyzing concrete isolated arguments, but it becomes
infeasible to construct a natural representation of an entire expressive higher-order theory and
its full deductive system. (TODO: cite from paper)
\<close>
subsection\<open>Prior Work involving Shallow Semantic Embeddings\<close>

text\<open>
Independently, the emergence of sophisticated higher-order reasoning environments like Isabelle/HOL
allows for a different approach, namely the analysis of arguments and theories directly in higher-order
logic by constructing Shallow Semantic Embeddings (SSEs) \cite{UniversalReasoning}. In contrast to
a @{emph \<open>deep semantic embedding\<close>} which defines the syntax of a target system using an inductive data
structure and evaluates statements semantically by recursively traversing this data structure,
a @{emph \<open>shallow\<close>} semantic embedding instead provides a syntactic translation from the target logic
to the meta-logic. This is done by reusing as much of the infrastructure of the meta-logic as possible,
while @{emph \<open>defining\<close>} the syntactic elements of the target logic that are not part of
the meta-logic by means of a representation of their semantics. Since sets have a natural
representation in higher-order logic, this approach works well for any logical system that
has a semantics defined in terms of sets. The approach of shallow semantic embeddings is discussed in
more detail in chapter~\ref{SSEs}.

(TODO: citation is embedding in simple type theory, not Isabelle/HOL. Rethink.)
In \cite{ModalLogics} Benzm\"uller and Paulson represented quantified modal logic using SSEs by means
of embedding modal operators based on their Kripke semantics (TODO cite). This allowed for an
extensive analysis of G\"odel's ontological argument in second-order S5 modal logic and weaker logics
such as KB (TODO cite), followed by a range of studies of similar ontological arguments (TODO cite). TODO: newer work by Benzm\"uller.

The advantage of these studies using SSEs compared to the earlier use of first-order systems is that arguments
can be represented in their native syntax and are thereby readable and maintainable, while the theorem
proving environment is capable of automatically transforming statements into a suitable first-order
representation on the fly to allow first-order theorem provers like E or SPASS (TODO: cite) to perform
proof search much like e.g. Prover9 was able to do on a manually constructed first-order representation.

These studies were still mainly concerned with case studies of concrete arguments or
with conservative extensions of higher-order logic like quantified higher-order modal logic.
\<close>

subsection\<open>Analysis of AOT with the SSE Approach\<close>

text\<open>
Initial results of our own research were reported in~\cite{MScThesis}, in which we applied an extended
version of the technique of SSEs to AOT. For AOT no extensive prior analysis of canonical models was available, in contrast to, for example,
the extensive analysis of Kripke models for higher-order modal logic that served as theoretical
basis for the previous work using SSEs mentioned above. While the so-called Aczel models of object theory
(TODO: cite) provide an important building block for constructing models of AOT in HOL, no full
set-theoretic model of object theory had been constructed. In \cite{MScThesis} we extended the
existing Aczel models to a richer model structure that was capable of approximating the validity
of statements of the at the time most recent formulation of the second-order fragment of AOT in Principia Logico-Metaphysica (PLM) (TODO: cite).
Furthermore, we introduced the new concept of @{emph \<open>abstraction layers\<close>}. An abstraction layer consists
of a derivation of the axioms and deduction rules of a target system from a given semantics that is
then considered as ground truth while "forgetting" the underlying semantic structure, i.e. the
reasoning system is prevented from using the semantics for proofs, but is instead configured to solely
rely on the derived axioms and deduction rules.
Abstraction layers turned out to be a helpful means for reasoning within a target theory without
the danger of deriving artifactual theories, even in the absence of a formal completeness result
about the used semantics.

A major initial result of this project, reported in~\cite{MScThesis}, was the discovery of an oversight
in the formulation of AOT that allowed for the reintroduction of a previously known paradox into the system. While multiple quick
fixes to restore the consistency of AOT were immediately available, in the aftermath of this result
AOT was significantly reworked and improved. The result triggered an extensive debate
of the foundations of AOT which culminated in the extension of the free logic of AOT to relations,
while previously it was restricted to individual terms only (to account for non-denoting
definite descriptions). This reworking of AOT was accompanied by a continuous further development of its
embedding in Isabelle/HOL. This mutually beneficial mode of work was described in
(TODO cite Open Philosophy) and resulted in a now stabilized and improved formulation of AOT and a
matching embedding of its second-order fragment. The details of this process and its results are
the main subject of this thesis. 

\<close>

section\<open>Contributions and Structure of the Thesis\<close>text\<open>\label{Structure}\<close>

text\<open>
In the following, we first provide a more detailed description of Shallow Semantical Embeddings (chapter~\ref{SSEs}) and
a brief introduction to Abstract Object Theory (chapter~\ref{AOT}).

Based on that, chapter~\ref{SSEofAOT} describes
the constructed embedding of the second-order fragment of Abstract Object Theory in Isabelle/HOL while
highlighting the contributions of the embedding to the theory of abstract objects on the one hand and
the techniques developed for its implementation up to the dedicated reasoning system implemented in
Isabelle/ML on the other hand.

In chapter~\ref{NaturalNumbers} we present the results on the derivation of Natural Numbers and
Mathematical Induction and discuss our proposed extension of AOT with a more general comprehension
principle for relations among abstract objects.

Finally, in chapter~\ref{HigherOrderAOT} we briefly discuss the issue of extending the current system to
encompass the full higher-order type-theoretic version of Abstract Object Theory.

The thesis is generated using Isabelle's document preparation system (TODO: cite).
In particular, all statements cited in the thesis are renderings of verified theorems
in the embedding, unless specifically stated otherwise and marked with vertical bars
at the page margins.

The appendix contains a rendering of the raw theory files of the embedding. While
Isabelle allows producing latex code for raw theories directly, semantic information
e.g. about free vs. bound variables are lost in the process, which reduces the
readability of the rendering. For that reason, we devised a custom theory presentation
system written in Isabelle/Scala similar to Isabelle's HTML theory presentation that
uses PIDE markup information (TODO: cite) to provide a color-coded rendering of the
theory files equipped with hyperlinks for cross-references. We discuss this process in
more detail in (TODO: actually do and cite).

Whenever a theorem in the appendix refers to a specific item number in PLM, the
corresponding item number can be found in parentheses at the right page margin.

TODO: Überleitung.

Bullet point thoughts:
  \<^item> General method for analyzing philosophical arguments and theories: SSEs.
  \<^item> AOT as challenging target, but feasible to implement to the benefit of the theory
    and the method.
  \<^item> Reproduction of the full deductive system of the theory in readable and usable
    form.
  \<^item> Demonstration of the extend of the target theory and the practical feasibility
    to reason in the target system in Natural Number theory.
  \<^item> Extensions and Progress in the target theory due to our work.
\<close>


chapter\<open>Shallow Semantic Embeddings\<close>text\<open>\label{SSEs}\<close>

section\<open>Embeddings of Domain-Specific Languages\<close>
text\<open>

In computer science, deep and shallow embeddings have been a traditional means to implement domain-specific
languages by embedding them into general-purpose host languages (see for example \cite{DomainSpecificLanguages}).
A simple example is a language of @{emph \<open>expressions\<close>} that can be either integer constants, resp. literals,
or the addition of two other expressions.
If we consider Isabelle/HOL as the host language in this process, the following would constitute a
@{emph \<open>deep\<close>} embedding of this language:
\<close>

(*<*)
locale Deep
begin
(*>*)

datatype expression = Literal int | Addition expression expression
primrec eval :: \<open>expression \<Rightarrow> int\<close> where
        \<open>eval (Literal x) = x\<close>
      | \<open>eval (Addition x y) = eval x + eval y\<close>

(*<*)
lemma CommutativeAdditionNonIdentity: \<open>Addition x y \<noteq> Addition y x\<close> if \<open>x \<noteq> y\<close>
  using that Deep.expression.inject(2) by auto
lemma CommutativeAdditionEquivalent: \<open>eval (Addition x y) = eval (Addition y x)\<close>
  by simp
end
(*>*)

text\<open>
The deep embedding consists of a (usually recursive) algebraic datatype that captures the syntax of
the language to be embedded. This syntax is then given a semantics by means of an evaluation function
that traverses this algebraic datatype.@{footnote \<open>In the setting of logical theories this evaluation
function would usually depend on interpretations and assignment functions of a model. Since the simple
language of expression used as example here neither involves constants nor variables (respectively since
literals have trivial interpretations), however, this is not necessary. TODO: rethink.\<close>}
A shallow embedding on the other hand, represents the syntactic elements of a target language directly
by its semantics. In our example, the semantic domain of expressions is the integers. On this domain,
the operations are then @{emph \<open>defined\<close>} directly by means of their semantics:
\<close>

(*<*)
locale Shallow
begin
(*>*)

type_synonym expression = int
definition Literal :: \<open>int \<Rightarrow> expression\<close> where \<open>Literal x \<equiv> x\<close>
definition Addition :: \<open>expression \<Rightarrow> expression \<Rightarrow> expression\<close> where \<open>Addition x y \<equiv> x + y\<close>

(*<*)
lemma CommutativeAdditionIdentity: \<open>Addition x y = Addition y x\<close>
  by (simp add: Shallow.Addition_def)
end

lemma Deep_Shallow_Literal: \<open>Deep.eval (Deep.Literal x) = Shallow.Literal x\<close>
  by (simp add: Deep.eval.simps(1) Shallow.Literal_def)

lemma Deep_Shallow_Addition: \<open>Deep.eval (Deep.Addition x y) = Shallow.Addition (Deep.eval x) (Deep.eval y)\<close>
  by (simp add: Deep.eval.simps(2) Shallow.Addition_def)

(*>*)

text\<open>
Note that in the shallow embedding, the domain of @{typ \<open>Shallow.expression\<close>}s is shared with the
meta-language by directly representing expressions in the type to which they evaluate semantically
in the deep embedding, namely @{typ \<open>int\<close>} in the example.

There is a natural correspondence between the deep and shallow representations of this
language. In particular it holds that @{thm[show_question_marks = false, names_short = false] Deep_Shallow_Literal} and
@{thm[show_question_marks = false, names_short = false] Deep_Shallow_Addition}.@{footnote \<open>TODO: Explain
qualified names; mention that this gets more complex when involving interpretation and assignment functions.\<close>}
So semantic evaluation is implicit in the shallow embedding.
On the other hand there are also differences between the two representation. For example, in the
deep embedding adding @{term x} to @{term y} results in an expression that is different from the expression of adding
 @{term y} to  @{term x} for distinct  @{term x} and  @{term y}, even though they are equivalent under evaluation:

@{thm[show_question_marks = false, names_short = false, display = true]
  Deep.CommutativeAdditionNonIdentity Deep.CommutativeAdditionEquivalent}

In contrast, commuted additions are identical in the shallow embedding:

@{thm[show_question_marks = false, names_short = false, display = true] Shallow.CommutativeAdditionIdentity}

In fact, the shallow embedding can be thought of as a @{emph \<open>quotient\<close>} of the deep embedding under
semantic evaluation. TODO: something formal about this? Or rather instead refer to the section
about models and embeddings?

While there are several advantages and disadvantages of using shallow vs. deep embeddings for
Domain-Specific languages, we forgo a detailed discussion of them here (TODO: maybe citation?) and
focus on the application of similar modes of embeddings to logical reasoning in the next sections.
\<close>

section\<open>SSEs as Universal Reasoning Tools\<close>

text\<open>

In \cite{UniversalReasoning}, Benzm\"uller develops the idea of using @{emph \<open>Shallow Semantic Embeddings\<close>} (SSEs)
in classical higher-order logics as a means for universal reasoning. TODO: paraphrase the idea a bit.
High-level concept and motivation here versus more technical details in the following sections.

\<close>

section\<open>SSE of Quantified Higher-Order Modal Logic\<close>text\<open>\label{SimpleS5}\<close>
text\<open>

An example of a non-classical logic that is used prominently in metaphysics is Quantified Higher-Order
Modal Logic in various different axiomatizations. While there have been extensive studies of
modal logics using SSEs in Isabelle/HOL (see: TODO: cite a good paper about QML in Isabelle/HOL
maybe: \url{http://page.mi.fu-berlin.de/cbenzmueller/papers/C47.pdf} or similar), we restrict ourselves
to the discussion of a simple embedding of S5 modal logic to further illustrate the general
concept of SSEs.
\<close>

(*<*)
locale SimpleS5 = AOT_no_meta_syntax
begin
(*>*)

text\<open>
A natural semantic basis for SSEs of any modal logic is its Kripke-semantics (TODO cite?).
In general, a Kripke frame consists of a set of possible worlds and a binary relation on these worlds
called @{emph \<open>accessibility relation\<close>}. For S5 there are two versions of semantics, one in which the
accessibility relation is an equivalence relation and one in which there is no accessibility relation at
all (TODO: cite M. Fitting "A Simple propositional S5 Tableau System"). For our purpose the simpler
model suffices.@{footnote \<open>We will later argue that this is a natural choice for the particular modal
logic of Abstract Object Theory due to its additional actuality operator and rigid definite descriptions. TODO: actually do that.\<close>}

For possible worlds we can introduce a primitive type in Isabelle/HOL.
\<close>

typedecl w

text\<open>
A Kripke model further involves a relation between possible worlds and modal formulas that is
usually read as a formula @{emph \<open>being satisfied at\<close>} a possible world. So the semantic domain of
propositions is boolean-valued function acting on (or, equivalently, sets of) possible worlds.
In an SSE we use the semantic domains as type for the formulas themselves, so we can introduce
a type @{text \<o>} of propositions as synonym of the type of functions mapping possible worlds (of type @{typ w})
to booleans (type @{typ bool}). This way the proposition can, as a function, be applied to a possible
world, yielding @{term True}, if the proposition is true at that world or @{term False} otherwise.
\<close>

type_synonym \<o> = \<open>w \<Rightarrow> bool\<close>

text\<open>
A proposition is @{emph \<open>valid\<close>} in case it is satisfied in all worlds.@{footnote \<open>The specification
in parentheses after the type @{typ \<open>\<o> \<Rightarrow> bool\<close>} is @{emph \<open>mixfix notation\<close>} used to introduce
the symbol @{text \<Turnstile>} as syntax for the introduced constant @{text valid}. The ability to
introduce custom syntax in Isabelle/HOL is discussed in more detail in section~\ref{SSESyntax}.\<close>}
\<close>

definition valid :: \<open>\<o> \<Rightarrow> bool\<close> (\<open>\<Turnstile> _\<close> 100) where
  \<open>\<Turnstile> p \<equiv> \<forall> w . p w\<close>

text\<open>Now the classical logical operators can be defined as follows (note the bold print for the
defined operators versus the non-bold print of the corresponding operators of the meta-logic):\<close>

definition not :: \<open>\<o> \<Rightarrow> \<o>\<close> (\<open>\<^bold>\<not>_\<close> [140] 140) where
  \<open>\<^bold>\<not>p \<equiv> \<lambda> w . \<not>p w\<close>
definition imp :: \<open>\<o> \<Rightarrow> \<o> \<Rightarrow> \<o>\<close> (infixl \<open>\<^bold>\<rightarrow>\<close> 125) where
  \<open>p \<^bold>\<rightarrow> q \<equiv> \<lambda> w . p w \<longrightarrow> q w\<close>
definition conj :: \<open>\<o> \<Rightarrow> \<o> \<Rightarrow> \<o>\<close> (infixl \<open>\<^bold>\<and>\<close> 135) where
  \<open>p \<^bold>\<and> q \<equiv> \<lambda> w . p w \<and> q w\<close>
definition disj :: \<open>\<o> \<Rightarrow> \<o> \<Rightarrow> \<o>\<close> (infixl \<open>\<^bold>\<or>\<close> 130) where
  \<open>p \<^bold>\<or> q \<equiv> \<lambda> w . p w \<or> q w\<close>

text\<open>The additional modal operators, i.e. the box operator for @{emph \<open>necessity\<close>} and the
     diamond operator for @{emph \<open>possibility\<close>}, can be further defined as:\<close>

definition box :: \<open>\<o> \<Rightarrow> \<o>\<close> (\<open>\<^bold>\<box>_\<close> [150] 150) where
  \<open>\<^bold>\<box>p \<equiv> \<lambda> w . \<forall> v . p v\<close>
definition dia :: \<open>\<o> \<Rightarrow> \<o>\<close> (\<open>\<^bold>\<diamond>_\<close> [150] 150) where
  \<open>\<^bold>\<diamond>p \<equiv> \<lambda> w . \<exists> v . p v\<close>

text\<open>Now Isabelle can show automatically that the S5 axioms are valid:\<close>

lemma K: \<open>\<Turnstile> \<^bold>\<box>(p \<^bold>\<rightarrow> q) \<^bold>\<rightarrow> (\<^bold>\<box>p \<^bold>\<rightarrow> \<^bold>\<box>q)\<close>
  by (auto simp: box_def imp_def valid_def)
lemma T: \<open>\<Turnstile> \<^bold>\<box>p \<^bold>\<rightarrow> p\<close>
  by (auto simp: box_def imp_def valid_def)
lemma 5: \<open>\<Turnstile> \<^bold>\<diamond>p \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>p\<close>
  by (auto simp: box_def dia_def imp_def valid_def)

text\<open>The proofs of both axioms are automatically found by @{command sledgehammer} (TODO cite?).

So far we have constructed an embedding of propositional S5 modal logic using what is commonly
known as \emph{Standard Translation} of modal logic (TODO: cite). However it is straightforward
to enrich this embedding with quantification.
\<close>

definition forall :: \<open>('a \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close> (binder \<open>\<^bold>\<forall>\<close> 110) where
  \<open>\<^bold>\<forall> x . \<phi> x \<equiv> \<lambda>w . \<forall> x . \<phi> x w\<close>
definition exists :: \<open>('a \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close> (binder \<open>\<^bold>\<exists>\<close> 110) where
  \<open>\<^bold>\<exists> x . \<phi> x \<equiv> \<lambda>w . \<exists> x . \<phi> x w\<close>

text\<open>Note that we didn't have to introduce any particular type for individuals, but stated
polymorphic definitions relative to a type variable @{typ 'a}. This way the same quantifier
can be used for propositions themselves, any desired type for individuals or even properties of
any order.

As an example of theorems involving quantifiers and modal logic, we derive the Barcan formulas.
@{command sledgehammer} can again automatically provide proofs.\<close>

lemma \<open>\<Turnstile> (\<^bold>\<forall>x . \<^bold>\<box>\<phi> x) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x . \<phi> x)\<close>
  by (auto simp: box_def forall_def imp_def valid_def)
lemma \<open>\<Turnstile> \<^bold>\<diamond>(\<^bold>\<exists>x . \<phi> x) \<^bold>\<rightarrow> (\<^bold>\<exists>x . \<^bold>\<diamond>\<phi> x)\<close>
  by (auto simp: dia_def exists_def imp_def valid_def)
lemma \<open>\<Turnstile> \<^bold>\<box>(\<^bold>\<forall>x . \<phi> x) \<^bold>\<rightarrow>  (\<^bold>\<forall>x . \<^bold>\<box>\<phi> x)\<close>
  by (auto simp: box_def forall_def imp_def valid_def)
lemma \<open>\<Turnstile> (\<^bold>\<exists>x . \<^bold>\<diamond>\<phi> x) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>x . \<phi> x)\<close>
  by (auto simp: dia_def exists_def imp_def valid_def)

text\<open>
However, note that the automatic proofs again unfold the semantic definitions. We have shown that
the Barcan formulas are valid in the constructed embedding, but from the proofs we cannot tell
which axioms are required for proving them.@{footnote \<open>As a matter of fact we did not even state any
axioms governing implications or quantifiers in the embedded logic.\<close>}

Depending on the application, it can be enough to be able to tell if a theorem is semantically
valid or if a statement semantically follows from a set of assumptions. However, for the purpose
of implementing a full logical theory including its own deductive system, semantic validity is
not the primary concern, but rather derivability from the formal system.

Fortunately, it is possible to restrict Isabelle's automated reasoning tools like
@{command sledgehammer}, s.t. they may not unfold semantic definitions. If this is done
at larger scale and in a reliable manner for the purpose of analyzing derivability in
a given deductive system, we say that we introduce @{emph \<open>abstraction layers\<close>} to the SSE.
\<close>

(*<*)
end
(*>*)

section\<open>SSEs with Abstraction Layers\<close>

text\<open>The concept of enriching traditional SSEs with abstraction layers was first introduced
in \cite{MScThesis}. The goal is to be able to use the automated reasoning tools provided
by a system like Isabelle/HOL not merely to analyze semantic validity of statements in the
embedded theory, but to reliably determine the derivability of a statement from the deductive
system of the theory itself, while still retaining ensured soundness. While Isabelle provides
its own mechanisms for abstract reasoning like type @{command class}es, @{command locale}s and
@{command specification}s, those are not primarily designed for this exact purpose and come with
limitations that can make them unsuitable to achieve that purpose on their own,
as described in more detail in the following section.

TODO: more high-level description before technical details?

The main tool for automated reasoning in Isabelle/HOL in question is @{command sledgehammer} (TODO: cite again?).
@{command sledgehammer} can be invoked during any proof and will try to automatically find a proof for
the current proof goal. To that end, simply speaking,@{footnote \<open>For the full and precise details of the process
refer to TODO: cite.\<close>} it collects all theorems derived in the current @{command theory} context
together with all local assumptions, and processes the resulting set of theorems heuristically to find
a subset of relevant theorems. It then encodes the problem of deriving the current goal from the chosen
theorems and assumptions in a format that can be consumed by external theorem provers like
CVC4, E or SPASS (TODO: cite). This may, for example, involve a translation from higher-order problems
to first-order problems. If one of the invoked provers can prove the current goal, @{command sledgehammer}
tries to reconstruct a short proof using Isabelle's proving methods (e.g. @{method metis} or @{method blast} TODO: cite?)
that can be directly inserted to prove the current goal.

The relevant part of the process to consider for the purpose of constructing an abstraction layer is
the initial selection of theorems from the @{command theory} context.
We do not want @{command sledgehammer} to use the equational theorems that unfold our semantic definitions,
but instead derive the goals from only the axioms and specific derivational rules we defined that correspond
to the rules of the deductive system of the embedded theory.
@{command sledgehammer} allows us to provide some guidance in its choice of theorems. It is possible
to (1) indicate that a certain set of theorems is likely to be helpful in the proof (using @{text \<open>add:\<close>}),
(2) prevent it from using certain theorems (either using @{text \<open>del:\<close>} or by marking the theorems with
the special attribute @{attribute no_atp} or (3) to provide it with a specific set of theorems to use
directly without taking any other theorems into account.

Conceptually, option (3) is the best fit for the purpose of abstraction layers and was used in
\cite{MScThesis}. However, @{command sledgehammer} will no longer employ its heuristics and machine
learning algorithms to filter the provided theorems to find relevant theorems, but will directly use
the provided set of theorems. Consequently, the proving power and therefore the usefulness of
@{command sledgehammer} is significantly diminished, especially for larger theories.

In our current implementation, we therefore use option (2) instead. However, this comes with
some challenges. While the equational theorems introduced by simple @{command definition}s can
easily be collected and marked, other more advanced constructions in Isabelle like type definitions
or @{command lift_definition}s (TODO: cite) introduce several theorems implicitly. While
it is still possible to collect these theorems manually, the process is cumbersome and error-prone.
TODO: cite sledgehammer user guide section 6.1.

On the other hand, it is not possible to simply exclude @{emph \<open>all\<close>} theorems that were defined
up to a certain point, since this includes the theorems of Isabelle's @{theory Main} theory, i.e.
- among others - the construction of classical higher-order logic from Isabelle's more basic @{theory Pure}
logic. This includes theorems @{command sledgehammer} relies on and disbarring them will leave it
non-functional (conceptually, such theorems in question can be thought of as meta-theorems about
derivations in our context TODO: rethink that, maybe collect examples).

The solution used in the current embedding of Abstract Object Theory is the use of option (2), while
using Isabelle's internal ML API to automatically collect theorems to be added to an exclusion
list. For convenience, an new command @{command AOT_sledgehammer} is introduced that internally
configures @{command sledgehammer} (TODO: rethink; in practice I usually set up sledgehammer globally instead)
to use the desired set of theorems and then passes the current
proof state to it. With this method we can achieve significantly better proof automation than in
the earlier version in \cite{MScThesis}.

\<close>

section\<open>Isabelle's Native Abstraction Mechanisms and their Limitations\<close>

text\<open>
TODO: reformulate along the lines of "While for the purpose above constructing a minimal model
would suffice, there are several reasons to..." plus "to that end we use Isabelle's abstraction mechanisms..."
plus "However, the use of these mechanisms in turn is not sufficient to provide the same assurances as
abstraction layers, respectively cannot sufficiently deal with polymorphic assumptions, etc.".
Also: explain rationale of being able to judge extensions of the system with new axioms and
using @{command nitpick}.

Additionally, we attempt to keep the constructed embedding as abstract as possible and try to make it
logically impossible for details of the used model to "bleed through" to the abstraction layer.
To that end, for example, we extensively use @{command specification}s instead of definitions (TODO: cite).
A @{command specification} is used to assert statements about previously uninterpreted constants
(as introduced using @{command consts}). The @{command specification} command opens a proof context
that requires the user to show that there exists a concrete instantiation for the given constants,
for which the desired statements hold. Internally it then uses Isabelle's Hilbert-Epsilon-operator
@{term \<open>SOME x. \<phi> x\<close>} to augment the given constants with a concrete definition. However, care
has to be taken to ensure that there actually is a choice to be made.

To illustrate this issue, we showcase the construction of a hyperintensional logic in which
@{term \<open>p \<and> q\<close>} implies both @{term p} and @{term q} and vice-versa, but it does not hold
that @{term \<open>(p \<and> q) = (q \<and> p)\<close>}.
We first show a construction that will fail due to a choice of representation types that
implies extensionality:
(TODO: consider moving these sections to different theory files to get rid of the subscripts)
\<close>

typedef \<o>\<^sub>1 = \<open>UNIV::bool set\<close>.. \<comment> \<open>Introduce a type of propositions @{typ \<o>\<^sub>1} as a copy of the type of booleans.\<close>

definition valid_\<o>\<^sub>1 :: \<open>\<o>\<^sub>1 \<Rightarrow> bool\<close> where
  \<open>valid_\<o>\<^sub>1 p \<equiv> Rep_\<o>\<^sub>1 p\<close> \<comment> \<open>Validity is simply given by the boolean representing the proposition.\<close>

consts \<o>\<^sub>1_conj :: \<open>\<o>\<^sub>1 \<Rightarrow> \<o>\<^sub>1 \<Rightarrow> \<o>\<^sub>1\<close> (infixl \<open>\<^bold>\<and>\<close> 100)

specification (\<o>\<^sub>1_conj) \<comment> \<open>We specify our conjunction by introduction and elimination rules.\<close>
  \<o>\<^sub>1_conjE1: \<open>valid_\<o>\<^sub>1 (p \<^bold>\<and> q) \<Longrightarrow> valid_\<o>\<^sub>1 p\<close>
  \<o>\<^sub>1_conjE2: \<open>valid_\<o>\<^sub>1 (p \<^bold>\<and> q) \<Longrightarrow> valid_\<o>\<^sub>1 q\<close>
  \<o>\<^sub>1_conjI: \<open>valid_\<o>\<^sub>1 p \<Longrightarrow> valid_\<o>\<^sub>1 q \<Longrightarrow> valid_\<o>\<^sub>1 (p \<^bold>\<and> q)\<close>
text\<open>We need to prove that there is a term satisfying the above specification. The natural choice is
     the lifted conjunction on the booleans.@{footnote \<open>For any @{command typedef}, Isabelle intoduces
     constants prefixed with @{text Abs_} and @{text Rep_}, mapping the representation type to the
     defined abstract type and vice-versa.\<close>}\<close>
  by (rule exI[where x=\<open>\<lambda> p q . Abs_\<o>\<^sub>1 (Rep_\<o>\<^sub>1 p \<and> Rep_\<o>\<^sub>1 q)\<close>])
     (auto simp: Abs_\<o>\<^sub>1_inverse valid_\<o>\<^sub>1_def)

text\<open>However, even though the identity of commuted conunctions not part of the @{command specification},
     it is @{emph \<open>still\<close>} derivable.\<close>
lemma \<open>p \<^bold>\<and> q = q \<^bold>\<and> p\<close>
  by (metis Rep_\<o>\<^sub>1_inject \<o>\<^sub>1_conjE1 \<o>\<^sub>1_conjE2 valid_\<o>\<^sub>1_def)

(*<*)
no_notation \<o>\<^sub>1_conj (infixl \<open>\<^bold>\<and>\<close> 100)
(*>*)

text\<open>The reason is that there is only one choice for a conjunction operator on the booleans
and this choice is commutative.

A way around this  issue is to not only introduce opaque constants by @{command specification}, but
to also take care that the @{emph \<open>type\<close>} of these constants can actually deliver the desired degree
of intentionality. For example, we introduce an opaque @{emph \<open>intensional type\<close>} for propositons
 that merely has a boolean @{emph \<open>extension\<close>} as follows:
\<close>

typedecl \<o>\<^sub>2 \<comment> \<open>Introduce an abstract type for propositions.\<close>

text\<open>Axiomatically introduce a surjective extension function mapping the abstract propositions
to their boolean extension.\<close>
axiomatization \<o>\<^sub>2_ext :: \<open>\<o>\<^sub>2 \<Rightarrow> bool\<close> where
  \<o>\<^sub>2_ext_surj: \<open>surj \<o>\<^sub>2_ext\<close>

definition valid_\<o>\<^sub>2 :: \<open>\<o>\<^sub>2 \<Rightarrow> bool\<close> where
  \<open>valid_\<o>\<^sub>2 p \<equiv> \<o>\<^sub>2_ext p\<close> \<comment> \<open>Validity of a proposition is given by its boolean extension.\<close>

consts \<o>\<^sub>2_conj :: \<open>\<o>\<^sub>2 \<Rightarrow> \<o>\<^sub>2 \<Rightarrow> \<o>\<^sub>2\<close> (infixl \<open>\<^bold>\<and>\<close> 100)

specification (\<o>\<^sub>2_conj) \<comment> \<open>We specify our conjunction by introduction and elimination rules.\<close>
  \<o>\<^sub>2_conjE1: \<open>valid_\<o>\<^sub>2 (p \<^bold>\<and> q) \<Longrightarrow> valid_\<o>\<^sub>2 p\<close>
  \<o>\<^sub>2_conjE2: \<open>valid_\<o>\<^sub>2 (p \<^bold>\<and> q) \<Longrightarrow> valid_\<o>\<^sub>2 q\<close>
  \<o>\<^sub>2_conjI: \<open>valid_\<o>\<^sub>2 p \<Longrightarrow> valid_\<o>\<^sub>2 q \<Longrightarrow> valid_\<o>\<^sub>2 (p \<^bold>\<and> q)\<close>
  text\<open>We again need to prove the existence of a term satisfying the given specification.
       For this it is important that we axiomatized the extension function to be surjective,
       since otherwise there may not be an appropriate choice.\<close>
  by (rule exI[where x=\<open>\<lambda> p q . (inv \<o>\<^sub>2_ext) (\<o>\<^sub>2_ext p \<and> \<o>\<^sub>2_ext q)\<close>])
     (simp add: \<o>\<^sub>2_ext_surj f_inv_into_f valid_\<o>\<^sub>2_def)

text\<open>Now as a consequence of our specification, our conjunction is still commutative @{emph \<open>under validity\<close>}:\<close>

lemma \<open>valid_\<o>\<^sub>2 (p \<^bold>\<and> q) = valid_\<o>\<^sub>2 (q \<^bold>\<and> p)\<close>
text\<open>Note that the proof (found by @{command sledgehammer}) now solely relies on the properties of
     @{const \<o>\<^sub>2_conj} given in our specification.\<close>
  using \<o>\<^sub>2_conjE1 \<o>\<^sub>2_conjE2 \<o>\<^sub>2_conjI by blast

text\<open>However, commuted conjunctions are no longer identical. The model-finding tool @{command nitpick} (TODO: cite)
     can provide a counterexample by constructing a model for @{typ \<o>\<^sub>2} that has more than two members.\<close>

lemma \<open>(p \<^bold>\<and> q) = (q \<^bold>\<and> p)\<close>
  nitpick[user_axioms, expect = genuine, show_consts, atoms \<o>\<^sub>2 = p q r, format = 2]
  oops (* Note that this additionally satisfies the axioms of the imported theory AOT_PLM *)

text\<open>The model chosen by @{command nitpick}@{footnote \<open>The precise model may vary for different versions of Isabelle.\<close>}
     chooses a three-element set for type @{typ \<o>\<^sub>2}. We chose @{text p}, @{text q} and @{text r} as names for these elements.
     @{const \<o>\<^sub>2_ext} is modelled as @{text \<open>(p := True, q := False, r := False)\<close>} and
     @{const \<o>\<^sub>2_conj} as @{text \<open>((p, p) := p, (p, q) := q, (p, r) := r, (q, p) := r, (q, q) := q, (q, r) := r, (r, p) := r, (r, q) := r,
     (r, r) := r)\<close>}.

     This is indeed one of the minimal models for conjunctions that are classical under validity, but
     are not identical under commutation.
     On the other hand, @{command nitpick} can also @{emph \<open>satisfy\<close>} the same statement by providing
     a model with cardinality 2 for type @{type \<o>\<^sub>2}:
\<close>

lemma \<open>(p \<^bold>\<and> q) = (q \<^bold>\<and> p)\<close>
  nitpick[satisfy, user_axioms, expect = genuine, show_consts, atoms \<o>\<^sub>2 = p q, format = 2]
  oops (* Note that this additionally satisfies the axioms of the imported theory AOT_PLM *)

text\<open>Note that for the above it is sufficient to find a concrete choice for @{term p} and @{term q},
     s.t. the identity holds for those two propositions. However, nitpick can also produce
     (in this case the same) model satisfying the identity for all propositions,
     respectively - equivalently - refute the identity failing to hold.\<close>

lemma \<open>\<forall>p q . (p \<^bold>\<and> q) = (q \<^bold>\<and> p)\<close> \<comment> \<open>Satisfy the identity for all @{term p} and @{term q}.\<close>
  nitpick[satisfy, user_axioms, expect = genuine, show_consts, atoms \<o>\<^sub>2 = p q, format = 2]
  oops (* Note that this additionally satisfies the axioms of the imported theory AOT_PLM *)

lemma \<open>(p \<^bold>\<and> q) \<noteq> (q \<^bold>\<and> p)\<close> \<comment> \<open>Refute the non-identity for any @{term p} and @{term q}.\<close>
  nitpick[user_axioms, expect = genuine, show_consts, atoms \<o>\<^sub>2 = p q, format = 2]
  oops (* Note that this additionally satisfies the axioms of the imported theory AOT_PLM *)

(*<*)
no_notation \<o>\<^sub>2_conj (infixl \<open>\<^bold>\<and>\<close> 100)
(*>*)

text\<open>TODO: explain limitations wrt polymorphic constants; move on to type classes and locales.\<close>


section\<open>Implicit Interpretation and Assignment Function in SSEs\<close>text\<open>\label{SSE:MetaModel}\<close>

text\<open>While in the following chapters we will say that we construct models of the target
logic AOT using our embedding, we do not (and do not have to) construct full models in the classical
sense. In particular, we do not construct explicit interpretations and assignment functions.

While a deep embedding would make the full models explicit, they remain implicit
in shallow embeddings. The meta-logic (TODO: check hyphenation everywhere) Isabelle/HOL
itself involves meta-logical constants and variables. In simple models of HOL, every
type has a set as its domain and a statement is valid in HOL, if it holds for every
interpretation of the constants of a type and every assignment of its variables.

A model of the embedded logic can be constructed by lifting a model of HOL through
the defined semantics. The model-finding tool @{command nitpick} (TODO: cite?) can
aid in making these lifted models concrete.

Technically, a shallow embedding defines a substructure in the models of HOL, which
yields a model of the embedded logic under the defined validity. (TODO: check.)

TODO: Elaborate? Original notes: This section will be important and will need a lot of care. Current plan:

Propose a simplified general model of Isabelle/HOL with domains for types, interpretations
of constants and variable assignments.

Similarly, describe a model of higher-order S5 modal logic.

Show that the substructure of the embedding with the defined validity is equivalent to
validity in the model of S5 modal logic.

Thereby explain that the SSE does not need interpretation and assignment functions, if the representation
types in the embedding are chosen general enough, s.t. any domain in any S5 model is covered, and
restrictions of the interpretation and assignment functions of the HOL model to the domains of a given S5 model
cover all interpretations and assignment functions of any S5 model.

Note that the part of the S5 models that remains implicit in the embedding is solely possible worlds.

Describe the problem with defining validity in the embedding using quantification over all worlds,
which prevents reasoning relative to an arbitrary but fixed world.

Hint at the syntactic solution to this issue that avoids having to manage these arbitrary but fixed
worlds - this might be described in the next section or in a section about the embedding of AOT.
\<close>

section\<open>Reproducing the Syntax of the Target Theory\<close>text\<open>\label{SSESyntax}\<close>

text\<open>
To achieve the goal of constructing a custom theorem proving environment for a new theory by the
means of an embedding, the primary concern is achieving a faithful representation of its axioms
and deductive system and, thereby, to be able to faithfully reproduce reasoning in the embedded system.

However, for the embedding to be of practical use, it is equally important that the
resulting representation is readable and, ideally, that a person that is familiar with the
embedded theory, but has limited expertise in the particularities of the meta-logical system
in which the theory is embedded, can still use the embedding to reason in the target system
without a steep learning curve.

Isabelle's @{emph \<open>Isar\<close>} (@{emph \<open>Intelligible semi-automated reasoning\<close>}) language itself is, as the
name suggests, specifically tailored towards being readable (TODO: cite isar-ref).
Isar makes up the @{emph \<open>outer syntax\<close>} of an Isabelle theory file and consists of commands that
specify theorems and structured proofs acting on Isabelle's system of terms and types, which are
formulated in @{emph \<open>inner syntax\<close>}.
@{emph \<open>Inner syntax\<close>} is highly customizable. In the examples in the previous sections we already
made use of the ability to define new (bold) operators using @{emph \<open>mixfix\<close>} notation (TODO cite).
However, we only used the mechanism to provide symbols to be used inside the grammar tree of
Isabelle/HOL's own term structure.
In general Isabelle's inner syntax is described by a context-free priority grammar.
It consists of a set of @{emph \<open>terminal symbols\<close>}, an extensible set of
@{emph \<open>non-terminal symbols\<close>} and a set of @{emph \<open>productions\<close>} (TODO cite: isar-ref 8.4).
For the purpose of embedding the syntax of a target theory during the construction of SSEs, it
stands to reason to use the defined validity as root for the grammar subtree of the embedded
language.

Reusing the example of the simple modal logic in section~\ref{SimpleS5}, this can be done as follows:
\<close>

type_synonym \<o>\<^sub>3 = \<open>w \<Rightarrow> bool\<close>

text\<open>This time we do not use mixfix notation to directly introduce syntax for the validity context.\<close>
definition valid_\<o>\<^sub>3 :: \<open>\<o>\<^sub>3 \<Rightarrow> bool\<close> where \<open>valid_\<o>\<^sub>3 p \<equiv> \<forall> w . p w\<close>

text\<open>Instead, we introduce a @{command nonterminal} as grammar root for the syntax of the embedded language.
     The nonterminal then serves as purely syntactic type for propositions in the grammar of our
     sub-language.\<close>
nonterminal prop\<o>\<^sub>3 
text\<open>The nonterminal can be used as syntactic type in @{command syntax} definitions.\<close>
syntax valid_\<o>\<^sub>3 :: \<open>prop\<o>\<^sub>3 \<Rightarrow> bool\<close>  (\<open>\<Turnstile> _\<close> 1)

text\<open>Furthermore, we need to specify how propositions can be produced from terminals in the grammar.
We want to use simple identifiers to refer to proposition variables. To that end we introduce a
@{emph \<open>copy-production\<close>} rule (a rule that is not tied to a constant). The terminal
@{typ id_position} is used for identifiers with additional markup information (TODO: reference and cite PIDE markup).
\<close>
syntax "" :: \<open>id_position \<Rightarrow> prop\<o>\<^sub>3\<close> (\<open>_\<close>)

text\<open>Now we can already construct a simple term in our new syntax:\<close>
term \<open>\<Turnstile> p\<close>

text\<open>Since we introduce an entirely new grammar subtree that is independent of the inner syntax of HOL,
we can now reuse the same symbols for logical connectives as used in HOL (compared to having to use
bold versions in the previous section).
We first define the connectives without syntax (here the symbols refer to connectives and operators
in the language of HOL):
\<close>

definition not_\<o>\<^sub>3 :: \<open>\<o>\<^sub>3 \<Rightarrow> \<o>\<^sub>3\<close> where \<open>not_\<o>\<^sub>3 p \<equiv> \<lambda>w . \<not>p w\<close>
definition imp_\<o>\<^sub>3 :: \<open>\<o>\<^sub>3 \<Rightarrow> \<o>\<^sub>3 \<Rightarrow> \<o>\<^sub>3\<close> where \<open>imp_\<o>\<^sub>3 p q \<equiv> \<lambda>w . p w \<longrightarrow> q w\<close>
definition conj_\<o>\<^sub>3 :: \<open>\<o>\<^sub>3 \<Rightarrow> \<o>\<^sub>3 \<Rightarrow> \<o>\<^sub>3\<close> where \<open>conj_\<o>\<^sub>3 p q \<equiv> \<lambda>w . p w \<and> q w\<close>
definition disj_\<o>\<^sub>3 :: \<open>\<o>\<^sub>3 \<Rightarrow> \<o>\<^sub>3 \<Rightarrow> \<o>\<^sub>3\<close> where \<open>disj_\<o>\<^sub>3 p q \<equiv> \<lambda>w . p w \<or> q w\<close>
definition box_\<o>\<^sub>3 :: \<open>\<o>\<^sub>3 \<Rightarrow> \<o>\<^sub>3\<close> where \<open>box_\<o>\<^sub>3 p \<equiv> \<lambda>w . \<forall>v . p v\<close>
definition dia_\<o>\<^sub>3 :: \<open>\<o>\<^sub>3 \<Rightarrow> \<o>\<^sub>3\<close> where \<open>dia_\<o>\<^sub>3 p \<equiv> \<lambda>w . \<exists>v . p v\<close>

text\<open>And then define syntax for them in our grammar subtree. We can reuse the same symbols
used in the syntax of HOL, since they will apply only be used for parsing the sublanguage, i.e.
terms behind the marker @{text \<Turnstile>} introduced above.\<close>

syntax not_\<o>\<^sub>3 :: \<open>prop\<o>\<^sub>3 \<Rightarrow> prop\<o>\<^sub>3\<close> (\<open>\<not>_\<close> [40] 40)
syntax imp_\<o>\<^sub>3 :: \<open>prop\<o>\<^sub>3 \<Rightarrow> prop\<o>\<^sub>3 \<Rightarrow> prop\<o>\<^sub>3\<close> (infixl \<open>\<longrightarrow>\<close> 25)
syntax conj_\<o>\<^sub>3 :: \<open>prop\<o>\<^sub>3 \<Rightarrow> prop\<o>\<^sub>3 \<Rightarrow> prop\<o>\<^sub>3\<close> (infixl \<open>\<and>\<close> 35)
syntax disj_\<o>\<^sub>3 :: \<open>prop\<o>\<^sub>3 \<Rightarrow> prop\<o>\<^sub>3 \<Rightarrow> prop\<o>\<^sub>3\<close> (infixl \<open>\<or>\<close> 30)
syntax box_\<o>\<^sub>3 :: \<open>prop\<o>\<^sub>3 \<Rightarrow> prop\<o>\<^sub>3\<close> (\<open>\<box>_\<close> [50] 50)
syntax dia_\<o>\<^sub>3 :: \<open>prop\<o>\<^sub>3 \<Rightarrow> prop\<o>\<^sub>3\<close> (\<open>\<diamond>_\<close> [50] 50)

text\<open>Now we can start to produce complex terms in our new syntax:\<close>
term \<open>\<Turnstile> \<box>p \<longrightarrow> q \<or> \<diamond>r\<close>

text\<open>However, it is noteworthy that, since the introduced grammar subtree is independent of the
usual HOL grammar, a lot of details need to be considered. For example, without further work it is
not possible to specify the types of terms in our grammar sub-tree.
For that to work the @{text \<open>::\<close>} syntax would need to be reintroduced, which involves becoming
more familiar with Isabelle's internals like the purely syntactic constant @{text \<open>_constrain\<close>}
(TODO: cite isar-ref 8.5.4). TODO: hint at the fact that only scarce documentation is available
for any of this and this usually involves reading through the theory files of Isabelle/Pure
and/or Isabelle/HOL as reference.

As a simpler example, we also need to introduce parentheses explicitly in our grammar subtree:\<close>

syntax "" :: \<open>prop\<o>\<^sub>3 \<Rightarrow> prop\<o>\<^sub>3\<close> (\<open>'(_')\<close>)
term \<open>\<Turnstile> p \<and> (\<diamond>q \<longrightarrow> p)\<close> \<comment> \<open>Without the above this would not parse.\<close>

text\<open>It is still possible to mix the usual HOL syntax with our newly defined subgrammar
to argue about validity:\<close>

lemma \<open>(\<Turnstile> \<diamond>p \<longrightarrow> q) \<longrightarrow> (\<not>(\<Turnstile> p) \<or> (\<Turnstile> q))\<close>
  using dia_\<o>\<^sub>3_def imp_\<o>\<^sub>3_def valid_\<o>\<^sub>3_def by auto

text\<open>In the above the left-most implication is the implication of the embedded logic,
while the other logical connectives are the ones of the meta-logic (i.e. of HOL).

While the mechanisms described above are sufficient to introduce an accurate representation
of the syntax of most target theories that are compatible with the lexical syntax of
Isabelle/Pure,@{footnote \<open>Note that @{emph \<open>Abstract Object Theory\<close>} does not fall into this category
and requires additional and more complex means to arrive at a good approximation of its syntax as
described in (TODO: refer to later section.).\<close>} @{emph \<open>reasoning\<close>} in the logic of the target theory
entails additional challenges (TODO: refer to last section - in particular reasoning relative to
a fixed but arbitrary possible world and the need to mention this world syntactically).

Chapter~\ref{SSEofAOT} describes these challenges in more detail and presents the
embedding of Abstract Object Theory in Isabelle/HOL as an example of a successful,
albeit technically complex solution. TODO: adjust references.
\<close>

chapter\<open>Abstract Object Theory\<close>text\<open>\label{AOT}\<close>

text\<open>
The following sections provide a brief introduction to Abstract Object Theory. While the first
section will explain the general idea and motivation of object theory, the following sections
reproduce the language and axiom system of AOT as implemented in our embedding. In the process,
we hint at the major differences between the formulation of AOT in PLM and its incarnation in
our embedding, hinting at implementational details that will be discussed in the
next chapter.
Recall that, as mentioned in section~\ref{Structure} all definitions and theorems are
cited directly from our embedding and thereby verified by Isabelle. Exceptions to this
rule are explicitly stated and marked by vertical bars at the page margins.

We restrict ourselves to the discussion of the second-order fragment of AOT which is the target of
our embedding in Isabelle/HOL.\footnote{In the following chapters up until chapter~\ref{HigherOrderAOT}, we will
refer to the second-order fragment of AOT plainly as AOT or \emph{object theory}.}
The second-order fragment is expressive enough for the analysis of a wide variety of objects occurring in Philosophy and Mathematics,
including Basic Logical Objects like Truh Values and Extensions of Propositions (see~\ref{AOT:AOT_BasicLogicalObjects}, resp. PLM chapter~10);
Platonic Forms (see PLM chapter~11); Situations, Worlds, Times, and Stories (see~\ref{AOT:AOT_PossibleWorlds}, resp. PLM chapter~12);
Concepts (see PLM chapter 13) and Natural Numbers (see~\ref{AOT:AOT_NaturalNumbers}, resp. PLM chapter~13). TODO: rethink references.

The applications of higher-order object theory and the challenges in representing it in Isabelle/HOL are
briefly discussed in chapter~\ref{HigherOrderAOT}. To get an intuition for the level of expressiveness of
higher-order object theory, note that it can be used to analyze e.g. Zermelo-Fraenkel set-theory itself as
one of its abstract objects.
\<close>
section\<open>Overview\<close>

(*<*)
AOT_theorem abs_eq: \<open>(A!x & A!y) \<rightarrow> (x = y \<equiv> \<box>\<forall>F(x[F] \<equiv> y[F]))\<close>
proof(safe intro!: "\<rightarrow>I" "\<equiv>I")
  AOT_assume \<open>([A!]x & [A!]y)\<close> and x_eq_y: \<open>x = y\<close>
  AOT_have 1: \<open>\<box>\<forall>F(x[F] \<equiv> x[F])\<close> by (safe intro!: RN GEN "\<equiv>I" "\<rightarrow>I")
  AOT_show \<open>\<box>\<forall>F(x[F] \<equiv> y[F])\<close>
    using "rule=E"[rotated, OF x_eq_y]
    using 1 by fast
next
  AOT_assume 0: \<open>([A!]x & [A!]y)\<close>
  AOT_assume \<open>\<box>\<forall>F(x[F] \<equiv> y[F])\<close>
  AOT_hence \<open>\<forall>F(x[F] \<equiv> y[F])\<close> using "qml:2"[axiom_inst, THEN "\<rightarrow>E"] by blast
  AOT_thus \<open>x = y\<close> using "ab-obey:1"[THEN "\<rightarrow>E", OF 0] "\<rightarrow>E" by blast
qed
AOT_theorem ord_eq: \<open>(O!x & O!y) \<rightarrow> (x = y \<equiv> \<box>\<forall>F([F]x \<equiv> [F]y))\<close>
proof(safe intro!: "\<rightarrow>I" "\<equiv>I")
  AOT_assume \<open>([O!]x & [O!]y)\<close> and x_eq_y: \<open>x = y\<close>
  AOT_have 1: \<open>\<box>\<forall>F([F]x \<equiv> [F]x)\<close> by (safe intro!: RN GEN "\<equiv>I" "\<rightarrow>I")
  AOT_show \<open>\<box>\<forall>F([F]x \<equiv> [F]y)\<close>
    using "rule=E"[rotated, OF x_eq_y]
    using 1 by fast
next
  AOT_assume 0: \<open>([O!]x & [O!]y)\<close>
  AOT_assume \<open>\<box>\<forall>F([F]x \<equiv> [F]y)\<close>
  AOT_hence \<open>\<forall>F([F]x \<equiv> [F]y)\<close> using "qml:2"[axiom_inst, THEN "\<rightarrow>E"] by blast
  AOT_thus \<open>x = y\<close> using "ord=E:2"[THEN "\<rightarrow>E", OF 0] "\<rightarrow>E" by blast
qed
(*>*)

text\<open>

Abstract Object Theory (AOT or @{emph \<open>object theory\<close>}) is a meta-physical theory inspired by ideas of
Ernst Mally and formalized by Edward Zalta. 
While the theory has been evolving for several decades (see TODO: cite), its most recent canonical
presentation is given in @{emph \<open>Principia Logico-Metaphysica\<close>} (PLM), which is continuously
developed further and the most recent version of which can be accessed as online monograph (TODO cite PLM).
This thesis is written relative to the version dated October 12, 2021 (TODO cite).

TODO: the following is pretty much the section of the Review of Symbolic Logic Paper and will need
some more revision and adjustment for the use as overview here.

AOT draws two fundamental distinctions, one between @{emph \<open>abstract\<close>} and
@{emph \<open>ordinary\<close>} objects, and one between two modes of predication, namely,
classical @{emph \<open>exemplification\<close>}  @{term "\<guillemotleft>[F]x\<guillemotright>"}, or more generally, @{term "\<guillemotleft>[R]x\<^sub>1...x\<^sub>n\<guillemotright>"} and
@{emph \<open>encoding\<close>} @{term "\<guillemotleft>x[F]\<guillemotright>"}.@{footnote \<open>Note that we use additional square brackets around property terms
in exemplification or encoding formulas, except for specific constants like @{term \<open>\<guillemotleft>E!\<guillemotright>\<close>}, @{term \<open>\<guillemotleft>O!\<guillemotright>\<close>} and @{term \<open>\<guillemotleft>A!\<guillemotright>\<close>}.
This is a syntactic concession that makes the process of parsing atomic formulas in Isabelle simpler.
In AOT's usual notation these square brackets would be omitted, i.e. exemplification would be written as
$Fx_1\ldots x_n$ and encoding as $xF$.\<close>} The variables @{term x}, @{term y}, @{term z}, @{text \<open>\<dots>\<close>} range over both ordinary and
abstract objects and we can distinguish claims about these two kinds of objects by using the exemplification 
predications @{term "\<guillemotleft>[O!]x\<guillemotright>"} or @{term "\<guillemotleft>[A!]x\<guillemotright>"} to assert, respectively, that @{term x} exemplifies @{emph \<open>being ordinary\<close>} or
@{term x} exemplifies @{emph \<open>being abstract\<close>}. Whereas ordinary objects are characterized only by the
properties they exemplify, abstract objects may be characterized by
both the properties they exemplify and the properties they encode. But
only the latter play a role in their identity conditions:
@{thm abs_eq[of _ "x::\<kappa> AOT_var" "y::\<kappa> AOT_var", print_as_theorem]}, i.e,
abstract objects are  identical if and only if they necessarily
encode the same properties. The identity for ordinary objects on the other hand is
classical: @{thm ord_eq[of _ "x::\<kappa> AOT_var" "y::\<kappa> AOT_var", print_as_theorem]}, i.e.,
ordinary objects @{term x} and @{term y} are identical if and only if they necessarily exemplify the same properties.
It is axiomatic that ordinary objects necessarily fail to encode properties (@{thm nocoder[axiom_inst, of _ x, print_as_theorem]}),
and so only abstract objects can be the subject of true encoding predications.
For example, whereas Pinkerton (a real American detective) exemplifies being a detective and
all his other properties (and doesn't encode any properties), Sherlock Holmes encodes
@{emph \<open>being a detective\<close>} (and all the other properties attributed to him in the novels),
but doesn't exemplify @{emph \<open>being a detective\<close>}. Holmes, on the other hand, intuitively exemplifies
being a fictional character (but doesn't encode this property) and exemplifies any property necessarily
implied by @{emph \<open>being abstract\<close>} (e.g., he exemplifies @{emph \<open>not having a mass\<close>},
@{emph \<open>not having a shape\<close>}, etc.).@{footnote \<open>He encodes @{emph \<open>having a mass\<close>}, @{emph \<open>having a shape\<close>},
etc., since these  are properties attributed to him, at least implicitly, in the story.
As an abstract object, however, he does @{emph \<open>not\<close>} exemplify these properties,
and so exemplifies their negations.\<close>}

The key axiom of AOT is the comprehension principle for abstract
objects. It asserts, for every expressible condition on properties (i.e.,
for every expressible set of properties), that there exists
an abstract object that encodes exactly the properties that satisfy the
condition; formally: @{thm "A-objects"[axiom_inst, of _ \<phi>, print_as_theorem]}

Here @{text "\<phi>{F}"} is the notation we use in the embedding to signify that @{term \<phi>} may contain
a free occurrence of the bound variable @{term F} (@{term \<phi>} may not contain a free occurrence of @{term x},
unless we had explicitly added @{term x} in curly braces as well).\footnote{PLM, on the
other hand, uses the opposite convention: any @{emph \<open>metavariable\<close>} like @{term \<phi>} may contain free
occurrences of arbitrary variables (even those that are bound at the occurrence of @{term \<phi>}) unless explicitly excluded,
i.e. instead of @{text "\<phi>{F}"}, PLM simply states @{term \<open>\<phi>\<close>} and uses natural language to add the proviso that @{term x} may
@{emph \<open>not\<close>} occur free in @{term \<phi>}. See~\ref{substitutability} for a more detailed discussion.} Taken together,
the comprehension principle and the identity conditions
of abstract objects imply that abstract objects can be modeled as elements of the power set of properties:
every abstract object uniquely corresponds to a specific set of properties.

Given this basic theory of abstract objects, AOT can elegantly define
a wide variety of objects that have been postulated in philosophy or
presupposed in the sciences, including Leibnizian concepts, Platonic
forms, possible worlds, natural numbers, logically-defined sets, etc.

Another crucial aspect of the theory is its hyperintensionality:
Relation identity is defined in terms of encoding rather than
in terms of exemplification. Two properties @{term F} and @{term G} are stipulated to be identical if they are
necessarily @{emph \<open>encoded\<close>} by the same abstract objects (@{thm "identity:2"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I", OF "cqt:2[const_var]"[axiom_inst], OF "cqt:2[const_var]"[axiom_inst], of _ F G, print_as_theorem]}).\footnote{Traditionally,
one might expect properties to be identical, if they are necessarily @{emph \<open>exemplified\<close>} by the same objects instead.}
The theory does not impose any restrictions on the properties encoded by a particular abstract
object. For example, the fact that an abstract object encodes the
property @{term \<open>\<guillemotleft>[\<lambda>x [F]x & [G]x]\<guillemotright>\<close>} does not imply that
it also encodes either the property @{term F}, or @{term G} or even
@{term \<open>\<guillemotleft>[\<lambda>x [G]x & [F]x]\<guillemotright>\<close>} (which, although extensionally equivalent to 
@{term \<open>\<guillemotleft>[\<lambda>x [F]x & [G]x]\<guillemotright>\<close>}, is a distinct intensional entity).

Therefore, without additional axioms, pairs of materially equivalent
properties (in the exemplification sense), and even necessarily equivalent properties, are not forced
to be identical. This is a key aspect of the theory that makes it
possible to represent the contents of human thought much more
accurately than classical exemplification logic would allow.  For instance, the
properties @{emph \<open>being a creature with a heart\<close>} and @{emph \<open>being a creature with a kidney\<close>}
may be regarded as distinct properties despite the fact that they are extensionally equivalent.
And @{emph \<open>being a barber who shaves all and only those persons who don't shave themselves\<close>}
and @{emph \<open>being a set of all those sets that aren't members of
  themselves\<close>} may be regarded as distinct properties, although they
are necessarily equivalent (both necessarily fail to be exemplified).

In the following sections, we provide a brief overview of the language, the axiom system and
the deductive system of PLM. For a full account and detailed discussion refer to (TODO: cite PLM).
\<close>

section\<open>The Language\<close>text\<open>\label{AOTLanguage}\<close>

text\<open>

A precise description of AOT's language can be found in (TODO: cite PLM).
In this section we provide a simplified informal description while explaining some of the deviations
from AOT's conventions we use in our embedding.

The language distinguishes between constants, variables and terms at each type. The types of
the second-order fragment consist of a type of individuals and, for each @{text \<open>n \<ge> 0\<close>}, of a type
of @{text n}-place relations, i.e. relations among @{text n} individuals.
Formulas are considered as @{text 0}-place relation terms. PLM uses the following conventions for
referring to the primitive language elements in each type:

  \<^item> Primitive individual constants: @{text \<open>a\<^sub>1, a\<^sub>2, \<dots>\<close>}
  \<^item> Individual variables: @{text \<open>x\<^sub>1, x\<^sub>2, \<dots>\<close>}
  \<^item> Primitive @{text n}-place relation constants: @{text \<open>P\<^sup>n\<^sub>1, P\<^sup>n\<^sub>2, \<dots>\<close>}
  \<^item> @{text n}-place relation variables: @{text \<open>F\<^sup>n\<^sub>1, F\<^sup>n\<^sub>2, \<dots>\<close>}
  \<^item> A distinguished 1-place relation constant for @{emph \<open>being concrete\<close>}: @{term \<open>\<guillemotleft>E!\<guillemotright>\<close>}

Additionally, PLM uses Greek letters for @{emph \<open>meta-variables\<close>}, i.e. schematic meta-logical variables,
that may range over all variable names or all terms at a given type. By convention, it associates specific kinds of
meta-variables with Greek letters (with additional numbered subscripts as needed) as follows:


  \<^item> Meta-variables ranging over individual variables: @{text \<nu>}
  \<^item> Meta-variables ranging over individual terms: @{text \<kappa>}
  \<^item> Meta-variables ranging over @{text n}-place relation terms: @{text \<open>\<Pi>\<^sup>n\<close>}
  \<^item> Meta-variables ranging over formulas (i.e. zero-place relation terms): @{text \<open>\<phi>, \<psi>, \<dots>\<close>}
  \<^item> Meta-variables ranging over variables of any type: @{text \<open>\<alpha>, \<beta>, \<dots>\<close>}
  \<^item> Meta-variables ranging over terms of any type: @{text \<open>\<tau>, \<sigma>, \<dots>\<close>}


AOT's strict distinction between constants, variables and meta-variables does not have to be reproduced
in all detail for our embedding for the following reasons:


  \<^item> The embedding collapses all alphabetic variants. This is discussed in more detail in section~\ref{alphabetic-variants}.
  \<^item> The embedding implicitly generalizes free variables in theorems to @{emph \<open>schematic variables\<close>}. This is discussed in more detail
    in section~\ref{free-variables-schematic}.
  \<^item> The distinction between constants and variables is done at the meta-logical level of Isabelle/HOL. TODO: explain further.


Furthermore, AOT introduces the following primitive formula- and term-forming operators:

  \<^item> @{term \<open>\<guillemotleft>\<not>\<phi>\<guillemotright>\<close>}, the @{emph \<open>negation\<close>} operator
  \<^item> @{term \<open>\<guillemotleft>\<box>\<phi>\<guillemotright>\<close>}, the @{emph \<open>necessity\<close>} operator
  \<^item> @{term \<open>\<guillemotleft>\<^bold>\<A>\<phi>\<guillemotright>\<close>}, the @{emph \<open>actuality\<close>} operator
  \<^item> @{term \<open>\<guillemotleft>\<phi> \<rightarrow> \<psi>\<guillemotright>\<close>}, the @{emph \<open>conditional\<close>} operator
  \<^item> @{term \<open>AOT_TERM[(\<forall>\<alpha> \<phi>{\<alpha>})]\<close>}, the @{emph \<open>universal quantifier\<close>}@{footnote \<open>As mentioned in the previous section,
  PLM, by default, allows any free variables to occur instances of a schematic meta-variable, unless specified otherwise.
  For technical reasons, we choose the opposite convention, i.e. while a schematic meta-variable may still contain
  any occurrence of variables that would remain @{emph \<open>free\<close>} (and which is not already named in the current context),
  any @{emph \<open>bound\<close>} variables (or variables that already have a name in the current context) that may
  occur in an instance of the schematic meta-variable have to be explicitly listed in curly brackets. See~\ref{substitutability} for
  a more detailed discussion.\<close>}
  \<^item> @{term \<open>AOT_TERM[\<^bold>\<iota>x \<phi>{x}]\<close>}, the @{emph \<open>definite description\<close>} operator
  \<^item> @{term \<open>AOT_TERM[[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]]\<close>}, the @{emph \<open>relation abstraction\<close>}- or @{text \<open>\<lambda>\<close>}-operator@{footnote \<open>Note
that this includes the zero-place case @{term \<open>AOT_TERM[[\<lambda> \<phi>]]\<close>}, read as @{emph \<open>that @{term \<phi>}\<close>}\<close>}

AOT uses two kinds of atomic formulas, @{emph \<open>exemplification\<close>} formulas and @{emph \<open>encoding\<close>} formulas.
In PLM exemplification formulas are written as @{text \<open>\<Pi>\<kappa>\<^sub>1\<dots>\<kappa>\<^sub>n\<close>}, whereas encoding formulas are
written as @{text \<open>\<kappa>\<^sub>1\<dots>\<kappa>\<^sub>n\<Pi>\<close>}. In our embedding, we use additional square brackets for easier parsing, i.e. we use:

  \<^item> @{term \<open>AOT_TERM[([\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n)]\<close>} for atomic exemplification formulas
  \<^item> @{term \<open>AOT_TERM[(\<kappa>\<^sub>1...\<kappa>\<^sub>n[\<Pi>])]\<close>} for atomic encoding formulas


Furthermore, PLM allows for extending above language using two kinds of definitions: definitions
by identity and definitions by equivalence. While the inferential role of these definitions will be
discussed in more detail in (TODO: cite), for now we rely on an intuitive understanding of their meaning.
PLM @{emph \<open>defines\<close>} multiple concepts that are commonly taken as primitive, such as logical existence
and identity. These basic definitions can be found in (TODO: cite PLM section) and are
implemented in our embedding in section~\ref{AOT:AOT_Definitions}.
In particular, PLM defines the following: (TODO: cite PLM section)

Derived connectives and quantifiers (see~\nameref{AOT:conventions:1}):\footnote{The diamond operator @{text \<open>\<diamond>\<phi>\<close>} can be
read as @{emph \<open>possibly @{text \<phi>}\<close>}.}

\begin{quote}
@{thm[display] "conventions:1"[of \<phi> \<psi>]
               "conventions:2"[of \<phi> \<psi>]
               "conventions:3"[of \<phi> \<psi>]
               "conventions:4"[of \<phi>]
               "conventions:5"[of \<phi>]}
\end{quote}

Logical existence, i.e. the conditions under which a term @{emph \<open>denotes\<close>} an object (see~\nameref{AOT:existence:1}):

\begin{quote}
@{thm[display] "existence:1"[of \<kappa>]
               "existence:2"[of \<Pi>]
               "existence:3"[of \<phi>]}
\end{quote}

Being @{emph \<open>ordinary\<close>} and being @{emph \<open>abstract\<close>} (see~\nameref{AOT:oa:1}):

\begin{quote}
@{thm[display] "oa:1" "oa:2"}
\end{quote}

Identity of individuals (see~\nameref{AOT:identity:1}):
\begin{quote}
@{thm[display] "identity:1"[of \<kappa> \<kappa>']}
\end{quote}

Identity of properties, i.e. 1-place relations (see~\nameref{AOT:identity:2}):

\begin{quote}
@{thm[display] "identity:2"[of \<Pi> \<Pi>']}
\end{quote}

Identity of @{text \<open>n\<close>}-place relations (@{text \<open>n \<ge> 2\<close>}):@{footnote \<open>The idea here is that two
@{text n}-place relations are identical, if they denote and all their projections to @{text \<open>n - 1\<close>} objects
are identical. In the embedding it is tricky to reproduce the ellipse notation used for this definition
directly, therefore the statement here is @{emph \<open>not\<close>} cited from the embedding. The implementation
of this definition in the embedding can be found in~\nameref{AOT:identity:3} and is discussed
in more detail in section TODO: cite.\<close>}

\begin{quote}
  \Squ{@{text \<open>\<Pi> = \<Pi>' \<equiv>\<^sub>d\<^sub>f \<Pi>\<down> & \<Pi>'\<down> & \<forall>y\<^sub>1\<dots>\<forall>y\<^bsub>n-1\<^esub> ([\<lambda>x [\<Pi>]xy\<^sub>1\<dots>y\<^bsub>n-1\<^esub>] = [\<lambda>x [\<Pi>']xy\<^sub>1\<dots>y\<^bsub>n-1\<^esub>] &
[\<lambda>x [\<Pi>]y\<^sub>1xy\<^sub>2\<dots>y\<^bsub>n-1\<^esub>] = [\<lambda>x [\<Pi>']y\<^sub>1xy\<^sub>2\<dots>y\<^bsub>n-1\<^esub>] & \<dots> &
[\<lambda>x [\<Pi>]y\<^sub>1\<dots>y\<^bsub>n-1\<^esub>x] = [\<lambda>x [\<Pi>']y\<^sub>1\<dots>y\<^bsub>n-1\<^esub>x]
)\<close>}}
\end{quote}

Based on the described language and definitions we can state AOT's axiom system in the following section.
\<close>

section\<open>The Axiom System\<close>text\<open>\label{AxiomSystem}\<close>

text\<open>
In the following, we reproduce the full axiom system of the latest formulation of AOT, while
commenting on several aspects that are specific to AOT. Unless explicitly noted otherwise, we
will directly cite the axioms from our implementation while explaining notational and conceptual
differences to the original axiom system of AOT. The original axiom system is stated in (TODO: cite PLM)
with detailed explanations. The implementation in our embedding can be found in~\ref{AOT:AOT_Axioms}.
Throughout the section we will refer to the statement of the axioms in~\ref{AOT:AOT_Axioms},
which will in turn refer to the item numbers of the axioms in PLM.

The first set of axioms build up a Hilbert-style deductive system for negation and implications
following Mendelsson's axiom system
(TODO: cite Elliott Mendelson, Introduction to Mathematical Logic, Van Nostrand, New York, 1979, p. 31.)
(see~\nameref{AOT:pl:1}):

\begin{quote}
@{thm[display] "pl:1"[axiom_inst, print_as_theorem, of \<phi> \<psi>]
      "pl:2"[axiom_inst, print_as_theorem, of \<phi> \<psi> \<chi>]
      "pl:3"[axiom_inst, print_as_theorem, of \<phi> \<psi>]}
\end{quote}

The next set of axioms constructs a quantifier logic for a free logic with non-denoting
terms (see~\nameref{AOT:cqt:1},~\nameref{AOT:cqt:3}).
Formulas of the form @{term \<open>\<guillemotleft>\<tau>\<down>\<guillemotright>\<close>} can be read as @{emph \<open>the term @{term \<open>\<tau>\<close>} denotes\<close>} and refer
to the notion of logical existence that was @{emph \<open>defined\<close>} in the previous section.\footnote{See
section~\ref{substitutability} for a discussion of the free variable notation using curly brackets.}

\begin{quote}
@{thm[display] "cqt:1"[axiom_inst, of _ \<phi> \<tau>, print_as_theorem]
      "cqt:3"[axiom_inst, of _ \<phi> \<psi>, print_as_theorem]
      "cqt:4"[axiom_inst, of _ \<phi>, print_as_theorem]
      "cqt:5:a"[axiom_inst, of _ \<Pi> \<kappa>\<^sub>1\<kappa>\<^sub>n, print_as_theorem]
      "cqt:5:b"[axiom_inst, of _ \<kappa>\<^sub>1\<kappa>\<^sub>n \<Pi>, print_as_theorem]}
\end{quote}

The last two axioms in the list above are noteworthy: they establish that if any
atomic exemplification or encoding formula (which are specific to AOT) is true,
then its primary terms are significant.

Additionally, PLM establishes a base set of denoting terms with the following axiom:

\begin{quote}
  \Squ{@{term \<open>\<guillemotleft>\<tau>\<down>\<guillemotright>\<close>}, provided @{term \<tau>} is a primitive constant, a variable, or a @{text \<open>\<lambda>\<close>}-expression
  in which the initial @{text \<open>\<lambda>\<close>} does not bind any variable in any encoding formula subterm.}
\end{quote}

Reproducing the natural language condition on @{term \<tau>} in the embedding is non-trivial (see~\nameref{AOT:cqt:2[const_var]},
which uses the auxiliary predicate @{text \<open>INSTANCE_OF_CQT_2\<close>} defined in~\nameref{AOT:AOT_semantics.AOT_instance_of_cqt_2}); we discuss
the implementation of this axiom in detail in section~\ref{cqt:2-impl}.

The next axiom states that identical objects can be substituted in formulas. Note that the used identity
is not primitive, but was @{emph \<open>defined\<close>} in the last section (see~\nameref{AOT:l-identity}).@{footnote \<open>PLM formulates
the axiom as: @{term \<open>\<guillemotleft>\<alpha> = \<beta> \<rightarrow> (\<phi> \<rightarrow> \<phi>')\<guillemotright>\<close>}, whenever @{text \<beta>} is @{emph \<open>substitutable for\<close>} @{text \<alpha>} in @{text \<phi>}, and
@{text \<open>\<phi>'\<close>} is the result of replacing zero or more free occurrences of @{text \<alpha>} in @{text \<phi>} with occurrences of @{text \<beta>}.
This precisely matches the formulation given above in our explicit free variable notation. This is discussed in more detail
in section~\ref{substitutability}.\<close>} 

\begin{quote}
@{thm[display] "l-identity"[axiom_inst, of _ \<alpha> \<beta> \<phi>, print_as_theorem]}
\end{quote}

The following axiom is the single @{emph \<open>modally fragile axiom\<close>} of the system (see~\nameref{AOT:logic-actual}). All other axioms
are considered @{emph \<open>modally strict\<close>}. This is significed by the turnstile operator
@{text \<open>\<^bold>\<turnstile>\<close>}, while all other axioms are modally strict (for simplicity, we assume the
corresponding turnstile operator @{text \<open>\<^bold>\<turnstile>\<^sub>\<box>\<close>} by default and refrain from mentioning it
explicitly).
The distinction is discussed further in section~\ref{ModallyStrictFragile}.

\begin{quote}
@{thm[display] "logic-actual"[act_axiom_inst, of \<phi>]}
\end{quote}

Apart from the above modally-fragile principle, the logic of actuality is governed by the following
modally-strict axioms (see~\nameref{AOT:logic-actual-nec:1}):

\begin{quote}
@{thm[display] "logic-actual-nec:1"[axiom_inst, of _ \<phi>, print_as_theorem]
               "logic-actual-nec:2"[axiom_inst, of _ \<phi> \<psi>, print_as_theorem]
               "logic-actual-nec:3"[axiom_inst, of _ \<phi>, print_as_theorem]
               "logic-actual-nec:4"[axiom_inst, of _ \<phi>, print_as_theorem]}
\end{quote}

TODO: say something about this together with the axiom relating actuality to necessity below is
a "standard" actuality operator plus citation.

The logic of necessity and possibility is axiomatized using the classical K, T and 5 axioms of a
propositional S5 modal logic (see~\nameref{AOT:qml:1}):

\begin{quote}
@{thm[display] "qml:1"[axiom_inst, of _ \<phi> \<psi>, print_as_theorem]
               "qml:2"[axiom_inst, of _ \<phi>, print_as_theorem]
               "qml:3"[axiom_inst, of _ \<phi>, print_as_theorem]}
\end{quote}

Additionally, PLM states the following axiom that requires that there might have been a concrete object
that is not @{emph \<open>actually\<close>} concrete, thereby committing the system against modal collapse
(TODO: cite some more discussion) (see~\nameref{AOT:qml:4}).
\begin{quote}
@{thm[display] "qml:4"[axiom_inst, print_as_theorem]}
\end{quote}

The classical S5 modal logic is connected to the logic of actuality by the following two axioms (see~\nameref{AOT:qml-act:1}):

\begin{quote}
@{thm "qml-act:1"[axiom_inst, of _ \<phi>, print_as_theorem]
      "qml-act:2"[axiom_inst, of _ \<phi>, print_as_theorem]}
\end{quote}

Definite descriptions in AOT are governed by the following axiom (which will allow for deriving
a version of Russell's analysis of descriptions; TODO: expand, cite?) (see~\nameref{AOT:descriptions}):

\begin{quote}
@{thm descriptions[axiom_inst, of _ x \<phi>, print_as_theorem]}
\end{quote}


A consistent axiomatization of complex relation terms in AOT requires some care. While @{text \<open>\<lambda>\<close>}-expressions
follow the classical principles of @{text \<alpha>}-, @{text \<beta>}- and @{text \<eta>}-conversion, they have to be
suitably restricted to denoting terms, since not all @{text \<open>\<lambda>\<close>}-expressions are guaranteed to denote.
Also note that the embedding generally collapses alphabetic variants (see~\ref{alphabetic-variants}),
so while @{text \<alpha>}-conversion can be stated, it effectively reduces to the statement that denoting
@{text \<lambda>}-expressions are self-identical (TODO: cite discussion) (see~\nameref{AOT:lambda-predicates:1}).

\begin{quote}
@{thm[display] "lambda-predicates:1"[axiom_inst, of _ \<phi>, print_as_theorem]
               "lambda-predicates:2"[axiom_inst, of _ \<phi> x\<^sub>1x\<^sub>n, print_as_theorem]
               "lambda-predicates:3"[axiom_inst, of _ F, print_as_theorem]}
\end{quote}
Note that the last of the above axioms, @{text \<eta>}-conversion, also has the @{text 0}-place case
@{thm "lambda-predicates:3[zero]"[axiom_inst, of _ p, print_as_theorem]}.\footnote{While identical by axiom,
the syntactically distinct terms @{text \<open>p\<close>} and @{text \<open>[\<lambda> p]\<close>} in AOT are meant to capture
the natural-language distinction between the statement @{text p} itself and the statement
@{emph \<open>that @{text p} is true\<close>}. TODO: rethink; mention subtlety of terms instead of variables.}

The following axiom is specific to AOT and, together with generally extending AOT's free logic
to relation terms and the refinement of base cases of denoting terms, a main aspect in the evolution
of PLM that was originally triggered by its analysis using our embedding (TODO: cite MSc thesis).
It states that whenever a @{text \<lambda>}-expression denotes, any @{text \<lambda>}-expression with a matrix
that is necessarily equivalent on all abstracted variables will denote as well (see~\nameref{AOT:safe-ext}):

\begin{quote}
@{thm[display] "safe-ext"[axiom_inst, of _ \<phi> \<psi>, print_as_theorem]}
\end{quote}

This axiom, together with AOT's move to a general free logic for complex terms, is discussed in
more detail in section TODO: cite.

The remaining axioms govern AOT's second mode of predication, @{emph \<open>encoding\<close>}.

The first of these axioms reduces @{term n}-ary encoding to unary encoding of projections as follows:@{footnote
\<open>Note that similarly to the definition of @{term n}-ary relation identity, the formulation using
ellipses is non-trivial to reproduce in the embedding. Therefore we again do @{emph \<open>not\<close>} cite the axiom
directly from the embedding, but state it as given in PLM modulo our notational conventions.
The precise implementation in the embedding can be found in~\nameref{AOT:nary-encoding[2]} and is discussed in
more detail in TODO: cite.\<close>}


\begin{quote}
  \Squ{@{text \<open>x\<^sub>1\<dots>x\<^sub>n[F] \<equiv> x\<^sub>1[\<lambda>y [F]yx\<^sub>2\<dots>x\<^sub>n] & x\<^sub>2[\<lambda>y [F]x\<^sub>1yx\<^sub>3\<dots>x\<^sub>n] & \<dots> & x\<^sub>n[\<lambda>y [F]x\<^sub>1\<dots>x\<^bsub>n-1\<^esub>y]\<close>}}
\end{quote}

The second axiom governing encoding states that encoding is @{emph \<open>modally rigid\<close>} (see~\nameref{AOT:encoding}):

\begin{quote}
  @{thm[display] encoding[axiom_inst, of _ x F, print_as_theorem]}
\end{quote}

Furthermore, as mentioned in the introduction of this chapter, encoding is reserved for @{emph \<open>abstract\<close>} objects or
in other words: ordinary objects do not encode properties (see~\nameref{AOT:nocoder}):

\begin{quote}
  @{thm nocoder[axiom_inst, of _ x, print_as_theorem]}
\end{quote}

The last axiom is the core axiom of AOT, the @{emph \<open>Comprehension Principle for Abstract Objects\<close>}.
For any expressible condition on properties, there exists an abstract object that encodes exactly those
properties that satisfy the condition (see~\nameref{AOT:A-objects}):

\begin{quote}
@{thm "A-objects"[axiom_inst, of _ \<phi>, print_as_theorem]}
\end{quote}

All above axioms are to be understood as axiom @{emph \<open>schemata\<close>}, i.e. their universal closures
are axioms as well. Furthermore, for all axioms except the modally-fragile axiom of actuality,
their modal closures are taken as axioms as well.
\<close>




section\<open>The Deductive System\<close>text\<open>\label{DeductiveSystem}\<close>

(*<*)
definition AOT_print_as_rule :: \<open>prop \<Rightarrow> prop\<close> where \<open>AOT_print_as_rule \<equiv> \<lambda> x . PROP x\<close>

lemma AOT_print_as_ruleI: assumes \<open>PROP a\<close> shows \<open>PROP AOT_print_as_rule (PROP a)\<close>
  using assms unfolding AOT_print_as_rule_def by simp

attribute_setup print_as_rule =
  \<open>Scan.succeed (Thm.rule_attribute [] (K (fn thm => thm COMP @{thm AOT_print_as_ruleI})))\<close>
  "Print as rule."

syntax (latex output)
  "_AOT_asms" :: "prop \<Rightarrow> prop \<Rightarrow> prop" ("_ /\<^latex>\<open>{\\normalsize \\,\<close>and\<^latex>\<open>\\,}\<close>/ _") (* ("_ and _") *)
  "_AOT_rule" :: "prop \<Rightarrow> prop \<Rightarrow> prop" ("\<^latex>\<open>{\\normalsize{}\<close>If\<^latex>\<open>\\,}\<close> _ /\<^latex>\<open>{\\normalsize \\,\<close>then\<^latex>\<open>\\,}\<close>/ _.") (*("If _ then _")*)
  "_AOT_for_arbitrary" :: \<open>id_position \<Rightarrow> AOT_prop \<Rightarrow> AOT_prop\<close> ("\<^latex>\<open>{\\normalsize{}\<close>for arbitrary\<^latex>\<open>\\,}\<close> _\<^latex>\<open>{\\normalsize{}\<close>:\<^latex>\<open>\\,}\<close>/ _" [1000,1] 1)

print_translation\<open>[
(\<^const_syntax>\<open>AOT_print_as_rule\<close>, fn ctxt => fn [x] => (
let
fun deconstruct x = (case Term.strip_comb x of (Const (\<^const_syntax>\<open>Pure.imp\<close>, _), [prem,concl]) => apfst (fn x => prem::x) (deconstruct concl)
                     | _ => ([],x))
val (prems,concl) = deconstruct x
val (v,concl) = case concl of (Const (\<^const_syntax>\<open>HOL.Trueprop\<close>, _) $ (Const (\<^const_syntax>\<open>AOT_model_valid_in\<close>, _ ) $ v $ c)) => (v,Const (\<^syntax_const>\<open>_AOT_process_frees\<close>, dummyT) $ c)
                            | _ => (Const (\<^const_syntax>\<open>undefined\<close>, dummyT),concl)
fun mapPremise (x as Const (\<^const_syntax>\<open>HOL.Trueprop\<close>, _) $ (Const (\<^const_syntax>\<open>AOT_model_valid_in\<close>, _ ) $ v' $ c)) = (if v = v' then Const (\<^syntax_const>\<open>_AOT_process_frees\<close>, dummyT) $ c else x)
  | mapPremise (x as Const (\<^const_syntax>\<open>Pure.all\<close>, _) $ (abs as Abs (name, t, xs))) = if t = @{typ w} then x else Const (\<^syntax_const>\<open>_AOT_for_arbitrary\<close>, dummyT) $ (Const ("_bound", dummyT) $ Free (name, dummyT)) $ (mapPremise (Term.betapply (abs, Const ("_bound", dummyT) $ Free (name, dummyT))))
  | mapPremise (x as Const (\<^const_syntax>\<open>Pure.imp\<close>, _) $ p $ q) = Const (\<^syntax_const>\<open>_AOT_derivable\<close>, dummyT) $ mapPremise p $ mapPremise q
  | mapPremise (x as Const (\<^const_syntax>\<open>HOL.Trueprop\<close>, _) $ (Const (\<^const_syntax>\<open>AOT_model_equiv_def\<close>, _ ) $ lhs $ rhs)) = (Const (\<^syntax_const>\<open>_AOT_equiv_def\<close>, dummyT) $ lhs $ rhs)
  | mapPremise (x as Const (\<^const_syntax>\<open>HOL.Trueprop\<close>, _) $ (Const (\<^const_syntax>\<open>AOT_model_id_def\<close>, _ ) $ lhs $ rhs)) = (Const (\<^const_syntax>\<open>AOT_model_id_def\<close>, dummyT) $ lhs $ rhs)
val prems = map mapPremise prems
val prem = (hd prems)
val prem = fold (fn c => fn p => (Const (\<^syntax_const>\<open>_AOT_asms\<close>, dummyT) $ p $ c)) (tl prems) prem
val der = case v of Const ("_var", _) $ _ => \<^syntax_const>\<open>_AOT_rule\<close> | _ => \<^syntax_const>\<open>_AOT_rule\<close>
in
Const (der, dummyT) $ prem $ concl
end))]\<close>
(*>*)
text\<open>

While an implementation of the complete deductive system of PLM chapter~9 (TODO: cite properly) can be
found in~\ref{AOT:AOT_PLM}, a full discussion of the entire system would go beyond the scope of this thesis.
However, we will discuss some aspects (TODO: that are required for understanding the rest of the thesis?) in detail.
\<close>

subsection\<open>Primitive and Derived Meta-Rules\<close>text\<open>\label{MetaRules}\<close>

text\<open>
Since the axioms of AOT are to be understood as axiom schemata, i.e. their statement
includes the statement of adequate closures, a single primitive rule of inference suffices for
the deductive system of PLM, i.e. Modus Ponens (see~\nameref{AOT:modus-ponens}):@{footnote \<open>Note that we are still citing rules directly from the embedding
using a special printing mode for meta-rules.\<close>}
\begin{quote}
@{thm[display] "modus-ponens"[print_as_rule]}
\end{quote}

While PLM can refer to structural induction on the complexity of a formula to derive further
meta-rules, by the nature of a Shallow Semantic Embedding, the precise term structure is not
preserved, but instead terms are directly represented as objects in their semantic domain. For that reason,
in our embedding we derive the rules in question by referring to the semantic properties of the
embedding. In particular, we derive the following rules semantically:

The deduction theorem (see~\nameref{AOT:deduction-theorem}):
\begin{quote}
@{thm[display] "deduction-theorem"[print_as_rule]}
\end{quote}

The rule of necessitation RN (see~\nameref{AOT:RN}):\footnote{TODO: refer to more detailed discussion about the converse of RN.}
\begin{quote}
@{thm[display] "RN"[print_as_rule]}
\end{quote}

The rule RN can only be applied to a formula @{term \<phi>}, if @{term \<phi>} has a @{emph \<open>modally-strict proof\<close>},
as signified by @{text \<open>\<^bold>\<turnstile>\<^sub>\<box>\<close>}. We discuss this in more detail in section~\ref{ModallyStrictFragile}.

The rule of generalization GEN (see~\nameref{AOT:rule-gen}):
\begin{quote}
@{thm[display] "GEN"[print_as_rule]}
\end{quote}
\<close>

subsection\<open>The Inferential Role of Definitions\<close>

text\<open>
PLM uses two kinds of definitions: definitions-by-equivalence @{text \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>\<close>} and definitions-by-identity
@{text \<open>\<tau> =\<^sub>d\<^sub>f \<sigma>\<close>}.
While, intuitively, definitions by equivalence imply definiens and definiendum to be equivalent (@{text \<open>\<equiv>\<close>})
and definitions by identity imply them to be identical (@{text \<open>=\<close>}), further care is required when stating their
precise inferential roles.
\<close>

subsubsection\<open>Definitions by Equivalence\<close>

text\<open>Since equivalence (@{text \<open>\<equiv>\<close>}) is itself @{emph \<open>defined\<close>} using a definition-by-equivalence (as mentioned in section~\ref{AOTLanguage}),
equivalence itself cannot be used to specify the inferential role of definitions-by-equivalence. Instead the inferential role
has to be formulated relative in terms of primitives of the language, i.e. in terms of implications.

To that end, PLM formulates a @{emph \<open>Rule of Definition by Equivalence\<close>} that we reproduce in
the embedding as follows (see~\nameref{AOT:df-rules-formulas[1]}):

\begin{quote}
@{thm[display] "df-rules-formulas[1]"[axiom_inst, of \<phi> \<psi>, print_as_rule]
               "df-rules-formulas[2]"[axiom_inst, of \<phi> \<psi>, print_as_rule]}
\end{quote}

In other words (and as formulated in PLM TODO: cite), a definition-by-equivalence of the form @{text \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>\<close>} introduces the closures of
@{text \<open>\<phi> \<rightarrow> \<psi>\<close>} and @{text \<open>\<psi> \<rightarrow> \<phi>\<close>} as necessary axioms.

The derived principle that a definition-by-equivalence implies definiens and definiendum to
in fact be equivalent becomes a theorem (see~\nameref{AOT:rule-eq-df:1}):

\begin{quote}
@{thm[display] "\<equiv>Df"[of \<phi> \<psi>, print_as_rule]}
\end{quote}

Another noteworthy subtlety in PLM's use of definitions by equivalence is its convention that such definitions
are stated using object-level variables, even though those variables act as meta-variables.
For instance, following PLM's conventions, the definition of identity for properties (TODO cite) can be stated as:

\begin{quote}
@{thm[display] "identity:2"[of F G]}
\end{quote}

However, replacing @{term F} and @{term G} by any property term constitutes a valid instance of this
definition. In order to avoid confusion for a reader that is not familiar with this convention, we
choose to either state the definitions using meta-variables instead, or state a derived equivalence
as theorem using object-variables in its place (which allows forgoing clauses about the significance
of the involved terms in the definiendum). I.e. in the upcoming chapters, instead of stating the full
definition-by-equivalence for e.g. property identity, we may illustrate the definition using a simpler
theorem using regular object-level variables while dropping significance constraints:

\begin{quote}
@{thm[display] "identity:2"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I", OF "cqt:2[const_var]"[axiom_inst], OF "cqt:2[const_var]"[axiom_inst], of _ F G, print_as_theorem]}
\end{quote}

This simplification is justified, since most definitions of PLM are formulated in such a way
that the definiens implies the significance of all free terms in the definiendum, so unless noted otherwise
it can be assumed that the definiendum of a definition-by-equivalence is false for non-denoting terms.
A notable example of an exception to this rule is the definition of non-identity: for two terms to be
non-identical neither has to be significant, respectively non-significant terms are non-identical
to any other terms.
\<close>

subsubsection\<open>Definitions by Identity\<close>

text\<open>
A subtlety in definitions by identity is their behaviour in the presence of non-denoting terms.
This is made explicit in the formulation of the Rule of Definition by Identity (see~\nameref{AOT:df-rules-terms[1]}):

\begin{quote}
@{thm[display] "df-rules-terms[1]"[axiom_inst, print_as_rule, of \<tau> \<sigma> _ \<tau>\<^sub>1\<tau>\<^sub>n]}
\end{quote}

I.e. if the definiens denotes, a definition by identity implies identity, if the definitions fails to denote,
a definition by identity implies that the definiendum fails to denote as well.
In the simplest case of a definition-by-identity that does not involve any free variables,
the definition-by-identity reduces to a plain identity, if the definiens provably denotes.

\<close>

subsection\<open>Reasoning in PLM\<close>(* TODO: section title? *)

text\<open>
Based on the fundamental meta-rules above, PLM derives further theorems and rules governing
Negations and Conditionals (see~\nameref{PLM: 9.5}); Quantification (see~\nameref{PLM: 9.6});
Logical Existence, Identity and Truth (see~\nameref{PLM: 9.7}); Actuality and Descriptions (see~\nameref{PLM: 9.8});
Necessity (see~\nameref{PLM: 9.9}); Relations (see~\nameref{PLM: 9.10}); Objects (see~\nameref{PLM: 9.11}) and
Propositional Properties (see~\nameref{PLM: 9.12}).
\<close>

subsection\<open>Restricted Variables\<close>text\<open>\label{RestrictedVariables}\<close>

text\<open>

TODO: cite discussion in PLM.

A common theme in abstract object theory is the definition and analysis of certain families
of objects. For instance, Possible Worlds, Logical Sets or Natural Numbers are families
of abstract objects with specific properties. Furthermore, some constructions involve talking
about the Ordinary Objects specifically. To be able to more conveniently state
theorems involving such families of objects, PLM introduces a general mechansism for defining
@{emph \<open>restricted variables\<close>} that range over objects satisfying a certain @{emph \<open>restriction condition\<close>}.
\<close>

text\<open>
A formula @{term \<psi>} that involves a single free, unrestricted variable @{term \<alpha>}, i.e. a formula
that can be written as @{text \<open>\<psi>{\<alpha>}\<close>} in the notational convention of the embedding, is called
a @{emph \<open>restriction condition\<close>}, just in case that it is both @{emph \<open>non-empty\<close>}, i.e.
@{thm (concl) "AOT_restriction_condition.res-var:2"[of \<psi>, print_as_theorem]} is a (modally-strict)
theorem, and has @{emph \<open>strict existential import\<close>}, i.e. @{thm (concl) "AOT_restriction_condition.res-var:3"[of \<psi> _ \<tau>, print_as_theorem]}
is a (modally-strict) theorem. PLM distinguishes @{emph \<open>restriction conditions\<close>}, in which non-emptyness
and strict existential import are modally-strict and @{emph \<open>weak restriction conditions\<close>}, in which neither
are required to be modally strict. Since the parts of PLM implemented in our embedding do not involve
weak restriction conditions, the embedding thus far forgoes an implementation of them. However,
it should be straightforward to extend the current implementation to also cover weak restriction
conditions.

An example of a restriction condition is @{emph \<open>being ordinary\<close>}, i.e. @{term \<open>\<guillemotleft>O!x\<guillemotright>\<close>}.\footnote{It
is a theorem that there necessarily exists an ordinary object @{thm "o-objects-exist:1"[print_as_theorem]}
TODO: cite PLM and embedding, as a consequence of the modal axiom @{thm "qml:4"[axiom_inst, print_as_theorem]},
the definition of @{emph \<open>being ordinary\<close>} as @{thm "oa:1"}, @{text \<open>\<beta>\<close>}-conversion and some modal reasoning.
Furthermore, strict existential instance follows from the last quantifier axiom TODO: ref.}

Restricted variables are governed by the following conventions (TODO: cite PLM):
Let @{term \<open>\<gamma>\<close>} be a variable that is restricted by the restriction condition @{text \<open>\<psi>{\<alpha>}\<close>}.
Then a quantified formula of the form @{text \<open>\<forall>\<gamma> \<phi>{\<gamma>}\<close>} is to be understood as an
abbreviation of @{text \<open>\<forall>\<alpha>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close>} for an unrestricted variable @{text \<open>\<alpha>\<close>}.
Furthermore, @{text \<open>\<exists>\<gamma> \<phi>{\<gamma>}\<close>} abbreviates @{text \<open>\<exists>\<alpha>(\<psi>{\<alpha>} & \<phi>{\<alpha>})\<close>} and similar
conventions are introduced for definite descriptions, @{text \<open>\<lambda>\<close>}-expressions and
definitions.

For weak restriction conditions, PLM bans the use of free restricted variables in theorem
statements and merely allows bound occurrences. However, for strict restriction conditions
PLM allows the use of free restricted variables and extends reasoning in the system
by allowing to take @{text \<open>\<psi>{\<gamma>}\<close>} as modally-strict axiom.

This construction allows natural reasoning with restricted variables, i.e. the
fundamental rules @{emph \<open>GEN\<close>} and @{emph \<open>RN\<close>} as well as usual quantifier
and modal reasoning (e.g. @{text \<open>\<forall>\<close>}-elimination, existential introduction, Barcan
formulas, etc.) can be extended to restricted variables introduced using a strict
restriction condition.
\<close>

subsection\<open>Identity on the Ordinary Objects\<close>

text\<open>
While the general definition of identity for individuals was given in TODO: ref,
PLM also introduces an identity @{emph \<open>relation\<close>} on the ordinary objects and
matching infix notation (see~\nameref{AOT:=E}):

\begin{quote}
@{thm [display] "=E"}
@{thm [display] "=E-simple:1"[of _ x y, print_as_theorem]}
\end{quote}

Notably, while the above definition of @{text \<open>=\<^sub>E\<close>} constitutes a denoting
@{emph \<open>relation\<close>} (the @{text \<open>\<lambda>\<close>}-expression does not involve encoding claims
and thereby denotes by axiom), general identity of both ordinary and abstract objects
@{emph \<open>does\<close>} involve encoding claims and does not constitute a general relation of
identity.

Identity on the Ordinary objects will play an important role in PLM's analysis of
Natural Numbers, discussed in chapter~\ref{NaturalNumbers}.
\<close>

subsection\<open>Definite Descriptions\<close>

text\<open>The following axiom that was already mentioned in section~\ref{AxiomSystem} governs
definite descriptions:

\begin{quote}
@{thm descriptions[axiom_inst, of _ x \<phi>, print_as_theorem]}
\end{quote}

In particular, definite descriptions are @{emph \<open>modally rigid\<close>} and refer to objects
in the actual world. While an extensive set of theorems and rules for reasoning with
definite descriptions is given in section 9.8 of PLM (see~\nameref{PLM: 9.8}), for
an intuitive understanding of descriptions in AOT it suffices to note that they follow
Russell's analysis of definite descriptions. In particular, atomic formulas involving
definite descriptions can be translated to existence claims as follows (for
simplicity we restrict ourselves to the case of unary exemplification and encoding):

\begin{quote}
@{lemma[display] \<open>print_as_theorem \<guillemotleft>[\<Pi>]\<^bold>\<iota>x \<phi>{x} \<equiv> \<exists>x (\<^bold>\<A>\<phi>{x} & \<forall>z (\<^bold>\<A>\<phi>{z} \<rightarrow> z = x) & [\<Pi>]x)\<guillemotright>\<close>
  by (safe intro!: print_as_theoremI "russell-axiom[exe,1].nec-russell-axiom")}
@{lemma[display] \<open>print_as_theorem \<guillemotleft>\<^bold>\<iota>x \<phi>{x}[\<Pi>] \<equiv> \<exists>x (\<^bold>\<A>\<phi>{x} & \<forall>z (\<^bold>\<A>\<phi>{z} \<rightarrow> z = x) & x[\<Pi>])\<guillemotright>\<close>
  by (safe intro!: print_as_theoremI "russell-axiom[enc,1].nec-russell-axiom")}
\end{quote}

I.e. an atomic formula involving a description is equivalent to there being a unique
object that actually satisfies the matrix of the description and this object satisfies
the given atomic formula.

Similarly, a definite description denotes, just in case that there is a unique object
that actually satisfies its matrix:

\begin{quote}
@{thm[display] "actual-desc:1"[print_as_theorem, of \<phi>]}
\end{quote}
\<close>

subsection\<open>Modally-Strict and Modally-Fragile Theorems\<close>text\<open>\label{ModallyStrictFragile}\<close>

text\<open>
PLM constructs two derivational systems, a modally-fragile one, @{text \<open>\<^bold>\<turnstile>\<close>}, and
a modally-strict one @{text \<open>\<^bold>\<turnstile>\<^sub>\<box>\<close>}.
The main difference between the two is that the modally-fragile system is equipped with
the modally-fragile axiom of actuality and its universal and actual (though not its necessary)
closures (as mentioned in section~\ref{AxiomSystem}):

\begin{quote}
@{thm[display] "logic-actual"[act_axiom_inst, of \<phi>]}
\end{quote}

As indicated by this axiom, semantically, the modally-fragile system is concerned with
all actual truths, whereas the modally-strict system is used to reason about truths that
are necessary.

Consequently, the fundamental meta-rule RN mentioned in section~\ref{MetaRules} is restricted
to modally-strict derivations: If @{term \<phi>} has a modally-strict proof, then its necessitation
@{term \<open>\<guillemotleft>\<box>\<phi>\<guillemotright>\<close>} is an (again modally-strict) theorem.

PLM's axiom system has the property that the actualization of any modally-fragile
axiom (in particular @{thm "act-conj-act:4"[print_as_theorem, of \<phi>]}) is a modally-strict
theorem (see~\nameref{AOT:act-conj-act:4}).

Consequently, for any formula that is derivable as modally-fragile theorem, i.e.
@{text \<open>\<^bold>\<turnstile> \<phi>\<close>}, it holds that @{text \<open>\<^bold>\<turnstile>\<^sub>\<box> \<^bold>\<A>\<phi>\<close>}. In particular, it follows from
@{text \<open>\<^bold>\<turnstile> \<box>\<phi>\<close>} that @{text \<open>\<^bold>\<turnstile>\<^sub>\<box> \<^bold>\<A>\<box>\<phi>\<close>}, which implies @{text \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi>\<close>}. PLM refers
to this principle as the @{emph \<open>weak converse of RN\<close>}.

However, while true in our semantics and derivable in the axiom system of PLM,
PLM rejects the weak converse of RN in general.
The goal is to explicitly allow augmenting the theory by asserting contingent truths without
having to assert their actualization as modally-strict fact. After doing so, the weak
converse of RN would indeed fail, so in order to keep the reasoning system robust against
additional assertions of this, PLM does not allow reasoning using the weak converse of RN.
A detailed discussion of this choice can be found in PLM (TODO: cite discussion in PLM).

While section~\ref{TrivialAccessibilityRelation} hints at a potential way of reproducing
this strict distinction using a more complex semantics, for simplicity we refrain from
doing so in our embedding and instead rely on our abstraction layers to prevent
reasoning using the weak converse of RN, while it remains valid in our semantics.\footnote{Note
that it is still possible to add contingent truths to the modally-fragile system of the
embedding and - while it would immediately become derivable semantically - just refrain
from adding a modally-strict actualization of the assertion to the abstraction
layer.}
\<close>

section\<open>Interesting Theorems of AOT\<close>

text\<open>
TODO: needs to mention:
  \<^item> There are distinct, but exemplification-indistinguishable abstract objects.
  \<^item> There is no general relation of identity.
  \<^item> There are 16 distinct properties (proof contributed by us). Relate to minimal models of AOT.
  \<^item> Blocking of the "Kirchner Paradox", referring to previous work.
  \<^item> "Kirchner's Theorem": Necessary and sufficient conditions for relations to denote (proof contributed by us).
  \<^item> Parts of possible world theory and in particular world-relative relations and the existence of Rigidifying relation (proof contributed by us, replacing it being an unnecessary axiom)
  \<^item> Maybe some "teasers" like the @{emph \<open>There are exactly two Truth Values.\<close>} or @{emph \<open>The True is identical to the Actual World.\<close>} or
    the Fundamental Theorems of Possible Worlds, etc. Maybe mention and cite extensibility e.g. to Temporal Logic as discussed in PLM's theory of stories (even though not yet embedded).

Maybe split into a part of interesting theorems and a part of interesting challenges (like the paradoxes and the free logic of lambda expressions).
\<close>

section\<open>Examples of Applications\<close>

text\<open>\<close>

section\<open>Implications for the Philosophy of Mathematics\<close>text\<open>\label{ImplicationsForPhilosophyOfMathematics}\<close>

text\<open>
TODO: Mention the use of higher-order AOT as logical meta-theory to argue for
logicism. Refer to the derivation of Natural Numbers claiming to be a "purely logical" derivation
in constract to a construction e.g. based on ZFC.
\<close>

chapter\<open>SSE of AOT in Isabelle/HOL\<close>text\<open>\label{SSEofAOT}\<close>

section\<open>Model\<close>

text\<open>
While the precise model construction of the embedding can be found in~\ref{AOT:AOT_model},
this section provides a high-level description of the construction.\footnote{Recall
the discussion in~\ref{SSE:MetaModel} for a precise meaning of constructing models
using an SSE.}
The general construction is based on Aczel models of AOT, which are extended
to accommodate for AOT's hyperintensional modal logic on the one hand and its
free logic for individual and relation terms on the other hand. Furthermore,
it employs type classes to model relations of arbitrary arity as relations among
tuples of individuals.

Note that while we talk about @{emph \<open>modelling\<close>} AOT, we do not construct concrete
models of AOT's logic in the classical sense. Instead, we @{emph \<open>implement\<close>} AOT in
Isabelle/HOL using a SSE and any set-theoretic model of the HOL theory we use as
meta-logic can be lifted to a full set-theoretic model of AOT. This way, in particular, we
can avoid defining concrete interpretation and assignment functions, since we can
rely on Isabelle's semantics for constants and variables instead. This technique
was discussed in more detail in section~\ref{SSE:MetaModel}.
\<close>

subsection\<open>Aczel Models\<close>

text\<open>
The general structure of our models is based on Aczel models (TODO: cite).
Aczel models are extensional models that validate both
the Comprehension Principle of Abstract Objects (the last axiom in section~\ref{AxiomSystem},
resp. \nameref{AOT:A-objects} in the embedding) and classical relation comprehension
in the absence of encoding formulas.

The following figure is illustrates the basic idea of Aczel models:

\tikzset{font=\fontsize{8pt}{10pt}\selectfont}
\begin{figure}[h!]
\centering
\begin{tikzpicture}

% Domains
 \node at (-2.4,-1) {Domain \textbf{D} = $\mathbf{A} \cup \mathbf{C}$};

% \node at (-.8,-1.5) {Define for $\mathitbf{x}\in \textbf{D}$, $|\mathitbf{x}| = 
%   \left\{\begin{array}{ll}
%      \hspace*{-.05in}\mathitbf{x}, \textrm{when}\  \mathitbf{x}\in \mathbf{C}\\
%      \hspace*{-.05in}\|\mathitbf{x}\|, \textrm{when}\  \mathitbf{x}\in 
% \mathbf{A}
%    \end{array}
%   \right.$};

% U
 \draw (0,0) ellipse (1 and .6);
 \draw (0,.6) -- (0,-.6);
 \node at (-2.5,0) {\textbf{U} = Urelements =};
 \node at (2.5,.7) {Define a mapping:};
 \node at (2.5,.4) {$\|a\| : \textbf{A} \to \textbf{S}$};
 \node at ($(-.45,.8)+(-90:1 and .6) + (0,-.2)$) {\textbf{C}};
 \node at ($(.45,.8)+(-90:1 and .6) + (0,-.2)$) {\textbf{S}};
 \node (S) at ($(.45,.9)+(-90:1 and .6) + (0,-.2)$) {};

% P
 \draw (0,2) ellipse (1.7 and 1);
 \node at (0,2) {\textbf{P} = Properties = $\wp (\mathbf{U})$};

% A
 \draw (0,4.8) ellipse (2.2 and 1.3);
 \node at (0,4.8) {\textbf{A} = Abstract Objects = $\wp (\mathbf{P})$};
 \node (A) at (1.7,4.1) {};


% Arrows
 \draw [>->] (A) to[out=-45, in=40] (S);

\end{tikzpicture}
\caption{Extensional, non-modal Aczel model of AOT.}\label{fig:aczel-model}
\end{figure}

Aczel models involve a domain of @{emph \<open>urelements\<close>} @{text U} that is split
into @{emph \<open>ordinary urelements\<close>} @{text C} and @{emph \<open>special urelements\<close>} @{term S}.
In the extensional, non-modal setting, the power set of the set of Urelements suffices
for representing properties. Abstract objects in turn are modelled using the power set
of properties.

Furthermore the models involve a (non-injective) mapping from abstract objects to
special urelements. The special urelement @{text \<open>||x||\<close>} to which an abstract object
@{text x} is mapped determines which properties the abstract object @{text x} @{emph \<open>exemplifies\<close>}.

The domain of individuals @{text D} is defined as the union of abstract objects and
ordinary urelements (resp. ordinary objects).

Any individual @{text \<open>x \<in> D\<close>} can be associated with an urelement @{text \<open>|x| \<in> U\<close>}:

\begin{equation*}
  |x| =
  \begin{cases}
    x\mbox{, if } x \in C \\
    ||x||\mbox{, if } x \in A
  \end{cases}
\end{equation*}

Based on this construction the truth conditions for AOT's atomic formulas, i.e.
encoding and exemplification, can be defined as follows:

  \<^item> An object @{text x} @{emph \<open>exemplifies\<close>} a property @{term F}, just in case that
    @{text \<open>|x| \<in> F\<close>}.
  \<^item> An object @{text x} @{emph \<open>encodes\<close>} a property @{term F}, just in case 
    @{text \<open>x \<in> A\<close>} and @{text \<open>F \<in> x\<close>}.

This construction immediately validates both the identity conditions for
abstract objects and the comprehension principle of abstract objects:

  \<^item> Two abstract objects are identical, if they encode the same properties.
  \<^item> For every set of properties, there is an abstract object that encodes exactly those
    properties in the set.

Furthermore, the models validate a restricted version of relation comprehension.
Since the truth conditions of any exemplification formula solely depend on the urelement
associated with the exemplifying individual, any condition @{term \<phi>} on individuals that does not
contain encoding claims can equivalently be represented as a condition on urelements.
Therefore, for any such condition @{term \<phi>}, there exists a relation @{term F} that is exemplified
by exactly those objects that satisfy @{term \<phi>}: @{text \<open>\<exists>F\<forall>x([F]x \<equiv> \<phi>{x})\<close>}, given
that @{text \<phi>} does not involve encoding claims.

While Aczel models generally demonstrate that abstract objects and encoding can be
modelled without being subject to the Clark-Boolos paradox (TODO: ref), there are
several issues that remain unaddressed:

  \<^item> AOT's relations are not extensional and not even merely intensional,
    but fully hyperintensional.
  \<^item> Relation comprehension for formulas in the absence of encoding formulas
    does not immediately cover all the base cases of axiomatically denoting relation
    terms as mentioned in section~\ref{AxiomSystem}.
  \<^item> Aczel models are prone to several classes of artifactual theorems, e.g.
    @{text[display] \<open>\<forall>x([F]x = [G]x) \<rightarrow> F = G\<close>}.

Therefore, while the models used for our embedding inherit the idea of urelements
and a mapping from abstract objects to special urelements, we significantly extend
the general model structure. As a first step, we describe the implementation of
AOT's hyperintensionality.
\<close>

subsection\<open>Hyperintensional Propositions\<close>

text\<open>

TODO: reference previous discussion of hyperintensionality, if any.

The hyperintensionality of AOT is modelled at the level of propositions.
A primitive type @{typ \<o>} (see~\nameref{AOT:AOT_model.<o>})
is used to represent hyperintensional propositions and is associated with modal extensions
following Kripke semantics: a primitive type @{typ w} for semantic possible
worlds is introduced (see~\nameref{AOT:AOT_model.w}) and it is axiomatized that
there be a surjective mapping @{term AOT_model_d\<o>} from propositions of type @{typ \<o>}
to Kripke-extensions, i.e. boolean valued functions on possible worlds (type @{typ \<open>w\<Rightarrow>bool\<close>};
see~\nameref{AOT:AOT_model.AOT_model_d<o>}).

We define for a proposition @{term p} of type @{typ \<o>} to be valid in a given semantic possible
world @{term v} (written @{term \<open>AOT_model_valid_in v p\<close>}), just in case @{term AOT_model_d\<o>} maps @{term p}
to a Kripke-extension that evaluates to @{term True} for @{term v} (see~\nameref{AOT:AOT_model.AOT_model_valid_in}).

This way, our type of propositions @{typ \<o>} is assured to contain a proposition for
each Kripke-extension, but still does not require the collapse of necessarily
equivalent propositions:

  \<^item> For any given Kripke-extension @{term \<phi>}, the inverse of @{term AOT_model_d\<o>}
    yields a proposition of type @{term \<o>} that is valid in exactly those worlds
    for which @{term \<phi>} evaluates to @{term True} (see~\nameref{AOT:AOT_model.AOT_model_proposition_choice}).
  \<^item> However, the construction allows for the type @{typ \<o>} to contain more propositions
    than there are Kripke-extensions. For example, there may be two distinct
    objects @{term p} and @{term q} of type @{typ \<o>} that are necessarilily equivalent,
    i.e. they are valid in the same semantic possible worlds. This can be confirmed by
    @{command nitpick}:
\<close>

lemma \<open>\<forall> v . [v \<Turnstile> p] \<longleftrightarrow> [v \<Turnstile> q]\<close> and \<open>p \<noteq> q\<close>
  nitpick[satisfy, user_axioms, expect=genuine]
  (*<*)oops(*>*)

text\<open>
@{command nitpick} can find a model in which @{term p} and @{term q} are mapped
to two distinct propositions, both of which evaluate to the same Kripke-extension
under @{term AOT_model_d\<o>}.

Note, however, that the construction also @{emph \<open>allows\<close>} for necessary equivalent
propositions to be collapsed:
\<close>

lemma \<open>\<forall> p q . (\<forall> v . [v \<Turnstile> p] \<longleftrightarrow> [v \<Turnstile> q]) \<longrightarrow> p = q\<close>
  nitpick[satisfy, user_axioms, expect=genuine]
  (*<*)oops(*>*)

text\<open>
In this case @{command nitpick} chooses a model in which the type @{typ \<o>} is
isomorphic to the type of Kripke-extensions @{typ \<open>w \<Rightarrow> bool\<close>}, i.e. there are
just as many objects of type @{typ \<o>} as there are Kripke-extensions.

So just as AOT itself, the model construction does not presuppose the degree of hyperintensionality of
propositions.

As a next step we construct a variant of Aczel models on top of the hyperintensional
propositions that aims to preserve hyperintensionality for relations and accounts
for AOT's free logic.
\<close>

subsection\<open>Extended Aczel Model Structure\<close>

(*<*)
(* TODO: ugly hack *)
consts explicitParen :: 'a
syntax (input) "_explicitParen" :: \<open>\<phi> \<Rightarrow> \<phi>\<close> ("\<^bold>'(_\<^bold>')")
syntax (output) "_explicitParen" :: \<open>\<phi> \<Rightarrow> \<phi>\<close> ("'(_')")
translations
  "_explicitParen x" == "CONST explicitParen x"
(*>*)

text\<open>
The embedding introduces a type of urelements @{typ \<upsilon>} (see~\nameref{AOT:AOT_model.<upsilon>})
that is comprised of three separate kinds of urelements:

  \<^item> Ordinary urelements of type @{typ \<omega>} (see~\nameref{AOT:AOT_model.<omega>}),
  \<^item> Special urelements of type @{typ \<sigma>} (see~\nameref{AOT:AOT_model.<sigma>}) and
  \<^item> Null-urelements of type @{typ null} (see~\nameref{AOT:AOT_model.null}).

Following the structure of Aczel models, ordinary urelements are used to model
ordinary objects and special urelements determine the exemplification behaviour of
abstract objects. The additional null-urelements are introduced to be able to
distinguish between distinct non-denoting individual terms.

For simple models, a plain primitive type for the special urelements suffices. However,
to model our proposed extended relation comprehension, we use a richer type
for special urelements and model them as subset of the set of triples of two copies
of sets of exemplification extensions on Ordinary urelements and one
very special urelements (type @{typ \<sigma>'}).
This is discussed in more detail in section~\ref{pred}.

Hyperintensional relations are modelled as proposition-valued functions.
In particular, the embedding introduces the type @{typ urrel} (see~\nameref{AOT:AOT_model.urrel})
that is represented by the set of all functions from urelements to propositions (type
@{typ \<open>\<upsilon> \<Rightarrow> \<o>\<close>}), which map null-urelements to necessarily false propositions.
This type or @{emph \<open>urrelations\<close>} will correspond to denoting property terms.

The additional null-urelements serve to avoid two kinds of artifactual theorems:
  \<^item> Let @{term p} be the proposition denoted by the term \<^term>\<open>\<guillemotleft>[F]\<^bold>\<iota>x \<phi>{x}\<guillemotright>\<close>
    and let @{term q} be the proposition denoted by the term \<^term>\<open>\<guillemotleft>[F]\<^bold>\<iota>x \<psi>{x}\<guillemotright>\<close>.
    Furthermore, assume that provably neither of the descriptions denote,
    i.e. both \<^term>\<open>\<guillemotleft>\<not>\<^bold>\<iota>x(\<phi>{x})\<down>\<guillemotright>\<close> and  \<^term>\<open>\<guillemotleft>\<not>\<^bold>\<iota>x(\<psi>{x})\<down>\<guillemotright>\<close> are theorems.
    Now while AOT requires @{term p} and @{term q} to be necessarily equivalent,
    in particular they are both necessarily false, it does not presuppose that @{term p} is
    @{emph \<open>identical\<close>} to @{term \<open>q\<close>}. In the model this is achieved by allowing
    both descriptions to be mapped to distinct null-urelements to which the urrelation
    corresponding to @{term F} can assign distinct (albeit necessarily false)
    propositions.
  \<^item> In AOT there may be distinct properties, s.t. for any object exemplifying either of
    them necessarily results in the same proposition, i.e. @{term \<open>print_as_theorem \<guillemotleft>\<forall>x \<box>\<^bold>(([F]x) = ([G]x)\<^bold>)\<guillemotright>\<close>}
    does @{emph \<open>not\<close>} imply @{term \<open>F = G\<close>}. The @{text \<open>\<forall>\<close>}-quantifier ranges over all denoting
    individuals. If relations were merely modelled as functions from urelements that
    correspond to denoting individual terms to propositions, the identity would follow,
    since two functions are identical, if they map to identical values for all arguments.
    By introducing null-urelements, however, we allow @{term F} and @{term G} to vary
    on additional urelements outside of the range of the quantifier.
  \<^item> It is important to note that the additional null-urelements have no impact on
    minimal models of AOT. In minimal models, propositions are extensional, i.e. they are
    in one-to-one correspondence to Kripke-extensions: for every boolean valued functions
    on possible worlds there is exactly one proposition.
    Since urrelations are required to necessarily be false on null-urelements, the
    introduction of one null-urelement does not increase the amount of relations in the
    models: while urrelations have to assign a Kripke-extensions to this null-urelement,
    there is only one choice for doing so, namely the constant-false function on possible
    worlds.

As a last ingredient of our Aczel model structure, we require a mapping @{text \<alpha>\<sigma>}
from sets of urrelations (which will be used to represent abstract objects) to
special urelements (see~\nameref{AOT:AOT_model.<alpha><sigma>}).

For urrelations to become a proper quotient of proposition-valued functions acting
on individual @{emph \<open>terms\<close>}, as described below, we require this mapping to be
surjective. For simple models that do not validate extended relation comprehension
it is easy to show that suitable surjective mappings exist (see~\nameref{AOT:AOT_model.<alpha><sigma>_restr})
and @{emph \<open>any\<close>} such surjective mapping is admissible. For the extended models,
we require additional properties and proving that those properties can be satisfied
is more involved (see~\nameref{AOT:AOT_model.<alpha><sigma>_ext} and the more detailed
discussion in section~\ref{pred}).

Given this extended Aczel model structure we can represent the terms of AOT.
\<close>

subsection\<open>Individual Terms and Type Classes for Terms\<close>text\<open>\label{IndividualTermsAndClasses}\<close>

text\<open>
As a first step in representing the terms of AOT, we introduce a concrete
type of individual terms @{typ \<kappa>} (see~\nameref{AOT:AOT_model.<kappa>}).
The type @{typ \<kappa>} consists of ordinary objects of type @{typ \<omega>} (shared with ordinary
urelements), abstract objects modelled as sets of urelements (type @{typ \<open>urrel set\<close>})
and null-objects of type @{typ null} (shared with null-urelements) that will
serve to model non-denoting definite descriptions. We can lift the surjective
mapping from abstract objects to special urelements @{text \<alpha>\<sigma>} to a full mapping
from individual terms to urelements @{text \<kappa>\<upsilon>} of type @{typ \<open>\<kappa> \<Rightarrow> \<upsilon>\<close>} (see~\nameref{AOT:AOT_model.<kappa><upsilon>}),
s.t. for any urelement we can find an individual term that is mapped to that urelement.

However, we also introduce a system of @{emph \<open>type classes\<close>} that abstract over
concrete types for two reasons (TODO: reference some to-be-done discussion of type classes?):
  \<^item> AOT involves axioms and theorems with (meta-)variables that may be instantiated
    to terms of several different types. In order not to have to restate multiple
    instances of such statements we formulate type classes that abstract over the
    required shared properties of all admissible types and prove the respective
    statement relative to this type class (which is instantiated to all concrete types
    that satisfy the necessary requirements).
  \<^item> AOT involves statements about @{text n}-ary relations for arbitrary @{text \<open>n \<ge> 0\<close>},
    so to cover the full extend of such statements, enumerating all concrete instances
    would be impossible. Instead we model relations acting on any type of an abstract
    type class of individual terms and then show that the product of an unary
    individual term (which constitutes another more restricted type class which
    abstracts the distinctive properties of the concrete type @{typ \<kappa>}) and another
    individual term (which may itself be an unary individual term or a product) again
    satisfies the requirements of the type class of individual terms. This way
    any statement about relations on the type class individual terms implicitly holds
    for relations among tuples of an arbitrary amount of objects of type @{typ \<kappa>}, i.e.
    we can capture statements about arbitrary @{text n}-ary relations.

The most basic type class we introduce is @{class AOT_Term} (see~\nameref{AOT:AOT_model.AOT_Term}).
It involves an abstract notion of a term to denote @{const AOT_model_denotes} for which
it is merely required that it is satisfied by at least one object. For example, for
type @{typ \<kappa>} @{const AOT_model_denotes} is true for all objects that are not null-objects.
We will later define quantifiers relative to this type class and prove the quantifier axioms, which are
independent of the concrete definition of the conditions under which an object of any
concrete type denotes.

The generic type class for individual terms based on which we will define relation terms
is @{class AOT_IndividualTerm} (see~\nameref{AOT:AOT_model.AOT_Term}).
The most important parameter of this type class is @{const AOT_model_term_equiv}, an
equivalence relation which is satisfied for two objects, if they have common urelements.
We furthermore introduce the notion of individual terms to be @{emph \<open>regular\<close>} and
specify a transformation of proposition-valued functions acting on individual terms, s.t.
the after the transformation the behaviour of the function is solely determined by
its values on regular terms. We will discuss this in more detail in the context of
@{text n}-ary relation identity (TODO: ref). An unary individual term is always
regular, while a tuple will only be regular, if at most one of its elements does not
denote.

We successively define more refined type classes on top of the basic class of
@{class AOT_IndividualTerm} to capture further and more abstract notions of
individual terms, e.g. we define an abstract notion of @{text n}-ary encoding
using the type classes @{class AOT_UnaryEnc} and @{class AOT_Enc} (see~\nameref{AOT:AOT_semantics.AOT_UnaryEnc} and~\nameref{AOT:AOT_semantics.AOT_Enc}).

We end up at the most refined classes @{class AOT_\<kappa>s} with the unary case
@{class AOT_\<kappa>} (see~\nameref{AOT:AOT_semantics.AOT_<kappa>s}), which will be used as the
default type classes for individuals and relations among them for the
formulation of the axiom system.

\<close>
subsection\<open>Relation Terms as Proposition-Valued Functions on Individual Terms\<close>
text\<open>
We can now introduce a generic type of relation terms as the type of
proposition-valued functions acting on a type of class @{class AOT_IndividualTerm}
(see~\nameref{AOT:AOT_model.rel}).
To instantiate the type class @{class AOT_Term} to this generic type of relation terms,
we have to define the conditions under which a relation term denotes.

A relation term denotes, if it is represented by a proposition-valued functions @{term \<phi>} on
individual terms, such that (TODO: figure out how to reference):
  \<^item> @{term \<phi>} agrees on equivalent terms, i.e. it evaluates to the same proposition for
    individual terms that share the same urelements.
  \<^item> For non-denoting individual terms, @{term \<phi>} evaluates to necessarily false propositions.
  \<^item> @{term \<phi>} is well-behaved on irregular terms (i.e. on irregular terms it evaluates
    to the proposition given by @{term \<open>AOT_model_irregular \<phi>\<close>}, which solely depends
    on @{term \<phi>}'s behaviour on regular terms).

Based on this definition, we can derive that denoting relation terms among type @{typ \<kappa>}
correspond to the urrelations of type @{typ urrel} we introduced earlier (see~\nameref{AOT:AOT_model.rel_to_urrel}).
This is crucial for validating the comprehension principle of abstract objects, since abstract objects
were modelled as sets of urrelations.

TODO: model encoding; maybe some more words about the tuple instantiation; trivial
instantiations for propositions. Relate to co-existence and Kirchner's theorem.

Before we describe how we derive an abstract semantics of AOT from this model
construction in section~\ref{Semantics}, we briefly discuss how we extend Isabelle's
inner syntax by an approximation of the syntax used in PLM and how we extend
Isabelle's outer syntax by custom commands used for structures reasoning in
the embedding. (TODO: reformulate)
\<close>

section\<open>Syntax of the Target Theory\<close>

text\<open>
We already discussed the possibility of extending Isabelle's inner syntax in general
in section~\ref{SSESyntax}. Following the method described in that section, we introduce
@{type AOT_prop} as syntactic root type for propsitions in AOT and define a custom grammar
for AOT on top of it. However, Isabelle's high-level mechanisms for defining
custom syntax has certain limitations that make an accurate representation of
AOT's usual syntax challenging.

In particular, Isabelle's lexical analysis is not designed to be configurable.
It presupposes that identifiers consist of multiple characters and have to be
delimited by whitespace or certain delimiter tokens.

While requiring identifiers to be delimited can be considered as a reasonable syntactic
concession, we found that reproducing the compact form of atomic formulas used in PLM
results in significantly improved readability.

Therefore we utilize Isabelle's low-level mechanisms to customize syntax by providing
transformations on its AST and its term representation written in Standard ML.

TODO: change to meta-variables, add @{const AOT_term_of_var} or comment about it.
In particular, we use @{command parse_ast_translation}s and @{command parse_translation}s (TODO cite)
to split what Isabelle would natively regard as a single identifier. That way we are
able to e.g. translate the term @{term \<open>print_as_theorem \<guillemotleft>[F]xy\<guillemotright>\<close>} to
@{text \<open>AOT_exe F (x, y)\<close>}. The 2-ary exemplification formula is translated to
an application of the constant @{const AOT_exe} to the relation term and a tuple of
individuals. Similarly, @{term \<open>print_as_theorem \<guillemotleft>xy[F]\<guillemotright>\<close>} is translated to
@{text \<open>AOT_enc (x,y) F\<close>}. The involved constants are introduced in~\ref{AOT:AOT_syntax}
as uninterpreted constants (see~\nameref{AOT:AOT_syntax.AOT_denotes}), which will only
later be enriched with semantic structure using @{command specification}s (TODO: refs).

Furthermore, PLM associates the symbols used for its terms with their types, as described in
section~\ref{AOTLanguage}. While it is possible to rely on Isabelle's type inference,
this will not always result in correctly typed terms without additional type annotations
which would negatively affect readability.

For that reason, we construct an extensible system for typing terms based on their names.
In particular we introduce the command @{command AOT_register_type_constraints} that
can be used to introduce named categories of types and equip them with type constraints
both for unary terms and tuples. We then allow registering symbols as variables and
metavariables of the given category with @{command AOT_register_variable_names} and
@{command AOT_register_metavariable_names}. The extensible design allows for reproducing
AOT's concept of @{emph \<open>restricted variables\<close>} (see~\ref{RestrictedVariables}) by further
associating a term category with a restriction condition (see~\ref{AOT:AOT_RestrictedVariables})
as required. TODO: details?

A danger in the extensive use of complex custom syntax is silent errors in the syntactic
translations that could result in an expression to be parsed contrary to their intended
meaning. To alleviate this danger we define multiple @{emph \<open>printing modes\<close>}. The
embedding can be configured to print terms in an approximation of AOT's syntax, e.g.:

@{term[display] \<open>\<guillemotleft>[\<Pi>]\<kappa>y \<rightarrow> (p \<or> \<phi>)\<guillemotright>\<close>}

using meta-syntax, an enriched version of HOL's syntax without complex transformations, e.g.:
\<close>(*<*) unbundle AOT_no_syntax context AOT_meta_syntax begin (*>*)text\<open>
@{term[display] \<open>\<guillemotleft>[\<Pi>]\<kappa>y \<rightarrow> (p \<or> \<phi>)\<guillemotright>\<close>}

or as plain HOL terms without any syntactic sugar, e.g.:\<close>(*<*) end (*>*)text\<open>
@{term[display] \<open>\<guillemotleft>[\<Pi>]\<kappa>y \<rightarrow> (p \<or> \<phi>)\<guillemotright>\<close>}
\<close>
(*<*) unbundle AOT_syntax (*>*)
text\<open>

Note that while the meta-syntax already involves distracting complexities like the
annotation of non-meta-variables using @{text \<open>\<langle>_\<rangle>\<close>}, additional explicit syntax for
exemplification @{text \<open>\<^bold>\<lparr>_,_\<^bold>\<rparr>\<close>} and explicit tuples, plain HOL syntax quickly
becomes unreadable for complex terms.

For the purpose of implementing a full theory with an extensive body of theorems
we feel that the improved readability outweighs the potential danger of complex
syntax transformations, especially given the ability to confirm the accuracy of
the translation using less complex printing modes.

TODO: mention ellipses?
\<close>

section\<open>Extending Isabelle's Outer Syntax\<close>

text\<open>

While the syntax transformations described in the last section go a long way in
allowing the intuitive statement of propositions of AOT, @{emph \<open>reasoning\<close>}
in the target logic entails additional challenges.

In particular, reasoning in the embedding involves keeping track of the semantic
possible world in which statements are valid. To avoid this cognitive overhead,
we implement a copy of Isabelle's Isar language in Standard ML that automatically
handles semantic possible worlds and allows theorem statements and proofs to be
transferred directly from PLM without the need of explicitly mention semantic possible
worlds. The list of commands can be found in~\ref{AOT:AOT_commands}, while the actual
ML implementation is available at (TODO: cite github repository).

Apart from tracking semantic possible worlds, the introduced commands also automatically
parse formulas relative to the @{type AOT_prop} grammar root mentioned in the last
section.

Additionally, we introduce the command @{command AOT_define}, which allows to directly
state definitions as in PLM. Internally, this involves introducing a new constant for
the defined entity, setting up the syntax for parsing and printing according to the
specified @{emph \<open>syntactic\<close>} type of the defined entity (while the logical type of
the constant is deduced). This new constant is then automatically specified to
fulfill the given definition using a mechanism similar to the @{command specification}
command, while the entailed existence proof is constructed automatically.

Furthermore, we introduce convenience commands like @{command AOT_find_theorems} and 
@{command AOT_sledgehammer}. @{command AOT_find_theorems} works similar to the Isar
command @{command find_theorems}, but automatically parses AOT syntax and generalizes
concrete variables to schematic variables for pattern matching (TODO: explain, cite?).
@{command AOT_sledgehammer} is a wrapper around @{command sledgehammer} that invokes
@{command sledgehammer} while restricting its search for theorems, s.t. the model-specific
theorems are ignored and only the theorems of the abstraction layers are allowed for proofs.

\<close>

section\<open>Representation of an Abstract Semantics of AOT\<close>text\<open>\label{Semantics}\<close>
text\<open>
In~\ref{AOT:AOT_semantics}, we derive an abstract semantics for the primitive and
some of the basic defined notions of AOT. This layer of abstraction is still allowed
to refer to the details of the model construction, but attempts to only derive just the
properties of the models that are required to derive the axiom system and fundamental
metarules of AOT later.

The defined semantics heavily rely on Isabelle's @{command specification} command to
abstract specific model choices to more general semantic properties.

The main purpose of this intermediate layer is to keep the derivation of the abstraction
layer used for the axiom system and deductive system of AOT, impervious to minor changes
in the models.

TODO: say more? examples?
\<close>

section\<open>Axiom System and Deductive System\<close>
text\<open>
The axiom system as derived in the embedding was already described in
section~\ref{AxiomSystem} and the fundamental metarules were mentioned in
section~\ref{DeductiveSystem}. By construction, most of them can be derived from the
abstract semantics described in the last section using simple, automatic proofs.

In the following sections we will focus on some particular axioms, rules and proofs
that are challenging to properly represent in the embedding. This mostly happens due to
PLM's statement involving either complex preconditions given in natural language or
due to the statement involving complex ellipses to generalize across e.g. arbitrary
arities of relations. 
\<close>

subsection\<open>Base Cases of Denoting Terms\<close>text\<open>\label{cqt:2-impl}\<close>

text\<open>

One of the axioms we mentioned explicitly as difficult to implement in section~\ref{AxiomSystem} was
the second quantifier axiom (see~\nameref{AOT:cqt:2[const_var]}) which establishes
a set of base cases of denoting terms. Recall the formulation of the axiom in PLM:

\begin{quote}
  \Squ{@{term \<open>\<guillemotleft>\<tau>\<down>\<guillemotright>\<close>}, provided @{term \<tau>} is a primitive constant, a variable, or a @{text \<open>\<lambda>\<close>}-expression
  in which the initial @{text \<open>\<lambda>\<close>} does not bind any variable in any encoding formula subterm.}
\end{quote}

We implement this axiom by splitting it up into cases. The first and obvious way
to split the axiom is to split it into the separate cases listed in the natural language
formulation: constants, variables and @{text \<open>\<lambda>\<close>}-expressions.

As discussed in more detail in section (TODO), the embedding does not have to distinguish
explicitly between constants and variables, so it suffices to state one case for
constants @{emph \<open>and\<close>} variables:

\begin{quote}
  @{thm[display] "cqt:2[const_var]"[axiom_inst, of _ \<alpha>, print_as_theorem]}
\end{quote}

This covers all expressions of type @{typ \<open>'a AOT_var\<close>} (see~\nameref{AOT:AOT_model.AOT_var}).
The embedding defines this type for each base type @{typ 'a} of class @{class AOT_Term} as all
members of the type that denote (see~\nameref{AOT:AOT_model.AOT_Term} and the discussion
n section~\ref{IndividualTermsAndClasses}). Any variable name is decorated with the constant
@{term AOT_term_of_var} of type @{typ \<open>'a AOT_var \<Rightarrow> 'a\<close>} and thereby implicitly denotes.
By construction there exists an object of type @{typ \<open>'a AOT_var\<close>} for every denoting
object of type @{typ 'a} and vice-versa.

The second base case for @{text \<open>\<lambda>\<close>}-expressions is more complex to represent.
While we cannot capture the syntactic restriction that the initial @{text \<open>\<lambda>\<close>}
does not bind any variable in any encoding formula subterm, we can inductively construct
the set of all formulas that match this description.

To that end we define the auxiliary constant @{const AOT_instance_of_cqt_2} (see~\nameref{AOT:AOT_semantics.AOT_instance_of_cqt_2}),
which acts on matrices of @{text \<open>\<lambda>\<close>}-expressions, i.e. on functions among individuals
of a type of class @{class AOT_\<kappa>s} (see~\ref{IndividualTermsAndClasses}).

@{const AOT_instance_of_cqt_2} itself is merely defined to be true for a matrix,
if using it as matrix for a @{text \<open>\<lambda>\<close>}-expression results in a term that necessarily
denotes. Internally, a @{text \<open>\<lambda>\<close>}-expression denotes, just in case that its
matrix is necessarily equivalent on all denoting objects that share an urelement, or
formally (see~\nameref{AOT:AOT_semantics.AOT_model_lambda_denotes}):

\begin{quote}
  @{thm[display] AOT_model_lambda_denotes[of \<phi>]}
\end{quote}

However, this is a semantic criterion and does not directly correspond to the formulation of above axiom. So instead
we derive inductive introduction rules for the predicate @{const AOT_instance_of_cqt_2}.

There are several cases:

  \<^item> Matrices with no free occurrences of the @{text \<open>\<lambda>\<close>}-bound variables trivially fall
    under the formulation of the axiom (see~\nameref{AOT:AOT_semantics.AOT_instance_of_cqt_2_intros_const}).
  \<^item> Exemplification formulas fall under the formulation of the axiom, if all primary terms
    fall under the formulation of the axiom, neither in the relation term nor in any of the
    individual terms that exemplify the relation occurs any @{text \<open>\<lambda>\<close>}-bound variable
    in an encoding subformula (see~\nameref{AOT:AOT_semantics.AOT_instance_of_cqt_2_intros_exe}).
  \<^item> Similarly, encoding formulas fall under the formulation of the axiom, if all primary
    terms fall under the formulation of the axiom (see~\nameref{AOT:AOT_semantics.AOT_instance_of_cqt_2_intros_enc}).
    However, this in turn is only the case if they do not involve any free occurrences of
    the @{text \<open>\<lambda>\<close>}-bound variables. Thus this case is actually already covered by the
    first case.
  \<^item> Complex formulas fall under the formulation of the axiom, just in case all its operands
    fall under the formulation of the axiom. E.g. a negation formula falls under the axiom,
    just in case the negated formula falls under the axiom
    (see~\nameref{AOT:AOT_semantics.AOT_instance_of_cqt_2_intros_not}).

The cases of relation terms and individual terms in exemplification position are
further split up into multiple cases, including cases for definite descriptions.
A full account of the cases can be found in the embedding (see~\nameref{AOT:AOT_semantics.AOT_instance_of_cqt_2}).

Note that at the time of writing, an extension of the axiom is under discussion that
would generalize it to the following:

\begin{quote}
  \Squ{@{term \<open>\<guillemotleft>\<tau>\<down>\<guillemotright>\<close>}, provided @{term \<tau>} is a primitive constant, a variable, or a @{text \<open>\<lambda>\<close>}-expression
  in which the initial @{text \<open>\<lambda>\<close>} does not bind any variable that is a primary term in an encoding formula subterm.}
\end{quote}

In an encoding formula @{text \<open>[\<Pi>]\<kappa>\<^sub>1\<cdots>\<kappa>\<^sub>n\<close>} only @{text \<open>\<Pi>\<close>} as well as @{text \<open>\<kappa>\<^sub>1\<close>} through
@{text \<open>\<kappa>\<^sub>n\<close>} are defined to be primary terms, but no nested term counts as primary term, so
this entails strictly more cases than the formulation given above.

Accounting for this change in the embedding would entail extending the encoding formula
base cases of the construction. While the current version of the embedding given in the
appendix specifically does not validate this alternative formulation of the axiom in
order to avoid theorems that would be artifactual without the extended axiom (TODO: mention), it would
be straightforward to extend the implementation to encompass this new extended
version of the axiom, once it is clear that PLM will move in that direction. (TODO: watch formulation).


\<close>

subsection\<open>The Rule of Substitution\<close>

text\<open>\<close>

subsection\<open>Proofs by Type Distinction\<close>

text\<open>
PLM involves proofs that involve a case distinction by type. An example is the theorem
that for two terms to be identical implies that both denote (see~\nameref{AOT:AOT_PLM.AOT_Term_id}).

In our embedding we reproduce this kind of reasoning by introducing a new type class,
in this case @{class AOT_Term_id}, and then by instantiating this type class to all
the types the statement is supposed to apply to. We then redefine the default type
constraints for terms of the given types to entail the newly defined class.

In a future version of the embedding, we would like to use Standard ML to define
a simple outer syntax command that will hide the complexity of this process and
will allow for an intuitive statement of theorems that are to be proven by type
distinction.
\<close>

subsection\<open>Auxiliary Constructs\<close>

text\<open>
  \<^item> Attributes for instantiating AOT axioms.
  \<^item> Attributes for "rulifying" AOT theorems.
  \<^item> Attributes for unconstraining constrained variables.
\<close>

section\<open>Meta Theorems\<close>

subsection\<open>The Collapse of Alphabetic Variants\<close>text\<open>\label{alphabetic-variants}\<close>

text\<open>
We already informally stated that the embedding collapses alphabetic variants. In this section
we will define more precisely what this means and justify this collapse.

Isabelle internally represents bound variables using de-Bruijin indices (TODO: cite). We will
showcase this mechanism in detail below. As a consequence, terms that are alphabetic variants
are meta-logically indistinguishable. To justify representing AOT's bound variables directly
using bound variables in Isabelle, we need to show that both (1) AOT's notion of alphabetic
variants is equivalent to Isabelle's use of de-Bruijin indices and (2) any two formulas
involving alphabetic variants are inter-derivable in AOT (fortunately, PLM already derives a suitable
meta-rule).

\<close>

subsubsection\<open>AOT's Alphabetic Variants Correspond to Isabelle's de-Bruijin Indices\<close>

(*<*)
setup\<open>
let
val antiquotation_pretty_source = Thy_Output.antiquotation_pretty_source
(* Next Isabelle release:  = Document_Output.antiquotation_pretty_source *)
in
antiquotation_pretty_source
end @{binding "ML_print_term"} Args.term (
fn ctxt => fn trm => 
  Pretty.chunks [
  Pretty.block [Syntax.pretty_term ctxt trm],
  Pretty.str "\n",
  Pretty.markup_block {consistent = true, indent = 8, markup = Markup.ML_string}
    [Pretty.str (ML_Pretty.string_of_polyml (ML_system_pretty (trm, FixedInt.fromInt 100)))]]
)\<close>
(*>*)

text\<open>
Internally, Isabelle represents binding notation by function application and abstraction.
E.g. if we let Isabelle print the internal representation of the term @{term \<open>\<guillemotleft>\<forall>p (p \<rightarrow> p)\<guillemotright>\<close>},
we arrive at the following:@{footnote \<open>Technically, we have setup an @{emph \<open>antiquotation\<close>} that
allows us to print a term together with the internal ML representation of the term. TODO: cite isar-ref?\<close>}

@{ML_print_term \<open>\<guillemotleft>\<forall>p (p \<rightarrow> p)\<guillemotright>\<close>}

Note that while the internal representation retains the name of the bound variable @{text p}, it
has no logical meaning and is merely used for term printing, while, logically, occurrences of the
bound variables are referred to by @{text \<open>Bound\<close>} with a de-Bruijin index. An index of zero
refers to the innermost abstraction the bound variable is contained in. An index of one
refers to the next outer abstraction, e.g.

@{ML_print_term \<open>\<guillemotleft>\<forall>p (p \<rightarrow> \<forall>q (q \<rightarrow> p))\<guillemotright>\<close>}

Note that in the inner abstraction @{text \<open>Bound 0\<close>} refers to @{term q}, while @{text \<open>Bound 1\<close>}
refers to @{term p}.

Our claim is that two terms or formulas of AOT are alphabetic variants, if and only if their
representation using de-Bruijin indices is the same.

PLM defines alphabetic variants as follows (TODO: cite): It refers to two occurrences of a
variable as @{emph \<open>linked\<close>}, if both are free or they are bound by the same occurrence of a
variable-binding operator. PLM further introduces @{emph \<open>BV-notation\<close>} for formulas and terms@{footnote \<open>In
the following we will restrict our discussion to formulas, but the argument applies analogously to terms
as well.\<close>}: the BV-notation of a formula @{term \<phi>} is @{text \<open>\<phi>[\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n]\<close>}, where @{text \<open>\<alpha>\<^sub>1, \<dots> \<alpha>\<^sub>n\<close>}
is the list of all variables that occur bound in @{term \<phi>}, including repetitions.
Further @{text \<open>\<phi>[\<beta>\<^sub>1/\<alpha>\<^sub>1, \<dots>, \<beta>\<^sub>n/\<alpha>\<^sub>n]\<close>} refers to the result of replacing @{text \<open>\<alpha>\<^sub>i\<close>} by @{text \<open>\<beta>\<^sub>i\<close>}
in @{text \<open>\<phi>[\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n]\<close>}. Now @{term \<phi>'} is defined to be an @{emph \<open>alphabetic variant\<close>} of @{term \<phi>}
just in case for some @{text n}:
  \<^item> @{text \<open>\<phi>' = \<phi>[\<beta>\<^sub>1/\<alpha>\<^sub>1, \<dots>, \<beta>\<^sub>n/\<alpha>\<^sub>n]\<close>},
  \<^item> @{text \<phi>'} has the same number of bound variable occurrences as @{text \<phi>} and so can be written as
    @{text \<open>\<phi>'[\<beta>\<^sub>1, \<dots>, \<beta>\<^sub>n]\<close>}, and
  \<^item> for @{text \<open>1 \<le> i, j \<le> n\<close>}, @{text \<alpha>\<^sub>i} and @{text \<alpha>\<^sub>j} are linked in @{text \<open>\<phi>[\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n]\<close>} if and
    only if @{text \<beta>\<^sub>i} and @{text \<beta>\<^sub>j} are linked in @{text \<open>\<phi>'[\<beta>\<^sub>1, \<dots> \<beta>\<^sub>n]\<close>}.

By definition each group of @{emph \<open>linked\<close>} variable occurrences in AOT corresponds to exactly
one abstraction in Isabelle's internal representation and all de-Bruijin indexed @{text Bound} terms
that refer to this abstraction. Since changing the variable name of a linking group will not affect the
de-Bruijin indices, the de-Bruijin representation of two alphabetic variants is therefore the same.
Conversely, changing any index in the de-Bruijin representation translates to breaking a linking
group as defined in PLM, thereby terms with different de-Bruijin representation are not alphabetic
variants.

TODO: consider trying to come up with a constructive proof, even though the correspondence is rather
obvious.

Now that it is established that the formulas and terms that are collapsed in Isabelle's internal
representation are exactly the alphabetic variants of AOT, it remains to argue that the collapse
is inferentially valid, i.e. all statements of AOT are equivalent to their alphabetic variants.
\<close>

subsubsection\<open>Equivalence of Alphabetic Variants in AOT\<close>

text\<open>
Conveniently, PLM itself derives the following @{emph \<open>Rule of Alphabetic Variants\<close>} (TODO: cite):@{footnote \<open>Note
that while PLM states meta-rules using @{text \<open>\<turnstile>\<close>}, unless otherwise noted by convention they apply to both @{text \<open>\<turnstile>\<close>} and
@{text \<open>\<turnstile>\<^sub>\<box>\<close>}. We adopt this convention for this section.\<close>}

\begin{quote}
\Squ{@{text \<open>\<Gamma> \<turnstile> \<phi>\<close>} if and only if @{text \<open>\<Gamma> \<turnstile> \<phi>'\<close>}, where @{text \<open>\<phi>'\<close>} is any alphabetic variant
of @{text \<phi>}.}
\end{quote}

It is straightforward to strengthen this further to the following:

\begin{quote}
\Squ{@{text \<open>\<Gamma> \<turnstile> \<phi>\<close>} if and only if @{text \<open>\<Gamma>' \<turnstile> \<phi>'\<close>}, where @{text \<open>\<phi>'\<close>} is any alphabetic variant
of @{text \<phi>} and @{text \<open>\<Gamma>'\<close>} is a set of alphabetic variants of @{text \<open>\<Gamma>\<close>}, i.e.
for every @{text \<open>\<psi> \<in> \<Gamma>\<close>} there is an alphabetic variant @{text \<open>\<psi>'\<close>} of @{text \<open>\<psi>\<close>},
s.t. @{text \<open>\<psi>' \<in> \<Gamma>'\<close>}, and vice-versa.}
\end{quote}

For a proof it suffices to realize that for every @{text \<open>\<psi> \<in> \<Gamma>\<close>} and @{text \<open>\<psi>' \<in> \<Gamma>'\<close>} by the above rule it holds that
@{text \<open>\<psi> \<stileturn>\<turnstile> \<psi>'\<close>} and hence all premises in @{text \<Gamma>} are derivable from @{text \<Gamma>'} and vice-versa.

Hence AOT allows to freely move from any formula to an alphabetic variant in all theorems and assumptions,
justifying the fact that the embedding identifies alphabetic variants.

TODO: think about mentioning the @{attribute rename_abs} attribute that allows for renaming
linked groups of bound variables.

\<close>

subsection\<open>Explicit Free Variable Notation and Substitutability\<close>text\<open>\label{substitutability}\<close>

text\<open>
TODO: recheck and refine all references to this section.

As mentioned in chapter~\ref{AOT}, PLM allows terms and formulas with arbitrary free variables
to be used in place of of its meta-variables, except for free variables that are explicitly excluded
in natural language. The embedding on the other hand requires to explicitly mention any variables that
already have a name in the current context, if they should be allowed to occur in an instance of a meta-variable.

For example, PLM formulates the first quantifier axiom as follows:

\begin{quote}
\Squ{$\forall \alpha\,\varphi\;\rightarrow\;(\tau\downarrow\,\rightarrow\,\varphi^{\tau}_{\alpha})$,
provided @{text \<tau>} is substitutable for @{text \<alpha>} in @{text \<phi>}}
\end{quote}

Here $\varphi^{\tau}_{\alpha}$ is defined in PLM item (14) (TODO: cite) as recursively replacing all occurrences
of @{text \<open>\<alpha>\<close>} in @{text \<open>\<phi>\<close>} that are not bound @{emph \<open>within @{text \<phi>} itself\<close>} with @{text \<tau>}.

The precise definition of @{emph \<open>being substitutable\<close>} can be found in PLM item (15) (TODO: cite).
In particular, it states the following summary:

\begin{quote}
@{text \<tau>} is substitutable at an occurrence of @{text \<alpha>} in @{text \<phi>} or @{text \<sigma>} just in
case every occurrence of any variable @{text \<beta>} free in @{text \<tau>} remains an occurrence
that is free when @{text \<tau>} is substituted for that occurrence of @{text \<alpha>} in @{text \<phi>} or @{text \<sigma>}.
\end{quote}

and further:

\begin{quote}
@{text \<tau>} is substitutable for @{text \<alpha>} in @{text \<phi>} or @{text \<sigma>} just in case @{text \<tau>}
is substitutable at every free occurrence of @{text \<alpha>} in @{text \<phi>} or @{text \<sigma>}.
\end{quote}

In the embedding, the same axiom is stated as follows:

\begin{quote}
@{thm[display] "cqt:1"[axiom_inst, print_as_theorem, of _ \<phi> \<tau>]}
\end{quote}

Technically, @{term \<phi>} here is a function acting on terms and both @{text \<open>\<phi>{\<alpha>}\<close>}, resp.
@{text \<open>\<phi>{\<tau>}\<close>}, are the function application of @{term \<phi>} to @{text \<alpha>}, resp. @{text \<tau>}.


\begin{quote}
@{text \<tau>} is substitutable for @{text \<alpha>} in @{text \<phi>} or @{text \<sigma>} just in case every
occurrence of any variable @{text \<beta>} free in @{text \<tau>} @{text \<open>[\<dots>]\<close>} remains an
occurrence that is free when @{text \<tau>} is substituted for every free occurrence of @{text \<alpha>}
in @{text \<phi>} or @{text \<sigma>}.
\end{quote}


TODO



TODO
\<close>

subsection\<open>Generalizing Free Variables to Schematic Variables\<close>text\<open>\label{free-variables-schematic}\<close>

text\<open>
After a theorem is proven in Isabelle, it is implicitly exported to the current theory context in
@{emph \<open>schematic\<close>} form. That means each free variable used in the theorem is implicitly
generalized to a @{emph \<open>schematic variable\<close>} that can be instantiated to any variable or term of
the same type. Since the embedding uses distinct types for (denoting) variables and (potentially non-denoting) terms
that have the same type in AOT (see~\ref{cqt:2-impl}),
this does @{emph \<open>not\<close>} mean that any theorem involving AOT variables can be directly instantiated
to AOT terms, however, it does mean that all theorems of AOT are implicitly stated using
meta-variables ranging over all variable names. As an example the theorem
@{lemma \<open>print_as_theorem \<guillemotleft>\<forall>F ([F]x \<rightarrow> [F]x)\<guillemotright>\<close> by (auto intro!: print_as_theoremI "\<rightarrow>I" GEN)}
not only implicitly asserts its alphabetic variants, e.g. 
@{lemma \<open>print_as_theorem \<guillemotleft>\<forall>G ([G]x \<rightarrow> [G]x)\<guillemotright>\<close> by (auto intro!: print_as_theoremI "\<rightarrow>I" GEN)},
but can also be directly instantiated for a different free individual variable, e.g. 
@{lemma \<open>print_as_theorem \<guillemotleft>\<forall>G ([G]y \<rightarrow> [G]y)\<guillemotright>\<close> by (auto intro!: print_as_theoremI "\<rightarrow>I" GEN)}.
In the notation of AOT this means that we actually state the theorem
@{lemma \<open>print_as_theorem \<guillemotleft>\<forall>G ([G]\<nu> \<rightarrow> [G]\<nu>)\<guillemotright>\<close> by (auto intro!: print_as_theoremI "\<rightarrow>I" GEN)},
where @{term \<nu>} ranges over all names for individual variables. While PLM does not derive
a meta-rule that matches this principle, it is usually a straightforward consequence of a series of
applications of the meta-rule of universal generalization GEN followed by applications
of the rule of @{text \<open>\<forall>\<close>}Elimination for variables. However, to formulate this as a general
principle, some care has to be taken and we have to additionally rely on the collapse of
alphabetic variants.

We start by stating and proving the trivial case as a meta-rule in AOT's system:

\begin{quote}
\Squ{If @{text \<open>\<turnstile> \<phi>\<close>}, then @{text \<open>\<turnstile> \<phi>\<^sup>\<beta>\<^sub>\<alpha>\<close>} where @{text \<beta>} is substitutable for @{text \<alpha>} in @{text \<phi>}.}
\end{quote}

Assume @{text \<open>\<turnstile> \<phi>\<close>}. Since the derivation of @{text \<phi>} does not need any premises,
it follows by the rule of universal generalization (GEN) (TODO: cite) that @{text \<open>\<turnstile> \<forall>\<alpha> \<phi>\<close>}. Since by assumption
@{text \<beta>} is substitutable for @{text \<alpha>} in @{text \<phi>} we can immediately conclude by @{text \<open>\<forall>\<close>}Elimination (TODO: cite)
that @{text \<open>\<turnstile> \<phi>\<^sup>\<beta>\<^sub>\<alpha>\<close>}.

However, we want to generalize this rule further to a version that allows for premises and does
not require the proviso that @{text \<beta>} is substitutable for @{text \<alpha>} in @{text \<phi>}.

To that end the next step is to generalize above rule to include premises:

\begin{quote}
\Squ{If @{text \<open>\<Gamma> \<turnstile> \<phi>\<close>}, then @{text \<open>\<Gamma>\<^sup>\<beta>\<^sub>\<alpha> \<turnstile> \<phi>\<^sup>\<beta>\<^sub>\<alpha>\<close>} where @{text \<beta>} is substitutable for @{text \<alpha>} in @{text \<phi>} and
in all @{text \<open>\<psi> \<in> \<Gamma>\<close>} @{text \<beta>} is sustitutable for @{text \<alpha>} in @{text \<psi>} and @{text \<open>\<Gamma>\<^sup>\<beta>\<^sub>\<alpha>\<close>} is
the set of all @{text \<open>\<psi>\<^sup>\<beta>\<^sub>\<alpha>\<close>} for @{text \<open>\<psi> \<in> \<Gamma>\<close>}.}
\end{quote}

One way to show this is by first eliminating all premises @{text \<Gamma>} using the deduction theorem (TODO: cite),
applying GEN to the resulting theorem, instantiating the introduced quantifier to @{text \<beta>}. The resulting
theorem will yield @{text \<open>\<phi>\<^sup>\<beta>\<^sub>\<alpha>\<close>} from @{text \<open>\<Gamma>\<^sup>\<beta>\<^sub>\<alpha>\<close>} by successive applications of modus ponens.

In particular, let @{text \<open>\<psi>\<^sub>1, \<dots>, \<psi>\<^sub>n\<close>} be the list of premises in @{text \<open>\<Gamma>\<close>}, s.t.
@{text \<open>\<psi>\<^sub>1, \<dots>, \<psi>\<^sub>n \<turnstile> \<phi>\<close>}. By the deduction theorem it follows that @{text \<open>\<psi>\<^sub>1, \<dots>, \<psi>\<^bsub>n-1\<^esub> \<turnstile> \<psi>\<^sub>n \<rightarrow> \<phi>\<close>}.
Continuing to apply the deduction theorem, we end up with @{text \<open>\<turnstile> \<psi>\<^sub>1 \<rightarrow> (\<psi>\<^sub>2 \<rightarrow> (\<dots> \<rightarrow> (\<psi>\<^sub>n \<rightarrow> \<phi>)\<dots>)\<close>}.
By assumption @{text \<beta>} is substitutable for @{text \<alpha>} in this theorem, hence be the rule above we
can conclude that: @{text \<open>\<turnstile> \<psi>\<^sub>1\<^sup>\<beta>\<^sub>\<alpha> \<rightarrow> (\<psi>\<^sub>2\<^sup>\<beta>\<^sub>\<alpha> \<rightarrow> (\<dots> \<rightarrow> (\<psi>\<^sub>n\<^sup>\<beta>\<^sub>\<alpha> \<rightarrow> \<phi>\<^sup>\<beta>\<^sub>\<alpha>)\<dots>)\<close>}.
Since all @{text \<open>\<psi>\<^sub>i\<^sup>\<beta>\<^sub>\<alpha>\<close>} are in @{text \<open>\<Gamma>\<^sup>\<beta>\<^sub>\<alpha>\<close>}, it follows that @{text \<open>\<Gamma>\<^sup>\<beta>\<^sub>\<alpha> \<turnstile> \<phi>\<^sup>\<beta>\<^sub>\<alpha>\<close>} by @{text n}
applications of modus ponens.

What remains is the proviso that @{text \<beta>} be substitutable for @{text \<alpha>} in @{text \<phi>} and
in all @{text \<open>\<psi> \<in> \<Gamma>\<close>}. However, note that for every @{text \<phi>} and @{text \<Gamma>} we can choose
alphabetic variants @{text \<phi>'} and @{text \<Gamma>'} that replace all bound occurrences of @{text \<beta>}
with a fresh variable @{text \<gamma>} that does not occur in @{text \<phi>} or in any @{text \<open>\<psi> \<in> \<Gamma>\<close>}.

In the last section we have seen that if @{text \<open>\<Gamma> \<turnstile> \<phi>\<close>}, then @{text \<open>\<Gamma>' \<turnstile> \<phi>'\<close>}. Since 
@{text \<beta>} is trivially substitutable for @{text \<alpha>} in @{text \<open>\<phi>'\<close>} and in all @{text \<open>\<psi> \<in> \<Gamma>'\<close>},
it follows by the previous rule in this section that @{text \<open>\<Gamma>'\<^sup>\<beta>\<^sub>\<alpha> \<turnstile> \<phi>'\<^sup>\<beta>\<^sub>\<alpha>\<close>}. Since Isabelle
collapses alphabetic variants by eliminating concrete variable names with de-Bruijin indices,
this suffices as justification for the schematic generalization of free variables in theorems
and rules in the embedding.

To clarify the last argument, consider the following theorem as example:
\begin{quote}
@{lemma[display] \<open>print_as_theorem \<guillemotleft>\<forall>x ([R]xy \<rightarrow> [R]xy)\<guillemotright>\<close> by (auto intro!: print_as_theoremI GEN "\<rightarrow>I")}
\end{quote}

Isabelle will let us instantiate this theorem using @{term z} in place of @{term y}, i.e.
@{lemma \<open>print_as_theorem \<guillemotleft>\<forall>x ([R]xz \<rightarrow> [R]xz)\<guillemotright>\<close> by (auto intro!: print_as_theoremI GEN "\<rightarrow>I")}
is an instance of above theorem.

However, Isabelle will not allow to @{emph \<open>directly\<close>} instantiate @{term y} to @{term x}, since in 
@{lemma \<open>print_as_theorem \<guillemotleft>\<forall>x ([R]xx \<rightarrow> [R]xx)\<guillemotright>\<close> by (auto intro!: print_as_theoremI GEN "\<rightarrow>I")} (which
also happens to be a theorem, but a distinct one) all occurrences of @{term x} are @{emph \<open>bound\<close>} and
while Isabelle allows to instantiate @{emph \<open>schematic variables\<close>} to free variable,
it does not allow instantiating them to  bound variables.@{footnote \<open>To be precise Isabelle @{emph \<open>will\<close>}
in fact allow this kind of instantiation, but only in situations in which it can automatically rename the bound variable
on its own, as we do manually in the continuation of the example.\<close>}

But since alphabetic variants are collapsed, the following is @{emph \<open>identical\<close>} to the original theorem:
@{lemma \<open>print_as_theorem \<guillemotleft>\<forall>z ([R]zy \<rightarrow> [R]zy)\<guillemotright>\<close> by (auto intro!: print_as_theoremI GEN "\<rightarrow>I")}

In this formulation of the theorem, there is no a naming conflict and we @{emph \<open>can\<close>} instantiate @{term y} to @{term x} to
get @{lemma \<open>print_as_theorem \<guillemotleft>\<forall>z ([R]zx \<rightarrow> [R]zx)\<guillemotright>\<close> by (auto intro!: print_as_theoremI GEN "\<rightarrow>I")}.

Note that this is still an @{emph \<open>instance\<close>} of the original theorem. We just cannot state this
instance without simultaneously renaming the bound variable. Even though, internally, the variable
names are eliminated, concrete variable names, of course, still make a difference when @{emph \<open>parsing\<close>}
inner syntax.

Given this discussion and the meta-rule derived above, we may conclude that the fact that
Isabelle implicitly generalizes free variables to schematic variables remains faithful
to the derivational system of AOT.
\<close>

subsection\<open>Trivial Accessibility Relation for the Modal Logic\<close>text\<open>\label{TrivialAccessibilityRelation}\<close>

text\<open>As already hinted at in section (TODO cite), choosing a trivial accessibility relation (respectively, equivalently,
no accessibility relation at all) is a natural choice for modelling the modal logic of AOT.
In fact, it can be shown that if AOT's actuality operator is modelled using a fixed actual world,
any accessibility relation used for modelling necessity has to be trivial.

To see this, consider the following simple embedding of a general extensional modal logic with actuality
operator, in which the actuality operator is modelled as validity in an arbitrary, but fixed actual world
@{text \<open>w\<^sub>0\<close>}.
\<close>

consts r :: \<open>w \<Rightarrow> w \<Rightarrow> bool\<close>
consts w\<^sub>0 :: w
type_synonym \<o> = \<open>w \<Rightarrow> bool\<close>
definition valid :: \<open>\<o> \<Rightarrow> bool\<close> (\<open>\<Turnstile> _\<close>) where \<open>valid \<equiv> \<lambda> \<phi> . \<forall> w . \<phi> w\<close>
definition impl :: \<open>\<o> \<Rightarrow> \<o> \<Rightarrow> \<o>\<close> (infixl \<open>\<^bold>\<rightarrow>\<close> 8) where \<open>impl \<equiv> \<lambda> \<phi> \<psi> w . \<phi> w \<longrightarrow> \<psi> w\<close>
definition box :: \<open>\<o> \<Rightarrow> \<o>\<close> (\<open>\<^bold>\<box>_\<close> [50] 50) where \<open>box \<equiv> \<lambda> \<phi> w . \<forall> v . r w v \<longrightarrow> \<phi> v\<close>
definition actual :: \<open>\<o> \<Rightarrow> \<o>\<close> (\<open>\<^bold>\<A>_\<close> [50] 50) where \<open>actual \<equiv> \<lambda> \<phi> w . \<phi> w\<^sub>0\<close>
definition equiv :: \<open>\<o> \<Rightarrow> \<o> \<Rightarrow> \<o>\<close> (infixl \<open>\<^bold>\<equiv>\<close> 10) where \<open>equiv \<equiv> \<lambda> \<phi> \<psi> w . \<phi> w \<longleftrightarrow> \<psi> w\<close>

text\<open>
In this simple system, @{command sledgehammer} can immediately prove that all semantic possible
worlds have to be related by the accessibility relation, given the T axiom and one of AOT's axioms
of actuality and necessity:
\<close>

lemma
  assumes \<open>\<And> \<phi> . \<Turnstile> (\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>)\<close>
      and \<open>\<And> \<phi> . \<Turnstile> (\<^bold>\<box>\<phi> \<^bold>\<equiv> \<^bold>\<A>\<^bold>\<box>\<phi>)\<close>
    shows \<open>\<forall> x y . r x y\<close>
  by (metis (mono_tags, hide_lams) assms equiv_def actual_def box_def impl_def valid_def)

text\<open>However, note that this does not mean that a trivial accessibility relation is in fact the only
choice in modelling AOT's modal logic. While the S5 axioms imply that the accessibility relation has
to be an equivalence relation, we conjecture that it is possible to model an actuality operator by
choosing a different actual world for each equivalence class of worlds induced by the accessibility relation.

However, independently of potential philosophical issues one may raise against presuming (even if only
for the purpose of modelling) more than one world that may, depending on modal context, be @{emph \<open>actual\<close>},
an additional practical problem arises: in order to additionally satisfy AOT's axiom for rigid definite descriptions,
the description operator would need to become world-relative: instead of choosing the unique object that
satisfies the matrix of the description in the globally-fixed actual world, the description operator
would have to choose the unique object that satisfies the matrix in the respective actual world of
the equivalence class of possible worlds in which the formula containing the description is evaluated.

Allowing the denotation of an individual term to vary depending on modal context constitutes a
significant complication for the models. Therefore, our current work forgoes further analysis
of this way to extend the basic model structure of AOT. However, such an extension of the models may
constitute an interesting topic for future research. We conjecture that it is possible to construct models
with a different actual world for each equivalence class of worlds, and that doing so could
lead to a means to reproduce the strict distinction between modally-strict and modally-fragile theorems
in AOT as follows: while modally-strict theorems could be modelled as being valid in all possible worlds,
i.e. across all equivalence classes in the accessibility relation, modally-fragile axioms could be
modelled as being valid in a globally-fixed actual world, despite the fact that actuality may choose
a different actual world depending on the modal context. This way, adding a contingent truth to the
modally-fragile derivation system would merely assert that it holds in the globally-fixed actual world,
whereas a modally-strict proof of some statement being @{emph \<open>actually true\<close>} would require that
statement to be true in @{emph \<open>all\<close>} actual worlds. This would constitute a model in which 
@{text \<open>\<turnstile> \<phi>\<close>} would no longer imply @{text \<open>\<turnstile>\<^sub>\<box> \<^bold>\<A>\<phi>\<close>} and, consequently, in which the converse of RN fails,
i.e. @{text \<open>\<turnstile> \<box>\<phi>\<close>} would no longer imply @{text \<open>\<turnstile>\<^sub>\<box> \<phi>\<close>} (while the former merely requires @{text \<open>\<phi>\<close>}
to be valid in all worlds accessible from the globally-fixed actual world, the latter also requires
@{text \<open>\<phi>\<close>} to be true even in worlds inaccessible from the global actual world).
\<close>

subsection\<open>Further Meta-Theorems\<close>

text\<open>
Ideas:
  \<^item> Relation of AOT's existential elimination and @{command obtain}.
  \<^item> Tuples as accurate representation of most of the general n-ary statements justified by the ability to define
    matching tuples in AOT.
  \<^item> More on generalization and e.g. constants?

\<close>

section\<open>Artifactual Theorems\<close>

text\<open>

\<close>

term \<open>\<guillemotleft>\<forall>F ([F]a \<equiv> [F]b) \<rightarrow> [\<lambda>x [R]xa] = [\<lambda>x [R]xb]\<guillemotright>\<close>

section\<open>Discussion\<close>

text\<open>
  \<^item> Sparse documentation of Isabelle/ML's internals.
  \<^item> Danger of hiding the actual reasoning behind too much syntax and custom infrastructure vs. readability and ease of reasoning transfer.
  \<^item> Concessions due to limitations of the type system, type classes, etc.
  \<^item> Challenges due to inability:
    \<^item> Configure root grammar nonterminal.
    \<^item> Hooking into @{command sledgehammer}'s fact selection.
    \<^item> A sub-optimal interface to the internals of theorem specifications and other commands.
  \<^item> Option to define a completely independent Isabelle/Pure based object logic vs. ensured soundness via
    @{command nitpick}-validated constructive models and working tools like @{command sledgehammer}.
\<close>

(*<*)
end
(*>*)