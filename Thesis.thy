(*<*)
theory Thesis
  imports AOT_PLM AOT_RestrictedVariables AOT_PossibleWorlds "HOL-Library.LaTeXsugar" (* "HOL-Library.OptionalSugar" *)
begin
(*>*)


chapter\<open>Introduction\<close>
(*
section\<open>Motivation (Version 1)\<close>
text\<open>
\blockquote{
\textins{Mathematics} may be defined as the subject in which we never know what we are
talking about, nor whether what we are saying is true.
}\footnote{Bertrand Russell, Recent Work on the Principles of Mathematics, The International
Monthly 4 (Jul 1901), 83-101  Repr. as “Mathematics and the Metaphysicians,” in Mysticism
and Logic and Other Essays, London, Longmans, Green, and Co., 1918, pp. 74-96  Page numbers are to ML 1918}


Where does infinity come from? Michael Resnick Keith Devlin

Logic Theorist footnote
\<close>
*)
section\<open>Motivation\<close>

text\<open>
The analysis of foundational formal systems using automated theorem provers is as old
as automated theorem provers themselves: Already in the middle of the last century, Betrand Russell was quick to recognize the potential
of computational methods, when confronted with the \emph{Logic Theorist},@{footnote \<open>A system developed by
Allen Newell and Herbert Simon at Carnegie Mellon and programmed by J. C. Shaw using the vacuum tubes of
the JOHNNIAC computer at the Institute for Advanced Study.\<close>}
 commonly regarded as the first
automated theorem prover, and its ability to prove 38 out of 52 theorems from chapter two of Whitehead and Russell’s
Principia Mathematica, including a proof more elegant than one of
Whitehead and Russell’s own (see~\cite{sep-computational-philosophy}):

\blockquote{I am delighted to know that Principia Mathematica can now be done by machinery.
I wish Whitehead and I had known of this possibility before we both wasted ten years doing it by hand.
I am quite willing to believe that everything in deductive logic can be done by a machine.\footnote{Letter
from Russell to Simon dated 2 November, 1956; preserved in~\cite{Simon1996}, page 208.}}

However, building up a sound reasoning environment from scratch is a
non-trivial task. Consequently, today there is only a limited number of trusted systems that can offer sophisticated
interactive and automated reasoning tools like Coq~\cite{coq}, HOL-Light~\cite{HOLLight} or Isabelle/HOL~\cite{Isabelle}.
Furthermore, most of these systems have at least parts of their logical foundation in common.
For example, they are all based on some variation of functional type theory. This may lead to a bias
in the computational analysis of foundational theories towards
systems that use a similar logical foundation.
\<close>
(*
text\<open>
On the other hand, there is still an ongoing debate about the most suitable foundational
system for mathematics (TODO: cite). While higher-order functional type
theory (HOL) is closely tied to set theory (see \cite{HigherOrderLogicSetTheoryFalseDilemma}, TODO: rethink this point and the citation;
also note e.g. the opposite statement \url{https://kwarc.info/people/frabe/Research/RI_isabelle_10.pdf})
and set theory has long been the prime choice for a common denominator of mathematical disciplines
(TODO: cite), its modern paradox-free axiomatization following Zermelo-Fraenkel is often viewed as
complex and counter-intuitive, respectively lacking in philosophical grounding and justification.

While there is prominent research into alternative foundational approaches (e.g. homotopy type
theory; topos theory; TODO: cite - maybe something else/more examples),  a practical problem for such approaches
and a pragmatic defense of the use of set theory or HOL as foundation is the effort required in building up automated
reasoning systems that are on par with the existing tools that are available for processing theories
grounded in set theory or traditional functional higher-order type theory.
\<close>
*)
text\<open>
The following represents an attempt at overcoming this issue. We utilize the concept of a
@{emph \<open>shallow semantic embedding\<close>} (SSE) with abstraction layers to transfer the merits of
the reasoning environment of Isabelle/HOL to a fundamentally
different foundational system, namely to Abstract Object Theory (AOT).

While it is not a requirement for our proposed general method, we demonstrate that
we can extend Isabelle/HOL by a customized reasoning infrastructure written in Isabelle/ML
that allows for an almost entirely transparent transfer of reasoning in our target logic and
abstracts the syntactic and inferential differences between Isabelle/HOL and AOT, while still
internally using the verified core logic of Isabelle/HOL as semantic backend. This means we
effectively construct a dedicated theorem proving environment for AOT that (1) is immediately guaranteed
to be sound, (2) can be used to explore the safety of axiomatic extensions of the system and (3) allows
for the reuse of the automation infrastructure available for Isabelle/HOL.

While our method can potentially be applied to a multitude of logical systems, AOT
is a particularly well-suited target. On the one hand, it aims to be a foundational metaphysical system
that can serve as the basis for mathematics and thereby stands in the tradition of Russell and
Whitehead's Principia Mathematica, while in fact extending its scope to e.g. linguistics and
the sciences in general (see~\cite{ObjectivesOfObjectTheory}). On the other hand, it is based on logical foundations that significantly differ
from classical functional higher-order type-theory and were even argued to be incompatible (see~\cite{rtt}).
Initial results of our research (see \cite{MScThesis}) demonstrated how our method for formally analyzing
models and semantics of such a system can be beneficial and vital for its soundness (see~\ref{NewParadox}).
During our continued work, we could contribute to the evolution of AOT and
simultaneously arrived at a model structure and semantics that allows to faithfully
reproduce its deductive system in Isabelle/HOL while retaining the existing infrastructure for automated reasoning.\footnote{Note,
however, that our embedding currently only extends to the second-order fragment of AOT.
We briefly discuss the challenges of representing full higher-order object theory in chapter~\ref{HigherOrderAOT}.}

As a prime result, we can show that the construction of Natural Numbers and the derivation
of the Peano-Dedekind postulates, including Mathematical Induction, described in Principia
Logico-Metaphysica (PLM)@{footnote \<open>PLM is a continuously developed online
monograph (see~\cite{PLM-current}) written by Edward Zalta, that contains
the most recent canonical presentation of AOT. This thesis is written relative
to the version dated October 13, 2021, archived in~\cite{PLM-Oct-13-2021}.\<close>} are
verifiably sound. Furthermore, we can suggest the generalization of
an additional axiom required for this construction, that we believe strengthens
the argument that the construction does not require any inherently mathematical axioms.
\<close>
(*
section\<open>Motivation\<close>
text\<open>
Automated reasoning environments are already a vital part of the modern analysis
of mathematics and their importance can only be expected
to increase in the future. A prime example is Hales' proof of the Kepler conjecture that was
only broadly accepted after reconstructing the argument as a formal proof that could be verified
by computerized theorem proving environments (TODO: cite). However, building up a sound reasoning environment from scratch is a
non-trivial task. Consequently, there is only a limited number of trusted systems that can offer sophisticated
interactive and automated reasoning tools like Coq~\cite{coq}, HOL-Light~\cite{HOLLight} or Isabelle/HOL~\cite{Isabelle}.
Furthermore, most of these systems have at least parts of their logical foundation in common,
for example they are all based on some variation of functional type theory.

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
@{emph \<open>shallow semantic embedding\<close>} (SSE) with abstraction layers to transfer the merits of
the sophisticated interactive and automated reasoning system Isabelle/HOL to a fundamentally
different foundational system, namely to Abstract Object Theory (AOT).

While it is not a requirement for our proposed general method, we demonstrate that
we can extend Isabelle/HOL by a customized reasoning infrastructure written in Isabelle/ML
that allows for an almost entirely transparent transfer of reasoning in our target logic and
abstracts the syntactic and inferential differences between Isabelle/HOL and AOT, while still
internally using the verified core logic of Isabelle/HOL as semantic backend. This means we
effectively construct a dedicated theorem proving environment for AOT that (1) is immediately guaranteed
to be sound, (2) can be used to explore the safety of axiomatic extensions to the system and (3) allows
for the reuse of the automation infrastructure available for Isabelle/HOL.

While our method can potentially be applied to a multitude of logical systems, AOT
is a particularly well-suited target. On the one hand, it aims to be a foundational metaphysical system
that can serve as the basis for mathematics and thereby stands in the tradition of Russell and
Whitehead's Principia Mathematica~\cite{PrincipiaMathematica}, while in fact extending its scope to e.g. linguistics and
the sciences in general (TODO: rethink, cite). Furthermore, it attempts to overcome the dilemma noted
by Quine by basing its analysis on an intuitive distinction between \emph{ordinary} and \emph{abstract} objects
and equipping the latter with a very general and yet natural comprehension principle.(TODO: rethink, refer to later sections). On the other hand, it is based on logical foundations that significantly differ
from classical functional higher-order type-theory and were even argued to be incompatible (see~\cite{rtt}).
Initial results of our research (see \cite{MScThesis}) demonstrated how our method for formally analyzing
models and semantics for such a system can be beneficial and vital for its soundness (see~\ref{NewParadox}).
During our continued work we could contribute to the evolution of Abstract Object Theory and
simultaneously arrived at a faithful representation of its model structure, semantics and
deductive system in Isabelle/HOL that can utilize the existing automated reasoning infrastructure.\footnote{Note,
however, that our embedding currently only extends to the second-order fragment of AOT.
We briefly discuss the challenges of representing full higher-order object theory in chapter~\ref{HigherOrderAOT}.}

As a prime result, we can show that the construction of Natural Numbers and the derivation
of the Peano-Dedekind postulates, including Mathematical Induction, described in Principia
Logico-Metaphysica (PLM)@{footnote \<open>PLM is a continuously developed online monograph (see~\cite{PLM-current}) written by Edward Zalta, that contains
the most recent canonical presentation of AOT. This thesis is written relative to the version dated October 13, 2021, archived in~\cite{PLM-Oct-13-2021}.\<close>} are verifiably sound. Furthermore, we can suggest the generalization of
an additional axiom required for this construction, that we believe strengthens
the argument that the construction does not require any inherently mathematical axioms.
\<close>
*)
section\<open>Prior Work\<close>
(*
text\<open>
The analysis of foundational formal systems using automated theorem provers is as old
as automated theorem provers themselves: Already in the middle of the last century, Betrand Russell was quick to recognize the potential
of computational methods, when confronted with the \emph{Logic Theorist}\footnote{A system developed by
Allen Newell and Herbert Simon at Carnegie Mellon and programmed by J. C. Shaw using the vacuum tubes of
the JOHNNIAC computer at the Institute for Advanced Study; see~\cite{sep-computational-philosophy}.}, commonly regarded as the first
automated theorem prover, and its ability to prove 38 out of 52 theorems from chapter two of Whitehead and Russell’s
Principia Mathematica, including a proof more elegant than one of
Whitehead and Russell’s own (see~\cite{sep-computational-philosophy}):

\blockquote{I am delighted to know that Principia Mathematica can now be done by machinery.
I wish Whitehead and I had known of this possibility before we both wasted ten years doing it by hand.
I am quite willing to believe that everything in deductive logic can be done by a machine.\footnote{Letter
from Russell to Simon dated 2 November, 1956; preserved in~\cite{Simon1996}, page 208.}}

Since then there has been significant progress both in the development of automated theorem provers
in general and in the application of computational methods to metaphysical questions and foundational
logical theories in particular. Some of the more recent developments in this area are outlined in the following sections.
\<close>
*)
text\<open>
Since the times of Russell and the Logic Theorist, there has been significant progress both in the development of automated theorem provers
in general and in the application of computational methods to metaphysical questions and foundational
logical theories in particular. Some of the more recent developments in this area are outlined in the following sections.
\<close>
subsection\<open>Prior Computational Analysis of Abstract Object Theory\<close>

text\<open>

The computational analysis of AOT was pioneered by Fitelson and Zalta in
\cite{FitelsonZalta}. They used the first-order system Prover9 (see~\cite{prover9-mace4}) for their work and were able to 
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
its full deductive system (see also~\cite{CrossFertilization}).
\<close>
subsection\<open>Prior Work involving Shallow Semantic Embeddings\<close>text\<open>\label{PriorSSEs}\<close>

text\<open>
Independently, the emergence of sophisticated higher-order reasoning environments like Isabelle/HOL
allows for a different approach, namely the analysis of arguments and theories directly in higher-order
logic by constructing Shallow Semantic Embeddings (SSEs) (see~\cite{UniversalReasoning}). In contrast to
a @{emph \<open>deep embedding\<close>} which defines the syntax of a target system using an inductive data
structure and evaluates statements semantically by recursively traversing this data structure,
a @{emph \<open>shallow\<close>} semantic embedding instead provides a syntactic translation from the target logic
to the meta-logic. This is done by reusing as much of the infrastructure of the meta-logic as possible,
while @{emph \<open>defining\<close>} the syntactic elements of the target logic that are not part of
the meta-logic by means of a representation of their semantics. Since sets have a natural
representation in higher-order logic, this approach works well for any logical system that
has a semantics defined in terms of sets. The approach of shallow semantic embeddings is discussed in
more detail in chapter~\ref{SSEs}.

For example, Benzm{\"u}ller et al. provide an extensive analysis of quantified modal logic using SSEs
by means of embedding modal operators based on their Kripke semantics
\cite{ModalLogics, ModalLogicCube, HOMLAutomationAndApplications}. This allowed for an
analysis of G\"odel's ontological argument in second-order S5 modal logic and weaker logics
such as KB (see~\cite{GoedelGod}), followed by a range of studies of similar ontological
arguments (see e.g.~\cite{LeibnizOntologicalArgument}).

Another more recent example of the application of SSEs is the LogiKEy framework for
ethical reasoning, normative theories and deontic logics (see~\cite{LogiKEy} and~\cite{LogiKEyData}).
The goal of LogiKEy is to develop the means for the control and governance of intelligent
autonomous systems. The framework is based on a set of SSEs of different denotic logics,
combinations thereof, as well as ethico-legal domain theories in higher-order logic
with an implementation in Isabelle/HOL.

The advantage of these studies using SSEs compared to the earlier use of first-order systems is that arguments
can be represented in their native syntax and are thereby readable and maintainable, while the theorem
proving environment is capable of automatically transforming statements into a suitable first-order
representation on the fly to allow first-order theorem provers like E (see~\cite{EProver}) or SPASS (see~\cite{SPASS}) to perform
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
(see~\cite{zalta1999}) provide an important building block for constructing models of AOT in HOL, no full
set-theoretic model of object theory had been constructed. In \cite{MScThesis} we extended the
existing Aczel models to a richer model structure that was capable of approximating the validity
of statements of the at the time most recent formulation of the second-order fragment of AOT in Principia Logico-Metaphysica.@{footnote \<open>The
respective version of PLM is archived in~\cite{PLM-Oct-28-2016}.\<close>}
Furthermore, we introduced the new concept of @{emph \<open>abstraction layers\<close>}. An abstraction layer consists
of a derivation of the axioms and deduction rules of a target system from a given semantics that is
then considered as ground truth while "forgetting" the underlying semantic structure, i.e. the
reasoning system is prevented from using the semantics for proofs, but is instead configured to solely
rely on the derived axioms and deduction rules.
Abstraction layers turned out to be a helpful means for reasoning within a target theory without
the danger of deriving artifactual theorems (see~\ref{ArtifactualTheorems}), while simultaneously allowing to maintain a flexible
semantic backend that can be used to explore axiomatic extensions and variations of the target theory.

A major initial result of this project, reported in~\cite{ReviewPaper}, was the discovery of an oversight
in the formulation of AOT that allowed for the reintroduction of a previously known paradox into the system. While multiple quick
fixes to restore the consistency of AOT were immediately available, in the aftermath of this result
AOT was significantly reworked and improved. The result triggered an extensive debate
about the foundations of AOT which culminated in the extension of the free logic of AOT to relations,
while previously it was restricted to individual terms only.
This evolution of AOT was accompanied by a continuous further development of its
embedding in Isabelle/HOL. This mutually beneficial mode of work was described in~\cite{CrossFertilization}
and resulted in a now stabilized and improved formulation of AOT and a
matching embedding of its second-order fragment. The details of this process and its results are
the main subject of this thesis.
\newpage
\<close>

section\<open>Contributions and Structure of the Thesis\<close>text\<open>\label{Structure}\<close>

text\<open>
In the following, we first provide a more detailed description of Shallow Semantic Embeddings (chapter~\ref{SSEs}) and
a brief introduction to Abstract Object Theory (chapter~\ref{AOT}).
Based on that, chapter~\ref{SSEofAOT} describes
the constructed embedding of the second-order fragment of AOT (as presented in PLM~\cite{PLM-Oct-13-2021}) in Isabelle/HOL.

In the process we highlight the contributions of the embedding to AOT on the one hand and
the techniques developed for its implementation on the other hand.

In chapter~\ref{NaturalNumbers} we present our results on PLM's construction of natural numbers 
and discuss an extension of AOT with a more general comprehension
principle for relations among abstract objects. We also discuss some interesting
variations of the construction that may be adopted by PLM in the future.

Finally, in chapter~\ref{HigherOrderAOT} we briefly discuss the issue of applying our method to
the full higher-order type-theoretic version of AOT.

Our primary goals are to show that:
  \<^item> SSEs can not only be used for case studies and the analysis of isolated arguments,
    but also for implementing the axioms and full deductive system of entire
    logical theories.
  \<^item> The above is even feasible for a challenging target like AOT, which itself has
    the ambition to be a foundational framework and is based on significantly different
    logical foundations compared to our meta-logic HOL.
  \<^item> We can reproduce the full deductive system of AOT in readable and usable form while
    preserving Isabelle's automation mechanisms. Thereby, we can effectively
    construct a dedicated automated theorem proving environment for AOT.
  \<^item> Using our method we could significantly contribute to our target theory.
  \<^item> We can demonstrate the extent of our target theory and the practical feasibility
    of reproducing complex reasoning in it by reproducing and validating its analysis
    of natural numbers.
  \<^item> In the process, we can provide valuable theoretical insights into, and analyze extensions and variations of, the
    construction of the natural numbers.
\newpage
\<close>

section\<open>Verified Document Generation and Conventions\<close>text\<open>\label{Conventions}\<close>

text\<open>
This thesis is generated using Isabelle's document preparation system (see~\cite{IsabelleSystemManual}).
In particular, all formal statements cited in the thesis are renderings of verified theorems
in the embedding, unless specifically stated otherwise and marked with vertical bars
at the page margins.@{footnote \<open>With the exception of chapter~\ref{HigherOrderAOT} which
is not written relative to an embedding in Isabelle and omits the marking at the page margins.\<close>}

The appendix contains a rendering of the raw theory files of the embedding including all proofs. The implementation
currently consists of around 25.000 lines of Isabelle proof text.@{footnote \<open>Around 20.000 lines are reasoning in the abstraction layer, i.e.
reasoning in the logic of the target theory, while the remainder builds up the required model structure and semantics as well as
the syntax representation of AOT.\<close>} While Isabelle allows producing latex code for raw theories directly,@{footnote \<open>This mechanism is used
for raw theory content that is inlined in the main thesis, but not for the appendix.\<close>} semantic information
(e.g. color-coding of free vs. bound variables) is lost in the process, which reduces the
readability. For that reason, we devised a custom theory presentation
system similar to Isabelle's HTML theory presentation that
uses PIDE markup information (see~\cite{PIDE}) to provide a color-coded rendering of the
theory files equipped with hyperlinks for cross-references.@{footnote \<open>Therefore, we recommend reading this
thesis in digital form.\<close>}

Whenever a theorem in the appendix refers to a specific item number in PLM, the
corresponding item number can be found in parentheses at the right page margin. While
we will sometimes refer to item numbers in PLM directly, we will usually refer to
the implementation in the appendix by section and line number and rely on the statement
in the appendix being annotated with the item number of the corresponding statement in PLM.
In particular, the thesis is written relative to the version of PLM dated October 13, 2021 (see~\cite{PLM-Oct-13-2021}).

While a certain degree of familiarity with the reasoning environment of Isabelle/HOL might be helpful,
the fact that reasoning in Isabelle/HOL is designed to be natural and intelligible should allow
following the constructions without extensive prior knowledge of Isabelle/HOL. An introduction
to reasoning in Isabelle/HOL can be found in~\cite{IsabelleTutorial}. The implementation
is written relative to the Isabelle2021-1 (December 2021) release of Isabelle.
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
The deep embedding consists of a (usually recursive) algebraic datatype that captures the syntactic elements of
the language to be embedded. This representation of the syntax is then given a semantics by means of an evaluation function
that traverses this algebraic datatype.@{footnote \<open>In the setting of logical theories this evaluation
function would usually depend on interpretations and assignment functions. However, in our
simple example this is not necessary, since the simple language of expressions neither involves constants nor variables (respectively since
literals have trivial interpretations).\<close>}
A shallow embedding on the other hand, represents the syntactic elements of a target language directly
in their semantic domain. In our example, the semantic domain of expressions is the integers. On this domain,
operations are then @{emph \<open>defined\<close>} directly by means of their semantics:
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
@{thm[show_question_marks = false, names_short = false] Deep_Shallow_Addition}.
So semantic evaluation is implicit in the shallow embedding.
On the other hand there are also differences between the two representations. For example, in the
deep embedding adding @{term x} to @{term y} results in an expression that is different from the expression of adding
 @{term y} to  @{term x} for distinct  @{term x} and  @{term y}, even though they are equivalent under evaluation:

@{thm[show_question_marks = false, names_short = false, display = true]
  Deep.CommutativeAdditionNonIdentity Deep.CommutativeAdditionEquivalent}

In contrast, commuted additions are identical in the shallow embedding:

@{thm[show_question_marks = false, names_short = false, display = true] Shallow.CommutativeAdditionIdentity}

In fact, the shallow embedding can be thought of as a @{emph \<open>quotient\<close>} of the deep embedding under
semantic evaluation.

While there are several advantages and disadvantages of using shallow vs. deep embeddings for
Domain-Specific languages, we forgo a detailed discussion of them here and
focus on shallow embeddings of logical theories in the next sections.
\<close>

section\<open>SSEs as Universal Reasoning Tools\<close>

text\<open>

In \cite{UniversalReasoning}, Benzm\"uller develops the idea of using @{emph \<open>Shallow Semantic Embeddings\<close>} (SSEs)
in classical higher-order logics (HOL) as a means for universal reasoning.

He notes that while already Leibniz envisioned a @{emph \<open>characteristica universalis\<close>}, a most
universal formal language in which all knowledge (and all arguments) about the world
and the sciences can be encoded, in practice, today we rather find a @{emph \<open>rich and
heterogenous zoo of different logical systems\<close>}.

A solution to this dilemma is the use of a universal @{emph \<open>meta\<close>}-logic,
in which a multitude of logic formalisms can be @{emph \<open>embedded\<close>}.

While there are multiple such unifying approaches, for example using algebratic
logic or category theory as framework,  Benzm\"uller defends
the use of SSEs in HOL for pragmatic reasons:

  \<^item> For HOL there are sophisticated automation tools readily available that have been
developed for several decades like e.g. Isabelle/HOL.
  \<^item> Since HOL itself is very expressive, an embedding into HOL can often be achieved
    using simple techniques and can result in an elegant and concise representation of
    the target logic.
  \<^item> Using a @{emph \<open>shallow\<close>} embedding approach, the technical overhead of the
    translation can be kept minimal, which enables the reuse of the automation
    infrastructure available for the meta-logic.

While we already mentioned a variety of results that were achieved using this general
method (see section~\ref{PriorSSEs}), in the following we will demonstrate the
process of building such an SSE at a simple example.
\<close>

section\<open>SSE of Quantified Higher-Order Modal Logic\<close>text\<open>\label{SimpleS5}\<close>
text\<open>

An example of a non-classical logic that is used prominently in philosophical arguments is Quantified Higher-Order
Modal Logic in various different axiomatizations. While there have been extensive studies of
modal logics using SSEs in Isabelle/HOL (see section~\ref{PriorSSEs}), we restrict ourselves
to the discussion of a simple embedding of S5 modal logic to further illustrate the general
concept of SSEs.
\<close>

(*<*)
locale SimpleS5 = AOT_no_meta_syntax
begin
(*>*)

text\<open>
A natural semantic basis for SSEs of any modal logic is its Kripke-semantics (see~\cite{KripkeSemantics}).
In general, a Kripke frame consists of a set of possible worlds and a binary relation on these worlds
called @{emph \<open>accessibility relation\<close>}. For S5 there are two versions of semantics, one in which the
accessibility relation is an equivalence relation and one in which there is no accessibility relation at
all (see~\cite{FittingS5}). For our purpose the simpler
model suffices.@{footnote \<open>We will later argue that this is also a natural choice for the particular modal
logic of Abstract Object Theory due to its additional actuality operator and rigid definite descriptions,
see section~\ref{TrivialAccessibilityRelation}.\<close>}

For possible worlds we can introduce a primitive type @{text w} in Isabelle/HOL.\footnote{A
set-theoretic model of HOL would represent this type with a non-empty set of objects that
may serve as denotation for objects of type @{text w}.}
\<close>

typedecl w

text\<open>
A Kripke model further involves a relation between possible worlds and modal formulas that is
usually read as a formula @{emph \<open>being satisfied at\<close>} a possible world. So the semantic domain of
propositions is the boolean-valued functions acting on (or, equivalently, the sets of) possible worlds.
In an SSE we use the semantic domains as types for the object-level terms themselves,@{footnote \<open>Note that it is also possible to model restrictions on the evaluation domains
explicitly, as recently demonstrated in~\cite{PublicAnnouncementLogic}.\<close>} so we can introduce
a type @{text \<o>} of propositions as synonym of the type of functions mapping possible worlds (of type @{typ w})
to booleans (type @{typ bool}). This way the proposition can, as a function, be applied to a possible
world, yielding @{term True}, if the proposition is satisfied at that world or @{term False} otherwise.@{footnote \<open>Note
that this choice of a representation of propositions commits us to a modal logic, in which
necessary equivalence implies identity. We will later discuss how we can construct a hyperintensional logic instead.\<close>}
\<close>

type_synonym \<o> = \<open>w \<Rightarrow> bool\<close>

text\<open>
A proposition is @{emph \<open>valid\<close>} in case it is satisfied in all worlds.@{footnote \<open>The specification
in parentheses after the type of the defined constant, @{typ \<open>\<o> \<Rightarrow> bool\<close>}, is @{emph \<open>mixfix notation\<close>} used to introduce
the symbol @{text \<Turnstile>} as syntax for the introduced constant @{text valid} with the specified precedence. The means to
introduce custom syntax in Isabelle/HOL are discussed in more detail in section~\ref{SSESyntax}.\<close>}
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

text\<open>The proofs of the axioms are automatically found by @{command sledgehammer}, Isabelle/HOL's
main tool for automation.\footnote{@{command sledgehammer} is discussed in more detail in the following section.}

So far we have constructed an embedding of propositional S5 modal logic using what is commonly
known as \emph{Standard Translation} of modal logic (see~\cite{ModalLogicSemanticPerspective}). However it is straightforward
to enrich this embedding with quantification.@{footnote \<open>See also the work by
Benzm{\"u}ller et al. cited in section~\ref{PriorSSEs}.\<close>}
\<close>

definition forall :: \<open>('a \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close> (binder \<open>\<^bold>\<forall>\<close> 110) where
  \<open>\<^bold>\<forall> x . \<phi> x \<equiv> \<lambda>w . \<forall> x . \<phi> x w\<close>
definition exists :: \<open>('a \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close> (binder \<open>\<^bold>\<exists>\<close> 110) where
  \<open>\<^bold>\<exists> x . \<phi> x \<equiv> \<lambda>w . \<exists> x . \<phi> x w\<close>

text\<open>Note that we didn't introduce any particular type for individuals, but stated
polymorphic definitions relative to a type variable @{typ 'a}. This way the same quantifier
can be used for propositions themselves, any desired type for individuals or even properties of
any order.@{footnote \<open>Note that this construction implies a shared domains for objects
across possible worlds. An additional meta-logical predicate for @{emph \<open>logical existence
in a possible world\<close>} can be added to model varying domains.\<close>}

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
not the primary concern, but rather derivability from the formal system.@{footnote \<open>Even if
the target theory is provably complete with respect to the semantics used for constructing
the embedding, i.e. semantic validity implies derivability, we still want to know which
axioms and rules can be used to construct a concrete derivation.\<close>}

Fortunately, it is possible to restrict Isabelle's automated reasoning tools like
@{command sledgehammer}, s.t. they may not unfold semantic definitions. If this is done
at larger scale and in a reliable manner for the purpose of analyzing derivability in
a given deductive system, we say that we introduce @{emph \<open>abstraction layers\<close>} to the SSE.
\<close>

(*<*)
end
(*>*)

section\<open>SSEs with Abstraction Layers\<close>text\<open>\label{SSEsWithAbstractionLayers}\<close>

text\<open>The concept of enriching traditional SSEs with abstraction layers was first introduced
in \cite{MScThesis}. The goal is to be able to use the automated reasoning tools provided
by a system like Isabelle/HOL not merely to analyze semantic validity of statements in the
embedded theory, but to reliably determine the derivability of a statement from the deductive
system of the theory itself.

An abstraction layer is simply constructed by proving that the axioms and deduction
rules of a target logic are semantically valid in the embedding, after which they
are considered as ground truths: all subsequent reasoning in the abstraction layer
is restricted to only rely on the derived axioms and rules and may no longer refer
to the underlying semantics. Consequently, only proper theorems of the target logic
are derivable in the abstraction layer.@{footnote \<open>Note, however, that this relies
on the additional assumption that meta-logical inferences based on the derived axioms and rules
correspond to derivations in the target logic, as mentioned in the end of this section.\<close>}

So while abstraction layers are conceptually rather simple, an interesting technical
question is how the automation capabilities of the meta-logic can be preserved and reliably restricted
to respect the imposed restrictions.

While Isabelle provides its own mechanisms for abstract reasoning like type @{command class}es, @{command locale}s and
@{command specification}s, those are not primarily designed for this exact purpose and come with
limitations that can make them unsuitable to achieve that purpose on their own,
as described in more detail in the following section.

As mentioned in the last section, the main tool for automated reasoning in Isabelle/HOL in question is @{command sledgehammer} (see~\cite{Sledgehammer}).
@{command sledgehammer} can be invoked during any proof and will try to automatically find a proof for
the current proof goal. To that end, simply speaking,@{footnote \<open>For a precise description of the full details of the process
refer to~\cite{Sledgehammer}.\<close>} it collects all theorems and definitions derived in the current @{command theory} context
together with all local assumptions (collectively referred to as @{emph \<open>facts\<close>}) and processes the resulting set of facts heuristically to find
a subset of relevant facts. It then encodes the problem of deriving the current goal from the chosen
facts in a format that can be consumed by external theorem provers like
E~\cite{EProver}, SPASS~\cite{SPASS}, verit~\cite{veriT} or Z3~\cite{Z3}.
This may, for example, involve a translation from higher-order problems
to first-order problems. If one of the invoked provers can prove the current goal, @{command sledgehammer}
tries to reconstruct a short proof using Isabelle's native proving methods (which operate
directly on Isabelle's trusted reasoning core) that can be directly inserted to prove the current goal.@{footnote \<open>Furthermore,
for provers like veriT and Z3, @{emph \<open>proof reconstruction\<close>} using the @{method smt} tactic is available, i.e. they provide
proofs that can (sometimes) be directly replayed relative to Isabelle's trusted reasoning core. See~\cite{veriTIsabelle} and~\cite{Z3Isabelle}.\<close>}

The relevant part of the process to consider for the purpose of constructing an abstraction layer is
the initial selection of facts from the theory context.
We do not want @{command sledgehammer} to use the equational theorems that unfold our semantic definitions,
but instead derive the goals from only the axioms and specific derivational rules that correspond
to the rules of the deductive system of the embedded theory.
@{command sledgehammer} allows us to provide some guidance in its choice. It is possible
to (1) indicate that a certain set of facts is likely to be helpful in the proof (using @{text \<open>add:\<close>}),
(2) prevent it from using certain facts (either using @{text \<open>del:\<close>} or by marking facts with
the special attribute @{attribute no_atp}) or (3) to provide it with a specific set of facts to use
directly without taking any other facts into account.

Conceptually, option (3) is the best fit for the purpose of abstraction layers and was used in
\cite{MScThesis}. However, @{command sledgehammer} will no longer employ its heuristics and machine
learning algorithms to filter the provided facts for relevance, but will directly use
the provided set. Consequently, the proving power and therefore the usefulness of
@{command sledgehammer} is significantly diminished, especially for larger theories.

In our current implementation, we therefore use option (2) instead. However, this comes with
some challenges. While the equational theorems introduced by simple @{command definition}s can
easily be collected and marked, other more advanced constructions in Isabelle like type definitions
or @{command lift_definition}s (see~\cite{LiftingTransfer}) introduce several theorems implicitly. While
it is still possible to collect these theorems manually, the process is cumbersome and error-prone.

On the other hand, it is not possible to simply exclude @{emph \<open>all\<close>} theorems that were derived
up to a certain point, since this includes the theorems of Isabelle's @{theory Main} theory, i.e.
- among others - the construction of classical higher-order logic on top of Isabelle's more basic @{theory Pure}
logic. This includes theorems @{command sledgehammer} relies on and disbarring them will leave it
non-functional (conceptually, such theorems can be thought of as meta-theorems about
derivations in our context).

The solution used in the current embedding of AOT is the use of 
Isabelle's internal ML API to automatically collect theorems to be added to an exclusion
list. For convenience, a new command @{command AOT_sledgehammer} is introduced that internally
configures @{command sledgehammer} to use the desired set of theorems and then passes the current
proof state to it.@{footnote \<open>Alternatively, we allow configuring @{command sledgehammer} itself to
only use the restricted set of theorems.\<close>} With this method we can achieve significantly better proof
automation than~\cite{MScThesis}.

It is important to note that abstraction layers still rely on the implicit assumption
that meta-logical reasoning about derivations in the target logic is faithfully represented
by the meta-logical inferences in Isabelle enabled by the constructed deduction rules.

In particular, the deductive system of our target theory is implemented as
meta-rules in Isabelle's Pure logic, while the used automation mechanisms additionally
rely on the logic of Isabelle/HOL. Consequently, we need to convince ourselves that resulting
inferences are reproducible in the target system and, conversely, that
derivations in our target system are exhaustively captured by the rules of our abstraction
layer. For our embedding of AOT we sketch such an argument in section~\ref{PureVsAOT}.
\<close>

section\<open>Isabelle's Native Abstraction Mechanisms\<close>text\<open>\label{NativeAbstractionMechanisms}\<close>

text\<open>
While abstraction layers provide a means to insulate reasoning in our embedding from artifactual theorems (i.e. theorems
that are merely semantically valid but not derivable in the target theory; see also~\ref{ArtifactualTheorems}), we additionally
use Isabelle's native abstraction mechanisms. This serves to establish an additional intermediate
abstraction between the concrete model construction and the derivation of the axioms and deductive
system of the target theory, which helps in exploring changes to the model structure without
having to adjust the full derivation of the abstraction layer.
\<close>
subsection\<open>Specifications\<close>text\<open>\label{Specifications}\<close>
text\<open>
For example, we extensively use @{command specification}s (see~\S11.4 in~\cite{IsarRef}).
A @{command specification} is used to assert statements about previously uninterpreted constants.
The @{command specification} command opens a proof context
that requires the user to show that there exists a concrete instantiation for the given constants,
for which the desired statements hold. Internally it then uses Isabelle's Hilbert-Epsilon-operator
@{term \<open>SOME x. \<phi> x\<close>} to augment the given constants with a concrete definition. We will discuss
the technical details of this mechanism in section~\ref{HilbertEpsilon}. As a consequence,
a model of the meta-logic may choose any denotation for the given constants that satisfies the
specification, while the existence of such a denotation is guaranteed by the provided witness. However,
depending on the use case of this mechanism, care has to be taken to ensure that there actually
are non-trivial choices beyond the provided witness.

To illustrate this issue, we showcase the construction of a (hyper-)intensional conjunction in which
@{term \<open>p \<and> q\<close>} implies both @{term p} and @{term q} and vice-versa, but it does not hold
that @{term \<open>(p \<and> q) = (q \<and> p)\<close>}.
We first show a construction that will fail due to the choice of a representation type that
implies extensionality:
\<close>

typedef \<o>\<^sub>1 = \<open>UNIV::bool set\<close>.. \<comment> \<open>Introduce an abstract type of propositions @{typ \<o>\<^sub>1} with the universal set
of booleans (i.e. @{term \<open>{True, False}\<close>}) as representation set.@{footnote \<open>For every type definition using
an explicit representation set (@{command typedef}), we need to prove that the set is non-empty. In the case of the universal
set of another type, this proof is trivial, as indicated by the two dots.\<close>}\<close>
definition valid_\<o>\<^sub>1 :: \<open>\<o>\<^sub>1 \<Rightarrow> bool\<close> where
  \<open>valid_\<o>\<^sub>1 p \<equiv> Rep_\<o>\<^sub>1 p\<close> \<comment> \<open>Validity is simply given by the boolean representing the proposition.@{footnote \<open>For any @{command typedef}, Isabelle intoduces
     constants prefixed with @{text Abs_} and @{text Rep_}, mapping the representation type to the
     defined abstract type and vice-versa.\<close>}\<close>

text \<open>We introduce an uninterpreted constant for conjunctions with infix syntax.\<close>
consts \<o>\<^sub>1_conj :: \<open>\<o>\<^sub>1 \<Rightarrow> \<o>\<^sub>1 \<Rightarrow> \<o>\<^sub>1\<close> (infixl \<open>\<^bold>\<and>\<close> 100)

specification (\<o>\<^sub>1_conj) \<comment> \<open>We specify our conjunction by introduction and elimination rules.\<close>
  \<o>\<^sub>1_conjE1: \<open>valid_\<o>\<^sub>1 (p \<^bold>\<and> q) \<Longrightarrow> valid_\<o>\<^sub>1 p\<close>
  \<o>\<^sub>1_conjE2: \<open>valid_\<o>\<^sub>1 (p \<^bold>\<and> q) \<Longrightarrow> valid_\<o>\<^sub>1 q\<close>
  \<o>\<^sub>1_conjI: \<open>valid_\<o>\<^sub>1 p \<Longrightarrow> valid_\<o>\<^sub>1 q \<Longrightarrow> valid_\<o>\<^sub>1 (p \<^bold>\<and> q)\<close>
text\<open>We need to prove that there is a term satisfying the above specification. The natural choice is
     the lifted conjunction on the booleans.\<close>
  by (rule exI[where x=\<open>\<lambda> p q . Abs_\<o>\<^sub>1 (Rep_\<o>\<^sub>1 p \<and> Rep_\<o>\<^sub>1 q)\<close>])
     (auto simp: Abs_\<o>\<^sub>1_inverse valid_\<o>\<^sub>1_def)

text\<open>However, even though the identity of commuted conjunctions is not part of the @{command specification},
     it is @{emph \<open>still\<close>} derivable.@{footnote \<open>Note that if we constructed abstraction layers
     as discussed in the last section, @{command sledgehammer} would be prevented from considering the implicit
     theorems introduced by the type definition of @{type \<o>\<^sub>1} (which relate the type to its representation type)
     and, therefore, would not be able to prove this theorem.\<close>}\<close>
lemma \<open>p \<^bold>\<and> q = q \<^bold>\<and> p\<close>
  by (metis Rep_\<o>\<^sub>1_inject \<o>\<^sub>1_conjE1 \<o>\<^sub>1_conjE2 valid_\<o>\<^sub>1_def)

text\<open>The reason is that there is only one choice for a conjunction operator on the booleans
that satisfies our specification and this choice is commutative. We can in fact prove
that our conjunction has to be identical to the witness we provided:
\<close>

lemma \<open>(\<^bold>\<and>) = (\<lambda>p q . Abs_\<o>\<^sub>1 (Rep_\<o>\<^sub>1 p \<and> Rep_\<o>\<^sub>1 q))\<close>
  by (metis Abs_\<o>\<^sub>1_inject Abs_\<o>\<^sub>1_inverse UNIV_I \<o>\<^sub>1_conjE1 \<o>\<^sub>1_conjE2 \<o>\<^sub>1_conjI
            type_copy_obj_one_point_absE type_definition_\<o>\<^sub>1 valid_\<o>\<^sub>1_def)
(*<*)
no_notation \<o>\<^sub>1_conj (infixl \<open>\<^bold>\<and>\<close> 100)
(*>*)

text\<open>
In order to avoid this issue, we cannot simply rely on the @{command specification} command, but
also have to take care that the @{emph \<open>types\<close>} of the specified constants can actually deliver the desired degree
of intensionality. In our example, we can introduce an abstract @{emph \<open>intensional type\<close>} for propositons
that merely has a boolean @{emph \<open>extension\<close>}. First we introduce an abstract type:
\<close>

typedecl \<o>\<^sub>2 \<comment> \<open>Introduce an abstract type for propositions.\<close>

text\<open>
Thus far, a model of HOL satisfying our theory may choose any non-empty set as
representation set for objects of type @{typ \<o>\<^sub>2}. To arrive at a meaningful type
of propositions, we axiomatically introduce a surjective extension function mapping
the abstract propositions to their boolean extension. The surjectivity of the extension function
excludes degenerate models in which there is only one proposition.@{footnote \<open>Note, that we can also construct
an equivalent type without a meta-logical axiom: we can (1) introduce an uninterpreted constant
that defines a set of products (or, alternatively, sums) of an additional uninterpreted type of intensions and the type of
extensions (@{typ bool} in the example), (2) specify that this set is both non-empty and large enough to allow
for a surjective function to the extensions (the universal set of such products will be a witness for this specification) and
(3) use this set as representation set for our intensional type. The existence of a surjective extension function will become
derivable from the specification. However, we found that the model-finding tool @{command nitpick}
works better with the equivalent axiomatic introduction of an extension function on an abstract type.\<close>}\<close>

axiomatization \<o>\<^sub>2_ext :: \<open>\<o>\<^sub>2 \<Rightarrow> bool\<close> where
  \<o>\<^sub>2_ext_surj: \<open>surj \<o>\<^sub>2_ext\<close>

definition valid_\<o>\<^sub>2 :: \<open>\<o>\<^sub>2 \<Rightarrow> bool\<close> where
  \<open>valid_\<o>\<^sub>2 p \<equiv> \<o>\<^sub>2_ext p\<close> \<comment> \<open>Validity of a proposition is given by its boolean extension.\<close>

consts \<o>\<^sub>2_conj :: \<open>\<o>\<^sub>2 \<Rightarrow> \<o>\<^sub>2 \<Rightarrow> \<o>\<^sub>2\<close> (infixl \<open>\<^bold>\<and>\<close> 100)

specification (\<o>\<^sub>2_conj) \<comment> \<open>We again specify our conjunction by introduction and elimination rules.\<close>
  \<o>\<^sub>2_conjE1: \<open>valid_\<o>\<^sub>2 (p \<^bold>\<and> q) \<Longrightarrow> valid_\<o>\<^sub>2 p\<close>
  \<o>\<^sub>2_conjE2: \<open>valid_\<o>\<^sub>2 (p \<^bold>\<and> q) \<Longrightarrow> valid_\<o>\<^sub>2 q\<close>
  \<o>\<^sub>2_conjI: \<open>valid_\<o>\<^sub>2 p \<Longrightarrow> valid_\<o>\<^sub>2 q \<Longrightarrow> valid_\<o>\<^sub>2 (p \<^bold>\<and> q)\<close>
  text\<open>We again need to prove the existence of a term satisfying the given specification.
       Since our extension function is surjective, a natural suitable witness can be
       constructed using the inverse of the extension function.\<close>
  by (rule exI[where x=\<open>\<lambda> p q . (inv \<o>\<^sub>2_ext) (\<o>\<^sub>2_ext p \<and> \<o>\<^sub>2_ext q)\<close>])
     (simp add: \<o>\<^sub>2_ext_surj f_inv_into_f valid_\<o>\<^sub>2_def)

text\<open>Now as a consequence of our specification, our conjunction is still commutative @{emph \<open>under validity\<close>}:\<close>

lemma \<open>valid_\<o>\<^sub>2 (p \<^bold>\<and> q) = valid_\<o>\<^sub>2 (q \<^bold>\<and> p)\<close>
text\<open>Note that the proof (found by @{command sledgehammer}) now solely relies on the properties of
     @{const \<o>\<^sub>2_conj} given in our specification:\<close>
  using \<o>\<^sub>2_conjE1 \<o>\<^sub>2_conjE2 \<o>\<^sub>2_conjI by blast

text\<open>However, commuted conjunctions are no longer identical. The model-finding tool @{command nitpick} (see~\cite{Nitpick})
     can provide a counterexample by constructing a model for @{typ \<o>\<^sub>2} that has more than two members.\<close>

lemma \<open>(p \<^bold>\<and> q) = (q \<^bold>\<and> p)\<close>
  nitpick[user_axioms, expect = genuine, show_consts, atoms \<o>\<^sub>2 = p q r, format = 2]
  oops \<comment> \<open>Abort proof and discard the lemma.\<close> (* Note that this additionally satisfies the axioms of the imported theory AOT_PLM *)

text\<open>The model given by @{command nitpick}@{footnote \<open>The precise model may vary for different versions of Isabelle.\<close>}
     chooses a three-element set for type @{typ \<o>\<^sub>2}. We chose @{text p}, @{text q} and @{text r} as names for these elements.
     @{const \<o>\<^sub>2_ext} is modelled as @{text \<open>(p := True, q := False, r := False)\<close>} and
     @{const \<o>\<^sub>2_conj} as @{text \<open>((p, p) := p, (p, q) := q, (p, r) := r, (q, p) := r, (q, q) := q, (q, r) := r, (r, p) := r, (r, q) := r,
     (r, r) := r)\<close>}.

     This is indeed one of the minimal (non-degenerate)@{footnote \<open>The specification for conjunctions alone
     can also be satisfied in degenerate models, in which either all propositions are true or all propositions
     are false, i.e. in particular for models with only one proposition. However, we excluded such degenerate models
     by requiring a surjective extension function, which prevents @{command nitpick} from considering these degenerate cases.\<close>} models for conjunctions that are classical under validity, but
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
     respectively - equivalently - refute the identity failing to hold:\<close>

lemma \<open>\<forall>p q . (p \<^bold>\<and> q) = (q \<^bold>\<and> p)\<close> \<comment> \<open>Satisfy the identity for all @{term p} and @{term q}.\<close>
  nitpick[satisfy, user_axioms, expect = genuine, show_consts, atoms \<o>\<^sub>2 = p q, format = 2]
  oops (* Note that this additionally satisfies the axioms of the imported theory AOT_PLM *)

lemma \<open>(p \<^bold>\<and> q) \<noteq> (q \<^bold>\<and> p)\<close> \<comment> \<open>Refute non-identity for arbitrary @{term p} and @{term q}.\<close>
  nitpick[user_axioms, expect = genuine, show_consts, atoms \<o>\<^sub>2 = p q, format = 2]
  oops (* Note that this additionally satisfies the axioms of the imported theory AOT_PLM *)

(*<*)
no_notation \<o>\<^sub>2_conj (infixl \<open>\<^bold>\<and>\<close> 100)
(*>*)

text\<open>While the above describes a general mechanism that (given a careful choice
of types) can be used to force Isabelle to rely on a specific set of specified properties
for constants while simultaneously retaining assured consistency,@{footnote \<open>The specification part is
guaranteed to be consistent, since we provided an explicit witness in the process; the
consistency of the axiom assuring the surjectivity of the extension function is confirmed
by @{command nitpick}.\<close>} the mechanism has limitations.

For instance, @{command specification}s are limited in their capability to specify
polymorphic constants. While it is both possible to provide a shared specification
for all types of a polymorphic constant, as well as to provide separate specifications for 
concrete distinct type instantiations of a polymorphic constant, doing both at the same time
is in general not possible.
\<close>

subsection\<open>Type Classes and Locales\<close>text\<open>\label{ClassesAndLocales}\<close>
text\<open>
Isabelle provides further abstraction mechanisms, e.g. type @{command class}es and
@{command locale}s, but each comes with its own limitations.
Technically, a @{command locale} (see~\S5.7~in~\cite{IsarRef}) is a functor that maps parameters and a specification
to a list of declarations. In practice, this can be used to reason
relative to abstract parameters that validate a set of assumptions and then @{command interpret}
the @{command locale} by proving the assumptions for a concrete instantiation of its
parameters. As a result of this interpretation of the locale, all declarations of, and
in particular all theorems proven in, the locale will be instantiated to the given parameters
and added to the theory context. A limitation of @{command locale}s is that they cannot involve polymorphic assumptions, which prevents
us from formulating the full system of AOT abstractly as a single locale.

Type @{command class}es (see~\S5.8~in~\cite{IsarRef}) are technically @{command locale}s that depend on @{emph \<open>exactly one\<close>}
type variable and additionally introduce an axiomatic type class for which, roughly speaking,
the parameters of the locale are introduced as global constants that satisfy the locale
assumptions. In practice, type classes can be used to define properties
on types and reason about any type with those properties. Type classes can then be
@{emph \<open>instantiated\<close>} for a concrete type@{footnote \<open>More precisely, a type constructor that
may depend on additional types that can be restricted to certain type classes, resp. @{emph \<open>sorts\<close>}.\<close>} by proving that the assumptions are satisfied for a concrete definition of
the locale parameters at that type. 

For example, it is possible to instantiate a type class to products of two generic types
(i.e. type variables) of specific sorts. We use this mechanism to inductively define
properties of @{term n}-ary relations of AOT as relations among arbitrary tuples (see section~\ref{ModelConstruction}).

Ideally, it would be possible to implement the full axiom system and deduction rules
of our target system using a system of type classes and locales (which would provide
an abstraction layer that is enforced on the logical level) and then merely to validate
the consistency of the construction by instantiating, resp. interpreting these
type classes and locales using a concrete semantic construction. However, in a
complex target system that involves polymorphic axioms and complex interdependencies
between its types, this is not always feasible and we have to rely on abstraction
layers as described in the last section.

While a full discussion of the subtleties of type @{command class}es
goes beyond the scope of this thesis, the short summary we provided above should
be sufficient for understanding our use of type classes in chapter~\ref{SSEofAOT}.
Furthermore, it is important to note that while we use type classes to formulate
theorems generically for several types, logically, the type classes can be eliminated
for each concrete instantiation of such a theorem with fully specified concrete types.
\<close>


section\<open>Implicit Interpretation and Assignment Functions in SSEs\<close>text\<open>\label{SSE:MetaModel}\<close>

text\<open>
Models of logical theories are usually formulated in terms of set-theory.
In the following chapters, when we say that we construct @{emph \<open>models\<close>} of the target
logic AOT using our embedding, we do not construct classical set-theoretic models, but our
implementation forms a model of AOT in HOL.

While a deep embedding would make interpretation and assignment functions explicit, they remain implicit
in shallow embeddings. The meta-logic Isabelle/HOL itself involves constants and variables that
are reused to represent the constants and variables of our target system.
Consequently, we do not have to construct explicit interpretation and assignment functions,
but can rely on HOL's semantics for constants and variables.

In simple models of HOL,@{footnote \<open>Ignoring complications due to e.g. polymorphism.\<close>} every type has a set as its domain and a statement is valid,
if it holds for every interpretation of the constants of each type and every assignment of the variables at each type.

A set-theoretic model of the embedded logic can be constructed by lifting a set-theoretic model of HOL through
the semantic definitions of the SSE. The model-finding tool @{command nitpick}~\cite{Nitpick} can
aid in making these lifted models concrete.

Technically, a shallow embedding defines a substructure in the models of HOL, which
yields a model of the embedded logic under the defined validity.
\<close>
(*<*)
text\<open>
TODO: Elaborate? Original notes:

Propose a simplified general model of Isabelle/HOL with domains for types, interpretations
of constants and variable assignments.

Similarly, describe a model of higher-order S5 modal logic.

Show that the substructure of the embedding with the defined validity is equivalent to
validity in the model of S5 modal logic.

Thereby explain that the SSE does not need interpretation and assignment functions, if the representation
types in the embedding are chosen general enough, s.t. any domain in any S5 model is covered, and
restrictions of the interpretation and assignment functions of the HOL model to the domains of a given S5 model
cover all interpretations and assignment functions of any S5 model.

Note that the part of the S5 models that remains explicit in the embedding is solely possible worlds.
\<close>
(*>*)

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

Isabelle's @{emph \<open>Isar\<close>} (@{emph \<open>Intelligible semi-automated reasoning\<close>}) language itself (see~\cite{IsarRef}) is, as the
name suggests, specifically tailored towards being readable.
Isar makes up the @{emph \<open>outer syntax\<close>} of an Isabelle theory file and consists of commands that
specify theorems and structured proofs acting on Isabelle's system of terms and types, which are
formulated in @{emph \<open>inner syntax\<close>}.
@{emph \<open>Inner syntax\<close>} is highly customizable. In the examples in the previous sections we already
made use of the ability to define new (bold) operators using @{emph \<open>mixfix\<close>} notation (see~\S8.2 in~\cite{IsarRef}).
However, we only used the mechanism to provide symbols to be used inside the grammar tree of
Isabelle/HOL's own term structure.@{footnote \<open>Thereby we cannot use symbols that are already used in HOL for our target
logic.\<close>}
In general Isabelle's inner syntax is described by a context-free priority grammar.
It consists of a set of @{emph \<open>terminal symbols\<close>}, an extensible set of
@{emph \<open>non-terminal symbols\<close>} and a set of @{emph \<open>productions\<close>} (see~\S8.4 in~\cite{IsarRef}).
For the purpose of embedding the syntax of a target theory during the construction of SSEs, it
stands to reason to use the defined validity as root for the grammar subtree of the embedded
language.

Reusing the example of the simple modal logic in section~\ref{SimpleS5}, this can be done as follows:
\<close>

type_synonym \<o>\<^sub>3 = \<open>w \<Rightarrow> bool\<close>

text\<open>This time we do not use mixfix notation to directly introduce syntax for the validity constant.\<close>
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
@{typ id_position} is used for identifiers with additional markup information (i.e. it contains
an encoding of the source position of the identifier to be used in the context of Isabelle/PIDE; see~\cite{PIDE}).
\<close>
syntax "" :: \<open>id_position \<Rightarrow> prop\<o>\<^sub>3\<close> (\<open>_\<close>)

text\<open>Now we can already construct a simple term in our new syntax:\<close>
term \<open>\<Turnstile> p\<close>

text\<open>Since we introduce an entirely new grammar subtree that is independent of the inner syntax of HOL,
we can now reuse the same symbols for logical connectives as used in HOL (instead of having to use
bold versions like in the previous section).
We first define the connectives without syntax (here the symbols refer to connectives and operators
in the language of HOL):
\<close>

definition not_\<o>\<^sub>3 :: \<open>\<o>\<^sub>3 \<Rightarrow> \<o>\<^sub>3\<close> where \<open>not_\<o>\<^sub>3 p \<equiv> \<lambda>w . \<not>p w\<close>
definition imp_\<o>\<^sub>3 :: \<open>\<o>\<^sub>3 \<Rightarrow> \<o>\<^sub>3 \<Rightarrow> \<o>\<^sub>3\<close> where \<open>imp_\<o>\<^sub>3 p q \<equiv> \<lambda>w . p w \<longrightarrow> q w\<close>
definition conj_\<o>\<^sub>3 :: \<open>\<o>\<^sub>3 \<Rightarrow> \<o>\<^sub>3 \<Rightarrow> \<o>\<^sub>3\<close> where \<open>conj_\<o>\<^sub>3 p q \<equiv> \<lambda>w . p w \<and> q w\<close>
definition disj_\<o>\<^sub>3 :: \<open>\<o>\<^sub>3 \<Rightarrow> \<o>\<^sub>3 \<Rightarrow> \<o>\<^sub>3\<close> where \<open>disj_\<o>\<^sub>3 p q \<equiv> \<lambda>w . p w \<or> q w\<close>
definition box_\<o>\<^sub>3 :: \<open>\<o>\<^sub>3 \<Rightarrow> \<o>\<^sub>3\<close> where \<open>box_\<o>\<^sub>3 p \<equiv> \<lambda>w . \<forall>v . p v\<close>
definition dia_\<o>\<^sub>3 :: \<open>\<o>\<^sub>3 \<Rightarrow> \<o>\<^sub>3\<close> where \<open>dia_\<o>\<^sub>3 p \<equiv> \<lambda>w . \<exists>v . p v\<close>

text\<open>And then define syntax for them in our grammar subtree. The syntax definitions
are only used for parsing terms of the syntactic type @{typ prop\<o>\<^sub>3}, i.e.
terms in the grammar tree spanned by the marker @{text \<Turnstile>} introduced above.\<close>

syntax not_\<o>\<^sub>3 :: \<open>prop\<o>\<^sub>3 \<Rightarrow> prop\<o>\<^sub>3\<close> (\<open>\<not>_\<close> [40] 40)
syntax imp_\<o>\<^sub>3 :: \<open>prop\<o>\<^sub>3 \<Rightarrow> prop\<o>\<^sub>3 \<Rightarrow> prop\<o>\<^sub>3\<close> (infixl \<open>\<longrightarrow>\<close> 25)
syntax conj_\<o>\<^sub>3 :: \<open>prop\<o>\<^sub>3 \<Rightarrow> prop\<o>\<^sub>3 \<Rightarrow> prop\<o>\<^sub>3\<close> (infixl \<open>\<and>\<close> 35)
syntax disj_\<o>\<^sub>3 :: \<open>prop\<o>\<^sub>3 \<Rightarrow> prop\<o>\<^sub>3 \<Rightarrow> prop\<o>\<^sub>3\<close> (infixl \<open>\<or>\<close> 30)
syntax box_\<o>\<^sub>3 :: \<open>prop\<o>\<^sub>3 \<Rightarrow> prop\<o>\<^sub>3\<close> (\<open>\<box>_\<close> [50] 50)
syntax dia_\<o>\<^sub>3 :: \<open>prop\<o>\<^sub>3 \<Rightarrow> prop\<o>\<^sub>3\<close> (\<open>\<diamond>_\<close> [50] 50)

text\<open>Now we can start to produce complex terms in our new syntax:\<close>
term \<open>\<Turnstile> \<box>p \<longrightarrow> q \<or> \<diamond>r\<close>

text\<open>However, it is noteworthy that since the introduced grammar subtree is independent of the
usual HOL grammar, a lot of details need to be considered. For example, without further work it is
not possible to specify the types of terms in our grammar sub-tree.
For that to work the @{text \<open>::\<close>} syntax used in HOL would need to be reintroduced,\footnote{Or, alternatively,
new syntax could be introduced for the same purpose. In our embedding of AOT we will instead reproduce the fact that
PLM implicitly imposes type constraints based on the names of its (meta-)variables.} which requires some familiarity with Isabelle's
internals like the purely syntactic constant @{text \<open>_constrain\<close>} (see~\S8.5.4~in~\cite{IsarRef}).

As a simpler example, we also need to introduce parentheses explicitly in our grammar subtree:\<close>

syntax "" :: \<open>prop\<o>\<^sub>3 \<Rightarrow> prop\<o>\<^sub>3\<close> (\<open>'(_')\<close>)
term \<open>\<Turnstile> p \<and> (\<diamond>q \<longrightarrow> p)\<close> \<comment> \<open>Without the above this would not parse.\<close>

text\<open>It is still possible to mix the usual HOL syntax with our newly defined subgrammar
to argue about validity:\<close>

lemma \<open>(\<Turnstile> \<diamond>p \<longrightarrow> q) \<longrightarrow> (\<not>(\<Turnstile> p) \<or> (\<Turnstile> q))\<close>
  using dia_\<o>\<^sub>3_def imp_\<o>\<^sub>3_def valid_\<o>\<^sub>3_def by auto

text\<open>In the above the left-most implication and the diamond operator are the implication of the embedded logic and
our defined possiblity operator. The other logical connectives are the ones of the meta-logic HOL.

While the mechanism described above is sufficient for introducing an accurate representation
of the syntax of most target theories that are compatible with the lexical syntax of
Isabelle/Pure,@{footnote \<open>Note that AOT does not fall into this category
and requires additional and more complex means to arrive at a good approximation of its syntax as
described in section~\ref{AOTSyntax}.\<close>} @{emph \<open>reasoning\<close>} in the logic of the target theory
entails additional challenges. For example, reasoning using Kripke-semantics usually
involves proving statements relative to a fixed, but arbitrary possible world - however
semantic possible worlds are not part of the syntax of the target theory and managing
them can become a distraction. Therefore, we not only define custom inner syntax
for the language of AOT, but also extend Isabelle's outer syntax by custom commands
that hide this complexity (see section~\ref{AOTOuterSyntax}).

In the following chapter we describe our target theory AOT in terms of our defined
syntax, while the technical construction of the syntax representation itself is discussed
in section~\ref{AOTSyntax}.
\<close>

chapter\<open>Abstract Object Theory\<close>text\<open>\label{AOT}\<close>

text\<open>
The following sections provide a brief introduction to Abstract Object Theory (AOT or @{emph \<open>object theory\<close>}). While the first
section will explain the general idea and motivation of object theory, the subsequent sections
reproduce the language and axiom system of AOT as implemented in our embedding. In the process,
we hint at the major differences between the formulation of AOT in PLM and its incarnation in
our embedding, referencing the discussion of implementational details in the next chapter where
applicable.
Recall that, as mentioned in section~\ref{Conventions}, all definitions and theorems are
cited directly from our embedding and thereby verified by Isabelle. Exceptions to this
rule are explicitly stated and marked by vertical bars at the page margins.

We restrict ourselves to the discussion of the second-order fragment of AOT which is the target of
our embedding in Isabelle/HOL.\footnote{In the following chapters up until chapter~\ref{HigherOrderAOT}, we will
refer to the second-order fragment of AOT plainly as AOT or \emph{object theory}.}
The second-order fragment is expressive enough for the analysis of a wide variety of objects occurring in philosophy and mathematics,
including Basic Logical Objects like Truth Values and Extensions of Propositions (see~\ref{AOT:AOT_BasicLogicalObjects}, resp. PLM chapter~10);
Platonic Forms (see PLM chapter~11); Situations, Worlds, Times, and Stories (see~\ref{AOT:AOT_PossibleWorlds}, resp. PLM chapter~12);
Concepts (see PLM chapter 13) and Natural Numbers (see~\ref{AOT:AOT_NaturalNumbers}, resp. PLM chapter~13).@{footnote \<open>The
chapter numbering of PLM is relative to~\cite{PLM-Oct-13-2021}.\<close>}

The applications of higher-order object theory and the challenges in representing it in Isabelle/HOL are
briefly discussed in chapter~\ref{HigherOrderAOT}. To get an intuition for the level of expressiveness of
full higher-order object theory, note that it can be used to analyze e.g. Zermelo-Fraenkel set-theory itself as
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
AOT_theorem proposition_identity: \<open>p = q \<equiv> [\<lambda>x p] = [\<lambda>x q]\<close>
  by(rule "identity:4"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I"]) "cqt:2"
(*>*)

text\<open>

AOT is a meta-physical theory inspired by ideas of
Ernst Mally and formalized by Edward Zalta. 
While the theory has been evolving for several decades (see~\cite{zalta1983abstract, zalta1988intensional}), its most recent canonical
presentation is given in @{emph \<open>Principia Logico-Metaphysica\<close>} (PLM), which is under continuous
development and the most recent version of which can be accessed as online monograph (see~\cite{PLM-current}).
This thesis is written relative to the version dated October 13, 2021 (see~\cite{PLM-Oct-13-2021}).
A summary similar to the one in this section can also be found in~\cite{ReviewPaper}.

AOT draws two fundamental distinctions, one between @{emph \<open>abstract\<close>} and
@{emph \<open>ordinary\<close>} objects, and one between two modes of predication, namely,
classical @{emph \<open>exemplification\<close>}  @{term "\<guillemotleft>[F]x\<guillemotright>"}, or more generally, @{term "\<guillemotleft>[R]x\<^sub>1...x\<^sub>n\<guillemotright>"} and
@{emph \<open>encoding\<close>} @{term "\<guillemotleft>x[F]\<guillemotright>"}, or more generally, @{term "\<guillemotleft>x\<^sub>1...x\<^sub>n[R]\<guillemotright>"}.@{footnote \<open>Note that we use additional square brackets around property terms
in exemplification or encoding formulas, except for specific (primitive or defined) constants like @{term \<open>\<guillemotleft>E!\<guillemotright>\<close>}, @{term \<open>\<guillemotleft>O!\<guillemotright>\<close>} and @{term \<open>\<guillemotleft>A!\<guillemotright>\<close>}.
This is a syntactic concession that makes the process of parsing atomic formulas in Isabelle simpler.
In AOT's usual notation these square brackets would be omitted, i.e. exemplification would be written as
$Fx_1\ldots x_n$ and encoding as $xF$.\<close>} The variables @{term x\<^sub>1}, @{term x\<^sub>2}, @{text \<open>\<dots>\<close>}, @{term x\<^sub>n}, resp. @{term x}, @{term y}, @{term z}, @{text \<open>\<dots>\<close>}, range over both ordinary and
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
objects. It asserts, for every expressible condition on properties (i.e. for every expressible set of properties), that there exists
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
of abstract objects imply that abstract objects can be modelled as elements of the power set of properties:
every abstract object uniquely corresponds to a specific set of properties.

Given this basic theory of abstract objects, AOT can elegantly define
a wide variety of objects that have been postulated in philosophy or
presupposed in the sciences, including Leibnizian concepts, Platonic
forms, possible worlds, natural numbers, logically-defined sets, etc.

Another crucial aspect of the theory is its hyperintensionality:
Relation identity is defined in terms of encoding rather than
in terms of exemplification. Two properties @{term F} and @{term G} are stipulated to be identical if they are
necessarily @{emph \<open>encoded\<close>} by the same abstract objects (\mbox{@{thm "identity:2"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I", OF "cqt:2[const_var]"[axiom_inst], OF "cqt:2[const_var]"[axiom_inst], of _ F G, print_as_theorem]}}).\footnote{Traditionally,
one might expect properties to be identical, if they are necessarily @{emph \<open>exemplified\<close>} by the same objects instead.}
The theory does not impose any restrictions on the properties encoded by a particular abstract
object. For example, the fact that an abstract object encodes the
property @{term \<open>\<guillemotleft>[\<lambda>x [F]x & [G]x]\<guillemotright>\<close>} does not imply that
it also encodes either the property @{term F}, or @{term G} or even
@{term \<open>\<guillemotleft>[\<lambda>x [G]x & [F]x]\<guillemotright>\<close>} (which, although extensionally equivalent to 
@{term \<open>\<guillemotleft>[\<lambda>x [F]x & [G]x]\<guillemotright>\<close>}, is a distinct intensional entity).@{footnote \<open>Note that
this hyperintensionality also extends to propositions. We will see that proposition identity is
defined in terms of property identity: @{thm proposition_identity[print_as_theorem, of p q]}\<close>}

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
the deductive system of PLM as implemented in our embedding.
For the original formulation of the system and a detailed discussion refer to~\cite{PLM-Oct-13-2021},
respectively~\cite{PLM-current}.@{footnote \<open>At the time of writing both citations refer
to the same version of PLM, but in the future \cite{PLM-current} will refer to the
most recent formulation of PLM, while \cite{PLM-Oct-13-2021} will contain the archived
version of PLM that served as reference for this thesis. Naturally, referenced
items and section numbers of PLM will be relative to \cite{PLM-Oct-13-2021}.\<close>}
\<close>

section\<open>The Language\<close>text\<open>\label{AOTLanguage}\<close>

text\<open>

A precise description of AOT's language can be found in PLM chapter~7.
In this section we provide a simplified informal description while explaining some of the deviations
from AOT's conventions we use in our embedding.

The language distinguishes between constants, variables and terms at each type. The types of
the second-order fragment consist of a type of individuals and of a type
of @{text n}-place relations (for each @{text \<open>n \<ge> 0\<close>}), i.e. relations among @{text n} individuals.@{footnote \<open>We
briefly discuss the full higher-order type theory in chapter~\ref{HigherOrderAOT}.\<close>}
Formulas are considered as @{text 0}-place relation terms. PLM uses the following naming conventions for
referring to the primitive language elements of each type:

  \<^item> Primitive individual constants: @{text \<open>a\<^sub>1, a\<^sub>2, \<dots>\<close>}
  \<^item> Individual variables: @{text \<open>x\<^sub>1, x\<^sub>2, \<dots>\<close>}
  \<^item> Primitive @{text n}-place relation constants: $P^n_1, P^n_2, \dots$
  \<^item> @{text n}-place relation variables: $F^n_1, F^n_2, \dots$
  \<^item> A distinguished 1-place relation constant for @{emph \<open>being concrete\<close>}: @{term \<open>\<guillemotleft>E!\<guillemotright>\<close>}

For increased readability, it allows to use less formal names, e.g. to use @{text \<open>x, y, z, \<dots>\<close>}
in place of @{text \<open>x\<^sub>1, x\<^sub>2, \<dots>\<close>}; @{text \<open>p, q, r, \<dots>\<close>} in place of $F^0_1, F^0_2, \dots$ or @{text \<open>F, G, H, \<dots>\<close>} in place of $F^1_1, F^1_2, \dots$, etc.@{footnote
\<open>See PLM item (5).\<close>}

Additionally, PLM uses Greek letters for @{emph \<open>meta-variables\<close>}, i.e. schematic meta-logical variables
that may range over all variable names or all terms at a given type. By convention, it associates specific kinds of
meta-variables with Greek letters (with additional numbered subscripts as needed) as follows:


  \<^item> Meta-variables ranging over individual variables: @{text \<open>\<nu>, \<mu>\<close>}
  \<^item> Meta-variables ranging over individual terms: @{text \<kappa>}
  \<^item> Meta-variables ranging over @{text n}-place relation terms: @{text \<open>\<Pi>\<^sup>n\<close>}
  \<^item> Meta-variables ranging over formulas (i.e. zero-place relation terms): @{text \<open>\<phi>, \<psi>, \<dots>\<close>}
  \<^item> Meta-variables ranging over variables of any type: @{text \<open>\<alpha>, \<beta>, \<dots>\<close>}
  \<^item> Meta-variables ranging over terms of any type: @{text \<open>\<tau>, \<sigma>, \<dots>\<close>}


PLM's system of constants, variables and meta-variables does not have to be reproduced
in all detail in our embedding for the following reasons:


  \<^item> The embedding collapses all alphabetic variants. This is discussed in more detail in section~\ref{alphabetic-variants}.
  \<^item> The embedding implicitly generalizes free variables in theorems to @{emph \<open>schematic variables\<close>}. This is discussed in more detail
    in section~\ref{free-variables-schematic}.
  \<^item> The distinction between constants and variables is done at the meta-logical level of Isabelle/HOL, i.e.
    variables and constants of the same type are distinguished by declaring them as constant, resp.
    using them as variable in the meta-logic.


Furthermore, AOT introduces the following primitive formula- and term-forming operators:

  \<^item> @{term \<open>\<guillemotleft>\<not>\<phi>\<guillemotright>\<close>}, the @{emph \<open>negation\<close>} operator
  \<^item> @{term \<open>\<guillemotleft>\<box>\<phi>\<guillemotright>\<close>}, the @{emph \<open>necessity\<close>} operator
  \<^item> @{term \<open>\<guillemotleft>\<^bold>\<A>\<phi>\<guillemotright>\<close>}, the @{emph \<open>actuality\<close>} operator
  \<^item> @{term \<open>\<guillemotleft>\<phi> \<rightarrow> \<psi>\<guillemotright>\<close>}, the @{emph \<open>conditional\<close>} operator
  \<^item> @{term \<open>AOT_TERM[(\<forall>\<alpha> \<phi>{\<alpha>})]\<close>}, the @{emph \<open>universal quantifier\<close>}@{footnote \<open>As mentioned in the previous section,
  PLM, by default, allows any free variables to occur in instances of a meta-variable, unless specified otherwise.
  For technical reasons, we choose the opposite convention, i.e. while a meta-variable may still contain
  any occurrence of variables that would remain @{emph \<open>free\<close>}, any @{emph \<open>bound\<close>} variables that may
  occur in an instance of the meta-variable have to be explicitly listed in curly brackets. See~\ref{substitutability} for
  a more detailed discussion. Also note that while the meta-logical @{text \<open>\<forall>\<close>}-quantifier in HOL has wide scope, the
  universal quantifier of AOT has narrow scope and quantifying over complex formulas generally requires parentheses.\<close>}
  \<^item> @{term \<open>AOT_TERM[\<^bold>\<iota>x \<phi>{x}]\<close>}, the @{emph \<open>definite description\<close>} operator\footnote{Note that similarly to the universal
    quantifier above, definite descriptions have narrow scope and using complex formulas as matrix requires parentheses.}
  \<^item> @{term \<open>AOT_TERM[[\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}]]\<close>}, the @{emph \<open>relation abstraction\<close>}- or @{text \<open>\<lambda>\<close>}-operator@{footnote \<open>Note
that this includes the zero-place case @{term \<open>AOT_TERM[[\<lambda> \<phi>]]\<close>}, read as @{emph \<open>that @{term \<phi>}\<close>}. The scope of the
@{text \<open>\<lambda>\<close>}-expression is explicitly given with the surrounding square brackets.\<close>}

AOT uses two kinds of atomic formulas, @{emph \<open>exemplification\<close>} formulas and @{emph \<open>encoding\<close>} formulas.
In PLM exemplification formulas are written as @{text \<open>\<Pi>\<kappa>\<^sub>1\<dots>\<kappa>\<^sub>n\<close>}, whereas encoding formulas are
written as @{text \<open>\<kappa>\<^sub>1\<dots>\<kappa>\<^sub>n\<Pi>\<close>}. In our embedding, we use additional square brackets for easier parsing, i.e. we use:

  \<^item> @{term \<open>AOT_TERM[([\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n)]\<close>} for atomic exemplification formulas
  \<^item> @{term \<open>AOT_TERM[(\<kappa>\<^sub>1...\<kappa>\<^sub>n[\<Pi>])]\<close>} for atomic encoding formulas


Furthermore, PLM allows for extending above language using two kinds of definitions: definitions
by identity and definitions by equivalence. While the inferential role of these definitions will be
discussed in more detail in section~\ref{InferentialRoleOfDefinitions}, for now we rely on an intuitive understanding of their meaning.
PLM @{emph \<open>defines\<close>} multiple concepts that are commonly taken as primitive, such as logical existence
and identity. These basic definitions can be found in section 7.2 of PLM and are
implemented in our embedding in section~\ref{AOT:AOT_Definitions}.
In particular, PLM defines the following:

Derived connectives and quantifiers (see~\nameref{AOT:conventions:1}):\footnote{The diamond operator @{text \<open>\<diamond>\<phi>\<close>} can be
read as @{emph \<open>possibly @{text \<phi>}\<close>}. The precedence of the operators is demonstrated in~\nameref{AOT:precedence}.}

\begin{quote}
@{thm[display] "conventions:1"[of \<phi> \<psi>]
               "conventions:2"[of \<phi> \<psi>]
               "conventions:3"[of \<phi> \<psi>]
               "conventions:4"[of \<phi>]
               "conventions:5"[of \<phi>]}
\end{quote}

Logical existence, i.e. the conditions under which a term @{emph \<open>denotes\<close>} (see~\nameref{AOT:existence:1}):

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

Identity of propositions, i.e. 0-place relations (see~\nameref{AOT:identity:4}):
\begin{quote}
@{thm[display] "identity:4"[of \<phi> \<psi>]}
\end{quote}

Identity of @{text \<open>n\<close>}-place relations (@{text \<open>n \<ge> 2\<close>}):@{footnote \<open>The idea here is that two
@{text n}-place relations are identical, if they denote and all their projections to @{text \<open>n - 1\<close>} objects
are identical. In the embedding it is tricky to reproduce the ellipse notation used for this definition
directly, therefore the statement here is @{emph \<open>not\<close>} cited from the embedding, as indicated by the
vertical bars at the margins. The implementation of this definition in the embedding can be found
in~\nameref{AOT:identity:3} and is discussed in more detail in section~\ref{nary}.\<close>}

\begin{quote}
  \Squ{@{text \<open>\<Pi> = \<Pi>' \<equiv>\<^sub>d\<^sub>f \<Pi>\<down> & \<Pi>'\<down> & \<forall>y\<^sub>1\<dots>\<forall>y\<^bsub>n-1\<^esub> ([\<lambda>x [\<Pi>]xy\<^sub>1\<dots>y\<^bsub>n-1\<^esub>] = [\<lambda>x [\<Pi>']xy\<^sub>1\<dots>y\<^bsub>n-1\<^esub>] &
[\<lambda>x [\<Pi>]y\<^sub>1xy\<^sub>2\<dots>y\<^bsub>n-1\<^esub>] = [\<lambda>x [\<Pi>']y\<^sub>1xy\<^sub>2\<dots>y\<^bsub>n-1\<^esub>] & \<dots> &
[\<lambda>x [\<Pi>]y\<^sub>1\<dots>y\<^bsub>n-1\<^esub>x] = [\<lambda>x [\<Pi>']y\<^sub>1\<dots>y\<^bsub>n-1\<^esub>x]
)\<close>}}
\end{quote}

Based on the described language and definitions we can state AOT's axiom system.
\<close>

section\<open>The Axiom System\<close>text\<open>\label{AxiomSystem}\<close>

text\<open>
In the following, we reproduce the full axiom system of the latest formulation of AOT, while
commenting on several aspects that are specific to AOT. Unless explicitly noted otherwise, we
will directly cite the axioms from our implementation while explaining notational and conceptual
differences to the original axiom system. The original axiom system is stated in PLM chapter~8
with detailed explanations. The implementation in our embedding can be found in~\ref{AOT:AOT_Axioms}.
Throughout the section we will refer to the statements of the axioms in~\ref{AOT:AOT_Axioms},
which will in turn refer to the item numbers of the respective axioms in PLM.

The first set of axioms build up a Hilbert-style deductive system for negation and implications
following Mendelson's~\cite{Mendelson1987} system (see~\nameref{AOT:pl:1}):

\begin{quote}
@{thm[display] "pl:1"[axiom_inst, print_as_theorem, of \<phi> \<psi>]
      "pl:2"[axiom_inst, print_as_theorem, of \<phi> \<psi> \<chi>]
      "pl:3"[axiom_inst, print_as_theorem, of \<phi> \<psi>]}
\end{quote}

The next set of axioms constructs a quantifier logic for a free logic with non-denoting
terms (see~\nameref{AOT:cqt:1},~\nameref{AOT:cqt:3}).
Formulas of the form @{term \<open>\<guillemotleft>\<tau>\<down>\<guillemotright>\<close>} can be read as @{emph \<open>the term @{term \<open>\<tau>\<close>} denotes\<close>} and refer
to the notion of logical existence that was @{emph \<open>defined\<close>} in the previous section.\footnote{See
section~\ref{substitutability} for a discussion of the free variable notation using curly brackets and
slight differences in the formulation compared to PLM.}

\begin{quote}
@{thm[display] "cqt:1"[axiom_inst, of _ \<phi> \<tau>, print_as_theorem]
      "cqt:3"[axiom_inst, of _ \<phi> \<psi>, print_as_theorem]
      "cqt:4"[axiom_inst, of _ \<phi>, print_as_theorem]
      "cqt:5:a"[axiom_inst, of _ \<Pi> \<kappa>\<^sub>1\<kappa>\<^sub>n, print_as_theorem]
      "cqt:5:b"[axiom_inst, of _ \<kappa>\<^sub>1\<kappa>\<^sub>n \<Pi>, print_as_theorem]}
\end{quote}

The last two axioms in the list above are noteworthy: they establish that if any
atomic exemplification or encoding formula is true, then its primary terms are significant.

Additionally, PLM establishes a base set of denoting terms with the following axiom:

\begin{quote}
  \Squ{@{term \<open>\<guillemotleft>\<tau>\<down>\<guillemotright>\<close>}, provided @{term \<tau>} is a primitive constant, a variable, or a @{text \<open>\<lambda>\<close>}-expression
  in which the initial @{text \<open>\<lambda>\<close>} does not bind any variable in any encoding formula subterm.}
\end{quote}

Reproducing the natural language condition on @{term \<tau>} in the embedding is non-trivial (see~\nameref{AOT:cqt:2[const_var]},
which uses the auxiliary predicate @{text \<open>INSTANCE_OF_CQT_2\<close>} defined in~\nameref{AOT:AOT_semantics.AOT_instance_of_cqt_2}); we discuss
the implementation of this axiom in detail in section~\ref{cqt:2-impl}.

For a simple intuition, note that all @{text \<open>\<lambda>\<close>}-expressions, in which every atomic formula
in the matrix is an exemplification formula, denote, while special care has to be taken
in the presence of encoding formulas.@{footnote \<open>Note that this includes "implicit" encoding
formulas that merely occur in the definiens of a defined constant used in the matrix. Those
are also counted as encoding formula subterms of the matrix. See PLM items (8) and (17.3).\<close>} The axiom will be discussed
in more detail later in this chapter.

The next axiom states that identical objects can be substituted in formulas. Note that the used identity
is not primitive, but was @{emph \<open>defined\<close>} in the last section (see~\nameref{AOT:l-identity}).@{footnote \<open>PLM formulates
the axiom as: @{term \<open>\<guillemotleft>\<alpha> = \<beta> \<rightarrow> (\<phi> \<rightarrow> \<phi>')\<guillemotright>\<close>}, whenever @{text \<beta>} is @{emph \<open>substitutable for\<close>} @{text \<alpha>} in @{text \<phi>}, and
@{text \<open>\<phi>'\<close>} is the result of replacing zero or more free occurrences of @{text \<alpha>} in @{text \<phi>} with occurrences of @{text \<beta>}.
This is equivalent to the formulation in the embedding modulo the equivalence of alphabetic variants (see~\ref{alphabetic-variants}).
The precise correspondence is discussed in more detail in section~\ref{substitutability} at the example of the first quantifier
axiom above.\<close>}

\begin{quote}
@{thm[display] "l-identity"[axiom_inst, of _ \<alpha> \<beta> \<phi>, print_as_theorem]}
\end{quote}

The following axiom (see~\nameref{AOT:logic-actual}) is the single @{emph \<open>modally fragile axiom\<close>} of the system.
This is signified by the turnstile operator @{text \<open>\<^bold>\<turnstile>\<close>}. All other axioms are @{emph \<open>modally strict\<close>} (for simplicity, we assume the
corresponding turnstile operator @{text \<open>\<^bold>\<turnstile>\<^sub>\<box>\<close>} by default and refrain from mentioning it
explicitly@{footnote \<open>Respectively, printing of modally-strict statements cited from the embedding is set
up in such a way that it does not print the turnstile operator.\<close>}).
The distinction is discussed further in section~\ref{ModallyStrictFragile}.

\begin{quote}
@{thm[display] "logic-actual"[act_axiom_inst, of \<phi>]}
\end{quote}

Intuitively, modally-fragile statements extend to @{emph \<open>actual\<close>} truths, while modally-strict
statements refer to @{emph \<open>necessary\<close>} truths.

Apart from the above modally-fragile principle, the logic of actuality is governed by the following
modally-strict axioms (see~\nameref{AOT:logic-actual-nec:1}):

\begin{quote}
@{thm[display] "logic-actual-nec:1"[axiom_inst, of _ \<phi>, print_as_theorem]
               "logic-actual-nec:2"[axiom_inst, of _ \<phi> \<psi>, print_as_theorem]
               "logic-actual-nec:3"[axiom_inst, of _ \<phi>, print_as_theorem]
               "logic-actual-nec:4"[axiom_inst, of _ \<phi>, print_as_theorem]}
\end{quote}

The logic of necessity and possibility is axiomatized using the classical K, T and 5 axioms of a
propositional S5 modal logic (see~\nameref{AOT:qml:1}):

\begin{quote}
@{thm[display] "qml:1"[axiom_inst, of _ \<phi> \<psi>, print_as_theorem]
               "qml:2"[axiom_inst, of _ \<phi>, print_as_theorem]
               "qml:3"[axiom_inst, of _ \<phi>, print_as_theorem]}
\end{quote}

Additionally, PLM states the following axiom (see~\nameref{AOT:qml:4}) that requires that there might be a concrete object
that is not @{emph \<open>actually\<close>} concrete, thereby ensuring that the domain of ordinary (i.e. possibly concrete) objects is
non-empty@{footnote \<open>Note that this consequence of the axiom relies, among others, on the fact that AOT allows deriving the Barcan formulas, in particular~\nameref{AOT:BFs:3}.\<close>} and committing the system against modal collapse.
\begin{quote}
@{thm[display] "qml:4"[axiom_inst, print_as_theorem]}
\end{quote}

The classical S5 modal logic is connected to the logic of actuality by the following two axioms (see~\nameref{AOT:qml-act:1}):

\begin{quote}
@{thm "qml-act:1"[axiom_inst, of _ \<phi>, print_as_theorem]
      "qml-act:2"[axiom_inst, of _ \<phi>, print_as_theorem]}
\end{quote}

Definite descriptions in AOT are governed by the following axiom (see~\nameref{AOT:descriptions}), which will allow the derivation
of a version of Russell's analysis of descriptions (see section~\ref{DefiniteDescriptions}):

\begin{quote}
@{thm descriptions[axiom_inst, of _ x \<phi>, print_as_theorem]}
\end{quote}


A consistent axiomatization of complex relation terms in AOT requires some care. While @{text \<open>\<lambda>\<close>}-expressions
follow the classical principles of @{text \<alpha>}-, @{text \<beta>}- and @{text \<eta>}-conversion, they have to be
suitably restricted to denoting terms, since not all @{text \<open>\<lambda>\<close>}-expressions are guaranteed to denote.
Also note that the embedding generally collapses alphabetic variants (see~\ref{alphabetic-variants}),
so while a version of @{text \<alpha>}-conversion can be stated, it effectively reduces to the statement that denoting
@{text \<lambda>}-expressions are self-identical in our implementation.
@{text \<alpha>}-, @{text \<beta>}- and @{text \<eta>}-conversion are formulated as follows (see~\nameref{AOT:lambda-predicates:1}):

\begin{quote}
@{thm[display] "lambda-predicates:1"[axiom_inst, of _ \<phi>, print_as_theorem]
               "lambda-predicates:2"[axiom_inst, of _ \<phi> x\<^sub>1x\<^sub>n, print_as_theorem]
               "lambda-predicates:3"[axiom_inst, of _ F, print_as_theorem]}
\end{quote}
Note that the last of the above axioms, @{text \<eta>}-conversion, also has the @{text 0}-place case
@{thm "lambda-predicates:3[zero]"[axiom_inst, of _ p, print_as_theorem]}.@{footnote\<open>While identical by axiom,
the syntactically distinct terms @{text \<open>p\<close>} and @{text \<open>[\<lambda> p]\<close>} in AOT are meant to capture
the natural-language distinction between the statement @{text p} itself and the statement
@{emph \<open>that @{text p} is true\<close>}. Also note that in the embedding the @{text 0}-place case
is stated separately for @{text \<eta>}-conversion (see~\nameref{AOT:lambda-predicates:3[zero]}) and
@{text \<alpha>}-conversion (see~\nameref{AOT:lambda-predicates:1[zero]}). @{text \<open>\<beta>\<close>}-conversion
in PLM is only stated for @{text \<open>n \<ge> 1\<close>}.\<close>}

The following axiom of @{emph \<open>coexistence\<close>} is specific to AOT and, together with generally extending AOT's free logic
to relation terms and the refinement of base cases of denoting terms, a main aspect in the evolution
of PLM that was originally triggered by its analysis using our embedding.
It states that whenever a @{text \<lambda>}-expression denotes, any @{text \<lambda>}-expression with a matrix
that is necessarily equivalent on all abstracted variables will denote as well (see~\nameref{AOT:safe-ext}):

\begin{quote}
@{thm[display] "safe-ext"[axiom_inst, of _ \<phi> \<psi>, print_as_theorem]}
\end{quote}

This axiom, together with AOT's move to a general free logic for complex terms, is discussed in
more detail in section~\ref{MoveToFreeLogic}.

The remaining axioms govern AOT's second mode of predication, @{emph \<open>encoding\<close>}.

The first of these axioms reduces @{term n}-ary encoding to unary encoding of projections as follows:@{footnote
\<open>Note that similarly to the definition of @{term n}-ary relation identity, the formulation using
ellipses is non-trivial to reproduce in the embedding. Therefore we again do @{emph \<open>not\<close>} cite the axiom
directly from the embedding, but state it as given in PLM modulo our notational conventions.
The precise implementation in the embedding can be found in~\nameref{AOT:nary-encoding[2]} and is discussed in
more detail in section~\ref{nary}.\<close>}


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
their modal closures (i.e. actualizations and necessitations) are taken as axioms as well.
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

While an implementation of the complete deductive system of PLM chapter~9 can be
found in~\ref{AOT:AOT_PLM}, a full discussion of the entire system would go beyond the scope of this thesis.
However, we will discuss some aspects in detail with a particular focus on concepts that are required
for the construction of natural numbers in chapter~\ref{NaturalNumbers}.
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

While PLM can refer to structural induction on the complexity of a formula and the length of derivations
to derive further meta-rules, by the nature of a Shallow Semantic Embedding, the precise term structure is not
preserved, but instead terms are directly represented as objects in their semantic domain, and theorem-hood is not defined
by means of derivations but internally constructed in terms of semantic validity.
For that reason, in our embedding we derive the rules in question by referring to the semantic
properties of the embedding.
In particular, we derive the following rules semantically:

The deduction theorem (see~\nameref{AOT:deduction-theorem}):
\begin{quote}
@{thm[display] "deduction-theorem"[print_as_rule]}
\end{quote}
I.e. if assuming @{term \<phi>} it can be derived that @{term \<psi>}, then @{term \<phi>} implies @{term \<open>\<psi>\<close>}.

The rule of necessitation RN (see~\nameref{AOT:RN} and~\nameref{AOT:RN[prem]}):
\begin{quote}
@{thm[display] "RN"[print_as_rule]}
\end{quote}

The rule RN can only be applied to a formula @{term \<phi>}, if @{term \<phi>} has a @{emph \<open>modally-strict proof\<close>},
as signified by @{text \<open>\<^bold>\<turnstile>\<^sub>\<box>\<close>}. We discuss this in more detail in section~\ref{ModallyStrictFragile}.

The rule of generalization GEN (see~\nameref{AOT:rule-gen}):
\begin{quote}
@{thm[display] "GEN"[print_as_rule]}
\end{quote}

@{text \<open>for arbitrary\<close>} is implemented using a meta-logical all quantifier.
This means that @{term \<phi>} has to hold for an arbitrary choice of @{text \<alpha>} and
therefore independently of any local assumptions about any concrete @{text \<alpha>}.
This goes along with PLM's restriction to only allow the application of GEN, if
@{text \<alpha>} does not occur free in any assumption.
\<close>

subsection\<open>The Inferential Role of Definitions\<close>text\<open>\label{InferentialRoleOfDefinitions}\<close>

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
has to be formulated in terms of primitives of the language, i.e. in terms of implications.

To that end, PLM formulates a @{emph \<open>Rule of Definition by Equivalence\<close>} that we reproduce in
the embedding as follows (see~\nameref{AOT:df-rules-formulas[1]}):

\begin{quote}
@{thm[display] "df-rules-formulas[1]"[axiom_inst, of \<phi> \<psi>, print_as_rule]
               "df-rules-formulas[2]"[axiom_inst, of \<phi> \<psi>, print_as_rule]}
\end{quote}

In other words, a definition-by-equivalence of the form @{text \<open>\<phi> \<equiv>\<^sub>d\<^sub>f \<psi>\<close>} introduces the closures of
@{text \<open>\<phi> \<rightarrow> \<psi>\<close>} and @{text \<open>\<psi> \<rightarrow> \<phi>\<close>} as necessary axioms.@{footnote \<open>Therefore, the rule has axiomatic
character and also has to be derived from the semantics in the appendix. The same is true for the
rule of definition by identity below.\<close>}

The principle that a definition-by-equivalence in fact implies definiens and definiendum to
be equivalent becomes a derived rule (see~\nameref{AOT:rule-eq-df:1}):

\begin{quote}
@{thm[display] "\<equiv>Df"[of \<phi> \<psi>, print_as_rule]}
\end{quote}

However, note that while this also implies @{emph \<open>necessary\<close>} equivalence of definiens
and definiendum (using the rule of necessitation RN mentioned above), in AOT necessary
equivalence of propositions does not imply their identity.
Another noteworthy subtlety in PLM's use of definitions by equivalence is its convention that such definitions
are stated using object-level variables, even though those variables act as meta-variables.
For instance, following PLM's conventions, the definition of identity for properties (see~\ref{AOTLanguage}) can be stated as:

\begin{quote}
@{thm[display] "identity:2"[of F G]}
\end{quote}

However, replacing @{term F} and @{term G} by any property term constitutes a valid instance of this
definition. In order to avoid confusion for a reader that is not familiar with this convention, we
choose to either state the definitions using meta-variables instead,@{footnote \<open>at the example of property identity: @{thm "identity:2"[of \<Pi> \<Pi>']}\<close>}
or state a derived equivalence as theorem using object-variables in its place (which allows
forgoing clauses about the significance of the involved terms in the definiendum).
I.e. in the upcoming chapters, instead of stating the full
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
to all other terms (of the same type).
\<close>

subsubsection\<open>Definitions by Identity\<close>

text\<open>
A subtlety in definitions by identity is the question of when a defined term denotes.
This is made explicit in the formulation of the @{emph \<open>Rule of Definition by Identity\<close>} (see~\nameref{AOT:df-rules-terms[1]}):

\begin{quote}
@{thm[display] "df-rules-terms[1]"[axiom_inst, print_as_rule, of \<tau> \<sigma> _ \<tau>\<^sub>1\<tau>\<^sub>n]}
\end{quote}

I.e. if the definiens denotes, a definition by identity implies identity, if the definiens fails to denote,
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

Apart from the specific items discussed in the following sections,
it may generally be helpful to be aware of the following derived
properties of the deductive system:

  \<^item> Propositional reasoning in AOT is classical.@{footnote \<open>In particular, as stated in PLM item (113),
all classical propositional tautologies are theorems of AOT.\<close>}
  \<^item> Modal reasoning can be read semantically as following Kripke-semantics without accessibility relation and
with a fixed designated actual world for the actuality operator. In particular, AOT follows an S5 modal logic with actuality operator and
Barcan formulas.
  \<^item> The free logic extends to all types, but all propositions provably denote.
    Quantifiers range over denoting objects and the defined identity constitutes an @{emph \<open>existing identity\<close>},
    i.e. to be identical two entities need to both denote @{emph \<open>and\<close>} denote the same thing.@{footnote \<open>Respectively,
    denote and satisfy the axiom of the substitution of identicals. Our implementation has the property that
    PLM's defined identity implies meta-logical identity.\<close>}

\<close>

subsection\<open>Restricted Variables\<close>text\<open>\label{RestrictedVariables}\<close>

text\<open>

A common theme in abstract object theory is the definition and analysis of certain families
of objects. For instance, Possible Worlds, Logical Sets or Natural Numbers are families
of abstract objects with specific properties. Furthermore, some constructions involve talking
about the Ordinary Objects specifically. To be able to more conveniently state
theorems involving such families of objects, PLM introduces a generic mechansism for defining
@{emph \<open>restricted variables\<close>} that range over objects satisfying a certain @{emph \<open>restriction condition\<close>} (see PLM section~10.5).
\<close>

text\<open>
A formula @{term \<psi>} that involves a single free, unrestricted variable @{term \<alpha>}, i.e. a formula
that can be written as @{text \<open>\<psi>{\<alpha>}\<close>} in the notational convention of the embedding, is called
a @{emph \<open>restriction condition\<close>}, just in case that it is both @{emph \<open>non-empty\<close>}, i.e.
@{thm (concl) "AOT_restriction_condition.res-var:2"[of \<psi>, print_as_theorem]} is a (modally-strict)
theorem, and has @{emph \<open>strict existential import\<close>}, i.e. @{thm (concl) "AOT_restriction_condition.res-var:3"[of \<psi> _ \<tau>, print_as_theorem]}
is a (modally-strict) theorem. PLM distinguishes @{emph \<open>restriction conditions\<close>}, in which non-emptyness
and strict existential import are modally-strict and @{emph \<open>weak restriction conditions\<close>}, in which neither
are required to be modally-strict. Since the parts of PLM implemented in our embedding do not involve
weak restriction conditions, the embedding thus far forgoes an implementation of them. However,
the current implementation can easily be extended to also cover weak restriction
conditions.

Furthermore, a restriction condition is @{emph \<open>rigid\<close>}, if additionally @{term \<open>print_term \<guillemotleft>\<forall>\<alpha>(\<psi>{\<alpha>} \<rightarrow> \<box>\<psi>{\<alpha>})\<guillemotright>\<close>}
is a modally-strict theorem.@{footnote \<open>While our embedding supports non-rigid restriction condition, the parts
of PLM currently implemented involve only rigid restriction conditions.\<close>}

An example of a rigid restriction condition is @{emph \<open>being ordinary\<close>}, i.e. @{term \<open>\<guillemotleft>O!x\<guillemotright>\<close>}.\footnote{It
is a theorem that there necessarily exists an ordinary object @{thm "o-objects-exist:1"[print_as_theorem]}
(see~\nameref{AOT:o-objects-exist:1}), as a consequence of the modal axiom @{thm "qml:4"[axiom_inst, print_as_theorem]},
the definition of @{emph \<open>being ordinary\<close>} as @{thm "oa:1"}, @{text \<open>\<beta>\<close>}-conversion and some modal reasoning.
Furthermore, strict existential instance follows from one of the quantifier axioms (see~\nameref{AOT:cqt:5:a}).
Rigidity is a consequence of the definition of being ordinary (see~\nameref{AOT:oa-facts:1}).}

Restricted variables are governed by the following conventions (see PLM item (331)):
Let @{term \<open>\<gamma>\<close>} be a variable that is restricted by the restriction condition @{text \<open>\<psi>{\<alpha>}\<close>}.
Then a quantified formula of the form @{text \<open>\<forall>\<gamma> \<phi>{\<gamma>}\<close>} is to be understood as an
abbreviation of @{text \<open>\<forall>\<alpha>(\<psi>{\<alpha>} \<rightarrow> \<phi>{\<alpha>})\<close>} for an unrestricted variable @{text \<open>\<alpha>\<close>}.
Furthermore, @{text \<open>\<exists>\<gamma> \<phi>{\<gamma>}\<close>} abbreviates @{text \<open>\<exists>\<alpha>(\<psi>{\<alpha>} & \<phi>{\<alpha>})\<close>} and similar
conventions are introduced for definite descriptions, @{text \<open>\<lambda>\<close>}-expressions and
definitions.

For non-rigid restriction conditions, PLM bans the use of free restricted variables in theorem
statements and merely allows bound occurrences. However, for rigid restriction conditions
PLM allows the use of free restricted variables in theorem statements and extends reasoning in the system
by allowing to take @{text \<open>\<psi>{\<gamma>}\<close>} as modally-strict axiom.

This construction allows natural reasoning with rigidly restricted variables, i.e. the
fundamental rules @{emph \<open>GEN\<close>} and @{emph \<open>RN\<close>} as well as usual quantifier
and modal reasoning (e.g. @{text \<open>\<forall>\<close>}-elimination, existential introduction, Barcan
formulas, etc.) can be extended to restricted variables governed by a rigid
restriction condition.
\<close>

subsection\<open>Identity on the Ordinary Objects\<close>text\<open>\label{IdentitySubE}\<close>

text\<open>
While the general definition of identity for individuals was given in section~\ref{AOTLanguage},
PLM also introduces an identity @{emph \<open>relation\<close>} on the ordinary objects and
matching infix notation (see~\nameref{AOT:=E}):@{footnote \<open>Note that the introduced
infix notation @{term \<open>\<guillemotleft>x =\<^sub>E y\<guillemotright>\<close>} merely abbreviates @{text \<open>[(=\<^sub>E)]xy\<close>} and the stated equivalence
is a theorem derived by @{term \<beta>}-conversion.\<close>}

\begin{quote}
@{thm [display] "=E"}
@{thm [display] "=E-simple:1"[of _ x y, print_as_theorem]}
\end{quote}

Notably, while the above definition of @{text \<open>=\<^sub>E\<close>} constitutes a denoting
@{emph \<open>relation\<close>} (the @{text \<open>\<lambda>\<close>}-expression does not involve encoding claims
and thereby denotes by axiom), general identity of both ordinary @{emph \<open>and\<close>} abstract objects
@{emph \<open>does\<close>} involve encoding claims and does not constitute a general relation of
identity. In particular, the assumption that general identity among individuals is a relation
contradicts the existence of indistinguishable abstract objects discussed
in section~\ref{IndistinguishableAbstractObjects}. 

Identity on the ordinary objects will play an important role in PLM's analysis of
Natural Numbers, discussed in chapter~\ref{NaturalNumbers}.
\<close>

subsection\<open>Definite Descriptions\<close>text\<open>\label{DefiniteDescriptions}\<close>

text\<open>The following axiom, that was already mentioned in section~\ref{AxiomSystem}, governs
definite descriptions:

\begin{quote}
@{thm descriptions[axiom_inst, of _ x \<phi>, print_as_theorem]}
\end{quote}

In particular, definite descriptions are @{emph \<open>modally rigid\<close>} and refer to objects
in the actual world. While an extensive set of theorems and rules for reasoning with
definite descriptions is given in section 9.8 of PLM (see~\nameref{PLM: 9.8}), for
an intuitive understanding of descriptions in AOT it suffices to note that they follow
a variant of Russell's analysis of definite descriptions. In particular, atomic formulas involving
definite descriptions can be translated to existence claims as follows:\footnote{For
simplicity we restrict ourselves to the case of unary exemplification and encoding. Analog
principles hold for @{text n}-ary exemplification and encoding formulas.}

\begin{quote}
@{lemma[display] \<open>print_as_theorem \<guillemotleft>[\<Pi>]\<^bold>\<iota>x \<phi>{x} \<equiv> \<exists>x (\<^bold>\<A>\<phi>{x} & \<forall>z (\<^bold>\<A>\<phi>{z} \<rightarrow> z = x) & [\<Pi>]x)\<guillemotright>\<close>
  by (safe intro!: print_as_theoremI "russell-axiom[exe,1].nec-russell-axiom")}
@{lemma[display] \<open>print_as_theorem \<guillemotleft>\<^bold>\<iota>x \<phi>{x}[\<Pi>] \<equiv> \<exists>x (\<^bold>\<A>\<phi>{x} & \<forall>z (\<^bold>\<A>\<phi>{z} \<rightarrow> z = x) & x[\<Pi>])\<guillemotright>\<close>
  by (safe intro!: print_as_theoremI "russell-axiom[enc,1].nec-russell-axiom")}
\end{quote}

I.e. an atomic formula involving a description is equivalent to there being a unique
object that actually satisfies the matrix of the description and this object satisfies
the given atomic formula. @{emph \<open>@{bold \<open>The\<close>} author of PLM is called Edward Zalta\<close>}
is equivalent to @{emph \<open>There is a unique object that is actually the author of PLM and this object is called
Edward Zalta\<close>}, respectively to @{emph \<open>There is an object that is
actually the author of PLM, every other object that is actually the author of PLM is the same object, and this
object is called Edward Zalta\<close>}.

Similarly, a definite description denotes, just in case that there is a unique object
that actually satisfies its matrix:

\begin{quote}
@{thm[display] "actual-desc:1"[print_as_theorem, of \<phi>]}
\end{quote}

E.g. @{emph \<open>@{bold \<open>the\<close>} author of Principia Mathematica\<close>} does not denote, since
Principia Mathematica was actually coauthored by Russell and Whitehead, i.e. there
is no unique object that actually authored Principia Mathematica (even if possibly
either either of them might have authored it alone in a non-actual world).
\<close>

subsection\<open>Modally-Strict and Modally-Fragile Theorems\<close>text\<open>\label{ModallyStrictFragile}\<close>

text\<open>
PLM constructs two derivational systems, the first, written as @{text \<open>\<^bold>\<turnstile>\<close>}, is called modally-fragile,
while the second, written as @{text \<open>\<^bold>\<turnstile>\<^sub>\<box>\<close>}, is called modally-strict.@{footnote \<open>To state modally-strict
and modally-fragile theorems in our embedding, we also use @{command AOT_theorem} and
@{command AOT_act_theorem} respectively. Cited statements that are undecorated are modally-strict by default.\<close>}
The main difference between the two is that the modally-fragile system is equipped with
the modally-fragile axiom of actuality and its universal (though not its necessary or actual)
closures (as mentioned in section~\ref{AxiomSystem}):

\begin{quote}
@{thm[display] "logic-actual"[act_axiom_inst, of \<phi>]}
\end{quote}

On the other hand, every modally-strict axiom is also part of the modally-fragile system.
As indicated by this axiom, semantically, the modally-fragile system is concerned with
all actual truths, whereas the modally-strict system is used to reason about truths that
are necessary.@{footnote \<open>Consequently, in our models modally-fragile axioms and theorems
are semantically valid in a designated actual world, while modally-strict axioms and
theorems are valid in all semantic possible worlds.\<close>}

Consequently, the fundamental meta-rule RN mentioned in section~\ref{MetaRules} is restricted
to modally-strict derivations: If @{term \<phi>} has a modally-strict proof, then its necessitation
@{term \<open>\<guillemotleft>\<box>\<phi>\<guillemotright>\<close>} is an (again modally-strict) theorem.

PLM's axiom system has the property that the actualization of any modally-fragile
axiom (in particular @{thm "act-conj-act:1"[print_as_theorem, of \<phi>]}) is a modally-strict
theorem (see~\nameref{AOT:act-conj-act:1}).

Consequently, for any formula that is derivable as modally-fragile theorem, i.e.
@{text \<open>\<^bold>\<turnstile> \<phi>\<close>}, it holds that @{text \<open>\<^bold>\<turnstile>\<^sub>\<box> \<^bold>\<A>\<phi>\<close>}. In particular, it follows from
@{text \<open>\<^bold>\<turnstile> \<box>\<phi>\<close>} that @{text \<open>\<^bold>\<turnstile>\<^sub>\<box> \<^bold>\<A>\<box>\<phi>\<close>}, which implies @{text \<open>\<^bold>\<turnstile>\<^sub>\<box> \<phi>\<close>}. PLM refers
to this principle as the @{emph \<open>weak converse of RN\<close>}.

However, while true in our semantics and derivable in the unextended axiom system of PLM,
PLM rejects the weak converse of RN in general.
The goal is to explicitly allow augmenting the theory by asserting contingent truths without
having to assert their actualization as modally-strict fact. After doing so, the weak
converse of RN would indeed fail, so in order to keep the reasoning system robust against
additional assertions of this kind, PLM does not allow reasoning using the weak converse of RN.
A detailed discussion of this issue can be found in PLM item (71).

While section~\ref{TrivialAccessibilityRelation} hints at a potential way of reproducing
this strict distinction using a more complex semantics, for simplicity we refrain from
doing so in our embedding and instead rely on our abstraction layer to prevent
reasoning using the weak converse of RN, while it remains valid in our semantics.\footnote{Note
that it is still possible to add contingent truths to the modally-fragile system of the
embedding and - while it would immediately become derivable semantically - just refrain
from adding a modally-strict actualization of the assertion to the abstraction
layer.}
\<close>


section\<open>Interesting Theorems of AOT\<close>

text\<open>
Before we continue our technical discussion of the specifics of AOT, we give
some examples of interesting abstract objects and properties that can be derived
about them.
\<close>

subsection\<open>Truth Values as Abstract Objects\<close>text\<open>\label{TruthValues}\<close>

text\<open>An example of AOT's ability to define metaphysical entities as abstract objects
and derive interesting properties about them, is truth values.

In AOT, it is possible to provide a @{emph \<open>syntactic\<close>} definition of what it means to
be a truth value of a proposition (see~\nameref{AOT:tv-p}):

\begin{quote}
@{thm[display] "tv-p"[of x p]}
\end{quote}

An abstract object @{text x} is the truth value of a proposition @{text p}, just in
case it encodes a property @{term F}, if and only if there is a proposition @{term q}
that is equivalent to @{term p} and @{term F} is the propositional property
@{emph \<open>being a @{text y}, such that @{term q}\<close>}.

We say that an abstract object @{term x} encodes a proposition @{term p}, if it encodes the
property @{emph \<open>being a @{text y}, s.t. @{term p}\<close>}, i.e. if @{term \<open>\<guillemotleft>x[\<lambda>y p]\<guillemotright>\<close>}.
Using that notion, it is possible to define two particular truth values, i.e. The True
and The False, as @{emph \<open>the\<close>} abstract object that encodes all propositions that
are true, resp. all propositions that are false (see~\nameref{AOT:the-true:1}):

\begin{quote}
@{thm[display] "the-true:1"}
@{thm[display] "the-true:2"}
\end{quote}

Now it becomes possible to @{emph \<open>derive\<close>} natural properties of truth values analytically.
For instance:

  \<^item> There are exactly two truth values (see~\nameref{AOT:two-T}):
    @{thm[display] "two-T"[print_as_theorem]}
  \<^item> The True is distinct from The False (see~\nameref{AOT:the-true:3}): @{thm "the-true:3"[print_as_theorem]}
  \<^item> The True and The False are truth values (see~\nameref{AOT:T-T-value:1}):\footnote{Note that
    since descriptions are modally rigid and refer to objects in the actual world, these theorems are
    modally-fragile, i.e. @{emph \<open>actual\<close>}, but not @{emph \<open>necessary\<close>} truths: While there are
    necessarily exactly two truth values, different possible worlds have different truth values (exactly two in each world).
    The defined @{text \<open>\<top>\<close>} and @{text \<open>\<bottom>\<close>} are the truth values of the actual world.}
    @{thm[display] "T-T-value:1"}
    @{thm[display] "T-T-value:2"}
  \<^item> A proposition is true, iff its truth value is The True and
    it is false, iff its truth value is The False (see~\nameref{AOT:valueof-facts:1}):
    @{thm[display] "valueof-facts:1"[of x p]}
    @{thm[display] "valueof-facts:2"[of x p]}

The analysis of truth values is an example of AOT's ability to define and analyze
abstract objects that faithfully represent entities that are usually only considered
semantically. AOT's analysis of possible worlds that is discussed in the next section
is another example of this feature.
\<close>

subsection\<open>Fundamental Theorems of Possible Worlds\<close>text\<open>\label{PossibleWorldTheory}\<close>

(*<*)
AOT_theorem trueInSituation: \<open>s \<Turnstile> p \<equiv> s[\<lambda>y p]\<close>
  apply (AOT_subst_def "true-in-s")
  apply (AOT_subst_def "prop-enc")
  by (metis "df-simplify:1" "ex:1:a" "oth-class-taut:3:a" "rule-ui:2[const_var]" Situation.restricted_var_condition)
(*>*)

text\<open>
Similarly to truth values, possible worlds are usually solely considered semantically.
However, AOT allows to @{emph \<open>define\<close>} possible worlds as a class of abstract objects
and derive fundamental theorems about them.

As a first step, consider the following definition of a @{emph \<open>Situation\<close>} (see~\nameref{AOT:situations}):

\begin{quote}
@{thm[display] "situations"[of x]}
\end{quote}

A situation is an abstract object that only encodes propositional properties.
A property @{term F} is propositional, just in case that there is a proposition @{term p}, s.t.
@{term \<open>print_as_theorem \<guillemotleft>F = [\<lambda>y p]\<guillemotright>\<close>} (see~\nameref{AOT:prop-prop1}):

\begin{quote}
@{thm[display] "prop-prop1"[of F]}
\end{quote}

Being a situation is a @{emph \<open>rigid restriction condition\<close>},@{footnote \<open>Note that by
@{emph \<open>being a situation\<close>} we refer to the @{emph \<open>formula\<close>} @{emph \<open>Situation(x)\<close>} in this case. The term
\mbox{@{term \<open>\<guillemotleft>[\<lambda>x Situation(x)]\<guillemotright>\<close>}} is not guaranteed to denote. Similarly for @{emph \<open>being a possible world\<close>} below.\<close>} so as explained in
section~\ref{RestrictedVariables}, we can use @{text s} as a restricted variable that ranges
over situations. A situation makes a proposition true, written @{term \<open>print_as_theorem \<guillemotleft>s \<Turnstile> p\<guillemotright>\<close>}, just
in case it encodes @{term \<open>\<guillemotleft>[\<lambda>y p]\<guillemotright>\<close>}:\footnote{Note that the double turnstile symbol @{text \<open>\<Turnstile>\<close>} used here
is a defined symbol in AOT and not the semantic symbol used in chapter~\ref{SSEs} and again starting
from section~\ref{HyperintensionalPropositions} to symbolize truth conditions in a semantic possible world
relative to the meta-logic HOL. Also note that by convention the defined double turnstile
symbol @{text \<open>\<Turnstile>\<close>} of AOT is to be understood to have the narrowest possible scope, i.e.
@{text \<open>w \<Turnstile> p & q\<close>} is to be read as @{text \<open>(w \<Turnstile> p) & q\<close>}.}

\begin{quote}
@{thm[display] "trueInSituation"[print_as_theorem, of s p]}
\end{quote}

Now a @{emph \<open>possible world\<close>} can be defined as a situation that possibly makes 
exactly those propositions true that are true (see~\nameref{AOT:world:1}):

\begin{quote}
@{thm[display] "world:1"[of x]}
\end{quote}

Similarly to situations, it can be shown that being a possible world is a rigid restriction condition, allowing
the use of @{text w} as a restricted variable ranging over possible worlds.

Now it can be derived that possible worlds are @{emph \<open>possible\<close>} (i.e. @{emph \<open>possibly actual\<close>}), @{emph \<open>consistent\<close>} and @{emph \<open>maximal\<close>}
situations and, furthermore, that any abstract object that is a possible and maximal situation is a possible world:

  \<^item> @{thm[display] "actual"[of x]}
    A situation is actual, if it only makes true propositions true (see~\nameref{AOT:actual}).
  \<^item> @{thm[display] "pos"[of x]}
    A situation is possible, if it is possibly actual (see~\nameref{AOT:pos}).
  \<^item> @{thm[display] "cons"[of x]}
    A situation is consistent, if it does not make any proposition and its negation
    true at the same time  (see~\nameref{AOT:cons}).
  \<^item> @{thm[display] "max"[of x]}
    A situation is maximal, if any proposition is either true or false in it (see~\nameref{AOT:max}).
  \<^item> @{thm "world-pos"[print_as_theorem, of w]}, @{thm "world-cons:1"[print_as_theorem, of w]}, @{thm "world-max"[print_as_theorem, of w]}\\
    Possible worlds are possible, consistent and maximal (see~\nameref{AOT:world-pos}, \nameref{AOT:world-cons:1} and \nameref{AOT:world-max}).
  \<^item> @{thm[display] "world=maxpos:2"[print_as_theorem, of x]}
    An abstract object is a possible world, if and only if it is a maximal and possible situation (see~\nameref{AOT:world=maxpos:2}).

The @{emph \<open>fundamental theorems of possible worlds\<close>} relate the defined possible worlds
to possibility and necessity of the modal logic of AOT (see~\nameref{AOT:fund:1} and~\nameref{AOT:fund:2}):

\begin{quote}
  @{thm[display] "fund:1"[print_as_theorem, of p]}
  @{thm[display] "fund:2"[print_as_theorem, of p]}
\end{quote}

A proposition is possible, just in case @{emph \<open>some\<close>} possible world makes it true,
and necessary, just in case @{emph \<open>every\<close>} possible world makes it true.

Furthermore, it can be shown that the basic connectives and quantifiers are well-behaved
with respect to being true in a possible world, i.e. (see~\nameref{AOT:conj-dist-w:1} and following):@{footnote \<open>Notably,
the proofs of the last two theorems were contributed to AOT on the basis of proofs in our embedding.\<close>}

  \<^item> @{thm[display] "conj-dist-w:1"[print_as_theorem, of w p q]}
  \<^item> @{thm[display] "conj-dist-w:2"[print_as_theorem, of w p q]}
  \<^item> @{thm[display] "conj-dist-w:3"[print_as_theorem, of w p q]}
  \<^item> @{thm[display] "conj-dist-w:4"[print_as_theorem, of w p q]}
  \<^item> @{thm[display] "conj-dist-w:5"[print_as_theorem, of w \<phi>]}
  \<^item> @{thm[display] "conj-dist-w:6"[print_as_theorem, of w \<phi>]}

Taken together this reproduces the semantic analysis of AOT with Kripke semantics
syntactically within the derivational system of AOT itself. It is a notable feature
of AOT that it can, in this sense, accurately reason about its own semantics.

While PLM provides an analysis of a range of further interesting objects, including
Logical Sets, Platonic forms, Stories and Fictional Characters and Leibnizian Concepts,
a full discussion of them would go beyond the scope of this thesis.

Instead, we discuss some further technical properties of the system of AOT that
will be relevant for our discussion of natural numbers in chapter~\ref{NaturalNumbers}.
\<close>


section\<open>Avoiding Known Paradoxes\<close>text\<open>\label{AvoidingParadoxes}\<close>

subsection\<open>The Clark-Boolos Paradox\<close>text\<open>\label{ClarkBoolosParadox}\<close>
(*<*)
AOT_register_variable_names
  Relation: K
(*>*)
text\<open>
Naive formulations of AOT, in which all @{text \<open>\<lambda>\<close>}-expression are assumed to
denote relations, are subject to the Clark-Boolos Paradox.@{footnote \<open>The paradox was
discovered by Romane Clark in a formalization of Meinong's theories by William Rapaport who
reported it in~\cite{Rapaport}, p. 225. Independently, George Boolos constructs the same
paradox in~\cite{BoolosFrege}, p. 17, under the name @{emph \<open>SuperRussell\<close>} in an analysis of
Frege's foundations of arithmetic.\<close>}

In particular consider the @{text \<open>\<lambda>\<close>}-expression @{term \<open>\<guillemotleft>[\<lambda>x \<exists>F (x[F] & \<not>[F]x)]\<guillemotright>\<close>}, i.e.
@{emph \<open>being an object, s.t. there is a property it encodes, but does not exemplify\<close>}.
The assumption that this property denotes leads to paradox (see~\nameref{AOT:block-paradox:1}):
Assuming that the @{text \<open>\<lambda>\<close>}-expression denotes, call it @{term K}, s.t. 
@{term \<open>\<guillemotleft>K = [\<lambda>x \<exists>F (x[F] & \<not>[F]x)]\<guillemotright>\<close>}.
By the comprehension principle of abstract objects, there is an abstract object @{term a}
that encodes exactly @{term K} and no other properties.
Now if @{term a} were to exemplify @{term K}, it would follow by @{text \<open>\<beta>\<close>}-conversion
that there is a property that @{term a} encodes, but does not exemplify. However, the
only property encoded by @{term a} is @{term K}, which @{emph \<open>is\<close>} exemplified by
@{term a} by assumption yielding a contradiction.

If, on the other hand, @{term a} does not exemplify @{term K}, it follows
that @{term a} encodes @{term K} and does not exemplify @{term K}, so it serves as witness to the claim
@{term \<open>\<guillemotleft>\<exists>F (a[F] & \<not>[F]a)\<guillemotright>\<close>}. Thus it follows by @{text \<open>\<beta>\<close>}-conversion that
@{term a} @{emph \<open>does\<close>} exemplify @{term K} yielding a contradiction.

Previous formulations of PLM disbarred @{text \<open>\<lambda>\<close>}-expressions like @{term K} syntactically:
a @{text \<open>\<lambda>\<close>}-expression was only considered to be @{emph \<open>well-formed\<close>},
if its matrix was a so-called @{emph \<open>propositional formula\<close>}. A formula was defined to be
propositional, just in case that it did not contain encoding subformulas. However, an oversight in the precise
formulation of these provisos made it possible to reintroduce the paradox as described
in the next section.

In the current formulation of PLM, the paradoxical @{text \<open>\<lambda>\<close>}-expression is well-formed, but
does not fall under the axiom that stipulates base cases of denoting terms (see~\ref{AxiomSystem}):
The initial @{text \<open>\<lambda>\<close>} binds a variable that occurs in an encoding formula subterm.

Given that the assumption that the @{text \<open>\<lambda>\<close>}-expression denotes leads to contradiction,
it now provably fails to denote (see~\nameref{AOT:block-paradox:1}):

\begin{quote}
@{thm[display] "block-paradox:1"[print_as_theorem]}
\end{quote}
\<close>

subsection\<open>Reintroduction of the Clark-Boolos Paradox\<close>text\<open>\label{NewParadox}\<close>

text\<open>
When attempting to construct an embedding of a previous formulation of PLM (see~\cite{PLM-Oct-28-2016}) that relied
on restricting matrices of @{text \<open>\<lambda>\<close>}-expressions to @{emph \<open>propositional formulas\<close>}
as defined in the previous section, we found the following oversight (see~\cite{MScThesis} and~\cite{ReviewPaper}):

Encoding formulas embedded in the matrix of definite descriptions within complex formulas
were not considered @{emph \<open>encoding subformulas\<close>} and thereby such complex formulas
were still considered propositional.@{footnote \<open>While the matrix of a definite description
(or a @{text \<lambda>}-expression) is a @{emph \<open>subterm\<close>} of any formula containing the description (or @{text \<lambda>}-expression),
it is not a @{emph \<open>subformula\<close>}. See PLM items (6), (7) and (8).\<close>}

This allowed constructing @{text \<open>\<lambda>\<close>}-expressions that were considered well-formed, but
(actually) equivalent to the paradoxical Clark-Boolos property @{term K} discussed above, namely:

\begin{quote}
@{term[display] \<open>AOT_model_id_def (\<lambda>(). K') (\<lambda>(). \<guillemotleft>[\<lambda>x [\<lambda>y \<forall>p (p \<rightarrow> p)]\<^bold>\<iota>z (z = x & \<exists>F (z[F] & \<not>[F]z))]\<guillemotright>)\<close>}
\end{quote}

Since @{term \<open>\<guillemotleft>[\<lambda>y \<forall>p (p \<rightarrow> p)]\<guillemotright>\<close>} is (necessarily) universally exemplified by all objects, it being
exemplified be a definite description is equivalent to the matrix of the description
being @{emph \<open>actually\<close>} satisfied by a unique object, i.e.:@{footnote \<open>We choose this
opportunity to demonstrate that reasoning in our embedding is readable and intuitively
understandable, by directly proving the equivalence in the syntax of the embedding. The
proof was automatically verified during the generation of this document as mentioned
in section~\ref{Conventions}.\<close>}
\<close>

AOT_theorem \<open>[\<lambda>y \<forall>p (p \<rightarrow> p)]\<^bold>\<iota>z (z = x & \<exists>F (z[F] & \<not>[F]z)) \<equiv>
             \<exists>!z (\<^bold>\<A>(z = x & \<exists>F (z[F] & \<not>[F]z)))\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>[\<lambda>y \<forall>p (p \<rightarrow> p)]\<^bold>\<iota>z (z = x & \<exists>F (z[F] & \<not>[F]z))\<close>
  AOT_hence \<open>\<^bold>\<iota>z (z = x & \<exists>F (z[F] & \<not>[F]z))\<down>\<close>
    using "cqt:5:a"[axiom_inst, THEN "\<rightarrow>E", THEN "&E"(2)] by blast
  AOT_thus \<open>\<exists>!z (\<^bold>\<A>(z = x & \<exists>F (z[F] & \<not>[F]z)))\<close>
    using "actual-desc:1"[THEN "\<equiv>E"(1)] by blast
next
  AOT_assume \<open>\<exists>!z (\<^bold>\<A>(z = x & \<exists>F (z[F] & \<not>[F]z)))\<close>
  AOT_hence \<open>\<^bold>\<iota>z (z = x & \<exists>F (z[F] & \<not>[F]z))\<down>\<close>
    using "actual-desc:1"[THEN "\<equiv>E"(2)] by simp
  AOT_thus \<open>[\<lambda>y \<forall>p (p \<rightarrow> p)]\<^bold>\<iota>z (z = x & \<exists>F (z[F] & \<not>[F]z))\<close>
    by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2" GEN "\<rightarrow>I")
qed

text\<open>
The left-hand side is equivalent to @{term \<open>\<guillemotleft>[K']x\<guillemotright>\<close>} by @{text \<open>\<beta>\<close>}-conversion (assuming
@{text \<open>K'\<close>} is a well-formed, respectively a denoting relation).
The right-hand side can be simplified to @{term \<open>\<guillemotleft>\<^bold>\<A>\<exists>F (x[F] & \<not>[F]x)\<guillemotright>\<close>}, so 
it is equivalent to @{term \<open>\<guillemotleft>\<^bold>\<A>[K]x\<guillemotright>\<close>}. Thereby, assuming @{term \<open>K'\<close>} denotes
yields a modally-fragile proof of a contradiction following the argument given in the
previous section.@{footnote \<open>The proof can also be strengthened to be modally-strict,
see~\nameref{AOT:block-paradox2:1[strict]}.\<close>}

An obvious solution to this issue would have been to further restrict propositional
formulas to not only disbar encoding subformulas, but also encoding formula subterms, i.e.
to also disallow encoding formulas embedded in matrices of descriptions and
thereby disbarring @{term \<open>K'\<close>} as not well-formed.

However, this had resulted in the loss of the ability to formulate interesting
@{text \<open>\<lambda>\<close>}-expressions involving descriptions that are safe and were deemed worthwhile
to preserve. Therefore, this solution was rejected in favour of extending
AOT's free logic to relation terms as described in the next section.
In the most recent formulation of AOT, it becomes a theorem that the paradoxical relation
@{text \<open>K'\<close>} does not denote on pain of contradiction (see~\nameref{AOT:block-paradox2:1},
resp.~\nameref{AOT:block-paradox2:1[strict]}).
\<close>

section\<open>Extending AOT's Free Logic to Relations\<close>text\<open>\label{MoveToFreeLogic}\<close>

text\<open>
In the aftermath of the discovery of the reintroduction of the Clark-Boolos paradox,
AOT's free logic was extended to all its types.@{footnote \<open>AOT previously
also involved a free logic. However, it was restricted to individual terms to account for non-denoting
definite descriptions. While there were @{text \<open>\<lambda>\<close>}-expressions that were not considered well-formed
syntactically, all @{text \<open>\<lambda>\<close>}-expressions that were well-formed were implicitly assumed
to denote.\<close>}

In the process, the definitions for logical existence (@{text \<open>\<tau>\<down>\<close>}) mentioned in section~\ref{AOTLanguage}
were introduced.\footnote{Previously, the free logic for individuals relied on a notion of logical existence
that was based on identity, i.e. @{term \<open>\<kappa>\<close>} was considered to denote, just in case @{term \<open>\<guillemotleft>\<exists>x (x = \<kappa>)\<guillemotright>\<close>}.
While the new definition of logical existence is more primitive, i.e. it is formulated in terms of primitives
of the language rather than defined identity, it now becomes a theorem that @{thm "free-thms:1"[print_as_theorem, of \<tau>]}
(see~\nameref{AOT:free-thms:1}).}
Notably, it is possible to define the conditions under which relation terms denote
using @{emph \<open>encoding\<close>}, i.e. @{thm "existence:2"[of \<Pi>]}, while a similar definition
using exemplification would fail in the second-order fragment, since there are denoting,
but necessarily unexemplified properties, i.e. @{term \<open>print_as_theorem \<guillemotleft>\<exists>x\<^sub>1...\<exists>x\<^sub>n [\<Pi>]x\<^sub>1...x\<^sub>n\<guillemotright>\<close>}
may be false for denoting @{term \<open>\<Pi>\<close>}.@{footnote \<open>In higher-order object theory, however,
it is possible to define existence of relations using higher-order exemplification as @{text \<open>\<exists>\<F> [\<F>]\<Pi>\<close>}.\<close>}

The switch to a richer free logic also involved multiple changes to the axiom system ultimately resulting in the version
given in section~\ref{AxiomSystem}.
The quantifier axioms were reformulated using the defined notion of @{term \<open>\<guillemotleft>\<tau>\<down>\<guillemotright>\<close>} for all types.
Furthermore, @{text \<open>\<alpha>\<close>}- and @{text \<open>\<beta>\<close>}-conversion were restricted to denoting
@{text \<open>\<lambda>\<close>}-expressions, the coexistence axiom was added and the base cases
for denoting terms were adjusted. The coexistence axiom was based on a similar principle
that was discovered as an artifactual theorem of the embedding of AOT at the time.@{footnote \<open>
In particular @{text \<open>\<exists>G\<box>\<forall>x\<^sub>1...x\<^sub>n(Gx\<^sub>1..x\<^sub>n \<equiv> \<phi>{x\<^sub>1...x\<^sub>n}) \<rightarrow> \<exists>F(F = [\<lambda>x\<^sub>1...x\<^sub>n \<phi>{x\<^sub>1...x\<^sub>n}])\<close>}.\<close>}
Recall its statement as:

\begin{quote}
@{thm "safe-ext"[axiom_inst, print_as_theorem, of \<phi> \<psi>]}
\end{quote}

It is also referred to as @{emph \<open>safe extension axiom\<close>}, since it merely asserts that
a @{text \<open>\<lambda>\<close>}-expression with matrix @{text \<psi>} denotes, in case there provably is a denoting @{text \<open>\<lambda>\<close>}-expression with
a matrix @{text \<phi>}, s.t. both matrices are necessarily equivalent on all objects, i.e. in case the extension of
the @{text \<open>\<lambda>\<close>}-expression is known to be safe.
Consequently, the axiom has no impact on the size of models (or on consistency):
a model can always choose the same denotation for @{term \<open>print_term \<guillemotleft>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<psi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<guillemotright>\<close>} as it
chose for @{term \<open>print_term \<guillemotleft>[\<lambda>\<nu>\<^sub>1...\<nu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n}]\<guillemotright>\<close>}.@{footnote \<open>However, note that this is not a requirement:
While, by construction, both @{text \<open>\<lambda>\<close>}-expressions are necessarily equivalent under @{text \<open>\<beta>\<close>}-conversion, AOT does not
require them to be identical.\<close>}

Initial versions of PLM that were equipped with a free logic on all types
still retained the concept of @{emph \<open>propositional formulas\<close>} (formulas without encoding subformulas), but
dropped the implicit assumption that well-formed @{text \<open>\<lambda>\<close>}-expressions (i.e. @{text \<open>\<lambda>\<close>}-expressions
with propositional matrix) generally denote, but instead excluded @{text \<open>\<lambda>\<close>}-expressions with matrices that
contain definite descriptions from the base cases of axiomatically denoting terms.

The coexistence axiom allowed to safely derive that certain @{text \<open>\<lambda>\<close>}-expressions involving
definite descriptions may still denote: Whenever it was possible to eliminate a description
from the matrix of a @{text \<open>\<lambda>\<close>}-expression using a description-free propositional formula
that is necessarily equivalent on all objects, it was safe to derive that the @{text \<open>\<lambda>\<close>}-expression denotes. 

However, due to the fact that no longer all @{text \<open>\<lambda>\<close>}-expressions with propositional matrix
could be assumed to denote, the distinction between propositional and non-propositional formulas lost most of its
relevance. Consequently, the next step was to simplify the system by replacing this syntactic distinction entirely
by a restriction of the base cases of denoting terms, i.e. all @{text \<open>\<lambda>\<close>}-expressions became
well-formed, but only @{text \<open>\<lambda>\<close>}-expressions without definite descriptions and without encoding formula subterms
were asserted to denote by axiom.

The, at the time of writing, most recent extension of the set of axiomatically denoting
@{text \<open>\<lambda>\<close>}-expression, which resulted in the formulation given in section~\ref{AxiomSystem},
allowed us to derive necessary and sufficient conditions for @{text \<open>\<lambda>\<close>}-expressions to denote,
as explained in section~\ref{KirchnersTheorem} below.
A potential further refinement is discussed in section~\ref{cqt:2-impl}.
\<close>

section\<open>Further Properties of AOT\<close>

subsection\<open>Indistinguishable Abstract Objects\<close>text\<open>\label{IndistinguishableAbstractObjects}\<close>

text\<open>
The issue raised in form of the Clark-Boolos Paradox and its variants in section~\ref{AvoidingParadoxes}
is a general issue of the comprehension principle for abstract object and their identity conditions, which
intuitively imply that abstract objects correspond to sets of properties, together with
the fact that abstract objects are simultaneously meant to themselves @{emph \<open>exemplify\<close>} properties:

Properties have exemplification-extensions which are traditionally conceived of as sets of
individuals.\footnote{In a modal setting properties are even associated with multiple sets of
objects for different semantic possible worlds or, equivalently, extensions of modal properties are conceived of as mapping
objects to sets of possible worlds in which the property is exemplified by the objects.} However, if abstract objects correspond
to sets of properties and exemplification-extensions of properties themselves correspond to sets of objects,
one may wonder how this can be achieved consistently:
How can abstract objects be sets of properties and simultaneously (in the simplest case of non-modal
and extensional properties) elements of properties?

A semantic solution to this dilemma is given by Aczel models which are described in
section~\ref{AczelModels}. But there are also derivable theorems of AOT that serve
to clarify how this dangling paradox may be avoided.

In particular, it is derivable that there are distinct, but exemplification-indistinguishable
abstract objects (see~\nameref{AOT:aclassical2}):

\begin{quote}
@{thm[display] "aclassical2"[print_as_theorem]}
\end{quote}

The comprehension principle for abstract objects requires the existence of that
many abstract objects, such that it has to be the case that some of them collapse
under exemplification. In light of avoiding a violation of Cantor's Theorem
one may even argue that @{emph \<open>most\<close>} abstract objects are indistinguishable, since
the cardinality of the set of abstract objects is strictly larger than the cardinality of
the set of properties.\footnote{And even the set of properties in turn has a strictly larger cardinality than
the set of urelements, which in Aczel models will serve as proxies for abstract objects to define
their exemplification behaviour, as described in more detail in section~\ref{AczelModels}.}

Interestingly, though, it is impossible to independently construct two concrete
abstract objects that provably fail to be distinguishable. This is also discussed
in section~\ref{JustificationExtendedComprehension} in the context of our proposed
extended comprehension principle for relations among abstract objects.
While PLM's proof of the theorem above (see~\nameref{AOT:aclassical2})
uses a slightly different construction, we can provide a proof that makes it explicit
that we can construct an abstract object particularly in such a way that there has
to be a distinct abstract object that is indistinguishable from it:
\<close>


AOT_theorem \<open>\<exists>x\<exists>y(A!x & A!y & x \<noteq> y & \<forall>F([F]x \<equiv> [F]y))\<close>
proof -
  \<comment> \<open>Consider the object @{term a} that encodes being indistinguishable from any
      abstract object that does not encode being indistinguishable from itself.\<close>
  AOT_obtain a where a_prop:
    \<open>A!a & \<forall>F (a[F] \<equiv> \<exists>y(A!y & F = [\<lambda>z \<forall>G([G]z \<equiv> [G]y)] & \<not>y[\<lambda>z \<forall>G([G]z \<equiv> [G]y)]))\<close>
    using "A-objects"[axiom_inst] "\<exists>E"[rotated] by fast

  \<comment> \<open>We show that @{term a} encodes being indistinguishable from itself using a proof by contradiction.\<close>
  AOT_have 0: \<open>a[\<lambda>z \<forall>G([G]z \<equiv> [G]a)]\<close>
  proof (rule "raa-cor:1")
    AOT_assume 1: \<open>\<not>a[\<lambda>z \<forall>G([G]z \<equiv> [G]a)]\<close>
    AOT_hence \<open>\<not>\<exists>y (A!y & [\<lambda>z \<forall>G([G]z \<equiv> [G]a)] = [\<lambda>z \<forall>G([G]z \<equiv> [G]y)] &
                    \<not>y[\<lambda>z \<forall>G([G]z \<equiv> [G]y)])\<close>
      by (safe intro!: a_prop[THEN "&E"(2), THEN "\<forall>E"(1), THEN "\<equiv>E"(3)] "cqt:2")
    AOT_hence \<open>\<forall>y \<not>(A!y & [\<lambda>z \<forall>G([G]z \<equiv> [G]a)] = [\<lambda>z \<forall>G([G]z \<equiv> [G]y)] &
                    \<not>y[\<lambda>z \<forall>G([G]z \<equiv> [G]y)])\<close>
      using "cqt-further:4"[THEN "\<rightarrow>E"] by blast
    AOT_hence \<open>\<not>(A!a & [\<lambda>z \<forall>G([G]z \<equiv> [G]a)] = [\<lambda>z \<forall>G([G]z \<equiv> [G]a)] &
                 \<not>a[\<lambda>z \<forall>G([G]z \<equiv> [G]a)])\<close>
      using "\<forall>E"(2) by blast
    moreover AOT_have \<open>A!a & [\<lambda>z \<forall>G([G]z \<equiv> [G]a)] = [\<lambda>z \<forall>G([G]z \<equiv> [G]a)] &
                       \<not>a[\<lambda>z \<forall>G([G]z \<equiv> [G]a)]\<close>
      by (safe intro!: a_prop[THEN "&E"(1)] "&I" "rule=I:1" "cqt:2" 1)
    ultimately AOT_show \<open>p & \<not>p\<close> for p using "reductio-aa:1" by blast
  qed
  \<comment> \<open>Hence, by construction, there is an abstract object, s.t. being indistinguishable from
      it is identical to being indistinguishable from @{term a}, but which does not encode being
      indistinguishable from itself.\<close>
  AOT_hence \<open>\<exists>y (A!y & [\<lambda>z \<forall>G([G]z \<equiv> [G]a)] = [\<lambda>z \<forall>G([G]z \<equiv> [G]y)] &
                 \<not>y[\<lambda>z \<forall>G([G]z \<equiv> [G]y)])\<close>
    by (safe intro!: a_prop[THEN "&E"(2), THEN "\<forall>E"(1), THEN "\<equiv>E"(1)] "cqt:2")
  \<comment> \<open>Call this object @{text b}.\<close>
  then AOT_obtain b where b_prop:
    \<open>A!b & [\<lambda>z \<forall>G([G]z \<equiv> [G]a)] = [\<lambda>z \<forall>G([G]z \<equiv> [G]b)] & \<not>b[\<lambda>z \<forall>G([G]z \<equiv> [G]b)]\<close>
    using "\<exists>E"[rotated] by blast
  \<comment> \<open>Now @{term a} and @{term b} are indistinguishable.\<close>
  AOT_have \<open>\<forall>G([G]a \<equiv> [G]b)\<close>
  proof -
    AOT_have \<open>[\<lambda>z \<forall>G([G]z \<equiv> [G]a)]a\<close>
      by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2" GEN "\<equiv>I" "\<rightarrow>I")
    AOT_hence \<open>[\<lambda>z \<forall>G([G]z \<equiv> [G]b)]a\<close>
      using b_prop[THEN "&E"(1), THEN "&E"(2)] "rule=E" by fast
    thus ?thesis
      using "\<beta>\<rightarrow>C" by blast
  qed
  \<comment> \<open>But while @{term a} encodes being indistinguishable from @{term b}, @{term b} does not
      encode being indistinguishable from itself and therefore @{term a} is not identical
      to @{term b}.\<close>
  moreover {
    AOT_have \<open>a[\<lambda>z \<forall>G([G]z \<equiv> [G]b)]\<close>
      using b_prop[THEN "&E"(1), THEN "&E"(2)] 0 "rule=E" by fast
    AOT_hence \<open>a \<noteq> b\<close>
      by (safe intro!: "ab-obey:2"[THEN "\<rightarrow>E"] "\<or>I"(1) "\<exists>I"(1)[where \<tau>=\<open>\<guillemotleft>[\<lambda>z \<forall>G([G]z \<equiv> [G]b)]\<guillemotright>\<close>]
                       "&I" b_prop[THEN "&E"(2)] "cqt:2")
  }
  \<comment> \<open>Therefore, @{term a} and @{term b} are witnesses to the claim of the theorem.\<close>
  ultimately AOT_have \<open>A!a & A!b & a \<noteq> b & \<forall>G([G]a \<equiv> [G]b)\<close>
    using "&I" a_prop[THEN "&E"(1)] b_prop[THEN "&E"(1), THEN "&E"(1)] by blast
  AOT_hence \<open>\<exists>y(A!a & A!y & a \<noteq> y & \<forall>G([G]a \<equiv> [G]y))\<close> by (rule "\<exists>I")
  AOT_thus \<open>\<exists>x\<exists>y(A!x & A!y & x \<noteq> y & \<forall>G([G]x \<equiv> [G]y))\<close> by (rule "\<exists>I")
qed

text\<open>
Notably, the existence of indistinguishable abstract objects can be used to prove that
there is no general relation of identity in AOT, i.e. @{term \<open>\<guillemotleft>[\<lambda>xy x = y]\<guillemotright>\<close>} does not
denote:
\<close>

AOT_theorem \<open>\<not>[\<lambda>xy x = y]\<down>\<close>
proof(rule "raa-cor:2") \<comment> \<open>Proof by contradiction.\<close>
  AOT_assume 0: \<open>[\<lambda>xy x = y]\<down>\<close>
  \<comment> \<open>Let a and b be witnesses to the theorem discussed above.\<close>
  AOT_obtain a b where 1: \<open>A!a & A!b & a \<noteq> b & \<forall>F([F]a \<equiv> [F]b)\<close>
    using "aclassical2" "\<exists>E"[rotated] by blast
  \<comment> \<open>From our assumption and the fact that a is self-identical, it follows
      that a exemplifies the projection of the identity relation to a.\<close>
  moreover AOT_have \<open>[\<lambda>x [\<lambda>xy x = y]ax]a\<close>
    by (safe intro!: 0 "\<beta>\<leftarrow>C" "cqt:2" tuple_denotes[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "=I")
  \<comment> \<open>Since a and b are indistinguishable, b has to exemplify this property as well.\<close>
  ultimately AOT_have \<open>[\<lambda>x [\<lambda>xy x = y]ax]b\<close>
    by (safe intro!: 1[THEN "&E"(2), THEN "\<forall>E"(1), THEN "\<equiv>E"(1)] 0 "cqt:2")
  \<comment> \<open>Which by beta-conversion yields that a is identical to b.\<close>
  AOT_hence \<open>a = b\<close>
    by (safe dest!: "\<beta>\<rightarrow>C")
  \<comment> \<open>Which contradicts the fact that a and b are distinct by construction.\<close>
  AOT_thus \<open>p & \<not>p\<close> for p
    using 1 "&E" "=-infix"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "reductio-aa:1" by blast
qed
text\<open>
This aspect of AOT will be of notable importance during the construction of
natural numbers in chapter~\ref{NaturalNumbers}.
In the following section, we will see another prominent example of a theorem of AOT
that involves indistinguishable objects and relates to Aczel models.
\<close>

subsection\<open>Necessary and Sufficient Condition for Relations to Denote\<close>text\<open>\label{KirchnersTheorem}\<close>

text\<open>
The move to a free logic for relation terms and the iterative extension of the
base cases of denoting terms mentioned in section~\ref{MoveToFreeLogic}, ultimately allowed
us to contribute the following theorem to AOT:

\begin{quote}
@{thm[display] "kirchner-thm:1"[print_as_theorem, of \<phi>]}
\end{quote}

A @{text \<open>\<lambda>\<close>}-expression denotes, if and only if necessarily its matrix agrees on
all indistinguishable objects.

The proof (see~\nameref{AOT:kirchner-thm:1}) relies on the fact that under the
assumption of the right-hand-side, it follows that @{term \<open>print_as_theorem \<guillemotleft>\<box>\<forall>y(\<exists>x(\<forall>F([F]x \<equiv> [F]y) & \<phi>{x}) \<equiv> \<phi>{y})\<guillemotright>\<close>}.
Now since \mbox{@{term \<open>print_as_theorem \<guillemotleft>[\<lambda>y \<exists>x(\<forall>F([F]x \<equiv> [F]y) & \<phi>{x})]\<down>\<guillemotright>\<close>}} by axiom (by construction
the initial @{text \<open>\<lambda>\<close>} does not bind a variable that occurs in an encoding formula subterm - in particular it
occurs only in the exemplification formula @{text \<open>[F]y\<close>}),
@{term \<open>print_as_theorem \<guillemotleft>[\<lambda>x \<phi>{x}]\<down>\<guillemotright>\<close>} follows by the coexistence axiom. The left-to-right direction
can be shown by instantiating @{term F} to @{term \<open>print_term \<guillemotleft>[\<lambda>x \<phi>{x}]\<guillemotright>\<close>} and some modal reasoning.

This theorem has several repercussions. It provides the analytical means to judge
whether a @{text \<open>\<lambda>\<close>}-expression denotes within the system of AOT itself.
Notably, this led to a proof of the existence of world-relative relations and
thereby of rigidifying relations, as discussed in more detail in the next section.

Furthermore, it can contribute to a potential reformulation of the construction of natural numbers
that does not require a modal axiom of possible infinity. This is mentioned in section~\ref{NewNumberTheory},
although at the time of writing, the analysis of
this potential change is not yet complete, so the current version of PLM at the time
of writing does not yet contain this new enhanced construction.

In general, this theorem is a prime example of the benefits of the semantic analysis
of AOT using our embedding that has led to significant theoretical improvements of AOT and
may yet allow for further improvements in the future.

Semantically, the theorem is closely related to Aczel models of AOT.
The condition of being indistinguishable, @{term \<open>print_term \<guillemotleft>\<forall>F ([F]x \<equiv> [F]y)\<guillemotright>\<close>},
semantically corresponds to @{term x} and @{term y} sharing the same @{emph \<open>urelement\<close>}.
Consequently, the theorem states that @{text \<open>\<lambda>\<close>}-expressions denote, if their matrix
agrees on objects with the same urelements or, in other words, if they can be represented
as functions acting on urelements. A more detailed semantic discussion and a precise
construction involving a mapping from individuals to urelements and relations modelled as
proposition-valued functions acting on these urelements can be found in chapter~\ref{SSEofAOT}.
\<close>

subsection\<open>World-Relative Relations and Rigidifying Relations\<close>text\<open>\label{WorldRelativeRelations}\<close>
(*<*)
(* TODO: ugly hack *)
definition explicitParen :: \<open>'a \<Rightarrow> 'a\<close> where \<open>explicitParen x \<equiv> x\<close>
syntax (input) "_explicitParen" :: \<open>\<phi> \<Rightarrow> \<phi>\<close> ("\<^bold>'(_\<^bold>')")
syntax (output) "_explicitParen" :: \<open>\<phi> \<Rightarrow> \<phi>\<close> ("'(_')")
translations
  "_explicitParen x" == "CONST explicitParen x"
(*>*)
text\<open>A notable consequence of the theory of possible worlds outlined in section~\ref{PossibleWorldTheory}
and the necessary and sufficient conditions for relations to denote described in the previous section is
the fact that world-relative relations denote.

In particular, it can be derived that any denoting @{text \<open>\<lambda>\<close>}-expression can be relativized
to a possible world, i.e. (see~\nameref{AOT:w-rel:1} and~\nameref{AOT:w-rel:2}):

\begin{quote}
@{thm[display] "w-rel:1"[print_as_theorem, of \<phi> w]}
@{thm[display] "w-rel:2"[print_as_theorem, of \<phi> w]}
\end{quote}

This allows for a definition of world-relative relations as follows (see~\nameref{AOT:w-index}):

\begin{quote}
@{thm[display] "w-index"}
\end{quote}

Notably, it becomes a theorem that there exist @{emph \<open>rigidifying relations\<close>}.

A relation is @{emph \<open>rigid\<close>}, if exemplifying it is modally collapsed (see~\nameref{AOT:df-rigid-rel:1}):

\begin{quote}
@{thm[display] "df-rigid-rel:1"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "cqt:2[const_var]"[axiom_inst], print_as_theorem, of F]}
\end{quote}

And a relation @{term F} @{emph \<open>rigidifies\<close>} a relation @{term G}, just in case
@{term F} is rigid and exemplifying it is equivalent to exemplifying @{term G} (see~\nameref{AOT:df-rigid-rel:2}):

\begin{quote}
@{thm[display] "df-rigid-rel:2"[of F G]}
\end{quote}

World-relative relations can now be used as a witness to show that there exist
rigidifying relations (see~\nameref{AOT:rigid-der:3}):

\begin{quote}
@{thm[display] "rigid-der:3"[print_as_theorem, of G]}
\end{quote}

Rigidifying relations will play an important role in the construction of natural
numbers described in chapter~\ref{NaturalNumbers} and their existence previously
had to be ensured by stating this last theorem as axiom.
\<close>

subsection\<open>Sixteen Distinct Properties\<close>

text\<open>Another result that can be traced back directly to the construction of
the embedding is the derivation of a more refined theorem about minimal models
of AOT. While previously PLM merely derived that there are six distinct properties,
it is a natural consequence of our constructed models that there are at least
sixteen distinct properties. This is due to the fact that there need to be at least
two distinguishable individuals (discerned by being ordinary and being abstract) and
two possible worlds (required by the axiom asserting the existence of a contingently
non-concrete objects object as mentioned in~\ref{AxiomSystem}). Two possible worlds
imply that there are at least $2^2=4$ distinct propositions. Mapping two discernible objects
to 4 propositions can be done in $2^4=16$ distinct ways.

And indeed we could construct a proof in the system of AOT itself that verifies that
this is not a mere artifact of the model construction, but a proper theorem in AOT.
See~\nameref{AOT:sixteen} for a detailed (though somewhat tedious) proof.

Notably, this result also implies that there is at least $2^{16} = 65556$ distinct
abstract objects in minimal models of AOT. On the other hand, models that validate the
theory of natural numbers described in chapter~\ref{NaturalNumbers} involve at
least countably infinitely many ordinary objects\footnote{At least in the current construction.
A potential future version of the construction mentioned in section~\ref{NewNumberTheory}
may instead require at least countably infinitely many @{emph \<open>special urelements\<close>}, but not
ordinary objects.} and thereby uncountably many properties and abstract objects.

Before we proceed to discuss AOT's analysis of natural numbers in chapter~\ref{NaturalNumbers},
we describe the technical details of the implementation of AOT in our embedding
in the next chapter.
\<close>

chapter\<open>SSE of AOT in Isabelle/HOL\<close>text\<open>\label{SSEofAOT}\<close>

section\<open>Model Construction\<close>text\<open>\label{ModelConstruction}\<close>

text\<open>
While the precise model construction of the embedding can be found in~\ref{AOT:AOT_model},
this section provides a high-level description of this construction.
The general idea is based on Aczel models of AOT, which are extended
to accommodate for AOT's hyperintensional modal logic on the one hand and its
free logic for individual and relation terms on the other hand. Furthermore,
we use a system of type classes to construct relations of arbitrary arity as relations among
tuples of individuals.\footnote{However, for each fixed arity of relations
the type classes can be logically eliminated.}

Recall that, as mentioned in section~\ref{SSE:MetaModel}, we do not construct set-theoretic
models of AOT, but instead construct models of AOT in HOL, while any set-theoretic model of
HOL that validates our construction can be lifted to a set-theoretic model of AOT.
\<close>

subsection\<open>Aczel Models\<close>text\<open>\label{AczelModels}\<close>

text\<open>

\tikzset{font=\fontsize{8pt}{10pt}\selectfont}
\begin{figure}[H]
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

The general structure of our models is based on Aczel models (see~\cite{zalta1999}).
Aczel models are extensional models that validate both
the comprehension principle for abstract objects\footnote{The last axiom in section~\ref{AxiomSystem},
resp. \nameref{AOT:A-objects} in the embedding: @{thm "A-objects"[axiom_inst, print_as_theorem, of \<phi>]}}
and classical relation comprehension in the absence of encoding formulas.

Aczel models involve a domain of @{emph \<open>urelements\<close>} @{text U} that is split
into @{emph \<open>ordinary urelements\<close>} @{text C} and @{emph \<open>special urelements\<close>} @{term S}.
In the extensional, non-modal setting, the power set of the set of urelements suffices
for representing properties. Abstract objects in turn are modelled using the power set
of properties.

Furthermore, the models involve a (non-injective) mapping from abstract objects to
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

Furthermore, Aczel models validate a restricted version of relation comprehension.
Since the truth conditions of any exemplification formula solely depend on the urelement
associated with the exemplifying individual, any condition @{term \<phi>} on individuals that does not
contain encoding claims can equivalently be represented as a condition on urelements.
Therefore, for any such condition @{term \<phi>}, there exists a relation @{term F} that is exemplified
by exactly those objects that satisfy @{term \<phi>}: @{text \<open>\<exists>F\<forall>x([F]x \<equiv> \<phi>{x})\<close>}, given
that @{text \<phi>} does not involve encoding claims.

While Aczel models generally demonstrate that abstract objects and encoding can be
modelled without being subject to the Clark-Boolos paradox (recall~\ref{ClarkBoolosParadox}), there are
several issues that remain unaddressed, including:

  \<^item> AOT's relations are not extensional and not even merely intensional,
    but fully hyperintensional.
  \<^item> Complex individual and relation terms and the free logic of AOT are not modelled explicitly.
  \<^item> Relation comprehension for formulas in the absence of encoding formulas
    does not immediately cover all the base cases of axiomatically denoting relation
    terms as mentioned in section~\ref{AxiomSystem}.
  \<^item> Aczel models do not cover @{text n}-ary relations for @{text \<open>n \<ge> 2\<close>}.@{footnote \<open>While in an extensional
    setting they can be interpreted as sets of tuples of urelements, validating AOT's definition
    of relation identity in a hyperintensional context requires further care.\<close>}

Therefore, while the models used for our embedding inherit the idea of urelements
and a mapping from abstract objects to special urelements, we extend
the general model structure for our embedding.
\<close>

subsection\<open>Types of the Embedding\<close>text\<open>\label{TypesOfTheEmbedding}\<close>

text\<open>
The terms of AOT are represented in our embedding using the following types in the meta-logic:@{footnote \<open>Note
that types and objects have separate namespaces in Isabelle. Also recall the brief introduction to type classes
in section~\ref{ClassesAndLocales}.\<close>}

  \<^item> Type @{typ \<o>} for formulas, resp. propositions.
  \<^item> Type @{typ \<kappa>} for individual terms.
  \<^item> Type @{typ \<open><'a>\<close>} for relation terms. Here @{typ 'a} is a type variable that is
    restricted to types of class @{class AOT_\<kappa>s}, which is instantiated for @{typ \<kappa>} (yielding unary
    relations, resp. properties, as @{typ \<open><\<kappa>>\<close>}) and arbitrary tuples of type @{typ \<kappa>}
    (i.e. @{typ \<open><\<kappa>\<times>\<kappa>>\<close>} is used to represent two-place-relations, etc.).@{footnote \<open>Technically,
@{class AOT_\<kappa>s} is instantiated for products of a type of class @{class AOT_\<kappa>} and a type of @{class AOT_\<kappa>s}, while
@{class AOT_\<kappa>} abstracts the properties of type @{typ \<kappa>} (and is only instantiated for @{typ \<kappa>}).\<close>}

In the following, we will briefly explain how each of these types is constructed.@{footnote \<open>This
will involve introducing additional types, in particular for urelements, that will not
be used for representing terms of AOT directly, but merely to construct the types above.\<close>}
The language elements of AOT (i.e. atomic formulas, logical connectives, quantifiers, complex
individual and relation terms) can then be represented by introducing
constants that act on objects of these types. We will introduce a custom sub-grammar in the inner syntax
of Isabelle/HOL that approximates AOT's syntax and translates to terms involving these constants
(as outlined in section~\ref{SSESyntax}). We will then formulate specifications for the constants
that will allow us to derive the axiom system and deduction rules of AOT. The construction of the types
will ensure that there are suitable witnesses for these specifications.

The type class @{class AOT_Term} (see~\nameref{AOT:AOT_model.AOT_Term}) is used as
a common type class that is instantiated for each of the types above. It involves
a single parameter @{term AOT_model_denotes} of type @{typ \<open>'a \<Rightarrow> bool\<close>}, that determines
the meta-logical conditions under which a term of type @{typ 'a} denotes. We will explain
how @{term AOT_model_denotes} is instantiated for each type below.

The additional type @{typ \<open>'a AOT_var\<close>} is defined for each type @{typ 'a} of class @{class AOT_Term}
using the objects of type @{typ 'a}, for which @{term AOT_model_denotes} is @{term True}, as representation set (see~\nameref{AOT:AOT_model.AOT_var}).@{footnote \<open>Since
the representation set of a type in Isabelle/HOL cannot be empty, the type class @{class AOT_Term}
involves the assumption that there is an object for which @{term AOT_model_denotes} is @{term True},
which has to be proven for each instantiation of the type class and thereby can be assumed for
each type of class @{class AOT_Term}.\<close>}
This type is used to represent the variables of each of the types above, e.g.
@{typ \<open>\<kappa> AOT_var\<close>} will be the type of individual variables.  Thereby,
variables range exactly over the denoting objects at each type. To be used
in place of terms, a variable of type @{typ \<open>'a AOT_var\<close>} is mapped to its representation type @{typ 'a}
using the constant @{term AOT_term_of_var}.@{footnote \<open>Each @{command typedef} that defines
a type using a representation set automatically introduces morphisms, usually
prefixed with @{text \<open>Rep_\<close>} and @{text \<open>Abs_\<close>}, that map objects of the defined type
to objects of its representation set and vice-versa. In this case we chose the
custom names @{term AOT_term_of_var} and @{term AOT_var_of_term} instead of
@{text \<open>Rep_AOT_var\<close>} and @{text \<open>Abs_AOT_var\<close>}.\<close>}
\<close>
(*<*)
text\<open>
    The type class @{class AOT_Term} (see~\nameref{AOT:AOT_model.AOT_Term}) involves
    a single parameter @{term AOT_model_denotes} of type @{typ \<open>'a \<Rightarrow> bool\<close>}, that determines
    the conditions under which a term of type @{typ 'a} denotes.
    The representation set of type @{typ \<open>'a AOT_var\<close>} is the set of all objects of type
    @{typ 'a} that denote, i.e. for which @{term AOT_model_denotes} is @{term True}.@{footnote \<open>Since
    the representation set of a type in Isabelle/HOL cannot be empty, the type class @{class AOT_Term}
    involves the assumption that there is an object for which @{term AOT_model_denotes} is @{term True},
    which has to be proven for each instantiation of the type class and thereby can be assumed for
    each type of class @{class AOT_Term}.\<close>}

Implication is represented as a constant @{const AOT_imp} of type @{typ \<open>\<o> \<Rightarrow> \<o> \<Rightarrow> \<o>\<close>},
i.e. a function taking two formulas to a formula. Similarly,
negation and the necessity and actuality operators are constants of type @{typ \<open>\<o> \<Rightarrow> \<o>\<close>}.
are defined as functions taking of @{typ \<open>\<o> \<Rightarrow> \<o>\<close>}, i.e. taking formulas to formulas.

The following constants depend on a type variable @{typ 'a} that
ranges over types of class @{class AOT_Term}:

  \<^item> @{const AOT_forall} of type @{typ \<open>('a \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close>} represents the all-quantifier.
    It takes functions of type @{typ \<open>'a \<Rightarrow> \<o>\<close>} (i.e. functions mapping objects
    of type @{typ 'a} to propositions) to propositions.
  \<^item> @{const AOT_denotes} of type @{typ \<open>'a \<Rightarrow> \<o>\<close>} represents the downarrow operator.
  \<^item> @{const AOT_eq} of type @{typ \<open>'a \<Rightarrow> 'a \<Rightarrow> \<o>\<close>} represents identity.

Furthermore, the following constants depend on a type variable @{typ 'a} that
ranges over types of class @{class AOT_\<kappa>s}:
  \<^item> @{const AOT_exe} of type @{typ \<open><'a> \<Rightarrow> 'a \<Rightarrow> \<o>\<close>} represents exemplification.
  \<^item> @{const AOT_lambda} of type @{typ \<open>('a \<Rightarrow> \<o>) \<Rightarrow> <'a>\<close>} represents @{text \<open>\<lambda>\<close>}-abstraction.
  \<^item> @{const AOT_enc} of type @{typ \<open>'a \<Rightarrow> <'a> \<Rightarrow> \<o>\<close>} represents encoding.
\<close>
(*>*)

subsection\<open>Hyperintensional Propositions\<close>text\<open>\label{HyperintensionalPropositions}\<close>

text\<open>
The hyperintensionality of AOT is modelled at the level of propositions.
The construction follows the general method outlined in section~\ref{Specifications}.

The type @{typ \<o>} is introduced as a primitive type (see~\nameref{AOT:AOT_model.<o>}).
It is used to represent hyperintensional propositions and is associated with modal extensions
following Kripke semantics: a primitive type @{typ w} for semantic possible
worlds is introduced (see~\nameref{AOT:AOT_model.w}) and it is axiomatized that
there be a surjective mapping @{term AOT_model_d\<o>} from propositions of type @{typ \<o>}
to Kripke-extensions, i.e. boolean valued functions on possible worlds (type @{typ \<open>w\<Rightarrow>bool\<close>};
see~\nameref{AOT:AOT_model.AOT_model_d<o>}).

We define for a proposition @{term \<phi>} of type @{typ \<o>} to be valid in a given semantic possible
world @{term v} (written @{term \<open>AOT_model_valid_in v \<phi>\<close>})\footnote{Note that this use of the double turnstile symbol
@{text \<open>\<Turnstile>\<close>} is defined within the meta-logic HOL and distinct from the use in AOT's possible world theory described in section~\ref{PossibleWorldTheory}.}, just in case @{term AOT_model_d\<o>} maps @{term p}
to a Kripke-extension that evaluates to @{term True} for @{term v} (see~\nameref{AOT:AOT_model.AOT_model_valid_in}).

This way, our type of propositions @{typ \<o>} is assured to contain a proposition for
each Kripke-extension, but does not require the collapse of necessarily
equivalent propositions:

For any given Kripke-extension @{term \<phi>}, the inverse of @{term AOT_model_d\<o>}
yields a proposition of type @{term \<o>} that is valid in exactly those worlds
for which @{term \<phi>} evaluates to @{term True} (see~\nameref{AOT:AOT_model.AOT_model_proposition_choice}).\footnote{This
fact relies on the surjectivity of @{const AOT_model_d\<o>}. The embedding introduces the notation @{text \<open>\<epsilon>\<^sub>\<o> w . \<phi> w\<close>}
for the proposition given by @{term \<open>inv AOT_model_d\<o> \<phi>\<close>}. We will use such propositions during witness proofs in
specifications.}

However, the construction allows for the type @{typ \<o>} to contain more propositions
than there are Kripke-extensions. I.e there may be two distinct
objects @{term p} and @{term q} of type @{typ \<o>} that are necessarily equivalent,
i.e. they are valid in the same semantic possible worlds. This can be confirmed by
@{command nitpick}:
\<close>

lemma \<open>\<forall> v . [v \<Turnstile> p] \<longleftrightarrow> [v \<Turnstile> q]\<close> and \<open>p \<noteq> q\<close>
  nitpick[satisfy, user_axioms, expect=genuine](*<*)oops(*>*)

text\<open>
@{command nitpick} can find a model in which @{term p} and @{term q} are represented
by two distinct objects, while both of them have the same Kripke-extension
under @{term AOT_model_d\<o>}.

Note, however, that the construction also @{emph \<open>allows\<close>} for necessary equivalent
propositions to be collapsed:
\<close>

lemma \<open>\<forall> p q . (\<forall> v . [v \<Turnstile> p] \<longleftrightarrow> [v \<Turnstile> q]) \<longrightarrow> p = q\<close>
  nitpick[satisfy, user_axioms, expect=genuine](*<*)oops(*>*)

text\<open>
In this case @{command nitpick} chooses a model in which the type @{typ \<o>} is
isomorphic to the type of Kripke-extensions @{typ \<open>w \<Rightarrow> bool\<close>}, i.e. there are
just as many objects of type @{typ \<o>} as there are Kripke-extensions.

Just as AOT itself, the model construction does not presuppose the degree of hyperintensionality of
propositions.

To instantiate the type class @{class AOT_Term} for type @{typ \<o>}, we need to define
the conditions under which propositions denote. Since in AOT all formulas denote,
@{term AOT_model_denotes} is @{term True} for all objects of type @{typ \<o>}.
Consequently, the type @{typ \<open>\<o> AOT_var\<close>} is isomorphic to the type @{typ \<o>}.

On top of this hyperintensional type of propositions, the logical connectives will later be
defined by @{command specification} as outlined in section~\ref{Specifications}.

Notably, previous versions of our embedding (in particular the construction in~\cite{MScThesis}),
modelled hyperintensionality more explicitly by using an additional primitive type @{text s} of
@{emph \<open>intensional states\<close>}. Propositions were modelled explicitly as boolean-valued functions acting
on states and possible worlds (type @{text \<open>s \<Rightarrow> w \<Rightarrow> bool\<close>}). Semantic validity was
defined using the evaluation of propositions in a designated @{emph \<open>actual\<close>} state. The logical
connectives were defined to have classical behaviour in the actual state, while their behaviour
was left unspecified in non-actual states. While such an explicit construction
using intensional states can still serve as a concrete model for our abstract type 
@{typ \<o>}, the fact that AOT does not presuppose any additional structure on non-actual
states allowed us to replace the explicit construction by the described more general abstraction.
\<close>

subsection\<open>Extended Aczel Model Structure\<close>text\<open>\label{ExtendedAczelModelStructure}\<close>

text\<open>
Our representation is based on Aczel models, so the construction of the types
of individuals and relations relies on urelements.

The embedding introduces a type of urelements @{typ \<upsilon>} (see~\nameref{AOT:AOT_model.<upsilon>})
that is comprised of three separate kinds of urelements:

  \<^item> Ordinary urelements of type @{typ \<omega>} (see~\nameref{AOT:AOT_model.<omega>}),
  \<^item> Special urelements of type @{typ \<sigma>} (see~\nameref{AOT:AOT_model.<sigma>}) and
  \<^item> Null-urelements of type @{typ null} (see~\nameref{AOT:AOT_model.null}).

Following the structure of Aczel models, ordinary urelements are used to model
ordinary objects and special urelements determine the exemplification behaviour of
abstract objects. The additional null-urelements are introduced to be able to
distinguish between non-denoting individual terms (see below).

For simple models, the types of ordinary, special and null urelements can all remain
purely abstract types.@{footnote \<open>I.e. a model of HOL may choose (non-empty) domains of any size
for each kind of urelements. In chapter~\ref{NaturalNumbers} we will discuss a more specific construction
that is required to validate the additional axioms needed for the construction of natural numbers.\<close>}

Hyperintensional relations are modelled as proposition-valued functions.
In particular, the embedding introduces the type @{typ urrel} (see~\nameref{AOT:AOT_model.urrel})
that is represented by the set of all functions from urelements to propositions (type
@{typ \<open>\<upsilon> \<Rightarrow> \<o>\<close>}), which map null-urelements to necessarily false propositions.@{footnote \<open>Note
that our construction allows for multiple distinct propositions that are necessarily false.\<close>}
This type of @{emph \<open>urrelations\<close>} will be in one-to-one correspondence with the denoting property terms, i.e.
denoting objects of type @{typ \<open><\<kappa>>\<close>}, respectively objects of type @{typ \<open><\<kappa>> AOT_var\<close>}.

The additional null-urelements serve to avoid two kinds of artifactual theorems:
  \<^item> Let @{term p} be the proposition denoted by the term \<^term>\<open>print_term \<guillemotleft>[F]\<^bold>\<iota>x \<phi>{x}\<guillemotright>\<close>
    and let @{term q} be the proposition denoted by the term \<^term>\<open>print_term \<guillemotleft>[F]\<^bold>\<iota>x \<psi>{x}\<guillemotright>\<close>.
    Furthermore, assume that provably neither of the descriptions denote,
    i.e. both \<^term>\<open>print_term \<guillemotleft>\<not>\<^bold>\<iota>x(\<phi>{x})\<down>\<guillemotright>\<close> and  \<^term>\<open>print_term \<guillemotleft>\<not>\<^bold>\<iota>x(\<psi>{x})\<down>\<guillemotright>\<close> are theorems.
    Now while AOT requires @{term p} and @{term q} to be necessarily equivalent,
    in particular they are both necessarily false, it does not (in general) presuppose that @{term p} is
    @{emph \<open>identical\<close>} to @{term \<open>q\<close>}.@{footnote \<open>An example of an exception is the case in which the matrices
    are alphabetic variants of each other or can be transformed into each other by substituting identical subterms,
    in which case @{term \<phi>} and @{term \<psi>} are also meta-logically identical.\<close>} In the embedding this is achieved by allowing
    descriptions (with distinct matrices) to be mapped to distinct null-urelements to which the urrelation
    corresponding to @{term F} can assign distinct (albeit necessarily false)
    propositions.@{footnote \<open>Note that this is not a mere technicality, but it may be desirable
    to distinguish e.g. between the proposition @{emph \<open>The number smaller than 3 is a natural number\<close>} (which fails due
    to there not being a unique such number) and @{emph \<open>The number greater than 3 and smaller than 2 is a natural number\<close>} (which
    fails due to there not being any such number). Furthermore, it might make sense to consider
    the proposition @{emph \<open>The present king of France is a natural number\<close>} to be an entirely different
    proposition than the first two. The embedding allows to assign each of the non-denoting definite descriptions
    distinct null-urelements and thereby allows the propositions to differ. However, it also allows to choose
    a model with only a single null-urelement which would collapse these propositions.\<close>}
    While artifactual theorems of this kind could also be avoided by merely allowing exemplification formulas
    to choose distinct propositions for distinct non-denoting terms, this would not be sufficient to avoid
    the second kind of artifactual theorems:
  \<^item> In AOT there may be distinct properties, s.t. for any object exemplifying either of
    them necessarily results in the same proposition. I.e. @{term \<open>print_as_theorem \<guillemotleft>\<forall>x \<box>\<^bold>(([F]x) = ([G]x)\<^bold>)\<guillemotright>\<close>}
    does @{emph \<open>not\<close>} imply @{term \<open>F = G\<close>}. The @{text \<open>\<forall>\<close>}-quantifier ranges over all denoting
    individuals. If relations were merely modelled as functions from urelements that
    correspond to denoting individual terms to propositions, the identity would follow,
    since two functions are identical, if they agree on all arguments.
    By introducing null-urelements, however, we allow @{term F} and @{term G} to vary
    on additional urelements outside of the range of the quantifier.@{footnote \<open>An alternative approach
    would be to introduce a primitive type of relations that is merely assigned a proposition-valued
    function as extension, similarly to how Kripke-extensions are assigned to the primitive type of
    propositions. However, this would require a polymorphic axiomatization to account for relations
    of all arities which is incompatible with the model-checking tool @{command nitpick}. Even
    only axiomatizing a finite subset of all arities would require @{command nitpick} to construct
    significantly larger models and thereby diminish its usefulness. Furthermore, this construction
    would further complicate validating the definition of @{text n}-ary relation identity.\<close>}

Note that the additional null-urelements have no impact on
minimal models of AOT. In minimal models, propositions are
in one-to-one correspondence to Kripke-extensions: for every boolean valued function
on possible worlds there is exactly one proposition.
While urrelations have to assign propositions to null-urelements,
by construction, urrelations are required to evaluate to necessarily false propositions on null-urelements.
Hence, there is only one choice for doing so, namely the single proposition with the constant-false function
as Kripke-extension. Consequently, the number of relations in minimal models of AOT is unaffected. 

As a last ingredient of our Aczel model structure, we require a mapping @{text \<alpha>\<sigma>}
from sets of urrelations (which will be used to represent abstract objects) to
special urelements (see~\nameref{AOT:AOT_model.<alpha><sigma>}). As in the basic Aczel
model construction, this mapping will determine the exemplification behavior of abstract
objects.

For urrelations to become a proper quotient of proposition-valued functions acting
on individual @{emph \<open>terms\<close>}, as described below, we require this mapping to be
surjective. However, we can show that any mapping @{term \<open>\<alpha>\<sigma>'\<close>} from sets of urrelations to
special urelements can be extended to a surjective mapping
@{term \<open>\<alpha>\<sigma>\<close>} that distinguishes all abstract objects that are distinguished by
@{term \<open>\<alpha>\<sigma>'\<close>}, i.e. if @{term \<open>\<alpha>\<sigma>' x \<noteq> \<alpha>\<sigma>' y\<close>}, then @{term \<open>\<alpha>\<sigma> x \<noteq> \<alpha>\<sigma> y\<close>}.
This is possible due to the fact that the set of abstract objects is significantly
larger than the set of special urelements. In particular, under any arbitary
mapping from abstract objects to special urelements, there has to be at least
one abstract object @{term a} that shares the same urelement with more
other abstract objects than there are special urelements (proof by a pigeonhole-style argument,
see~\nameref{AOT:AOT_model.<alpha><sigma>_pigeonhole}).
Therefore, any mapping @{term \<alpha>\<sigma>'} that is not surjective, can be extended to a surjective
mapping by further differentiating the abstract objects that share their urelements with @{term a}.

To keep the construction as flexible as possible, we first introduce an uninterpreted
constant @{term \<alpha>\<sigma>'} and then generically extend it to a surjective
mapping @{term \<alpha>\<sigma>} (see~\nameref{AOT:AOT_model.<alpha><sigma>'}).

To validate extended relation comprehension we can then augment @{term \<alpha>\<sigma>'} using a
suitable @{command specification}. The precise construction of @{term \<alpha>\<sigma>'} needed for
extended relation comprehension is discussed in more detail in section~\ref{pred}.

Additionally, we introduce the constant @{const AOT_model_concrete\<omega>} (see~\nameref{AOT:AOT_model.AOT_model_concrete<omega>})
and specify it in such a way, that (1) for every object @{term x} (of type @{typ \<omega>}) there is a possible world @{term w} (of type @{typ w}), s.t.
@{term \<open>AOT_model_concrete\<omega> x w\<close>} and (2) there is an object @{term x} and a possible world @{term w}, s.t.
@{term \<open>AOT_model_concrete\<omega> x w \<and> \<not>AOT_model_concrete\<omega> x w\<^sub>0\<close>} (where @{term w\<^sub>0} is the designated actual world).
This constant will be used to construct AOT's relation of being concrete. The specified properties ensure that
objects of type @{typ \<omega>} will be possibly concrete, i.e. ordinary, and that there possibly is an object that is concrete, but not actually
concrete, which is asserted by AOT as an axiom. A function that is true
for an object @{term x} (of type @{typ \<omega>}) and a semantic possible world @{term w} (of type @{typ w}),
just in case @{term w} is not the actual world @{term w\<^sub>0}, can serve as witness for the specification.@{footnote \<open>Note that we have to assert
the existence of a non-actual world using a meta-logical axiom, see~\nameref{AOT:AOT_model.AOT_model_nonactual_world}.
Also note that this construction does not imply that in our embedding no objects will be actually concrete and
all ordinary objects will be concrete in all non-actual worlds. While our witness has this additional property, a model
of HOL may choose any denotation for @{const AOT_model_concrete\<omega>} that merely satisfies the properties of the specification.\<close>}

Based on the type of urelements @{typ \<upsilon>} and the type of urrelations @{typ urrel}
we can construct the type @{typ \<kappa>} of individual terms.
\<close>

subsection\<open>Individual Terms and Properties\<close>

text\<open>
The type @{typ \<kappa>} (see~\nameref{AOT:AOT_model.<kappa>}) consists of ordinary objects of type @{typ \<omega>} (shared with ordinary
urelements), abstract objects modelled as sets of urelements (type @{typ \<open>urrel set\<close>})
and null-objects of type @{typ null} (shared with null-urelements) that will
serve to model non-denoting definite descriptions. We can lift the surjective
mapping from abstract objects to special urelements @{text \<alpha>\<sigma>} to a surjective mapping @{text \<kappa>\<upsilon>}
from individual terms to urelements (i.e. type \mbox{@{typ \<open>\<kappa> \<Rightarrow> \<upsilon>\<close>}}) (see~\nameref{AOT:AOT_model.<kappa><upsilon>}),
s.t. for any urelement we can find an object of type @{typ \<kappa>} that is mapped to that urelement (see~\nameref{AOT:AOT_model.<kappa><upsilon>_surj}).

To instantiate the type class @{class AOT_Term} for type @{typ \<kappa>}, we define
@{term AOT_model_denotes} to be @{term True} for exactly those objects of type @{typ \<kappa>} that
are not null-objects.

Relation terms will be defined relative to types of a type class that
abstracts individuals and tuples of individuals. We will explain this generic construction
below. However, it may be helpful to first consider the case of properties (i.e.
type @{typ \<open><\<kappa>>\<close>}) specifically, even though in the embedding this case will only occur
as a special case of the generic construction.

Property terms (of type @{typ \<open><\<kappa>>\<close>}) are represented by proposition-valued functions acting
on individuals (type @{typ \<open>\<kappa> \<Rightarrow> \<o>\<close>}). A property term @{emph \<open>denotes\<close>}, if its representing function
@{term \<phi>} satisfies the following conditions:

  \<^item> @{term \<open>\<phi> \<kappa> = \<phi> \<kappa>'\<close>}, whenever @{term \<open>\<kappa>\<upsilon> \<kappa> = \<kappa>\<upsilon> \<kappa>'\<close>}, i.e. @{term \<phi>} evaluates to the
    same propositions for objects that have the same urelements.
  \<^item> @{term \<phi>} evaluates to necessarily false propositions for objects of type @{typ \<kappa>} that do not denote.

Consequently, since @{term \<kappa>\<upsilon>} is surjective and urrelations have the property to be necessarily
unexemplified on null-urelements, denoting property terms are in one-to-one correspondence
with urrelations (see~\nameref{AOT:AOT_model.rel_to_urrel}).
This is crucial for constructing encoding and validating the comprehension principle of
abstract objects, since abstract objects are modelled as sets of urrelations.

We can now now construct a function that can later serve as witness for our specification of exemplification.
For a property term @{term \<Pi>} and an individual term @{term \<kappa>}, we can choose a proposition @{term p}, such that:
  \<^item> If @{term \<Pi>} denotes, then @{term \<open>p = Rep_rel \<Pi> \<kappa>\<close>}, i.e. the proposition resulting from
    applying the function representing @{term \<Pi>} to @{term \<kappa>}. This proposition will, by construction,
    be necessarily false, if @{term \<kappa>} does not denote.
  \<^item> @{term p} is a necessarily false proposition otherwise.

Furthermore, the construction allows to define the meta-logical truth conditions of encoding as follows:
@{term \<kappa>} encodes @{term \<Pi>} just in case that (1) @{term \<Pi>} denotes, (2) @{term \<kappa>} is represented by an abstract object @{term x} and
(3) the urrelation corresponding to @{term \<Pi>} is contained in @{term x}.
\<close>
subsection\<open>Type Classes for Individual Terms\<close>text\<open>\label{IndividualTermsAndClasses}\<close>

(*<*)
text\<open>

We introduce a system of @{emph \<open>type classes\<close>} that abstract over
concrete types for two reasons (see section~\ref{ClassesAndLocales} for a
brief discussion of type classes):
  \<^item> AOT involves axioms and theorems with (meta-)variables that may be instantiated
    to terms of several different types. In order to avoid having to restate multiple
    instances of such statements we formulate type classes that abstract over the
    required shared properties of all admissible types and prove the respective
    statements relative to this type class. The type class itself is then instantiated to all concrete types
    that satisfy the necessary requirements.
  \<^item> AOT involves statements about @{text n}-ary relations for arbitrary @{text \<open>n \<ge> 0\<close>},
    so to cover the full extent of such statements, listing all concrete instances
    would be impossible. Instead we model relations as proposition-valued functions
    acting on any type of an abstract type class of individual terms and then show that the product of an unary
    individual term (which constitutes another more restricted type class which
    abstracts the distinctive properties of the concrete type @{typ \<kappa>}) and another
    individual term (which may itself be an unary individual term or a product) again
    satisfies the requirements of the type class of individual terms. This way
    any statement about relations on a type of this class of individual terms implicitly holds
    for relations among arbitrarily large tuples of objects of type @{typ \<kappa>}, i.e.
    we can capture statements about arbitrary @{text n}-ary relations.

The most basic type class we introduce is @{class AOT_Term} (see~\nameref{AOT:AOT_model.AOT_Term}).
It involves an abstract notion of a term to denote @{const AOT_model_denotes} for which
it is merely required that it is satisfied by at least one object. For type @{typ \<kappa>}
@{const AOT_model_denotes} is true for all objects that are not null-objects.
We will define quantifiers relative to this type class and derive the quantifier axioms, which are
independent of the concrete definition of the conditions under which an object of any
concrete type denotes.@{footnote \<open>Similarly, we can define equality on the class @{class AOT_Term}
and formulate the substitution of identicals relative to it. To validate AOT's definitions of identity
we then show that meta-logical identity coincides with AOT's defined identity on denoting terms.\<close>}
\<close>
(*>*)
text\<open>
The type class @{class AOT_\<kappa>s} is a combination of three more specific type classes:

@{class AOT_IndividualTerm} (see~\nameref{AOT:AOT_model.AOT_IndividualTerm}),
@{class AOT_RelationProjection} (see~\nameref{AOT:AOT_semantics.AOT_RelationProjection})
and @{class AOT_Enc} (see~\nameref{AOT:AOT_semantics.AOT_Enc}).
The latter two formulate conditions on relations among objects of their type variable. Therefore,
they can only be formulated after a type of relations is introduced. The type of relations itself will
be defined relative to the class @{class AOT_IndividualTerm}.

The most important parameter of this class is @{const AOT_model_term_equiv}, an
equivalence relation which is satisfied for two objects, if they have common urelements.@{footnote \<open>Note that an @{emph \<open>object\<close>} of a type
of class @{class AOT_IndividualTerm} may itself e.g. be a pair of two objects of type @{typ \<kappa>}, since
the product of @{typ \<kappa>} with itself, i.e. type @{typ \<open>\<kappa>\<times>\<kappa>\<close>}, is also of class @{class AOT_IndividualTerm}.
@{const AOT_model_term_equiv} for pairs is defined as the conjunction of @{const AOT_model_term_equiv} on both projections. Consequently,
two tuples @{text \<open>(\<kappa>\<^sub>1,...\<kappa>\<^sub>n)\<close>} and @{text \<open>(\<kappa>\<^sub>1',...\<kappa>\<^sub>n')\<close>} of objects of type @{typ \<kappa>} are @{term AOT_model_term_equiv}-equivalent if
for all @{text \<open>1 \<le> i \<le> n\<close>}, @{term \<kappa>\<^sub>i} has the same urelement as @{term \<kappa>\<^sub>i'}.\<close>}
We furthermore introduce the notion of individual terms to be @{emph \<open>regular\<close>} and
specify a transformation of proposition-valued functions acting on individual terms, s.t.
after the transformation the behaviour of the function is solely determined by
its values on regular terms. This will be relevant for the definition of
@{text n}-ary relation identity (see~\ref{nary}). An unary individual term (i.e. an object of type @{typ \<kappa>}) is always
regular, while a tuple will only be regular, if at most one of its elements does not
denote.

In the next section, we will introduce relations as proposition-valued functions acting on objects of
sort @{class AOT_IndividualTerm}. The class @{class AOT_RelationProjection} defines an abstract notion of
projections of relations that will be relevant for defining @{text n}-ary relation identity.
The class @{class AOT_Enc} defines an abstract notion of encoding.
Encoding for type @{typ \<kappa>} is specified as explained in the last section, while for tuples
it is constructed in such a way that the axiom of @{text n}-ary encoding will become derivable.
Together, the three type classes form the class @{class AOT_\<kappa>s}.

In the formulation of the axiom system, individuals in ellipses notation will be allowed to
have any type of class @{class AOT_\<kappa>s},
and relations will be assumed to act on any type of class @{class AOT_\<kappa>s}.@{footnote \<open>Unless a statement
involves explicit exemplification or encoding formulas that imply restrictions on the type, e.g. a particular arity.\<close>} This
way axioms about relations can be stated for all arities at the same time (since the
concrete type of individuals @{typ \<kappa>} as well as arbitrary iterated products of it, e.g.
@{typ \<open>\<kappa>\<times>\<kappa>\<times>\<kappa>\<close>}, are all of class @{class AOT_\<kappa>s}).
\<close>
subsection\<open>Generic Relation Terms\<close>text\<open>\label{RelationsAsPropositionValuedFunctions}\<close>
text\<open>
The generic type of relation terms is defined as the type of
proposition-valued functions acting on a type of class @{class AOT_IndividualTerm}
(see~\nameref{AOT:AOT_model.rel}).

To instantiate the type class @{class AOT_Term} to our generic type of relation terms,
we have to define the conditions under which a relation term denotes.

A relation term denotes, if it is represented by a proposition-valued functions @{term \<phi>} on
individual terms, such that (see~\nameref{AOT:AOT_model_denotes_rel}):
  \<^item> @{term \<phi>} agrees on @{const AOT_model_term_equiv}-equivalent terms, i.e. it evaluates to the same proposition for
    individual terms that share the same urelements.
  \<^item> For non-denoting individual terms, @{term \<phi>} evaluates to necessarily false propositions.
  \<^item> @{term \<phi>} is well-behaved on irregular terms (i.e. on irregular terms it evaluates
    to the proposition given by @{term \<open>AOT_model_irregular \<phi>\<close>}, which solely depends
    on @{term \<phi>}'s behaviour on regular terms). This will be important to validate the
    definition of @{text n}-ary relation identity and is discussed in section~\ref{nary}.
    Note that since unary individual terms, i.e. objects of type @{typ \<kappa>}, are always
    regular, this restriction does not apply to properties of type @{typ \<open><\<kappa>>\<close>}.

Consequently, exemplification of denoting relation terms, can (as already indicated for the unary case)
simply be modelled by the application of the proposition-valued function representing the
relation term to the given individual term (which may be a tuple of terms of type @{typ \<kappa>}),
while exemplifying non-denoting relation terms yields a necessarily false
proposition.@{footnote \<open>By @{emph \<open>can be modelled\<close>} here we mean that we can construct a witness
for the semantic specification of exemplification.\<close>}

Generic encoding was already described in the last section.

We now have constructed all the required types and prepared the required witnesses
for constructing an abstract semantics of AOT using specifications in section~\ref{Semantics}.
However, this semantics is formulated using our implementation of AOT's syntax,
so in the following two sections we will first
briefly discuss how we extend Isabelle's inner syntax by an approximation of the syntax
used in PLM and how we extend Isabelle's outer syntax by custom commands used for
structured reasoning in the embedding.
\<close>

(*<*)
setup\<open>
let
val antiquotation_pretty_source = Document_Output.antiquotation_pretty_source
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
setup\<open>
let
val antiquotation_pretty_source = Document_Output.antiquotation_pretty_source
in
antiquotation_pretty_source
end @{binding "ML_print_term'"} Args.term (
fn ctxt => fn trm => 
  Pretty.chunks [
  Pretty.markup_block {consistent = true, indent = 8, markup = Markup.ML_string}
    [Pretty.str (ML_Pretty.string_of_polyml (ML_system_pretty (trm, FixedInt.fromInt 100)))]]
)\<close>
(*>*)

section\<open>Syntax of the Target Theory\<close>text\<open>\label{AOTSyntax}\<close>

text\<open>
We already discussed the possibility of extending Isabelle's inner syntax in general
in section~\ref{SSESyntax}. Following the method described in that section, we introduce
@{type AOT_prop} as syntactic root type for propositions in AOT (see~\ref{AOT:AOT_commands}) and define a custom grammar
for AOT on top of it (see~\ref{AOT:AOT_syntax}). However, Isabelle's high-level mechanisms for defining
custom syntax have certain limitations that make an accurate representation of
AOT's syntax challenging.

In particular, Isabelle's lexical analysis is not designed to be configurable.
It presupposes that identifiers consist of multiple characters and have to be
delimited by whitespace or certain delimiter tokens.

While requiring identifiers to be delimited can be considered as a reasonable syntactic
concession, we found that reproducing the compact form of atomic formulas used in PLM
results in significantly improved readability.

Therefore we utilize Isabelle's low-level mechanisms to customize syntax by providing
transformations on its abstract syntax tree and its term representation written in Standard ML.

In particular, we use @{command parse_ast_translation}s and @{command parse_translation}s (see~\S8.4 in~\cite{IsarRef})
to split what Isabelle would natively regard as a single identifier. That way we are
able to e.g. translate the term @{term \<open>print_as_theorem \<guillemotleft>[\<Pi>]\<kappa>\<kappa>'\<guillemotright>\<close>} to
@{text \<open>AOT_exe \<Pi> (\<kappa>,\<kappa>')\<close>}. The 2-ary exemplification formula is translated to
an application of the constant @{const AOT_exe} to the relation term and a tuple of
individual terms. Similarly, @{term \<open>print_as_theorem \<guillemotleft>\<kappa>\<kappa>'[\<Pi>]\<guillemotright>\<close>} is translated to
@{text \<open>AOT_enc (\<kappa>,\<kappa>') \<Pi>\<close>}. Involved constants are introduced in~\ref{AOT:AOT_syntax}
as uninterpreted constants (see~\nameref{AOT:AOT_syntax.AOT_denotes}), which are only
later enriched with semantic structure using @{command specification}s (see~\ref{AOT:AOT_semantics} and section~\ref{Semantics}).@{footnote \<open>The type
construction discussed in the previous section allows us to construct witnesses for these specifications.\<close>}

Furthermore, PLM associates the symbols used for its terms with their types, as described in
section~\ref{AOTLanguage}. While it is possible to rely on Isabelle's type inference in most cases,
this will not always result in correctly typed terms without additional type annotations
which would negatively affect readability.

For that reason, we construct an extensible system for typing terms based on their names.
In particular we introduce the command @{command AOT_register_type_constraints} that
can be used to introduce named categories of types and equip them with type constraints
both for unary terms and tuples. We then allow registering symbols as variables and
meta-variables of a given category with @{command AOT_register_variable_names} and
@{command AOT_register_metavariable_names}. The extensible design allows for reproducing
AOT's concept of @{emph \<open>restricted variables\<close>} (see~\ref{RestrictedVariables}) by further
associating a term category with a restriction condition (see~\ref{AOT:AOT_RestrictedVariables}).@{footnote \<open>The restriction
condition will be added when parsing quantifiers using restricted variables. For rigidly restricted variables a sub-type is
introduced that is restricted to all terms that satisfy the restriction condition, allowing to add the restriction condition as
axiom for objects of this restricted type.\<close>}

A danger in the extensive use of complex custom syntax is silent errors in the syntactic
translations that could result in an expression to be parsed contrary to their intended
meaning. To alleviate this danger we define multiple @{emph \<open>printing modes\<close>}. The
embedding can be configured to print terms in an approximation of AOT's syntax, e.g.:
\begin{quote}
@{term[display] \<open>\<guillemotleft>[\<Pi>]\<kappa>y \<rightarrow> (p \<or> \<phi>)\<guillemotright>\<close>}
\end{quote}
using @{emph \<open>meta-syntax\<close>}, an enriched version of HOL's syntax without complex transformations, e.g.:
\<close>(*<*) unbundle AOT_no_syntax context AOT_meta_syntax begin (*>*)text\<open>
\begin{quote}
@{term[display] \<open>\<guillemotleft>[\<Pi>]\<kappa>y \<rightarrow> (p \<or> \<phi>)\<guillemotright>\<close>}
\end{quote}

or as plain HOL terms without any syntactic sugar, e.g.:\<close>(*<*) end (*>*)text\<open>
\begin{quote}
@{term[display] \<open>\<guillemotleft>[\<Pi>]\<kappa>y \<rightarrow> (p \<or> \<phi>)\<guillemotright>\<close>}
\end{quote}
\<close>
(*<*) unbundle AOT_syntax (*>*)
text\<open>

Note that while the meta-syntax already involves distracting complexities like the
annotation of non-meta-variables using @{text \<open>\<langle>_\<rangle>\<close>}, additional explicit syntax for
exemplification @{text \<open>\<^bold>\<lparr>_,_\<^bold>\<rparr>\<close>} and explicit tuples, plain HOL syntax quickly
becomes unreadable for complex terms.

For the purpose of implementing a full theory with an extensive body of theorems,
we contend that the improved readability outweighs the potential danger of complex
syntax transformations, especially given the ability to confirm the accuracy of
the translation using less complex printing modes.
\<close>

section\<open>Extending Isabelle's Outer Syntax\<close>text\<open>\label{AOTOuterSyntax}\<close>

text\<open>

While the syntax transformations described in the last section go a long way in
allowing the intuitive statement of terms and formulas of AOT, @{emph \<open>reasoning\<close>}
in the target logic entails additional challenges.

For example, reasoning in the embedding involves keeping track of the semantic
possible world in which statements are valid. To avoid this cognitive overhead,
we implement a copy of Isabelle's Isar language in Standard ML that automatically
handles semantic possible worlds and allows theorem statements and proofs to be
transferred directly from and to PLM without the need of explicitly mentioning semantic possible
worlds.

While modally-strict theorems of PLM are valid in all semantic possible worlds,
conceptually its proofs work relative to an arbitrary but fixed world.
For proving a necessary fact during a proof, e.g. @{term \<open>\<guillemotleft>\<box>\<phi>\<guillemotright>\<close>}, PLM often reasons by
providing a @{emph \<open>modally-strict\<close>} sub-proof of @{term \<phi>} and appealing to the rule RN.
In our embedding we reproduce this by introducing an outer syntax command @{command "AOT_modally_strict {"} that
opens a block of reasoning relative to a fresh possible world. For example:
\<close>

AOT_theorem \<open>\<box>(\<not>\<phi> & \<not>\<psi>) \<rightarrow> \<box>(\<phi> \<equiv> \<psi>)\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<box>(\<not>\<phi> & \<not>\<psi>)\<close>
  \<comment> \<open>Start a modally-strict sub-proof.\<close>
  AOT_modally_strict {
    AOT_assume \<open>\<not>\<phi> & \<not>\<psi>\<close>
    AOT_hence \<open>\<phi> \<equiv> \<psi>\<close>
      by (metis "&E" "\<rightarrow>I" "\<equiv>I" "reductio-aa:1")
  }
  \<comment> \<open>Conclude the necessitation of the result by RN.\<close>
  AOT_hence \<open>\<box>((\<not>\<phi> & \<not>\<psi>) \<rightarrow> (\<phi> \<equiv> \<psi>))\<close>
    by (metis "\<rightarrow>I" RN)
  AOT_thus \<open>\<box>(\<phi> \<equiv> \<psi>)\<close> using 0 "qml:1"[axiom_inst] "\<rightarrow>E" by blast
qed


text\<open>
This corresponds to the following proof using Isabelle's native outer syntax:
\<close>

\<comment> \<open>We formulate the statement relative to a fixed, but arbitrary world @{term v}.\<close>
theorem \<open>[v \<Turnstile> \<box>(\<not>\<phi> & \<not>\<psi>) \<rightarrow> \<box>(\<phi> \<equiv> \<psi>)]\<close>
proof(rule "\<rightarrow>I")
  assume 0: \<open>[v \<Turnstile> \<box>(\<not>\<phi> & \<not>\<psi>)]\<close>
  {
    fix w \<comment> \<open>We choose a fresh possible world for our sub-proof.\<close>
    assume \<open>[w \<Turnstile> \<not>\<phi> & \<not>\<psi>]\<close>
    hence \<open>[w \<Turnstile> (\<phi> \<equiv> \<psi>)]\<close>
      by (metis "&E" "\<rightarrow>I" "\<equiv>I" "reductio-aa:1")
  }
  hence \<open>[v \<Turnstile> \<box>((\<not>\<phi> & \<not>\<psi>) \<rightarrow> (\<phi> \<equiv> \<psi>))]\<close>
    by (metis "\<rightarrow>I" RN)
  thus \<open>[v \<Turnstile> \<box>(\<phi> \<equiv> \<psi>)]\<close> using 0 "qml:1"[axiom_inst] "\<rightarrow>E" by blast
qed

text\<open>
Additionally, we introduce the command @{command AOT_define}, which allows to directly
state definitions of PLM (see~\ref{InferentialRoleOfDefinitions}). Internally, this involves
introducing a new constant for the defined entity and setting up the syntax for parsing and printing according to the
specified @{emph \<open>syntactic\<close>} type (while the logical type of the constant is deduced). This new constant is then automatically specified to
fulfill the given definition using a mechanism similar to the @{command specification}
command, while the entailed existence proof is constructed automatically.\footnote{The existence
proofs are generally trivial: the definiens itself can be chosen as witness.}

The convenience of this mechanism becomes apparent at a simple example:
\<close>

AOT_define xor1 :: \<open>\<phi> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (infixl \<open>XOR1\<close> 10)
  xor1_spec: \<open>\<phi> XOR1 \<psi> \<equiv>\<^sub>d\<^sub>f (\<phi> \<or> \<psi>) & \<not>(\<phi> & \<psi>)\<close>

text\<open>
This is (roughly)@{footnote \<open>@{command AOT_define} additionally supports our printing modes
and performs internal book-keeping needed for example for the substitution methods to recognize
the new definition.\<close>} the same as:
\<close>
consts xor2 :: \<open>\<o> \<Rightarrow> \<o> \<Rightarrow> \<o>\<close>
syntax xor2 :: \<open>\<phi> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (infixl \<open>XOR2\<close> 10)
specification(xor2)
  xor2_spec: \<open>AOT_model_equiv_def \<guillemotleft>\<phi> XOR2 \<psi>\<guillemotright> \<guillemotleft>(\<phi> \<or> \<psi>) & \<not>(\<phi> & \<psi>)\<guillemotright>\<close>
  by (auto intro!: exI[where x=\<open>\<lambda> \<phi> \<psi> . \<epsilon>\<^sub>\<o> w . [w \<Turnstile> (\<phi> \<or> \<psi>) & \<not>(\<phi> & \<psi>)]\<close>]
           simp: AOT_model_equiv_def AOT_model_proposition_choice_simp)

text\<open>

We also introduce auxiliary commands like @{command AOT_find_theorems} and 
@{command AOT_sledgehammer} to aid in constructing proofs.
@{command AOT_find_theorems} works similar to the Isar
command @{command find_theorems}, but automatically parses AOT syntax and generalizes
concrete variables to schematic variables for pattern matching.
@{command AOT_sledgehammer} is a wrapper that invokes
@{command sledgehammer} while restricting its search for theorems, s.t. the model-specific
theorems are ignored and only the theorems and rules of the abstraction layer are allowed for proofs.

The list of commands can be found in~\ref{AOT:AOT_commands}, while the actual
ML implementation is available at (TODO: cite github repository).
\<close>

section\<open>Representation of an Abstract Semantics of AOT\<close>text\<open>\label{Semantics}\<close>
text\<open>
In~\ref{AOT:AOT_semantics}, we construct an abstract semantics for the primitive (and
some of the basic defined) language elements of AOT. The goal of this layer of abstraction is to
only specify just the properties of the models that are required to derive the axiom system and
rules of AOT later.

The defined semantics heavily relies on Isabelle's @{command specification} command to
abstract specific model choices to more general semantic properties.
The model construction merely enables us to construct witnesses
for the specifications.

As a simple example, we specify implications by requiring that @{term \<open>\<guillemotleft>\<phi> \<rightarrow> \<psi>\<guillemotright>\<close>}
is true in a semantic possible world @{term w}, just in case @{term \<phi>} being true in
@{term w} implies @{term \<psi>} being true in @{term w} (see~\nameref{AOT:AOT_imp_spec}).

More complex examples include the specification of descriptions (see~\nameref{AOT:AOT_desc_spec})
and the joint specification of exemplification and @{text \<lambda>}-abstraction (see~\nameref{AOT:AOT_exe_lambda_spec}).

Notably, we specify necessity (see~\nameref{AOT:AOT_box_spec}) using validity in all semantic possible
worlds and actuality (see~\nameref{AOT:AOT_act_spec}) using validity in a designated actual world @{term w\<^sub>0} (see also~\ref{TrivialAccessibilityRelation}).
Furthermore, we specify AOT's identity as existing identity of meta-logical terms (see \nameref{AOT:AOT_eq_spec}), while
we derive that this corresponds to AOT's definition of identity at each type in~\nameref{AOT:identity:1}.@{footnote \<open>Logical
existence @{term \<open>\<guillemotleft>\<tau>\<down>\<guillemotright>\<close>} is handled similarly.\<close>}

One goal of this intermediate layer of abstraction is to keep the derivation of the abstraction
layer that contains the axioms and the deductive system of AOT impervious to minor changes
in the model construction.

However, it also eliminates artifactual theorems: instead of simply defining @{text \<lambda>}-abstraction
and exemplification using a concrete model construction, we introduce them using abstracted
properties and merely provide a concrete witness that satisfies those properties.
This increases the choice of admissible models of HOL validating our construction, since
such a model is not restricted to the provided witness, but is merely bound by the abstract properties. This eliminates
artifactual theorems that would merely be true for our provided witness, but are not derivable
from the required properties.

For example, in the witness proof of the specification of exemplification and @{text \<lambda>}-abstraction (see~\nameref{AOT:AOT_exe_lambda_spec}), we define
exemplification, as indicated in the previous sections, as a function @{term exe} (type @{typ \<open><'a> \<Rightarrow> 'a \<Rightarrow> \<o>\<close>} with @{typ 'a} of sort @{class AOT_IndividualTerm})
taking a relation term @{term \<Pi>} and individual terms @{term \<kappa>s} to a proposition @{term p}, s.t. if @{term \<Pi>} denotes,
@{term p} is given by applying the function representing @{term \<Pi>} to the individual terms @{term \<kappa>s}, and if @{term \<Pi>}
does not denote, @{term p} is a specific, fixed necessarily false proposition. This choice of a witness implies that
@{term \<open>\<guillemotleft>([\<Pi>]\<kappa>) = ([\<Pi>]\<kappa>')\<guillemotright>\<close>} for any @{term \<kappa>} and @{term \<kappa>'}, whenever @{term \<Pi>} does not denote.
However, since our specification does not imply this fact, the construction still allows
for models in which @{term \<open>\<guillemotleft>[\<Pi>]\<kappa>\<guillemotright>\<close>} is a proposition that is distinct from @{term \<open>\<guillemotleft>[\<Pi>]\<kappa>'\<guillemotright>\<close>}
for distinct @{term \<kappa>} and @{term \<kappa>'} (though both propositions have to be necessarily false).

In this sense, the technical details of the constructed witnesses are not particularly
relevant in contrast to that we (1) have chosen representation types and
basic definitions (e.g. for terms to denote) that @{emph \<open>allow\<close>} constructing suitable
witnesses, (2) our specification is sufficiently strong to validate the
axiom system of AOT and (3) our specification is weak enough and our types are general
enough to preserve hyperintensionality and avoid most artifactual theorems. The
details of our specifications can be found in~\ref{AOT:AOT_semantics}.
\<close>

section\<open>Specifications and the Hilbert-Epsilon-Operator\<close>text\<open>\label{HilbertEpsilon}\<close>

text\<open>
As mentioned in section~\ref{Specifications}, the @{command specification} command internally uses Isabelle's
native Hilbert-Epsilon-operator @{term \<open>SOME x . \<phi> x\<close>}. This operator is axiomatized
in the meta-logic using the following single principle:

\begin{quote}
@{thm[display] someI[where P=\<open>\<lambda>x . \<phi> x\<close>]}
\end{quote}

In particular, this implies that the operator behaves like the classical
Hilbert-Epsilon-operator, i.e. it holds that @{lemma \<open>(\<exists> x . \<phi> x) \<longleftrightarrow> \<phi> (SOME x. \<phi> x)\<close> by (meson someI_ex)}.
Consequently, whenever there is a witness for @{term \<phi>}, then whatever is true for @{emph \<open>everything\<close>} that
satisfies @{term \<phi>} is true for @{term \<open>SOME x. \<phi> x\<close>}:

\begin{quote}
@{thm[display] someI2_ex[where P=\<open>\<lambda> x . \<phi> x\<close> and Q = \<open>\<lambda>x . \<psi> x\<close>]}
\end{quote}

However, it is noteworthy that this operator obeys the following principle of extensionality:

\begin{quote}
@{lemma[display] \<open>(\<forall>x . \<phi> x = \<psi> x) \<longrightarrow> (SOME x . \<phi> x) = (SOME x . \<psi> x)\<close> by auto}
\end{quote}

This is due to the fact, that in the meta-logic, extensional equivalence implies
identity, i.e. the antecedent implies @{term \<open>\<phi> = \<psi>\<close>} and the consequent follows
by substitution of identicals.

Therefore, we @{emph \<open>cannot\<close>} e.g. define an intensional conjunction as follows (we reuse
the type @{typ \<o>\<^sub>2} and its defined validity from section~\ref{Specifications}):@{footnote \<open>Note
that in @{emph \<open>mixfix\<close>} notation a single quote @{text \<open>'\<close>} is used as escape character for distinguishing
placeholders @{text \<open>_\<close>} from underscores @{text \<open>'_\<close>}. A syntactic single quote is therefore given as
@{text \<open>''\<close>}.\<close>}
\<close>
definition \<o>\<^sub>2_conj' (infixl \<open>\<^bold>\<and>''\<close> 100) where
  \<open>\<phi> \<^bold>\<and>' \<psi> \<equiv> SOME \<chi> . valid_\<o>\<^sub>2 \<chi> \<longleftrightarrow> (valid_\<o>\<^sub>2 \<phi> \<and> valid_\<o>\<^sub>2 \<psi>)\<close>

text\<open>
Since it holds that @{lemma \<open>(valid_\<o>\<^sub>2 \<chi> \<longleftrightarrow> (valid_\<o>\<^sub>2 \<phi> \<and> valid_\<o>\<^sub>2 \<psi>)) \<longleftrightarrow> (valid_\<o>\<^sub>2 \<chi> \<longleftrightarrow> (valid_\<o>\<^sub>2 \<psi> \<and> valid_\<o>\<^sub>2 \<phi>))\<close> by auto},
commutativity of @{term \<open>(\<^bold>\<and>')\<close>} is immediately derivable:
\<close>

lemma \<open>(p \<^bold>\<and>' q) = (q \<^bold>\<and>' p)\<close>
  unfolding \<o>\<^sub>2_conj'_def by metis

text\<open>
However, we can avoid this issue, if we do not define the @{emph \<open>value\<close>} of the conjunction
function for specific arguments using the Epsilon-operator, but instead the conjunction function itself, i.e.:
\<close>

definition \<o>\<^sub>2_conj'' (infixl \<open>\<^bold>\<and>''''\<close> 100) where
  \<open>(\<^bold>\<and>'') \<equiv> SOME conj . \<forall> \<phi> \<psi> . valid_\<o>\<^sub>2 (conj \<phi> \<psi>) = (valid_\<o>\<^sub>2 \<phi> \<and> valid_\<o>\<^sub>2 \<psi>)\<close>

text\<open>
This way, our conjunction has any property that is true for @{emph \<open>all possible\<close>} functions
that behave as conjunction under validity. In other words, any choice
for a concrete conjunction is admissible, including intensional ones, as long as
it has our required extensional property under validity.@{footnote \<open>Note, however,
that we still need to make sure that the involved @{emph \<open>types\<close>} are sufficiently
intensional as discussed in section~\ref{Specifications}.\<close>}

This is exactly how the @{command specification} command works: the specification
statements are transformed to closed terms by universal generalization and combined
via conjunction and the result is used as the matrix of the Hilbert-Epsilon-operator.
Given the provided witness, the desired properties of the Hilbert-Epsilon
term become derivable.

Note that the extensionality of the Hilbert-Epsilon operator still implies that any
other operator defined using a meta-logically equivalent condition is identical, i.e.:
\<close>

definition \<o>\<^sub>2_conj''' (infixl \<open>\<^bold>\<and>''''''\<close> 100) where
  \<open>(\<^bold>\<and>''') \<equiv> SOME conj . \<forall> \<phi> \<psi> . (valid_\<o>\<^sub>2 \<psi> \<and> valid_\<o>\<^sub>2 \<phi>) = valid_\<o>\<^sub>2 (conj \<phi> \<psi>)\<close>

lemma \<open>(\<^bold>\<and>'') = (\<^bold>\<and>''')\<close>
  by (auto intro!: Eps_cong simp: \<o>\<^sub>2_conj'''_def \<o>\<^sub>2_conj''_def)

text\<open>
To avoid this issue completely, we would need to introduce an additional dependency
on a meta-logical parameter that is allowed to vary across otherwise meta-logically
equivalent definitions.@{footnote \<open>Note that @{command nitpick} has specific support for the @{command specification} command:
it ignores the underlying definition using the Hilbert-Epsilon operator, and instead solely considers the given specification, see~\cite{Nitpick}.
In that sense, the underlying definition of a @{command specification} is commonly treated
as part of an inaccessible implementational detail of an abstraction layer,
even in the meta-logic HOL itself.\<close>}
\<close>

section\<open>Axiom System and Deductive System\<close>
text\<open>
The axiom system as derived in the embedding was already described in
section~\ref{AxiomSystem} and the fundamental meta-rules were mentioned in
section~\ref{DeductiveSystem}. By construction, most of them can be derived from the
abstract semantics using simple, automatically generated proofs.

While the full derivation of the axiom system in the embedding can be found in~\ref{AOT:AOT_Axioms}
and the deductive system of PLM chapter 9 is derived in~\ref{AOT:AOT_PLM},
in the following, we will focus on some particular axioms, rules and proofs
that are challenging to represent in the embedding. This mostly happens due to
PLM's statement involving either complex preconditions given in natural language or
due to the statement extending over multiple types. 
\<close>

subsection\<open>Base Cases of Denoting Terms\<close>text\<open>\label{cqt:2-impl}\<close>

text\<open>
One of the axioms we mentioned explicitly as difficult to implement in section~\ref{AxiomSystem} is
the second (in PLM's numbering) quantifier axiom which establishes
a set of base cases of denoting terms. Recall the formulation of the axiom in PLM (item (39.2)):

\begin{quote}
  \Squ{@{term \<open>\<guillemotleft>\<tau>\<down>\<guillemotright>\<close>}, provided @{term \<tau>} is a primitive constant, a variable, or a @{text \<open>\<lambda>\<close>}-expression
  in which the initial @{text \<open>\<lambda>\<close>} does not bind any variable in any encoding formula subterm.}
\end{quote}

We implement this axiom by splitting it up into cases. The first and obvious way
to split the axiom is to split it into the separate cases listed in the natural language
formulation: constants, variables and @{text \<open>\<lambda>\<close>}-expressions.

The embedding does not have to distinguish
explicitly between constants and variables: both constants and variables are modelled
as entities of the same type (@{typ \<open>'a AOT_var\<close>}) and the distinction between constants and variables is
done by declaring the entity as a constant or using it as a variable in the meta-logic. So it suffices
to state one case for constants @{emph \<open>and\<close>} variables (see~\nameref{AOT:cqt:2[const_var]}):

\begin{quote}
  @{thm[display] "cqt:2[const_var]"[axiom_inst, of _ \<alpha>, print_as_theorem]}
\end{quote}

@{term \<alpha>} ranges over all expressions of type @{typ \<open>'a AOT_var\<close>} (see~\ref{TypesOfTheEmbedding}) and
therefore ranges over the denoting objects of type @{typ 'a}, which immediately validates
@{thm "cqt:2[const_var]"[axiom_inst, of _ \<alpha>, print_as_theorem]} semantically.
Note that the axiom only extends to @{emph \<open>primitive\<close>} constants, i.e. it does @{emph \<open>not\<close>} extend
to @{emph \<open>defined\<close>} constants. In our embedding defined constants are modelled as @{emph \<open>terms\<close>} of a given
type, i.e. directly in the base type @{typ 'a}, not the type @{typ \<open>'a AOT_var\<close>}, so the axiom cannot
be instantiated to them, as intended.

The remaining case concerns @{text \<open>\<lambda>\<close>}-expressions and is more complex to represent.
Internally, a @{text \<open>\<lambda>\<close>}-expression denotes, just in case that its
matrix @{term \<phi>} is necessarily equivalent on all denoting objects that share an urelement, or
formally (see~\nameref{AOT:AOT_semantics.AOT_model_lambda_denotes}):

\begin{quote}
  @{thm[display] AOT_model_lambda_denotes[of \<phi>]}
\end{quote}

However, this is a semantic criterion and does not directly correspond to the formulation of above axiom.
While, for arbitrary complex terms, we cannot directly capture the syntactic restriction
stating that the initial @{text \<open>\<lambda>\<close>} does not bind any variable in any encoding formula subterm,
we can construct a set of introduction rules for a predicate on matrices that will cover all terms that match the
natural language description.

To that end, we define the auxiliary constant @{const AOT_instance_of_cqt_2} (see~\nameref{AOT:AOT_semantics.AOT_instance_of_cqt_2}).
This constant acts on matrices of @{text \<open>\<lambda>\<close>}-expressions, i.e. on functions that map entities
of a type of class @{class AOT_\<kappa>s} (recall that this may either be an unary individual or 
a tuple of individuals, see~\ref{IndividualTermsAndClasses}) to propositions.

@{const AOT_instance_of_cqt_2} is true for any such function that agrees on arguments
that denote and are @{const AOT_model_term_equiv}-equivalent, i.e. that has identical
values for arguments that denote and share the same urelements. By construction of
@{text \<open>\<lambda>\<close>}-expressions the use of any such function as matrix of a @{text \<open>\<lambda>\<close>}-expression
will result in a denoting relation term.

Now we enrich the abstraction layer with several introduction rules for @{const AOT_instance_of_cqt_2}:

  \<^item> Functions that do not depend on their argument correspond to matrices in which
    the @{text \<open>\<lambda>\<close>}-bound variables do not occur. Therefore such functions trivially fall
    under the formulation of the axiom (see~\nameref{AOT:AOT_semantics.AOT_instance_of_cqt_2_intros_const}).
  \<^item> Exemplification formulas of the form @{term \<open>print_term \<guillemotleft>[\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n\<guillemotright>\<close>} in which
    the @{text \<open>\<lambda>\<close>}-bound variable does not occur in @{term \<Pi>} fall under the axiom,
    if all individual terms @{term \<open>\<kappa>\<^sub>i\<close>} do not contain an occurrence of the
    @{text \<open>\<lambda>\<close>}-bound variable in encoding formula subterms. This is captured in another
    auxiliary constant @{const AOT_instance_of_cqt_2_exe_arg} (see~\nameref{AOT:AOT_semantics.AOT_instance_of_cqt_2_exe_arg})
    described below.
  \<^item> Let @{text \<open>\<nu>\<^sub>1...\<nu>\<^sub>n\<close>} be the variables bound by the initial @{text \<lambda>}. Then an exemplification formula of the form
    @{term \<open>print_term \<guillemotleft>[\<lambda>\<mu>\<^sub>1...\<mu>\<^sub>n \<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n,\<mu>\<^sub>1...\<mu>\<^sub>n}]\<kappa>\<^sub>1...\<kappa>\<^sub>n\<guillemotright>\<close>} as matrix falls under the axiom, if
    (1) all individual terms @{text \<open>\<kappa>\<^sub>i\<close>} fall under the axiom as described below and
    (2) @{term \<phi>} falls under the axiom wrt. @{text \<open>\<nu>\<^sub>1...\<nu>\<^sub>n\<close>}, i.e. @{term \<phi>} does not
    contain any occurrences of @{text \<open>\<nu>\<^sub>1...\<nu>\<^sub>n\<close>} in encoding formula subterms, respectively
    for any @{text \<open>\<mu>\<^sub>1...\<mu>\<^sub>n\<close>} it holds that @{text \<open>\<phi>{\<nu>\<^sub>1...\<nu>\<^sub>n,\<mu>\<^sub>1...\<mu>\<^sub>n}\<close>} as function on
    @{text \<open>\<nu>\<^sub>1...\<nu>\<^sub>n\<close>} satisfies @{const AOT_instance_of_cqt_2} (see~\nameref{AOT:AOT_semantics.AOT_instance_of_cqt_2_intros_exe_lam}).
  \<^item> Complex formulas fall under the formulation of the axiom, just in case all its
    operands fall under the formulation of the axiom. E.g. a negation falls under the
    axiom, just in case the negated formula falls under the axiom (see~\nameref{AOT:AOT_semantics.AOT_instance_of_cqt_2_intros_not}).
  \<^item> Encoding formulas only fall under the axiom, if the @{text \<open>\<lambda>\<close>}-bound variables do
    not occur in them at all. This is already covered in the first case above.
    However, this may be refined in the future anticipating an upcoming change in PLM
    as discussed at the end of this section.

The above rules cover all cases except the primary individual terms in exemplification
formulas. The additional auxiliary constant @{const AOT_instance_of_cqt_2_exe_arg} (see~\nameref{AOT:AOT_semantics.AOT_instance_of_cqt_2_exe_arg})
acts on functions taking entities of a type @{typ 'a} of class @{class AOT_\<kappa>s} to
entities of a type @{typ 'b} of class @{class AOT_\<kappa>s}.
@{const AOT_instance_of_cqt_2_exe_arg} holds for any such function that sends denoting and
@{const AOT_model_term_equiv}-equivalent arguments to again @{const AOT_model_term_equiv}-equivalent
values. By construction, if the application of any such function to the variables @{text \<open>\<nu>\<^sub>1...\<nu>\<^sub>n\<close>}
occurs as primary individual term in an exemplification formula, then the exemplification
formula satisfies the meta-logical definition of @{const AOT_instance_of_cqt_2} (since the result of the exemplification
is known to agree on objects with the same urelements).

Similarly to @{const AOT_instance_of_cqt_2} we add introduction rules for
@{const AOT_instance_of_cqt_2_exe_arg} to the abstraction layer:

  \<^item> The identity function falls under @{const AOT_instance_of_cqt_2_exe_arg} (this is the case
    in which the @{text \<open>\<lambda>\<close>}-bound variables themselves occur as primary individual terms in an 
    exemplification formula; see~\nameref{AOT:AOT_semantics.AOT_instance_of_cqt_2_intros_exe_arg_self}).
  \<^item> Constant functions fall under @{const AOT_instance_of_cqt_2_exe_arg}
    (this is the case in which the @{text \<open>\<lambda>\<close>}-bound variables do @{emph \<open>not\<close>} occur
    in a primary individual term of an exemplification formula; see~\nameref{AOT:AOT_semantics.AOT_instance_of_cqt_2_intros_exe_arg_const}).
  \<^item> Definite descriptions fall under @{const AOT_instance_of_cqt_2_exe_arg} just in case their
    matrix (as function acting on the @{text \<lambda>}-bound variables) falls under @{const AOT_instance_of_cqt_2}, i.e. a description may occur in
    a primary term of an exemplification formula, if its matrix does not contain the
    @{text \<open>\<lambda>\<close>}-bound variables in an encoding formula subterm (see~\nameref{AOT:AOT_semantics.AOT_instance_of_cqt_2_intros_desc}).
  \<^item> There are further technical introduction rules due to the implementation of n-ary
    relations as relations acting on tuples (see~\nameref{AOT:AOT_semantics.AOT_instance_of_cqt_2_intros_exe_arg_fst}), e.g. the @{const fst} and @{const snd} projections
    fall under @{const AOT_instance_of_cqt_2_exe_arg} (i.e. @{term \<open>\<guillemotleft>[\<lambda>xy [F]x]\<guillemotright>\<close>} and @{term \<open>\<guillemotleft>[\<lambda>xy [F]y]\<guillemotright>\<close>})
    and the application of the @{const Pair} function to two terms falls under the axiom,
    if both terms fall under @{const AOT_instance_of_cqt_2_exe_arg} (i.e. @{term \<open>\<guillemotleft>[\<lambda>x [F]\<kappa>\<kappa>']\<guillemotright>\<close>}
    falls under the axiom, if neither @{term \<kappa>} nor @{term \<kappa>'} contain @{term x} in an encoding formula subterm).

While the details of this construction are complex, the result is a set of introduction
rules that allow proving @{const AOT_instance_of_cqt_2} exactly for those matrices that
fall under the natural language condition of the axiom. The axiom itself is then implemented
conditionally: a @{text \<open>\<lambda>\<close>}-expression denotes axiomatically, if its matrix satisfies
@{const AOT_instance_of_cqt_2} (see~\nameref{AOT:cqt:2[lambda]}).
The introduced introduction rules may be used in the abstraction layer, while it is
inadmissible to unfold the definition of @{const AOT_instance_of_cqt_2} itself (i.e.
the only matrices for which @{const AOT_instance_of_cqt_2} is derivable in the abstraction
layer are exactly those that satisfy the natural language restriction of PLM's axiom).

Note that at the time of writing, a generalization of the axiom is under discussion that
would extend it to the following:@{footnote \<open>The precise formulation in the
upcoming next version of PLM may vary slightly in its wording, but is likely to extend over the
same amount of cases.\<close>}

\begin{quote}
  \Squ{@{term \<open>\<guillemotleft>\<tau>\<down>\<guillemotright>\<close>}, provided @{term \<tau>} is a primitive constant, a variable, or a @{text \<open>\<lambda>\<close>}-expression
  in which the initial @{text \<open>\<lambda>\<close>} does not bind any variable that is a primary term in an encoding formula subterm.}
\end{quote}

In an encoding formula @{text \<open>\<kappa>\<^sub>1...\<kappa>\<^sub>n[\<Pi>]\<close>} only @{text \<open>\<Pi>\<close>} as well as @{text \<open>\<kappa>\<^sub>1\<close>} through
@{text \<open>\<kappa>\<^sub>n\<close>} are defined to be primary terms, but no nested term counts as primary term, so
this entails strictly more cases than the formulation given above.

In anticipation of this change, this is already validated by the embedding, however,
the corresponding introduction rules are not yet added to the abstraction layer
to disbar their use for the time being (see~\nameref{AOT:AOT_semantics.AOT_instance_of_cqt_2_enc_arg}).

See~\ref{ArtifactAczel} for a discussion of some consequences of this upcoming change.
\<close>

subsection\<open>The Rule of Substitution\<close>

text\<open>
Similar to the axiom above, there is also derived rules in PLM that are challenging
to reproduce in the embedding. A prominent example is the Rule of Substitution.
PLM formulates this rule in item (159) as follows:\footnote{PLM
formulates the rule relative to modally-fragile derivations @{text \<open>\<turnstile>\<close>}, but further
argues that it is equally valid for modally-strict derivations @{text \<open>\<turnstile>\<^sub>\<box>\<close>}. Furthermore,
it also states a variant in which the precondition is weakened to @{text \<open>\<turnstile>\<^sub>\<box> \<phi> \<equiv> \<chi>\<close>},
which allows to derive @{text \<open>\<turnstile>\<^sub>\<box> \<box>(\<phi> \<equiv> \<chi>)\<close>} by RN.}

\begin{quote}
\Squ{If @{text \<open>\<turnstile> \<box>(\<phi> \<equiv> \<chi>)\<close>}, then where @{text \<open>\<Gamma>\<close>} is any set of formulas and
@{text \<open>\<phi>'\<close>} is the result of substituting the formula @{text \<chi>} for zero or more
occurrences of @{text \<psi>} where the latter is a subformula of @{text \<phi>}, @{text \<open>\<Gamma> \<turnstile> \<phi>\<close>} if
and only if @{text \<open>\<Gamma> \<turnstile> \<phi>'\<close>}.}
\end{quote}

The notable restriction in this formulation is the proviso that 
@{text \<open>\<psi>\<close>} is a @{emph \<open>subformula\<close>} of @{text \<phi>}. Subformulas are defined recursively
in PLM item (6) and notably do not entail matrices of
descriptions or @{text \<open>\<lambda>\<close>}-expressions: E.g. the formula @{text \<phi>} is @{emph \<open>not\<close>} a
subformula of @{term \<open>print_term \<guillemotleft>[F]\<^bold>\<iota>x \<phi>{x}\<guillemotright>\<close>} or of @{term \<open>print_term \<guillemotleft>[\<lambda>y \<phi>{y}]x\<guillemotright>\<close>}.

While the inductive base cases for proving the rule can easily be reproduced in the
embedding (see~\nameref{AOT:rule-sub-lem:1:a}), combining the rule to a single statement
in Isabelle is challenging. Therefore we instead provide customly written proving
@{theory_text method}s that allow applying the rule as intended by PLM. This works
by internally analyzing the structure of (the ML representation of)@{footnote \<open>A proving method
written in Isabelle/ML can traverse the ML representation of terms and determine structural properties.
However, properties determined in this way cannot be used as logical preconditions in inner syntax. They are
meta-logical properties that, in general, cannot be represented in the logical layer.\<close>} the involved formulas in order to choose the appropriate
rule that allows to reduce the goal to a substitution in a less complex formulas. In that sense, the proving
methods reconstruct the general proof of the rule in PLM by induction on the complexity of the
involved formulas at every invocation of the proving method on a concrete formula.
\<close>

subsection\<open>Proofs by Type Distinction\<close>

text\<open>
PLM involves proofs that involve a case distinction by type. An example is the theorem
that two terms being identical implies that both denote (see~\nameref{AOT:AOT_PLM.AOT_Term_id}).

In our embedding, we reproduce this kind of reasoning by introducing a new type class,
in this case @{class AOT_Term_id}, that assumes the statement of the theorem, and then
by instantiating this type class to all the types the statement is supposed to apply to.
We then augment the type constraints for terms of these types to include the newly defined class.

In a future version of the embedding, we intend to use Standard ML to define
a simple outer syntax command (similarly to @{command AOT_define} discussed in
section~\ref{AOTOuterSyntax}) that will hide the complexity of this process and
will allow for a more intuitive statement of theorems that are to be proven by type
distinction.
\<close>

subsection\<open>Definition of @{text \<open>n\<close>}-ary Relation Identity\<close>text\<open>\label{nary}\<close>
(*<*)
definition explicitVerbatim :: \<open>'a \<Rightarrow> 'a\<close> where \<open>explicitVerbatim x \<equiv> x\<close>
syntax (input) "_explicitVerbatim" :: \<open>any \<Rightarrow> \<phi>\<close> (\<open>\<^bold>\<guillemotleft>_\<^bold>\<guillemotright>\<close>)
syntax (input) "_explicitVerbatim" :: \<open>any \<Rightarrow> \<tau>\<close> (\<open>\<^bold>\<guillemotleft>_\<^bold>\<guillemotright>\<close>)
syntax (input) "_explicitVerbatim" :: \<open>\<phi> \<Rightarrow> any\<close> (\<open>\<^bold>\<guillemotleft>_\<^bold>\<guillemotright>\<close>)
syntax (input) "_explicitVerbatim" :: \<open>\<tau> \<Rightarrow> any\<close> (\<open>\<^bold>\<guillemotleft>_\<^bold>\<guillemotright>\<close>)
syntax (output) "_explicitVerbatim" :: \<open>any \<Rightarrow> \<phi>\<close> (\<open>\<guillemotleft>_\<guillemotright>\<close>)
syntax (output) "_explicitVerbatim" :: \<open>any \<Rightarrow> \<tau>\<close> (\<open>\<guillemotleft>_\<guillemotright>\<close>)
syntax (output) "_explicitVerbatim" :: \<open>\<phi> \<Rightarrow> any\<close> (\<open>\<guillemotleft>_\<guillemotright>\<close>)
syntax (output) "_explicitVerbatim" :: \<open>\<tau> \<Rightarrow> any\<close> (\<open>\<guillemotleft>_\<guillemotright>\<close>)
translations
  "_explicitVerbatim x" == "CONST explicitVerbatim x"
AOT_theorem prop_id_explicit:
  \<open>\<Pi> = \<Pi>' \<equiv>\<^sub>d\<^sub>f \<Pi>\<down> & \<Pi>'\<down> & \<forall>x\<^sub>1...\<forall>x\<^sub>n(\<^bold>\<guillemotleft>AOT_sem_proj_id (explicitVerbatim x\<^sub>1x\<^sub>n) (\<lambda>\<kappa>\<^sub>1\<kappa>\<^sub>n. \<^bold>\<guillemotleft>[\<Pi>]\<kappa>\<^sub>1...\<kappa>\<^sub>n\<^bold>\<guillemotright>) (\<lambda>\<kappa>\<^sub>1\<kappa>\<^sub>n. \<^bold>\<guillemotleft>[\<Pi>']\<kappa>\<^sub>1...\<kappa>\<^sub>n\<^bold>\<guillemotright>)\<^bold>\<guillemotright>)\<close>
  unfolding explicitVerbatim_def
  using "identity:3".
lemma unary_proj_id_explicit:
  \<open>AOT_sem_proj_id \<kappa> \<phi> \<psi> = explicitVerbatim (print_term (AOT_eq (AOT_lambda (\<lambda>x :: 'a ::AOT_\<kappa>. \<phi> x)) (AOT_lambda (\<lambda>x. \<psi> x))))\<close>
  unfolding explicitVerbatim_def print_term_def
  using AOT_sem_unary_proj_id.
lemma nary_proj_id_explicit:
  \<open>AOT_sem_proj_id (\<kappa>\<^sub>1::'a::AOT_\<kappa>, \<kappa>\<^sub>2\<kappa>\<^sub>n::'b::AOT_\<kappa>s) (\<lambda>(x,y\<^sub>1y\<^sub>n) . explicitVerbatim (print_term (\<phi> x y\<^sub>1y\<^sub>n))) (\<lambda>(x,y\<^sub>1y\<^sub>n). explicitVerbatim (print_term (\<psi> x y\<^sub>1y\<^sub>n))) = explicitVerbatim (print_term (
AOT_conj (AOT_eq (AOT_lambda (\<lambda>x :: 'a. \<phi> x \<kappa>\<^sub>2\<kappa>\<^sub>n)) (AOT_lambda (\<lambda>x. \<psi> x \<kappa>\<^sub>2\<kappa>\<^sub>n)))
(explicitVerbatim (AOT_sem_proj_id \<kappa>\<^sub>2\<kappa>\<^sub>n (\<lambda>y\<^sub>1y\<^sub>n. explicitVerbatim (\<phi> \<kappa>\<^sub>1 y\<^sub>1y\<^sub>n)) (\<lambda>y\<^sub>1y\<^sub>n. explicitVerbatim (\<psi> \<kappa>\<^sub>1 y\<^sub>1y\<^sub>n))))
))\<close>
  unfolding explicitVerbatim_def print_term_def
  AOT_sem_proj_id_prod_def by auto
lemma unary_inst: \<open>AOT_model_equiv_def \<guillemotleft>\<Pi> = \<Pi>'\<guillemotright> \<guillemotleft>\<Pi>\<down> & \<Pi>'\<down> & \<forall>x \<^bold>([\<lambda>x [\<Pi>]x] = [\<lambda>x [\<Pi>']x]\<^bold>)\<guillemotright>\<close>
  by (simp add: explicitParen_def "identity:3"[where 'a=\<kappa>, unfolded AOT_sem_unary_proj_id])

(*>*)
text\<open>
Recall the definition of @{text n}-ary relation identity of PLM given in section~\ref{AOTLanguage}:

\begin{quote}
  \Squ{@{text \<open>\<Pi> = \<Pi>' \<equiv>\<^sub>d\<^sub>f \<Pi>\<down> & \<Pi>'\<down> & \<forall>y\<^sub>1\<dots>\<forall>y\<^bsub>n-1\<^esub> ([\<lambda>x [\<Pi>]xy\<^sub>1\<dots>y\<^bsub>n-1\<^esub>] = [\<lambda>x [\<Pi>']xy\<^sub>1\<dots>y\<^bsub>n-1\<^esub>] &
[\<lambda>x [\<Pi>]y\<^sub>1xy\<^sub>2\<dots>y\<^bsub>n-1\<^esub>] = [\<lambda>x [\<Pi>']y\<^sub>1xy\<^sub>2\<dots>y\<^bsub>n-1\<^esub>] & \<dots> &
[\<lambda>x [\<Pi>]y\<^sub>1\<dots>y\<^bsub>n-1\<^esub>x] = [\<lambda>x [\<Pi>']y\<^sub>1\<dots>y\<^bsub>n-1\<^esub>x]
)\<close>}}
\end{quote}

While we can easily represent ellipse notation in terms that are uniform over arities, as e.g. in
@{text \<beta>}-conversion, by choosing a single variable of a type class that can be instantiated to tuples in place
of the ellipse list of variables, this definition involves additional conjunctive clauses depending on the
arity and is thereby harder to implement.

A solution would be to approximate the statement of the definition by stating it explicitly
for finitely many arities.@{footnote \<open>In fact, for convenience we do this for arities up to
four (see~\nameref{AOT:identity:3[2]}).\<close>} However, the construction using type class instantiations on
product types described in section~\ref{ModelConstruction} also allows us to state the definition generically, albeit that we have
to rely on an auxiliary construction in the meta-logic.

The generic version of the definition in our embedding is the following (see~\nameref{AOT:identity:3}):

\begin{quote}
@{thm[display] prop_id_explicit}
\end{quote}

The quotation marks @{text \<open>\<guillemotleft>_\<guillemotright>\<close>} allow us to inject meta-logical terms into the
custom grammar we introduced for AOT syntax and vice-versa.
Here ellipses like @{text \<open>x\<^sub>1...x\<^sub>n\<close>} are, meta-logically, a single variable @{text \<open>x\<^sub>1x\<^sub>n\<close>} restricted to an arbitrary type
of the type class @{class AOT_\<kappa>s}. The auxiliary constant @{term AOT_sem_proj_id} is defined
in the type class @{class AOT_RelationProjection} (see~\nameref{AOT:AOT_semantics.AOT_RelationProjection}; recall that this
is a subclass of @{class AOT_\<kappa>s}). It satisfies
an additional restriction on types of the class @{class AOT_UnaryRelationProjection} (resp. on the concrete type @{typ \<kappa>};
see~\nameref{AOT:AOT_semantics.AOT_UnaryRelationProjection})
and has a concrete definition on products:

\begin{quote}
@{thm[display] unary_proj_id_explicit}
@{thm[display] nary_proj_id_explicit}
\end{quote}

Note that the outermost identities in these statements are meta-logical identities that
thereby allow immediate meta-logical substitution.
In the unary case, @{term AOT_sem_proj_id} reduces to the the identity of the one-place
relations given by @{text \<open>\<lambda>\<close>}-abstracting the given matrices @{text \<open>\<phi>\<close>} and @{text \<open>\<psi>\<close>}.

In the product case, it is defined for matrices acting on pairs (of type @{typ \<open>'a\<times>'b\<close>}) as a conjunction. The first conjunct is the identity of the one-place
relations resulting from @{text \<open>\<lambda>\<close>}-abstracting @{text x} in the applications of the matrices to
@{term x} and @{text \<open>\<kappa>\<^sub>2...\<kappa>\<^sub>n\<close>}.
The second conjunct recursively refers to @{term AOT_sem_proj_id} on type @{typ 'b}
acting on @{text \<open>\<kappa>\<^sub>2\<kappa>\<^sub>n\<close>} (corresponding to @{text \<open>\<kappa>\<^sub>2...\<kappa>\<^sub>n\<close>} in our AOT syntax implementation)
and partial applications of the matrices to @{term \<kappa>\<^sub>1}.

Now restricting the generic definition to type @{term \<kappa>}, yields the following instance:

\begin{quote}
@{thm prop_id_explicit[where 'a=\<kappa>, rename_abs x \<kappa> \<kappa>]}
\end{quote}

Unfolding the definition of @{term AOT_sem_proj_id} in the unary case, this yields
\begin{quote}
@{thm unary_inst}
\end{quote}

While this is technically not a definition of AOT, the implied equivalence is a theorem
as a consequence of @{term \<eta>}-conversion.

Restricting the definition to type @{term \<open>\<kappa>\<times>\<kappa>\<close>}, yields this instance:

\begin{quote}
@{thm prop_id_explicit[where 'a=\<open>\<kappa>\<times>\<kappa>\<close>, rename_abs x \<kappa>\<^sub>1\<kappa>\<^sub>2 \<kappa>\<^sub>1\<kappa>\<^sub>2]}
\end{quote}

Now unfolding the definition of @{term AOT_sem_proj_id} in the product case (i.e. for type @{typ \<open>\<kappa>\<times>\<kappa>\<close>}) followed
by unfolding it for the recursive unary case, yields the proper definition of
@{text 2}-ary relation identity:@{footnote \<open>Technically, this additionally involves expanding the
@{text n}-ary quantifier to two unary quantifiers, one of which can be eliminated.\<close>}

\begin{quote}
@{thm "identity:3[2]"[where F=\<Pi> and G=\<Pi>']}
\end{quote}

Similarly, instantiating to type @{typ \<open>\<kappa>\<times>\<kappa>\<times>\<kappa>\<close>} yields ternary relation identity, etc.

While this construction yields the technical means to state the definition
of @{text n}-ary relation identity as well as the axiom of @{text n}-ary encoding generically,
properly unfolding the meta-logical definitions can be cumbersome in practice.

For that reason we additionally explicitly derive the definition of identity and the axiom
of @{text n}-ary encoding for arities up to four, which is more than sufficient for
the instances currently used in PLM. For @{text n}-ary encoding we currently do not
formulate a generic version, even though the same mechanism as above can be applied
to this case as well.

In the future, we intend to define a convenient @{emph \<open>theorem attribute\<close>} (see below) that can
be used to immediately instantiate @{text n}-ary statements of generic form directly to an arbitrary
arity @{text n} given as argument to the attribute.

Another subtlety in the definition of @{text n}-ary relation identity is the fact
that two @{text n}-ary relations already have to be identical, if all their
projections to unary relations using @{text \<open>n-1\<close>} @{emph \<open>denoting\<close>} individual terms are identical.
However, in order to avoid artifactual theorems, we defined relations as
functions that also act on @{typ null}-urelements, resp. on tuples that may involve
@{typ null}-urelements. The identity of their projections merely implies that the functions
representing the @{text n}-ary relations
in question evaluate to the same propositions for all tuples of @{text \<open>n-1\<close>} urelements that
correspond to denoting individuals (i.e. that are not @{text null}-urelements) and one urelement that
may be a @{text null}-urelement.
This is the reason why in section~\ref{RelationsAsPropositionValuedFunctions} we required the
behaviour of an @{text n}-ary relation on @{emph \<open>irregular\<close>} individual terms (i.e.
tuples that involve more than one @{text null}-urelement) to be completely determined
by the behaviour of the relation on @{emph \<open>regular\<close>} individual terms (i.e. tuples
that involve at most one @{text null}-urelement). This way the identity of all
projections of two @{text n}-ary relations to unary relations indeed implies their
identity as required for validating the definition, while we still avoid the
artifactual theorem that @{text \<open>\<forall>x\<^sub>1...\<forall>x\<^sub>n ([\<Pi>]x\<^sub>1...x\<^sub>n = [\<Pi>']x\<^sub>1...x\<^sub>n) \<rightarrow> \<Pi> = \<Pi>'\<close>}.
\<close>


subsection\<open>Auxiliary Theorem Attributes\<close>

text\<open>
The embedding defines several auxiliary @{emph \<open>theorem attributes\<close>} that help
in reproducing common reasoning patterns of PLM that would otherwise be subject
to technical complications.

PLM often prefers stating theorems using object level variables rather than
meta-variables (that would range over potentially non-denoting terms) in order to avoid
having to specifically state the precondition that the respective terms denote.

However, whenever a term is trivially known to denote from context, PLM may simply
instantiate such theorems directly to terms. This is valid, since it is always possible
to apply GEN followed by @{text \<open>\<forall>\<close>}-elimination for terms to the theorem. To reproduce
this transformation within the embedding the theorem attribute @{attribute unvarify}
is introduced (see~\nameref{AOT:AOT_PLM.unvarify}), which takes the variable to be
generalized as argument and automatically performs the required transformation on
the theorem. Similarly, the attribute @{attribute unconstrain} (see~\nameref{AOT:AOT_RestrictedVariables.unconstrain})
can be used to transform a theorem formulated with restricted variables to a theorem
involving unconstrained variables with the added precondition that they satisfy the respective restriction
conditions.
\<close>

section\<open>Meta Theorems\<close>text\<open>\label{MetaTheorems}\<close>

subsection\<open>The Collapse of Alphabetic Variants\<close>text\<open>\label{alphabetic-variants}\<close>

text\<open>
We already informally stated that the embedding collapses alphabetic variants. In this section
we will define more precisely what this means and justify this collapse.

Isabelle internally represents bound variables using de-Bruijn indices (see~\cite{DeBruijnIndices}). We will
showcase this mechanism in detail below. As a consequence, terms that are alphabetic variants
are meta-logically indistinguishable. To justify representing AOT's bound variables directly
using bound variables in Isabelle, we need to show that both (1) AOT's notion of alphabetic
variants is equivalent to Isabelle's use of de-Bruijn indices and (2) any rule of AOT is still valid
if any assumption or the conclusion are replaced by an alphabetic variant (as a generalization of PLM's
existing @{emph \<open>Rule of Alphabetic Variants\<close>}).\footnote{This includes theorems and axioms by
thinking of them as rules with an empty set of assumptions.}

\<close>

subsubsection\<open>AOT's Alphabetic Variants align with Isabelle's use of de-Bruijn Indices\<close>text\<open>\label{alphabetic-variants-de-bruijin}\<close>

text\<open>
Internally, Isabelle represents binding notation by function application and abstraction.
E.g. if we let Isabelle print the internal ML representation of the term @{term \<open>\<guillemotleft>\<forall>p (p \<rightarrow> p)\<guillemotright>\<close>},
we arrive at the following:@{footnote \<open>Note that we are not merely talking about a representation in
the meta-logic HOL, but about the internal ML representation of HOL terms.
Technically, we have setup an @{emph \<open>antiquotation\<close>} that
allows us to print a term together with its internal representation.\<close>}

@{ML_print_term \<open>\<guillemotleft>\<forall>p (p \<rightarrow> p)\<guillemotright>\<close>}

While a complete discussion of the ML representation of terms goes beyond the scope of
this thesis, it suffices to have a rough understanding of the involved syntax.
The atomic terms are typed constants, @{text \<open>Const ([identifier], [type])\<close>},
bound variables @{text \<open>Bound [de-Bruijn index]\<close>} and free variables @{text \<open>Free ([identifier], [type])\<close>}.
@{text \<open>$\<close>} is a binary operator that signifies function application between terms.
@{text \<open>Abs ([name], [type], [term])\<close>} is the abstraction of @{text \<open>[term]\<close>} over a
bound variable of type @{text \<open>[type]\<close>}. Note that while the internal representation retains
the name of the bound variable @{text p}, it has no logical meaning and is merely used
e.g. for term printing, while, logically, occurrences of the
bound variables are referred to by @{text \<open>Bound\<close>} with a de-Bruijn index. An index of zero
refers to the innermost abstraction the bound variable is contained in. An index of one
refers to the next outer abstraction, e.g.

@{ML_print_term \<open>\<guillemotleft>\<forall>p (p \<rightarrow> \<forall>q (q \<rightarrow> p))\<guillemotright>\<close>}

Note that in the inner abstraction @{text \<open>Bound 0\<close>} refers to @{term q}, while @{text \<open>Bound 1\<close>}
refers to @{term p}.

Our claim is that two terms or formulas of AOT are alphabetic variants, if and only if their
representation using de-Bruijn indices is the same.

PLM defines alphabetic variants as follows (see PLM item (16)): It refers to two occurrences of a
variable as @{emph \<open>linked\<close>}, if both are free or they are bound by the same occurrence of a
variable-binding operator. PLM further introduces @{emph \<open>BV-notation\<close>} for formulas and terms:@{footnote \<open>In
the following we will restrict our discussion to formulas, but the argument applies analogously to terms
as well.\<close>} the BV-notation of a formula @{term \<phi>} is @{text \<open>\<phi>[\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n]\<close>}, where @{text \<open>\<alpha>\<^sub>1, \<dots> \<alpha>\<^sub>n\<close>}
is the list of all variables that occur bound in @{term \<phi>}, including repetitions.
Further @{text \<open>\<phi>[\<beta>\<^sub>1/\<alpha>\<^sub>1, \<dots>, \<beta>\<^sub>n/\<alpha>\<^sub>n]\<close>} refers to the result of replacing @{text \<open>\<alpha>\<^sub>i\<close>} by @{text \<open>\<beta>\<^sub>i\<close>}
in @{text \<open>\<phi>[\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n]\<close>}. Now @{term \<phi>'} is defined to be an @{emph \<open>alphabetic variant\<close>} of @{term \<phi>}
just in case for some @{text n}:

  \<^item> @{text \<open>\<phi>' = \<phi>[\<beta>\<^sub>1/\<alpha>\<^sub>1, \<dots>, \<beta>\<^sub>n/\<alpha>\<^sub>n]\<close>},
  \<^item> @{text \<phi>'} has the same number of bound variable occurrences as @{text \<phi>} and so can be written as
    @{text \<open>\<phi>'[\<beta>\<^sub>1, \<dots>, \<beta>\<^sub>n]\<close>}, and
  \<^item> for @{text \<open>1 \<le> i, j \<le> n\<close>}, @{text \<alpha>\<^sub>i} and @{text \<alpha>\<^sub>j} are linked in @{text \<open>\<phi>[\<alpha>\<^sub>1, \<dots>, \<alpha>\<^sub>n]\<close>} if and
    only if @{text \<beta>\<^sub>i} and @{text \<beta>\<^sub>j} are linked in @{text \<open>\<phi>'[\<beta>\<^sub>1, \<dots> \<beta>\<^sub>n]\<close>}.


By definition, each group of @{emph \<open>linked\<close>} variable occurrences in AOT corresponds to exactly
one abstraction in Isabelle's internal representation and all de-Bruijn indexed @{text Bound} terms
that refer to this abstraction. Since changing the variable name of a linking group will not affect the
de-Bruijn indices, the de-Bruijn representation of two alphabetic variants is therefore the same.
Conversely, changing any index in the de-Bruijn representation translates to breaking a linking
group as defined in PLM, thereby terms with different de-Bruijn representation are not alphabetic
variants.

Since thereby the formulas and terms that are collapsed in Isabelle's internal
representation are exactly the alphabetic variants of AOT, it remains to argue that the collapse
is inferentially valid, i.e. AOT allows to freely interchange alphabetic variants in any
derivation.
\<close>

subsubsection\<open>Equivalence of Alphabetic Variants in AOT\<close>

text\<open>
Conveniently, PLM itself derives the following @{emph \<open>Rule of Alphabetic Variants\<close>} (see PLM item (114)):@{footnote \<open>Note
that while PLM states meta-rules using @{text \<open>\<turnstile>\<close>}, unless otherwise noted by convention they apply to both @{text \<open>\<turnstile>\<close>} and
@{text \<open>\<turnstile>\<^sub>\<box>\<close>}. See remark (67) in PLM. We adopt this convention in the following sections.\<close>}

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

To see that this rule is valid, it suffices to realize that for every @{text \<open>\<psi> \<in> \<Gamma>\<close>} and @{text \<open>\<psi>' \<in> \<Gamma>'\<close>} by the above rule it holds that
@{text \<open>\<psi> \<stileturn>\<turnstile> \<psi>'\<close>} and hence all premises in @{text \<Gamma>} are derivable from @{text \<Gamma>'} and vice-versa. More rigorously,
the version with assumptions can be reduced to the version without assumptions by arguing with successive
applications of the deduction theorem to eliminate the assumptions, applying the version of the rule without
assumptions and then reconstructing the result using modus ponens.
This mechanism is shown explicitly in section~\ref{free-variables-schematic} for a similar case.

Hence, AOT allows to freely move from any formula to an alphabetic variant in all theorems and assumptions,
justifying the fact that the embedding identifies alphabetic variants.
\<close>

subsection\<open>Free Variable Notation, Substitutability and Bound Variables\<close>text\<open>\label{substitutability}\<close>

text\<open>
As mentioned in chapter~\ref{AOT}, PLM allows terms and formulas with arbitrary free variables
to be used in place of of its meta-variables, except for free variables that are explicitly excluded
in natural language. The embedding on the other hand requires to explicitly mention any variables that
are bound at the occurrence of a meta-variable, if they should be allowed to occur in an instance of the
meta-variable. This is due to the fact that binders are implemented in the embedding as
operators that act on functions. Similarly, the substitution of variables in meta-variables
is implemented using function application.

For example, PLM formulates the first quantifier axiom as follows (see PLM item (39.1)):

\begin{quote}
\Squ{$\forall \alpha\,\varphi\;\rightarrow\;(\tau\downarrow\,\rightarrow\,\varphi^{\tau}_{\alpha})$,
provided @{text \<tau>} is substitutable for @{text \<alpha>} in @{text \<phi>}}
\end{quote}

Here $\varphi^{\tau}_{\alpha}$ is defined in PLM item (14) as recursively replacing all occurrences
of @{text \<open>\<alpha>\<close>} in @{text \<open>\<phi>\<close>} that are not bound @{emph \<open>within @{text \<phi>} itself\<close>} with @{text \<tau>}.

The precise definition of @{emph \<open>being substitutable\<close>} can be found in PLM item (15).
In particular, it states the following summary:

\begin{quote}
\Squ{@{text \<tau>} is substitutable at an occurrence of @{text \<alpha>} in @{text \<phi>} or @{text \<sigma>} just in
case every occurrence of any variable @{text \<beta>} free in @{text \<tau>} remains an occurrence
that is free when @{text \<tau>} is substituted for that occurrence of @{text \<alpha>} in @{text \<phi>} or @{text \<sigma>}.}
\end{quote}

and further:

\begin{quote}
\Squ{@{text \<tau>} is substitutable for @{text \<alpha>} in @{text \<phi>} or @{text \<sigma>} just in case @{text \<tau>}
is substitutable at every free occurrence of @{text \<alpha>} in @{text \<phi>} or @{text \<sigma>}.}
\end{quote}

In the embedding, the same axiom is stated as follows:

\begin{quote}
@{thm[display] "cqt:1"[axiom_inst, print_as_theorem, of _ \<phi> \<tau>]}
\end{quote}

Internally, @{term \<phi>} is a function acting on terms and both @{text \<open>\<phi>{\<alpha>}\<close>}, resp.
@{text \<open>\<phi>{\<tau>}\<close>}, are the function application of @{term \<phi>} to @{text \<alpha>}, resp. @{text \<tau>}.
The following is the HOL representation of the formula of the axiom:
\<close>
(*<*)unbundle AOT_no_syntax(*>*)
text\<open>\begin{quote}@{term \<open>\<guillemotleft>\<forall>\<alpha> \<phi>{\<alpha>} \<rightarrow> (\<tau>\<down> \<rightarrow> \<phi>{\<tau>})\<guillemotright>\<close>}\end{quote}\<close>
(*<*)unbundle AOT_syntax(*>*)
text\<open>

The @{text \<open>\<forall>\<close>}-quantifier is represented as the function application
of the constant @{const AOT_forall} to the meta-logical @{text \<open>\<lambda>\<close>}-abstraction of
@{term \<phi>} applied to the bound variable @{term \<alpha>}.
The substitution of @{term \<tau>} for @{term \<alpha>} in @{term \<phi>} is represented as the
function application of @{term \<phi>} to @{term \<tau>}.

As mentioned in section~\ref{alphabetic-variants-de-bruijin}, internally Isabelle
represents bound variables using de-Bruijn indices that uniquely associate any
bound variable with its binder, independently of the name of the variable. @{text \<open>\<beta>\<close>}-reduction of 
the function application of an abstraction to a term merely replaces the bound variables
referring to the outermost abstracted variable. Thereby, substitutability is implicit
in the construction: applying a meta-variable that is represented as a function
to different arguments does not affect variables bound by nested binders.

Therefore, strictly speaking, the implementation of the axiom in the embedding is stronger
than the axiom stated in PLM. Consider the following instance of the axiom:

\begin{quote}
@{thm[display] "cqt:1"[where \<phi>=\<open>\<lambda>\<tau> . \<guillemotleft>\<exists> \<beta>\<^bold>(\<beta> = \<tau>\<^bold>)\<guillemotright>\<close>, axiom_inst, print_as_theorem, of \<tau>]}
\end{quote}

Here @{term \<phi>} is @{term \<open>\<guillemotleft>\<exists>\<beta>(\<beta> = \<alpha>)\<guillemotright>\<close>}. Now in PLM's terms, @{text \<beta>} itself would
not be substitutable for @{term \<alpha>} in @{term \<phi>}, since substituting @{term \<beta>} for @{term \<alpha>}
directly would result in @{term \<beta>} being bound by the existence quantifier.
However, Isabelle allows this instantiation and resolves this issue by automatically
generating an alphabetic variant of the nested binder. The following is the direct result
of instantiating @{term \<phi>} to @{term \<open>\<guillemotleft>\<exists>\<beta>(\<beta> = \<alpha>)\<guillemotright>\<close>} and @{term \<open>\<tau>\<close>} to @{term \<beta>} in
above axiom:

\begin{quote}
@{thm[display] "cqt:1"[where \<phi>=\<open>\<lambda>\<tau> . \<guillemotleft>\<exists> \<beta>\<^bold>(\<beta> = \<tau>\<^bold>)\<guillemotright>\<close> and \<tau>=\<open>\<beta>\<close>, axiom_inst, print_as_theorem]}
\end{quote}

While this is not a direct instance of the axiom in PLM, we have argued in section~\ref{alphabetic-variants}
that it is a meta-theorem of AOT that all alphabetic variants are interderivable.
Furthermore, for any @{term \<phi>} an alphabetic variant can be constructed that makes
any @{term \<tau>} substitutable for an occurrence of @{term \<alpha>} in @{term \<phi>} by replacing
all variables bound in @{term \<phi>} that occur free in @{term \<tau>} by fresh variables.

This signifies one of the main advantages and simultaneously disadvantages of the
use of SSEs. While the use of the meta-logical mechanisms to deal with alphabetic
variants and binders allows the implementation to forgo a custom implementation
of concepts like substitutions and substitutability, this in turn requires a careful
meta-theoretical analysis to assure that the resulting implementation remains faithful.
However, for practical purposes the advantages outweigh the disadvantages. Not only
is a custom implementation of substitutions and alphabetic variants error-prone and cumbersome,
since it is at the same time seemingly trivial, but nonetheless implementationally complex, but relying
on the meta-logical implementation has also significant advantages for automated reasoning:
For example, while by construction Isabelle will see alphabetic variants as identical entities and
can freely substitute them, manual substitution, as it would be required for deep embeddings,
would require rigorous proofs about recursively defined transformations on the deep syntax representation
that can quickly go beyond the limits of the available automation capabilities, even without
attempting to prove complex theorems.
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
\mbox{@{lemma \<open>print_as_theorem \<guillemotleft>\<forall>F ([F]x \<rightarrow> [F]x)\<guillemotright>\<close> by (auto intro!: print_as_theoremI "\<rightarrow>I" GEN)}}
not only implicitly asserts its alphabetic variants, e.g. 
\mbox{@{lemma \<open>print_as_theorem \<guillemotleft>\<forall>G ([G]x \<rightarrow> [G]x)\<guillemotright>\<close> by (auto intro!: print_as_theoremI "\<rightarrow>I" GEN)}},
but can also be directly instantiated for a different free individual variable, e.g. 
\mbox{@{lemma \<open>print_as_theorem \<guillemotleft>\<forall>G ([G]y \<rightarrow> [G]y)\<guillemotright>\<close> by (auto intro!: print_as_theoremI "\<rightarrow>I" GEN)}}.
In the notation of AOT this means that we actually state the theorem
\mbox{@{lemma \<open>print_as_theorem \<guillemotleft>\<forall>G ([G]\<nu> \<rightarrow> [G]\<nu>)\<guillemotright>\<close> by (auto intro!: print_as_theoremI "\<rightarrow>I" GEN)}},
where @{term \<nu>} ranges over all names for individual variables. While PLM does not derive
a meta-rule that matches this principle, it is usually a straightforward consequence of a series of
applications of the meta-rule of universal generalization GEN followed by applications
of the rule of @{text \<open>\<forall>\<close>}Elimination for variables. However, to formulate this as a general
principle, some care has to be taken and we have to additionally rely on the collapse of
alphabetic variants.

We start by stating and proving the trivial case as a rule in AOT's system:

\begin{quote}
\Squ{If @{text \<open>\<turnstile> \<phi>\<close>}, then \<^latex>\<open>$\vdash \varphi^\beta_\alpha$\<close> where @{text \<beta>} is substitutable for @{text \<alpha>} in @{text \<phi>}.}
\end{quote}

Assume @{text \<open>\<turnstile> \<phi>\<close>}. Since the derivation of @{text \<phi>} does not need any premises,
it follows by the rule of universal generalization (GEN) (see section~\ref{MetaRules}) that @{text \<open>\<turnstile> \<forall>\<alpha> \<phi>\<close>}.@{footnote \<open>Note that we are using PLM's
syntactic convention here, i.e. @{term \<alpha>} may occur free in @{term \<phi>}, which using our conventions we would usually
signify by writing @{text \<open>\<phi>{\<alpha>}\<close>}.\<close>} Since by assumption
@{text \<beta>} is substitutable for @{text \<alpha>} in @{text \<phi>} we can immediately conclude by @{text \<open>\<forall>\<close>}Elimination (see~\nameref{AOT:rule-ui:3})
that \<^latex>\<open>$\vdash \varphi^\beta_\alpha$\<close>.

However, we want to generalize this rule further to a version that allows for premises and does
not require the proviso that @{text \<beta>} is substitutable for @{text \<alpha>} in @{text \<phi>}.

To that end the next step is to generalize above rule to include premises:

\begin{quote}
\Squ{If @{text \<open>\<Gamma> \<turnstile> \<phi>\<close>}, then \<^latex>\<open>$\Gamma^\beta_\alpha \vdash \varphi^\beta_\alpha$\<close> where (1) @{text \<beta>} is substitutable for @{text \<alpha>} in @{text \<phi>} and
(2) @{text \<beta>} is sustitutable for @{text \<alpha>} in all @{text \<open>\<psi> \<in> \<Gamma>\<close>} and (3) \<^latex>\<open>$\Gamma^\beta_\alpha$\<close> is
the set of all \<^latex>\<open>$\psi^\beta_\alpha$\<close> for @{text \<open>\<psi> \<in> \<Gamma>\<close>}.}
\end{quote}

One way to show this is by first eliminating all premises in @{text \<Gamma>} using the deduction theorem (see section~\ref{MetaRules})
and then referring to the simpler rule above. The resulting theorem will yield \<^latex>\<open>$\varphi^\beta_\alpha$\<close>
from \<^latex>\<open>$\Gamma^\beta_\alpha$\<close> by successive applications of modus ponens.

In particular, let @{text \<open>\<psi>\<^sub>1, \<dots>, \<psi>\<^sub>n\<close>} be the list of premises in @{text \<open>\<Gamma>\<close>}, s.t.
@{text \<open>\<psi>\<^sub>1, \<dots>, \<psi>\<^sub>n \<turnstile> \<phi>\<close>}.@{footnote \<open>Note the discussion of derivations in PLM item (59).\<close>} By the deduction theorem it follows that @{text \<open>\<psi>\<^sub>1, \<dots>, \<psi>\<^bsub>n-1\<^esub> \<turnstile> \<psi>\<^sub>n \<rightarrow> \<phi>\<close>}.
Continuing to apply the deduction theorem, we end up with @{text \<open>\<turnstile> \<psi>\<^sub>1 \<rightarrow> (\<psi>\<^sub>2 \<rightarrow> (\<dots> \<rightarrow> (\<psi>\<^sub>n \<rightarrow> \<phi>)\<dots>)\<close>}.
By assumption @{text \<beta>} is substitutable for @{text \<alpha>} in this theorem, hence by the rule above we
can conclude that: \<^latex>\<open>$\vdash {\psi_1}^\beta_\alpha \rightarrow ({\psi_2}^\beta_\alpha \rightarrow (\dots \rightarrow ({\psi_n}^\beta_\alpha \rightarrow \varphi^\beta_\alpha)\dots)$\<close>

Since all \<^latex>\<open>${\psi_i}^\beta_\alpha$\<close> are in \<^latex>\<open>$\Gamma^\beta_\alpha$\<close>, it follows that \<^latex>\<open>$\Gamma^\beta_\alpha \vdash \varphi^\beta_\alpha$\<close> by @{text n}
applications of modus ponens.

What remains is the proviso that @{text \<beta>} be substitutable for @{text \<alpha>} in @{text \<phi>} and
in all @{text \<open>\<psi> \<in> \<Gamma>\<close>}. However, note that for every @{text \<phi>} and @{text \<Gamma>} we can choose
alphabetic variants @{text \<phi>'} and @{text \<Gamma>'} that replace all bound occurrences of @{text \<beta>}
with a fresh variable @{text \<gamma>} that does not occur in @{text \<phi>} or in any @{text \<open>\<psi> \<in> \<Gamma>\<close>}.

In the last section we have seen that @{text \<open>\<Gamma> \<turnstile> \<phi>\<close>}, if and only if @{text \<open>\<Gamma>' \<turnstile> \<phi>'\<close>}. Since 
@{text \<beta>} is trivially substitutable for @{text \<alpha>} in @{text \<open>\<phi>'\<close>} and in all @{text \<open>\<psi> \<in> \<Gamma>'\<close>},
it follows by the rule above that \<^latex>\<open>${\Gamma'}^\beta_\alpha \vdash {\varphi'}^\beta_\alpha$\<close>. Since Isabelle
collapses alphabetic variants by eliminating concrete variable names with de-Bruijn indices,
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

Note that this is still an @{emph \<open>instance\<close>} of the original theorem, but we just cannot state this
instance without simultaneously renaming the bound variable. Even though, internally, the variable
names are eliminated, concrete variable names, of course, still make a difference when @{emph \<open>parsing\<close>}
inner syntax.

Given this discussion, the meta-rule derived above together and the justification of
the collapse of alphabetic variants, we may conclude that the fact that
Isabelle implicitly generalizes free variables to schematic variables remains faithful
to the derivational system of AOT.@{footnote \<open>Note that for free meta-variables
the generalization to schematic form is in fact a requirement for being able
to instantiate the meta-variables to arbitrary terms as intended by AOT.\<close>}
\<close>

subsection\<open>Trivial Accessibility Relation for the Modal Logic\<close>text\<open>\label{TrivialAccessibilityRelation}\<close>

text\<open>As already hinted at in section~\ref{SimpleS5}, choosing a trivial accessibility relation (respectively, equivalently,
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
  by (metis (mono_tags, opaque_lifting) assms equiv_def actual_def box_def impl_def valid_def)

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
of this way to extend our representation of AOT. However, such an extension of the models may
constitute an interesting topic for future research. We conjecture that it is possible to construct models
with a different actual world for each equivalence class of worlds, and that doing so could
lead to a means to reproduce the strict distinction between modally-strict and modally-fragile theorems
in AOT as follows (recall section~\ref{ModallyStrictFragile}): while modally-strict theorems could be modelled as being valid in all possible worlds,
i.e. across all equivalence classes in the accessibility relation, modally-fragile axioms could be
modelled as being valid in a globally-fixed actual world. This way, adding a contingent truth to the
modally-fragile derivation system would merely assert that it holds in the globally-fixed actual world,
whereas a modally-strict proof of some statement being @{emph \<open>actually true\<close>} would require that
statement to be true in @{emph \<open>all\<close>} actual worlds. This would constitute a model in which 
@{text \<open>\<turnstile> \<phi>\<close>} would no longer imply @{text \<open>\<turnstile>\<^sub>\<box> \<^bold>\<A>\<phi>\<close>} and, consequently, in which the converse of RN fails,
i.e. @{text \<open>\<turnstile> \<box>\<phi>\<close>} would no longer imply @{text \<open>\<turnstile>\<^sub>\<box> \<phi>\<close>} (while the former merely requires @{text \<open>\<phi>\<close>}
to be valid in all worlds accessible from the globally-fixed actual world, the latter also requires
@{text \<open>\<phi>\<close>} to be true even in worlds inaccessible from the global actual world).
\<close>

subsection\<open>Primitive Inferences of Isabelle/Pure and Derivations of AOT\<close>text\<open>\label{PureVsAOT}\<close>

text\<open>
As mentioned in section~\ref{SSEsWithAbstractionLayers}, being able to trust
the abstraction layer constructed for AOT relies on verifying that
inferences in the meta-logic correspond to valid reasoning in the system of PLM,
given that the set of available theorems and rules is suitably restricted.

We implement the rules of AOT as rules in Isabelle's Pure logic.
The primitive inferences of Pure are described in section 2.3 of~\cite{IsabelleImplementation}.@{footnote \<open>In
particular figure~\ref{fig:prim-rules} is presented as figure 2.2 in section 2.3.1 of~\cite{IsabelleImplementation}.\<close>}
In this section we will in particular argue that the rules in figure~\ref{fig:prim-rules},
when applied in our abstraction layer, will correspond to valid reasoning in AOT.@{footnote \<open>As noted below,
an exhaustive analysis would also need to consider the richer logic of Isabelle/HOL.\<close>}

  \begin{figure}[H]
  \begin{center}
  \[
  \infer[\<open>(axiom)\<close>]{\<open>\<turnstile> A\<close>}{\<open>A \<in> \<Theta>\<close>}
  \qquad
  \infer[\<open>(assume)\<close>]{\<open>A \<turnstile> A\<close>}{}
  \]
  \[
  \infer[\<open>(\<And>\<hyphen>intro)\<close>]{\<open>\<Gamma> \<turnstile> \<And>x. B[x]\<close>}{\<open>\<Gamma>
\<turnstile> B[x]\<close> & \<open>x \<notin> \<Gamma>\<close>}
  \qquad
  \infer[\<open>(\<And>\<hyphen>elim)\<close>]{\<open>\<Gamma> \<turnstile> B[a]\<close>}{\<open>\<Gamma> \<turnstile>
\<And>x. B[x]\<close>}
  \]
  \[
  \infer[\<open>(\<Longrightarrow>\<hyphen>intro)\<close>]{\<open>\<Gamma> - A \<turnstile> A \<Longrightarrow>
B\<close>}{\<open>\<Gamma> \<turnstile> B\<close>}
  \qquad
  \infer[\<open>(\<Longrightarrow>\<hyphen>elim)\<close>]{\<open>\<Gamma>\<^sub>1 \<union> \<Gamma>\<^sub>2 \<turnstile>
B\<close>}{\<open>\<Gamma>\<^sub>1 \<turnstile> A \<Longrightarrow> B\<close> & \<open>\<Gamma>\<^sub>2 \<turnstile>
A\<close>}
  \]
  \caption{Primitive inferences of Pure}\label{fig:prim-rules}
  \end{center}
  \end{figure}

The meta-logical @{emph \<open>axiom\<close>} rule corresponds to PLM items (63.1) and (63.3) which
state that axioms and theorems of AOT can be used in derivations.

@{emph \<open>assume\<close>} corresponds to the special case of PLM item (63.2) given as
@{text \<open>\<phi> \<turnstile> \<phi>\<close>}.

@{emph \<open>@{text \<open>\<And>\<close>}-intro\<close>} and @{emph \<open>@{text \<open>\<And>\<close>}-elim\<close>} align with our implementations of PLM's GEN rule and
@{text \<open>\<forall>\<close>}-elimination:
Using our notational convention, it is an instance of @{emph \<open>@{text \<open>\<And>\<close>}-intro\<close>} that
@{text \<open>\<Gamma> \<turnstile> \<phi>{\<alpha>}\<close>} and @{text \<open>\<alpha> \<notin> \<Gamma>\<close>} implies @{text \<open>\<Gamma> \<turnstile> for arbitrary \<alpha>: \<phi>{\<alpha>}\<close>}.
The latter is the precondition of our GEN rule, i.e. we can derive @{text \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close>}
in AOT. Similarly, the @{emph \<open>@{text \<open>\<And>\<close>}-elim\<close>} rule corresponds to
the rule given in~\nameref{AOT:rule-ui:3}, which states that we can derive
@{text \<open>\<phi>{\<beta>}\<close>} from @{text \<open>\<forall>\<alpha> \<phi>{\<alpha>}\<close>}.

Note, however, that the @{emph \<open>@{text \<open>\<And>\<close>}-intro\<close>} and @{emph \<open>@{text \<open>\<And>\<close>}-elim\<close>}
rules are not restricted to our defined types of object-level variables of AOT.
In particular, they can also be applied to meta-variables ranging over terms of AOT.
However, applications of @{emph \<open>@{text \<open>\<And>\<close>}-intro\<close>} and @{emph \<open>@{text \<open>\<And>\<close>}-elim\<close>}
to meta-variables exactly corresponds to the fact that PLM allows to instantiate
arbitrary terms of a given type in place of its meta-variables.

The @{emph \<open>@{text \<open>\<Longrightarrow>\<close>}-intro\<close>} and @{emph \<open>@{text \<open>\<Longrightarrow>\<close>}-elim\<close>} rules correspond
to the deduction theorem (PLM item (75)), which states that if @{text \<open>\<Gamma>, \<phi> \<turnstile> \<psi>\<close>},
then @{text \<open>\<Gamma> \<turnstile> (\<phi> \<rightarrow> \<psi>)\<close>} and the meta-rule stated in PLM item (63.5) stating
that if @{text \<open>\<Gamma>\<^sub>1 \<turnstile> \<phi>\<close>} and @{text \<open>\<Gamma>\<^sub>2 \<turnstile> (\<phi> \<rightarrow> \<psi>)\<close>}, then @{text \<open>\<Gamma>\<^sub>1,\<Gamma>\<^sub>2 \<turnstile> \<psi>\<close>}.

Furthermore, Pure is equipped with a primitive equality that allows for
substituting terms that are meta-logically equal.
Such substitutions are justified, since it is a property of our embedding that
PLM's identity corresponds to meta-logical equality on denoting terms
on the one hand (see~\nameref{AOT:AOT_eq_spec}) and the fact that distinct
non-denoting terms in PLM are @{emph \<open>not\<close>} meta-logically identical in our embedding on the
other hand (e.g. recall the fact that non-denoting definite descriptions can be assigned distinct @{emph \<open>null\<close>}-urelements).
Furthermore we argued in section~\ref{alphabetic-variants} that the meta-logical equality
of alphabetic variants is consistent with reasoning in PLM.

While we do not claim that this analysis is exhaustive,@{footnote \<open>While the rules of our
target theory are implemented in the format of rules of Isabelle/Pure, the automated proving methods we use (e.g.
@{method metis}, @{method meson} and @{method blast}) work relative to the richer logic of
Isabelle/HOL (see chapter~2 of ~\cite{IsabelleLogics}) and for a full account the
relevant axioms and inferences of Isabelle/HOL would need to be considered as well.\<close>}
it nevertheless provides strong evidence for the assumption that reasoning in our abstraction layer is in fact reproducible as
derivations in the sense of PLM. For the purpose of a seamless exchange of results
between our embedding and PLM, this level of assurance has proven sufficient. In our
work we have not encountered a proof in our abstraction layer that could not be
reproduced in the system of PLM.

Conversely, the fact that we can derive PLM's axioms and rules in the
embedding shows that derivations of PLM can be reproduced in the embedding.

An interesting project for future research may be to implement AOT directly as an object logic
of Isabelle/Pure. However, instead of being able to rely on the soundness of
Isabelle/HOL as semantic backend, this would require a direct axiomatization of AOT in Pure,
which means that we would loose the ability to easily judge the consistency of our representation
of AOT and of extensions of its axiom system, which is one of the prime objectives of
our current project.
\<close>

section\<open>Artifactual Theorems\<close>text\<open>\label{ArtifactualTheorems}\<close>

text\<open>
In general, artifactual theorems can be defined as follows:

Let $T$ be the target theory and $M$ be the theory in which we are
building a model @{text \<open>\<M>\<close>} of $T$ (so that @{text \<open>\<M>\<close>} is expressible in $M$).
Then an artifactual theorem $\phi$ of $T$ relative to $M$ and @{text \<open>\<M>\<close>}
is a formula expressible in the language of $T$ that is derivable
in $M$ from @{text \<open>\<M>\<close>} but which is not derivable in $T$ itself.  For
example, if $T$ is second-order logic with identity (2OL=) and $M$
is ZF+U (Zermelo-Fraenkel set theory with Urelements) and the model
@{text \<open>\<M>\<close>} in ZF+U represents the predicates of $T$ as sets of Urelements
in ZF+U, then the claim:

$\phi$ =  $\forall x(Fx \equiv Gx) \to F=G$

becomes derivable in ZF+U from @{text \<open>\<M>\<close>}, even though it is not a theorem of 2OL=.
(in this case, $\phi$ is interpreted in @{text \<open>\<M>\<close>} as an
instance of the axiom of Extensionality of ZF+U.) This particular
$\phi$ is therefore an artifactual theorem of 2OL= relative to ZF+U 
and the model @{text \<open>\<M>\<close>} of predicates as sets.  

The abstraction layer we define in our embedding aims to disallow
artifactual theorems by limiting theoremhood to what can be
derived from the representation of the axioms and rules of $T$
in @{text \<open>\<M>\<close>}; thus, appeals to the axioms and rules of $M$ (beyond those that
represent the rules of $T$) are not allowed in the derivations of theorems of $T$.
\<close>
(*
text\<open>
Artifactual Theorems are theorems that are valid in a concrete model, respectively
valid with respect to a concretely defined semantics, but which are not derivable from
a formal system itself.
\<close>

text\<open>
The abstraction layer we define in our embedding aims to disallow deriving artifactual
theorems by restricting proofs to solely rely on the implementation of the axioms and
deduction rules of AOT itself.

\<close>
*)

text\<open>
We have discussed in section~\ref{MetaTheorems} that for technical reasons the
embedding collapses certain classes of statements (e.g. alphabetic variants), but that
this merely extends to statements that are interderivable in AOT itself. As a result
we can reasonably assume that well-formed statements of AOT that are provable in the abstraction layer of
our embedding also have a derivation in AOT, i.e. only theorems that are derivable from the formal system
$T$ itself are derivable from @{text \<open>\<M>\<close>} using the representation of the axioms and rules of $T$.

Ideally, the construction of @{text \<open>\<M>\<close>} is general enough, s.t. even using the full system
of axioms and rules of $M$, no theorem is derivable from @{text \<open>\<M>\<close>} that does not have
a derivation in the formal system of $T$ itself. Or in other words, ideally, there are
no artifactual theorems and the abstraction layer becomes unnecessary. However, 
in the case of our embedding, there are still counterexamples.

As a matter of fact, comparing derivability in the abstraction layer of the embedding,
respectively in the formal system of PLM itself, with validity in our underlying
semantic structure has been the driving force in our collaboration with the authors of AOT.

In particular, whenever a potential artifactual theorem was recognized, this resulted
in an analysis of the discrepancy which regularly led to either a further abstraction
of the semantics used in the embedding to eliminate the theorem or to an extension of AOT's
axiom system itself, in case it turned out that (1) the discrepancy could be resolved by
a natural extension of AOT's axiom system, (2) this extension had merit in that it allowed
for deriving new interesting theorems in AOT or that it simplified existing derivations
and (3) the extension was philosophically justifiable.

An example of a statement that is now a theorem of AOT, but originated as an artifactual
theorem of the embedding, is the necessary and sufficient conditions for relations to denote
discussed in section~\ref{KirchnersTheorem}. An earlier example is the coexistence axiom
discussed in~\ref{MoveToFreeLogic}, the formulation of which was based on a similar
principle that was discovered in the analysis of the semantic properties of the embedding
at the time.

This process is ongoing and in the remainder of this section we will discuss some
examples of remaining artifactual theorems and the current state of their discussion.
\<close>

subsection\<open>Identity of Projections to Indistinguishable Objects\<close>text\<open>\label{ArtifactAczel}\<close>

(*<*)
AOT_theorem Artifactual1: \<open>\<forall>F ([F]a \<equiv> [F]b) \<rightarrow> [\<lambda>x [R]xa] = [\<lambda>x [R]xb]\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<forall>F([F]a \<equiv> [F]b)\<close>
  {
    fix c
    AOT_have \<open>[\<lambda>x (c[\<lambda>z [R]zx])]\<down>\<close>
      by (safe intro!: "cqt:2" AOT_instance_of_cqt_2_intro_next)
    AOT_hence 1: \<open>\<forall>x \<forall>y (\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> \<box>(c[\<lambda>z [R]zx] \<equiv> c[\<lambda>z [R]zy]))\<close>
      using "kirchner-thm-cor:1"[THEN "\<rightarrow>E"] \<comment> \<open>see~\nameref{AOT:kirchner-thm-cor:1}\<close>
      by blast
    AOT_have \<open>\<box>(c[\<lambda>z [R]za] \<equiv> c[\<lambda>z [R]zb])\<close>
      using 1[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF 0] by blast
  }
  AOT_hence \<open>\<forall>c \<box>(c[\<lambda>z [R]za] \<equiv> c[\<lambda>z [R]zb])\<close>
    by (rule GEN)
  AOT_hence \<open>\<box>\<forall>c(c[\<lambda>z [R]za] \<equiv> c[\<lambda>z [R]zb])\<close>
    by (rule BF[THEN "\<rightarrow>E"]) \<comment> \<open>see~\nameref{AOT:BFs:1}\<close>
  AOT_thus \<open>[\<lambda>z [R]za] = [\<lambda>z [R]zb]\<close>
    by (AOT_subst_def "identity:2") \<comment> \<open>see~\nameref{AOT:identity:2}\<close>
       (auto intro!: "&I" "cqt:2")
qed
AOT_theorem Artifactual2: \<open>\<forall>F ([F]a \<equiv> [F]b) \<rightarrow> [\<lambda>x [R]ax] = [\<lambda>x [R]bx]\<close>
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<forall>F([F]a \<equiv> [F]b)\<close>
  {
    fix c
    AOT_have \<open>[\<lambda>x (c[\<lambda>z [R]xz])]\<down>\<close>
      by (safe intro!: "cqt:2" AOT_instance_of_cqt_2_intro_next)
    AOT_hence 1: \<open>\<forall>x \<forall>y (\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> \<box>(c[\<lambda>z [R]xz] \<equiv> c[\<lambda>z [R]yz]))\<close>
      using "kirchner-thm-cor:1"[THEN "\<rightarrow>E"] \<comment> \<open>see~\nameref{AOT:kirchner-thm-cor:1}\<close>
      by blast
    AOT_have \<open>\<box>(c[\<lambda>z [R]az] \<equiv> c[\<lambda>z [R]bz])\<close>
      using 1[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF 0] by blast
  }
  AOT_hence \<open>\<forall>c \<box>(c[\<lambda>z [R]az] \<equiv> c[\<lambda>z [R]bz])\<close>
    by (rule GEN)
  AOT_hence \<open>\<box>\<forall>c(c[\<lambda>z [R]az] \<equiv> c[\<lambda>z [R]bz])\<close>
    by (rule BF[THEN "\<rightarrow>E"]) \<comment> \<open>see~\nameref{AOT:BFs:1}\<close>
  AOT_thus \<open>[\<lambda>z [R]az] = [\<lambda>z [R]bz]\<close>
    by (AOT_subst_def "identity:2") \<comment> \<open>see~\nameref{AOT:identity:2}\<close>
       (auto intro!: "&I" "cqt:2")
qed
AOT_theorem Artifactual3:
  shows \<open>\<forall>F([F]a \<equiv> [F]b) \<rightarrow> \<forall>G\<^bold>(([G]a) = ([G]b)\<^bold>)\<close>
  unfolding explicitParen_def
proof(rule "\<rightarrow>I")
  AOT_assume 0: \<open>\<forall>F([F]a \<equiv> [F]b)\<close>
  {
    fix G
    {
      fix c
      AOT_have \<open>[\<lambda>x (c[\<lambda>z [G]x])]\<down>\<close>
        by (safe intro!: GEN "cqt:2" AOT_instance_of_cqt_2_intro_next)
      AOT_hence 1: \<open>\<forall>x \<forall>y (\<forall>F ([F]x \<equiv> [F]y) \<rightarrow> \<box>(c[\<lambda>z [G]x] \<equiv> c[\<lambda>z [G]y]))\<close>
        using "kirchner-thm-cor:1"[THEN "\<rightarrow>E"] \<comment> \<open>see~\nameref{AOT:kirchner-thm-cor:1}\<close>
        by blast
      AOT_have \<open>\<box>(c[\<lambda>z [G]a] \<equiv> c[\<lambda>z [G]b])\<close>
        using 1[THEN "\<forall>E"(2), THEN "\<forall>E"(2), THEN "\<rightarrow>E", OF 0] by blast
    }
    AOT_hence \<open>\<forall>c \<box>(c[\<lambda>z [G]a] \<equiv> c[\<lambda>z [G]b])\<close>
      by (rule GEN)
    AOT_hence \<open>\<box>\<forall>c(c[\<lambda>z [G]a] \<equiv> c[\<lambda>z [G]b])\<close>
      by (rule BF[THEN "\<rightarrow>E"]) \<comment> \<open>see~\nameref{AOT:BFs:1}\<close>
    AOT_hence \<open>[\<lambda>z [G]a] = [\<lambda>z [G]b]\<close>
      by (AOT_subst_def "identity:2") \<comment> \<open>see~\nameref{AOT:identity:2}\<close>
         (auto intro!: "&I" "cqt:2")
    AOT_hence \<open>([G]a) = ([G]b)\<close>
      by (AOT_subst_def "identity:4")
        (auto intro!: "&I" "log-prop-prop:2")
  }
  AOT_thus \<open>\<forall>G([G]a) = ([G]b)\<close>
    by (rule GEN)
qed
(*>*)

text\<open>
A variant of the fact that there are indistinguishable abstract objects
discussed in section~\ref{IndistinguishableAbstractObjects} is the fact that for every
two-place relation of AOT there are distinct abstract objects, s.t. the projections of the relation
to these abstract objects are identical (see~\nameref{AOT:aclassical:1} and~\nameref{AOT:aclassical:2}):

\begin{quote}
@{thm[display] "aclassical:1"[THEN "\<forall>E"(2), print_as_theorem, of R]}
@{thm[display] "aclassical:2"[THEN "\<forall>E"(2), print_as_theorem, of R]}
\end{quote}

However, the construction used for the embedding makes the following stronger statements true:

\begin{quote}
@{thm[display] Artifactual1[print_as_theorem, of a b R]}
@{thm[display] Artifactual2[print_as_theorem, of a b R]}
\end{quote}

This is an artifact of modelling relations as proposition-valued functions acting
on urelements. Since being indistinguishable, @{term \<open>print_term \<guillemotleft>\<forall>F ([F]a \<equiv> [F]b)\<guillemotright>\<close>},
semantically implies that @{term a} and @{term b} share the same urelement, the
projections are forced to collapse.

However, we already mentioned in section~\ref{cqt:2-impl} that it is currently being
considered to extend the base cases of denoting @{text \<open>\<lambda>\<close>}-expressions. This extension
has particular merit in deriving theorems in higher-order object theory. In the second-order
fragment it would be a consequence of this change that the following @{text \<open>\<lambda>\<close>}-expressions denotes by axiom:
\begin{quote}
@{term[display] \<open>print_as_theorem \<guillemotleft>[\<lambda>x (y[\<lambda>z [R]zx])]\<down>\<guillemotright>\<close>}
\end{quote}

Under this assumption, however, the currently artifactual theorems above become
proper theorems of AOT, respectively theorems of the abstraction layer of the embedding (see~\nameref{AOT:AOT_misc.shared_urelement_projection_identity} for a proof).
By an analogous proof (see~\nameref{AOT:AOT_misc.shared_urelement_exemplification_identity}),
even the following becomes derivable (since the extended axiom will also assert that 
@{term \<open>print_as_theorem \<guillemotleft>[\<lambda>x (y[\<lambda>z [G]x])]\<down>\<guillemotright>\<close>}):

\begin{quote}
@{thm[display] Artifactual3[print_as_theorem, of a b]}
\end{quote}

Semantically, this theorem states that whenever two objects share an urelement,
then exemplifying any property results in the same proposition for both of them,
which further consolidates the derivational system of AOT with the representation
of relations as proposition-valued functions acting on urelements.

So while the theorems above are currently artifactual, they are likely to become proper
theorems of the next upcoming version of PLM.
\<close>

subsection\<open>Proposition Identity and Identity of Propositional Relations\<close>
(*<*)
AOT_theorem prop_eq_two_place: \<open>[\<lambda>xy p] = [\<lambda>xy q] \<equiv> p = q\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>[\<lambda>xy p] = [\<lambda>xy q]\<close>
  hence \<open>\<guillemotleft>[\<lambda>xy p]\<guillemotright> = \<guillemotleft>[\<lambda>xy q]\<guillemotright>\<close>
    using AOT_sem_eq by blast
  hence \<open>AOT_lambda (\<lambda>x :: \<kappa>\<times>\<kappa>. AOT_term_of_var p) = AOT_lambda (\<lambda>x. AOT_term_of_var q)\<close>
    by (simp add: cond_case_prod_eta)
  hence \<open>AOT_term_of_var p = AOT_term_of_var q\<close>
    using AOT_sem_lambda_eq_prop_eq
    by blast
  hence \<open>p = q\<close>
    by (metis AOT_var.AOT_term_of_var_inverse)
  AOT_thus \<open>p = q\<close>
    by (simp add: AOT_sem_eq AOT_sem_denotes AOT_model_denotes_\<o>_def)
next
  AOT_assume \<open>p = q\<close>
  moreover AOT_have \<open>[\<lambda>xy p] = [\<lambda>xy p]\<close>
    by (safe intro!: "rule=I:2[lambda]" "cqt:2")
  ultimately AOT_show \<open>[\<lambda>xy p] = [\<lambda>xy q]\<close>
    using "rule=E" by fast
qed
(*>*)
text\<open>

AOT's definition of proposition identity reduces proposition identity to the identity
of unary propositional relations (see~\nameref{AOT:identity:4}):

\begin{quote}
@{thm[display] "identity:4"[of p q]}
\end{quote}

However, due to the fact that our semantic specification of exemplification and
@{text \<lambda>}-abstraction (see~\nameref{AOT:AOT_exe_lambda_spec}) is polymorphic and
simultaneously specifies relations of all arities, it involves the following more
general assertion:

\begin{quote}
@{thm[display] AOT_sem_lambda_eq_prop_eq[of \<phi> \<psi>]}
\end{quote}

It is a consequence of this more general semantic principle that, for example, the following becomes an
artifactual theorem:

\begin{quote}
@{thm[display] prop_eq_two_place[print_as_theorem, of p q]}
\end{quote}

Even though relations are modelled as proposition-valued functions in the embedding,
theoretically, it is possible to allow the @{text \<lambda>}-expressions in question to map
to propositions that are merely necessarily equivalent to @{term p}, resp. @{term q},
but not identical to them. However, since the definition of proposition identity still
needs to be validated, this would require splitting the specification
of exemplification and @{text \<lambda>}-expressions into separate cases for relations
on unary individual terms and tuples of individual terms (e.g. using
an additional system of type classes), which represents a technical challenge. The details
of such a modified construction also depend on more general open questions
regarding @{term n}-ary relation identity and generalized @{text \<eta>}-conversion,
which we will discuss in the next section.
\<close>

subsection\<open>Corner-Cases of Relation Identity\<close>
(*<*)
AOT_theorem Artifactual4: \<open>([\<lambda>x [F]xy]x) = ([F]xy)\<close>
  oops
(*
  unfolding AOT_sem_eq
  apply (auto simp: "log-prop-prop:2")
proof (subst AOT_sem_lambda_denoting)
  AOT_modally_strict {
    AOT_show \<open>\<guillemotleft>Abs_rel (\<lambda>\<kappa>. \<guillemotleft>[F]\<kappa>y\<guillemotright>)\<guillemotright>\<down>\<close>
    unfolding AOT_sem_denotes AOT_model_denotes_rel_def
    apply auto
      apply (subst (0 1) Abs_rel_inverse)
       apply simp
    using AOT_sem_exe_denoting
    apply (metis (no_types, lifting) AOT_meta_prod_equivI(2) AOT_model.AOT_term_of_var AOT_model_denotes_rel.rep_eq AOT_sem_denotes)
     apply (subst (asm) Abs_rel_inverse)
      apply simp
     apply (meson "russell-axiom[exe,2,1,1].\<psi>_denotes_asm" AOT_sem_denotes)
    apply (subst (0 1) Abs_rel_inverse)
     apply simp
    by (simp add: AOT_model_regular_\<kappa>_def)
  } note 0 = this
  show \<open>AOT_exe (Abs_rel (\<lambda>x. AOT_exe (AOT_term_of_var F) (x, AOT_term_of_var y))) (AOT_term_of_var x) =
    AOT_exe (AOT_term_of_var F) (AOT_term_of_var x, AOT_term_of_var y)\<close>
    by (simp add: "0" AOT_sem_exe_denoting Abs_rel_inverse)
qed
*)
  thm "identity:3[2]"[of \<open>\<guillemotleft>[\<lambda>xy [F]xya]\<guillemotright>\<close> \<open>\<guillemotleft>[\<lambda>xy [G]xya]\<guillemotright>\<close>]
      "identity:3[2]"[of \<open>\<guillemotleft>[\<lambda>xy [F]xay]\<guillemotright>\<close> \<open>\<guillemotleft>[\<lambda>xy [G]xay]\<guillemotright>\<close>]
      "identity:3[2]"[of \<open>\<guillemotleft>[\<lambda>xy [F]axy]\<guillemotright>\<close> \<open>\<guillemotleft>[\<lambda>xy [G]axy]\<guillemotright>\<close>]
(*>*)

text\<open>
AOT involves two axiomatic, respectively definitional claims about identity between
@{text n}-ary (@{text \<open>n \<ge> 2\<close>}) relation terms (besides the identity of alphabetic variants), in particular @{text \<open>\<eta>\<close>}-conversion:

\begin{quote}
@{thm[display] "lambda-predicates:3"[axiom_inst, print_as_theorem, of F]}
\end{quote}

As well as @{text \<open>n\<close>}-ary relation identity, e.g. for @{text \<open>n = 2\<close>}:

\begin{quote}
@{thm[display] "identity:3[2]"[of \<Pi> \<Pi>']}
\end{quote}

However, AOT does not presuppose that nested atomic exemplification formulas
in @{text \<lambda>}-expressions can be arbitrarily contracted to identical relations.
For example, none of the following are theorems of AOT:

\begin{quote}
@{term[display] \<open>print_as_theorem \<guillemotleft>[\<lambda>xy [\<lambda>z [F]zy]x] = [\<lambda>xy [F]xy]\<guillemotright>\<close>}
@{term[display] \<open>print_as_theorem \<guillemotleft>[\<lambda>xy [\<lambda>z [F]xz]y] = [\<lambda>xy [F]xy]\<guillemotright>\<close>}
@{term[display] \<open>print_as_theorem \<guillemotleft>[\<lambda>xy [\<lambda>z [F]zy]x] = [\<lambda>xy [\<lambda>z [F]xz]y]\<guillemotright>\<close>}
\end{quote}

The embedding constructs @{text \<open>\<lambda>\<close>}-abstraction and exemplification using the
@{command specification} command by postulating that @{text \<open>\<lambda>\<close>}-abstraction and exemplification
have to exhibit certain properties (e.g. @{text \<open>\<beta>\<close>}- and @{text \<open>\<eta>\<close>}-conversion) and by then providing
a concrete witness that satisfies these properties.

However, the postulated properties given in the specification go beyond the axioms of
AOT they ultimately validate. Validating the axioms of AOT for arbitrary
@{text n}-ary relations in the embedding while maintaining the definition of @{text n}-ary relation identity
requires, at least in the current construction of the embedding, additional properties
for @{text \<open>\<lambda>\<close>}-abstraction and exemplification.@{footnote \<open>For example, the property
named @{text AOT_sem_exe_denoting} in~\nameref{AOT:AOT_exe_lambda_spec} is solely
used for validating @{text n}-ary relation identity.\<close>}

While the artifactual theorems above are validated by the provided witness for our specification, it
is currently unknown whether the properties postulated in the specification
are sufficient to derive them as artifactual theorem. Neither can @{command nitpick}
provide a counterexample for the theorem, nor can @{command sledgehammer} construct
a proof from the specification, so further manual inspection of the situation is
required.

Interestingly, in general, AOT refrains from presuming the identity of its intensional
entities, even under conditions that would usually be assumed to imply equality.
@{text \<open>\<eta>\<close>}-conversion is a notable exception to this principle. However, there are
also arguments for @{emph \<open>rejecting\<close>} @{text \<open>\<eta>\<close>}-conversion in an hyperintensional
context that is meant to accurately represent human thought and language, see e.g.~\cite{ProperTreatmentOfPredication}.

So independently of the potential artifactual theorem discussed above, it is
an interesting philosophical question whether @{text \<open>\<eta>\<close>}-conversion should be
presumed by axiom at all. Similarly, there are open questions about the definition
of identity of @{text n}-place relations in AOT and a potential alternative definition using
@{text n}-ary encoding as discussed in PLM~\cite{PLM-Oct-13-2021} item (37). Curiously,
while the current definition of @{text n}-ary relation identity reduces the identity of ternary
relations to the identity of all their projections to unary relations, the identity of all their projections to
two-place relations does not imply the identity of direct projections to unary
relations (without a more general contraction principle) and therefore does not imply
the identity of the ternary relations.

We expect that a future more extensive analysis of this issue will,
similarly to previous artifactual theorems, result in further theoretical insights,
ultimately followed by either an enhancement of the formulation of AOT or a refined embedding, in
which e.g. the above might provably not be a theorem (even outside the abstraction layer).
\<close>

section\<open>Discussion\<close>

text\<open>
We have described an implementation of the second-order fragment of AOT in classical
higher-order logic by means of an SSE that can accurately reproduce AOT's reasoning
in an abstraction layer. While our semantic backend
is not provably free of artifactual theorems, this can be explained due to the fact that AOT does
not itself presuppose a strong and exhaustive @{emph \<open>intended semantics\<close>}, relative to which a completeness result
is intended and could be achieved. On the contrary, the authors of AOT explicitly try to avoid letting the axioms and deductive
system of AOT be @{emph \<open>driven by semantics\<close>}, but rather aspire to devise a philosophically
justifiable formal system that stands independently of a set-theoretic semantics and in which
notions like truth values and possible worlds can instead be analysed as objects of the system itself:

\blockquote{It is important to remember that the formal semantics simply provides
a set-theoretic framework in which models of the metaphysical
theory may be constructed. The models serve the heuristic purpose of
helping us to visualize or picture the theory in a rigorous way. It is
extremely important not to confuse the models of the theory with the
world itself. \textelp{} So the goal of our enterprise is not to build a model, but rather to
construct a formal theory that correctly mirrors the structure the world
may have and, as a result, correctly reflects the entailments among the
data.@{footnote \<open>Edward Zalta in~\cite{zalta1988intensional} section 2.4.\<close>}
}

Nevertheless, our semantic analysis could significantly contribute especially to the
theoretical understanding of the conditions, in AOT, under which relations exist.
These existence questions require rigorous philosophical consideration and can
have a profound impact on the axiom system (recall e.g.~\ref{MoveToFreeLogic}).

While there are open questions e.g. concerning the identity of @{term n}-ary relation terms,
we anticipate these questions to be the subject of future debate that will, similar to past examples of similar
discussions, result in both theoretical insights and an improved implementation. 
\<close>
(*

text\<open>
A potential future refinement of the embedding may (1) instead of representing relations as
proposition-valued functions define an intensional type of unary relations that is merely equipped with a
surjective extension function and (2) represent @{text n}-ary relations (@{text \<open>n \<ge> 2\<close>}) directly as a suitably
restricted subset of the set of tuples of @{text n}
projection functions, each of which assigning @{text \<open>n-1\<close>} tuples of individuals an unary relation.@{footnote \<open>This
construction would immediately validate the definition of @{text n}-ary relation identity while avoiding
artifactual theorems without the need for additional null-urelements and a definition of @{emph \<open>regular\<close>} tuples
of individual terms. However, such an implementation would increase the complexity of a generic implementation
of @{text n}-ary relations using type classes, which is a pragmatic reason for attempting to further
refine the implementation based on proposition-valued functions pending the results of a future
discussion of @{text n}-ary relation identity and @{text \<open>\<eta>\<close>}-conversion.\<close>}
\<close>
*)
text\<open>
Given our discussion of the general system of AOT in the previous chapter and its implementation in our
embedding in this chapter, we are now suitably equipped to discuss our implementation
of PLM's construction of natural numbers, including the extended model construction
required for validating its additional axioms.
\<close>

(*<*)
end
(*>*)