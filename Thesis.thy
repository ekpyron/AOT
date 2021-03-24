(*<*)
theory Thesis
  imports AOT_axioms
begin
(*>*)

chapter\<open>Introduction\<close>

section\<open>Motivation\<close>
text\<open>

While automated reasoning environments are already a vital part of the modern analysis
of mathematics and formal systems and their importance can only be expected
to increase in the future, building up a sound reasoning environment from scratch is a highly
non-trivial task. Consequently, there is only few trusted systems that can offer sophisticated
interactive and automated reasoning tools like Coq, HOL-Light or Isablle/HOL (TODO: cite).
Furthermore, most of these systems have at least parts of their logical foundation in common
(for example they are all based on some variation of functional type theory).

On the other hand, there is still an ongoing debate about the most suitable logical system
to be used for the foundations of mathematics (TODO: cite). While higher-order functional type
theory is closely tied to set theory (see \cite{HigherOrderLogicSetTheoryFalseDilemma}, TODO: rethink citation)
and set theory has long been a prime choice for a common denominator of mathematical disciplines
(TODO: cite), it's modern paradox free axiomatization following Zermelo-Fraenkel is often viewed as complex and counter-intuitive,
respectively lacking in philosophical grounding and justification.

While there is prominent research into alternative foundational approaches (e.g. homotopy type
theory; TODO: cite - maybe something else, since homotopy type theory maps just perfectly to HOL...),
a potential practical problem for such approaches and a pragmatic defense of set theory as foundation
is the effort required in building up automated reasoning systems that are on par with the existing
tools that are available for processing theories grounded in set theory.

The following represents an attempt at overcoming this issue. We utilize the concept of a
\emph{shallow semantic embedding} with abstraction layers (TODO: cite) to transfer the merits of
the sophisticated interactive and automated reasoning system Isabelle/HOL to a fundamentally
different foundational system, namely to Abstract Object Theory (TODO: cite).

While our method can potentially be applied to a multitude of logical systems, Abstract Object Theory
is a particularly interesting target. On the one hand it aims to be a foundational metaphysical system
that can serve as the basis for mathematics, linguistics and the sciences (TODO: rethink, cite), while
on the other hand it is based on logical foundations that differ from classical functional higher-order
theory and were even argued to be incompatible (see \cite{rtt}).
In our previous work (see \cite{MScThesis}) we demonstrated how our method for formally analysing
models and semantics for such a system can be beneficial and vital for its soundness.
During our continued work we could contribute to the evolution of Abstract Object Theory and
simultaneously arrived at a faithful representation of its model structure, semantics and
deductive system in Isabelle/HOL that can utilize the existing automated reasoning infrastructure.
As a prime result (TODO: hopefully... but I'm close.) we can show that the construction of Natural
Numbers described in Principia Logico-Metaphysica is logically equivalent to the traditional
set-based construction by proving its algebraic properties as defined in Isabelle/HOL's system
of type classes.

\<close>

section\<open>Previous Work\<close>

text\<open>

The computational analysis of Abstract Object Theory (AOT) was pioneered by Fitelson and Zalta in
\cite{FitelsonZalta}. They used the first-order system Prover9 for their work and were able to 
verify the proofs of the theorems in AOT's analysis of situations and possible worlds in
\cite{zalta1993}. Furthermore, they discovered an error in \cite{PelletierZalta} in a theorem
about Platonic Forms that was left as an exercise.
Other work with Prover9 that does not target AOT includes the simplification of the reconstruction
of Anselm's ontological argument (in \cite{OppenheimerZalta2011}, Oppenheimer and Zalta show that
only one of the three premises they used in \cite{OppenheimerZalta1991} is sufficient) or the
reconstruction of theorems in Spinoza's \emph{Ethics} in \cite{SpinozaProver9}.

However, there are inherent limitations to the approach of analyzing a higher-order theory like AOT
with the help of first-order provers. While it is possible to reason about the first order truth
conditions of statements by introducing sort predicates and using a number of special techniques
to translate the statements into the less-expressive language of multi-sorted first-order logic
(a detailed account of such techniques is given in \cite{AlamaZalta2015}), the complexity of the
resulting representation increases for expressive, higher-order philosophical claims.
In general, this approach may be sufficient for analyzing concrete isolated arguments, but it becomes
infeasible to construct a natural representation of an entire expressive higher-order theory and
its full deductive system.

Independently, the emergence of sophisticated higher-order reasoning environments like Isabelle/HOL
allows for a different approach, namely the analysis of arguments and theories directly in higher-order
logic by constructing Shallow Semantic Embeddings (SSEs) \cite{UniversalReasoning}. In contrast to
a \emph{deep semantic embedding} which defines the syntax of a target system using an inductive data
structure and evaluates statements semantically by recursively traversing this data structure,
a \emph{shallow} semantic embedding instead provides a syntactic translation from the target logic
to the meta-logic. This is done by reusing as much of the infrastructure of the meta-logic as possible,
while \emph{defining} the syntactic elements of the target logic that are not part of
the meta-logic by means of a representation of their semantics. Since sets have a natural
representation in higher-order logic, this approach works well for any logical system that
has a semantics defined in terms of sets.

In \cite{ModalLogics} Benzm\"uller and Paulson represented quantified modal logic using SSEs by means
of embedding modal operators based using their Kripke semantics (TODO cite). This allowed for an
extensive analysis of G\"odel's ontological argument in second-order S5 modal logic (TODO cite), followed
by a range of studies of similar ontological arguments (TODO cite). TODO: newer work by Benzm\"uller.

The advantage of these studies using SSEs compared to the earlier use of Prover9 is that arguments
can be represented their native syntax and are thereby readable and maintainable, while the theorem
proving environments are capable of automatically transforming statements into a suitable first-order
representation on the fly to allow first-order theorem provers like E or SPASS (TODO: cite) perform
proof search much like Prover9 was able to do on a manually constructed first-order representation.

These studies were still mainly concerned with case studies of concrete arguments or
with only conservative extensions of higher-order logic like functional higher-order modal logic.
Furthermore, they relied heavily on the previously available completeness results of second-order modal
logic with respect to Kripke models.

In our own previous work (in \cite{MScThesis}) we applied an extended version of this technique
to AOT. For AOT no extensive prior analysis for canonical models - like Kripke models for higher-order
modal logic - was available. While the so-called Aczel models of object theory (TODO: cite) provided
an important building block for constructing models of AOT in HOL, no full set-theoretic model
of object theory had been constructed. In \cite{MScThesis} we extended the existing Aczel models to
a richer model structure that was capable of approximating the validity of statements of the most
recent formulation of AOT. Furthernmore, we introduced the new concept of \emph{abstraction layers}.
An abstraction layer consists of a derivation of the axioms and deduction rules of a target system
from a given semantics that is then considered as ground truth while "forgetting" the underlying
semantic structure (i.e. the reasoning system is prevented from using the semantics for proofs, but
configured to solely rely on the derived axioms and deduction rules). Abstraction layers turned out
to be a helpful means for reasoning within a target theory without the danger of deriving artifactual
theories, even in the absence of a formal completeness result about the used semantics. Furthermore,
it can be used to analyze soundness and completeness of the semantics itself.

The final result of \cite{MScThesis} was the discovery of an oversight in the formulation of AOT that
allowed for the reintroduction of a previously known paradox into the system. While multiple quick
fixes to restore the consistency of AOT were immediately available, in the aftermath of this result
AOT was significantly reworked and improved, the aftermath of this result was an extensive debate
of the foundations of AOT which culminated in the extension of the free logic AOT that was previously
restricted to its individual terms to account for non-denoting definite descriptions to its relation
terms as well. This reworking of AOT was accompanied by a continuous further development of its
embedding in Isabelle/HOL. This mutually beneficial mode of work was already partly described in
(TODO cite Open Philosophy) and resulted in a now stabilized improved formulation of AOT and a
matching embedding. The details of this process and its results is the main subject of this thesis. 

\<close>

section\<open>Overview of the Following Chapters\<close>

text\<open>
In the following,  we first give a brief introduction to Abstract Object Theory and
a more detailed description of Shallow Semantical Embeddings. Based on that we describe the constructed
embedding of Abstract Object Theory in Isabelle/HOL while highlighting the contributions
of the embedding to the theory of abstract objects on the one hand and the techniques developed for
its implementation on the other hand. Finally we present the results on Natural Numbers and
discuss the issue of extending the current system to encompass the full higher-order
type-theoretic version of Abstract Object Theory.
\<close>


chapter\<open>Shallow Semantic Embeddings\<close>

section\<open>History\<close>
text\<open>
\<close>

section\<open>SSE of Quantified Higher-Order Modal Logic\<close>
text\<open>
\<close>

chapter\<open>Abstract Object Theory\<close>

section\<open>Overview and Motivation\<close>

text\<open>

\<close>

section\<open>The Axiom System\<close>

text\<open>

\<close>

section\<open>The Deductive System\<close>

text\<open>

\<close>

section\<open>Examples of Applications\<close>

chapter\<open>SSE of AOT in Isabelle/HOL\<close>

text\<open>

\<close>

chapter\<open>Meta-Analysis of the Embedding\<close>

section\<open>Soundness\<close>

text\<open>
\<close>

section\<open>Completeness\<close>

text\<open>
\<close>

section\<open>Derivability\<close>

text\<open>
\<close>

section\<open>Meta Theorems\<close>

text\<open>

\<close>

chapter\<open>Natural Numbers in AOT\<close>

text\<open>

\<close>

chapter\<open>Higher-Order Type-Theoretic Object Theory\<close>

text\<open>

\<close>

chapter\<open>Conclusion\<close>

text\<open>

\<close>

(*<*)
end
(*>*)