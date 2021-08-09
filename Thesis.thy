(*<*)
theory Thesis
  imports AOT_PLM "HOL-Library.LaTeXsugar" (* "HOL-Library.OptionalSugar" *)
begin
(*>*)


chapter\<open>Introduction\<close>

section\<open>Motivation\<close>
text\<open>
While automated reasoning environments are already a vital part of the modern analysis
of mathematics and formal systems in general and their importance can only be expected
to increase in the future, building up a sound reasoning environment from scratch is a highly
non-trivial task. Consequently, there is only a limited number of trusted systems that can offer sophisticated
interactive and automated reasoning tools like Coq, HOL-Light or Isablle/HOL (TODO: cite).
Furthermore, most of these systems have at least parts of their logical foundation in common,
for example they are all based on some variation of functional type theory (TODO: make sure this
can actually be stated as such in particular towards Coq).

On the other hand, there is still an ongoing debate about the most suitable logical system
to be used for the foundations of mathematics (TODO: cite). While higher-order functional type
theory is closely tied to set theory (see \cite{HigherOrderLogicSetTheoryFalseDilemma}, TODO: rethink this point and the citation;
also note e.g. the opposite statement \url{https://kwarc.info/people/frabe/Research/RI_isabelle_10.pdf})
and set theory has long been a prime choice for a common denominator of mathematical disciplines
(TODO: cite), its modern paradox free axiomatization following Zermelo-Fraenkel is often viewed as
complex and counter-intuitive, respectively lacking in philosophical grounding and justification (TODO: cite).

While there is prominent research into alternative foundational approaches (e.g. homotopy type
theory; TODO: cite - maybe something else/more examples), a practical problem for such approaches
and a pragmatic defense of the use of set theory or HOL as foundation is the effort required in building up automated
reasoning systems that are on par with the existing tools that are available for processing theories
grounded in set theory or traditional higher-order type theory.

The following represents an attempt at overcoming this issue. We utilize the concept of a
@{emph \<open>shallow semantic embedding\<close>} with abstraction layers (TODO: cite) to transfer the merits of
the sophisticated interactive and automated reasoning system Isabelle/HOL to a fundamentally
different foundational system, namely to Abstract Object Theory (TODO: cite).

While it is not a requirement for our proposed general method, we demonstrate that
we can extend Isabelle/HOL by a customized reasoning infrastructure written in Isabelle/ML
that allows for an almost entirely transparent transfer of reasoning in our target logic and
abstracts the syntactic and inferential differences between Isabelle/HOL and AOT, while still
internally using the verified core logic of Isabelle/HOL as semantic backend. This means we
effectively construct a dedicated theorem proving environment for AOT that (1) is immediately guaranteed
to be sound, (2) can be used to explore the safety of axiomatic extensions to the system and (3) allows
for the reuse of the automation infrastructure available for Isabelle/HOL.

While our method can potentially be applied to a multitude of logical systems, Abstract Object Theory
is a particularly well-suited target. On the one hand it aims to be a foundational metaphysical system
that can serve as the basis for mathematics, linguistics and the sciences (TODO: rethink, cite), while
on the other hand it is based on logical foundations that differ from classical functional higher-order
type-theory and were even argued to be incompatible (see \cite{rtt}).
In our previous work (see \cite{MScThesis}) we demonstrated how our method for formally analyzing
models and semantics for such a system can be beneficial and vital for its soundness (TODO: refer to section with details).
During our continued work we could contribute to the evolution of Abstract Object Theory and
simultaneously arrived at a faithful representation of its model structure, semantics and
deductive system in Isabelle/HOL that can utilize the existing automated reasoning infrastructure.

As a prime result, we can show that the construction of Natural Numbers and the derivation
of the Peano-Dedekind postulates as well as Mathematical Induction described in Principia
Logico-Metaphysica (TODO: cite) are verifiably sound. Furthermore, we can suggest the generalization of
an additional axiom required for this construction, that we believe strengthens
the argument that the construction does not require any inherently mathematical axioms.
\<close>

section\<open>Previous Work\<close>

subsection\<open>Previous Computational Analysis of Abstract Object Theory\<close>

text\<open>

The computational analysis of Abstract Object Theory (AOT) was pioneered by Fitelson and Zalta in
\cite{FitelsonZalta}. They used the first-order system Prover9 for their work and were able to 
verify the proofs of the theorems in AOT's analysis of situations and possible worlds in
\cite{zalta1993}. Furthermore, they discovered an error in a theorem about Platonic Forms in~\cite{PelletierZalta}
that was left as an exercise.
Other work with Prover9 that does not target AOT includes the simplification of the reconstruction
of Anselm's ontological argument (in \cite{OppenheimerZalta2011}, Oppenheimer and Zalta show that
only one of the three premises they used in \cite{OppenheimerZalta1991} is sufficient) or the
reconstruction of theorems in Spinoza's @{emph \<open>Ethics\<close>} in \cite{SpinozaProver9}.

However, there are inherent limitations to the approach of analyzing higher-order theories like AOT
with the help of first-order provers. While it is possible to reason about the first order truth
conditions of statements by introducing sort predicates and using a number of special techniques
to translate the statements into the less-expressive language of multi-sorted first-order logic
(a detailed account of such techniques is given in \cite{AlamaZalta2015}), the complexity of the
resulting representation increases for expressive, higher-order philosophical claims.
In general, this approach may be sufficient for analyzing concrete isolated arguments, but it becomes
infeasible to construct a natural representation of an entire expressive higher-order theory and
its full deductive system.
\<close>
subsection\<open>Previous Work involving Shallow Semantic Embeddings\<close>

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
extensive analysis of G\"odel's ontological argument in second-order S5 modal logic (TODO cite), followed
by a range of studies of similar ontological arguments (TODO cite). TODO: newer work by Benzm\"uller.

The advantage of these studies using SSEs compared to the earlier use of first-order systems is that arguments
can be represented in their native syntax and are thereby readable and maintainable, while the theorem
proving environment is capable of automatically transforming statements into a suitable first-order
representation on the fly to allow first-order theorem provers like E or SPASS (TODO: cite) to perform
proof search much like e.g. Prover9 was able to do on a manually constructed first-order representation.

These studies were still mainly concerned with case studies of concrete arguments or
with conservative extensions of higher-order logic like functional higher-order modal logic.
Furthermore, they relied heavily on the previously available completeness results of second-order modal
logic with respect to Kripke models (TODO: cite).
\<close>

subsection\<open>Previous Work on AOT involving the SSE Approach\<close>

text\<open>

In our own previous work (see~\cite{MScThesis}) we applied an extended version of the technique of
SSEs to AOT. For AOT no extensive prior analysis of canonical models was available, in contrast to, for example,
the extensive analysis of Kripke models for higher-order modal logic that served as theoretical
basis for the previous work using SSE as mentioned above. While the so-called Aczel models of object theory
(TODO: cite) provide an important building block for constructing models of AOT in HOL, no full
set-theoretic model of object theory had been constructed. In \cite{MScThesis} we extended the
existing Aczel models to a richer model structure that was capable of approximating the validity
of statements of the at the time most recent formulation of AOT in Principia Logico-Metaphysica (PLM) (TODO: cite).
Furthermore, we introduced the new concept of @{emph \<open>abstraction layers\<close>}. An abstraction layer consists
of a derivation of the axioms and deduction rules of a target system from a given semantics that is
then considered as ground truth while "forgetting" the underlying semantic structure, i.e. the
reasoning system is prevented from using the semantics for proofs, but is instead configured to solely
rely on the derived axioms and deduction rules.
Abstraction layers turned out to be a helpful means for reasoning within a target theory without
the danger of deriving artifactual theories, even in the absence of a formal completeness result
about the used semantics.
Furthermore, it can be used to analyze soundness and completeness of the semantics itself. (TODO: rethink; maybe
reformulate differently)

A major result of \cite{MScThesis} was the discovery of an oversight in the formulation of AOT that
allowed for the reintroduction of a previously known paradox into the system. While multiple quick
fixes to restore the consistency of AOT were immediately available, in the aftermath of this result
AOT was significantly reworked and improved. The result triggered an extensive debate
of the foundations of AOT which culminated in the extension of the free logic of AOT to relations,
while previously it was restricted to individual terms only (to account for non-denoting
definite descriptions). This reworking of AOT was accompanied by a continuous further development of its
embedding in Isabelle/HOL. This mutually beneficial mode of work was already partly described in
(TODO cite Open Philosophy) and resulted in a now stabilized improved formulation of AOT and a
matching embedding. The details of this process and its results are the main subject of this thesis. 

\<close>

section\<open>Overview of the Following Chapters\<close>

text\<open>
In the following, we first give a more detailed description of Shallow Semantical Embeddings (chapter~\ref{SSEs}) and
a brief introduction to Abstract Object Theory (chapter~\ref{AOT}).

Based on that, chapter~\ref{SSEofAOT} describes
the constructed embedding of Abstract Object Theory in Isabelle/HOL while highlighting the contributions
of the embedding to the theory of abstract objects on the one hand and the techniques developed for
its implementation up to the dedicated reasoning system implemented in Isabelle/ML on the other hand.

In chapter~\ref{NaturalNumbers} we present the results on the derivation of Natural Numbers and
Mathematical Induction and discuss our proposed extension of AOT with a general comprehension
principle for relations among abstract objects.

Finally, in chapter~\ref{HigherOrderAOT} we briefly discuss the issue of extending the current system to
encompass the full higher-order type-theoretic version of Abstract Object Theory.
TODO: explicitly mention the fact that the embedding deals with the second-order fragment only earlier and restate here.
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
focus on the application of similar modes of embeddings to logical reasoning in the next section.
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
model suffices.@{footnote \<open>We will later show that this is the only choice for the particular modal
logic of Abstract Object Theory due to its additional actuality operator. TODO: actually do that.\<close>}

For possible worlds we can introduce a primitive type in Isabelle/HOL.
\<close>

typedecl w

text\<open>
A Kripke model further involves a relation between possible worlds and modal formulas that is
usually read as a formula @{emph \<open>being satisfied at\<close>} a possible world. So the semantic domain of
propositions is boolean-valued functions acting on (or, equivalently, sets of) possible worlds.
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

So far we have constructed an embedding of propositional S5 modal logic. However it is straightforward
to enrich it with quantification.
\<close>

definition forall :: \<open>('a \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close> (binder \<open>\<^bold>\<forall>\<close> 110) where
  \<open>\<^bold>\<forall> x . \<phi> x \<equiv> \<lambda>w . \<forall> x . \<phi> x w\<close>
definition exists :: \<open>('a \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close> (binder \<open>\<^bold>\<exists>\<close> 110) where
  \<open>\<^bold>\<exists> x . \<phi> x \<equiv> \<lambda>w . \<exists> x . \<phi> x w\<close>

text\<open>Note that we didn't have to introduce any particular type for individuals, but stated the
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
limitations that can make them unsuitable to achieve that purpose entirely on their own,
as described in more detail in the following section.

TODO: more high-level description before technical details?

The main tool for automated reasoning in Isabelle/HOL in question is @{command sledgehammer} (TODO: cite again?).
@{command sledgehammer} can be invoked during any proof and will try to automatically find a proof for
the current proof goal. To that end, simply speaking,@{footnote \<open>For the full and precise details of the process
refer to TODO: cite.\<close>} it collects all theorems derived in the current @{command theory} context
together with all local assumptions, processes the resulting set of theorems heuristically to find
a subset of relevant theorems. It then encodes the problem of deriving the current goal from the chosen
theorems and assumptions in a format that can be consumed by external theorem provers like
CVC4, E or SPASS (TODO: cite). This may, for example, involve a translation from higher-order problems
to first order problems. If one of the invoked provers can prove the current goal, @{command sledgehammer}
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
or the @{command lift_definition}s (TODO: cite) introduce several theorems implicitly. While
it is still possible to collect these theorems manually, the process is cumbersome and error-prone.
TODO: cite sledgehammer user guide section 6.1.

On the other hand, it is not possible to simply exclude @{emph \<open>all\<close>} theorems that were defined
up to a certain point, since this includes the theorems of Isabelle's @{theory Main} theory, i.e.
- among others - the construction of classical higher-order logic from Isabelle's more basic @{theory Pure}
logic. This includes theorems @{command sledgehammer} relies on and disbarring them will leave it
non-functional (conceptually, such theorems in question can be thought of as meta-theorems about
derivations in our context TODO: rethink that, maybe collect examples).

The solution used in the current embedding of Abstract Object Theory is the use of option (2), but
it uses Isabelle's internal ML API to automatically collect theorems to be added to an exclusion
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


section\<open>Implicit Interpretation and Assignment Function in SSEs\<close>

text\<open>TODO: This section will be important and will need a lot of care. Current plan:

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
     The nonterminal then serves as the purely syntactic type for propositions in the grammar of our
     sub-language.\<close>
nonterminal prop\<o>\<^sub>3 
text\<open>The nonterminal can be used as (purely syntactic) type in @{command syntax} definitions.\<close>
syntax valid_\<o>\<^sub>3 :: \<open>prop\<o>\<^sub>3 \<Rightarrow> bool\<close>  (\<open>\<Turnstile> _\<close> 1)

text\<open>Furthermore we need to specify how propositions can be produced from terminals in the grammar.
We want to use simple identifiers to refer to proposition variables. To that end we introduce a
@{emph \<open>copy-production\<close>} rule (a rule that is not tied to a constant). The terminal
@{typ id_position} is used for identifiers with additional markup information (TODO: reference and cite PIDE markup).
\<close>
syntax "" :: \<open>id_position \<Rightarrow> prop\<o>\<^sub>3\<close> (\<open>_\<close>)

text\<open>Now we can already construct a simple term in our new syntax:\<close>
term \<open>\<Turnstile> p\<close>

text\<open>Since we introduce an entirely new grammar subtree that is independent of the usual HOL inner syntax,
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

text\<open>Note that it is still possible to mix the usual HOL syntax with our newly defined subgrammar
to argue about validity:\<close>

lemma \<open>(\<Turnstile> \<diamond>p \<longrightarrow> q) \<longrightarrow> (\<not>(\<Turnstile> p) \<or> (\<Turnstile> q))\<close>
  using dia_\<o>\<^sub>3_def imp_\<o>\<^sub>3_def valid_\<o>\<^sub>3_def by auto

text\<open>Note that in the above the left-most implication is the implication of the embedded logic,
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
albeit technically complex, solution. TODO: adjust references.
\<close>

chapter\<open>Abstract Object Theory\<close>text\<open>\label{AOT}\<close>

text\<open>
The following sections provide a brief introduction into Abstract Object Theory. While the first
section will explain the general idea and motivation of object theory, the following sections
reproduce the language and axiom system of AOT as implemented in our embedding. In the process,
we hint at the major differences between the original formulation of AOT and its incarnation in
our embedding, hinting at more detailed implementational details that will be discussed in the
next chapter.
Note that unless explicitly stated otherwise, all definitions and theorems are cited directly
from our embedding. TODO: rethink, elaborate (i.e. they are actual Isabelle-verified statements
relative to the embedding).
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
a free occurrence of @{term F} (@{term \<phi>} may not contain a free occurrence of @{term x}, unless we had
explicitly added @{term x} in curly braces as well; TODO: cite later section).
Therefore, abstract objects can be modeled as elements
of the power set of properties: every abstract object uniquely
corresponds to a specific set of properties.

Given this basic theory of abstract objects, AOT can elegantly define
a wide variety of objects that have been postulated in philosophy or
presupposed in the sciences, including Leibnizian concepts, Platonic
forms, possible worlds, natural numbers, logically-defined sets, etc.

Another interesting aspect of the theory is its hyperintensionality.
Relation identity is defined in terms of encoding rather than
in terms of exemplification. Two properties @{term F} and @{term G} are stipulated to be identical if they are
necessarily @{emph \<open>encoded\<close>} by the same abstract objects (@{thm "identity:2"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I", OF "cqt:2[const_var]"[axiom_inst], OF "cqt:2[const_var]"[axiom_inst], of _ F G, print_as_theorem]}).
However, the theory does not impose any restrictions on the properties encoded by a particular abstract
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

In the following sections we provide a brief overview of the language, the axiom system and
the deductive system of PLM. For a full account and detailed discussion refer to (TODO: cite PLM).
\<close>

section\<open>The Language\<close>

text\<open>

A precise description of AOT's language can be found in (TODO: cite PLM).
In the following we provide a simplified informal description while explaining some of the deviations
from AOT's conventions we use in our embedding.

The language distinguishes between constants, variables and terms at each type. The types of
the second-order fragment consist of a type of individuals and, for each @{text \<open>n \<ge> 0\<close>}, of a type
of @{text n}-place relations, i.e. relations among @{text n} individuals.
Formulas are considered as @{text 0}-place relation terms. Additionally,
PLM uses @{emph \<open>meta-variables\<close>} that range over all variable names of a given type.
PLM uses the following conventions for referring to the primitive language elements in each type:

  \<^item> Primitive individual constants: @{text \<open>a\<^sub>1, a\<^sub>2, \<dots>\<close>}
  \<^item> Individual variables: @{text \<open>x\<^sub>1, x\<^sub>2, \<dots>\<close>}
  \<^item> Primitive @{text n}-place relation constants: @{text \<open>P\<^sup>n\<^sub>1, P\<^sup>n\<^sub>2, \<dots>\<close>}
  \<^item> @{text n}-place relation variables: @{text \<open>F\<^sup>n\<^sub>1, F\<^sup>n\<^sub>2, \<dots>\<close>}
  \<^item> A distinguished 1-place relation constant for @{emph \<open>being concrete\<close>}: @{term \<open>\<guillemotleft>E!\<guillemotright>\<close>}


Additionally, AOT uses the Greek letters for meta-variables, i.e. schematic meta-logical variables
ranging over arbitrary variable names or over terms. By convention, it associates specific kinds of
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
  \<^item> @{term \<open>AOT_TERM[(\<forall>\<alpha> \<phi>{\<alpha>})]\<close>}, the @{emph \<open>universal quantifier\<close>}@{footnote \<open>While PLM, by default, allows
  any free variables to occur instances of a schematic meta-variable, unless specified otherwise, for
  technical reasons, we choose the opposite convention, i.e. while a schematic meta-variable may contain
  any occurence of variable that would remain @{emph \<open>free\<close>}, any @{emph \<open>bound\<close>} variables that may
  occur in an instance of the schematic meta-variable have to be explicitly listed in curly brackets.\<close>}
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
and identity. In particular, PLM defines the following: (TODO: cite PLM section)

Derived connectives and quantifiers:

\begin{quote}
@{thm[display] "conventions:1"[of \<phi> \<psi>]
               "conventions:2"[of \<phi> \<psi>]
               "conventions:3"[of \<phi> \<psi>]
               "conventions:4"[of \<phi>]
               "conventions:5"[of \<phi>]}
\end{quote}

Logical existence, i.e. the conditions under which an object @{emph \<open>denotes\<close>}:

\begin{quote}
@{thm[display] "existence:1"[of \<kappa>]
               "existence:2"[of \<Pi>]
               "existence:3"[of \<phi>]}
\end{quote}

Being @{emph \<open>ordinary\<close>} and being @{emph \<open>abstract\<close>}:

\begin{quote}
@{thm[display] "oa:1" "oa:2"}
\end{quote}

Identity of individuals:
\begin{quote}
@{thm[display] "identity:1"[of \<kappa> \<kappa>']}
\end{quote}

Identity of properties (i.e. @{text 1}-place relations):

\begin{quote}
@{thm[display] "identity:2"[of \<Pi> \<Pi>']}
\end{quote}

Identity of @{text \<open>n\<close>}-place relations (@{text \<open>n \<ge> 2\<close>}):@{footnote \<open>The idea here is that two
@{text n}-place relations are identical, if they denote and all their projections to @{text \<open>n - 1\<close>} objects
are identical. In the embedding it is tricky to reproduce the ellipse notation used for this definition
directly, therefore the statement here is @{emph \<open>not\<close>} cited from the embedding. The implementation
of this definition in the embedding is discussed in more detail in section TODO: cite.\<close>}

\begin{quote}
  \Squ{@{text \<open>\<Pi> = \<Pi>' \<equiv>\<^sub>d\<^sub>f \<Pi>\<down> & \<Pi>'\<down> & \<forall>y\<^sub>1\<dots>\<forall>y\<^bsub>n-1\<^esub> ([\<lambda>x [\<Pi>]xy\<^sub>1\<dots>y\<^bsub>n-1\<^esub>] = [\<lambda>x [\<Pi>']xy\<^sub>1\<dots>y\<^bsub>n-1\<^esub>] &
[\<lambda>x [\<Pi>]y\<^sub>1xy\<^sub>2\<dots>y\<^bsub>n-1\<^esub>] = [\<lambda>x [\<Pi>']y\<^sub>1xy\<^sub>2\<dots>y\<^bsub>n-1\<^esub>] & \<dots> &
[\<lambda>x [\<Pi>]y\<^sub>1\<dots>y\<^bsub>n-1\<^esub>x] = [\<lambda>x [\<Pi>']y\<^sub>1\<dots>y\<^bsub>n-1\<^esub>x]
)\<close>}}
\end{quote}

Based on the described language and definitions we can state AOT's axiom system in the following section.
\<close>

section\<open>The Axiom System\<close>

text\<open>
In the following we reproduce the full axiom system of the latest formulation of AOT, while
commenting on several aspects that are specific to AOT. Unless explicitly noted otherwise, we
will directly cite the axioms from our implementation while explaining notational and conceptual
differences to the original axiom system of AOT, which can be found with detailed explanations in
(TODO: cite PLM).

The first set of axioms build up a Hilbert-style deductive system for negation and implications
following Mendelsson's axiom system (TODO: cite Elliott Mendelson, Introduction to Mathematical Logic, Van Nostrand, New York, 1979, p. 31.):

\begin{quote}
@{thm[display] "pl:1"[axiom_inst, print_as_theorem, of \<phi> \<psi>]
      "pl:2"[axiom_inst, print_as_theorem, of \<phi> \<psi> \<chi>]
      "pl:3"[axiom_inst, print_as_theorem, of \<phi> \<psi>]}
\end{quote}

The next set of axioms constructs a quantifier logic for a free logic with non-denoting terms.
Formulas of the form @{term \<open>\<guillemotleft>\<tau>\<down>\<guillemotright>\<close>} can be read as @{emph \<open>the term @{term \<open>\<tau>\<close>} denotes\<close>} and refer
to the notion of logical existence that was @{emph \<open>defined\<close>} in the previous section.

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
  in which the initial @{text \<open>\<lambda>\<close>} does not bind any variable in any encoding formula substerm.}
\end{quote}

Reproducing the natural language condition on @{term \<tau>} in the embedding is non-trivial; we discuss
the implementation of this axiom in detail in section (TODO: cite).

The next axiom states that identical objects can be substituted in formulas. Note that the used identity
is not primitive, but was @{emph \<open>defined\<close>} in the last section.@{footnote \<open>TODO: say something
about "being substitutable" vs the free variable notation.\<close>} 

\begin{quote}
@{thm[display] "l-identity"[axiom_inst, of _ \<alpha> \<beta> \<phi>, print_as_theorem]}
\end{quote}

The following axiom is the single @{emph \<open>modally fragile axiom\<close>} of the system. All other axioms
are considered @{emph \<open>modally strict\<close>}. The distinction is discussed in more detail in TODO: cite.
TODO: note a few things here as well, including the turnstile operator.

\begin{quote}
@{thm[display] "logic-actual"[act_axiom_inst, of \<phi>]}
\end{quote}

Apart from the above modally-fragile principle, the logic of actuality is governed by the following
modally-strict axioms:

\begin{quote}
@{thm[display] "logic-actual-nec:1"[axiom_inst, of _ \<phi>, print_as_theorem]
               "logic-actual-nec:2"[axiom_inst, of _ \<phi> \<psi>, print_as_theorem]
               "logic-actual-nec:3"[axiom_inst, of _ \<phi>, print_as_theorem]
               "logic-actual-nec:4"[axiom_inst, of _ \<phi>, print_as_theorem]}
\end{quote}

TODO: say something about this together with the axiom relating actuality to necessity below is
a "standard" actuality operator plus citation.

The logic of necessity and possibility is axiomatized using the classical K, T and 5 axioms of a
propositional S5 modal logic:

\begin{quote}
@{thm[display] "qml:1"[axiom_inst, of _ \<phi> \<psi>, print_as_theorem]
               "qml:2"[axiom_inst, of _ \<phi>, print_as_theorem]
               "qml:3"[axiom_inst, of _ \<phi>, print_as_theorem]}
\end{quote}

Additionally, PLM states the following axiom that requires that there might have been a concrete object
that is not @{emph \<open>actually\<close>} concrete, thereby committing the system against modal collapse
(TODO: cite some more discussion).
\begin{quote}
@{thm[display] "qml:4"[axiom_inst, print_as_theorem]}
\end{quote}

The classical S5 modal logic is connected to logic of actuality by the following two axioms:

\begin{quote}
@{thm "qml-act:1"[axiom_inst, of _ \<phi>, print_as_theorem]
      "qml-act:2"[axiom_inst, of _ \<phi>, print_as_theorem]}
\end{quote}

Definite descriptions in AOT are governed by the following axiom (which will allow for deriving
a version of Russell's analysis of descriptions; TODO: expand, cite?):

\begin{quote}
@{thm descriptions[axiom_inst, of _ x \<phi>, print_as_theorem]}
\end{quote}


A consistent axiomatization of complex relation terms in AOT requires some care. While @{text \<open>\<lambda>\<close>}-expressions
follow the classical principles of @{text \<alpha>}-, @{text \<beta>}- and @{text \<eta>}-conversion, they have to be
suitably restricted to denoting terms, since not all @{text \<open>\<lambda>\<close>}-expressions are guaranteed to denote.
Also note that, as mentioned above (TODO cite?), the embedding generally collapses alphabetic variants,
so while @{text \<alpha>}-conversion can be stated, it effectively reduces to the statement that denoting
@{text \<lambda>}-expressions are self-identical (TODO: cite discussion).

\begin{quote}
@{thm[display] "lambda-predicates:1"[axiom_inst, of _ \<phi>, print_as_theorem]
               "lambda-predicates:2"[axiom_inst, of _ \<phi> x\<^sub>1x\<^sub>n, print_as_theorem]
               "lambda-predicates:3"[axiom_inst, of _ F, print_as_theorem]}
\end{quote}
Note that the last of the above axioms, @{text \<eta>}-conversion, also has the @{text 0}-place case
@{thm "lambda-predicates:3[zero]"[axiom_inst, of _ p, print_as_theorem]}.

The following axiom is specific to AOT and, together with generally extending AOT's free logic
to relation terms and the refinement of base cases of denoting terms, a main aspect in the evolution
of PLM that was originally triggered by our previous work in (TODO: cite MSc thesis).
It states that whenever a @{text \<lambda>}-expression denotes, any @{text \<lambda>}-expression with a matrix
that is necessarily equivalent on all abstracted variables will denote as well:

\begin{quote}
@{thm[display] "safe-ext"[axiom_inst, of _ \<phi> \<psi>, print_as_theorem]}
\end{quote}

This axiom, together with AOT's move to a general free logic for complex terms, is discussed in
more detail in section TODO: cite.

The remaining axioms govern AOT's second mode of predication, @{emph \<open>encoding\<close>}.

The first of these axioms reduces @{term n}-ary encoding to unary encoding of projections as follows:@{footnote
\<open>Note that similarly to the definition of @{term n}-ary relation identity, the formulation using
ellipses is non-trivial to reproduce in the embedding. Therefore we again do @{emph \<open>not\<close>} cite the axiom
directly from the embedding, but state it as given in PLM modulo our notational conventions. The precise implementation in the embedding
is discussed in TODO: cite.\<close>}


\begin{quote}
  \Squ{@{text \<open>x\<^sub>1\<dots>x\<^sub>n[F] \<equiv> x\<^sub>1[\<lambda>y [F]yx\<^sub>2\<dots>x\<^sub>n] & x\<^sub>2[\<lambda>y [F]x\<^sub>1yx\<^sub>3\<dots>x\<^sub>n] & \<dots> & x\<^sub>n[\<lambda>y [F]x\<^sub>1\<dots>x\<^bsub>n-1\<^esub>y]\<close>}}
\end{quote}

The second axiom governing encoding states that encoding is @{emph \<open>modally rigid\<close>}:

\begin{quote}
  @{thm[display] encoding[axiom_inst, of _ x F, print_as_theorem]}
\end{quote}

Furthermore, as mentioned in the overview, encoding is reserved for @{emph \<open>abstract\<close>} objects or
in other words: ordinary objects do not encode properties:

\begin{quote}
  @{thm nocoder[axiom_inst, of _ x, print_as_theorem]}
\end{quote}

The last axiom is the core axiom of AOT, the @{emph \<open>Comprehension Principle for Abstract Objects\<close>}.
For any expressible condition on properties, there exists an abstract object that encodes exactly those
properties that satisfy the condition:

\begin{quote}
@{thm "A-objects"[axiom_inst, of _ \<phi>, print_as_theorem]}
\end{quote}

All above axioms are to be understood as axiom @{emph \<open>schemata\<close>}, i.e. their universal closures
will also be axioms. Furthermore, for all axioms except the modally-fragile axiom of actuality,
their modal closures are taken as axioms as well.
\<close>




section\<open>The Deductive System\<close>

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
val (v,concl) = case concl of (Const (\<^const_syntax>\<open>HOL.Trueprop\<close>, _) $ (Const (\<^const_syntax>\<open>AOT_model_valid_in\<close>, _ ) $ v $ c)) => (v,c)
fun mapPremise (x as Const (\<^const_syntax>\<open>HOL.Trueprop\<close>, _) $ (Const (\<^const_syntax>\<open>AOT_model_valid_in\<close>, _ ) $ v' $ c)) = (if v = v' then Const (\<^syntax_const>\<open>_AOT_process_frees\<close>, dummyT) $ c else x)
  | mapPremise (x as Const (\<^const_syntax>\<open>Pure.all\<close>, _) $ (abs as Abs (name, t, xs))) = if t = @{typ w} then x else Const (\<^syntax_const>\<open>_AOT_for_arbitrary\<close>, dummyT) $ (Const ("_bound", dummyT) $ Free (name, dummyT)) $ (mapPremise (Term.betapply (abs, Const ("_bound", dummyT) $ Free (name, dummyT))))
  | mapPremise (x as Const (\<^const_syntax>\<open>Pure.imp\<close>, _) $ p $ q) = Const (\<^syntax_const>\<open>_AOT_derivable\<close>, dummyT) $ mapPremise p $ mapPremise q
val prems = map mapPremise prems
val prem = (hd prems)
val prem = fold (fn c => fn p => (Const (\<^syntax_const>\<open>_AOT_asms\<close>, dummyT) $ p $ c)) (tl prems) prem
val der = case v of Const ("_var", _) $ _ => \<^syntax_const>\<open>_AOT_rule\<close> | _ => \<^syntax_const>\<open>_AOT_rule\<close>
in
Const (der, dummyT) $ prem $ (Const (\<^syntax_const>\<open>_AOT_process_frees\<close>, dummyT) $  concl)
end))]\<close>
(*>*)
text\<open>

While an implementation of the complete deductive system of PLM chapter~9 (TODO: cite properly) can be
found in (TODO: cite), a full discussion of the entire system would be beyond the scope of this thesis.
However, we will discuss some aspects in detail.

Since the axioms in the last section are to be understood as axiom schemata, i.e. their statement
includes the statement of adequate closures, a single primitive rule of inference suffices for
the deductive system of PLM, i.e. Modus Ponens:@{footnote \<open>Note that we are still citing rules directly from the embedding
using a special printing mode for meta-rules.\<close>}
\begin{quote}
@{thm[display] "modus-ponens"[print_as_rule]}
\end{quote}

While PLM can refer to structural induction on the complexity of a formula to derive further
meta-rules, by the nature of a Shallow Semantic Embedding, the precise term structure is not
preserved, but instead terms are directly represented as objects in their semantic domain. For that reason,
in our embedding we derive the rules in question by referring to the semantic properties of the
embedding. In particular, we derive the following rules semantically:

The deduction theorem:
\begin{quote}
@{thm[display] "deduction-theorem"[print_as_rule]}
\end{quote}

The rule of necessitation RN:
\begin{quote}
@{thm[display] "RN"[print_as_rule]}
\end{quote}

The rule of generalization GEN:
\begin{quote}
@{thm[display] "GEN"[print_as_rule]}
\end{quote}

TODO: needs to mention (since referenced later):
  \<^item> Inferential role of definitions.
  \<^item> Two deductive systems: modally-strict and modally-fragile.
  \<^item> Rigid restriction conditions and restricted variables.
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
TODO: extensive description of the actual models used in the embedding.
  \<^item> Aczel Models
  \<^item> Hyperintensional Propositions
  \<^item> Relations as Proposition Valued Functions
  \<^item> Terms implemented as type classes with a partial equivalence relation signifying exemplification-indistinguishability and determining when terms denote.
  \<^item> Nary terms as relations on tuples, abstracted by type classes instantiated to the product type.
  \<^item> "Regular" and "irregular" terms for precisely modelling nary-relation identity.
  
\<close>

section\<open>Syntax of the Target Theory\<close>

text\<open>
  \<^item> Independent grammar root with extensive use of parse translations
  \<^item> Splitting of identifiers in atomic formulas like @{term \<open>\<guillemotleft>[F]xy\<guillemotright>\<close>}.
  \<^item> Registering symbols for implied types; handling of meta-variables; simulating ellipses with type classes.
  \<^item> Multiple printing modes.
\<close>

section\<open>Extending Isabelle's Outer Syntax\<close>

text\<open>
  \<^item> ML implemented copy of the Isar language.
  \<^item> Automatically parses inner syntax at @{typ AOT_prop} grammar root.
  \<^item> Tracks semantic possible worlds.
  \<^item> Reproducing AOT's system of definitions using @{command AOT_define}; implicit tracking
    of defined constants; implicit instantiation, internally using the @{command specification} backend.
  \<^item> @{command AOT_find_theorems} and @{command AOT_sledgehammer}
\<close>

section\<open>Representation of an Abstract Semantics of AOT\<close>
text\<open>
  \<^item> Abstraction of the properties of the models required for deriving the axiom system.
  \<^item> Heavy use of @{command specification} to allow for general models and obtain some degree of guaranteed automatic abstraction.
\<close>

section\<open>Axiom System and Deductive System\<close>
text\<open>
  \<^item> Deriving Axioms and Fundamental Meta-Rules from semantics.
  \<^item> Challenge in stating the natural language conditions with focus on cqt.2 (base cases of denoting terms).
  \<^item> Custom proving methods for substitutition.
  \<^item> Proof by types using type classes.
  \<^item> Attributes for "rulifying" AOT theorems.
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
setup\<open>Thy_Output.antiquotation_pretty_source @{binding "ML_print_term"} Args.term (
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
s.t. @{text \<open>\<psi>' \<in> \<Gamma>'\<close>}, and vice-verse.}
\end{quote}

For a proof it suffices to realize that for every @{text \<open>\<psi> \<in> \<Gamma>\<close>} and @{text \<open>\<psi>' \<in> \<Gamma>'\<close>} by the above rule it holds that
@{text \<open>\<psi> \<stileturn>\<turnstile> \<psi>'\<close>} and hence all premises in @{text \<Gamma>} are derivable from @{text \<Gamma>'} and vice-versa.

Hence AOT allows to freely move from any formula to an alphabetic variant in all theorems and assumptions,
justifying the fact that the embedding identifies alphabetic variants.

TODO: think about mentioning the @{attribute rename_abs} attribute that allows for renaming
linked groups of bound variables.

\<close>

subsection\<open>Generalizing Free Variables to Schematic Variables\<close>text\<open>\label{free-variables-schematic}\<close>

text\<open>
After a theorem is proven in Isabelle, it is implicitly exported to the current theory context in
@{emph \<open>schematic\<close>} form. That means each free variable used in the theorem is implicitly
generalized to a @{emph \<open>schematic variable\<close>} that can be instantiated to any variable or term of
the same type. Since the embedding uses distinct types for variables and terms that have the same type in AOT (TODO: cite),
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

Given this discussion and the meta-rule derived above, the fact that Isabelle implicitly generalizes
free variables to schematic variables remains faithful to the derivational system of AOT.
\<close>

subsection\<open>Further Meta-Theorems\<close>

text\<open>
Ideas:
  \<^item> Relation of AOT's existential elimination and @{command obtain}.
  \<^item> Tuples as accurate representation of most of the general n-ary statements justified by the ability to define
    matching tuples in AOT.
  \<^item> More on generalization and e.g. constants?

\<close>

subsection\<open>Discussion\<close>

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