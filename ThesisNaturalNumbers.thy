(*<*)
theory ThesisNaturalNumbers
  imports Thesis AOT_NaturalNumbers AOT_misc
begin
(*>*)

chapter\<open>Natural Numbers in AOT\<close>text\<open>\label{NaturalNumbers}\<close>

text\<open>
While AOT can represent mathematical theories themselves as @{emph \<open>abstract objects\<close>}
(see chapter~\ref{HigherOrderAOT}), it distinguishes this analysis of @{emph \<open>Theoretical Mathematics\<close>}
from the notion of @{emph \<open>Natural Mathematics\<close>}. @{emph \<open>Natural Mathematics\<close>}
consists of ordinary, pretheoretic claims about mathematical objects
and arises directly as abstraction of exemplification patterns rather
than being based on the axioms of some mathematical theory (see item (304) in PLM~\cite{PLM-Oct-13-2021}).

Following this idea, the claim of PLM's Chapter 14 is that natural numbers 
can be naturally defined within object theory and the laws they abide by up to and including
Second-Order Peano Arithmetic can be derived without having to appeal to any intrinsically mathematical
axioms or notions.

We have reproduced parts of this construction in our implementation@{footnote \<open>At the
time of writing the implementation encompasses the construction of natural numbers and the
Peano-Dedekind postulates. We expect a full derivation of Second-Order Peano Arithmetic in the
foreseeable future.\<close>} and arrived at the following results:
  \<^item> The construction of natural numbers is sound and the Peano-Dedekind postulates, including mathematical induction, are consistently derivable.
  \<^item> We could model the additional axioms required for the construction in our framework.
  \<^item> We could generalize one of the aforementioned axioms, strengthening the theoretical basis and
    justification of the construction.
  \<^item> We could suggest several amendments to the construction and discover and fix several
    minor errors and inconsistencies in the presentation.

In particular, we can derive the Dedekind-Peano postulates about Natural Numbers as follows: (TODO: improve formulations and cite)
    \<^enum> Zero is a Natural Number.
    \<^enum> No Natural Number has Zero as its Successor.
    \<^enum> If a Natural Number @{text k} succeeds the numbers @{text n} and @{text m}, then @{text \<open>n = m\<close>}.
    \<^enum> Every Natural Number has a Successor.
    \<^enum> Mathematical Induction:
      If (1) Zero exemplifies a property @{text F} and (2) for any number @{text n},
      it follows from the fact that @{text n} exemplifies @{text F} that the successor
      of @{text n} exemplifies @{text F}, then @{text F} is exemplified by all natural numbers.
\<close>
text\<open>
Furthermore, the contributions to the general evolution of AOT we described in the previous chapters have
had repercussions on the details of the construction. We will describe this interaction in more
detail in the following sections, while reproducing the construction Nodelman and Zalta present in PLM chapter~14.
\<close>

section\<open>General Idea of the Construction\<close>

text\<open>
The strategy for constructing natural numbers in AOT follows the idea of Frege's Theorem (see~\cite{sep-frege-theorem} TODO:
check link).
Frege showed that the Peano axioms can be derived from @{emph \<open>Hume's Principle\<close>} using Second-Order
Logic. Hume's Principle states that the number of @{term F}s is equal to the number of @{term G}s if and
only if @{term F} and @{term G} are @{emph \<open>equinumerous\<close>}. Two relations are @{emph \<open>equinumerous\<close>},
if and only if there is a one-to-one correspondence between them or, in other words, if and only if
there is a bijection between the objects exemplifying @{term F} and the objects exemplifying @{term G}.

Frege himself derived Hume's Principle from @{emph \<open>Basic Law V\<close>}, which together with second-order
logic leads to Russel's Paradox. However, deriving Peano arithmetic @{emph \<open>from\<close>} Hume's Principle
itself does not require @{emph \<open>Basic Law V\<close>}. In PLM's chapter 14, Nodelman and Zalta propose a
definition of @{emph \<open>equinumerosity\<close>} and @{emph \<open>the number of @{term F}s\<close>} in object theory
and are able to derive Hume's Principle. Based on that, Natural Numbers and the Dedekind-Peano postulates become consistently
derivable as expected.
\<close>

section\<open>Equinumerosity of Relations\<close>

text\<open>On the basis of traditional mathematical training based on set theory and functional logic,
the seemingly most natural conception of @{emph \<open>equinumerosity\<close>} involves the notion of a
bijection. Two properties are equinumerous (i.e., intuitively, they are exemplified by "the same number" of objects),
if and only if there is a bijection between the sets of objects they exemplify.

However, this conception of equinumerosity relies on objects of theoretical mathematics
and their axiomatization (sets, functions, bijections). While object theory can in fact define
those notions as well, it takes relations to be the more primitive, fundamental concept and thereby
prefers a definition in terms of relations alone.

The concept of there being a bijection between the sets of objects two properties exemplify can 
equivalently be captured by the notion of there being a @{emph \<open>one-to-one correspondence\<close>} between
the properties.
\<close>

subsection\<open>One-to-One Correspondences\<close>

text\<open>
A @{emph \<open>one-to-one correspondence\<close>} between the properties @{term F} and @{term G} is a relation
@{term R}, s.t. (1) for every object @{term x} that exemplifies @{term F}, there is a unique object
@{term y} exemplifying @{term G}, s.t. @{term x} bears @{term R} to @{term y} and conversely (2) for
every object @{term y} that exemplifies @{term G}, there is a unique object @{term x} exemplifying
@{term F}, s.t. @{term x} bears @{term R} to @{term y}. Formally (see~\nameref{AOT:1-1-cor}):@{footnote \<open>Note that as mentioned in section~\ref{InferentialRoleOfDefinitions}, instead of stating
the original definitions-by-equivalence of AOT that involve additional significance
clauses, we may instead illustrate the definitions in simpler form using
derived equivalences formulated using object-level variables throughout this chapter.
In each case the full definition in the appendix is referenced.\<close>}

\begin{quote}
@{lemma[display] \<open>print_as_theorem \<guillemotleft>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> G \<equiv> \<forall>x ([F]x \<rightarrow> \<exists>!y ([G]y & [R]xy)) & \<forall>y ([G]y \<rightarrow> \<exists>!x ([F]x & [R]xy))\<guillemotright>\<close> by (auto dest: "&E" "1-1-cor"[THEN "\<equiv>\<^sub>d\<^sub>fE"] intro!: print_as_theoremI "\<equiv>I" "\<rightarrow>I" "&I" "cqt:2[const_var]"[axiom_inst] "1-1-cor"[THEN "\<equiv>\<^sub>d\<^sub>fI"])}
\end{quote}

The relation to a bijection is readily apparent: for any object exemplified by @{text F}, the relation @{text R}
identifies a unique object exemplified by @{text G} and vice-versa.

However, this unrestricted notion of a one-to-one correspondence is not well-suited for a definition
of equinumerosity that validates Hume's principle in AOT. The intuitive reason for this is that abstract
objects cannot be counted. In particular, recall that there are distinct, but
exemplification-indistinguishable abstract objects (see section~\ref{IndistinguishableAbstractObjects} and~\nameref{AOT:aclassical2}):

\begin{quote}
@{thm[display] "aclassical2"[print_as_theorem]}
\end{quote}

Based on this fact, we can prove that there is no one-to-one correspondence between @{term \<open>\<guillemotleft>A!\<guillemotright>\<close>}
and itself:
\<close>

AOT_theorem \<open>\<not>\<exists>R R |: A! \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> A!\<close>
proof(rule "raa-cor:2") \<comment> \<open>Proof by contradiction.\<close>
  AOT_assume \<open>\<exists>R R |: A! \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> A!\<close> \<comment> \<open>Assume the contrary.\<close>
  then AOT_obtain R where 0: \<open>R |: A! \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> A!\<close> \<comment> \<open>Let @{term R} be a witness.\<close>
    using "\<exists>E" by metis 
  \<comment> \<open>By definition of a one-to-one correspondence it follows that:\<close>
  AOT_hence \<open>\<forall>x ([A!]x \<rightarrow> \<exists>!y ([A!]y & [R]xy))\<close>
    using "1-1-cor"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  \<comment> \<open>Now let @{term a} and @{term b} be witnesses to the theorem cited above.\<close>
  moreover AOT_obtain a b where 1: \<open>A!a & A!b & a \<noteq> b & \<forall>F([F]a \<equiv> [F]b)\<close>
    using "aclassical2" "\<exists>E"(*<*)[rotated](*>*) by blast
  \<comment> \<open>Taken together, this means there has to be a unique abstract object to which @{term a} bears @{term R}.\<close>
  ultimately AOT_have \<open>\<exists>!y ([A!]y & [R]ay)\<close>
    using "\<forall>E"(2) "&E" "\<rightarrow>E" by blast
  \<comment> \<open>Now let @{term c} be a witness, s.t. @{term c} is abstract and @{term a} bears @{term R} to @{term c}.\<close>
  then AOT_obtain c where 2: \<open>A!c & [R]ac\<close>
    using "&E"(1) "\<exists>E"(*<*)[rotated](*>*) "uniqueness:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"] by blast
  \<comment> \<open>By beta-conversion it follows that @{term a} exemplifies @{emph \<open>being an @{term x} that bears @{term R} to @{term c}.\<close>}\<close>
  AOT_hence \<open>[\<lambda>x [R]xc]a\<close>
    by (auto intro!: "\<beta>\<leftarrow>C" "cqt:2" dest: "&E")
  \<comment> \<open>Since by construction @{term a} and @{term b} exemplify the same properties, the same holds true for @{term b}.\<close>
  AOT_hence \<open>[\<lambda>x [R]xc]b\<close>
    by (safe intro!: 1[THEN "&E"(2), THEN "\<forall>E"(1), THEN "\<equiv>E"(1)]) "cqt:2[lambda]"
  \<comment> \<open>Again by beta conversion it follows that @{term b} bears @{term R} to @{term c}.\<close>
  AOT_hence 5: \<open>[R]bc\<close>
    using "\<beta>\<rightarrow>C" by blast
  \<comment> \<open>Now the following is a consequence of the assumption that @{term \<open>\<guillemotleft>A!\<guillemotright>\<close>} is in one-to-one correspondence to itself:\<close>
  AOT_have \<open>\<forall>x \<forall>y \<forall>z ([A!]x & [A!]y & [A!]z \<rightarrow> ([R]xz & [R]yz \<rightarrow> x = y))\<close>
    using "eq-1-1"[unvarify F G, OF "oa-exist:2", OF "oa-exist:2", THEN "\<equiv>E"(1),
                   THEN "fFG:4"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(1),
                   THEN "fFG:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2), OF 0].
  \<comment> \<open>In particular this is true for @{term a}, @{term b} and @{term c}.\<close>
  AOT_hence \<open>[A!]a & [A!]b & [A!]c \<rightarrow> ([R]ac & [R]bc \<rightarrow> a = b)\<close>
    using "\<forall>E"(2) by blast
  \<comment> \<open>But we already established that @{term a}, @{term b} and @{term c} are abstract, as well as
      that @{term a} bears @{term R} to @{term c} and @{term b} bears @{term R} to @{term c}, so
      @{term a} and @{term b} have to be identical.\<close>
  AOT_hence \<open>a = b\<close>
    using 1[THEN "&E"(1)] 2 5 "&E" "\<rightarrow>E" "&I" by metis
  \<comment> \<open>Which contradicts @{term a} and @{term b} being distinct by construction.\<close>
  AOT_thus \<open>p & \<not>p\<close> for p
    using 1 "=-infix" "\<equiv>\<^sub>d\<^sub>fE" "&I" "&E" "raa-cor:1" by fast
qed

text\<open>
So if @{emph \<open>equinumerosity\<close>} was defined to be contingent on the existence of a full one-to-one correspondence,
@{term \<open>\<guillemotleft>A!\<guillemotright>\<close>} would not be equinumerous to itself and consequently equinumerosity
would not be an equivalence relation. However, Frege's construction assumes that
equinumerosity partitions all properties into equivalence classes, i.e. that equinumerosity
@{emph \<open>is\<close>} an equivalence relation. While it is an interesting question for future
research, whether a variant of the construction was possible, in which equinumerosity merely
was a partial equivalence relation (and consequently not all properties could be counted,
resp. @{emph \<open>the number of @{text F}s\<close>} would not denote for every @{text F}), the
construction in the current version of PLM at the time of writing chooses to
stay closer to Frege's original method. In particular, Nodelman and Zalta restrict
their analysis to @{emph \<open>ordinary objects\<close>} and we will therefore choose this option for
the main discussion in this chapter.

In section~\ref{NewNumberTheory} we will discuss alternative options to address the issue
that may lead to an enhanced version of the construction in the future.
\<close>

subsection\<open>One-to-One Correspondences on the Ordinary Objects\<close>text\<open>\label{OneToOneCorrespondenceE}\<close>

text\<open>
As mentioned in the introduction of this chapter, natural mathematics arises from abstracting
exemplification patterns. In case of natural numbers, those patterns in particular
need to be among objects that can be counted. While abstract objects in general cannot,
ordinary objects can always naturally be counted.
Hence Nodelman and Zalta introduce the notion of one-to-one correspondences @{emph \<open>among the ordinary
objects\<close>}. To that end, they introduce the restricted variables @{term u}, @{term v}, @{term r}, @{term s}
that range over only the ordinary objects.@{footnote \<open>Recall the discussion about reproducing
restricted variables in the embedding in section~\ref{RestrictedVariables}.\<close>} Using these restricted variables, a one-to-one
correspondence@{text \<open>\<^sub>E\<close>} among the ordinary objects can be defined in the same way as a full one-to-one
correspondence (see~\nameref{AOT:equi:2}):

\begin{quote}
@{lemma[display] \<open>print_as_theorem \<guillemotleft>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G \<equiv> \<forall>u ([F]u \<rightarrow> \<exists>!v ([G]v & [R]uv)) & \<forall>v ([G]v \<rightarrow> \<exists>!u ([F]u & [R]uv))\<guillemotright>\<close> by (auto dest: "&E" "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] intro!: print_as_theoremI "\<equiv>I" "\<rightarrow>I" "&I" "cqt:2[const_var]"[axiom_inst] "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"])}
\end{quote}
\<close>

subsection\<open>Definition of Equinumerosity\<close>text\<open>\label{DefinitionOfEquinumerosity}\<close>

text\<open>
Based on one-to-one correspondences@{text \<open>\<^sub>E\<close>} on the ordinary objects, @{emph \<open>equinumerosity\<close>} on the ordinary objects
can be defined as suggested above: two relations are equinumerous@{text \<open>\<^sub>E\<close>}, if and only if there is a one-to-one
correspondence@{text \<open>\<^sub>E\<close>} on the ordinary objects between them (see~\nameref{AOT:equi:3}):@{footnote \<open>In the following sections we will drop the explicit mention
of the restriction to the ordinary objects and simply talk about @{emph \<open>equinumerosity\<close>} and being @{emph \<open>equinumerous\<close>}
instead of @{emph \<open>equinumerosity on the ordinary objects\<close>}, resp. @{emph \<open>equinumerous@{text \<open>\<^sub>E\<close>}\<close>}.\<close>}

\begin{quote}
@{thm[display] "equi:3"[of F G]}
\end{quote}

Equinumerosity on the ordinary objects is indeed an equivalence relation (see~\nameref{AOT:eq-part:1}):

\begin{quote}
@{thm[display] "eq-part:1"[of _ F, print_as_theorem] "eq-part:2"[of _ F G, print_as_theorem] "eq-part:3"[of _ F G H, print_as_theorem]}
\end{quote}

Reflexivity can be shown by using the identity on the ordinary objects @{term \<open>\<guillemotleft>(=\<^sub>E)\<guillemotright>\<close>} (see~\ref{IdentitySubE}) as witness for
the existence of a one-to-one-correspondence@{text \<open>\<^sub>E\<close>} between any property and itself. Note that this
is only possible, since, in contrast to general identity, identity on the ordinary objects constitutes
a (denoting) relation.

Symmetry is a simple consequence of the symmetry of the definition of one-to-one correspondences@{text \<open>\<^sub>E\<close>}.

Transitivitity requires a slightly more verbose proof (see~\nameref{AOT:eq-part:3}), that hinges on the fact that
@{term \<open>\<guillemotleft>[\<lambda>xy O!x & O!y & \<exists>v ([G]v & [R\<^sub>1]xv & [R\<^sub>2]vy)]\<guillemotright>\<close>} can be chosen as a witness for the existence
of a one-to-one-correspondence@{text \<open>\<^sub>E\<close>} between @{term F} and @{term H}, if @{term R\<^sub>1} is a one-to-one-correspondence@{text \<open>\<^sub>E\<close>}
between @{term F} and @{term G} and @{term R\<^sub>2} is a one-to-one-correspondence@{text \<open>\<^sub>E\<close>} between @{term G} and @{term H}.
\<close>

subsection\<open>Properties of Equinumerosity\<close>

text\<open>
Nodelman and Zalta continue to derive a variety of properties of equinumerosity that are helpful
for the remainder of the construction. While a full account of the progression of theorems can be
found in PLM, respectively in our implementation in \ref{AOT:AOT_NaturalNumbers}, the following is a
selection of noteworthy auxiliary theorems:

Properties that are unexemplified on the ordinary objects are equinumerous (any relation may serve
as one-to-one-correspondence@{text \<open>\<^sub>E\<close>} between them; see~\nameref{AOT:empty-approx:1}):
\begin{quote}
@{thm[display] "empty-approx:1"[of _ F H, print_as_theorem]}
\end{quote}

A property @{term F} that is exemplified by some ordinary object is @{emph \<open>not\<close>} equinumerous
to a relation @{term H} that is not exemplified by any ordinary object (proof by contradiction, since
the existence of a one-to-one correspondence@{text \<open>\<^sub>E\<close>} would imply that @{term H} is exemplified by
an ordinary object; see~\nameref{AOT:empty-approx:2}):
\begin{quote}
@{thm[display] "empty-approx:2"[of _ F H, print_as_theorem]}
\end{quote}

Removing and adding ordinary objects to equinumerous properties yields equinumerous properties (see~\nameref{AOT:eqP'}):@{footnote \<open>The statements
rely on the following definition of @{term \<open>\<guillemotleft>[F]\<^sup>-\<^sup>x\<guillemotright>\<close>}, i.e. @{emph \<open>being an F that is not @{term x}\<close>}: @{thm "F-u"}. The proofs
rely on constructing suitable one-to-one correspondences@{text \<open>\<^sub>E\<close>} by case analysis.\<close>}
\begin{quote}
@{thm[display] eqP'[of _ F G u v, print_as_theorem]
                "P'-eq"[of _ F u G v, print_as_theorem]}
\end{quote}

Properties that are equivalent on the ordinary objects (written as @{text "\<equiv>\<^sub>E"}) are equinumerous (see~\nameref{AOT:eqE},~\nameref{AOT:apE-eqE:1}):@{footnote \<open>The identity
on the ordinary objects @{term \<open>\<guillemotleft>(=\<^sub>E)\<guillemotright>\<close>} can be chosen as witness for the existence of a one-to-one-correspondence@{text \<open>\<^sub>E\<close>}.\<close>}

\begin{quote}
@{thm[display] eqE[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I", OF "cqt:2[const_var]"[axiom_inst], OF "cqt:2[const_var]"[axiom_inst], of _ F G, print_as_theorem]
               "apE-eqE:1"[of _ F G, print_as_theorem]}
\end{quote}
\<close>

subsection\<open>Modal Properties of Equinumerosity\<close>

text\<open>
It is noteworthy that, in general, equinumerosity is @{emph \<open>not\<close>} modally rigid. In particular, it
is provable that there are relations that are possibly equinumerous and possibly not equinumerous (see~\nameref{AOT:approx-cont:1}):

\begin{quote}
@{thm[display] "approx-cont:1"[print_as_theorem]}
\end{quote}

As a simple example consider a property that is necessarily unexemplified and another property
that is @{emph \<open>actually\<close>} unexemplified, but @{emph \<open>possibly\<close>} exemplified by some ordinary object.@{footnote \<open>The
existence of such properties is guaranteed by the fact that by axiom there is an object that is not actually, but
possibly concrete as mentioned in section~\ref{AxiomSystem}.\<close>}
While such properties are equinumerous in the actual world, there is no one-to-one-correspondence@{text \<open>\<^sub>E\<close>}
between them in the possible world, in which the second property is exemplified by an object.

We will see in the next section that for this reason it makes sense to use the actual world as a reference for the definition
of @{emph \<open>numbering properties\<close>}.

In any modal context, it is possible to express equinumerosity relative to the behaviour of properties
in the actual world. In particular the following is a (modally-strict) theorem (see~\nameref{AOT:approx-nec:2}):
\begin{quote}
@{thm[display] "approx-nec:2"[of _ F G, print_as_theorem]}
\end{quote}

I.e. two properties @{term F} and @{term G} are equinumerous, if and only if for all properties @{term H},
@{term F} is equinumerous to @{emph \<open>actually exemplifying @{term H}\<close>} just in case that
@{term G} is. Furthermore, for @{emph \<open>rigid\<close>} properties,@{footnote \<open>I.e. properties that are modally collapsed: @{thm "df-rigid-rel:1"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "cqt:2[const_var]"[axiom_inst], of _ F, rename_abs x, print_as_theorem]}, see also~\ref{WorldRelativeRelations}.\<close>}
equinumerosity is modally collapsed (see~\nameref{AOT:approx-nec:3}):
\begin{quote}
@{thm[display] "approx-nec:3"[of _ F G, print_as_theorem]}
\end{quote}

The proofs of the last two theorems hinge on the existence of @{emph \<open>rigidifying\<close>} relations. Recall the
earlier discussion of this topic in section~\ref{WorldRelativeRelations} - notably, in earlier versions of PLM,
the existence of rigidifying relations had to be ensured by axiom. In the current formulation of AOT,
the necessary and sufficient conditions for relations to denote that we contributed
to the theory (see section~\ref{KirchnersTheorem}), can be used to prove the existence of @{emph \<open>world-indexed properties\<close>}
that can serve as witnesses for the existence of rigidifying relations, thereby eliminating the need
for the additional axiom.

\<close>




section\<open>The Number of Fs and Hume's Theorem\<close>text\<open>\label{Numbers}\<close>

text\<open>
To state Hume's Theorem, additionally to the definition of @{emph \<open>equinumerosity\<close>} above,
a definition of @{emph \<open>The Number of @{term F}s\<close>} (written as @{term \<open>\<guillemotleft>#F\<guillemotright>\<close>}) is required.
To that end Nodelman and Zalta first define what it means for an object
to number a property as follows (see~\nameref{AOT:numbers}):

\begin{quote}
@{thm[display] "numbers[den]"[THEN "\<rightarrow>E", OF "cqt:2[const_var]"[axiom_inst], of _ x G, print_as_theorem]}
\end{quote}

An abstract object @{term x} numbers a property @{term G}, if it encodes exactly those properties,
such that @{emph \<open>actually exemplifying\<close>} them is equinumerous to @{term G}.
An alternative choice would be to forgo the actuality operator and merely require that @{term x}
encodes exactly those properties that are themselves equinumerous to @{term G}.@{footnote \<open>In fact,
earlier versions of the construction used this definition (see e.g.~\cite{zalta1999}).\<close>}
 However, we noted in the last section that equinumerosity is (in general) not modally rigid, so
such a definition would have the undesirable consequence that numbering properties would depend on modal context and
consequently that every possible world would need its own sets of numbers (see~\ref{CountingInPossibleWorlds}). To avoid this
issue the actual world is used as a reference. Later in this chapter, we will show that this does
@{emph \<open>not\<close>} mean that it is impossible to count in non-actual worlds and that this definition is consistent with
the pretheoretic intuition of numbers in possible worlds (see~\ref{CountingInPossibleWorlds}).

Now @{emph \<open>The Number of @{term G}s\<close>} can simply be defined as @{emph \<open>the\<close>} object that numbers
@{term G} (see~\nameref{AOT:num-def:1}):

\begin{quote}
@{thm[display] "num-def:1"}
\end{quote}

Using these definitions Hume's theorem becomes derivable (see~\nameref{AOT:hume:2}):

\begin{quote}
@{thm[display] "hume:2"[of F G]}
\end{quote}

Note that, due to the fact that AOT's definite descriptions are modally rigid and refer to objects
in the actual world, this theorem is not modally strict.@{footnote \<open>Recall that this is signified by the turnstile
symbol @{text "\<^bold>\<turnstile>"} and recall the discussion in section~\ref{ModallyStrictFragile}.\<close>} However, the following variants are necessary facts with modally-strict proofs (see~\nameref{AOT:hume-strict:1}):

\begin{quote}
@{thm[display] "hume-strict:1"[of _ F G, print_as_theorem]}
@{thm[display] "hume-strict:2"[of _ F G, print_as_theorem]}
\end{quote}

Note that the last theorem corresponds to a translation of the descriptions in Hume's theorem according to Russell's analysis of
definite descriptions.
\<close>

section\<open>The Number Zero\<close>

(*<*)
AOT_lemma ord_eq_e_eq: \<open>(O!x & x \<noteq>\<^sub>E x) \<equiv> (O!x & x \<noteq> x)\<close>
proof (safe intro!: "\<equiv>I" "\<rightarrow>I" "&I" dest: "&E"; (auto dest: "&E"; fail)?)
  AOT_assume \<open>O!x & x \<noteq>\<^sub>E x\<close>
  AOT_thus \<open>x \<noteq> x\<close>
    by (metis "contraposition:1[2]" "\<equiv>E"(1) "ord=Eequiv:1" "thm-neg=E" "\<rightarrow>E" "\<rightarrow>I" "&E")
next
  AOT_assume \<open>O!x & x \<noteq> x\<close>
  AOT_thus \<open>x \<noteq>\<^sub>E x\<close>
    by (meson "=-infix" "\<equiv>\<^sub>d\<^sub>fE" "&E"(2) "raa-cor:3" "rule=I:2[const_var]")
qed
(*>*)

text\<open>
  Given the fact that we defined numbers by means of the properties they number, which in turn is - informally
speaking - based on how many objects those properties exemplify, a natural definition of the number zero arises.
The number zero is the object that numbers the empty property, to be more precise the number of
@{emph \<open>being a non-self-identical ordinary object\<close>} (see~\nameref{AOT:zero:1}).@{footnote \<open>To be precise being a
non-self-identical@{text \<open>\<^sub>E\<close>} object (see section~\ref{IdentitySubE}).
This distincation is non-trivial: While @{thm ord_eq_e_eq[of _ x, print_as_theorem]} is a theorem,
due to the hyperintensionality of object theory, it does not have to be the case that
@{term \<open>\<guillemotleft>[\<lambda>x O!x & x \<noteq>\<^sub>E x]\<guillemotright>\<close>} and @{term \<open>\<guillemotleft>[\<lambda>x O!x & x \<noteq> x]\<guillemotright>\<close>} are the same property (as a matter of fact it is
not even asserted @{emph \<open>a priori\<close>} that the latter even denotes a property at all). So
@{term \<open>\<guillemotleft>#[\<lambda>x O!x & x \<noteq>\<^sub>E x]\<guillemotright>\<close>} and @{term \<open>\<guillemotleft>#[\<lambda>x O!x & x \<noteq> x]\<guillemotright>\<close>} are not the same object
@{emph \<open>a priori\<close>}, even though it is a theorem that they are identical. But this theorem
has to appeal to the fact that both properties are equinumerous and to Hume's Theorem.
Further examples of terms denoting the number zero are @{term \<open>\<guillemotleft>#[\<lambda>x x \<noteq> x]\<guillemotright>\<close>} and
@{term \<open>\<guillemotleft>#[\<lambda>x \<exists>p (p & \<not>p)]\<guillemotright>\<close>}.\<close>}

\begin{quote}
@{thm[display] "zero:1"}
\end{quote}

Note that while the above definition introduces the number zero as (abstract) object, we have not
defined the notion of a @{emph \<open>Natural Number\<close>} yet, nor shown that the number zero indeed @{emph \<open>is\<close>} a
natural number. The definition of @{emph \<open>Natural Number\<close>} will rely on introducing a @{emph \<open>predecessor\<close>}
relation and, intuitively speaking, defining that an abstract object is a natural number, if there is
a series of objects starting at zero, ending at the given abstract object, s.t. two consecutive objects
in that series bear the predecessor relation to each other. While we will describe this construction
in detail in the following sections, we can already define the strictly more general@{footnote \<open>It is
a theorem that @{term \<open>\<guillemotleft>#O!\<guillemotright>\<close>} is a natural cardinal that is infinite and not a natural number (see~\nameref{AOT:inf-card-exist:2}).\<close>} notion of a
@{emph \<open>Natural Cardinal\<close>} and it will immediately follow that zero is a natural cardinal.
An object @{term x} is a natural cardinal, just in case that there is a property @{term G},
s.t. @{term x} is the number of @{term G}s (see~\nameref{AOT:card}):

\begin{quote}
@{thm[display] card[of x]}
\end{quote}

By the definition of the number zero, it becomes immediately apparent that zero is a natural cardinal (see~\nameref{AOT:zero-card}):@{footnote \<open>However,
note that the proof has to appeal to the fact that @{thm "num-def:2"[print_as_theorem, of G]} (see~\nameref{AOT:num-def:2}) as well as the
fact that @{lemma \<open>print_as_theorem \<guillemotleft>[\<lambda>x O!x & x \<noteq>\<^sub>E x]\<down>\<guillemotright>\<close> by (auto simp: print_as_theorem_def intro!: "cqt:2")} by axiom.\<close>}

\begin{quote}
@{thm[display] "zero-card"[print_as_theorem]}
\end{quote}

\<close>


section\<open>Counting in Possible Worlds\<close>text\<open>\label{CountingInPossibleWorlds}\<close>

text\<open>
In section~\ref{Numbers}, we mentioned the use of the actual world as reference for defining numbering
properties and hinted at the fact that this is justified and consistent with pretheoretic intuition.
We can now discuss this in more detail at the example of the number Zero.

The number of a property is defined as rigid definite description
and thereby uses the actual world as frame of reference.
In particular, using the number Zero as example, this means the following (see~\nameref{AOT:0F:2}):

\begin{quote}
@{thm[display] "0F:2"[of _ F, print_as_theorem]}
\end{quote}

If and only if a property @{term F} is not @{emph \<open>actually\<close>} exemplified by any ordinary object,
the number of that property is Zero. This may seem counter-intuitive at first: the stated theorem
is modally-strict and thereby a @{emph \<open>necessary\<close>} fact. So in any possible world, even in worlds
in which @{term F} could be exemplified, the number of @{term F} is still zero, if
@{term F} is not @{emph \<open>actually\<close>} exemplified. However, this is merely due to the fact that
definite descriptions are rigid and themselves refer to objects in the actual world.

Moving away from the rigidly defined @{emph \<open>number of Fs\<close>}, it is a modally-strict theorem
(and thereby a @{emph \<open>necessary\<close>} fact), that Zero @{emph \<open>numbers\<close>} any property that is not
exemplified by any ordinary object (see~\nameref{AOT:0F:1}):
\begin{quote}
@{thm[display] "0F:1"[of _ F, print_as_theorem]
               "0F:1"[THEN RN, of _ F, print_as_theorem]}
\end{quote}

I.e. Zero numbers empty properties in all possible worlds. A different take on this is the
fact that any object that @{emph \<open>possibly\<close>} numbers a necessarily empty property is the number zero (see~\nameref{AOT:AOT_misc.PossiblyNumbersEmptyPropertyImpliesZero}):
\begin{quote}
@{thm[display] PossiblyNumbersEmptyPropertyImpliesZero[of _ x, print_as_theorem]}
\end{quote}

By contrast, if numbering a property had been defined without using the actual world
as reference, then "the" number Zero would be a different abstract object in different possible worlds:

If we define @{text \<open>Numbers'\<close>} without the use of the actuality operator, s.t.:
\begin{quote}
@{thm[display] Numbers'equiv[of _ x G, print_as_theorem]}
\end{quote}
Then it is a theorem (see~\nameref{AOT:AOT_misc.Numbers'DistinctZeroes}) that:
\begin{quote}
@{thm[display] Numbers'DistinctZeroes[print_as_theorem]}
\end{quote}
I.e. there would be distinct abstract objects that might count necessarily empty properties.
This is clearly contrary to the pretheoretic intuition that numbers are universal, i.e. that
counting empty properties in any world will yield one and the same number Zero.

On the other hand, we can further consolidate the use of the actual world as reference frame, by
realizing that we @{emph \<open>can\<close>} talk about the numbers of properties in different worlds, despite the
rigidity of definite descriptions and the use of the actual world as reference for defining numbers.
We again use the number Zero as example and can show that if and only if a property @{term F} is not exemplified
in a given possible world @{term w}, then @{emph \<open>the number of exemplifying @{term F} at @{term w}\<close>}
is Zero (see~\nameref{AOT:0F:4}):@{footnote \<open>Recall the discussion
of AOT's theory of Possible Worlds and world-indexed properties in section~\ref{WorldRelativeRelations}.\<close>}
\begin{quote}
@{thm[display] "0F:4"[of _ w F, print_as_theorem]}
\end{quote}

\<close>



section\<open>Ancestral Relations and Transitive Closures\<close>

text\<open>
As mentioned above, natural numbers will, informally speaking, be defined by the means of
series of objects that bear a (yet to be introduced) predecessor relation to each other.
However, traditionally, a series of objects relies on it being possible to index its objects using a
continuous sequence of natural numbers. Since our goal is to @{emph \<open>define\<close>} natural numbers, using
this traditional notion of a series is not an option.
Instead we construct @{emph \<open>ancestral relations\<close>}. In particular the @{emph \<open>strong ancestral\<close>} of
a relation will match the concept of the transitive closure of the relation.
Natural numbers will be defined as the objects to which the number zero bears the
@{emph \<open>weak ancestral\<close>} (i.e. the transitive and reflexive@{footnote \<open>We will see that reflexivity
will have to be restricted to a specific domain.\<close>} closure) of the predecessor relation, i.e. the number zero itself or any
object that is transitively preceded by zero.

The first step in this process is to define being a @{emph \<open>hereditary\<close>} property with respect to
a relation, which will lead to a definition of the @{emph \<open>strong ancestral\<close>} of a relation.

\<close>

subsection\<open>Properties that are Hereditary with respect to a Relation\<close>

text\<open>
A property @{term F} is @{emph \<open>hereditary\<close>} w.r.t. a relation @{term R}, if and only if for every pair
of objects @{term x} and @{term y}, s.t. @{term x} bears @{term R} to @{term y}, if @{term x} exemplifies
@{term F}, then @{term y} exemplifies @{term F} (see~\nameref{AOT:hered:1}):

\begin{quote}
@{thm[display] "hered:1"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I", OF "cqt:2[const_var]"[axiom_inst], OF "cqt:2[const_var]"[axiom_inst], of _ F R, print_as_theorem]}
\end{quote}


Intuitively, a relation @{term R} defines sequences of objects as follows: we call a list of
objects @{term x\<^sub>1}, ..., @{term x\<^sub>n} an @{term R}-induced sequence, if for every @{text "0 < i < n"}, 
@{term x\<^sub>i} bears @{term R} to @{text \<open>x\<^bsub>i+1\<^esub>\<close>}.
Then @{term F} being hereditary w.r.t. @{term R} means that any @{term R}-induced sequence starting
in @{term F} (i.e. starting with an object exemplified by @{term F}), is completely contained in
@{term F} (i.e. every object in the sequence exemplifies @{term F} as well).

Or in other words, a property @{term F} is hereditary w.r.t a relation @{term R}, if "@{term F}-ness"
is inherited from all objects that exemplify @{term F} to the objects that are @{term R}-related to them.
\<close>

subsection\<open>Strong Ancestral of a Relation and Transitive Closures\<close>

text\<open>
Using the above definition, we can introduce the @{emph \<open>Strong Ancestral\<close>} of a relation @{term R},
which is written as @{term \<open>\<guillemotleft>[R]\<^sup>*\<guillemotright>\<close>} (see~\nameref{AOT:ances-df}):\footnote{Note that while
PLM uses @{text \<open>R\<^sup>*\<close>} for the strong ancestral, i.e. the transitive closure, of @{term R} and later @{text \<open>R\<^sup>+\<close>}
for the weak ancestral, i.e. the transitive and reflexive closure, of @{term R}, Isabelle's HOL library
uses the opposite convention, i.e. it uses @{text \<open>r\<^sup>+\<close>} as transitive and @{text \<open>r\<^sup>*\<close>} as reflexive-transitive closure.}

\begin{quote}
@{thm[display] "ances-df"}
\end{quote}

An object @{term x} bears @{term \<open>\<guillemotleft>[R]\<^sup>*\<guillemotright>\<close>} to @{term y}, just in case that @{term y} exemplifies every
property @{term F} that is hereditary w.r.t @{term R} and that is exemplified by all objects to
which @{term x} bears @{term R}.
To convince ourselves that this definition captures the transitive closure of @{term R}, we may fix
@{term x} and consider a property @{term F}, s.t. @{term \<open>\<guillemotleft>\<forall>z([R]xz \<rightarrow> [F]z) & Hereditary(F,R)\<guillemotright>\<close>}.
Any such property @{term F} is exemplified by all objects immediately following @{term x} in an
@{term R}-induced sequence (first conjunct) as well as all objects in any longer @{term R}-induced
sequence starting at @{term x} (second conjunct). Hence (informally thinking of properties as sets)
any such @{term F} contains all objects that are transitively related to @{term x}. Note,
however, that @{term F} may exemplify additional objects that are not part of any @{term R}-induced
sequence. However, the intersection of all such properties @{term F} yields the smallest set of
objects that are transitively related to @{term x}, which is @{emph \<open>exactly\<close>} those objects that
@{emph \<open>are\<close>} transitively related to @{term x}.

It is interesting to note that there is a different way to define the transitive closure of
a relation @{term R}, namely:

The transitive closure of a relation @{term R} is the intersection of all transitive relations @{term R'} that
are contained in @{term R}.
As a matter of fact, we can state this definition in AOT as well, and prove it to be equivalent to
the strong ancestral of @{term R}.

First we define for a relation to be transitive as follows:
\<close>

AOT_define Transitive :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>Transitive'(_')\<close>)
  \<open>Transitive(R) \<equiv>\<^sub>d\<^sub>f \<forall>x\<forall>y\<forall>z([R]xy & [R]yz \<rightarrow> [R]xz)\<close>

text\<open>
Next we can define for a relation to be contained in another relation, or alternatively, moving
away from set-theoretic concepts, for a relation to entail another relation:
\<close>

AOT_define Entails :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>Entails'(_,_')\<close>)
  \<open>Entails(R,R') \<equiv>\<^sub>d\<^sub>f \<forall>x\<forall>y([R]xy \<rightarrow> [R']xy)\<close>

text\<open>
Being in the intersection of all transitive relations entailed by @{term R} means exemplifying
all of them. Hence we can define the transitive closure of @{term R} as follows:
\<close>

AOT_define TransitiveClosure :: \<open>\<tau> \<Rightarrow> \<Pi>\<close> (\<open>TransitiveClosure'(_')\<close>)
  \<open>TransitiveClosure(R) =\<^sub>d\<^sub>f [\<lambda>xy \<forall>R'(Transitive(R') & Entails(R,R') \<rightarrow> [R']xy)]\<close>

text\<open>
Now we can prove that this definition of a transitive closure is equivalent to the definition
of a strong ancestral above:
\<close>

AOT_theorem \<open>[TransitiveClosure(R)]xy \<equiv> [R\<^sup>*]xy\<close>
proof(safe intro!: "\<equiv>I" "\<rightarrow>I")
  AOT_assume \<open>[TransitiveClosure(R)]xy\<close>
  AOT_hence \<open>[\<lambda>xy \<forall>R'(Transitive(R') & Entails(R,R') \<rightarrow> [R']xy)]xy\<close>
    by (auto intro: "rule-id-df:2:a"[OF TransitiveClosure] intro!: "cqt:2")
  AOT_hence \<open>\<forall>R'(Transitive(R') & Entails(R,R') \<rightarrow> [R']xy)\<close>
    using "\<beta>\<rightarrow>C" by fast
  AOT_hence \<open>Transitive(R\<^sup>*) & Entails(R,R\<^sup>*) \<rightarrow> [R\<^sup>*]xy\<close>
    using "\<forall>E"(1) "rule-id-df:2:b"[OF "ances-df"] "hered:2" by blast
  \<comment> \<open>The following is a consequence of PLM's theorems about strong ancestral relations (see~\nameref{AOT:anc-her:1} and~\nameref{AOT:anc-her:6}).\<close>
  moreover AOT_have \<open>Transitive(R\<^sup>*) & Entails(R,R\<^sup>*)\<close>
    by (auto intro!: "&I" Entails[THEN "\<equiv>\<^sub>d\<^sub>fI"] Transitive[THEN "\<equiv>\<^sub>d\<^sub>fI"] GEN "\<rightarrow>I"
               simp: "anc-her:1"[THEN "\<rightarrow>E"] "anc-her:6"[THEN "\<rightarrow>E"])
  ultimately AOT_show \<open>[R\<^sup>*]xy\<close>
    using "\<rightarrow>E" "&I" by blast
next
  AOT_assume 0: \<open>[R\<^sup>*]xy\<close>
  AOT_have \<open>\<forall>R'(Transitive(R') & Entails(R,R') \<rightarrow> [R']xy)\<close>
  proof(safe intro!: GEN "\<rightarrow>I"; frule "&E"(1); drule "&E"(2))
    fix R'
    AOT_assume transitive: \<open>Transitive(R')\<close> and entails: \<open>Entails(R,R')\<close>
    \<comment> \<open>The following is an instance of another theorem about strong ancestral relations (see~\nameref{AOT:anc-her:2}).\<close>
    AOT_have \<open>[R\<^sup>*]xy & \<forall>z([R]xz \<rightarrow> [\<lambda>z [R']xz]z) & Hereditary([\<lambda>z [R']xz],R) \<rightarrow> [\<lambda>z [R']xz]y\<close>
      by (rule "anc-her:2"[unvarify F]) "cqt:2[lambda]"
    moreover AOT_have \<open>Hereditary([\<lambda>z [R']xz],R)\<close>
    proof (safe intro!: "hered:1"[THEN "\<equiv>\<^sub>d\<^sub>fI"] "&I" "cqt:2" GEN "\<rightarrow>I")
      fix z y
      AOT_assume \<open>[R]zy\<close> and \<open>[\<lambda>z [R']xz]z\<close>
      AOT_hence \<open>[R']zy\<close> and \<open>[R']xz\<close>
        using entails by (auto dest: Entails[THEN "\<equiv>\<^sub>d\<^sub>fE"] "\<forall>E"(2) "\<rightarrow>E" "\<beta>\<rightarrow>C")
      AOT_hence \<open>[R']xy\<close>
        using transitive by (auto dest!: Transitive[THEN "\<equiv>\<^sub>d\<^sub>fE"] dest: "\<forall>E"(2) "\<rightarrow>E" intro!: "&I")
      AOT_thus \<open>[\<lambda>z [R']xz]y\<close>
        by (auto intro!: "\<beta>\<leftarrow>C" "cqt:2")
    qed
    moreover AOT_have \<open>\<forall>z([R]xz \<rightarrow> [\<lambda>z [R']xz]z)\<close>
      using entails[THEN Entails[THEN "\<equiv>\<^sub>d\<^sub>fE"]]
      by (auto intro!: GEN "\<rightarrow>I" "\<beta>\<leftarrow>C" "cqt:2" dest: "\<forall>E"(2) "\<rightarrow>E")
    ultimately AOT_have \<open>[\<lambda>z [R']xz]y\<close>
      using 0 "&I" "\<rightarrow>E" by auto
    AOT_thus \<open>[R']xy\<close>
      by (rule "\<beta>\<rightarrow>C")
  qed
  AOT_thus \<open>[TransitiveClosure(R)]xy\<close>
    by (auto intro: "rule-id-df:2:b"[OF TransitiveClosure]
             intro!: "\<beta>\<leftarrow>C" "cqt:2" tuple_denotes[THEN "\<equiv>\<^sub>d\<^sub>fI", OF "&I"])
qed
(*<*)
(* TODO: think about mentioning this (especially due to opposite meaning of * and +): *)
find_theorems trancl
find_theorems tranclp
lemma \<open>R\<^sup>+ = {(a,b) . \<forall>R' . trans R' \<and> (R \<subseteq> R') \<longrightarrow> (a,b) \<in> R'}\<close>
  apply (rule; rule)
   apply simp
   apply (metis trancl_id trancl_mono)
  apply simp
  by (simp add: subrelI)
(*>*)

section\<open>Weak Ancestral Relations\<close>

text\<open>
As mentioned above, our goal is to define being a natural number as either being Zero or being an
object, s.t. Zero bears the strong ancestral of the to-be-defined predecessor relation to it.
This matches the notion of the @{emph \<open>weak ancestral\<close>} of the predecessor relation. Traditionally,
the weak ancestral of a relation @{term \<open>\<guillemotleft>[R]\<^sup>+\<guillemotright>\<close>} is defined, s.t. an object @{term x}
bears @{term \<open>\<guillemotleft>[R]\<^sup>+\<guillemotright>\<close>} to an object @{term y}, if and only if either @{term x} bears the strong ancestral
@{term \<open>\<guillemotleft>[R]\<^sup>*\<guillemotright>\<close>} to @{term y} or @{term \<open>x = y\<close>}.

However, recall that in AOT there is no general relation of identity, i.e. @{term \<open>\<guillemotleft>[\<lambda>xy x = y]\<guillemotright>\<close>} does not
denote (see~\ref{IndistinguishableAbstractObjects}). Consequently, the immediate candidate
for defining the weak ancestral of a relation @{term \<open>\<guillemotleft>[\<lambda>xy [R]\<^sup>*xy \<or> x = y]\<guillemotright>\<close>} does not denote
for arbitrary choices of @{term R}.@{footnote \<open>For example, if @{term R} is a necessarily empty relation,
the matrix of  @{term \<open>\<guillemotleft>[\<lambda>xy [R]\<^sup>*xy \<or> x = y]\<guillemotright>\<close>}
is necessarily equivalent to @{term \<open>\<guillemotleft>[\<lambda>xy x = y]\<guillemotright>\<close>} for all @{term x} and @{term y} and
@{term \<open>\<guillemotleft>[\<lambda>xy [R]\<^sup>*xy \<or> x = y]\<guillemotright>\<close>} fails to denote by co-existence.\<close>}

For this reason Nodelman and Zalta proceed by introducing @{emph \<open>rigid one-to-one relations\<close>}.
Rigid one-to-one relations induce a notion of identity on their @{emph \<open>domain\<close>} that is consistent
with general identity (on this domain), but constitutes a denoting relation.
\<close>
subsection\<open>Rigid One-to-One Relations\<close>

text\<open>
For a relation to be @{emph \<open>one-to-one\<close>} is related to the notion of a function being injective.
A relation @{term R} is @{emph \<open>one-to-one\<close>}, if whenever two objects @{term x} and @{term y} bear
@{term R} to the same object @{term z}, then @{term x} and @{term y} are identical (see~\nameref{AOT:df-1-1:1}):

\begin{quote}
@{thm[display] "df-1-1:1"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "cqt:2[const_var]"[axiom_inst], of _ R, print_as_theorem]}
\end{quote}

Note, however, that one-to-one relations are more general than injective functions, since the criterion
to be one-to-one does not imply that the relation is @{emph \<open>functional\<close>}, i.e. that each object
in its domain is related to exactly one object.

An object @{term x} is in the domain of a relation @{term R}, just in case that there is an
object @{term y}, s.t. @{term x} bears @{term R} to @{term y} (see~\nameref{AOT:df-1-1:5}):

\begin{quote}
@{thm[display] "df-1-1:5"[of x R, THEN "\<equiv>Df", print_as_theorem]}
\end{quote}

While the predecessor relation will in fact be a functional relation, a relation that
relates a single object to all other objects, but no other object to any object, is an example of a
one-to-one relation that's succinctly non-functional. However, in order to introduce a restricted
notion of identity, functionality is not a requirement.

On the other hand, in order to simplify modal reasoning and to be able to introduce well-behaved
restricted variables, it is helpful to only consider @{emph \<open>rigid\<close>} one-to-one relations.
A rigid one-to-one relation is a relation that is one-to-one and rigid (see~\nameref{AOT:df-rigid-rel:1},~\nameref{AOT:df-1-1:2}):\footnote{Recall the discussion about rigid relations in section~\ref{WorldRelativeRelations}.}

\begin{quote}
@{thm[display] "df-1-1:2"[THEN "\<equiv>Df", of _ R, print_as_theorem]}
\end{quote}

Since being a rigid one-to-one relation is a rigid restriction condition, we can introduce 
well-behaved restricted variables that range over them.@{footnote \<open>Recall the discussion of restricted variables in section~\ref{RestrictedVariables}.\<close>}

In the following we will use @{term \<R>} as a restricted variable ranging over rigid one-to-one relations.@{footnote \<open>Note
that PLM uses $\underline{R}$. However, in our framework choosing @{term \<R>} is simpler for technical reasons.\<close>}
\<close>

subsection\<open>Identity Restricted to the Domain of Rigid One-to-one Relations\<close>

text\<open>
For a variable @{term \<R>} that is restricted to rigid one-to-one relations, a restricted notion
of identity can now be defined as follows (see~\nameref{AOT:id-d-R}):

\begin{quote}
@{thm[display] "id-d-R"}
\end{quote}

Note that in contrast to general identity, @{term \<R>}-identity is (trivially) a proper, denoting relation.

By @{text \<beta>}-conversion and using infix notation, two objects @{term x} and @{term y} are
@{term \<R>}-identical, just in case that there is an object to which they are both @{term \<R>}-related (see~\nameref{AOT:id-R-thm:1}):

\begin{quote}
@{thm[display] "id-R-thm:1"[of _ \<R> x y, print_as_theorem]}
\end{quote}

Since @{term \<R>} is restricted to rigid one-to-one relations, the resulting identity relation is exactly the
restriction of general identity to the domain of @{term \<R>} (see~\nameref{AOT:AOT_misc.restricted_identity}):

\begin{quote}
@{thm[display] restricted_identity[of _ \<R> x y, print_as_theorem]}
\end{quote}

Consequently, the defined identity is a partial equivalence relation that is
reflexive on the domain of @{term \<R>} (see~\nameref{AOT:id-R-thm:5}):

\begin{quote}
@{thm "id-R-thm:5"[of _ x \<R>, print_as_theorem]
      "id-R-thm:6"[of _ \<R> x y, print_as_theorem]
      "id-R-thm:7"[of _ \<R> x y z, print_as_theorem]}
\end{quote}

A simple example of a rigid one-to-one-relation is the identity on the ordinary objects @{term \<open>\<guillemotleft>(=\<^sub>E)\<guillemotright>\<close>}, the domain of
which is the ordinary objects (see~\nameref{AOT:AOT_misc.equal_E_rigid_one_to_one} and~\nameref{AOT:AOT_misc.equal_E_domain}).
\<close>

subsection \<open>The Weak Ancestral of a Relation\<close>

(*<*)
AOT_theorem ances_in_domain: \<open>InDomainOf(x,\<R>) \<rightarrow> ([\<R>]\<^sup>+xy \<equiv> [\<R>]\<^sup>*xy \<or> x = y)\<close>
proof(safe intro!: "\<rightarrow>I")
  AOT_assume \<open>InDomainOf(x,\<R>)\<close>
  AOT_hence 0: \<open>x =\<^sub>\<R> y \<equiv> x = y\<close>
    using "id-R-thm:4"[THEN "\<rightarrow>E", OF "\<or>I"(1)] by blast
  AOT_have \<open>[\<R>]\<^sup>+xy \<equiv> [\<R>]\<^sup>*xy \<or> x =\<^sub>\<R> y\<close>
    using "w-ances".
  also AOT_have \<open>\<dots> \<equiv> [\<R>]\<^sup>*xy \<or> x = y\<close>
    using 0 "oth-class-taut:8:g" "\<rightarrow>E" by blast
  finally AOT_show \<open>[\<R>]\<^sup>+xy \<equiv> [\<R>]\<^sup>*xy \<or> x = y\<close>.
qed
(*>*)

text\<open>
Based on the concept of @{term \<R>}-identity, the @{emph \<open>weak ancestral\<close>} @{term \<open>\<R>\<^sup>+\<close>} of a
rigid one-to-one relation @{text \<R>} can be defined as follows (see~\nameref{AOT:w-ances-df}):

\begin{quote}
@{thm[display] "w-ances-df"}
\end{quote}

Restricting to the domain of @{term \<R>}, two object are now exactly in the weak ancestral relation
@{term \<open>\<guillemotleft>[\<R>]\<^sup>+\<guillemotright>\<close>}, if they are either transitively @{term \<R>}-related (i.e. in the strong ancestral
relation @{term \<open>\<guillemotleft>[\<R>]\<^sup>*\<guillemotright>\<close>}) or identical:

\begin{quote}
@{thm[display] ances_in_domain[of _ x \<R> y, print_as_theorem]}
\end{quote}

In other words, the weak ancestral of a relation is its transitive and reflexive closure, with
reflexivity being restricted to the domain of the relation.
\<close>

section\<open>Generalized Induction\<close>text\<open>\label{GeneralizedInduction}\<close>

text\<open>
In order to understand the formulation of generalized induction, first consider the
following theorem that Nodelman and Zalta prove before even introducing weak ancestral relations,
but which already has "inductive character" (see~\nameref{AOT:anc-her:3}):

\begin{quote}
@{thm[display] "anc-her:3"[of _ F x R y, print_as_theorem]}
\end{quote}

While this may not look like an inductive principle as stated, unfolding the definition of
@{text \<open>Hereditary\<close>}, this is equivalent (under some trivial transformations) to the following:
\<close>

AOT_theorem pre_ind': \<open>[F]z & \<forall>x\<forall>y([R]xy \<rightarrow> ([F]x \<rightarrow> [F]y)) \<rightarrow> \<forall>y ([R]\<^sup>*zy \<rightarrow> [F]y)\<close>
proof(safe intro!: "\<rightarrow>I" GEN)
  fix y
  AOT_assume \<open>[F]z & \<forall>x\<forall>y([R]xy \<rightarrow> ([F]x \<rightarrow> [F]y))\<close>
  AOT_hence \<open>[F]z & Hereditary(F,R)\<close>
    by (AOT_subst_def "hered:1") (auto intro!: "&I" "cqt:2" elim: "&E")
  moreover AOT_assume \<open>[R]\<^sup>*zy\<close>
  moreover AOT_have \<open>[F]z & [R\<^sup>*]zy & Hereditary(F,R) \<rightarrow> [F]y\<close>
    using "anc-her:3". \<comment> \<open>This is an instance of the theorem cited above.\<close>
  ultimately AOT_show \<open>[F]y\<close>
    using "&I" "&E" "\<rightarrow>E" by metis
qed

text\<open>
I.e. if an object @{term z} exemplifies @{term F} and @{term F} is inherited via @{term R}, then
any object that is transitively @{term R}-related to @{term z} exemplifies @{term F}.

Pretend for a moment that @{term R} was a well-defined predecessor relation and @{term z} the number zero.
Then this theorem would imply that if (1) @{term F} holds for Zero and
(2) for any @{term x} and @{term y}, s.t. @{term x} precedes @{term y}, if @{term x} exemplifies
@{term F}, then @{term y} exemplifies @{term F}, then @{term F} holds for all numbers transitively
preceded by Zero (and since @{term F} also holds for Zero by assumption this would trivially imply that
@{term F} holds for any natural number).

In principle, this is how mathematical induction will be derived.
However, it is inconvenient that the induction step in this formulation ranges over the full domain
of all objects. Instead, it should be sufficient to consider all natural numbers.

By instantiating @{term F} to @{term \<open>\<guillemotleft>[\<lambda>x [F]x & [\<R>]\<^sup>+zx]\<guillemotright>\<close>}, we arrive at the following
theorem, which PLM refers to as @{emph \<open>Generalized Induction\<close>}
(see~\nameref{AOT:pre-ind}):@{footnote \<open>Note that (1) @{term \<open>\<guillemotleft>[\<R>]\<^sup>+zy\<guillemotright>\<close>} for any @{term y}
implies @{term \<open>\<guillemotleft>[\<R>]\<^sup>+zz\<guillemotright>\<close>}, yielding @{term \<open>\<guillemotleft>[\<lambda>x [F]x & [\<R>]\<^sup>+zx]z\<guillemotright>\<close>} in all cases in which the consequent
of the strengthened theorem does not trivially hold (i.e. if @{term \<open>\<guillemotleft>\<not>\<exists>y [\<R>]\<^sup>+zy\<guillemotright>\<close>}) and (2) that the consequent of
the weaker theorem can be strengthened since @{term \<open>\<guillemotleft>[\<R>]\<^sup>+zy\<guillemotright>\<close>} either
 implies (a) @{term \<open>z = y\<close>}, in which case @{term \<open>\<guillemotleft>[F]y\<guillemotright>\<close>} follows from the assumption @{term \<open>\<guillemotleft>[F]z\<guillemotright>\<close>},
or it implies (b) @{term \<open>\<guillemotleft>[\<R>]\<^sup>*zy\<guillemotright>\<close>}, in which case the consequent of the weaker principle yields @{term \<open>\<guillemotleft>[F]y\<guillemotright>\<close>}.
The additional fact that @{term \<open>\<guillemotleft>[\<R>]xy\<guillemotright>\<close>} and @{term \<open>\<guillemotleft>[\<R>]\<^sup>+zx\<guillemotright>\<close>} imply @{term \<open>\<guillemotleft>[\<R>]\<^sup>+zy\<guillemotright>\<close>} is sufficient to
arrive at the strengthened theorem.\<close>}

\begin{quote}
@{thm[display] "pre-ind"[of _ F z \<R>, print_as_theorem]}
\end{quote}

In this formulation, the induction step merely ranges over objects to which @{term z} bears
the weak ancestral relation of @{text \<open>\<R>\<close>}. Thinking of @{text \<open>\<R>\<close>} as the predecessor relation
and @{term z} as the number zero, this will be exactly the natural numbers. I.e. instantiating this
generalized principle of induction to the predecessor relation and the number Zero,
yields classical mathematical induction (relative to the upcoming definition of natural numbers).
\<close>

section\<open>The Predecessor Relation\<close>

subsection\<open>Definition\<close>

text\<open>
While the definition of the predecessor relation is rather straightforward, the interesting question
will be whether it actually denotes a relation, which we will discuss in detail in section~\ref{pred-denotes}. For the moment
assume that the @{text \<open>\<lambda>\<close>}-expression in the definiens of the following definition
denotes (see~\nameref{AOT:pred-thm:1}):\footnote{Note that PLM uses the symbol $\mathbb{P}$ for
the predecessor relation instead.}

\begin{quote}
@{thm[display] "pred-thm:1"}
\end{quote}

Given the assumption that this relation denotes, it follows by @{text \<open>\<beta>\<close>}-conversion that (see~\nameref{AOT:pred-thm:3}):

\begin{quote}
@{thm[display] "pred-thm:3"[of _ x y, print_as_theorem]}
\end{quote}

So an object @{term x} precedes an object @{term y} just in case there is a property @{term F}
and an ordinary object @{term u}, s.t. @{term u} exemplifies @{term F}, @{term y} numbers @{term F}
and @{term x} numbers being an @{term F} other than @{term u}  (via the definition @{thm "F-u"}).

This is a variant of Frege's definition of the successor relation.@{footnote \<open>Nodelman and
Zalta argue in favour of a predecessor relation due to the fact that in contrast to a successor relation,
the argument order of the predecessor relation matches the numerical order of objects in the relation.
Apart from that, the notions are interchangeable, i.e. @{text \<open>Succeeds(y,x)\<close>} is exactly @{term \<open>\<guillemotleft>[\<P>]xy\<guillemotright>\<close>}.\<close>}
The idea can be clarified by considering how the first natural numbers are related w.r.t. this relation:
\<^item> The number Zero numbers properties that are not exemplified by any ordinary object. Hence there
  cannot be a property @{term F} that is exemplified by an object @{term u}, s.t. Zero numbers @{term F},
  which means that Zero is not preceded by any object.
\<^item> The number One numbers properties that are exemplified by a single ordinary object.@{footnote \<open>While
  we have not formally introduced any number other than Zero, we consider this intuitive understanding helpful
  in clarifying the idea of the predecessor relation. The number One will formally be introduced later in this chapter.\<close>}
  Hence any property @{term F} numbered by One is exemplified
  by some ordinary object @{term \<open>u\<close>}. Furthermore, @{term \<open>\<guillemotleft>[F]\<^sup>-\<^sup>u\<guillemotright>\<close>}, i.e. being an object exemplifying @{term F} other than @{term u},
  is not exemplified by any ordinary object. Hence Zero is the unique predecessor of One.
\<^item> The number Two numbers properties that are exemplified by two distinct ordinary objects.
  Being an object that exemplifies any of these properties other than any particular object the given
  property exemplifies, is a property exemplified by only one ordinary object, hence numbered by One, i.e.
  One preceeds Two, etc.
\<close>


subsection\<open>Assuring that the Predecessor Relation Denotes\<close>text\<open>\label{pred-denotes}\<close>

text\<open>
It is important to realize that the @{text \<open>\<lambda>\<close>}-expression used in above definition does not
trivially denote a relation in AOT.
@{emph \<open>Numbering a property\<close>} is an encoding claim: an object numbers a property @{term G}, just in case
it encodes all properties, s.t. actually exemplifying it is equinumerous to @{term G}.
In general, encoding claims cannot be abstracted to denoting properties and relations.\footnote{Recall the
discussion in section~\ref{AvoidingParadoxes}.}

In fact it is easy to see that the minimal model of AOT does not validate this axiom: the minimal
model contains one ordinary urelement (resp. one ordinary object) and one special urelement.
Since special urelements determine the exemplification extensions of abstract objects, there being
only one special urelement implies that all abstract objects exemplify the same properties and relations.
This implies in particular that either all objects are preceded by zero or no object is, i.e.
@{term \<open>\<guillemotleft>[\<P>]0 0\<guillemotright>\<close>} or @{term \<open>\<guillemotleft>\<not>\<exists>x [\<P>]0 x\<guillemotright>\<close>}. However, we have already (informally) argued above that zero is
not preceded by any object.@{footnote \<open>Both @{thm "no-pred-0:1"[print_as_theorem]} and @{thm "prec-facts:1"[print_as_theorem]} are formally 
derived in~\nameref{AOT:no-pred-0:1}, resp.~\nameref{AOT:prec-facts:1}.\<close>} Hence in this model it would have to hold that @{term \<open>\<guillemotleft>\<not>\<exists>x [\<P>]0 x\<guillemotright>\<close>}.
However, since the minimal model still contains one ordinary object, the number One can be constructed
and (again as argued above) is preceded by Zero, i.e. @{term \<open>\<guillemotleft>[\<P>]0 1\<guillemotright>\<close>}, which yields a contradiction.

Nodelman and Zalta assert that the predecessor relation denotes by axiom and emphasize that the relation
is not inherently mathematical and no mathematical primitives are needed to assert, as an axiom, that
it denotes (see PLM~\cite{PLM-Oct-13-2021} item (782)). In particular, they argue that expressions of the form
@{term \<open>\<guillemotleft>Numbers(y,F)\<guillemotright>\<close>}, while seemingly mathematical in nature, can be eliminated, since they are @{emph \<open>defined\<close>}
in terms of primitives of AOT. Furthermore, they argue that the relation merely asserts the
existence of an ordering relation on abstract objects and ordering relations can, in general, be expressed in
entirely logical terms.

However, even if one concedes that the axiom is not inherently mathematical, it can be objected
that it is rather @{emph \<open>ad-hoc\<close>}: rather than asserting a general principle according to which
encoding claims can be abstracted to relations, it singles out a specific relation and this
relation is, after all, used to @{emph \<open>define\<close>} a concept that is very much mathematical in nature.
Furthermore, the axiom is not trivially consistent: as we have already shown minimal models of the
base system of AOT do not validate it.

Using our embedding we can, however, contribute to this situation in two ways:
  \<^item> We can show that the axiom is consistent by constructing models that validate it.
  \<^item> We can generalize the axiom to an independently justifiable comprehension principle
    for relations among abstract objects, s.t. it becomes a theorem that the predecessor
    relation in particular denotes.

We defer a more detailed discussion to section~\ref{pred} and in the following continue to
reproduce the construction of natural numbers and the derivation of the Dedekind-Peano
postulates as given by Nodelman and Zalta in PLM.
\<close>

subsection\<open>The Predecessor Relation as Rigid One-to-One Relation.\<close>

text\<open>
It can be derived that the predecessor relation is modally rigid: @{thm "pred-1-1:2"[print_as_theorem]},
respectively @{thm "pred-1-1:1"[of _ x y,print_as_theorem]}.
While the full proofs can be found in~\nameref{AOT:pred-1-1:1}, it is noteworthy that it again requires
to argue with @{emph \<open>rigidifying\<close>} relations: by the theorem governing the predecessor relation given above,
@{term \<open>\<guillemotleft>[\<P>]xy\<guillemotright>\<close>} implies that there exists a relation @{term F} and an ordinary object @{term u}, s.t.
@{term \<open>\<guillemotleft>[F]u & Numbers(y, F) & Numbers(x,[F]\<^sup>-\<^sup>u)\<guillemotright>\<close>}. However, none of the conjuncts are guaranteed to
be necessary. But we may refer to the fact that for any relation @{term F} there exists a relation @{term G}
that @{emph \<open>rigidifies\<close>} @{term F} and this relation @{term G} can serve as witness for the claim that
@{term \<open>\<guillemotleft>\<box>[\<P>]xy\<guillemotright>\<close>}.

Furthermore, it is a consequence of a modally-strict variant of Hume's principle that the predecessor
relation is one-to-one (see~\nameref{AOT:pred-1-1:3}): @{thm "pred-1-1:3"[print_as_theorem]}.

Consequently, the Predecessor Relation is a rigid one-to-one relation and we can instantiate
the definition of the @{emph \<open>strong\<close>} ancestral to @{term \<open>\<guillemotleft>\<P>\<guillemotright>\<close>} (see~\nameref{AOT:assume-anc:1}):

\begin{quote}
@{thm[display] "assume-anc:1"[print_as_theorem]}
\end{quote}

Furthermore, being @{term \<open>\<guillemotleft>\<P>\<guillemotright>\<close>}-identical as well as the @{emph \<open>weak\<close>} ancestral of @{term \<open>\<guillemotleft>\<P>\<guillemotright>\<close>} are also well-defined (see~\nameref{AOT:assume1:2}):

\begin{quote}
@{thm[display] "assume1:2"[of _ x y, print_as_theorem] "assume1:3"[print_as_theorem]}
\end{quote}

Before we continue to define natural numbers, note that it is already derivable that
the number Zero neither has a direct nor a transitive predecessor (see~\nameref{AOT:no-pred-0:1}): @{thm "no-pred-0:1"[print_as_theorem]}
respectively @{thm "no-pred-0:2"[print_as_theorem]}
\<close>

section\<open>Natural Numbers\<close>

text\<open>

Using the infrastructure introduced in the past sections, we can now follow through with the strategy
described in the beginning of the chapter and define @{emph \<open>being a natural number\<close>} as being an
object, s.t. Zero bears the weak ancestral of the predecessor relation to it (see~\nameref{AOT:nnumber:1}):

\begin{quote}
@{thm[display] "nnumber:1"}
\end{quote}

Since being a natural number trivially denotes, it follows by @{text \<beta>}-conversion that (see~\nameref{AOT:nnumber:3}):

\begin{quote}
@{thm[display] "nnumber:3"[of _ x, print_as_theorem]}
\end{quote}
\<close>

section\<open>Zero is a Natural Number\<close>

text\<open>

The first Dedekind-Peano postulate can now be derived (see~\nameref{AOT:0-n}):

\begin{quote}
@{thm[display] "0-n"[print_as_theorem]}
\end{quote}

Interestingly, both in Frege's original work and in Zalta's initial reconstruction (see~\cite{zalta1999})
the weak ancestral was defined using general identity and consequently @{term \<open>\<guillemotleft>[\<P>]\<^sup>+0 0\<guillemotright>\<close>} is a simple
consequence of the fact that zero is self-identical. However, due to the construction via rigid one-to-one relations
this theorem requires a non-trivial proof: @{term \<open>\<guillemotleft>[\<P>]\<^sup>+0 0\<guillemotright>\<close>} by definition is just the case if either
@{term \<open>\<guillemotleft>[\<P>]\<^sup>*0 0\<guillemotright>\<close>} (which was already refuted above) or @{term \<open>\<guillemotleft>0 =\<^sub>\<P> 0\<guillemotright>\<close>}.

However, @{term \<open>\<guillemotleft>0 =\<^sub>\<P> 0\<guillemotright>\<close>} is not a simple consequence of the fact that @{term \<open>\<guillemotleft>0 = 0\<guillemotright>\<close>}, but additionally
requires that @{term \<open>\<guillemotleft>InDomainOf(0,\<P>)\<guillemotright>\<close>}, respectively that @{term \<open>\<guillemotleft>\<exists>y [\<P>]0 y\<guillemotright>\<close>}, i.e. the proof
effectively requires to construct the number One as witness.@{footnote \<open>The number One can for example
be introduced as the number of any relation exemplified by exactly one ordinary object.
Since it is a theorem (see~\nameref{AOT:o-objects-exist:1}) that there is an ordinary object @{thm "o-objects-exist:1"[THEN "qml:2"[axiom_inst, THEN "\<rightarrow>E"], print_as_theorem]},
we can choose @{term a} to be a witness to this existential claim and choose @{term \<open>\<guillemotleft>#[\<lambda>x O!x & x =\<^sub>E a]\<guillemotright>\<close>} as a witness
to @{term \<open>\<guillemotleft>\<exists>y [\<P>]0 y\<guillemotright>\<close>}..\<close>}

Preliminary working versions of the chapter of PLM left this non-trivial proof
as an exercise referring to it being a trivial consequence of the self-identity of the number Zero.
Trying to prove the statement in the embedding showed that additional work is required due to the
changes in the construction compared to previous versions and we could suggest the proof given in~\nameref{AOT:0-n} 
and outlined in the footnote of the last paragraph.@{footnote \<open>Note that the chapter was under heavy revision at the time
and this omission would likely have been independently discovered eventually. However, it is one of
the merits of working in a computer-verified setting that such omissions become immediately apparent.\<close>}
\<close>

section\<open>Being a Natural Number is Rigid\<close>

text\<open>

From the generalized principle of induction when instantiating @{term F} to @{term \<open>\<guillemotleft>[\<lambda>x \<box>[\<nat>]x]\<guillemotright>\<close>}
and @{term \<R>} to @{term \<open>\<guillemotleft>\<P>\<guillemotright>\<close>}, it follows that @{thm "mod-col-num:1"[of _ x, print_as_theorem]}
and consequently that @{thm "mod-col-num:2"[print_as_theorem]} (see~\nameref{AOT:mod-col-num:1},~\nameref{AOT:mod-col-num:2}).

Since furthermore Zero is a witness to the existence of natural numbers and it is easy to prove
that @{term \<open>\<guillemotleft>[\<nat>]\<kappa> \<rightarrow> \<kappa>\<down>\<guillemotright>\<close>},@{footnote \<open>It is a simple consequence of one of the quantifier axioms mentioned
in section~\ref{AxiomSystem}.\<close>} @{emph \<open>being a natural number\<close>} is a @{emph \<open>rigid restriction condition\<close>} and
it is possible to introduce well-behaved restricted variables ranging over the natural numbers (recall section~\ref{RestrictedVariables}).

In the following the variable names @{term m}, @{term n}, @{term k}, @{term i} and @{term j}
are used to range over natural numbers.

\<close>

section\<open>Zero Has No Predecessor\<close>

text\<open>
We have already mentioned the fact that @{thm "no-pred-0:1"[print_as_theorem]} above, but we can
now restate this theorem @{emph \<open>a fortiori\<close>} for variables restricted to natural numbers, which
constitutes the second Dedkind-Peano postulate (as mentioned earlier this formulation is equivalent to
the assertion that Zero is not the successor of any natural number; see~\nameref{AOT:0-pred}):

\begin{quote}
@{thm[display] "0-pred"[print_as_theorem]}
\end{quote}
\<close>

section\<open>No Two Natural Numbers have the Same Successor\<close>

text\<open>
The third Dedekind-Peano postulate is a general property of any one-to-one relation, but can
be stated explicitly using restricted variables for natural numbers (on which @{term \<open>\<guillemotleft>\<P>\<guillemotright>\<close>}-identity
matches general identity) as follows (see~\nameref{AOT:no-same-succ}):

\begin{quote}
@{thm[display] "no-same-succ"[print_as_theorem]}
\end{quote}

Whenever two natural numbers @{text n} and @{text m} precede the same natural
number @{text k} (or, equivalently, if @{text n} and @{text m} have the same
successor), they have to be identical.
\<close>

section\<open>Mathematical Induction\<close>text\<open>\label{MathematicalInduction}\<close>

text\<open>
Futhermore, we can now derive Mathematical Induction (see~\nameref{AOT:induction}):

\begin{quote}
@{thm induction[print_as_theorem]}
\end{quote}

If a property (1) is exemplified by the number zero and (2) it being exemplified by a
natural number implies it being exemplified by its successor, then
all natural numbers exemplify that property.@{footnote \<open>Note that, strictly speaking, our natural language formulation
rather corresponds to the derived theorem @{thm induction'[print_as_theorem]} (see~\nameref{AOT:AOT_misc.induction'}),
where @{term \<open>\<guillemotleft>n\<^bold>'\<guillemotright>\<close>} is defined as @{emph \<open>the\<close>} successor of @{text n}, resp. @{emph \<open>the\<close>} natural number that is preceded by @{text n}
(see~\nameref{AOT:def-suc}). However, this formulation can only be derived after proving that every
number @{emph \<open>has\<close>} a (unique) successor.\<close>}
This is a simple consequence of instantiating generalized induction (recall section~\ref{GeneralizedInduction})
to the predecessor relation.

Thereby the fifth Dedekind-Peano postulate is derivable.
Note, however, that we haven't yet derived the fourth postulate, i.e. that
every natural number has a unique successor.
The construction so far is validated by the minimal models of AOT that are extended to validate the predecessor axiom (i.e.
in which the predecessor relation denotes).
Validating the predecessor axiom involves increasing the number of special urelements in the model (see~\ref{pred}),
but it does not require to increase the number of ordinary urelements/objects, so there are still
models with only a single ordinary urelement/object, in which the predecessor relation denotes.
However, in such models the only natural numbers are Zero and One and the number One does not have a successor.
For that reason, Nodelman and Zalta extend the system by another axiom, which we will discuss below
after stating a few more derived properties of the predecessor relation and natural numbers.
\<close>

section\<open>Properties of the Predecessor Relation and Natural Numbers\<close>

(*<*)
AOT_theorem "pred-num[ext1]": \<open>[\<P>]\<^sup>*xn \<rightarrow> [\<nat>]x\<close>
proof (rule "\<rightarrow>I")
  AOT_have \<open>[\<lambda>y \<forall>x ([\<P>]\<^sup>*x y \<rightarrow> [\<nat>]x)]n\<close>
  proof (safe intro!: "pre-ind"[unconstrain \<R>, unvarify F z \<beta>, OF "pred-thm:2", OF "zero:2", THEN "\<rightarrow>E", THEN "\<rightarrow>E", THEN "\<forall>E"(2), THEN "\<rightarrow>E"]
                      "pred-1-1:4" "Number.\<psi>"[THEN "nnumber:3"[THEN "\<equiv>E"(1)]]; safe intro!: "&I" "\<rightarrow>I" GEN "\<beta>\<leftarrow>C" "cqt:2" "zero:2")
    fix x
    AOT_assume \<open>[\<P>\<^sup>*]x 0\<close>
    AOT_thus \<open>[\<nat>]x\<close> using "existential:2[const_var]" "no-pred-0:2" "raa-cor:4" by fast
  next
    fix \<alpha> y x
    AOT_assume \<open>[\<P>]\<^sup>+0\<alpha> & [\<P>]\<^sup>+0y\<close>
    AOT_hence N\<alpha>: \<open>[\<nat>]\<alpha>\<close> using "con-dis-i-e:2:a" "intro-elim:3:b" "nnumber:3" by blast
    AOT_assume \<open>[\<lambda>y \<forall>x ([\<P>\<^sup>*]xy \<rightarrow> [\<nat>]x)]\<alpha>\<close>
    AOT_hence \<open>\<forall>x ([\<P>\<^sup>*]x\<alpha> \<rightarrow> [\<nat>]x)\<close> using "\<beta>\<rightarrow>C" by blast
    AOT_hence 0: \<open>[\<P>\<^sup>*]x\<alpha> \<rightarrow> [\<nat>]x\<close> using "\<forall>E"(2) by blast
    AOT_assume \<open>[\<P>]\<alpha>y\<close>
    moreover AOT_assume \<open>[\<P>\<^sup>*]xy\<close>
    ultimately AOT_have \<open>[\<P>]\<^sup>+x \<alpha>\<close>
      using "1-1-R:1"[unconstrain \<R>, unvarify \<beta>, THEN "\<rightarrow>E", OF "pred-thm:2", OF "pred-1-1:4", THEN "\<rightarrow>E", OF "&I"] by blast
    AOT_hence \<open>[\<P>]\<^sup>*x \<alpha> \<or> x =\<^sub>\<P> \<alpha>\<close>
      by (metis "assume1:5" "intro-elim:3:a")
    moreover {
      AOT_assume \<open>x =\<^sub>\<P> \<alpha>\<close>
      AOT_hence \<open>\<exists>z ([\<P>]xz & [\<P>]\<alpha>z)\<close> using "assume1:2"[THEN "\<equiv>E"(1)] by blast
      then AOT_obtain z where \<open>[\<P>]xz & [\<P>]\<alpha>z\<close> using "\<exists>E"[rotated] by blast
      AOT_hence \<open>x = \<alpha>\<close>
        using "pred-1-1:3"[THEN "df-1-1:1"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(2)] "\<forall>E"(2) "\<rightarrow>E" by blast
      AOT_hence \<open>[\<nat>]x\<close> using N\<alpha> "rule=E" id_sym by blast
    }
    moreover {
      AOT_assume \<open>[\<P>]\<^sup>*x \<alpha>\<close>
      AOT_hence \<open>[\<nat>]x\<close> using 0 "\<rightarrow>E" by blast
    }
    ultimately AOT_show \<open>[\<nat>]x\<close> by (metis "con-dis-i-e:4:c" "raa-cor:1")
  qed
  AOT_hence \<open>\<forall>x ([\<P>]\<^sup>*x n \<rightarrow> [\<nat>]x)\<close> using "\<beta>\<rightarrow>C" by blast
  moreover AOT_assume \<open>[\<P>]\<^sup>*xn\<close>
  ultimately AOT_show \<open>[\<nat>]x\<close> using "\<forall>E"(2) "\<rightarrow>E" by blast
qed
AOT_theorem "pred-num[ext2]": \<open>[\<P>]\<^sup>+xn \<rightarrow> [\<nat>]x\<close>
proof (rule "\<rightarrow>I")
  AOT_assume \<open>[\<P>]\<^sup>+xn\<close>
  AOT_hence \<open>[\<P>]\<^sup>*xn \<or> x =\<^sub>\<P> n\<close> by (metis "assume1:5" "intro-elim:3:a")
  moreover {
    AOT_assume \<open>[\<P>]\<^sup>*xn\<close>
    AOT_hence \<open>[\<nat>]x\<close> using "pred-num[ext1]"[THEN "\<rightarrow>E"] by blast
  }
  moreover {
    AOT_assume \<open>x =\<^sub>\<P> n\<close>
    AOT_hence \<open>x = n\<close>
      using "id-R-thm:3"[unconstrain \<R>, unvarify \<beta>, THEN "\<rightarrow>E", OF "pred-thm:2", OF "pred-1-1:4", THEN "\<rightarrow>E"]
      by blast
    AOT_hence \<open>[\<nat>]x\<close> by (metis "rule=E" Number.restricted_var_condition id_sym)
  }
  ultimately AOT_show \<open>[\<nat>]x\<close> by (metis "con-dis-i-e:4:c" "raa-cor:1")
qed

(*>*)

text\<open>
Successors of natural numbers are (transitively) natural numbers (see~\nameref{AOT:suc-num:1}):

\begin{quote}
@{thm[display] "suc-num:1"[of _ n x, print_as_theorem]
               "suc-num:2"[of _ n x, print_as_theorem]
               "suc-num:3"[of _ n x, print_as_theorem]}
\end{quote}

Predecessors of natural numbers are (transivitely) natural numbers (see~\nameref{AOT:pred-num}):

\begin{quote}
@{thm[display] "pred-num"[of _ x n, print_as_theorem]
               "pred-num[ext1]"[of _ x n, print_as_theorem]
               "pred-num[ext2]"[of _ x n, print_as_theorem]}
\end{quote}

Natural numbers are natural cardinals (see~\nameref{AOT:nat-card}):

\begin{quote}
@{thm[display] "nat-card"[of _ x, print_as_theorem]}
\end{quote}

The predecessor relation is functional (see~\nameref{AOT:pred-func:1}):

\begin{quote}
@{thm[display] "pred-func:1"[of _ x y z, print_as_theorem]
               "pred-func:2"[of _ n m k, print_as_theorem]}
\end{quote}
\<close>

section\<open>Possible Richness of Objects\<close>text\<open>\label{ModalAxiom}\<close>

text\<open>
As mentioned above, the construction so far is valid in models with only a single ordinary 
object and consequently with only two natural numbers, which is not sufficient to
derive that every natural number has a successor.

The following modal axiom, by which Nodelman and Zalta proceed to extend the system, changes this (see~\nameref{AOT:modal-axiom}):

\begin{quote}
@{thm[display] "modal-axiom"[axiom_inst, of _ G, print_as_theorem]}
\end{quote}

If there is a natural number which numbers @{term G}, then there might have been a concrete object
@{term y} which is distinct from every ordinary object that @{emph \<open>actually\<close>} exemplifies @{term G}.
We will explain in detail how we extend our models to be able to validate this axiom in section~\ref{modell-modal-axiom}.
In summary, the axiom requires extending the domain of ordinary urelements/objects to an at least
countably infinite set.

This axiom requires some justification, especially given the claim that the construction is
@{emph \<open>purely logical\<close>} and does not require to presuppose any intrinsically mathematical claims.

Traditionally, a system is no longer considered to be @{emph \<open>purely logical\<close>}, if it asserts the existence
of more than one object.@{footnote \<open>E.g. PLM cites Boolos~\cite{BoolosFrege}:
\blockquote{In logic, we ban the empty domain as a concession to technical convenience but draw the line there: We
firmly believe that the existence of even two objects, let alone infinitely many, cannot be guaranteed by
logic alone.}\<close>} While Nodelman and Zalta agree with this principle, they argue (see PLM~\cite{PLM-Oct-13-2021} item (799)) that
it only extends to @{emph \<open>concrete\<close>} objects.
While above axiom does imply that the domain of @{emph \<open>ordinary\<close>} objects (recall that @{emph \<open>being ordinary\<close>}
is defined as @{emph \<open>being @{emph \<open>possibly\<close>} concrete\<close>}) is at least countably infinite, it does not imply
that there is even a single object that is @{emph \<open>actually concrete\<close>}.
Nodelman and Zalta further argue that on the one hand it is in fact common for logical systems to assert the existence
of more than one @{emph \<open>abstract\<close>} object, for example that there are two distinct truth values, the
True and the False,@{footnote \<open>In particular, they refer to Frege's logic.\<close>} and that on the other hand logicians traditionally
work under the assumption that @{emph \<open>the domain of objects @{emph \<open>might\<close>} be of any size\<close>}, which
they take as a modal claim: while logic may not presuppose that the domain of concrete object
has any particular size, it allows for the @{emph \<open>possiblity\<close>} of the domain being of any size, i.e.
it is valid for a logic to presuppose that there @{emph \<open>may possibly\<close>} be more than one object, as
long as that does not imply that there is @{emph \<open>actually\<close>} more than one (concrete) object.

Independently of the question whether this axiom may or may not be considered as @{emph \<open>purely logical\<close>},
towards which we refrain from presuming to pass judgement either way, we certainly agree that it captures a pretheoretic
intuition: it can be considered as a prerequisite of talking about natural numbers to be able to imagine that
no matter how many objects we currently consider that there @{emph \<open>possibly might have been\<close>} yet another object,
even though for doing so we do not need to be able to point to this object in the actual world (i.e. it may not be concrete, but
merely @{emph \<open>possibly concrete\<close>}).

While this may serve as justification for the axiom, Frege's original construction does
not rely on a similar assumption, but can use the number of the property @{emph \<open>being smaller
or equal to @{term n}\<close>}, @{text \<open>#[\<lambda>x x \<le> n]\<close>}, as witness for a successor of any
natural number @{term n}. In the presented construction that relies on equinumerosity among
the ordinary objects, this is not an option: since natural numbers are abstract, being a natural number
smaller or equal to @{text n} is only exemplified by abstract objects and therefore unexemplified by ordinary objects.
Thus @{text \<open>#[\<lambda>x x \<le> n]\<close>} is Zero and, in particular, cannot serve as the successor of any number.

However, we will discuss two variants of the construction in section~\ref{NewNumberTheory}
in which @{emph \<open>discernible\<close>} abstract objects @{emph \<open>can\<close>} be counted (and in which natural
numbers, in particular, will be discernible). This allows for the construction of a
successor of @{text n} as @{text \<open>#[\<lambda>x x \<le> n]\<close>}, thereby eliminating the need for this axiom.
\<close>

section\<open>Every Number has a Unique Successor\<close>
text\<open>
The axiom above is sufficient to derive the last Dedekind-Peano postulate, i.e. that every
natural number has a unique successor (see~\nameref{AOT:th-succ}):
\begin{quote}
@{thm[display] "th-succ"[print_as_theorem]}
\end{quote}

Every natural number @{text n} is a natural cardinal and, by definition (see~\nameref{AOT:card}), natural cardinals
are the number of some property and thus @{thm card[THEN "\<equiv>Df", THEN "conventions:3"[THEN "\<equiv>\<^sub>d\<^sub>fE"], THEN "&E"(1), print_as_theorem, of n]}.

Let @{term G} be a property such that @{term \<open>print_term \<guillemotleft>n = #G\<guillemotright>\<close>}.

Now the axiom implies that there is an ordinary object @{term v}, s.t. @{term G} does not actually exemplify @{term v}. This
requires an appeal to the Barcan formulas (in particular~\nameref{AOT:BFs:3}) and relies
on the additional fact (see~\nameref{AOT:modal-lemma}) that:

\begin{quote}
 @{thm[display] "modal-lemma"[print_as_theorem, of G v]}
\end{quote}

Hence, since @{term \<open>print_term \<guillemotleft>n = #G\<guillemotright>\<close>} implies that @{text n} numbers @{term \<open>\<guillemotleft>[\<lambda>x \<^bold>\<A>[G]x]\<guillemotright>\<close>} (see~\nameref{AOT:eq-num:2}),
the object that numbers @{term \<open>\<guillemotleft>[\<lambda>x \<^bold>\<A>[G]x \<or> x =\<^sub>E v]\<guillemotright>\<close>} can be used as witness for a successor of @{text n}.

Uniqueness follows from the fact that the predecessor relation is functional.

Hence it is possible to define @{emph \<open>the\<close>} successor @{term \<open>\<guillemotleft>n\<^bold>'\<guillemotright>\<close>} of a natural number as
@{emph \<open>the\<close>} natural number that is preceded by m:
\begin{quote}
@{thm[display] "def-suc"[rename_abs _ _ x]}
\end{quote}

Numerals can be defined as iterative successors, e.g. @{thm "numerals:1"}.

While PLM continues to derive further theorems of Number Theory, defines mathematical
functions and operations, including recursively defined functions such as addition, and proceeds to
derive Second-Order Dedekind-Peano arithmetic, we will conclude our discussion of the topic here
and instead discuss in more detail how we modelled the two required additional axioms.
\<close>

section\<open>The Predecessor Axiom in Detail\<close>text\<open>\label{pred}\<close>

text\<open>
Recall that the predecessor axiom of PLM is stated as follows (see~\nameref{AOT:pred}):

\begin{quote}
@{thm[display] pred[print_as_theorem]}
\end{quote}

In section~\ref{pred-denotes} we have already established that the relation in question
distinguishes certain abstract objects that number properties and that this relation
does @{emph \<open>not\<close>} denote in the minimal models of the base system of AOT. We also have already
discussed that there cannot be a relation in AOT that generally distinguishes between arbitrary abstract
objects (in particular @{term \<open>\<guillemotleft>[\<lambda>xy x = y]\<guillemotright>\<close>} does not denote; see~\ref{IndistinguishableAbstractObjects}). So we need to determine
what is special about the abstract objects that are distinguished by the predecessor relation
and allows us to construct models for it.

To that end, we first show that the predecessor relation coexists with @{emph \<open>numbering a property\<close>}.
In particular we can prove the following (see~\nameref{AOT:AOT_NaturalNumbers.pred_coex}):

\begin{quote}
@{thm[display] pred_coex[print_as_theorem]}
\end{quote}

So to validate the predecessor axiom, we can equivalently
construct models in which @{thm numbers_prop_den[of _ F, print_as_theorem]} is
a theorem.
Recall that @{emph \<open>numbering a property\<close>} is equivalent to the following (see~\nameref{AOT:numbers[den]}):

\begin{quote}
@{thm[display] "numbers[den]"[THEN "\<rightarrow>E", OF "cqt:2[const_var]"[axiom_inst], of _ x G, print_as_theorem]}
\end{quote}

So while @{emph \<open>numbering a property\<close>} is a condition on the properties an abstract object encodes,
it requires the abstract object to encode an entire class of properties, namely all properties, s.t.
@{emph \<open>actually\<close>} exemplifying them is equinumerous@{text \<open>\<^sub>E\<close>} to the numbered property. Further recall that
being @{emph \<open>equinumerous@{text \<open>\<^sub>E\<close>}\<close>}, informally speaking, means to be exemplified by the same amount of
@{emph \<open>ordinary\<close>} objects.

This is the crucial fact that allows us to construct suitable models: while we need to distinguish
between abstract objects based on the properties they @{emph \<open>encode\<close>}, the condition under which these
abstract objects encode or do not encode properties solely depends on the exemplification patterns of 
those properties on the @{emph \<open>ordinary\<close>} objects.

In our models, two abstract objects are exemplification-distinguishable, if they are mapped to distinct
@{emph \<open>special urelements\<close>}. If we wanted to be able to distinguish between abstract objects
in general based on the exemplification patterns of the properties they encode, this would mean that
there had to be a distinct @{emph \<open>special urelements\<close>} for any set of such patterns. Exemplification patterns
are functions from @{emph \<open>urelements\<close>} (including special urelements) to modal
truth conditions (i.e. functions from semantic possible worlds to booleans).

Therefore, if we wanted to assign distinct special urelements based on @{emph \<open>general\<close>} exemplification
patterns, we would need an injective function from exemplification patterns (i.e. sets of functions
acting on urelements) to special urelements, which would be in violation of Cantor's theorem.

However, fortunately, we only need to distinguish between exemplification patterns on @{emph \<open>ordinary\<close>}
objects. Since the domains of special urelements and ordinary urelements are independent, it is
consistently possible to construct special urelements in such a way that there can be
an injective function mapping distinct sets of functions @{emph \<open>acting on ordinary urelements alone\<close>}
to distinct special urelements.

In our general models we choose an @{emph \<open>abstract\<close>} type @{typ \<sigma>} as type of special urelements.@{footnote \<open>I.e.
we allow any non-empty domain for @{typ \<sigma>} in models of the meta-logic without restriction.\<close>}
In our extended models that validate the predecessor axiom, we instead @{emph \<open>define\<close>} the
type @{typ \<sigma>} using the set of objects of type @{typ \<open>(\<omega> \<Rightarrow> w \<Rightarrow> bool) set \<times> (\<omega> \<Rightarrow> w \<Rightarrow> bool) set \<times> \<sigma>'\<close>}
as representation set.

Recall that the type @{typ \<omega>} is the type of ordinary urelements and @{typ w} is the type of
semantic possible worlds. @{typ \<sigma>'} is an additional abstract type of @{emph \<open>very special urelements\<close>}
that will retain the model's ability to distinguish between abstract objects beyond those that
differ in exemplification patterns on the ordinary objects.
So in these models, special urelements are tuples of two sets of property extensions on
ordinary objects and a very special urelement. We refer to the first set of extensions as the
@{emph \<open>intersection set of ordinary property extensions\<close>} and to the second copy as the
@{emph \<open>union set of ordinary property extensions\<close>}.

When we map an abstract object @{term a} to this new type of special urelements,
we insert a property extension on the ordinary objects into the intersection set, just in case 
@{term a} encodes @{emph \<open>all\<close>} properties with this extension on the ordinary objects.
And we insert an extension into the union set, just in case that there @{emph \<open>exists\<close>}
a property with that extension (on the ordinary objects) that is encoded by @{term a}.

We use this construction as witness for a specification of the mapping @{term \<open>\<alpha>\<sigma>'\<close>}, which will then be
extended to a surjective mapping @{term \<alpha>\<sigma>} as explained in section~\ref{ExtendedAczelModelStructure}.

This construction @{emph \<open>forces\<close>} two abstract objects to be assigned different special urelements,
in case either (1) one of them encodes a property with a given extension on the ordinary object, while the other doesn't
encode any such property, or (2) one of them encodes all properties with a given extension on the ordinary object,
while the other fails to encode at least one such property.

Furthermore, the construction still @{emph \<open>allows\<close>} two abstract objects to be assigned different special urelements,
in case they differ only in encoding properties with the same extension on the ordinary objects (by assigning them
distinct @{emph \<open>very special\<close>} urelements).

This extended model validates the following two axioms
(see~\nameref{AOT:AOT_Axioms.AOT_ExtendedModel.indistinguishable_ord_enc_all},~\nameref{AOT:AOT_Axioms.AOT_ExtendedModel.indistinguishable_ord_enc_ex}):

  \<^item> @{thm indistinguishable_ord_enc_all[rename_abs F G u G u, of \<Pi> x y, axiom_inst, print_as_theorem]}
  \<^item> @{thm indistinguishable_ord_enc_ex[rename_abs F G u G u, of \<Pi> x y, axiom_inst, print_as_theorem]}

I.e. if two abstract objects are (exemplification-)indistinguishable, then they
(1) co-encode all properties that are necessarily equivalent on the ordinary objects to any given denoting
property term @{term \<Pi>} and (2) if either one encodes any property that is necessarily equivalent to
@{term \<Pi>} on the ordinary objects, there is also such a property that is encoded by the other.

While this formulation of the axioms is rather complex and not particularly intuitive, we can equivalently
(given the necessary and sufficient conditions for relation terms to denote described in section~\ref{KirchnersTheorem}) state them as follows
(see~\nameref{AOT:AOT_ExtendedRelationComprehension.denotes_ex},~\nameref{AOT:AOT_ExtendedRelationComprehension.denotes_ex_neg}):

\begin{quote}
@{thm[display] denotes_ex[of _ F, print_as_theorem] denotes_ex_neg[of _ F, print_as_theorem]}
\end{quote}

I.e. (1) @{emph \<open>encoding a property that is necessarily equivalent on the ordinary objects to a
given property @{term F}\<close>} denotes a property and (2) @{emph \<open>not encoding a property that is necessarily
equivalent on the ordinary objects to a given property @{term F}\<close>} denotes a property.@{footnote \<open>Note that these
properties coexist with their negations, i.e. @{thm denotes_all_neg[of _ F, print_as_theorem]} is equivalent
to the first, @{thm denotes_all[of _ F, print_as_theorem]} is equivalent to the second.\<close>}

The following comprehension principles are derivable from the fact that above properties
denote (see~\nameref{AOT:AOT_ExtendedRelationComprehension.Comprehension_1},~\nameref{AOT:AOT_ExtendedRelationComprehension.Comprehension_2}):

\begin{quote}
@{thm[display] Comprehension_1[of _ \<phi>, print_as_theorem] Comprehension_2[of _ \<phi>, print_as_theorem]}
\end{quote}

We call @{term \<phi>} a @{emph \<open>condition on extensions on ordinary objects\<close>}, just in case that
@{term \<open>print_as_theorem \<guillemotleft>\<box>\<forall>F\<forall>G(\<box>G \<equiv>\<^sub>E F \<rightarrow> (\<phi>{F} \<equiv> \<phi>{G}))\<guillemotright>\<close>}.
Then the comprehension principles state that for any condition @{term \<phi>} on extensions on ordinary objects,
both @{emph \<open>encoding a property that satisfies @{term \<phi>}\<close>} and
@{emph \<open>not encoding a property that satisfies @{term \<phi>}\<close>} denote properties.@{footnote \<open>See
also~\nameref{AOT:AOT_ExtendedRelationComprehension.Comprehension_1'} and~\nameref{AOT:AOT_ExtendedRelationComprehension.Comprehension_2'} for derived
variants of these principles.\<close>}

In combination these two principles yield the following (see~\nameref{AOT:AOT_ExtendedRelationComprehension.Comprehension_3}):@{footnote \<open>However, note that above
principles are stronger, i.e. they are @{emph \<open>not\<close>} derivable from the combined principle.\<close>}
\begin{quote}
@{thm[display] Comprehension_3[of _ \<phi>, print_as_theorem]}
\end{quote}

I.e. for every condition @{term \<open>\<phi>\<close>} on extensions on ordinary objects,
@{emph \<open>encoding exactly those properties that satisfy @{term \<open>\<phi>\<close>}\<close>} denotes a property.

It is easy to show that @{emph \<open>being an @{term F}, s.t. actually exemplifying @{term F} is equinumerous
to @{term G}\<close>}, is a condition on extensions on ordinary objects. Hence it is a consequence of
this last comprehension principle that @{term \<open>\<guillemotleft>[\<lambda>x \<forall>F (x[F] \<equiv> [\<lambda>z \<^bold>\<A>[F]z] \<approx>\<^sub>E G)]\<down>\<guillemotright>\<close>} and
thereby @{emph \<open>numbering a property\<close>} denotes by coexistence (see~\nameref{AOT:AOT_NaturalNumbers.numbers_prop_den}).

\<close>

subsubsection\<open>Justification of the Comprehension Principles\<close>text\<open>\label{JustificationExtendedComprehension}\<close>

text\<open>
While the predecessor axiom singles out a particular relation
among abstract objects for the sole purpose of defining a mathematical relation, the comprehension principles we
suggest provide a general means to construct relations among abstract objects based on specific encoding
patterns in a manner that is provably consistent, but also independently justifiable.

In general, the burden of justification rather lies in the fact that some abstract objects @{emph \<open>are\<close>}
exemplification-indistinguishable: let @{term R\<^sub>t} be the relation @{emph \<open>thinking about\<close>}, s.t. 
@{term \<open>\<guillemotleft>[R\<^sub>t]xy\<guillemotright>\<close>} can be read as @{term x} is thinking about @{term y}. Then for two distinct abstract
objects @{term a} and @{term b} to be exemplification-indistinguishable implies that it is impossible
for anyone to think about one without thinking about the other: @{term \<open>\<guillemotleft>\<forall>x \<box>([R\<^sub>t]xa \<equiv> [R\<^sub>t]xb)\<guillemotright>\<close>}, resp.
@{term \<open>\<guillemotleft>\<not>\<diamond>\<exists>x ([R\<^sub>t]xa & \<not>[R\<^sub>t]xb \<or> [R\<^sub>t]xb & \<not>[R\<^sub>t]xa)\<guillemotright>\<close>}.

While the existence of such objects is justifiable, it is not necessarily a pre-theoretic intuition.
Interestingly, it is not possible to @{emph \<open>independently\<close>} construct two abstract objects that
are in fact exemplification-indistinguishable: while it is provable that there @{emph \<open>exist\<close>} such
pairs of objects, the construction always has to rely on constructing one of the objects particularly
in such a way that it cannot be distinguished from the other.@{footnote \<open>And even this is only possible
for specific choices of a first abstract object: For example, we cannot construct an abstract object that
is indistinguishable from the null-object (that encodes no properties) since we can always conceive of a
model that maps the null-object to a designated special urelement that no other abstract object maps to.\<close>}
Whenever two abstract objects are constructed independently, a model can generally choose two distinct
special urelements for them, thereby making them distinguishable. Only if the construction of the
second abstract object @{emph \<open>depends\<close>} on the choice of a special urelement for the first and forces
both objects to be collapsed under the mapping from abstract objects to special urelements,
this becomes infeasible.

This helps in consolidating the fact that there are indistinguishable abstract objects with pre-theoretic
intuition: given two independent abstract objects, we can always find ourselves thinking about one, but
not the other. However, we can conceive of concepts that e.g. themselves involve @{emph \<open>being indistinguishable from other
abstract objects\<close>}, for which a clever construction in fact yields distinct concepts that are indistinguishable.@{footnote \<open>Recall
the discussion in section~\ref{IndistinguishableAbstractObjects}.\<close>}

So while we can always consistently distinguish between @{emph \<open>particular, independent\<close>} abstract objects,
given that there still @{emph \<open>are\<close>} indistinguishable abstract objects, we cannot formulate
a completely general principle that allows for distinguishing @{emph \<open>arbitrary\<close>} abstract objects.

However, our suggested comprehension principles are restricted to abstract objects that have encoding
conditions that differ in exemplification patterns on the @{emph \<open>ordinary\<close>} objects.
If for two abstract objects we can point to a pattern among the ordinary objects,
s.t. one of the object involves this pattern (i.e. it encodes a property that satisfies
this pattern), but the other one doesn't involve this pattern at all (i.e. it encodes no
property that satisfies this pattern), we have a concrete criterion for telling
the objects apart. The same can be said, if one of the object fails to fully encode such a pattern
(i.e. there is a property with this pattern on the ordinary objects that it doesn't encode),
while the other encodes all properties with this pattern.

The third, combined principle (which is weaker than the first two principles, but strong enough
for @{emph \<open>numbering a property\<close>} to denote) is seemingly even easier to justify: if an abstract object
encodes @{emph \<open>exactly\<close>} those properties that satisfy a given pattern on the ordinary objects, then it is fully determined
by this pattern, so in this sense we can @{emph \<open>identify\<close>} such abstract objects with the
respective patterns on the ordinary objects they encode.

Assuming that there are distinct patterns
among the ordinary objects that are indistinguishable seems hardly justifiable. However, this
relies on a particular understanding of what it means to encode patterns among the
ordinary objects that may not be completely intuitive, as conceded in the next section.

However, our construction already shows that it is not necessary to justify the predecessor relation directly
as a denoting relation: We can generalize the issue to the question of when abstract objects can
be assured to be exemplification-distinguishable. In this more general question we no longer see any ties to
Mathematics whatsoever, but rather a metaphysical discussion of the nature of abstract objects and
relations among them.
\<close>

subsubsection\<open>Caveats of the Comprehension Principles\<close>

(*<*)
AOT_register_variable_names
  Relation: T
(*>*)

text\<open>

While the comprehension principles suggested above have some justification and allow for deriving
that useful encoding conditions such as @{emph \<open>numbering a property\<close>} can be abstracted to properties,
they are not the only conceivable way of generically extending AOT with relations among abstract objects.

In particular, it does @{emph \<open>not\<close>} follow from the suggested principles that any of the
following properties denote:

  \<^item> @{term \<open>\<guillemotleft>[\<lambda>x \<forall>F (x[F] \<rightarrow> \<box>\<forall>z ([F]z \<rightarrow> O!z))]\<guillemotright>\<close>}, i.e. @{emph \<open>encoding only properties that
     are necessarily restricted to ordinary objects.\<close>}
  \<^item> @{term \<open>print_term \<guillemotleft>[\<lambda>x (x[\<lambda>z O!z & \<phi>{z}])]\<guillemotright>\<close>}, i.e. encoding a particular pattern among the
    ordinary objects.
  \<^item> @{term \<open>\<guillemotleft>[\<lambda>x ExtensionOf(x, [\<lambda>z O!z & [G]z])]\<guillemotright>\<close>} where @{term \<open>\<guillemotleft>ExtensionOf(x,[G])\<guillemotright>\<close>} is defined
    by PLM as @{thm "exten-property:1"[of x G]} (see~\nameref{AOT:exten-property:1}).

The notion of an @{emph \<open>extension on the ordinary objects\<close>} we used above would have to be defined as (see~\nameref{AOT:AOT_misc.OrdinaryExtensionOf}):

\begin{center}
@{thm[display] OrdinaryExtensionOf[of x G]}
\end{center}

With this definition, @{thm BeingOrdinaryExtensionOfDenotes[print_as_theorem, of G]} is derivable from the suggested
principles (see~\nameref{AOT:AOT_misc.BeingOrdinaryExtensionOfDenotes}).
However, using this conception of extensions on ordinary objects as the basis for
our comprehension principles, has some potentially counter-intuitive implications:

If one abstract objects encodes exactly the property @{emph \<open>being
an ordinary table\<close>}, and another abstract object encodes exactly @{emph \<open>being an ordinary table or
being abstract\<close>}, our comprehension principles are not sufficient for telling them
apart. Both objects involve the same pattern among the ordinary objects, but neither encodes
it fully, since, for instance, neither encodes @{emph \<open>being an ordinary table or being
a natural number\<close>}, which also has the same exemplification pattern among the ordinary objects.

The third, combined principle alone cannot even distinguish between an object that
encodes exactly @{emph \<open>being an ordinary table\<close>} and an object that encodes
exactly @{emph \<open>being a mathematician\<close>} - neither of these objects are @{emph \<open>fully
determined by a pattern on the ordinary objects\<close>} in the sense of our principles, since
neither encodes @{emph \<open>all\<close>} properties with this pattern.@{footnote \<open>However, they
become distinguishable on the bases of the first principle above, since we can find
a pattern among ordinary objects one of the abstract objects encodes, while the other
one doesn't (assuming mathematicians aren't tables).\<close>}
\<close>

subsubsection\<open>Relation to Leibnizian Concepts and Platonic Forms\<close>
text\<open>
Despite the concessions above, our comprehension principles align well with the analysis of other
philosophical objects in AOT.
PLM defines for an abstract object to be the Leibnizian Concept of a property as follows (see~\nameref{AOT:concept-of-G}):@{footnote \<open>@{emph \<open>Being a concept\<close>} @{term \<open>\<guillemotleft>C!\<guillemotright>\<close>} is
defined as @{thm concepts}.\<close>}

\begin{quote}
  @{thm "concept-of-G"[of x G]}
\end{quote}

An object @{text x} is a concept of @{term G}, just in case it encodes exactly those properties
that are necessarily implied by @{term G}, using the following definition of necessary implications
between properties (see~\nameref{AOT:F-imp-G}):

\begin{quote}
  @{thm "F-imp-G"[of F G]}
\end{quote}

Now our comprehension principles make it derivable that @{emph \<open>being a concept of @{term H}\<close>}
is a property, if @{term H} necessarily implies @{emph \<open>being ordinary\<close>} (see~\nameref{AOT:AOT_misc.ConceptOfOrdinaryProperty}):

\begin{quote}
@{thm ConceptOfOrdinaryProperty[print_as_theorem, of H]}
\end{quote}

So concepts of properties that do not involve abstract objects can always be distinguished
from other abstract objects.

Reusing the example above, the concept of @{emph \<open>being an ordinary table\<close>}
@{emph \<open>does\<close>} encode @{emph \<open>being an ordinary table or being abstract\<close>},
since the former necessarily implies the latter. In fact it encodes all
properties that are necessarily equivalent on the ordinary objects to @{emph \<open>being an ordinary table\<close>},
since all those properties are necessarily implied by @{emph \<open>being an ordinary table\<close>}.

Consequently, concepts of properties that necessarily imply being ordinary and possibly differ on
some ordinary object become provably distinguishable.
In particular, it becomes a @{emph \<open>theorem\<close>} that the concept of @{emph \<open>being an ordinary table\<close>} is discernible
from the concept of @{emph \<open>being a mathematician\<close>} (assuming that these properties are not necessarily exemplified by the same objects).

Further examples of theorems that can be derived from our comprehension principles are (see~\nameref{AOT:AOT_misc.concept_inclusion_denotes_1}
and~\nameref{AOT:AOT_misc.concept_inclusion_denotes_2}):

\begin{quote}
@{thm[display] concept_inclusion_denotes_1[print_as_theorem, of H]}
@{thm[display] concept_inclusion_denotes_2[print_as_theorem, of H]}
\end{quote}

I.e. both @{emph \<open>including\<close>} and @{emph \<open>being included by\<close>} the concept of a
property @{term H} denote, given that @{term H} necessarily implies being ordinary.@{footnote \<open>The definitions
of @{term \<open>\<guillemotleft>\<^bold>c\<^sub>G\<guillemotright>\<close>} (see~\nameref{AOT:concept-G}) and @{text \<open>\<preceq>\<close>} (see~\nameref{AOT:con:1}) can be found in appendix~\ref{AOT:AOT_misc}, which implements fragments
of the theory of concepts given in PLM chapter~13.\<close>}

Thick platonic forms are defined similarly to Leibnizian concepts of properties (see~\nameref{AOT:tform-of}):

\begin{quote}
@{thm[display] "tform-of"[of x G]}
\end{quote}

So we can also derive that @{emph \<open>being the (thick) platonic form of H\<close>} denotes a property,
if @{term H} necessarily implies @{emph \<open>being ordinary\<close>} (see~\nameref{AOT:AOT_misc.FormOfOrdinaryProperty}):

\begin{quote}
@{thm[display] FormOfOrdinaryProperty[print_as_theorem, of H]}
\end{quote}

This shows that our comprehension principles are by no means @{emph \<open>ad hoc\<close>} and
have relevant implications for philosophical objects beyond the natural numbers.
A detailed study of the implications of these principles will be an interesting
topic for future research.

However, given the prospect of a move from abstracting patterns among @{emph \<open>ordinary\<close>} objects
to abstracting patterns among @{emph \<open>discernible\<close>} objects instead,
an even more interesting question may be whether similar general comprehension principles
can be formulated for distinguishing objects that encode different patterns among @{emph \<open>discernible\<close>} objects.
We will discuss this further in section~\ref{NewNumberTheory}.
\<close>

(*<*)
(* TODO: think about stating the full proof *)
AOT_theorem
  \<comment> \<open>We assume that for any property term @{text \<open>\<Pi>\<close>} it is a modally-strict theorem\<close>
  \<comment> \<open>that numbering @{text \<open>\<Pi>\<close>} denotes a property\<close>
  assumes \<open>for arbitrary \<Pi>: \<^bold>\<turnstile>\<^sub>\<box> [\<lambda>z Numbers(z,\<Pi>)]\<down>\<close>
  shows \<open>[\<lambda>xy \<exists>F \<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))]\<down>\<close>
\<comment> \<open>Proof using the safe extension axiom.\<close>
proof(rule "safe-ext[2]"[axiom_inst, THEN "\<rightarrow>E", OF "&I"])
  \<comment> \<open>The following relation denotes axiomatically:\<close>
  AOT_show \<open>[\<lambda>xy \<exists>F \<exists>u ([F]u & [\<lambda>z Numbers(z,F)]y & [\<lambda>z Numbers(z,[F]\<^sup>-\<^sup>u)]x)]\<down>\<close>
    by "cqt:2"
next
  \<comment> \<open>It remains to show that the matrix of the relation above is necessarily universally\<close>
  \<comment> \<open>equivalent to the matrix of the predecessor relation:\<close>
  AOT_show \<open>\<box>\<forall>x \<forall>y (\<exists>F \<exists>u ([F]u & [\<lambda>z Numbers(z,F)]y & [\<lambda>z Numbers(z,[F]\<^sup>-\<^sup>u)]x) \<equiv>
                     \<exists>F \<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u)))\<close>
  proof(safe intro!: RN GEN "\<equiv>I" "\<rightarrow>I")
    AOT_modally_strict {
      fix x y
      AOT_assume \<open>\<exists>F \<exists>u ([F]u & [\<lambda>z Numbers(z,F)]y & [\<lambda>z Numbers(z,[F]\<^sup>-\<^sup>u)]x)\<close>
      then AOT_obtain F where \<open>\<exists>u ([F]u & [\<lambda>z Numbers(z,F)]y & [\<lambda>z Numbers(z,[F]\<^sup>-\<^sup>u)]x)\<close>
        using "\<exists>E"[rotated] by blast
      then AOT_obtain u where \<open>[F]u & [\<lambda>z Numbers(z,F)]y & [\<lambda>z Numbers(z,[F]\<^sup>-\<^sup>u)]x\<close>
        using "Ordinary.\<exists>E"[rotated] by meson
      AOT_hence \<open>[F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u)\<close>
        by (metis "\<beta>\<rightarrow>C"(1) "&I" "&E")
      AOT_hence \<open>\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
        by (rule "Ordinary.\<exists>I")
      AOT_thus \<open>\<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
        by (rule "\<exists>I")
    }
  next
    AOT_modally_strict {
      fix x y
      AOT_assume \<open>\<exists>F\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
      then AOT_obtain F where \<open>\<exists>u ([F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u))\<close>
        using "\<exists>E"[rotated] by blast
      then AOT_obtain u where \<open>[F]u & Numbers(y,F) & Numbers(x,[F]\<^sup>-\<^sup>u)\<close>
        using "Ordinary.\<exists>E"[rotated] by meson
      \<comment> \<open>This application of @{text \<open>\<beta>\<close>}-conversion relies on the assumption\<close>
      \<comment> \<open>that numbering properties denotes.\<close>
      AOT_hence \<open>[F]u & [\<lambda>z Numbers(z,F)]y & [\<lambda>z Numbers(z,[F]\<^sup>-\<^sup>u)]x\<close>
        by (metis "\<beta>\<leftarrow>C"(1)[OF assms, OF "cqt:2[const_var]"[axiom_inst]] "&I" "&E")
      AOT_hence \<open>\<exists>u ([F]u & [\<lambda>z Numbers(z,F)]y & [\<lambda>z Numbers(z,[F]\<^sup>-\<^sup>u)]x)\<close>
        by (rule "Ordinary.\<exists>I")
      AOT_thus \<open>\<exists>F\<exists>u ([F]u & [\<lambda>z Numbers(z,F)]y & [\<lambda>z Numbers(z,[F]\<^sup>-\<^sup>u)]x)\<close>
        by (rule "\<exists>I")
    }
  qed
qed
(*>*)


section\<open>Modelling Possible Richness of Objects\<close>text\<open>\label{modell-modal-axiom}\<close>

text\<open>

Recall that the axiom of possible richness of objects was stated as follows (see~\nameref{AOT:modal-axiom}):

\begin{quote}
@{thm[display] "modal-axiom"[axiom_inst, of _ G, print_as_theorem]}
\end{quote}

Compared with the predecessor axiom, modelling possible richness of objects is straightforward.
The axiom implies that there are countably infinitely many ordinary (even though potentially
not @{emph \<open>actually\<close>}, but merely @{emph \<open>possibly\<close>} concrete) objects, so in our models we simply require there being a surjection from our type
@{typ \<omega>} of ordinary urelements to Isabelle's type of natural numbers @{typ nat}.
While deriving the axiom from this change in the model is still non-trivial, we can prove (notably,
our proof relies on the extended relation comprehension principles we introduced for modelling the
predecessor relation as well as AOT's defined mathematical induction), that @{emph \<open>being a natural number\<close>} in the models
corresponds to encoding only properties that are actually exemplified by only finitely many
ordinary objects. Thereby, whenever a natural number numbers a property, it is only actually
exemplified by a finite number of ordinary objects and since we have required infinitely many
ordinary objects in our model, we can produce a witness to the claim of the axiom (modulo
some further modal reasoning).

Furthermore, there is no way to model the axiom @{emph \<open>without\<close>} extending the domain of
ordinary objects in the model to infinitely many objects.

So for this axiom, the more interesting issue compared to modelling it is whether it can be philosophically
justified as a purely logical axiom or not. It is interesting to note that the axiom does not
require @{emph \<open>actual completed infinity\<close>}, but merely @{emph \<open>potential infinity\<close>}, which is
philosophically less controversial (TODO: cite).
While we do not presume to judge whether this fact and the justifications provided by Zalta and
Nodelman in PLM item (799) is sufficient to consider this axiom purely logical, we certainly
agree that it captures a natural and intuitive conception of @{emph \<open>counting\<close>}.

Interestingly, however, it may be possible to eliminate the axiom altogether and
more closely reproduce Frege's proof that every natural number has a successor as
discussed in the next section.

\<close>

section\<open>Prospect of an Enhanced Version of the Construction\<close>text\<open>\label{NewNumberTheory}\<close>
(*<*)

AOT_define Discernible :: \<open>\<Pi>\<close> (\<open>D!\<close>)
  \<open>D! =\<^sub>d\<^sub>f [\<lambda>x \<box>\<forall>y(y \<noteq> x \<rightarrow> \<exists>F \<not>([F]y \<equiv> [F]x))]\<close>

AOT_define eq_D :: \<open>\<Pi>\<close> (\<open>'(=\<^sub>D')\<close>)
  "=D": \<open>(=\<^sub>D) =\<^sub>d\<^sub>f [\<lambda>xy \<box>\<forall>F([F]x \<equiv> [F]y)]\<close>

syntax "_AOT_eq_D_infix" :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl "=\<^sub>D" 50)
translations
  "_AOT_eq_D_infix \<kappa> \<kappa>'" == "CONST AOT_exe (CONST eq_D) (CONST Pair \<kappa> \<kappa>')"
print_translation\<open>
AOT_syntax_print_translations
[(\<^const_syntax>\<open>AOT_exe\<close>, fn ctxt => fn [
  Const ("\<^const>AOT_PLM.eq_D", _),
  Const (\<^const_syntax>\<open>Pair\<close>, _) $ lhs $ rhs
] => Const (\<^syntax_const>\<open>_AOT_eq_D_infix\<close>, dummyT) $ lhs $ rhs)]\<close>


AOT_define AOT_exists_unique_D :: \<open>\<alpha> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close>
  "equi:1":  \<open>\<guillemotleft>AOT_exists_unique_D \<phi>\<guillemotright> \<equiv>\<^sub>d\<^sub>f \<exists>\<alpha> (\<phi>{\<alpha>} & \<forall>\<beta> (\<phi>{\<beta>} \<rightarrow> \<beta> =\<^sub>D \<alpha>))\<close>
syntax "_AOT_exists_unique_D" :: \<open>\<alpha> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> ("\<exists>!\<^sub>D_ _" [1,40])
translations
  "_AOT_exists_unique_D \<tau> \<phi>" <= "CONST AOT_exists_unique_D (_abs \<tau> \<phi>)"
syntax
   "_AOT_exists_unique_ellipse_D" :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close>
   (\<open>\<exists>!\<^sub>D_...\<exists>!\<^sub>D_ _\<close> [1,40])
parse_ast_translation\<open>
[(\<^syntax_const>\<open>_AOT_exists_unique_ellipse_D\<close>,
  fn ctx => fn [a,b,c] => Ast.mk_appl (Ast.Constant "AOT_exists_unique_D")
  [parseEllipseList "_AOT_vars" ctx [a,b],c]),
 (\<^syntax_const>\<open>_AOT_exists_unique_D\<close>,
  AOT_restricted_binder
    \<^const_name>\<open>AOT_exists_unique_D\<close>
    \<^const_syntax>\<open>AOT_conj\<close>)]\<close>
print_translation\<open>[
  AOT_preserve_binder_abs_tr'
    \<^const_syntax>\<open>AOT_exists_unique_D\<close>
    \<^syntax_const>\<open>_AOT_exists_unique_D\<close>
    (\<^syntax_const>\<open>_AOT_exists_unique_ellipse_D\<close>, true)
    \<^const_name>\<open>AOT_conj\<close>,
  AOT_binder_trans
    @{theory}
    @{binding "AOT_exists_unique_binder_D"}
    \<^syntax_const>\<open>_AOT_exists_unique_D\<close>
]\<close>

AOT_register_variable_names
  Individual: u v t s r

AOT_define CorrelatesDOneToOne :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (\<open>_ |: _ \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D _\<close>)
  "equi:2": \<open>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G \<equiv>\<^sub>d\<^sub>f R\<down> & F\<down> & G\<down> &
                               (\<forall>x ([F]x \<rightarrow> \<exists>!\<^sub>Dy([G]y & [R]xy)) &
                               \<forall>y ([G]y \<rightarrow> \<exists>!\<^sub>Dx([F]x & [R]xy)))\<close>

AOT_define EquinumerousE :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<phi>\<close> (infixl "\<approx>\<^sub>D" 50)
  "equi:3": \<open>F \<approx>\<^sub>D G \<equiv>\<^sub>d\<^sub>f \<exists>R (R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>D G)\<close>


(*>*)
text\<open>
At the time of writing, there is an ongoing debate concerning variations of the analysis of natural
numbers. In particular, instead of restricting the analysis to ordinary objects, identity on the
ordinary objects and equinumerosity on the ordinary object, Zalta and Nodelman brought
up the idea to instead follow the same basic construction relative to @{emph \<open>discernible objects\<close>}.

@{emph \<open>Being discernible\<close>}, @{text \<open>D!\<close>}, can be defined as the following
relation:

\begin{quote}
@{thm Discernible}
\end{quote}

Using the necessary and sufficient conditions for relations to denote
discussed in section~\ref{KirchnersTheorem}, it can be shown that @{text \<open>D!\<close>} denotes.@{footnote \<open>Note that due to
the matrix involving a non-identity claim and identity on individuals being defined in terms of
encoding, the @{text \<open>\<lambda>\<close>}-expression does not denote axiomatically.\<close>} Furthermore, just as
@{emph \<open>being ordinary\<close>}, @{emph \<open>being discernible\<close>} is a rigid restriction condition. Similar to
@{text \<open>=\<^sub>E\<close>} on the ordinary objects, a relation of identity on the discernible objects @{text \<open>=\<^sub>D\<close>} can be
defined as @{term \<open>\<guillemotleft>[\<lambda>xy \<box>\<forall>F([F]x \<equiv> [F]y)]\<guillemotright>\<close>}, i.e. for discernible objects @{emph \<open>being indistinguishable\<close>}
implies identity. The construction up until the modal axiom of section~\ref{ModalAxiom} can be preserved
without any major changes. Being equinumerous@{text \<open>\<^sub>D\<close>} can be defined just as equinumerous@{text \<open>\<^sub>E\<close>} (see section~\ref{DefinitionOfEquinumerosity}), but relative
to a one-to-one correspondence@{text \<open>\<^sub>D\<close>} on discernible objects, which in turn can be defined just as a
one-to-one correspondence@{text \<open>\<^sub>E\<close>} (see section~\ref{OneToOneCorrespondenceE}), but using restricted variables
ranging over discernible instead of ordinary objects.

The fact that @{emph \<open>numbering a property\<close>} coexists with the predecessor relation described
in section~\ref{pred} is invariant under this change. Moreover, natural numbers will
themselves become discernible (since by Hume's theorem for two objects numbering the same properties
implies their identity). This allows for abandoning the modal axiom for
possible richness of ordinary objects and instead to more closely follow Frege's
construction, in which the successor of a number @{text n} is defined as the number
of the property @{emph \<open>being smaller-or-equal to @{text n}\<close>}, i.e. @{text \<open>n\<^bold>' = #[\<lambda>m m \<le> n]\<close>},
yielding @{term \<open>\<guillemotleft>[\<P>]n n\<^bold>'\<guillemotright>\<close>}.

At the time of writing, we have prototypes for models of this new derivation available.
In these models we restrict the domain of ordinary urelements to be at most countably
infinite (i.e. either finite or in bijiection to the natural numbers), and require the
domain of special urelements to be countably infinite.@{footnote \<open>In a more general
construction, it would be sufficient to require there being countably infinitely many
special urelements that serve as proxies for discernible objects, while allowing an
arbitrary number of special urelements for indiscernible objects.\<close>}
From this restriction it can be derived that the class of cardinal numbers that measure
the size of sets of discernible objects is itself a countable set.@{footnote \<open>There is
one cardinal number for finite sets of @{text n} discernibles and an additional cardinal for countably
infinite sets of discernibles.\<close>} Since abstract objects that number properties
will be in one-to-one correspondence with the cardinals of sets of discernible urelements,@{footnote \<open>In
another variant mentioned below they will be in one-to-one correspondence with the cardinals of
sets of arbitrary urelements.\<close>} they can thus injectively be mapped into the special
urelements, making them discernible. Hence this validates the theorem that
@{emph \<open>numbering a property\<close>} denotes and consequently yields models for the predecessor
axiom.

As mentioned in section~\ref{JustificationExtendedComprehension}, is is an interesting question
whether similar general comprehension principles can be formulated for distinguishing objects
that encode different patterns among @{emph \<open>discernible\<close>} objects, as we could suggest
for patterns among @{emph \<open>ordinary\<close>} objects. However, since discerning abstract object
based on patterns among discernible objects yields new discernible objects, there is an
increased danger of general comprehension principles for encoding patterns among
discernible objects to become self-referential and thereby inconsistent. So while we
expect to be able to formulate meta-theorems about the conditions under which it
will be safe to assert the existence of relations among abstract objects that encode
patterns among discernible objects,@{footnote \<open>For example, any axiom that implies
that certain abstract objects become discernible can be consistently modelled, as long as 
it discerns at most countably many abstract objects.\<close>} it is unclear if we will be able to arrive at
general comprehension principles that can be formulated in the theorem itself.

In general, the price of being able to eliminate the modal axiom
described in section~\ref{ModalAxiom} using the new construction will be that
the predecessor axiom will become stronger and may have to rely
on independent means of justification.

Another similar variant of the construction, for which we have already constructed
full models (TODO cite), does not restrict the domain of objects that can be counted at all, but
instead of counting distinct objects rather counts equivalence classes of objects that
are indistinguishable.@{footnote \<open>I.e. indistinguishable objects belong to the same equivalence class and
objects belonging to different equivalence classes are distinguishable.\<close>} This involves weakening the unique existence used
in one-to-one correspondences to uniqueness up to distinguishability, i.e.
we define unique existence@{text \<open>\<^sub>D\<close>} as follows:
\begin{quote}
@{thm[display] "equi:1"[where \<phi> = \<open>\<lambda> \<alpha>. \<phi> \<alpha>\<close>]}
\end{quote}

One-to-one correspondences and equinumerosity are then constructed relative to this
restricted notion of unique existence:

\begin{quote}
@{thm[display]
"equi:2"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I", OF "&I", OF "cqt:2[const_var]"[axiom_inst],
OF "cqt:2[const_var]"[axiom_inst], OF "cqt:2[const_var]"[axiom_inst], of _ R F G, print_as_theorem]}
@{thm[display] "equi:3"[of F G]}
\end{quote}

While a construction based on discernible objects ignores objects that are indiscernible
for the purpose of counting, i.e. a property that is exemplified by two indistinguishable
abstract objects and no other objects is counted by Zero, this construction would count
such objects in bulk, i.e. the same property would be counted by One.
For properties that are only exemplified by discernible objects, both constructions
are equivalent (i.e. such properties are equinumerous in the first variant if and
only if they are equinumerous in the second).
\<close>

section\<open>Summary\<close>

text\<open>
In summary, we can conclude that the construction of natural numbers and the derivation
of the Dedekind-Peano postulates given in PLM is provably sound. While the construction relies
on additional axioms, we can say that:
  \<^item> PLM can present reasonable justifications for both axioms.
  \<^item> The predecessor axiom in the current construction can be generalized to comprehension
    principles that are independently justifiable, which strengthens the argument that the axiom
    is not intrinsically mathematical.
  \<^item> In a future construction, the modal axiom of possible richness of objects may no
    longer be required, eliminating the need for its justification.
  \<^item> It will be an interesting question for future research to determine whether the predecessor axiom
    can be similarly generalized in this future construction.

Methodologically, we can conclude that:
  \<^item> Our embedding can successfully reproduce even complex constructions and reasoning in our target system AOT.
  \<^item> We can achieve our goal to provide a natural and readable implementation that accurately reproduces syntax and
    reasoning in AOT without the need of keeping complex translations in mind.
  \<^item> The automation infrastructure of Isabelle can be preserved even for complex constructions in the target system.
  \<^item> Using our method we could provide insights into the construction and efficiently analyze potential extensions.

\<close>

chapter\<open>Higher-Order Type-Theoretic Object Theory\<close>text\<open>\label{HigherOrderAOT}\<close>

text\<open>
While the second-order fragment of AOT is expressive enough for a variety of
applications, including applications in @{emph \<open>natural mathematics\<close>}, as demonstrated
in the last chapter at the example of the analysis of natural numbers, the theory can
be generalized to a full type-theoretic higher-order version. A notable application of
this generalized version of AOT is its analysis of @{emph \<open>theoretical mathematics\<close>}.

While natural mathematics involves the construction of mathematical objects directly
by abstracting exemplification patterns and their properties are derived from the
principles of AOT itself, theoretical mathematics involves analyzing mathematical theories
themselves (as well as their objects, axioms and relations) as abstract objects.

While a full discussion of the type-theoretic version of AOT is beyond the scope
of this thesis, this chapter will provide a short, informal overview of its construction
and the challenges in constructing an embedding of it in Isabelle/HOL.

Note that while we reuse the notational conventions of our embedding for consistency
with the last chapters (e.g. we use square brackets in exemplification and encoding
formulas and the free-variable notation discussed in section~\ref{substitutability}),
this chapter is @{emph \<open>not\<close>} written relative to an Isabelle representation, so
in contrast to the last chapters, none of the statements and terms are cited from
an embedding. We forgo marking the statements in this chapter using vertical bars at the page margin.
\<close>
section\<open>Overview of Higher-Order Object Theory\<close>
text\<open>
Our description is based on an at the time of writing unpublished draft of a chapter
of PLM. However, the full type-theoretic version of AOT is also already discussed in
(TODO cite) and a simplified version serves as the basis of the upcoming
paper @{emph \<open>A Defense of Logicism\<close>} jointly authored by Hannes Leitgeb, Uri Nodelman and
Edward Zalta (see~\cite{Logicism}).

We already hinted at AOT's system of types in section~\ref{AOTLanguage}.
Formally, it involves the following types:

  \<^item> @{text i} is a type.
  \<^item> Whenever @{text \<open>t\<^sub>1,\<cdots>,t\<^sub>n\<close>} are types (@{text \<open>n \<ge> 0\<close>}), @{text \<open>\<langle>t\<^sub>1,\<dots>,t\<^sub>n\<rangle>\<close>} is a type.

@{text i} is the primitive type of individuals, @{text \<open>\<langle>t\<^sub>1,\<dots>,t\<^sub>n\<rangle>\<close>} is the type of relations
among @{text n} objects of the respective types @{text \<open>t\<^sub>1,\<dots>,t\<^sub>n\<close>}.
Zero-place relations, i.e. relations of type @{text \<open>\<langle>\<rangle>\<close>}, form the type of propositions.
@{text \<open>\<langle>i\<rangle>\<close>} is the type of properties among individuals. @{text \<open>\<langle>\<langle>i\<rangle>\<rangle>\<close>} is the type of
properties of properties of individuals. @{text \<open>\<langle>\<langle>i\<rangle>, \<langle>\<rangle>\<rangle>\<close>} is the type of relations between
properties and propositions, etc.

The distinction between exemplification and encoding is reproduced for higher-order
types, i.e. the language involves exemplification formulas of the form
$[\tau^{\langle t_1,\dots,t_n \rangle}]\tau^{\tau_1}\dots\tau^{\tau_n}$ and
encoding formulas of the form $\tau^{\tau_1}\dots\tau^{\tau_n}[\tau^{\langle t_1,\dots,t_n \rangle}]$.

Furthermore, the distinction between ordinary and abstract objects is generalized to
all types. I.e. for every type @{text t} there is a distinguished constant
$E!^{\langle t \rangle}$ exemplified by all concrete objects of type @{text t},
which yields definitions of @{emph \<open>being ordinary\<close>} and @{emph \<open>being abstract\<close>} at every type.

While the definitions and axiom system are similar to the second-order version described in
sections~\ref{AOTLanguage} and~\ref{AxiomSystem}, there are some notable differences.
The following is a non-exhaustive list:

  \<^item> Relation identity for relations of type @{text \<open>\<langle>t\<rangle>\<close>} is defined as:@{footnote \<open>@{text n}-ary
    relation identity for @{text \<open>n \<ge> 2\<close>} and proposition identity are extended in a similar manner to account
    for abstract @{text n}-place relations, resp. propositions.\<close>}
    @{text[display] \<open>F = G \<equiv>\<^sub>d\<^sub>f ([O!]F & [O!]G & \<box>\<forall>x(x[F] \<equiv> x[G])) \<or> ([A!]F & [A!]G & \<box>\<forall>\<H>(F[\<H>] \<equiv> G[\<H>]))\<close>}
  \<^item> Denoting @{text \<lambda>}-expressions are ordinary by axiom.
  \<^item> @{text \<eta>}-conversion is restricted to ordinary relations.

Notably, the comprehension principle for abstract objects is retained at all types @{text t}.
I.e. let @{text \<alpha>} by of type @{text t} and @{text F} be of type @{text \<open>\<langle>t\<rangle>\<close>}, then the following is an axiom:
\begin{quote}
  @{text[display] \<open>\<exists>\<alpha>([A!]\<alpha> & \<forall>F(\<alpha>[F] \<equiv> \<phi>{F}))\<close>}
\end{quote}
\<close>
section\<open>Applications to Theoretical Mathematics\<close>

text\<open>
The analysis of Theoretical Mathematics in higher-order object theory was described
in (TODO: cite) and a simplified version is used in~\cite{Logicism}.

While a full-discussion of the involved subtleties again goes beyond the scope of this
thesis, we illustrate the general idea at the example of the representation of
Zermelo-Fraenkel set-theory as an abstract object @{text \<open>ZF\<close>} in higher-order AOT.

Technically, a mathematical theory in AOT is a @{emph \<open>situation\<close>}, i.e. an abstract
object that encodes only propositional properties.@{footnote \<open>Recall the discussion in
section~\ref{PossibleWorldTheory}.\<close>} So we can reuse the notation @{text \<open>T \<Turnstile> p\<close>} as
the proposition @{text p} is true in theory @{text T}.

One of the cornerstones of the analysis is the @{emph \<open>Importation Principle\<close>},
stated in~\cite{Logicism} as follows:

\begin{quote}
  When @{text \<phi>} is a closed theorem of @{text T}, then @{text \<open>T \<Turnstile> \<phi>\<^sup>*\<close>} shall be
  an axiom, where @{text \<open>\<phi>\<^sup>*\<close>} is the result of indexing every occurrence of a term or
  predicate of @{text T} to @{text T}.
\end{quote}

So taking @{term S} as ZF's property of @{emph \<open>being a set\<close>}, it is a theorem of
ZF that:

\begin{quote}
  @{text[display] \<open>\<turnstile>\<^sub>Z\<^sub>F \<not>\<exists>y([S]y & y \<in> \<emptyset>)\<close>}
\end{quote}

This theorem can be imported to AOT using the following instance of the Importation Principle:

\begin{quote}
  @{text[display] \<open>ZF \<Turnstile> \<not>\<exists>y([S\<^sub>Z\<^sub>F]y & y \<in>\<^sub>Z\<^sub>F \<emptyset>\<^sub>Z\<^sub>F)\<close>}
\end{quote}

Furthermore, the involved indexed terms of ZF are in turn abstract objects in AOT, e.g.
\begin{quote}
  @{text[display] \<open>\<emptyset>\<^sub>Z\<^sub>F = \<^bold>\<iota>x([A!]x & \<forall>F(x[F] \<equiv> ZF \<Turnstile> [F]\<emptyset>\<^sub>Z\<^sub>F)\<close>}
  @{text[display] \<open>S\<^sub>Z\<^sub>F = \<^bold>\<iota>F([A!]F & \<forall>\<F>(x[\<F>] \<equiv> ZF \<Turnstile> [\<F>]S\<^sub>Z\<^sub>F)\<close>}
  @{text[display] \<open>\<in>\<^sub>Z\<^sub>F = \<^bold>\<iota>R([A!]R & \<forall>\<R>(x[\<R>] \<equiv> ZF \<Turnstile> [\<R>]\<in>\<^sub>Z\<^sub>F)\<close>}
\end{quote}

Exemplifying properties in ZF can be translated to encoding claims in AOT. E.g.
in ZF, @{text \<open>\<emptyset>\<close>} exemplifies the property @{text \<open>[\<lambda>x \<not>\<exists>y([S]y & y \<in> x)]\<close>}. This
property can be captured as an @{emph \<open>abstract property\<close>} in AOT that is @{emph \<open>encoded\<close>}
by @{text \<open>\<emptyset>\<^sub>Z\<^sub>F\<close>}:@{footnote \<open>While @{text \<lambda>}-expressions in higher-order AOT are ordinary,
theory-indexed @{text \<lambda>}-expressions are abstract.\<close>}

\begin{quote}
  @{text[display] \<open>\<emptyset>\<^sub>Z\<^sub>F[[\<lambda>x \<not>\<exists>y([S\<^sub>S\<^sub>F]y & y \<in>\<^sub>Z\<^sub>F x)]\<^sub>Z\<^sub>F]\<close>}
\end{quote}

While a detailed account of the construction and its implications is the topic of
the upcoming paper~\cite{Logicism}, we will discuss the general issue of embedding
higher-order AOT in Isabelle/HOL in the next section.
\<close>

section\<open>Bounded Models\<close>

text\<open>

\cite{Logicism} constructs minimal extensional models for the simplified version
of higher-order AOT it uses for its argumentation. This construction defines the
@{emph \<open>height\<close>} of a type @{text t}, written @{text \<open>h(t)\<close>}, and
the @{emph \<open>width\<close>} of a type @{text t}, written @{text \<open>w(t)\<close>} as:

  \<^item> @{text \<open>h(i) = 0\<close>}
  \<^item> @{text \<open>h(\<langle>\<rangle>) = 1\<close>}
  \<^item> @{text \<open>h(\<langle>t\<^sub>1,\<dots>,t\<^sub>n\<rangle>) = 1 + max{h(t\<^sub>1),\<dots>,h(t\<^sub>n)}\<close>}
  \<^item> @{text \<open>w(i) = 1\<close>}
  \<^item> @{text \<open>w(\<langle>\<rangle>) = 1\<close>}
  \<^item> $w(\langle t_1,\dots,t_n \rangle) = \sum_1^k w(t_k)$

And then presents a concrete model construction for bounded languages @{text \<open>\<L>\<^sub>n\<^sub>,\<^sub>m\<close>} that are @{emph \<open>cut off\<close>}
at width @{text n} and height @{text m}, i.e. the well-formed expressions of the language @{text \<open>\<L>\<^sub>n\<^sub>,\<^sub>m\<close>} are
the expressions of the unbounded language @{text \<open>\<L>\<close>} in which only terms of type @{text t} are well-formed,
if @{text \<open>w(t) \<le> n\<close>} and @{text \<open>h(t) \<le> m\<close>}.
In particular, types of height @{text m} only involve ordinary objects, not abstract objects. For example,
the second-order fragment described in the last chapters, is cut off at height @{text 1}: while it involves
abstract objects, all relations and propositions are ordinary. Furthermore, while the
second-order fragment considers properties of objects (height 1), it does not consider higher-order
relations like properties of properties or properties of propositions.@{footnote \<open>Note that the cut-off involves
subtle changes in the precise formulation of the definitions and the axiom system.\<close>}

While we expect it to be feasible to construct a representation in Isabelle/HOL
that allows for an arbitrary parameter as cut-off in height (and potentially width, though it may be possible
to keep width unbounded), we expect the details of such a construction to be non-trivial due to the non-uniform nature of the
representation sets of types. We leave the construction of such an embedding to future
research.
\<close>

section\<open>Abstract Objects in Unbounded Models\<close>

text\<open>
While, arguably, a construction of models for higher-order object theory with a fixed, but arbitrary
cutoff may be sufficient for all intents and purposes, the issue of constructing unbounded
models (resp. an unrestricted embedding of higher-order AOT in HOL) is nevertheless interesting:
Theoretically, it may provide insights into the relative strength of higher-order AOT
compared to HOL. Technically, unbounded models have the advantage of being uniform in all types,
which is beneficial for a generic implementation.

However, if we consider the extent of the generalized comprehension principle of
abstract objects and the identity conditions of abstract objects, it becomes clear
that the construction of such models is not trivial.

In particular, note that the comprehension principle for
abstract individuals has the following instance:

\begin{quote}
@{text[display] \<open>\<exists>x ([A!]x & \<forall>F (x[F] \<equiv> ([O!]F & \<phi>{F} \<or> [A!]F & \<forall>\<F> (F[\<F>] \<equiv> \<psi>{\<F>}))))\<close>}
\end{quote}

Such an abstract object @{text x} (at type @{text i})
encodes all ordinary properties @{text F} (at type @{text \<open>\<langle>i\<rangle>\<close>}) that
satisfy an arbitrary condition @{text \<phi>} and all abstract properties @{text F}
that encode exactly those properties of properties @{text \<F>} (at type @{text \<open>\<langle>\<langle>i\<rangle>\<rangle>\<close>}) that satisfy
an arbitrary condition @{text \<psi>} on @{text \<F>}.

Now for two such abstract objects (at type @{text i}) to be identical,
they not only have to encode the same ordinary properties (at type @{text \<open>\<langle>i\<rangle>\<close>}), but
also the same abstract properties (at type @{text \<open>\<langle>i\<rangle>\<close>}).
Those abstract properties in turn are identical, if they encode the same properties
of properties (at type @{text \<open>\<langle>\<langle>i\<rangle>\<rangle>\<close>}).

This can be iterated further, since there are also abstract properties of properties among individuals that
may encode properties of properties of properties among individuals, etc. pp.

While we leave a more detailed and rigorous analysis to future research, we try to
informally illustrate the expected size of the set of abstract objects in unbounded
models.

Thinking in terms of Aczel models, let @{text \<open>O\<^sub>t\<close>} be the set of ordinary objects at
type @{text t} and @{text \<open>S\<^sub>t\<close>} the set of special urelements of type @{text t}.
Now the set of relations among objects of type @{text t}, i.e. @{text \<open>O\<^sub>\<langle>\<^sub>t\<^sub>\<rangle>\<close>} will
be at least as large as the power set @{text \<open>\<P>(O\<^sub>t \<union> S\<^sub>t)\<close>}. For simplicity, we consider
minimal, extensional Aczel models, in which we have @{text \<open>O\<^sub>\<langle>\<^sub>t\<^sub>\<rangle> = \<P>(O\<^sub>t \<union> S\<^sub>t)\<close>}.

If we restrict ourselves to unary relations and write @{text 0} for the type of ordinary individuals @{text i},
@{text 1} for the type of relations among individuals @{text \<open>\<langle>i\<rangle>\<close>} and so on, i.e. in general
we choose @{text \<open>n+1\<close>} for unary relations among the type we identified with @{text n}, we get
the following:

@{text \<open>O\<^sub>1 = \<P>(O\<^sub>0 \<union> S\<^sub>0)\<close>}\<^latex>\<open>\\\<close>
@{text \<open>O\<^sub>2 = \<P>(O\<^sub>1 \<union> S\<^sub>1)\<close>}\<^latex>\<open>\\\<close>
@{text \<open>O\<^sub>3 = \<P>(O\<^sub>2 \<union> S\<^sub>2)\<close>}\<^latex>\<open>\\\<close>
@{text \<open>\<dots>\<close>}

Now if we, solely for the purpose of arriving at a crude size estimate,
further assume @{text \<open>O\<^sub>0\<close>} is empty and @{text \<open>S\<^sub>i = S\<^sub>0 = S\<close>}, we get:

@{text \<open>O\<^sub>0 = \<emptyset>\<close>}\<^latex>\<open>\\\<close>
@{text \<open>O\<^sub>1 = \<P>(O\<^sub>0 \<union> S) = \<P>(S)\<close>}\<^latex>\<open>\\\<close>
@{text \<open>O\<^sub>2 = \<P>(O\<^sub>1 \<union> S) = \<P>(\<P>(S) \<union> S) \<supseteq> \<P>(\<P>(S)) \<union> \<P>(S)\<close>}\<^latex>\<open>\\\<close>
@{text \<open>O\<^sub>3 = \<P>(O\<^sub>2 \<union> S) = \<P>(\<P>(\<P>(S) \<union> S) \<union> S) \<supseteq> \<P>(\<P>(\<P>(S))) \<union> \<P>(\<P>(S)) \<union> \<P>(S)\<close>}\<^latex>\<open>\\\<close>
@{text \<open>\<dots>\<close>}

Now if we assume that @{text S} has only one element and identify it with
@{text \<open>\<P>(\<emptyset>)\<close>}, and (informally for the purpose of illustrating) consider the limit @{text \<open>O\<^sub>\<omega>\<close>}
of relations at countably infinite height, we arrive at a model of
the natural numbers, i.e. @{text \<open>|O\<^sub>\<omega>| \<ge> |\<nat>|\<close>}.

The set of abstract objects at type @{text \<open>m - 1\<close>} is the power set of ordinary and
abstract objects of type @{text m}, i.e. @{text \<open>A\<^sub>m\<^sub>-\<^sub>1 = \<P>(O\<^sub>m \<union> A\<^sub>m)\<close>}. So we get:

@{text \<open>A\<^sub>m\<^sub>-\<^sub>1 = \<P>(O\<^sub>m \<union> A\<^sub>m)\<close>}\<^latex>\<open>\\\<close>
@{text \<open>A\<^sub>m\<^sub>-\<^sub>2 = \<P>(O\<^sub>m\<^sub>-\<^sub>1 \<union> A\<^sub>m\<^sub>-\<^sub>1) = \<P>(O\<^sub>m\<^sub>-\<^sub>1 \<union> \<P>(O\<^sub>m \<union> A\<^sub>m))\<close>}\<^latex>\<open>\\\<close>
@{text \<open>A\<^sub>m\<^sub>-\<^sub>3 = \<P>(O\<^sub>m\<^sub>-\<^sub>2 \<union> A\<^sub>m\<^sub>-\<^sub>2) = \<P>(O\<^sub>m\<^sub>-\<^sub>2 \<union> \<P>(O\<^sub>m\<^sub>-\<^sub>1 \<union> \<P>(O\<^sub>m \<union> A\<^sub>m)))\<close>}\<^latex>\<open>\\\<close>
@{text \<open>\<dots>\<close>}\<^latex>\<open>\\\<close>
@{text \<open>A\<^sub>0 = \<P>(O\<^sub>1 \<union> \<P>(O\<^sub>2 \<union> \<P>(O\<^sub>3 \<union> \<P>(\<dots> \<union> A\<^sub>m)\<dots>)))\<close>}

In particular, no finite application of power set operations is enough to
construct @{text \<open>A\<^sub>0\<close>} from the (illustrative) limit set @{text \<open>A\<^sub>\<omega>\<close>}, which in turn would be the power set
of @{text \<open>O\<^sub>\<omega>\<close>}, i.e. of a set at least as large as the natural numbers.

While this informal argument will not hold up to scrutiny, it is safe to say that the
set of abstract objects in an unbounded model of higher-order object theory will
be huge. We wouldn't be surprised if a future more rigorous analysis were to
conclude that the set of abstract individuals in non-trivial models of higher
order AOT had to be sufficiently large to form a model of ZF itself (resp. that
the cardinality of @{text \<open>A\<^sub>0\<close>} is strongly inaccessible).

Consequently, a verifiably sound implementation relative to the unextended background theory
of Isabelle/HOL may be challenging, since the expressive power of higher-order AOT may be
on par with or even exceed the expressive power of this choice of a meta-logic. However, even if this turns
out to be the case, it may be possible to construct a representation based on a stronger
extension of Isabelle/HOL, for example HOLZF or one of its variants (TODO: cite), which
axiomatizes the ZFC universe itself as a type in HOL. The feasibility of such an embedding
as well as results about the relative strength of higher-order object theory, are
interesting questions for future research.
\<close>

chapter\<open>Conclusion\<close>

text\<open>
We presented an implementation of a foundational metaphysical theory
in an automated reasoning environment by leveraging and extending the concept of
shallow semantic embeddings in classical higher-order logic.

In the process, we could demonstrate that:
  \<^item> The SSE approach is scalable and can not only be used for analyzing isolated arguments,
    but can also be applied to a full metaphysical theory, while providing an accurate
    implementation of its axioms and deductive system.
  \<^item> Such an implementation is not merely a technical exercise, but can trigger a fruitful
    exchange that in our case led to significant improvements of the analyzed theory
    on the one hand and sched new light on the technical possibilities and limitations
    of the SSE approach on the other hand. In particular, our embedding allows for the
    rapid analysis of changes to and extensions of the axiom system of the target theory
    on the one hand, and of the effects of variations of complex constructions within a given
    axiomatization of the target system on the other hand.
  \<^item> It is not only possible to technically reproduce the logic of a complex
    target theory, but also to construct a nearly transparent representation of its
    syntax and reasoning flow, allowing for an efficient and effortless exchange
    of results between traditional pen-and-paper based reasoning and theorems and
    properties of the system discovered on the basis of its computerized implementation.
  \<^item> The automation infrastructure of Isabelle/HOL can be preserved and applied to
    construct proofs that accurately correspond to derivations in the target system.
    This way we effectively arrive at a dedicated automated theorem proving environment for
    our target system, while retaining a verifiably consistent meta-logical backend.
  \<^item> The target theory AOT itself can verifiably live up to its claim to be able to
    provide a philosophically grounded construction and analysis of natural mathematics.
    In particular, we can confirm that AOT can serve as a sound basis for a variant of
    Frege's construction of natural numbers. Furthermore, we could significantly contribute
    to the evolution of this construction and provide further insights into the nature
    of its required axioms.

Curiously, our results simultaneously support the use of higher-order logic
as universal meta-logic in that we can demonstrate that the SSE approach can be used
to accurately represent even challenging foundational logical theories, while also
strengthening the position of our target theory AOT as foundational system in confirming
its ability to provide a philosophically grounded construction of mathematical objects.
In this context, an attempt of an implementation of the full type-theoretic higher-order
version of AOT using the SSE approach, as well as the formal analysis of its relative
strength compared to HOL and ZF are fascinating opportunities for future research.
\<close>

(*<*)
end
(*>*)