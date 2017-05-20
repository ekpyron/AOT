(*<*)
theory Thesis
imports TAO_9_PLM TAO_98_ArtificialTheorems TAO_99_SanityTests TAO_99_Paradox
    "~~/src/HOL/Library/LaTeXsugar"
    "~~/src/HOL/Library/OptionalSugar"
begin
(*>*)

(*<*)
(* Pretty printing settings for antiquotations. *)
notation (latex output)
  validity_in ("[\<^latex>\<open>\\embeddedstyle{\<close>_\<^latex>\<open>}\<close> in _]")
notation (latex output)
  actual_validity ("[\<^latex>\<open>\\embeddedstyle{\<close>_\<^latex>\<open>}\<close>]")
notation (latex output)
  Axioms.axiom ("[[ \<^latex>\<open>\\embeddedstyle{\<close>_\<^latex>\<open>}\<close> ]]")
definition embedded_style where "embedded_style \<equiv> id"
lemma embedded_meta_def: "(A \<equiv> B) \<Longrightarrow> (embedded_style A) = B" unfolding embedded_style_def by auto
lemma embedded_meta_eq: "(A = B) \<Longrightarrow> (embedded_style A) = B" unfolding embedded_style_def by auto
lemma embedded_def: "(A \<equiv> B) \<Longrightarrow> (embedded_style A) = (embedded_style B)"
    unfolding embedded_style_def by auto
lemma embedded_eq: "(A = B) \<Longrightarrow> (embedded_style A) = (embedded_style B)"
    unfolding embedded_style_def by auto
notation (latex output)
  embedded_style ("\<^latex>\<open>\\embeddedstyle{\<close>_\<^latex>\<open>}\<close>")
translations
  "x" <= "CONST make\<kappa> x"
translations
  "p" <= "CONST make\<o> p"
translations
  "p" <= "CONST make\<Pi>\<^sub>1 p"
translations
  "p" <= "CONST make\<Pi>\<^sub>2 p"
translations
  "p" <= "CONST make\<Pi>\<^sub>3 p"
translations
  "x" <= "CONST eval\<kappa> x"
translations
  "p" <= "CONST eval\<o> p"
translations
  "p" <= "CONST eval\<Pi>\<^sub>1 p"
translations
  "p" <= "CONST eval\<Pi>\<^sub>2 p"
translations
  "p" <= "CONST eval\<Pi>\<^sub>3 p"
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
  forall ("\<^bold>\<forall> \<alpha> . _ \<alpha>")
notation (latex output)
  exists ("\<^bold>\<exists> \<alpha> . _ \<alpha>")
notation (latex output)
  exists_unique ("\<^bold>\<exists>! \<alpha> . _ \<alpha>")
notation (latex output)
  lambdabinder1 ("\<^bold>\<lambda>x. _ x")
translations
  (type) "\<alpha>" <= (type) "\<Pi>\<^sub>1 set"
(* auxiliary lemmata and attributes to aid in pretty printing *)
lemma expand_def1: "p \<equiv> q \<Longrightarrow> (\<And>x . p x = q x)" by simp
lemma expand_def2: "p \<equiv> q \<Longrightarrow> (\<And>x y . p x y = q x y)" by simp
lemma expand_def3: "p \<equiv> q \<Longrightarrow> (\<And>x y z . p x y z = q x y z)" by simp
attribute_setup expand1 = {*
  Scan.succeed (Thm.rule_attribute [] 
    (fn _ => fn thm => thm RS @{thm expand_def1}))
*}
attribute_setup expand2 = {*
  Scan.succeed (Thm.rule_attribute [] 
    (fn _ => fn thm => thm RS @{thm expand_def2}))
*}
attribute_setup expand3 = {*
  Scan.succeed (Thm.rule_attribute [] 
    (fn _ => fn thm => thm RS @{thm expand_def3}))
*}
no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") 
no_syntax "__listcompr" :: "args \<Rightarrow> 'a list" ("[(_)]")
(*>*)
  
(* abstract in thesis/root.tex *)

chapter{* Introduction *}

text{*
\epigraph{Calculemus!}{\textit{Leibniz}}
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
in an automated fashion, an idea that became famous under the slogan \emph{Calculemus!}.

Nowadays with the rise of powerful computer systems such a universal logical framework could have
repercussions throughout the sciences (TODO: change this?) and may be a vital part of
machine-computer interaction in the future. Leibniz' ideas have inspired
recent efforts to use functional higher-order logic (HOL) as such a universal logical language
and to represent various logical systems by the use of \emph{shallow semantical embeddings}
(TODO: reference \url{https://arxiv.org/abs/1703.09620}).

Notably this approach received attention due to the formalisation, validation and analysis
of G\"odel's ontological proof of the existence of God by Christoph Benzm\"uller (TODO: reference),
for which higher-order modal logic was embedded in the computerized logic framework Isabelle/HOL.
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

While this approach will work for most target logics, it has several drawbacks. It is likely that there are
principles that are shared between the target logic and the background logic, such as @{text "\<alpha>"}-conversion
for @{text "\<lambda>"}-expressions or the equivalence of terms with renamed variables in general. In a deep
embedding these principles usually have to be explicitly shown to hold for the syntactic representation
of the target logic, which is usually connected with significant complexity. Furthermore if the
framework used for the background logic allows automated reasoning, the degree of automation that
can be achieved in the embedded logic is limited, as any reasoning in the target logic will have
to consider the translation process to the background logic that will usually be complex.

A \emph{shallow} embedding uses a different approach based on the idea that most contemporary
logical systems are semantically characterized by the means of set theory. A shallow embedding
now defines primitive syntactical objects of the target language such as variables or propositions
using a set theoretic representation. For example propositions in a modal logic can be represented
as functions from possible worlds to truth values in a non-modal logic.

The shallow embedding aims to equationally define only the syntactical elements of the target logic
that are not already present in the background logic or whose semantics behaves differently than in
the background logic, while preserving as much of the logical structure of the background logic
as possible. The modal box operator for example can be represented as a quantification over all
possible worlds satisfying an accessibility relation, while negation and quantification can be
directly represented using the negation and quantification of the background logic (preserving
the dependency on possible worlds).

This way basic principles of the background logic (such as alpha conversion) can often be directly
applied to the embedded logic and the equational, definitional nature of the representation preverses
a larger degree of automation. Furthermore axioms in the embedded logic can often be equivalently
stated in the background logic, which makes the construction of models for the system easier and again increases
the degree of automation that can be retained.

The shallow semantical embedding of modal logic was the basis for the analysis of
G\"odel's onthological argument and the general concept has shown great potential as a universal
tool for logical embeddings while retaining the existing infrastructure for automation as for
example present in a framework like Isabelle/HOL. (TODO: more application examples)

*}

(* TODO: no new section? *)
section{* Relational Type Theory vs. Functional Type Theory *}

text{*
The universality of this approach has since been challenged by Paul Oppenheimer and Edward Zalta
who argue in the paper \emph{Relations Versus Functions at the Foundations of Logic: Type-Theoretic
Considerations}(@{cite rtt}) that relational type theory is more general than functional type theory.
In particular they argue that the Theory of Abstract Objects, which is founded in relational type
theory, can not be properly characterized in functional type theory.

This has led to the question whether a shallow semantical embedding of the Theory of Abstract Objects
in a functional logical framework like Isabelle/HOL is at all possible, which is the core question
the work presented here attempts to examine and partially answer.

One of their main arguments is that unrestricted @{text "\<lambda>"}-expressions as present in functional type
theory lead to an inconsistency when combined with one of the axioms of the theory and indeed it
has been shown for early attempts on embedding the theory that despite significant efforts
to avoid the aforementioned inconsistency by excluding problematic @{text "\<lambda>"}-expressions in the embedded
logic, it could still be reproduced using an appropriate construction in the background logic.

The solution presented here circumvents this problem by identifying @{text "\<lambda>"}-expressions as one element of the
target language that behaves differently than their counterparts in the background logic and
consequently by representing @{text "\<lambda>"}-expressions of the target logic using a new \emph{defined}
kind of @{text "\<lambda>"}-expressions. This forces @{text "\<lambda>"}-expressions in the embedded logic to have a particular
semantics that is inspired by the \emph{Aczel-model} of the target theory (see \ref{aczel-model})
and avoids prior inconsistencies. The mentioned issue and the employed solution is discussed in
more detail in section \ref{challenges}.

*}

section{* Our Contribution *}

text{*
\begin{TODO}
  Embedding of second order fragment of PLM. Complex semantics, term-based syntax,
  scope of the embedding, technical challenges. Kirchner's paradox.
\end{TODO}
*}

section{* Overview of the following Chapters *}

text{*
  \begin{TODO}
    Improve and adjust.
  \end{TODO}

  The following chapters are structured as follows:

  \begin{itemize}
    \item The second chapter gives an overview of the motivation and structure of
          the target theory of the embedding, the Theory of Abstract Objects. It also
          introduces the \emph{Aczel-model} of the theory, that was adapted as the basis
          for the embedding.
  
    \item The third chapter is a detailed documentation of the concepts and
          technical structure of the embedding. This chapter references the
          Isabelle theory that can be found in the appendix.
  
    \item The fourth chapter discusses the relation between the embedding and the target theory
          of PLM and describes some of the results achieved using the embedding. Furthermore it
          states some open questions for future research.
  
    \item The last chapter consists of a technical discussion about some of the issues encountered
          during the construction of the embedding due to limitations of the logical framework
          of Isabelle/HOL and the solutions that were employed.
  \end{itemize}

  Note that this entire document is generated from an Isabelle theory file and thereby starting
  from the third chapter all formal statements throughout the document are well-formed terms,
  resp. verified valid theorems in the constructed embedding unless the contrary is explicitly
  stated.
*}

chapter{* The Theory of Abstract Objects *}

text{*
  \epigraph{
It is widely supposed that every entity falls into one of two categories:
Some are concrete; the rest abstract. The distinction is supposed to be
of fundamental significance for metaphysics and epistemology.
}{\textit{Stanford Encyclopedia of Philosophy\cite{sep-abstract-objects}}}
*}

section{* Motivation *}

text{*

As the name suggests the Theory of Abstract Objects revolves around \emph{abstract objects} and
is thereby a metaphysical theory.
As Zalta puts it: \textquote{Whereas physics attempts a systematic description of fundamental
and complex concrete objects, metaphysics attempts a systematic description of fundamental
and complex abstract objects. \textelp{} The theory of abstract objects attempts to organize
these objects within a systematic and axiomatic framework. \textelp{We can} think of abstract
objects as possible and actual property-patterns. \textelp{} Our theory of abstract
objects will \emph{objectify} or \emph{reify} the group of properties satisfying \textins{such a}
pattern.}\cite{MallyTheory}

So what is the fundamental distinction between abstract and concrete objects? The analysis
in the Theory of Abstract Objects is based on a distinction between two fundamental modes of
predication that is based on the ideas of Ernst Mally (TODO: reference, maybe again just \cite{MallyTheory}).
Whereas objects that are concrete (the Theory of Abstract Objects calls them \emph{ordinary objects})
are characterized by the classical mode of predication, i.e. \emph{exemplification},
a second mode of predication is introduced that is reserved for abstract objects. This new mode of
predication is called \emph{encoding} and formally written as @{text "xF"} (@{text "x"}
\emph{encodes} @{text "F"}) in contrast to @{text "Fx"} (@{text "x"} \emph{exemplifies} @{text "F"}).

Mally informally introduces this second mode of predication in order to represent sentences about
fictional objects. In his thinking only concrete objects, that for example have a fixed spatiotemporal
location, a body and shape, etc., can \emph{exemplify} their properties and are characterized
by the properties they exemplify. Sentences about fictional objects such as \textquote{Sherlock Holmes
is a detective} have a different meaning. Stating that \textquote{Sherlock Holmes is a detective} 
does not imply that there is some concrete object that is Sherlock Holmes and this object exemplifies
the property of being a detective - it rather states that the concept we have of the fictional
character Sherlock Holmes includes the property of being a detective. Sherlock Holmes is not concrete,
but an abstract object that is \emph{determined} by the properties Sherlock Holmes is given by the
fictional works involving him as character. This is expressed using the second mode of predication
\emph{Sherlock Holmes encodes the property of being a detective}.

To clarify the difference between the two concepts note that any object either exemplifies a property
or its negation. The same is not true for encoding. For example it is not determinate whether 
Sherlock Holmes has a mole on his left foot. Therefore the abstract object Sherlock Holmes neither
encodes the property of having a mole on his left foot, nor the property of not having a mole on
his left foot.

The theory even allows for an abstract object to encode properties that no object
could possibly exemplify and reason about them, for example the quadratic circle. In classical logic
meaningful reasoning about a quadratic circle is impossible - as soon as I suppose an object that
\emph{exemplifies} the properties of being a circle and of being quadratic, this will lead to a
contradiction and every statement becomes derivable.

In the Theory of Abstract Objects on the other hand
there is an abstract object that encodes exactly these two properties and it is possible to reason
about it. For example we can state that this object \emph{exemplifies} the property of \emph{being
thought about by the reader of this paragraph}. This shows that the Theory of Abstract Objects provides
the means to reason about processes of human thought in a much broader sense than classical logic
would allow.

It turns out that by the means of abstract objects and encoding the Theory of Abstract Objects
  can be used to represent and reason about a large variety of concepts that
regularly occur in philosophy, mathematics or linguistics.

In \cite{MallyTheory} the principal objectives of the theory are summerized as follows:

\begin{itemize}
  \item To describe the logic underlying (scientific) thought and reasoning by extending
        classical propositional, predicate, and modal logic.
  \item To describe the laws governing universal entities such as properties, relations,
        and propositions (i.e., states of affairs).
  \item To identify \emph{theoretical} mathematical objects and relations as well as
        the \emph{natural} mathematical objects such as natural numbers and natural sets.
  \item To analyze the distinction between fact and fiction and systematize the various
        relationships between stories, characters, and other fictional objects.
  \item To systematize our modal thoughts about possible (actual, necessary) objects,
        states of affairs, situations and worlds.
  \item To systematize our modal thoughts about possible (actual, necessary) objects,
        states of affairs, situations and worlds.
  \item To account for the deviant logic of propositional attitude reports, explain the
        informativeness of identity statements, and give a general account of the objective
        and cognitive content of natural language.
  \item To axiomatize philosophical objects postulated by other philosophers, such as Forms (Plato),
        concepts (Leibniz), monads (Leibniz), possible worlds (Leibniz), nonexistent objects (Meinong),
        senses (Frege), extensions of concepts (Frege), noematic senses (Husserl), the world as a
        state of affairs (early Wittgenstein), moments of time, etc.
\end{itemize}

The Theory of Abstract Objects has therefore the ambition and the potential to serve as a foundational
theory of metaphysics as well as mathematics and can provide a simple unified axiomatic framework to reason
about a huge variety of concepts throughout the sciences. This makes the attempt to represent the
theory using the universal reasoning approach of shallow semantical embeddings outlined in the previous
chapter particularly challenging and at the same time rewarding, if successful.

A successful implementation of
the theory that allows it to utilize the existing sophisticated infrastructure for automated reasoning 
present in a framework like Isabelle/HOL would not only strongly support the applicability of shallow
semantical embeddings as a universal reasoning tool, but could also serve as the basis for spreading
the utilization of the theory itself as a foundational theory for various scientific fields by
enabling convenient interactive and automated reasoning in a verified framework.

Although the embedding revealed certain challenges in this approach and there remain open questions
for example about the precise relationship between the embedding and the target theory or its soundness
and completeness, it is safe to say that it represents a significant step towards achieving this
goal. 

*}

section{* Basic Principles *}

text{*
  Although the formal language of the theory is introduced only in the next section,
  it is worth to present some of the basic concepts of the theory in advance to provide
  further motivation for the formalism.

  The following are the two most important principles of the theory:

  \begin{itemize}
    \item @{text "\<exists>x(A!x & \<forall>F(xF \<equiv> \<Phi>))"}
    \item @{text "x = y \<equiv> \<box>\<forall>F(xF \<equiv> yF)"}
  \end{itemize}

  The first statement asserts that for every condition on properties @{text "\<Phi>"} there exists
  an abstract object that encodes exactly those properties satisfying @{text "\<Phi>"}, whereas the
  second statement holds for two abstract objects @{text "x"} and @{text "y"} and states that
  they are equal, if and only if they necessarily encode the same properties.

  Together these two principles clarify the notion of abstract objects as the reification
  of property patterns: Any set of properties is objectified as a distinct abstract object.

  Note that these principles already allow it to postulate interesting abstract objects.

  For example the Leibnizian concept of an (ordinary) individual @{text "u"} can be 
  defined as \emph{the (unique) abstract object that encodes all properties that @{text "u"} exemplifies},
  formally: \mbox{@{text "\<iota>x A!x & \<forall>F (xF \<equiv> Fu)"}}
  
  Other interesting examples include possible worlds, Platonic Forms or even basic logical objects
  like truth values. Here it is important to note that the theory allows it to formulate
  a purely \emph{syntactic} definition of objects like possible worlds and truth values and
  from these syntactic definitions it can be \emph{derived} that there are two truth values
  or that the application of the modal box operator to a proposition is equivalent to the proposition
  being true in all possible worlds (where \emph{being true in a possible world} is again defined
  syntactically).

  This is an impressive property of the Theory of Abstract Objects: it can \emph{syntactically}
  define objects that are usually only considered semantically.
*}
  
section{* The Language of PLM *}
  
text{*
The target of the embedding is the second order fragment of object theory as described
in chapter 7 of Edward Zalta's upcoming \emph{Principia Logico Metaphysica} (PLM) @{cite PM}.
The logical foundation of the theory uses a second-order modal logic (without primitive identity)
formulated using relational type theory that is modified to admit \emph{encoding} as a second mode
of predication besides the traditional \emph{exemplification}.
In the following an informal description of the important aspects of the language is provided;
for a detailed and fully formal description and the type-theoretic background refer to the respective
chapters of PLM@{cite PM}.

A compact description of the language can be given in Backus-Naur Form (BNF)\mbox{@{cite \<open>p. 170\<close> PM}}.
The following grammatical categories are used:

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

It is important to note that the language distinguishes between two types of basic formulas,
namely (non-propositional) \emph{formulas} that \emph{may} contain encoding subformulas and
\emph{propositional formulas} that \emph{may not} contain encoding subformulas. Only propositional
formulas may be used in @{text "\<lambda>"}-expressions. The main reason for this distinction will be explained
in the section~\ref{russell-paradox}.

Note that there is a case in which propositional formulas \emph{can} contain encoding
expressions. This is due to the fact that \emph{subformula} is defined in such a way that
@{text "xQ"} is \emph{not} a subformula of @{text "\<iota>x(xQ)"} (for a formal definition of subformula
refer to definition (\ref{PM-df-subformula}) in @{cite PM}). Thereby @{text "F\<iota>x(xQ)"} is a
propositional formula and @{text "[\<lambda>y F\<iota>x(xQ)]"} a well-formed @{text "\<lambda>"}-expression.
On the other hand @{text "xF"} is not a propositional formula and therefore
@{text "[\<lambda>x xF]"} not a well-formed @{text "\<lambda>"}-expression. This fact will become relevant in
the discussion in section~\ref{paradox}, that describes a paradox in the formulation of
the theory in the draft of PLM at the time of writing. (TODO: mention solvability already here?)

Furthermore the theory contains a designated relation constant @{text "E!"} to be read as
\emph{being concrete}. Using this constant the distinction between ordinary and abstract objects
is defined as follows:

  \begin{itemize}
    \item @{text "O! =\<^sub>d\<^sub>f [\<lambda>x \<^bold>\<diamond>E!x]"}
    \item @{text "A! =\<^sub>d\<^sub>f [\<lambda>x \<^bold>\<not>\<^bold>\<diamond>E!x]"}
  \end{itemize}

So ordinary objects are possibly concrete, whereas abstract objects cannot possibly be concrete.

It is important to note that the language does not contain the identity as primitive.
Instead the language uses \emph{defined} identities as follows:

\begin{tabular}{lc}
  ordinary objects & @{text "x =\<^sub>E y =\<^sub>d\<^sub>f O!x & O!y & \<box>(\<forall>F Fx \<equiv> Fy)"}\\
  individuals & @{text "x = y =\<^sub>d\<^sub>f x =\<^sub>E y \<or> (A!x & A!y & \<box>(\<forall>F xF \<equiv> yF))"}\\
  one-place relations & @{text "F\<^sup>1 = G\<^sup>1 =\<^sub>d\<^sub>f \<box>(\<forall>x xF\<^sup>1 \<equiv> xG\<^sup>1)"}\\
  zero-place relations & @{text "F\<^sup>0 = G\<^sup>0 =\<^sub>d\<^sub>f [\<lambda>y F\<^sup>0] = [\<lambda>y G\<^sup>0]"}
\end{tabular}

The identity for @{text "n"}-place relations with @{text "n \<ge> 2"} is defined in terms of the
identity of one-place relations, see (\ref{PM-p-identity})@{cite PM} for the full details.

The identity for ordinary objects follows Leibniz's law of the identity of indiscernibles:
Two ordinary objects that necessarily exemplify the same properties are identical.
Abstract objects, however, are only identical if they necessarily \emph{encode} the same
properties. As mentioned in the previous section this goes along with the concept of
abstract objects as the reification of property patterns.
Notably the identity for properties has a different definition than one would expect from
classical logic. Classically two properties are considered identical if and only if they
necessarily are \emph{exemplified} by the same objects. The Theory of Abstract Objects, however,
defines two properties to be identical if and only if they are necessarily \emph{encoded} by
the same (abstract) objects. This has some interesting consequences that will be considered
in more detail in section \ref{hyperintensionality} that describes the \emph{hyperintensionality}
of relations in the theory. 

*}

section{* The Axioms *}
  
text{*

Based on the language above an axiom system is defined that constructs a S5 modal logic with
an actuality operator, axioms for definite descriptions that go along with Russell's analysis
of descriptions, the substitution for identicals as per the defined identity, @{text "\<alpha>"}-,
@{text "\<beta>"}-, @{text "\<eta>"}- and a special @{text "\<iota>"}-conversion for @{text "\<lambda>"}-expressions, as well
as dedicated axioms for encoding. A full accounting of the axioms in their representation in the
embedding is found in section~\ref{axioms}. For the original axioms refer to @{cite \<open>chap. 8\<close> PM}.
At this point the axioms of encoding are the most relevant, namely:

  \begin{itemize}
    \item @{text "xF \<rightarrow> \<box>xF"}
    \item @{text "O!x \<rightarrow> \<not>\<exists>F xF"}
    \item @{text "\<exists>x (A!x & \<forall>F (xF \<equiv> \<phi>))"},\\ provided x doesn't occur free in @{text "\<phi>"}
  \end{itemize}

So encoding is modally rigid, ordinary objects do not encode properties and
most importantly the comprehension axiom for abstract objects that was already mentioned above:

For every condition on properties @{text "\<phi>"} there exists an abstract object, that encodes exactly
those properties, that satisfy @{text "\<phi>"}.

*}

section{* Hyperintensionality *}
  
text{*

\label{hyperintensionality}

An interesting property of the Theory of Abstract Objects results from the definition
of identity of one-place relations. Recall that two properties are defined to be identical
if and only if they are \emph{encoded} by the same (abstract) objects. Further note that
the theory imposes no restrictions whatsoever on which properties an abstract object encodes.
Let for example @{text "F"} be the property \emph{being the morning star} and @{text "G"} be the
property \emph{being the evening star}. Now since the morning star and the evening star are
actually both the planet Venus, every object that \emph{exemplifies} @{text "F"} will also
\emph{exemplify} @{text "G"} and vice-versa: @{text "\<box>\<forall>x Fx \<equiv> Gx"}. However the concept of being
the morning star is different from the concept of being the evening star. The Theory of Abstract
Object therefore does not prohibit the existence of an abstract object that \emph{encodes} @{text "F"},
but does \emph{not} encode @{text "G"}. Therefore by the definition of identity for properties
it does \emph{not} hold that @{text "F = G"}. As a matter of fact the Theory of Abstract Object
does not force @{text "F = G"} for any @{text "F"} or @{text "G"}. It rather stipulates what needs
to be proven, if @{text "F = G"} is to be established, namely that they are necessarily encoded by
the same objects. Therefore if two properties \emph{should} be equal in some context an axiom has to be added
to the theory that allows it to prove that both properties are encoded by the same abstract objects.

To understand the extent of this \emph{hyperintensionality} of the theory consider that the
following are \emph{not} necessarily equal in object theory:

\begin{center}
    @{text "[\<lambda>y p \<or> \<not>p]"} and @{text "[\<lambda>y q \<or> \<not>q]"}\\
    @{text "[\<lambda>y p & q]"} and @{text "[\<lambda>y q & p]"}
\end{center}

Of course the theory can be extended in such a way that these properties are equal, namely by
introducing a new axiom that requires that they are necessarily encoded by the same abstract objects.
Without additional axioms, however, it is not provable that above properties are equal.

As outlined in the next chapter the hyperintensionality of the theory is a particular challenge
for the representation of the theory in a shallow embedding (TODO: reference).

Furthermore it is important to note that the theory is only hyperintensional in exactly the sense
described above. Propositional reasoning is still governed by classical extensionality (TODO: be more precise).

*}
  
section{* The Aczel-Model *}

text{*
\label{aczel-model}

When thinking about a model for the theory one will quickly notice the following problem:
The comprehension axiom for abstract objects implies that for each set of properties there
exists an abstract object, hence there exists an injective map from the power set of properties
to the set of abstract objects. On the other hand for an object @{text "y"} the term
\mbox{@{text "[\<lambda>x Rxy]"}} constitutes a property. If for distinct objects these properties were always
distinct, this would result in a violation of Cantor's theorem, since this would mean that
there is an injective map from the power set of properties to the set of properties. So the question
is, does the Theory of Abstract Objects as constructed above have a model? An answer was provided
by Peter Aczel who proposed the model structure illustrated in figure~\ref{aczel-model-graphic}
(in fact to our knowledge Dana Scott proposed a first model for the theory before Peter Aczel
that we believe is a special case of an Aczel model).

\begin{figure}[h]
  \caption{Illustration of the Aczel-Model}
  \includegraphics[width=\textwidth]{aczel-model.pdf}
  \label{aczel-model-graphic}
\end{figure}

In an Aczel model abstract objects are represented by sets of properties. This of course validates
the comprehension axiom of abstract objects. Properties on the other hand are not naively represented
by sets of objects, which would lead to a violation of Cantor's theorem, but rather as the sets of
\emph{urelements}. Urelements are partitioned into two groups, ordinary urelements
(@{text "C"} in the illustration) and special urelements (@{text "S"} in the illustration).
Ordinary urelements can serve as the denotations of ordinary objects. Every abstract object on
the other hand has a special urelement as its proxy. Which properties an abstract object exemplifies
now solely depends on its proxy. However, the map from abstract objects to special urelements is
not injective, so more than one abstract object can share the same proxy. This way a violation of
Cantor's theorem is avoided. As a consequence there are abstract objects, that are
exemplification-indistinguishable. Interestingly the existence of abstract objects
that are exemplification-indistinguishable is a theorem of the Theory of Abstract Objects, see
(\ref{PM-aclassical2})@{cite PM}.

Note that although the Aczel-model illustrated in figure~\ref{aczel-model-graphic} is non-modal,
the extension to a modal version is straightforward by introducing primitive possible worlds
as in the Kripke semantics of modal logic.

Also note that the Aczel-model in figure~\ref{aczel-model-graphic} is \emph{extensional}.
Since properties are represented as the power set of urelements, two properties are in fact
equal if they are exemplified by the same objects. This has no bearing on the soundness of the
Aczel-model as a model for the Theory of Abstract Objects, but it has the consequence, that
statements like @{text "[\<lambda> p \<or> \<not>p] = [\<lambda> q \<or> \<not>q]"} are true in the model, although they are not
derivable from the axioms of object theory as explained in the previous section.

For this reason an \emph{intensional} variant of the Aczel-model is developed and used as the
basis of the embedding. The technicalities of this model are described in the next chapter.

*}
  
chapter{* The Embedding *}

section{* Background *}

text{*
The background theory for the embedding is Isabelle/HOL, that provides a higher order logic
that serves as meta-logic. For a short overview of the extents of the background theory
see \cite{WhatsInMain}.

TODO: what more to say about Isabelle/HOL?

TODO: overview section? Reorder the sections?

TODO: explain color distinction between embedded and meta-logic somewhere.

*}
  
section{* Challenges *}

text{*
\label{challenges}
TODO: russell style paradox; hyperintensionality revisited; relations vs. functions revisited; general complexity, etc.
*}

subsection{* A Russell-style Paradox *}

text{*
  \label{russell-paradox}

  One of the major challenges of an implementation of the Theory of Abstract Objects in functional
  logic is the fact that the naive representation of the @{text "\<lambda>"}-expressions of the theory using the
  unrestricted, @{text "\<beta>"}-convertible @{text "\<lambda>"}-expressions of functional logic results in the following
  paradox (see @{cite \<open>p. 24-25\<close> rtt}):

  Assume @{text "[\<lambda>x \<exists>F (xF & \<not>Fx)]"} were a valid @{text "\<lambda>"}-expression denoting a relation.
  Now the comprehension axiom of abstract objects requires the following:

  \begin{center}
    @{text "\<exists>x (A!x & \<forall>F (xF \<equiv> F = [\<lambda>x \<exists>F (xF & \<not>Fx)]))"}
  \end{center}

  So there is an abstract object that encodes only the property @{text "[\<lambda>x \<exists>F (xF & \<not>Fx)]"}.
  Let @{text "b"} be such an object. Now first assume @{text "b"} exemplifies
  @{text "[\<lambda>x \<exists>F (xF & \<not>Fx)]"}. By @{text "\<beta>"}-reduction this implies that there exists a property, that
  @{text "b"} encodes, but does not exemplify. Since @{text "b"} only encodes @{text "[\<lambda>x \<exists>F (xF & \<not>Fx)]"},
  but does also exemplify it by assumption this is a contradiction.

  Now assume @{text "b"} does not exemplify @{text "[\<lambda>x \<exists>F (xF & \<not>Fx)]"}. By @{text "\<beta>"}-reduction it
  follows that there does not exist a property that @{text "b"} encodes, but does not exemplify.
  Since @{text "b"} encodes @{text "[\<lambda>x \<exists>F (xF & \<not>Fx)]"} by construction and does not exemplify
  it by assumption this is again a contradiction.

  This paradox is prevented in the formulation of object theory by disallowing encoding
  subformulas in @{text "\<lambda>"}-expressions, so in particular @{text "[\<lambda>x \<exists>F (xF & \<not>Fx)]"} is not
  part of the language. However during the construction of the embedding it was discovered
  that this restriction is not sufficient to prevent paradoxes in general. This is discussed
  in section~\ref{paradox}. The solution used in the embedding is described in
  section~\ref{lambda-expressions}.
*}  

subsection{* Hyperintensionality of Relations *}

section{* Basic Concepts *}

text{*

The introduction mentioned that shallow semantical embeddings were used to successfully represent
different varieties of modal logic by implementing them using Kripke semantics. The advantage here
is that Kripke semantics is well understood and there are extensive results about its completeness
(TODO: reference).

For the Theory of Abstract Object the situation is different. Although it is believed that
Aczel-models are sound, section~\ref{aczel-model} already established that even a modal version
of the traditional Aczel-model is extensional and therefore theorems are true in it,
that are not derivable from the axioms of object theory.

*}

subsection{* Hyperintensional Aczel-model *}
  
text{*

\label{hyper-aczel-model}

As mentioned in section~\ref{aczel-model} it is straightforward to extend
the traditional (non-modal) Aczel-model to a modal version by introducing
primitive possible worlds following the Kripke semantics for a modal S5 logic.

Relations in the resulting Aczel-model are, however, still \emph{extensional}.
Two relations that are necessarily exemplified by the same objects are equal. 
The Aczel-model that is used as the basis for the embedding therefore introduces
\emph{states} as another primitive besides possible worlds. Truth values are now
represented as ternary functions from states and possible worlds to booleans,
relations as functions from urelements, states and possible worlds to booleans.

Abstract objects are still defined as sets of one-place relations and the division
of urelements into ordinary urelements and special urelements, that serve as proxies
for abstract objects is retained as well. Consequently encoding is still defined
as set membership of a relation in an abstract object and exemplification still defined
as function application of the relation to the urelement corresponding to an individual.

The semantical truth evaluation of a proposition in a given possible world, is defined
to its evaluation for a designated \emph{actual state} and the possible world.

Logical connectives are defined to behave classically in the \emph{actual state}, but
have undefined behavior in any other state.

The reason for this construction becomes apparent if one considers the definition of
the identity of relations: relations are considered identical if they are \emph{encoded}
by the same abstract objects. Encoding now depends on the behavior of the relation in
all states. Now two relations can still necessarily be \emph{exemplified} by the
same objects in the actual state, but still not be identical, since they have different
behavior in other states. Therefore hyperintensionality of relations is achieved.

The dependency on states is not limited to relations, but introduced to all propositions,
connectives and quantifiers to allow the definition of @{text "\<lambda>"}-expressions 
in section~\ref{lambda-expressions}.

The implementational details will be explained throughout section~\ref{representation-layer}.

TODO: improve this section.
*}

subsection{* Layered Structure *}
  
text{*

Although the constructed variant of the Aczel-model preserves the hyperintensionality of the
theory at least to some degree, it is still known that there are true theorems in this model
that are not derivable from the axioms of object theory. TODO: reference later section.

Given this lack of a model with a well-understood degree of completeness, the embedding uses
a different approach than other semantical embeddings, namely the embedding is divided into
several \emph{layers} as follows:

\begin{itemize}
  \item The first layer represents the primitives of PLM using a hyper-intensional variant of the
        Aczel-model.
  \item In a second layer the objects of the embedded logic constructed in the first layer are
        considered as primitives and some of their semantic properties are derived using the
        background logic as meta-logic.
  \item The third layer derives the axiom system of PLM mostly using the semantics of the second
        layer and partly using the meta-logic directly.
  \item Based on the third layer the deductive system PLM as described in @{cite \<open>Chap. 9\<close> PM}
        is derived solely using the axiom system of the third layer and the meta-rules stated
        in PLM. The meta-logic and the properties of the representation layer are explicitly
        not used in any proofs. Thereby the reasoning in the third layer is independent of the
        first two layers.
\end{itemize}

The reasoning behind this approach is the following:
The first layer provides a representation of the embedded logic that is provably consistent.
Only minimal axiomatization is necessary, whereas the main construction is purely definitional.
Since the subsequent layers don't contain any additional axiomatization (the axiom system in layer three
is \emph{derived}) their consistency is thereby guaranteed as well.

The second layer tries to abstract from the details of the representation by implementing an
approximation of the preliminary formal semantics of PLM\footnote{Our thanks to Edward Zalta for supplying
us with a preliminary version.}. The long time goal would be to arrive at the representation
of a complete semantics in this layer, that would be sufficient to derive the axiom system in the
next layer and which any specific model structure would have to satisfy. Unfortunately this could not
be achieved so far, but it was possible to lay some foundations for future work.

At the moment full abstraction from the representation layer is only achieved after deriving the axiom
system in the third layer. Still it can be reasoned that in any model of object theory the axiom system
has to be derivable and therefore by disallowing all further proofs to rely on the meta-logic and the
model structure directly the derivation of the deductive system PLM should be universal. The only
exceptions are the primitive meta-rules of PLM: modus ponens, RN (necessitation) and
GEN (universal generalisation), as well as the deduction rule. These rules do not follow from the axiom system
itself, but are derived from the semantics in the second layer (see~\ref{PLM-metarules}).
Still as the corresponding semantical rules will again have to be derivable for \emph{any} model,
this does not have an impact on the universality of the subsequent reasoning.

There remains one issue, though. Since the logic of PLM is formulated in relational type theory,
whereas Isabelle/HOL employs functional reasoning some formulations have to be adjusted to be representable
and there may still be some reservations about the accuracy of the representation of the axiom system.
This issue is addressed in section (TODO: reference).

The next sections will now describe the technical details of the embedding.

*}

section{* The Representation Layer *}
  
text{*

\label{representation-layer}

The first layer of the embedding (see \ref{TAO_Embedding}) implements the variant
of the Aczel-model described in section~\ref{hyper-aczel-model} and builds a representation
of the language of PLM in the logic of Isabelle/HOL. This process is outlined step by step
throughout this section.

*}
  
subsection{* Primitives *}

text{*
The following primitive types are the basis of the embedding (see \ref{TAO_Embedding_Primitives}):

\begin{itemize}
  \item Type @{type i} represents possible worlds in the Kripke semantics.
  \item Type @{type j} represents \emph{states} as decribed in section~\ref{hyper-aczel-model}.
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

Based on the primitive types above the following types are defined (see \ref{TAO_Embedding_Derived_Types}):

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
        (in this case type @{type \<nu>}) and an additional special element called @{term "None"}.
        @{term "None"} is used to represent individual terms that are definite descriptions
        that are not logically proper (i.e. they do not denote an individual).
\end{itemize}

\begin{remark}
  The Isabelle syntax @{theory_text "typedef \<o> = UNIV::(j\<Rightarrow>i\<Rightarrow>bool) set morphisms eval\<o> make\<o> .."}
  found in the theory source in the appendix introduces a new abstract type @{type \<o>} that is represented
  by the full set (@{term UNIV})   of objects of type @{typ "j\<Rightarrow>i\<Rightarrow>bool"}. The morphism @{text "eval\<o>"} maps
  an object of abstract type @{type \<o>} to its representative of type @{typ "j\<Rightarrow>i\<Rightarrow>bool"}, whereas 
  the morphism @{text "make\<o>"} maps an object of type @{typ "j\<Rightarrow>i\<Rightarrow>bool"} to the object
  of type @{type \<o>} that is represented by it. Defining these abstract types makes it
  possible to consider the defined types as primitives in later stages of the embedding,
  once their meta-logical properties are derived from the underlying representation.
  For a theoretical analysis of the representation layer the type @{type \<o>} can be considered
  a synonym of @{typ "j\<Rightarrow>i\<Rightarrow>bool"}.

  The Isabelle syntax @{theory_text "setup_lifting type_definition_\<o>"} allows definitions for the
  abstract type @{type \<o>} to be stated directly for its representation type @{typ "j\<Rightarrow>i\<Rightarrow>bool"}
  using the syntax @{theory_text "lift_definition"}.

  In the remainder of this document these morphisms are omitted and definitions are stated
  directly for the representation types.
\end{remark}

*}

subsection{* Individual Terms and Definite Descriptions *}

text{*
\label{individual-terms-and-descriptions}

There are two basic types of individual terms in PLM: definite descriptions and individual variables.
For any logically proper definite description there is an individual variable that denotes
the same object. A definite description is logically proper if its matrix is true for a unique
object.

In the embedding the type @{type \<kappa>} encompasses all individual terms, i.e. individual variables
\emph{and} definite descriptions. To use an individual variable (of type @{type \<nu>}) as in place of
an object of type @{type \<kappa>} the decoration @{term "embedded_style (DUMMY\<^sup>P)"} is introduced
(see \ref{TAO_Embedding_IndividualTerms}):

\begin{center}
  @{thm \<nu>\<kappa>.rep_eq[where x=x, THEN embedded_meta_eq]}
\end{center}

The expression @{term "embedded_style (x\<^sup>P)"} (of type @{typeof "x\<^sup>P"}) is now marked to always be
logically proper (it can only be substituted by objects that are internally of the form @{term "Some x"})
and to always denote the same object as the individual variable @{term "x"}.

It is now possible to define definite descriptions as follows:

\begin{center}
  @{thm that.rep_eq[where x=\<phi>, THEN embedded_meta_eq]}
\end{center}

If the propriety condition of a definite description @{prop "\<exists>!x. \<phi> x dj dw"} holds,
i.e. \emph{there exists a unique @{term "x"}, such that @{term "\<phi> x"} holds for the actual state and
the actual world}, the term @{term "\<^bold>\<iota>x . \<phi> x"} is represented by @{term "Some (THE x . \<phi> x dj dw)"}.
Isabelle's @{theory_text THE} operator evaluates to the unique object, for which the given condition holds,
if there is a unique such object, and is undefined otherwise. If the propriety condition does not hold,
the term is represented by @{term "None"}.

The following meta-logical functions are defined to aid in handling individual terms:

\begin{itemize}
  \item @{thm[display] proper.rep_eq}
  \item @{thm[display] rep.rep_eq}
\end{itemize}

@{term "the"} maps an object of type @{typ "'a option"} that is of the form @{term "Some x"} to
@{term "x"} and is undefined for @{term "None"}. For an object of type @{type \<kappa>} the expression
@{term "proper x"} is therefore true, if the term is logically proper, and if this is the case,
the expression @{term "rep x"} evaluates to the individual of type @{type \<nu>} that the term denotes.
*}

subsection{* Mapping from Individuals to Urelements *}

text{*

To map abstract objects to urelements (for which relations can be evaluated), a constant
@{term \<alpha>\<sigma>} of type @{typeof \<alpha>\<sigma>} is introduced, which maps abstract objects (of type @{type \<alpha>})
to special urelements (of type @{type \<sigma>}), see \ref{TAO_Embedding_AbstractObjectsToSpecialUrelements}.

To assure that every object in the full domain of urelements actually is an urelement for (one or more)
individual objects, the constant @{term \<alpha>\<sigma>} is axiomatized to be surjective.

Now the mapping @{term "\<nu>\<upsilon>"} of type @{typeof "\<nu>\<upsilon>"} can be defined as follows:

\begin{center}
@{thm \<nu>\<upsilon>_def[atomize]}
\end{center}

To clarify the syntax note that this is equivalent to the following:

\begin{center}
@{lemma "(\<forall> x . \<nu>\<upsilon> (\<omega>\<nu> x) = \<omega>\<upsilon> x) \<and> (\<forall> x . \<nu>\<upsilon> (\<alpha>\<nu> x) = \<sigma>\<upsilon> (\<alpha>\<sigma> x))" by (simp add: \<nu>\<upsilon>_def)}
\end{center}

So ordinary objects are simply converted to an urelements by the type constructor
@{term "\<omega>\<upsilon>"} for ordinary urelements, whereas for abstract objects the corresponding
special urelement under @{text "\<alpha>\<sigma>"} is converted to an urelement by the type constructor
@{term "\<sigma>\<upsilon>"} for special urelements.

\begin{remark}
  Note that it may make sense to let the mapping from individuals to urelements depend
  on states. This is discussed in more detail in section TODO: reference.
\end{remark}

*}

subsection{* Exemplification of n-place relations *}

text{*
  Exemplification of n-place relations can now be defined. Exemplification of zero-place
  relations is simply defined as the identity, whereas exemplification of n-place relations
  for @{text "n \<ge> 1"} is defined to be true, if all individual terms are logically proper and
  the function application of the relation to the urelements corresponding to the individuals
  yields true for a given possible world and state (see \ref{TAO_Embedding_Exemplification}):
  \begin{itemize}
    \item @{thm[display] exe0.rep_eq[where x=p, THEN embedded_meta_eq]}
    \item @{thm[display] exe1.rep_eq[where x=F and xa=x, THEN embedded_meta_eq]}
    \item @{thm[display] exe2.rep_eq[where x=F and xa=x and xb=y, THEN embedded_meta_eq]}
    \item @{thm[display] exe3.rep_eq[where x=F and xa=x and xb=y and xc=z, THEN embedded_meta_eq]}
  \end{itemize}
*}

subsection{* Encoding *}

text{*
  Encoding can now be defined as follows (see \ref{TAO_Embedding_Encoding}):

  \begin{center}
  @{thm enc.rep_eq[of x F, THEN embedded_meta_eq]}
  \end{center}

  That is for a given state @{term s} and a given possible world @{term w} it holds that
  an individual term @{term x} encodes @{term F}, if @{term x} is logically proper,
  the representative individual variable of @{term x} is of the form @{term "\<alpha>\<nu> \<alpha>"} for
  some abstract object @{term \<alpha>} and @{term F} is contained in @{term \<alpha>} (remember that
  abstract objects are defined to be sets of one-place relations). Also note that encoding
  is a represented as a function of possible worlds and states to ensure type-correctness,
  but its evaluation does not depend on either. On the other hand whether @{term F} is contained
  in @{term \<alpha>} actually does depend on the behavior of @{term F} in \emph{all} states.
*}

subsection{* Connectives and Quantifiers *}

text{*
  \label{connectives}

  Following the model described in section~\ref{hyper-aczel-model} the connectives and quantifiers
  are defined in such a way that they behave classically if evaluated for the designated actual state @{term "dj"},
  whereas their behavior is governed by uninterpreted constants in any other state.

  For this purpose the following uninterpreted constants are introduced (see \ref{TAO_Embedding_Connectives}):
  \begin{itemize}
    \item @{const I_NOT} of type @{typeof I_NOT}
    \item @{const I_IMPL} of type @{typeof I_IMPL}
  \end{itemize}

  Modality is represented using the dependency on primitive possible worlds using
  a standard Kripke semantics for a S5 modal logic.

  The basic connectives and quantifiers are now defined as follows
  (see \ref{TAO_Embedding_Connectives}):
  \begin{itemize}
    \item @{thm[display] not.rep_eq[of p, THEN embedded_meta_eq]}
    \item @{thm[display] impl.rep_eq[of p q, THEN embedded_meta_eq]}
    \item @{thm[display] forall\<^sub>\<nu>.rep_eq[of \<phi>, rename_abs s w x, THEN embedded_meta_eq]}
    \item @{thm[display] forall\<^sub>0.rep_eq[of \<phi>, rename_abs s w p, THEN embedded_meta_eq]}
    \item @{thm[display] forall\<^sub>1.rep_eq[of \<phi>, rename_abs s w F, THEN embedded_meta_eq]}
    \item @{thm[display] forall\<^sub>2.rep_eq[of \<phi>, rename_abs s w F, THEN embedded_meta_eq]}
    \item @{thm[display] forall\<^sub>3.rep_eq[of \<phi>, rename_abs s w F, THEN embedded_meta_eq]}
    \item @{thm[display] box.rep_eq[of p, THEN embedded_meta_eq]}
    \item @{thm[display] actual.rep_eq[of p, THEN embedded_meta_eq]}
  \end{itemize}

  Note in particular that the definition of negation and implication behaves
  classically if evaluated for the actual state @{term "s = dj"}, but
  is governed by the uninterpreted constants @{term I_NOT} and @{term I_IMPL} for
  @{term "s \<noteq> dj"}:

  \begin{itemize}
  \item @{lemma[display] "s = dj \<longrightarrow> eval\<o> (embedded_style (\<^bold>\<not>p)) s w = (\<not>eval\<o> (embedded_style (p)) s w)"
          by (unfold embedded_style_def, transfer, auto)}
  \item @{lemma "s \<noteq> dj \<longrightarrow> eval\<o> (embedded_style (\<^bold>\<not>p)) s w = (I_NOT (eval\<o> (embedded_style (p))) s w)"
          by (unfold embedded_style_def, transfer, auto)}
  \item @{lemma[display] "s = dj \<longrightarrow> eval\<o> (embedded_style (p \<^bold>\<rightarrow> q)) s w = (eval\<o> (embedded_style p) s w \<longrightarrow> eval\<o> (embedded_style q) s w)"
          by (unfold embedded_style_def, transfer, auto)}
  \item @{lemma "s \<noteq> dj \<longrightarrow> eval\<o> (embedded_style (p \<^bold>\<rightarrow> q)) s w = (I_IMPL (eval\<o> (embedded_style p)) (eval\<o> (embedded_style q)) s w)"
          by (unfold embedded_style_def, transfer, auto)}
  \end{itemize}

  \begin{remark}
    It may be that non-classical behavior in states @{term "s \<noteq> dj"}
    for negation and implication is found not to be sufficient for achieving the
    desired level of hyperintensionality. It would be trivial to introduce additional
    uninterpreted constants to govern the behavior of the remaining connectives and quantifiers
    in such states as well, though. The remainder of the embedding would not be affected, i.e.
    no assumption about the behavior of connectives and quantifiers in states other than @{term "dj"}
    is made in the subsequent reasoning.
  \end{remark}

*}
  
subsection{* $\lambda$-Expressions *}
  
text{*

  \label{lambda-expressions}

  The bound variables of the @{text "\<lambda>"}-expressions of the embedded logic are individual
  variables, whereas relations are represented as functions acting on urelements.
  Therefore the definition of the @{text "\<lambda>"}-expressions of the embedded logic is non-trivial.
  The embedding defines them as follows (see \ref{TAO_Embedding_Lambda}):

  \begin{itemize}
    \item @{thm[display] lambdabinder0.rep_eq[of p, THEN embedded_meta_eq]}
    \item @{thm[display] lambdabinder1.rep_eq[of \<phi>, THEN embedded_meta_eq]}
    \item @{thm[display, eta_contract=false] lambdabinder2.rep_eq[of "\<lambda> x y . \<phi> x y", THEN embedded_meta_eq]}
    \item @{thm[display, eta_contract=false] lambdabinder3.rep_eq[of "\<lambda> x y z . \<phi> x y z", THEN embedded_meta_eq]}
  \end{itemize}

\begin{remark}
  For technical reasons Isabelle only allows @{text "\<lambda>"}-expressions for one-place relations
  to use a nice binder notation. Although better workarounds may be possible, for now the
  issue is avoided by the use of the primitive @{text "\<lambda>"}-expressions of the background
  logic in combination with the constants @{term "\<^bold>\<lambda>\<^sup>2"} and @{term "\<^bold>\<lambda>\<^sup>3"} as shown above.
\end{remark}

  The representation of zero-place @{text "\<lambda>"}-expressions as the identity is straight-forward,
  the representation of n-place @{text "\<lambda>"}-expressions for \mbox{@{text "n \<ge> 1"}} is illustrated
  for the case \mbox{@{text "n = 1"}}:

  The matrix of the @{text "\<lambda>"}-expression @{term "embedded_style \<phi>"} is a function from individuals
  (of type @{type \<nu>}) to truth values (of type @{type \<o>}, resp. @{typ "j\<Rightarrow>i\<Rightarrow>bool"}).
  One-place relations are represented as functions of type @{typ "\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool"}, though,
  where @{type \<upsilon>} is the type of urelements.

  The result of the evaluation of a @{text "\<lambda>"}-expression @{term "embedded_style (\<^bold>\<lambda>x. \<phi> x)"} for an urelment @{term u},
  a state @{term s} and a possible world @{term w}) is given by the following equation:

  \begin{center}
  @{lemma "eval\<Pi>\<^sub>1 (embedded_style (\<^bold>\<lambda>x . \<phi> x)) u s w = (\<exists> x . \<nu>\<upsilon> x = u \<and> eval\<o> (embedded_style (\<phi> x)) s w)"
    by (simp add: embedded_style_def meta_defs meta_aux)}
  \end{center}

  Note that @{term "\<nu>\<upsilon>"} is bijective for ordinary objects and therefore:

  \begin{center}
  @{lemma "eval\<Pi>\<^sub>1 (embedded_style (\<^bold>\<lambda>x . \<phi> x)) (\<omega>\<upsilon> u) s w = eval\<o> (embedded_style (\<phi>) (\<omega>\<nu> u)) s w"
    by (simp add: embedded_style_def meta_defs meta_aux, metis \<nu>.exhaust \<nu>\<upsilon>_\<omega>\<nu>_is_\<omega>\<upsilon> \<upsilon>.inject(1) no_\<alpha>\<omega>)}
  \end{center}

  However in general @{term "\<nu>\<upsilon>"} can map several abstract objects to the same special urelement,
  so an analog statement for abstract objects does not hold for arbitrary @{term "\<phi>"}. As described
  in section~\ref{russell-paradox} such a statement would in fact not be desirable, since it would
  lead to inconsistencies.

  Instead the embedding introduces the concept of \emph{proper maps}.
  A map from individuals to propositions is defined to be proper if its truth evaluation for the actual state only
  depends on the urelement corresponding to the individual (see \ref{TAO_Embedding_Proper}):

  \begin{itemize}
    \item @{thm[display] IsProperInX.rep_eq[of \<phi>]}
    \item @{thm[display] IsProperInXY.rep_eq[of \<phi>]}
    \item @{thm[display] IsProperInXYZ.rep_eq[of \<phi>]}
  \end{itemize}

  Now by the definition of proper maps the evaluation of @{text "\<lambda>"}-expressions behaves as expected:

  \begin{center}
  @{lemma "IsProperInX \<phi> \<longleftrightarrow> (\<forall> w x . eval\<Pi>\<^sub>1 (embedded_style (\<^bold>\<lambda>x . \<phi> (x\<^sup>P))) (\<nu>\<upsilon> x) dj w = eval\<o> (embedded_style (\<phi> (x\<^sup>P))) dj w)"
    by (auto simp: embedded_style_def meta_defs meta_aux IsProperInX_def)}
  \end{center}

  \begin{remark}
    Note that the above equation does not quantify over all states, but is only true for the actual state @{term "dj"}.
    This is sufficient given that truth evaluation only depends on the actual state (see TODO: reference)
    and goes along with the desired semantics of @{text "\<lambda>"}-expressions (see TODO: reference).
  \end{remark}

  The concept behind this is that maps that contain encoding formulas in its argument are in general
  not proper and thereby the paradox mentioned in section~\ref{russell-paradox} is avoided.

  In fact proper maps are the most general kind of functions that may appear in a lambda-expression,
  such that @{text "\<beta>"}-conversion holds. In what way proper maps correspond to the formulas that PLM
  allows as the matrix of a @{text "\<lambda>"}-expression is a complex question and discussed seperately in
  section TODO: reference. A detailed discussion about the denotations of \emph{improper}
  lambda-expression and how the mentioned paradox is avoided precisely is presented in section
  TODO: reference (same section as before?).
*}
 

subsection{* Validity *}

text{*
  A formula is considered semantically valid for a possible world @{term v} if it evaluates
  to @{term True} for the actual state @{term dj} and the given possible world @{term v}.
  Semantic validity is defined as follows (see \ref{TAO_Embedding_Validity}):
  
  \begin{center}
    @{thm valid_in.rep_eq[of v "embedded_style \<phi>"]}
  \end{center}

  This way the truth evaluation of a proposition only depends on the evaluation of its functional representative
  for the actual state @{term dj}. Remember that for the actual state the connectives and quantifiers
  are defined to behave classically. In fact the only formulas of the embedded logic whose truth
  evaluation \emph{does} depend on all states are formulas containing encoding expressions.

  \begin{remark}
    The Isabelle Theory in the appendix defines the syntax @{text "v \<Turnstile> p"} in the representation
    layer, as this is the syntax used in the preliminary formal semantics of PLM.
    The syntax @{term "[p in v]"} that is easier to use in Isabelle due to bracketing the expression
    is only introduced after the semantics is derived in \ref{TAO_Semantics_Validity}.
    For simplicity only the latter syntax is used in this document.
  \end{remark}
*}

subsection{* Concreteness *}

text{*
  \label{concreteness}

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
  following way (see \ref{TAO_Embedding_Concreteness}):
  \begin{itemize}
    \item @{thm OrdinaryObjectsPossiblyConcreteAxiom}
    \item @{thm PossiblyContingentObjectExistsAxiom}
    \item @{thm PossiblyNoContingentObjectExistsAxiom}
  \end{itemize}

  Concreteness can now be defined as a one-place relation (see \ref{TAO_Embedding_Concreteness}):

  \begin{center}
  @{thm Concrete.rep_eq[THEN embedded_meta_eq]}
  \end{center}

  The equivalence of the axioms stated in the meta-logic and the notion of concreteness in Principia
  can now be verified (see \ref{TAO_SanityTests_MetaAxioms}):

  \begin{itemize}
    \item @{thm[display] SanityTests.OrdAxiomCheck[rename_abs x v y u z z]}
    \item @{thm[display] SanityTests.AbsAxiomCheck[rename_abs x v y u z z]}
    \item @{thm[display] SanityTests.PossiblyContingentObjectExistsCheck}
    \item @{thm[display] SanityTests.PossiblyNoContingentObjectExistsCheck}
  \end{itemize}
*}

subsection{* The Syntax of the Embedded Logic*}


text{*

The embedding aims to provide a readable syntax for the embedded logic that is as close as possible
to the syntax of PLM, that can be easily understood and that clearly distinguishes between the embedded
logic and the meta-logic. Some concessions have to be made due to the limitations of definable syntax
in Isabelle, though.

The syntax for the basic formulas of PLM used in the embedding is summarized in the
following table:

\begin{center}
\begin{tabular}{l|l|l|c}
PLM & syntax in words & embedded logic & type \\
\hline
@{text "p"} & it holds that @{text "p"} & @{term "embedded_style (p)"} & @{type \<o>} \\
@{text "\<not>p"} & not @{text "p"} & @{term "embedded_style (\<^bold>\<not>p)"} & @{type \<o>}  \\
@{text "p \<rightarrow> q"} & @{text "p"} implies @{text "q"} & @{term "embedded_style (p \<^bold>\<rightarrow> q)"} & @{type \<o>}  \\
@{text "\<Pi>\<upsilon>"} & @{text "\<upsilon>"} (an individual term) exemplifies @{text "\<Pi>"} & @{term "embedded_style \<lparr>\<Pi>,\<upsilon>\<rparr>"} & @{type \<o>}  \\
@{text "\<Pi>x"} & @{text "x"} (an individual variable) exemplifies @{text "\<Pi>"} & @{term "embedded_style \<lparr>\<Pi>,x\<^sup>P\<rparr>"} & @{type \<o>}  \\
@{text "\<Pi>\<upsilon>\<^sub>1\<upsilon>\<^sub>2"} & @{text "\<upsilon>\<^sub>1"} and @{text "\<upsilon>\<^sub>2"} exemplify @{text "\<Pi>"} & @{term "embedded_style \<lparr>\<Pi>,\<upsilon>\<^sub>1,\<upsilon>\<^sub>2\<rparr>"} & @{type \<o>}  \\
@{text "\<Pi>xy"} & @{text "x"} and @{text "y"} exemplify @{text "\<Pi>"} & @{term "embedded_style \<lparr>\<Pi>,x\<^sup>P,y\<^sup>P\<rparr>"} & @{type \<o>}  \\
@{text "\<Pi>\<upsilon>\<^sub>1\<upsilon>\<^sub>2\<upsilon>\<^sub>3"} & @{text "\<upsilon>\<^sub>1"}, @{text "\<upsilon>\<^sub>2"} and @{text "\<upsilon>\<^sub>3"} exemplify @{text "\<Pi>"} & @{term "embedded_style \<lparr>\<Pi>,\<upsilon>\<^sub>1,\<upsilon>\<^sub>2,\<upsilon>\<^sub>3\<rparr>"} & @{type \<o>}  \\
@{text "\<Pi>xyz"} & @{text "x"}, @{text "y"} and @{text "z"} exemplify @{text "\<Pi>"} & @{term "embedded_style \<lparr>\<Pi>,x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr>"} & @{type \<o>}  \\
@{text "\<upsilon>\<Pi>"} & @{text "\<upsilon>"} encodes @{text "\<Pi>"} & @{term "embedded_style \<lbrace>\<upsilon>,\<Pi>\<rbrace>"} & @{type \<o>}  \\
@{text "\<iota>x\<phi>"} & \emph{the} @{text "x"}, such that @{text "\<phi>"} & @{term "embedded_style (\<^bold>\<iota>x . \<phi> x)"} & @{type \<kappa>}  \\
@{text "\<forall>x(\<phi>)"} & for all individuals @{text "x"} it holds that @{text "\<phi>"} & @{term "embedded_style (\<^bold>\<forall>\<^sub>\<nu> x . \<phi> x)"} & @{type \<o>} \\
@{text "\<forall>p(\<phi>)"} & for all propositions @{text "x"} it holds that @{text "\<phi>"} & @{term "embedded_style (\<^bold>\<forall>\<^sub>0 x . \<phi> x)"} & @{type \<o>} \\
@{text "\<forall>F(\<phi>)"} & for all relations @{text "F"} it holds that @{text "\<phi>"} & @{term "embedded_style (\<^bold>\<forall>\<^sub>1 F . \<phi> F)"} & @{type \<o>} \\
& & @{term "embedded_style (\<^bold>\<forall>\<^sub>2 F . \<phi> F)"} & \\
& & @{term "embedded_style (\<^bold>\<forall>\<^sub>3 F . \<phi> F)"} & \\
@{text "[\<lambda> p]"} & being such that @{text "p"} & @{term "embedded_style (\<^bold>\<lambda>\<^sup>0 p)"}  & @{typ \<Pi>\<^sub>0} \\
@{text "[\<lambda>x \<phi>]"} & being @{text "x"} such that @{text "\<phi>"} & @{term "embedded_style (\<^bold>\<lambda> x . \<phi> x)"} & @{type \<Pi>\<^sub>1} \\
@{text "[\<lambda>xy \<phi>]"} & being @{text "x"} and @{text "y"} such that @{text "\<phi>"} & @{term[eta_contract=false] "embedded_style (\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<phi> x y))"} & @{type \<Pi>\<^sub>2} \\
@{text "[\<lambda>xyz \<phi>]"} & being @{text "x"}, @{text "y"} and @{text "z"} such that @{text "\<phi>"} & @{term[eta_contract=false] "embedded_style (\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<phi> x y z))"} & @{type \<Pi>\<^sub>3}
\end{tabular}
\end{center}

Several subtleties have to be considered:

\begin{itemize}
  \item @{term "n"}-place relations are only represented for \mbox{@{text "n \<le> 3"}}.
        As the resulting language is already expressive enough to represent the most interesting
        parts of the theory and analog implementations for \mbox{@{text "n > 3"}} would be trivial
        to implement, this is considered to be sufficient.
  \item There is a distinction between individual terms and variables. This circumstance
        was already mentioned in section~\ref{individual-terms-and-descriptions}: an individual term
        in PLM can either be an individual variable (or constant) or a definite description.
        Statements in PLM that use individual variables are represented using the decoration
        @{term "DUMMY\<^sup>P"}.
  \item Whereas conceptually in PLM if a general term @{term "\<phi>"} as it occurs in definite descriptions,
        quantifications and @{text "\<lambda>"}-expressions above contains a \emph{free} variable is used within
        the scope of a variable binding operator, the free occurrences of the variable are considered
        to be \emph{bound} by the operator. In the embedding this concept is replaced by considering
        @{term "\<phi>"} to be a \emph{function} and using the native concept of binding operators in
        Isabelle to convert this function to a term with bound variables. This concept is discussed
        in more detail in section TODO: reference.
  \item The representation layer of the embedding defines a separate quantifier for every type of
        variable in PLM. This is done to assure that only quantifications ranging over these types
        are part of the embedded language. The definition of a general quantifier in the representation layer
        could for example be used to quantify over individual \emph{terms} (of type @{type \<kappa>}), whereas
        only quantifications ranging over individuals (of type @{type \<nu>}) are part of the language of PLM.
        Once the semantics is introduced in section~\ref{semantics}, a \emph{type class} is introduced
        that is characterized by the semantics of all quantification and instantiated for all variable types.
        This way a general binder that can be used for all variable types can be defined. The details
        of this approach are explained in section~\ref{general-quantifier}.
\end{itemize}

The syntax used for stating that a proposition is semantically valid is the following:
\begin{center}
    @{term "[\<phi> in v]"}
\end{center}

In the expression above @{term "embedded_style \<phi>"} and @{term "v"} are free variables,
therefore stating the expression as a lemma will implicitly be a quantified statement over all
propositions @{term "embedded_style \<phi>"} and all possible worlds @{term "v"} (unless
@{term "embedded_style \<phi>"} was explicitly declared as a constant in the global scope).

TODO: talk about scopes?

TODO: constants vs. variables.

*}

(*<*)
context Semantics
begin
(*>*)

section{* Semantical Abstraction *}
  
text{*
\label{semantics}

The second layer of the embedding (see~\ref{TAO_Semantics}) abstracts away from the technicalities
of the representation layer and states the truth conditions for the formulas of the embedded logic
in a similar way as the (at the time of writing unpublished) preliminary semantics of object theory.

TODO: repeat more statements from the appendix throughout the section?
*}

subsection{* Domains and Denotation Functions *}
  
text{*
In order to do so the abstract types introduced in the representation layer
@{typ \<kappa>}, @{typ \<o>} resp. @{typ \<Pi>\<^sub>0}, @{typ \<Pi>\<^sub>1}, @{typ \<Pi>\<^sub>2} and @{typ \<Pi>\<^sub>3} are considered
as primitive types and assigned semantic domains: @{type R\<^sub>\<kappa>}, @{typ R\<^sub>0}, @{typ R\<^sub>1},
@{typ R\<^sub>2} and @{typ R\<^sub>3} (see~\ref{TAO_Semantics_Semantics_Domains}).

For the embedding the definition of these semantic domains is trivial, since the abstract types of
the representation layer are already modeled using a representation set. Therefore the semantic domains
for each type can simply be defined as the type of its representatives.

As a next step denotation functions are defined that assign each abstract type its semantic denotation
(see~\ref{TAO_Semantics_Semantics_Denotations}).
Note that the formal semantics of PLM does not a priori assume that every term has a denotation, therefore
the denotation functions are represented as functions that map to the @{text "option"} type of the
respective domain. This way they can either map a term to @{term "Some x"}, if the term denotes
@{term "x"}, or to @{term "None"}, if the term does not denote.

In the embedding all relation terms always denote, therefore the denotation functions @{term "d\<^sub>0"},
@{text "\<dots>"}, @{term "d\<^sub>3"} for relations can simply be defined as the type constructor @{term "Some"}.
Individual terms on the other hand are already represented by an @{text "option"} type,
so the denotation function @{term "d\<^sub>\<kappa>"} can be defined as the identity.

Moreover the primitive type of possible worlds @{type i} is used as the semantical domain of possible
worlds @{typ W} and the primitive actual world @{term "dw"} as the semantical actual world
@{term "w\<^sub>0"} (see~\ref{TAO_Semantics_Semantics_Actual_World}).

\begin{remark}
The definitions for semantical domains and denotations seem trivial. However, it must be considered that conceptually
the abstract types of the representation layer now have the role of primitive types. Although for
simplicity the last section regarded the type @{type \<o>} as synonym of @{typ "j\<Rightarrow>i\<Rightarrow>bool"}, it was
introduced as a distinct type for which the set of all functions of type @{typ "j\<Rightarrow>i\<Rightarrow>bool"} merely
serves as the underlying set of representatives. An object of type @{type \<o>} cannot directly be
substituted for a variable of type @{typ "j\<Rightarrow>i\<Rightarrow>bool"}. To do so it first has to be mapped to its
representative of type @{typ "j\<Rightarrow>i\<Rightarrow>bool"} by the use of the morphism @{term "eval\<o>"} that was introduced
in the type definition and omitted in the last section for the sake of readability. Therefore although
the definitions of the semantic domains and denotation functions may seem trivial, the domains are
different types than the corresponding abstract type and the denotation functions are functions between
distinct types (note the use of @{theory_text "lift_definition"} rather than @{theory_text "definition"} 
for the denotation functions in~\ref{TAO_Semantics_Semantics_Denotations} that allows to define
functions on abstract types in the terms of the underlying representation types).
\end{remark}

*}

subsection{* Exemplification and Encoding Extensions *}
  
text{*
Semantical truth conditions for exemplification formulas are defined using \emph{exemplification extensions}.
Exemplification extensions are functions relative to
semantical possible worlds that map objects in the domain of @{text "n"}-place relations to meta-logical truth
conditions in the case of @{text "n = 0"} and sets of @{text "n"}-tuples of objects in the domain
of individuals in the case of @{text "n \<ge> 1"}. Formally they are defined as follows
(see~\ref{TAO_Semantics_Semantics_Exemplification_Extensions}):

\begin{itemize}
  \item @{thm[display] ex0_def[expand2, of p w]}
  \item @{thm[display] ex1_def[expand2, of F w]}
  \item @{thm[display] ex2_def[expand2, of R w]}
  \item @{thm[display] ex3_def[expand2, of R w]}
\end{itemize}

The exemplification extension of a @{text "0"}-place relation is its evaluation for the actual state and the
given possible world. The exemplification extension of @{text "n"}-place relations \mbox{(@{text "n \<ge> 1"})}
in a possible world is the set of all (tuples of) \emph{individuals} that are mapped to an
\emph{urelement} for which the relation evaluates to true for the given possible world and the
actual state. This is in accordance with the constructed Aczel-model (see~\ref{hyper-aczel-model}.

It is important to note that the concept of exemplification extensions as maps to sets of \emph{individuals}
is independent of the underlying model and in particular does not need the concept of \emph{urelements}
as they are present in an Aczel-model. The definition of truth conditions by the use of their
exemplification extensions is therefore an abstraction away from the technicalities
of the representation layer.

Similarly to the exemplification extensions for one-place relations an \emph{encoding extension}
is defined as follows (see~\ref{TAO_Semantics_Semantics_Encoding_Extension}):

\begin{center}
  @{thm en_def[expand1, of F]}
\end{center}

The encoding extension of a relation is defined as the set of all abstract objects that contain
the relation. This is again in accordance with the Aczel-model. Since encoding is modally rigid
the encoding extension does not need to be relativized for possible worlds.
*}

subsection{* Truth Conditons of Formulas *}

text{*

On the basis of the semantical definitions above it is now possible to define truth conditions
for the atomic formulas of the language.

For exemplification formulas of @{text "n"}-place relations
it suffices to consider the case of one-place relations, for which the truth condition is defined
as follows (see~\ref{TAO_Semantics_Semantics_Exemplification}):

\begin{center}
  @{thm T1_1[of w "embedded_style \<Pi>" "embedded_style \<kappa>"]}
\end{center}

The relation term @{term "embedded_style \<Pi>"} is exemplified by an individual term @{term "embedded_style \<kappa>"} in a possible world
@{term "w"} if both terms have a denotation and the denoted individual is contained in the exemplification
extension of the denoted relation in @{term "w"}. The definitions for @{text "n"}-place relations
\mbox{(@{text "n > 1"})} and @{text "0"}-place relations are analog.

The truth condition for encoding formulas is defined in a similar manner as
(see~\ref{TAO_Semantics_Semantics_Encoding}):

\begin{center}
  @{thm T2[of w "embedded_style \<Pi>" "embedded_style \<kappa>"]}
\end{center}

The only difference to exemplification formulas is that the encoding extension does not depend
on the possible world @{term "w"}.

The definitions of truth conditions for complex formulas are straightforward
(see~\ref{TAO_Semantics_Semantics_Complex_Formulas}):

\begin{itemize}
  \item @{thm[display] T4[of w \<psi>]}
  \item @{thm[display] T5[of w \<psi> \<chi>]}
  \item @{thm[display] T6[of w \<psi>]}
  \item @{thm[display] T7[of w \<psi>]}
  \item @{thm[display] T8_\<nu>[of w \<psi>]}
  \item @{thm[display] T8_0[of w \<psi>]}
  \item @{thm[display] T8_1[of w \<psi>]}
  \item @{thm[display] T8_2[of w \<psi>]}
  \item @{thm[display] T8_3[of w \<psi>]}
\end{itemize}

A negation formula @{term "embedded_style (\<^bold>\<not>\<psi>)"} is semantically true in a possible world, if and only if
@{term "embedded_style \<psi>"} is not semantically true in the given possible world, similarly truth conditions for
implication formulas and quantification formulas are defined canonically.

The truth condition of the modal box operator @{term "embedded_style (\<^bold>\<box>\<psi>)"} as @{term "embedded_style \<psi>"} being true in all
possible worlds, shows that modality follows a S5 logic. For the actuality operator @{term "embedded_style (\<^bold>\<A>\<psi>)"}
is defined to be semantically true, if and only if @{term "embedded_style \<psi>"} is true in the designated actual world.

Once more it is important to note that all introduced truth conditions do \emph{not} depend
on the actual state following the ideas of section TODO: reference.

*}

subsection{* Denotation of Definite Descriptions *}
  
text{*

The definition of the denotation of description terms (see~\ref{TAO_Semantics_Semantics_Descriptions})
can be presented in a more readable form by splitting it into its two cases and by using the meta-logical
quantifier for unique existence:
\begin{itemize}
  \item @{lemma[display] "(\<exists>!x. [\<psi> x in w\<^sub>0])
            \<Longrightarrow> d\<^sub>\<kappa> (embedded_style (\<^bold>\<iota>x. \<psi> x)) = Some (THE x. [\<psi> x in w\<^sub>0])"
    by (auto simp: embedded_style_def D3)}
  \item @{lemma[display] "\<not>(\<exists>!x. [\<psi> x in w\<^sub>0])
            \<Longrightarrow> d\<^sub>\<kappa> (embedded_style (\<^bold>\<iota>x. \<psi> x)) = None"
    by (auto simp: embedded_style_def D3)}
\end{itemize}

If there exists a unique @{term "x"}, such that @{term "embedded_style (\<psi> x)"} is true in the actual world,
the definite description denotes and its denotation is this unique @{term "x"}, otherwise
the definite description fails to denote.

It is important to consider what happens if a non-denoting definite description occurs in a formula:
The only positions in which such a term could occur in a complex formula is in an exemplification expression
or in an encoding expression. Given the above truth conditions it becomes clear, that
the presence of non-denoting terms does \emph{not} mean that there are formulas without
truth conditions: Since exemplification and encoding formulas are defined to be true \emph{if and only if}
the contained individual term has a denotation, such formulas are @{term "False"} for non-denoting
individual terms (TODO: reference Russell's analysis).

*}

subsection{* Denotation of $\lambda$-Expressions *}

text{*

The most complex part of the semantical abstraction is the definition of a denotation for @{text "\<lambda>"}-expressions.
The preliminary formal semantics of PLM is split into several cases and uses a special class of
\emph{Hilbert-Ackermann @{text "\<epsilon>"}-terms} that are challenging to represent. Therefore a simplified
formulation of the denotation criteria is used. Moreover the denotations of @{text "\<lambda>"}-expressions are
coupled to syntactical conditions. This fact is represented using the notion of \emph{proper maps}
as a restriction for the matrix of a @{text "\<lambda>"}-expression that was introduced in section~\ref{lambda-expressions}.
The definitions are implemented as follows (see~\ref{TAO_Semantics_Semantics_Lambda_Expressions}):

\begin{itemize}
  \item @{lemma[display] "d\<^sub>1 (embedded_style (\<^bold>\<lambda>x. \<lparr>\<Pi>, x\<^sup>P\<rparr>)) = d\<^sub>1 (embedded_style \<Pi>)"
          by (simp add: embedded_style_def D4_1)}
  \item @{lemma[display] "IsProperInX (embedded_style \<phi>) \<Longrightarrow> Some r = d\<^sub>1 (embedded_style (\<^bold>\<lambda>x. \<phi> (x\<^sup>P)))
          \<and> Some o\<^sub>1 = d\<^sub>\<kappa> (embedded_style x) \<longrightarrow> (o\<^sub>1 \<in> ex1 r w) = [\<phi> x in w]"
          by (simp add: embedded_style_def D5_1)}
  \item @{lemma[display] "Some r = d\<^sub>0 (embedded_style (\<^bold>\<lambda>\<^sup>0 \<phi>)) \<longrightarrow> ex0 r w = [\<phi> in w]"
    by (simp add: embedded_style_def D6)}
\end{itemize}

The first condition for \emph{elementary} @{text "\<lambda>"}-expressions is straightforward.
The general case in the second condition is more complex: Given that @{term "embedded_style \<phi>"}
is a proper map then the relation denoted by the @{text "\<lambda>"}-expression has the property, that for a
denoting individual term @{term "embedded_style x"}, the denoted individual is contained in
its exemplification extension for a possible world @{term "w"}, if and only if @{term "embedded_style (\<phi> x)"}
holds in @{term "w"}.
At a closer look this is the statement of @{text "\<beta>"}-conversion restricted to denoting individuals:
the truth condition of the @{text "\<lambda>"}-expression being exemplified by some denoting individual term,
is the same as the truth condition of the matrix of the term for the denoted individual.
Therefore it is clear that the precondition that @{term "embedded_style \<phi>"} is a proper map
is necessary and sufficient.
Given this consideration the case for @{text "0"}-place relations is again straightforward.

*}

subsection{* Properties of the Semantics *}

text{*

  The formal semantics of PLM imposes several further restrictions some of which are derived as
  auxiliary lemmas. Furthermore some auxiliary statements that are specific to the underlying
  representation layer are derived. Future work may try to refrain from this second kind
  of statements.

  The statements are comprised of the following (see~\ref{TAO_Semantics_Semantics_Auxiliary_Lemmata}):
  \begin{enumerate}
    \item All relations denote, e.g. @{thm[display] propex\<^sub>1[of "embedded_style F"]}
    \item An individual term of the form @{term "embedded_style (x\<^sup>P)"} denotes @{term "x"}:
          @{lemma[display] "d\<^sub>\<kappa> (embedded_style (x\<^sup>P)) = Some (embedded_style x)"
            by (simp add: embedded_style_def d\<^sub>\<kappa>_proper)}
    \item Every ordinary object is contained in the extension of the concreteness property for some
          possible world:
          @{lemma[display] "Some r = d\<^sub>1 (embedded_style (E!)) \<Longrightarrow> (\<forall> x . \<exists> w . \<omega>\<nu> x \<in> ex1 r w)"
            by (simp add: embedded_style_def ConcretenessSemantics1)}
    \item An object that is contained in the extension of the concreteness property in any world is
          an ordinary object:
          @{lemma[display] "Some r = d\<^sub>1 (embedded_style (E!)) \<Longrightarrow> (\<forall> x . x \<in> ex1 r w \<longrightarrow> (\<exists> y . x = \<omega>\<nu> y))"
            by (simp add: embedded_style_def ConcretenessSemantics2)}
    \item The denotation functions for relation terms are injective, e.g.
          @{thm[display] d\<^sub>1_inject[of "embedded_style F" "embedded_style G"]}
    \item The denotation functions for individual terms is injective for denoting terms:
          @{thm[display] d\<^sub>\<kappa>_inject[of "o\<^sub>1" "embedded_style x" "embedded_style y"]}
  \end{enumerate}

  Especially the statements 5 and 6 are only derivable due to the specific construction of
  the representation layer: since the semantical domains were defined as the representation sets
  of the respective type of term and denotations were defined canonically, objects that have the
  same denotation are identical as objects of their abstract type.
*}

subsection{* Proper Maps *}
  
text{*
  The definition of \emph{proper maps} as described in section~\ref{lambda-expressions} is
  formulated in terms of the meta-logic. Since denotation conditions in the semantics and
  later some of the axioms have to be restricted to proper maps, a method has to be devised
  by which the propriety of a map can easily be shown without using meta-logical concepts.

  Therefore introduction rules for @{term "IsProperInX"}, @{term "IsProperInXY"} and
  @{term "IsProperInXYZ"} are derived and a proving method @{method[names_short = true] "show_proper"}
  is defined that can be used to proof the propriety of a map using these introduction rules
  (see~\ref{TAO_Semantics_Proper}).

  The rules themselves rely on the power of the \emph{unifier} of Isabelle/HOL: Any map acting
  on individuals that can be expressed by another map that solely acts on exemplification expressions
  involving the individuals, is shown to be proper. This effectively means that all maps whose arguments
  only appear in exemplification expressions are proper. For a discussion about the relation between
  this concept and admissible @{text "\<lambda>"}-expressions in PLM see TODO: reference.
*}

(*<*)
end (* context Semantics *)
(*>*)

section{* General All-Quantifier *}

text{*
  \label{general-quantifier}

  Since the last section established the semantic truth conditions of the specific versions of the
  all quantifier for all variable types of PLM, it is now possible to define a binding symbol for general
  all quantification.

  This is done using the concept of \emph{type classes} in Isabelle/HOL. Type classes define
  constants that depend on a \emph{type variable} and state assumptions about this constant.
  In subsequent reasoning the type of an object can be restricted to a type of the introduced
  type class. Thereby the reasoning can make use of all assumptions that have been stated about
  the constants of the type class. A priori it is not assumed that any type actually satisfies
  the requirements of the type class, so initially statements involving types restricted
  to a type class can not be applied to any specific type.

  To allow this the type class has to be \emph{instantiated} for the desired type. This is done
  by first providing a definition of the constants of the type class that is specific to the
  respective type and then providing proofs for each assumption made by the type class given the
  particular type and the provided definitions. Once this is done any statement that was proven for
  the general type class can be applied to this type.

  In the case of general all quantification for the embedding this concept can be utilized by
  introducing the type class @{class quantifiable} that is equipped with a constant that is used
  as the general all quantification binder (see~\ref{TAO_Quantifiable_Class}).
  For this constant it can now be assumed that it satisfies the semantic properties of all
  quantification: @{thm quantifiable_T8[of w \<psi>]}.

  Since it was already shown in the last section that all variable types satisfy this property,
  the type class can immediately be instantiated for the types @{type \<nu>}, @{type \<Pi>\<^sub>0}, @{type \<Pi>\<^sub>1},
  @{type \<Pi>\<^sub>2} and @{type \<Pi>\<^sub>3} (see~\ref{TAO_Quantifiable_Instantiation}). The instantiation proofs
  only need to refer to the statements derived in the semantics section for the respective version
  of the quantifier and are thereby independent of the representation layer.

  From this point onward therefore the general all quantifier can be used and the type specific
  versions of the quantifiers are no longer needed. This is true even if a quantification is meant
  to only range over objects of a particular type: In this case the desired type
  (if it can not implicitly be deduced from the context) can be stated explicitly while still using
  the general quantifier.

*}

section{* Derived Language Elements *}

text{*
  The language of the embedded logic constructed so far is limited to the minimal set of
  primitive elements, e.g. only negation and implication are present and no notion of identity
  has been introduced so far.

  Since section~\ref{semantics} has established the semantical properties of these basic elements of
  the language, it now makes sense to extend the language by introducing some basic definitions
  that can be expressed directly in the embedded logic.
*}

subsection{* Connectives *}

text{*
  The remaining classical connectives are defined in the traditional manner (see~\ref{TAO_BasicDefinitions_DerivedConnectives}):
  \begin{itemize}
    \item @{thm[display] conj_def[expand2, THEN embedded_eq, of \<phi> \<psi>]}
    \item @{thm[display] disj_def[expand2, THEN embedded_eq, of \<phi> \<psi>]}
    \item @{thm[display] equiv_def[expand2, THEN embedded_eq, of \<phi> \<psi>]}
    \item @{thm[display] diamond_def[expand1, THEN embedded_eq, of \<phi>]}
  \end{itemize}

  Furthermore the general all quantifier is supplemented by an existence quantifier as follows:
  \begin{itemize}
    \item @{thm[display] exists_def[expand1, of \<phi>, THEN embedded_eq]}
  \end{itemize}
*}

subsection{* Identity *}
  
text{*
  More importantly the definitions for identity are stated for each type of variable
  (see~\ref{TAO_BasicDefinitions_Identity}):

  \begin{itemize}
    \item @{thm[display] basic_identity\<^sub>E_infix_def[unfolded basic_identity\<^sub>E_def, THEN embedded_def, of x y]}
    \item @{thm[display] basic_identity\<^sub>1_def[expand2, of F G, rename_abs x, THEN embedded_eq]}
    \item @{thm[display] basic_identity\<^sub>2_def[expand2, of F G, rename_abs x, THEN embedded_eq]}
    \item @{thm basic_identity\<^sub>3_def[expand2, of F G, rename_abs x y, THEN embedded_eq]}
  \end{itemize}

  TODO: reformatting/line breaks in the list somehow.

  Similarly to the general all quantifier it makes sense to introduce a general identity
  relation for all types of terms (@{type \<kappa>}, @{type \<o>} resp. @{typ \<Pi>\<^sub>0}, @{typ \<Pi>\<^sub>1}, @{typ \<Pi>\<^sub>2}, @{typ \<Pi>\<^sub>3}).
  In contrast to all quantification this is more challenging, though, since there is no
  semantic criterion that characterizes the identity for all these types. Therefore a general
  identity symbol will only be introduced after the next section, since it will then be possible
  to formulate and prove a reasonable property shared by the identity of all types of terms.

*}

(*<*)
context MetaSolver
begin
(*>*)

section{* Proving Method meta\_solver *}
 
text{* \label{meta_solver} *}
  
subsection{* Concept *}
  
text{*

  Since the section~\ref{semantics} constructed a first abstraction layer on top of the first layer
  that focuses on a single kind of model and is connected with specific technicalities, it makes sense
  to revisit the general concept of the layered structure of the embedding.

  The idea behind this approach is that the reasoning in subsequent layers should - as far as possible - only
  rely on the previous layer. Automated reasoning in this way, however, can be cumbersome, since
  automated proving tools have to be restricted to only consider a specific set of theorems that are
  true in the context. While this is possible it is still an interesting question whether the process
  of automated reasoning in the layered approach can be made easier.

  To that end the embedding facilitates the possibility of defining custom proving methods that
  the Isabelle package \emph{Eisbach} provides. This package allows it to conveniently
  define a new proving method that is based on the systematic application of existing methods.
  
  \begin{remark}
    The Eisbach package even allows to construct more complex proving methods that involve
    pattern matching. This is utilized in the construction of a substitution method in section TODO: reference details
  \end{remark}

  The idea is to construct a simple resolution prover that allows it to deconstruct complex
  formulas of the embedded logic to simpler formulas that are connected by some relation in the meta-logic
  as required by the semantics.

  For example an implication formula can be deconstructed as follows:
  \begin{center}
    @{thm ImplS[of v \<phi> \<psi>]}
  \end{center}

  Whereas the basic proving methods available in Isabelle cannot immediately prove
  \mbox{@{lemma "[\<phi> \<^bold>\<rightarrow> \<phi> in v]" by (simp add: ImplS)}} without any facts about the definitions of validity and implication,
  they \emph{can} prove \mbox{@{lemma "[\<phi> in v] \<longrightarrow> [\<phi> in v]" by simp}} directly as an instance of
  \mbox{@{lemma "p \<longrightarrow> p" by simp}}.
*}
  
subsection{* Implementation *}

text{*
  Following this idea the method @{method meta_solver} is introduced (see~\ref{TAO_MetaSolver})
  that repeatedly applies rules like the above in order to translate a formula in the embedded logic
  to a meta-logical statement involving simpler formulas.

  The statement of appropriate introduction, elimination and substitution rules for the logical
  connectives and quantifiers is straightforward, but beyond that the concept can be used to
  resolve exemplification and encoding formulas to their semantic truth conditions as well,
  e.g. (see~\ref{TAO_MetaSolver_Encoding}):
  \begin{center}
    @{thm Exe1E[of v F x]}
  \end{center}

  This way a large set of formulas can be decomposed to semantic expressions that can be automatically
  proven without having to rely on the meta-logical definitions directly.

  As mentioned before the concept of a strict separation between the layers is not yet achieved by
  the embedding. In particular the @{method meta_solver} is equipped with rules about
  being abstract and ordinary and most importantly about the defined identity that depend on the
  specific structure of the representation layer and are not solely derivable from the semantics.

  Notably the representation layer has the property that the defined identities are equivalent to
  the identity in the meta-logic. Formally the following statements are true and defined as rules
  for the @{method meta_solver} (see~\ref{TAO_MetaSolver_Identity}):

  \begin{itemize}
    \item @{thm[display] Eq\<^sub>ES[of v "embedded_style x" "embedded_style y"]}
    \item @{thm[display] Eq\<kappa>S[of v "embedded_style x" "embedded_style y"]}
    \item @{thm[display] Eq\<^sub>1S[of v "embedded_style F" "embedded_style G"]}
    \item @{thm[display] Eq\<^sub>2S[of v "embedded_style F" "embedded_style G"]}
    \item @{thm[display] Eq\<^sub>3S[of v "embedded_style F" "embedded_style G"]}
    \item @{thm[display] Eq\<^sub>0S[of v "embedded_style F" "embedded_style G"]}
  \end{itemize}

  The proofs for these statements (see~\ref{TAO_MetaSolver_Identity}) are complex and do not
  solely rely on the properties of the formal semantics of PLM.

  Although future work may try to forgo these statements or to replace them with statements that
  are in fact based on the formal semantics alone, the fact that they are true in the constructed
  embedding has a distinct advantage: since identical terms in the sense of PLM are identical in
  the meta-logic, proving the axiom of substitution (TODO: reference) is trivial.

  \begin{remark}
    Instead of introducing a custom proving method using the Eisbach package, a similar
    effect could be achieved by instead supplying the derived introduction, elimination and substitution
    rules directly to one of the existing proving methods like @{method auto} or @{method clarsimp}.
    In practice, however, we found that the custom @{method meta_solver} produces more reliable
    results, especially in the case that a proving objective cannot be solved by the supplied rules
    completely. Moreover the construction of a custom proving method may serve as a proof of concept
    and inspire the development of further more complex proving methods that go beyond a simple
    resolution prover in the future.
  \end{remark}
*}

subsection{* Applicability *}

text{*
  Given the discussion above and keeping the layered structure of the embedding in mind, it is
  important to precisely determine for which purposes it is valid to use the constructed
  @{method meta_solver}.

  The main application of the method in the embedding is its use in the derivation of the axiom system as described in
  section TODO: reference. Furthermore the @{method meta_solver} can aid in examining the
  meta-logical properties of the embedding. Care has been taken that the meta-solver only employs
  \emph{reversable} transformations, thereby it is for example justified to use it to simplify a statement
  before employing a tool like @{theory_text "nitpick"} in order to look for counter-models for a statement.

  However it is \emph{not} justified to assume that a theorem that can be proven with the aid of the
  @{method meta_solver} method can be considered to be derivable in the formal system of PLM, since
  the result still depends on the specific structure of the representation layer. Note, however,
  that the concept of the @{method meta_solver} inspired another proving method that is
  introduced in section TODO: reference, namely the @{method PLM.PLM_solver}. This proving method
  only employs rules that are derivable from the formal system of PLM itself. Thereby this method
  \emph{can} be used in proves without sacrificing the universality of the result.
  
*}

(*<*)
end (* context MetaSolver *)
(*>*)

section{* General Identity Relation *}

text{*
  As already mentioned in section~\ref{general-quantifier} similarly to the general quantification
  binder it is desirable to introduce a general identity relation.

  Since the identity of PLM is not directly defined using semantic truth conditions, but instead
  by the means of a complex formulas in the embedded logic that is specific to each type of terms,
  the question is whether they share a property that can reasonably be used as the condition of
  a type class.

  A natural choice for such a condition is based on the axiom of the substitution of identicals
  (see TODO: reference). The axiom states that if two objects are identical (in the sense of the defined
  identity of PLM), then a formula involving the first object implies the formula resulting from
  substituting the second object for the first object. This inspires the following condition for
  the type class (see~\ref{TAO_Identifiable_Class}):

  \begin{center}
    @{thm identifiable_class.l_identity[of v \<alpha> \<beta> \<phi>]}
  \end{center}

  Using the fact that in the last section it was already derived, that the defined identity
  in the embedded-logic for each term implies the primitive identity of the meta-logical objects,
  this type class can be instantiated for all types of terms: @{type \<kappa>}, @{typ \<Pi>\<^sub>0} resp. @{type \<o>},
  @{type \<Pi>\<^sub>1}, @{type \<Pi>\<^sub>2}, @{type \<Pi>\<^sub>3} (see~\ref{TAO_Identifiable_Instantiation}).

  Since now general quantification and general identity are available, it seems reasonable to
  define the unique existence quantifier that involves both quantification and identity. To that
  end a derived type class that is introduced that is the combination of the @{class quantifiable}
  and the @{class identifiable} classes (since both general quantification and identity have to be
  available).Although this is straightforward for the relation types, this reveals a subtlety
  involving the distinction between individuals of type @{type \<nu>} and individual terms of type @{type \<kappa>}:
  The type @{type \<nu>} belongs to the class @{class quantifiable}, the type @{type \<kappa>} on the other hand
  does not: no quantification over individual \emph{terms} (that may not denote) was defined.
  On the other hand the class @{class identifiable} was only instantiated for the type @{type \<kappa>},
  but not for the type @{type \<nu>}. This issue can be solved by noticing that it is straightforward and
  justified to define an identity for @{type \<nu>} as allows:

  \begin{center}
    @{thm identity_\<nu>_def[expand2, of x y, THEN embedded_eq]}
  \end{center}

  This way type @{type \<nu>} is equipped with both the general all quantifier and the general identity
  relation and unique existence can be defined for all variable types as expected:

  \begin{center}
    @{thm exists_unique_def[expand1, of \<phi>, THEN embedded_eq]}
  \end{center}

  Another subtlety has to be considered: at times it is necessary to expand the definitions
  of identity for a specific type to derive statements in PLM. Since the defined identities were
  introduced prior to the general identity symbol, such an expansion is therefore so far not possible
  for a statement that uses the general identity, even if the types are fixed in the context.

  To allow such an expansion the definitions of identity are equivalently restated for the general
  identity symbol and each specific type (see~\ref{TAO_Identifiable_Definitions}). This way
  the general identity can from this point onward completely replace the type-specific identity
  symbols.

*}
  
(*<*)
context Axioms
begin
(*>*)

section{* The Axiom System of PLM *}

text{*
  \label{axioms}

  The last step in abstracting away from the representation layer used as the basis
  of the embedding is the derivation of the axiom system of PLM. Conceptionally the
  derivation of the axioms is the last moment in which it is deemed admissible to rely
  on the meta-logical properties of the underlying model structure. Future work may even
  restrict this further to only allow the use of the properties of the semantics in the
  proofs (if this is found to be possible).

  To be able to distinguish between the axioms and other statements and theorems in the
  embedded logic they are stated using a dedicated syntax. To that end axioms are not
  stated relative to a specific possible world, but using the following definition
  (see~\ref{TAO_Axioms}):
  \begin{center}
    @{thm axiom_def[expand1, of \<phi>]}
  \end{center}

  Axioms are unconditionally true in all possible worlds. The only exceptions are
  \emph{necessitation-averse}, resp. \emph{modally fragile} axioms (currently there
  is only one such axiom). Such axioms are stated using the following definition:
  \begin{center}
    @{thm actual_validity_def[expand1, of \<phi>]}
  \end{center}

  \begin{remark}
    Additionally a proving method @{method axiom_meta_solver} is introduced, that
    unfolds above definition, then applies the meta-solver and if possible resolves
    the proof objective automatically.
  \end{remark}
  
*}
  
subsection{* Axioms as Schemata *}
  
text{*
  \label{axiom-schemata}

  The axioms in PLM are meant as axiom schemata. They are stated using variables that range over
  and can therefore be instantiated for any formula and term (potentially satisfying explicitly stated
  restrictions). Furthermore PLM introduces the notion of \emph{closures}. Effectively this means
  that the statement of an axiom schema implies that the universal generalization of the schema,
  the actualization of the schema and the necessitation of the schema is also an axiom.
  The modally fragile Axiom~\ref{PM-logic-actual} is the only exception to this.
  This axiom is considered and its necessitation is not an axiom.

  Since in Isabelle/HOL free variables in a theorem already range over all terms of the same type
  no special measures have to be taken to allow instantiations for arbitrary terms. The concept of
  closures is introduced using the following rules (see~\ref{TAO_Axioms_Closures}):

  \begin{itemize}
    \item @{thm[display] axiom_instance[of \<phi> v]}
    \item @{thm[display] closures_universal[of \<phi>]}
    \item @{thm[display] closures_actualization[of \<phi>]}
    \item @{thm[display] closures_necessitation[of \<phi>]}
  \end{itemize}

  For modally fragile axioms only the following rules are introduced:

  \begin{itemize}
    \item @{thm[display] necessitation_averse_axiom_instance[of \<phi>]}
    \item @{thm[display] necessitation_averse_closures_universal[of \<phi>]}
  \end{itemize}

  \begin{remark}
    To simplify the instantiation of the axioms in subsequent proofs,
    a set of \emph{attributes} is defined that can be used to transform
    the statement of the axioms using the rules defined above.

    This way for example the axiom \mbox{@{thm qml_2}} can be directly transformed
    to \mbox{@{thm qml_2[axiom_universal, axiom_instance, of v \<phi>]}} by not referencing
    it directly as @{theory_text qml_2}, but by applying the defined attributes
    to it: @{theory_text "qml_2[axiom_universal, axiom_instance]"}
  \end{remark}
*}

subsection{* Derivation of the Axioms *}

text{*
  Most of the axioms can be derived by the @{method axiom_meta_solver} directly.
  Some axioms, however, require more verbose proofs or special attention has to
  be taken regarding their representation in the functional setting of Isabelle/HOL.
  Therefore in the following the complete axiom system is listed and discussed in
  detail where necessary. Additionally they are associated with the numbering in
  the current draft of PLM @{cite PM}.
*}
  
subsubsection{* Axioms for Negations and Conditionals *}
  
text{*
  The axioms for negations and conditionals can be derived automatically and
  present no further issues (see~\ref{TAO_Axioms_NegationsAndConditionals}):

  \begin{itemize}
    \item @{thm pl_1} \hfill{(\ref{PM-pl}.1)}
    \item @{thm pl_2} \hfill{(\ref{PM-pl}.2)}
    \item @{thm pl_3} \hfill{(\ref{PM-pl}.3)}
  \end{itemize}

*}

subsubsection{* Axioms of Identity *}

text{*
  The axiom of the substitution of identicals can be proven automatically,
  if additionally supplied with the defining assumption of the type class
  @{class identifiable}. The statement is the following (see~\ref{TAO_Axioms_Identity}):

  \begin{itemize}
    \item @{thm l_identity} \hfill{(\ref{PM-l-identity})}
  \end{itemize}

  TODO: discussion
*}

subsubsection{* Axioms of Quantification *}

text{*
  \label{quantification-axioms}

  The axioms of quantification are formulated in a way that differs from the statements in
  PLM, as follows (see~\ref{TAO_Axioms_Quantification}):

  \begin{itemize}
    \item @{thm cqt_1} \hfill{(\ref{PM-cqt}.1)}
    \item @{thm cqt_1_\<kappa>} \hfill{(\ref{PM-cqt}.1)}
    \item @{thm cqt_3} \hfill{(\ref{PM-cqt}.3)}
    \item @{thm cqt_4} \hfill{(\ref{PM-cqt}.4)}
    \item @{thm cqt_5} \hfill{(\ref{PM-cqt}.5)}
    \item @{thm cqt_5_mod} \hfill{(\ref{PM-cqt}.5)}
  \end{itemize}

  The direct translation of the axioms of PLM would be the following:

  \begin{itemize}
    \item @{term "[[(\<^bold>\<forall> \<alpha> . \<phi> \<alpha>) \<^bold>\<rightarrow> ((\<^bold>\<exists> \<beta> . \<beta> \<^bold>= \<tau>) \<^bold>\<rightarrow> \<phi> \<tau>)]]"} \hfill{(\ref{PM-cqt}.1)}
    \item @{term "[[\<^bold>\<exists> \<beta> . \<beta> \<^bold>= \<tau>]]"} \hfill{(\ref{PM-cqt}.2)}
    \item @{thm cqt_3} \hfill{(\ref{PM-cqt}.3)}
    \item @{thm cqt_4} \hfill{(\ref{PM-cqt}.4)}
    \item @{thm cqt_5} \hfill{(\ref{PM-cqt}.5)}
  \end{itemize}

  Axiom~(\ref{PM-cqt}.2) is furthermore restricted to @{term "\<tau>"} not being a definite description.
  Now in the embedding definite descriptions have the type @{type \<kappa>} that is different from the
  type for individuals @{type \<nu>} and quantification is only defined for @{type \<nu>}, not for @{type \<kappa>}.

  Thereby the restriction of (\ref{PM-cqt}.2) does not apply, since @{term "\<tau>"} cannot be a
  definite description by construction. Since (\ref{PM-cqt}.2) would therefore hold in general,
  the additional restriction of (\ref{PM-cqt}.1) can be dropped - again since a quantifier is used in the
  formulation, the problematic case of definite descriptions (which would have type @{type \<kappa>})
  is excluded already.

  Now the modification of (\ref{PM-cqt}.5) can be explained: Since (\ref{PM-cqt}.2) already
  implies the right hand side for every term except definite
  descriptions, (\ref{PM-cqt}.5) can be stated for general terms
  instead of stating it specifically for definite descriptions.

  What's left to be considered is how (\ref{PM-cqt}.1) can be applied to definite
  descriptions in the embedding. The modified version of (\ref{PM-cqt}.5) states that under the same condition
  that the unmodified version requires for a description to denote, the description (that has type @{type \<kappa>})
  denotes an object of type @{type \<nu>} and thereby (\ref{PM-cqt}.1) can be applied using the substitution of identicals.

  Future work may want to reconsider the reformulation of the axioms, especially considering the most
  recent developments described in TODO: reference. At the time of writing the fact that due to the
  type restrictions of the embedding, the reformulated version of the axioms is \emph{derivable} from
  the original version the reformulation is a reasonable compromise.

  \begin{remark}
    A formulation of the axioms as in PLM could be possible using the concept of domain restricted
    quantification as employed in embedding free logics (TODO: reference) to define a restricted
    quantification over the type @{type \<kappa>}. This would require some non-trivial restructuring of
    the embedding, though.
  \end{remark}

  What's left is to clarify the precondition for (\ref{PM-cqt}.5). The predicate @{term "SimpleExOrEnc"}
  is defined as an inductive predicate with the following introduction rules:

  \begin{itemize}
    \item @{lemma[eta_contract=false] "SimpleExOrEnc (\<lambda>x. embedded_style \<lparr>F,x\<rparr>)" by (simp add: SimpleExOrEnc.intros embedded_style_def)}
    \item @{lemma[eta_contract=false] "SimpleExOrEnc (\<lambda>x. embedded_style \<lparr>F,x,DUMMY\<rparr>)" by (simp add: SimpleExOrEnc.intros embedded_style_def)}
    \item @{lemma[eta_contract=false] "SimpleExOrEnc (\<lambda>x. embedded_style \<lparr>F,DUMMY,x\<rparr>)" by (simp add: SimpleExOrEnc.intros embedded_style_def)}
    \item @{lemma[eta_contract=false] "SimpleExOrEnc (\<lambda>x. embedded_style \<lparr>F,x,DUMMY,DUMMY\<rparr>)" by (simp add: SimpleExOrEnc.intros embedded_style_def)}
    \item @{lemma[eta_contract=false] "SimpleExOrEnc (\<lambda>x. embedded_style \<lparr>F,DUMMY,x,DUMMY\<rparr>)" by (simp add: SimpleExOrEnc.intros embedded_style_def)}
    \item @{lemma[eta_contract=false] "SimpleExOrEnc (\<lambda>x. embedded_style \<lparr>F,DUMMY,DUMMY,x\<rparr>)" by (simp add: SimpleExOrEnc.intros embedded_style_def)}
    \item @{lemma[eta_contract=false] "SimpleExOrEnc (\<lambda>x. embedded_style \<lbrace>x,F\<rbrace>)" by (simp add: SimpleExOrEnc.intros embedded_style_def)}
  \end{itemize}

  This corresponds exactly to the restriction of @{term "embedded_style \<psi>"} to an exemplification
  or encoding formula in PLM.

*}

subsubsection{* Axioms of Actuality *}
  
text{*
  \label{axioms-actuality}

  As mentioned in the beginning of the section the modally-fragile axiom of actuality
  is stated using a different syntax (see~\ref{TAO_Axioms_Actuality}):

  \begin{itemize}
    \item @{thm logic_actual} \hfill{(\ref{PM-logic-actual})}
  \end{itemize}

  Note that the model finding tool @{theory_text nitpick} can find a counter-model for the
  formulation as a regular axiom, as expected.

  The remaining axioms of actuality are not modally-fragile and therefore stated as regular
  axioms:
  
  \begin{itemize}
    \item @{thm logic_actual_nec_1} \hfill{(\ref{PM-logic-actual-nec}.1)}
    \item @{thm logic_actual_nec_2} \hfill{(\ref{PM-logic-actual-nec}.2)}
    \item @{thm logic_actual_nec_3} \hfill{(\ref{PM-logic-actual-nec}.3)}
    \item @{thm logic_actual_nec_4} \hfill{(\ref{PM-logic-actual-nec}.4)}
  \end{itemize}

  All of the above can be proven automatically by the @{method axiom_meta_solver} method.
*}

subsubsection{* Axioms of Necessity *}

text{*
  The axioms of necessity are the following (see~\ref{TAO_Axioms_Necessity}):

  \begin{itemize}
    \item @{thm qml_1} \hfill{(\ref{PM-qml}.1)}
    \item @{thm qml_2} \hfill{(\ref{PM-qml}.2)}
    \item @{thm qml_3} \hfill{(\ref{PM-qml}.3)}
    \item @{thm qml_4} \hfill{(\ref{PM-qml}.4)}
  \end{itemize}

  While the first three axioms can be derived automatically, the last axiom requires
  special attention. On a closer look the formulation may be familiar. The axiom
  was already mentioned in section~\ref{concreteness} while constructing the representation
  of the constant @{term "embedded_style E!"}. To be able to derive this axiom now this
  constant had to be specifically axiomatized. Consequently the derivation here requires
  the use of the axioms stated in the representation layer.

*}

subsubsection{* Axioms of Necessity and Actuality *}
  
text{*
  The axioms of necessity and actuality can be derived automatically
  and require no further attention (see~\ref{TAO_Axioms_NecessityAndActuality}):

  \begin{itemize}
    \item @{thm qml_act_1} \hfill{(\ref{PM-qml-act}.1)}
    \item @{thm qml_act_2} \hfill{(\ref{PM-qml-act}.2)}
  \end{itemize}
*}

subsubsection{* Axioms of Descriptions *}

text{*
  There is only one axiom dedicated to descriptions only (note, however, that descriptions play
  a role in the axioms of quantification). The statement is the following (see~\ref{TAO_Axioms_Descriptions}):

  \begin{itemize}
    \item @{thm descriptions} \hfill{(\ref{PM-descriptions})}
  \end{itemize}

  Given the technicalities of descriptions already discussed in section~\ref{quantification-axioms}
  it comes at no surprise that the proof for this statement is rather verbose.

*}

subsubsection{* Axioms of Complex Relation Terms *}
(*<*)
context
begin
  interpretation MetaSolver .
(*>*)
text{*
  The axioms of complex relation terms deal with the properties of @{text "\<lambda>"}-expressions.
  
  Since the @{method meta_solver} was not equipped with explicit rules for @{text "\<lambda>"}-expressions,
  the statements rely on their semantic properties as described in section~\ref{semantics} directly.

*}
(*<*)
end (* unnamed subcontext with MetaSolver interpretation *)
(*>*)
text{*

  The statements are the following (see~\ref{TAO_Axioms_ComplexRelationTerms}):
  \begin{itemize}
    \item @{thm lambda_predicates_1[THEN embedded_eq, of \<phi>]} \hfill{(\ref{PM-lambda-predicates}.1)}
    \item @{thm lambda_predicates_2_1} \hfill{(\ref{PM-lambda-predicates}.2)}
    \item @{thm lambda_predicates_2_2} \hfill{(\ref{PM-lambda-predicates}.2)}
    \item @{thm[display] lambda_predicates_2_3} \hfill{(\ref{PM-lambda-predicates}.2)}
    \item @{thm lambda_predicates_3_0} \hfill{(\ref{PM-lambda-predicates}.3)}
    \item @{thm lambda_predicates_3_1} \hfill{(\ref{PM-lambda-predicates}.3)}
    \item @{thm lambda_predicates_3_2} \hfill{(\ref{PM-lambda-predicates}.3)}
    \item @{thm lambda_predicates_3_3} \hfill{(\ref{PM-lambda-predicates}.3)}
    \item @{thm lambda_predicates_4_0} \hfill{(\ref{PM-lambda-predicates}.4)}
    \item @{thm lambda_predicates_4_1} \hfill{(\ref{PM-lambda-predicates}.4)}
    \item @{thm lambda_predicates_4_2} \hfill{(\ref{PM-lambda-predicates}.4)}
    \item @{thm lambda_predicates_4_3} \hfill{(\ref{PM-lambda-predicates}.4)}
  \end{itemize}

  Note that the first axiom - @{text "\<alpha>"}-conversion - could be omitted entirely, since the fact
  that lambda-expressions are modelled using functions with bound variables and @{text "\<alpha>"}-conversion
  is part of the logic of Isabelle/HOL, it already holds implicitly.

  Further note that the notion of \emph{proper maps} is used as a necessary precondition for
  @{text "\<beta>"}-conversion, as explained in section~\ref{lambda-expressions}.

  Lastly note that the formulation of the last class of axioms
  ((\ref{PM-lambda-predicates}.4), @{term "\<iota>"}-conversion)
  has to be adjusted to be representable in the functional setting:
  
  The original axiom is stated as follows in the syntax of PLM:
  \begin{center}
    @{text "\<A>(\<phi> \<equiv> \<psi>) \<rightarrow> ([\<lambda>x\<^sub>1\<cdots>x\<^sub>n \<chi>\<^sup>*] = [\<lambda>x\<^sub>1\<cdots>x\<^sub>n \<chi>\<^sup>*']"}
  \end{center}
  Here @{text "\<chi>\<^sup>*'"} is required to be the result of substituting  @{text "\<iota>x\<psi>"} for zero or more occurrences of @{text "\<iota>x\<phi>"}
  in @{text "\<chi>\<^sup>*"}. In the functional setting @{term "embedded_style \<chi>"} can be represented
  as function from individual terms of type @{type \<kappa>} to propositions of type @{type \<o>}.
  Thereby substituting @{text "\<iota>x\<psi>"} for occurences of @{text "\<iota>x\<phi>"} can be expressed as
  comparing the function application of @{term "embedded_style \<chi>"} to @{term "embedded_style (\<^bold>\<iota>x. \<phi> x)"}
  with that to @{term "embedded_style (\<^bold>\<iota>x. \<psi> x)"}.

  Now since @{term "embedded_style \<phi>"} and @{term "embedded_style \<psi>"} are again functions (this time
  from individuals of type @{type \<nu>} to type @{type \<o>}) the precondition has to be reformulated
  to hold for the application of @{term "embedded_style \<phi>"} and @{term "embedded_style \<psi>"} to
  an arbitrary individual @{term "embedded_style x"} to capture the concept of @{text "\<A>(\<phi> \<equiv> \<psi>)"} in PLM, where @{text "\<phi>"}
  and @{text "\<psi>"} may contain @{text "x"} as a free variable.
*}

subsubsection{* Axioms of Encoding *}
  
text{*
  The last class of axioms is comprised of the axioms of encoding (see~\ref{TAO_Axioms_Encoding}):

  \begin{itemize}
    \item @{thm encoding} \hfill{(\ref{PM-encoding})}
    \item @{thm nocoder} \hfill{(\ref{PM-nocoder})}
    \item @{thm A_objects} \hfill{(\ref{PM-A-objects})}
  \end{itemize}

  Whereas the first statement (encoding is modally rigid) is a direct consequence of the semantics
  (recall that the encoding extension of a property was not relativized to possible worlds; see
   section~\ref{semantics}), the second axiom (ordinary objects do not encode) is only derivable
  by expanding the definition of the encoding extension and the meta-logical distinction
  between ordinary and abstract objects.

  Similarly the comprehension axiom for abstract objects
  depends on the meta-logic and follows from the definition of abstract objects as the power set
  of relations and the representation of encoding as set membership.

  It is again a requirement of the representation in the functional setting that
  @{term "embedded_style \<phi>"} in the comprehension axiom is a function and the condition
  it imposes on @{term "embedded_style F"} is expressed as its application to @{term "embedded_style F"}.
  The formulation in PLM on the other hand has to explicitly exclude a free occurence of @{text "x"}
  in @{text "\<phi>"}. In the functional setting this is not necessary, since the only way the condition
  @{term "embedded_style \<phi>"} imposes could depend on the @{term "embedded_style x"} bound by the
  existential quantifier would be that @{term "embedded_style x"} was given to the @{term "embedded_style \<phi>"}
  as an argument (note that for that to be possible @{term "embedded_style \<phi>"} would also have to have a different
  type as a function).

*}

subsubsection{* Summery *}
  
text{*
  Although the formulation of some of the axioms has to be adjusted to work in the environment of
  functional type theory it is possible to arrive at a formulation that faithfully represents
  the original axiom system of PLM. Future work may attempt to further align the given representation
  with PLM and compare the extents of both systems in detail.

  Furthermore a large part of the axioms can be derived independently of the technicalities of
  the representation layer by only depending on the representation of the semantics described in
  section~\ref{semantics}. Future work may explore possible options to further minimize the dependency
  on the underlying model structure.

  To verify that the axiom system is a good representation of the reference, as a next step the
  deductive system PLM as described in @{cite \<open>Chap. 9\<close> PM} is derived solely based on the
  formulation of the axioms without falling back to the meta-logic.
*}

(*<*)
end (* context Axioms *)
(*>*)


(*<*)
context PLM
begin
(*>*)
  
section{* The Deductive System PLM *}
  
text{*
  The derivation of the deductive system PLM from the constructed axiom system constitutes
  a major part of the Isabelle Theory in the appendix (see~\ref{TAO_PLM}). Its extent over
  over one-hundred pages makes it infeasible to discuss every aspect in full detail here.

  Nevertheless it is worthwhile to have a look at the mechanics of the derivation and to
  extract some interesting concepts.
*}

subsection{* Modally Strict Proofs *}
  
text{*
  \label{PLM-modally-strict}

  PLM distinguishes between two sets of theorems, the set of theorems, that are derivable from
  the complete axiom system, and the set of theorems, that have \emph{modally strict} proofs.

  A modally strict proof is a proof that does not use modally fragile axioms (namely the axiom
  of actuality described in section~\ref{axioms-actuality}).

  Although it is challenging to completely reproduce this distinction in the embedding
  (see~\ref{differences-modally-strict}), the following schema can provide a reasonable representation:

  Modally strict theorems are stated to be true for an \emph{arbitrary} semantic possible world
  in the embedding as: \mbox{@{term "[\<phi> in v]"}}

  Here the variable @{term "v"} implicitly ranges over \emph{any} semantic possible world of
  type @{type i}, including the designated actual world @{term "dw"}. Since modally fragile axioms
  only hold in @{term "dw"}, they therefore cannot be used to prove a statement formulated
  this way, as desired.

  Non-modally strict theorems on the other hand are stated to be true only for the designated
  actual world: \mbox{@{term "[\<phi> in dw]"}}

  This way necessary axioms, as well as modally fragile axioms can be used in the proofs. However
  it is not possible to infer from a modally fragile theorem that the same statement holds as a
  modally strict axiom.

  It is important to note that the set of modally-strict theorems in PLM is in fact a \emph{subset}
  of the theorems of the form \mbox{@{term "[\<phi> in v]"}} that are semantically true in the embedding.
  However, the rules introduced in PLM are stated in such a way that only this subset is in fact
  derivable without falling back to the semantics or the meta-logic. This is discussed in more detail
  in section~\ref{differences-modally-strict}.
*}

subsection{* Fundamental Metarules of PLM *}

text{*
  \label{PLM-metarules}

  The primitive rule of PLM is the modus ponens rule (see~\ref{TAO_PLM_ModusPonens}):
  
  \begin{itemize}
    \item @{thm modus_ponens[of v \<phi> \<psi>]} \hfill{(\ref{PM-modus-ponens})}
  \end{itemize}

  In the embedding this rule is a direct consequence of the semantics of the implication.

  Additionally two fundamental Metarules are derived in PLM, \emph{GEN} and \emph{RN} (see~\ref{TAO_PLM_GEN_RN}):

  \begin{itemize}
    \item @{thm rule_gen[of v \<phi>]} \hfill{(\ref{PM-rule-gen})}
    \item @{thm RN_2[of \<phi> \<psi> v]} \hfill{(\ref{PM-RN})}
  \end{itemize}

  Although in PLM these rules are derived by structural induction on the complexity of
  a formula, unfortunately this proving mechanism cannot be reproduced in Isabelle. However,
  the rules are direct consequences of the semantics described in section~\ref{semantics}.
  The same is true for the deduction rule (see~\ref{TAO_PLM_NegationsAndConditionals}):

  \begin{itemize}
    \item @{thm deduction_theorem[of v \<phi> \<psi>]} \hfill{(\ref{PM-deduction-theorem})}
  \end{itemize}

  As a consequence this rule is derived from the semantics of the implication as well.
  
  Note that these rules are the \emph{only} exceptions to the concept that the deductive system of
  PLM is completely derived from the axiom system and the primitive rule of inference (modus ponens).

*}
  
subsection{* PLM Solver *}

(*<*)
context
begin
interpretation MetaSolver .
(*>*)
text{*

  Similarly to the @{method meta_solver} described in section~\ref{meta_solver} another proving
  method is introduced, namely the @{method PLM_solver} (see~\ref{TAO_PLM_Solver}).

  This proving method is initially not equipped with any rules. Throughout the derivation of the
  deductive system of PLM, however, some of the rules of PLM are added to its set of rules.
  Furthermore at several instances further rules become trivially \emph{derivable} from the
  statements of PLM proven so far. Such rules are added to the @{method PLM_solver} as well.

  Furthermore the @{method PLM_solver} can instantiate any rule of the deductive system PLM proven
  so far or any axiom, if this allows to resolve a proving objective.

  By its construction the @{method PLM_solver} has the property, that it can \emph{only} prove
  statements that are derivable from the deductive system PLM. Thereby it is safe to use to aid
  in any proof throughout the section. As a matter of fact a lot of the simple tautological statements
  derived in the beginning of @{cite \<open>Chap. 9\<close> PM} can be proven automatically using this method.

  Unfortunately some rules that would make the solving method more powerful and would make it more
  helpful in the derivation of more complex theorems, are \emph{not} derivable from the deductive
  system itself (and consequently are \emph{not} added to the set of admissible rules). Namely
  one example is the converse of the rule RN. This circumstance is discussed in more detail in
  section (TODO: reference).

*}
(*<*)
end (* unnamed subcontext with MetaSolver interpretation *)
(*>*)

subsection{* Additional Type Classes *}
  
text{*
  There is one further subtlety one may notice in the derivation of the deductive system.
  In PLM it is possible to derive statements involving the general identity symbol by case
  distinction: if such a statement is derivable for all types of terms in the language separately,
  it can be concluded that it is derivable in general. Such a case distinction cannot be directly
  reproduced in the embedding, since no assumption can be made, that every instantiation of the
  type class @{class identifiable} is in fact one of the types of terms of PLM.

  However, there is a simple way to still formulate such general statements. This is done by
  the introduction of additional type classes. A simple example is the type class @{class id_eq}
  (see~\ref{TAO_PLM_Identity}). This new type class assumes the following statements to be true:

  \begin{itemize}
    \item @{thm id_eq_1[of v \<alpha>]} \hfill{(\ref{PM-id-eq}.1)}
    \item @{thm id_eq_2[of v \<alpha> \<beta>]} \hfill{(\ref{PM-id-eq}.2)}
    \item @{thm id_eq_3[of v \<alpha> \<beta> \<gamma>]} \hfill{(\ref{PM-id-eq}.3)}
  \end{itemize}

  Since these statements can be derived \emph{separately} for the types @{type \<nu>}, @{type \<Pi>\<^sub>0},
  @{type \<Pi>\<^sub>1}, @{type \<Pi>\<^sub>2} and @{type \<Pi>\<^sub>3}, the type class @{class id_eq} can now trivially be
  instantiated for each of these types.
*}

subsection{* The Rule of Substitution *}

subsubsection{* The Issue *}
  
text{*
  A challenge in the derivation of the deductive system that is worth to examine in
  detail is the \emph{rule of substitution}.  The rule is stated in PLM as follows
  (see~@{cite \<open>(\ref{PM-rule-sub-nec})\<close> PM}):

  \begin{addmargin}{1cm}
    If @{text "\<turnstile>\<^sub>\<box> \<psi> \<equiv> \<chi>"} and @{text "\<phi>'"} is the result of substituting the formula @{text "\<chi>"}
    for zero or more occurrences of @{text "\<psi>"} where the latter is a subformula of @{text "\<phi>"},
    then if @{text "\<Gamma> \<turnstile> \<phi>"}, then @{text "\<Gamma> \<turnstile> \<phi>'"}. [Variant: If @{text "\<turnstile>\<^sub>\<box> \<psi> \<equiv> \<chi>"}, then @{text "\<phi> \<turnstile> \<phi>'"}]
  \end{addmargin}

  Naively one could try to express this in the functional setting as follows:

  \begin{center}
    @{term "(\<And>v. [\<psi> \<^bold>\<equiv> \<chi> in v]) \<Longrightarrow> [\<phi> \<psi> in v] \<longleftrightarrow> [\<phi> \<chi> in v]"}
  \end{center}

  However this statement would \emph{not} be derivable. The issue is connected to the restriction
  of @{term "\<psi>"} being a \emph{subformula} of @{text "\<phi>"} in PLM. The formulation above would allow
  the substitution for \emph{any function} @{term "embedded_style \<phi>"} from formulas to formulas.

  Formulas in the embedding have type @{type \<o>} which is internally represented by functions of the
  type @{typ "j\<Rightarrow>i\<Rightarrow>bool"}. Reasoning is only defined to be classically in the designated state
  @{term "dj"}, though. In the formulation above nothing would prevent @{term "embedded_style \<phi>"}
  to be a function with the following internal representation:
  \mbox{@{term "\<lambda> \<psi> . make\<o>(\<lambda> s w .  \<forall> s . eval\<o> (embedded_style \<psi>) s w)"}}

  So nothing prevents @{term "embedded_style \<phi>"} from evaluating its argument for a state
  different from the designated actual state @{term "dj"}. The condition @{term "(\<And>v. [\<psi> \<^bold>\<equiv> \<chi> in v])"}
  on the other hand only requires @{term "embedded_style \<psi>"} and @{term "embedded_style \<chi>"} to be
  equivalent in all possible worlds particularly in the \emph{actual state} - no statement about
  other states is implied.

  Another issue arises if one considers one of the example cases of legitimate uses of the rule
  of substitution in PLM (see~@{cite \<open>(\ref{PM-rule-sub-nec})\<close> PM}):

  \begin{addmargin}{1cm}
    If @{text "\<turnstile> \<exists>x A!x"} and @{text "\<turnstile>\<^sub>\<box> A!x \<equiv> \<not>\<diamond>E!x"}, then @{text "\<turnstile> \<exists>x \<not>\<diamond>E!x"}.
  \end{addmargin}

  This does not follow from the naive formulation above. Since @{text "x"} is \emph{bound} by
  the existential quantifier, in the functional representation @{term "embedded_style \<phi>"}
  has to have a different type: to be applicable in this example @{term "embedded_style \<phi>"}
  has to be \mbox{@{term[eta_contract=false] "(embedded_style \<phi>) = (\<lambda> \<psi> . embedded_style (\<^bold>\<exists> x . \<psi> x))"}},
  whereas @{term "embedded_style \<psi>"} and @{term "embedded_style \<chi>"} themselves have to be functions as follows:
  \mbox{@{term[eta_contract=false] "(embedded_style \<psi>) = (\<lambda> x . embedded_style \<lparr>A!,x\<rparr>)"}} and
  \mbox{@{term[eta_contract=false] "(embedded_style \<chi>) = (\<lambda> x . embedded_style (\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<rparr>))"}}.
  Furthermore now the equivalence condition has to be \mbox{@{term "\<And> x v. [\<psi> x \<^bold>\<equiv> \<chi> x in v]"}}.
  This is analog to the fact that @{text "x"}
  is a free variable in the condition @{text "\<turnstile>\<^sub>\<box> A!x \<equiv> \<not>\<diamond>E!x"} in PLM.

  
*}

subsubsection{* Solution *}

text{*

  The embedding employs a solution that is rather complex, but can successfully address the issues 
  described above.

  First of all the following definition is introduced:

  \begin{center}
    @{thm Substable_def[expand2, of cond \<phi>]}
  \end{center}

  Given a condition @{term "cond"} a function @{term "embedded_style \<phi>"}
  is considered @{term "Substable"}, if and only if for all @{term "embedded_style \<psi>"}
  and  @{term "embedded_style \<chi>"} (which may have an arbitrary type) it follows in each
  possible world @{term "v"} that \mbox{@{term "[\<phi> \<psi> \<^bold>\<equiv> \<phi> \<chi> in v]"}}.

  Now several introduction rules for this property are derived. The idea is to capture the
  notion of \emph{subformula} in PLM. A few examples are:

  \begin{itemize}
    \item @{lemma "Substable cond (\<lambda>\<phi>. embedded_style \<Theta>)"
            by (simp add: embedded_style_def Substable_intro_const)}
    \item @{lemma "Substable cond \<psi> \<Longrightarrow> Substable cond (\<lambda>\<phi>. embedded_style ( \<^bold>\<not>\<psi> \<phi>))"
            by (simp add: embedded_style_def Substable_intro_not)}
    \item @{lemma "Substable cond \<psi> \<and> Substable cond \<chi> \<Longrightarrow> Substable cond (\<lambda>\<phi>. embedded_style (\<psi> \<phi> \<^bold>\<rightarrow> \<chi> \<phi>))"
            by (simp add: embedded_style_def Substable_intro_impl)}
  \end{itemize}

  These rules can be derived from the rules proven in PLM.

  Now as mentioned above in the functional setting substitution has to be allowed not only for formulas,
  but also for \emph{functions} to formulas. To that end the type class @{class Substable} is introduced
  that fixes a condition @{term "Substable_Cond"} to be used as @{term "cond"} in the definition above
  and assumes the following:

  \begin{center}
    @{thm Substable_class.rule_sub_nec[of \<phi> \<psi> \<chi> \<Theta> v]}
  \end{center}

  If @{term "embedded_style \<phi>"} is @{term "Substable"} (as per the definition above) under the
  condition @{term "Substable_Cond"} that was fixed in the type class, and @{term "embedded_style \<psi>"}
  and @{term "embedded_style \<chi>"} satisfy the fixed condition @{term "Substable_Cond"}, then everything
  that is true for @{term "[\<phi> \<psi> in v]"} is also true for @{term "[\<phi> \<chi> in v]"}.

  Now as a base case this type class is \emph{instantiated} for the type of formulas @{type \<o>} with
  the following definition of @{term "Substable_Cond"}:

  \begin{center}
    @{thm Substable_Cond_\<o>_def[expand2, of \<psi> \<chi>]}
  \end{center}

  Furthermore the type class is instantiated for \emph{functions} from an arbitrary type to
  a type of the class @{class Substable} with the following definition of @{term "Substable_Cond"}:

  \begin{center}
    @{thm Substable_Cond_fun_def[expand2, of \<psi> \<chi>]}
  \end{center}

  This construction now allows substitutions in all cases required by the original formulation in PLM.
*}
  
subsubsection{* Proving Methods *}

text{*

  Although the construction above covers exactly the cases in which PLM allows substitutions, it does
  not yet have a form that allows it to conveniently \emph{apply} the rule of substitution. In order
  to apply the rule, it first has to be established that a formula can be decomposed into a
  function with the substituents as arguments and it further has to be shown that this function
  satisfies the appropriate @{term "Substable"} condition. This complexity prevents any reasonable
  use cases. This problem is mitigated by the introduction of proving methods, that are convenient
  to use. The main method is called @{method PLM_subst_method}.

  This method uses a combination of pattern matching and automatic rule application, to provide
  a convenient way to apply the rule of substitution in practice.

  For example assume the current proof objective is @{term "[\<^bold>\<not>\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<rparr> in v]"}. Now it is possible to
  apply the @{method PLM_subst_method} method as follows:
  \begin{center}
    @{theory_text "apply (PLM_subst_method \"\<lparr>A!,x\<rparr>\" \"(\<^bold>\<not>(\<^bold>\<diamond>\<lparr>E!,x\<rparr>))\""}
  \end{center}
  This will now automatically analyze the current proof goal, look for an appropriate choice of
  a function @{term "embedded_style \<phi>"}, apply the substitution rule and resolve the substitutability
  claim about @{term "embedded_style \<phi>"}. Consequently it can resolve the current proof objective
  by producing two new proving goals: @{term "\<forall>v. [\<lparr>A!,x\<rparr> \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<rparr> in v]"} and @{term "[\<^bold>\<not>\<lparr>A!,x\<rparr> in v]"},
  as expected. The complexity of the construction above is hidden away entirely.

  Similarly assume the proof objective is @{term "[\<^bold>\<exists> x . (\<^bold>\<not>(\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>))  in v]"}. Now the method
  @{method PLM_subst_method} can be invoked as follows:
  \begin{center}
    @{theory_text "apply (PLM_subst_method \"\<lambda>x . \<lparr>A!,x\<^sup>P\<rparr>\" \"\<lambda>x . (\<^bold>\<not>(\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>))\""}
  \end{center}
  This will result in the new proving goals:
  \mbox{@{term "\<forall>x v. [\<lparr>A!,x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> in v]"}} and \mbox{@{term "[\<^bold>\<exists>x. \<lparr>A!,x\<^sup>P\<rparr> in v]"}}, as
  desired.

*}  

subsubsection{* Summery *}

text{*
  Although an adequate representation of the rule of substitution in the functional setting
  is challenging, the above construction allows a convenient use of the rule. Moreover it is
  important to note that despite the complexity of the representation no assumptions about
  the meta-logic or the underlying model structure were made. The construction is completely
  derivable from the rules of PLM itself, so the devised rule is safe to use without
  compromising the provability claim of the layered structure of the embedding.

  All statements that are proven using the constructed substitution methods, remain derivable
  from the deductive system of PLM.
*}

subsection{* Automation and Interactivity in the Embedding *}
  
text{*
  
*}  

subsection{* Summery *}
  
text{*
  Despite the presented challenges it was possible to derive a full representation of
  the deductive system PLM, as described in @{cite \<open>Chap. 9\<close> PM} without sacrificing the
  layered structure of the embedding.
*}
  
(*<*)
end (* context PLM*)
(*>*)

chapter{* Discussion and Results *}

section{* Differences between the Embedding and PLM *}
  
text{*
  Although the embedding attempts to represent the language and logic of PLM as precisely
  as possible, it is important to note that there are certain differences between PLM and
  its representation in Isabelle/HOL.
*}
  
subsection{* Terms and Variables *}

text{*

  In PLM an individual term can be an individual variable, an individual constant or a definite
  description. A large number of statements is formulated using specific variables. From such
  a statement its universal generalization can be derived (using the rule GEN), which then can be
  instantiated for any individual term, given that it denotes (\mbox{@{text "\<exists>\<beta> \<beta> = \<tau>"}}).

  As already mentioned in sections~\ref{individual-terms-and-descriptions} and~\ref{quantification-axioms}
  the embedding uses a slightly different approach. In the embedding individual variables and
  individual terms have different \emph{types} and an individual variable (of type @{type \<nu>})
  has to be converted to an individual term (of type @{type \<kappa>}) using the decoration @{term "DUMMY\<^sup>P"},
  so that it can be used for example in an exemplifcation formula (which is defined for terms of
  type @{type \<kappa>}).

  The technicalities of this approach and a discussion about the acuracy of this representation
  were already given in the referenced sections, so at this point it suffices to summerize the
  resulting differences between the embedding and PLM:

  \begin{itemize}
    \item The individual variables of PLM are represented as variables of type @{type \<nu>} in the embedding.
    \item Individual constants can be represented by declaring a constant of type @{type \<nu>}.
    \item Meta-level variables (like @{text "\<tau>"}) ranging over all individual terms
          in PLM can be represented as variables of type @{type \<kappa>}.
    \item Objects of type @{type \<nu>} have to be explicitly converted to objects of type @{type \<kappa>}
          if they are to be used in a context that also allows individual terms.
    \item The axioms of quantification are adjusted to go along with this representation
          (see~\ref{quantification-axioms}).
  \end{itemize}

  In PLM the situation for relation variables, constants and terms is analog. However the
  embedding uses the following simplification in order to avoid the additional complexity
  introduced for individuals:

  Since at the time of writing PLM unconditionally asserts \mbox{@{text "\<exists>\<beta> \<beta> = \<tau>"}}
  is for any relation term by an axiom, the embedding uses only one type (@{text "\<Pi>\<^sub>n"}) for each
  arity of relations. Therefore no special type conversion between variables and terms is necessary
  and every relation term can immediately be instantiated for a variable of type (@{text "\<Pi>\<^sub>n"}).
  This hides the additional steps PLM employs for such instantiations (the generalization by GEN
  followed by an instantiation using quantification theory). Since \mbox{@{text "\<exists>\<beta> \<beta> = \<tau>"}} holds
  unconditionally for relation terms, this simplification is justified.

  Recent developments as described in section~\ref{paradox}, however, suggest that \mbox{@{text "\<exists>\<beta> \<beta> = \<tau>"}}
  will likely no longer hold unconditionally for every relation term in future versions of PLM, so
  future versions of the embedding will have to include a distinction between relation terms and
  relation variables in a similar way as it is already done for individuals.

*}
  
subsection{* Propositional Formulas and $\lambda$-Expressions *}
  
text{*
  The main difference between the embedding and PLM is the fact that the embedding does
  not distinguish between propositional and non-propositional formulas. 
*}
  
subsection{* Modally-strict Proofs and the Converse of RN *}

(*<*)
context PLM
begin
(*>*)
  
text{*

\label{differences-modally-strict}

As already mentioned in section~\ref{PLM-modally-strict}, modally-strict theorems
in the embedding are stated in the form \mbox{@{term "[\<phi> in v]"}} for arbitrary @{term "v"}.
On the other hand more statements of the form \mbox{@{term "[\<phi> in v]"}} are semantically
true in the embedding, than would be derivable using modally-strict proofs in PLM.

To understand this circumstance and the solution for this issue used in the embedding,
the converse of the meta-rule RN has to be considered.

In PLM the metarule RN states in essence that if there is a modally strict proof for @{text "\<phi>"},
then @{text "\<box>\<phi>"} is derivable as a theorem. Therefore the converse of RN would be that if 
@{text "\<box>\<phi>"} is derivable, then there is a modally strict proof for @{text "\<phi>"}.

The discussion in remark (\ref{PM-abstraction-contingent})@{cite PM} shows that this is
not true in PLM. However in the embedding the following is derivable from the semantics of
the box operator:

\begin{center}
  @{lemma "[\<^bold>\<box>\<phi> in dw] \<Longrightarrow> (\<forall> v . [\<phi> in v])" by (simp add: Semantics.T6) }
\end{center}

So although the converse of RN is not true in PLM, an equivalent statement for theorems of
the form \mbox{@{term "[\<phi> in v]"}} in the embedding can be derived from the semantics.

The reason for this is that modally-strict theorems are in fact a subset of a larger class of
theorems, namely the theorems that are \emph{necessarily true}. Semantically a statement of the form
\mbox{@{term "[\<phi> in v]"}} in the embedding is derivable, whenever @{term "embedded_style \<phi>"}
is a \emph{necessary theorem}.

Modally-strict theorems in PLM on the other hand are defined as a proof-theoretic concept:
modally-strict proofs are not allowed to use modally fragile axioms. Therefore they are solely derived
from axioms whose necessitations are axioms as well (see~\ref{axiom-schemata}). PLM now proves the fact
that a modally strict derivation of @{text "\<phi>"} implies that there is a derivation of @{text "\<box>\<phi>"}
by induction on the the length of the proof. However, remark (\ref{PM-abstraction-contingent})@{cite PM}
gives an example of a case where the converse is false.

The problem for the embedding is that there is no semantic characterization of a statement that allows
to decide whether it is a necessary theorem or a modally-strict theorem. Therefore the embedding has
to express modally-strict theorems as necessary theorems. As seen above for this set of theorems the
converse of RN is in fact true, though.

This still does not compromise the concept that any statement that is derived in \ref{TAO_PLM}
is also derivable in PLM: the basis of this concept is that no proofs may rely on the meta-logic, but
only the rules that are derived in PLM are allowed. To guarantee that no statement of the form
\mbox{@{term "[\<phi> in v]"}} is derived that is \emph{not} a modally-strict theorem of PLM,
the converse of RN is not stated as an admissible rule for these proofs.

Unfortunately this has the consequence that the proving method @{method PLM_solver} cannot be
equipped with an elimination rule for the box-operator, which significantly reduces its power
as an automated proving method. Preserving the claim that theorems derived in the embedding
are also theorems of PLM was considered to be more important, though.

*}

(*<*)
end (* context PLM *)
(*>*)

section{* A Paradox in PLM *}

text{*
  \label{paradox}

  During the analysis of the constructed embedding it was discovered,
  that the formulation of the theory in PLM allowed paradoxical constructions.

  This section first describes the process that led to the discovery of the paradox and
  the role the embedding played in it, after which the construction of the paradox is
  outlined in the language of PLM.

  Note that the paradox has since been confirmed by Edward Zalta\footnote{Edward Zalta decided to
  refer to the paradox as \emph{Kirchner's paradox} in the future} and a vivid discussion
  about the repercussions and possible solutions has developed. At the time of writing
  it has become clear that there are several options to recover from the paradox while
  in essence retaining the full set of theorems of PLM. So far no final decision has been
  reached about which option will be implemented in future versions of PLM.
*}

subsection{* Discovery of the Paradox *}
  
text{*
  The discovery of the paradox originates in the analysis of the representation of
  @{text "\<lambda>"}-expressions in the embedding. The syntactic distinction between propositional and
  non-propositional formulas of PLM is replaced by the concept of \emph{proper maps}\footnote{Prior
  to the discussion that followed the discovery of the paradox \emph{proper maps} were called
  \emph{propositional maps} in the embedding; the term \emph{proper maps} is based on the concept of
  \emph{proper @{text "\<lambda>"}-expressions} that may be part of future versions of PLM to avoid the paradox.
  TODO: change this?} as described in section~\ref{lambda-expressions}.

  The idea behind this replacement was that, although it allows more @{text "\<lambda>"}-expressions
  than PLM, every @{text "\<lambda>"}-expressions of PLM would become a @{text "\<lambda>"}-expression of the
  embedding. While verifying this concept, it was discovered, that @{text "\<lambda>"}-expressions of
  the form \mbox{@{text "[\<lambda>y F\<iota>x(y[\<lambda>z Rxz])]"}} in which the bound variable @{text "y"} occurs in
  an encoding formula inside the matrix of a definite description, were part of PLM, but their
  matrix was \emph{not} a proper map in the embedding and therefore @{text "\<beta>"}-conversion
  was not derivable for these terms.

  In the attempt to proof that @{text "\<beta>"}-conversion would in fact follow for these expressions
  in the embedding in Isabelle, it first became clear, that this is not the case without a restriction
  of the Aczel-model. Namely without some kind of restriction of the map from abstract objects to urelements,
  @{text "\<beta>"}-conversion would not be derivable for these cases.

  In order to better understand how the embedding could accommodate these circumstances, the
  consequences of allowing @{text "\<beta>"}-conversion in the mentioned cases \emph{by assumption}
  were further studied in the embedding which lead to the first proof of inconsistency
  (see~\ref{TAO_Paradox_original-paradox}. Since the meta-logic was not used in the proof, it was
  possible to reconstruct an equivalent proof in the language of PLM, which then served as the
  basis of further discussions with Edward Zalta.

  Since then the issue leading to the paradox was identified as the \emph{description backdoor}
  (see~\ref{TAO_Paradox_description_backdoor}) that can be used to construct a variety of
  paradoxical cases, e.g. the paradox mentioned in section~\ref{russell-paradox} can be reconstructed.
  This refined version of the paradox is used in the inconsistency proof in \ref{TAO_Paradox_russell-paradox}
  and the following reconstruction in the language of PLM.
*}

subsection{* Construction using the Language of PLM *}
  
text{*

  Object theory distinguishes between propositional and
  non-propositional formulas. Propositional formulas are not allowed to
  contain encoding subformulas, so for example \mbox{@{text "\<exists>F xF"}} is not
  propositional. Only propositional formulas can be the matrix of a
  @{text "\<lambda>"}-expression, so \mbox{@{text "[\<lambda>x \<exists>F xF]"}} is not a valid term of
  the theory - it is excluded syntactically.

  The reason for this is that considering \mbox{@{text "[\<lambda>x \<exists>F xF & \<not>Fx]"}} a valid, denoting
  @{text "\<lambda>"}-expression for which @{text "\<beta>"}-conversion holds would result in a
  paradox as described in section~\ref{russell-paradox}.

  Now the idea was that not allowing non-propositional formulas in
  @{text "\<lambda>"}-expressions would be sufficient to exclude \emph{all} cases that lead to
  inconsistencies.

  During the construction of the embedding this was shown to be incorrect, though.

  The problem is the \emph{description backdoor}. The syntactical definition
  of propositional formulas does allow expressions of the following form:
  \mbox{@{text "[\<lambda>y F\<iota>x\<psi>]"}} where @{text "\<psi>"} does not have to be propositional itself,
  but can be \emph{any} formula. This is due to the definition of \emph{subformula}:
  by this definition @{text "\<psi>"} is \emph{not} a subformula of @{text "F\<iota>x\<psi>"}, so @{text "\<psi>"}
  \emph{may} contain encoding subformulas itself, and @{text "F\<iota>x\<psi>"} is still considered to be a
  propositional formula.

  This was deemed to be no problem and for cases like \mbox{@{text "[\<lambda>y F\<iota>x(xG)]"}} as
  they are mentioned in PLM this is indeed true.

  It had not been considered that @{text "y"} may appear within the matrix of
  such a description and more so, it may appear in a encoding formula
  within the matrix of such a description, for example 
  \mbox{@{text "[\<lambda>y F\<iota>x(xG & yG)]"}} is still considered a propositional formula. At least
  it had not been considered that this is a problem, but:

  This way the following construction is possible:

  \begin{equation}\tag{1}
    @{text "[\<lambda>y [\<lambda>p \<forall>p(p\<rightarrow>p)]\<iota>x(x = y & \<psi>)]"}
  \end{equation}

  Here @{text "\<psi>"} can be an arbitrary non-propositional formula in which @{text "x"} and @{text "y"}
  may be free and 1 is still a valid, denoting @{text "\<lambda>"}-expression for which
  @{text "\<beta>"}-conversion holds.

  Now it is possible to show that by @{text "\<beta>"}-conversion and description
  theory the following is derivable:

  \begin{equation}\tag{2}
    @{text "[\<lambda>y [\<lambda>p \<forall>p(p\<rightarrow>p)]\<iota>x(x = y & \<psi>)]x \<equiv> \<psi>^x_y"}
  \end{equation}

  \begin{remark}
    Using a modally-strict proof only the following is derivable:\\
    \mbox{@{text "[\<lambda>y [\<lambda>p \<forall>p(p\<rightarrow>p)]\<iota>x(x = y & \<psi>)]x \<equiv> \<A>\<psi>^x_y"}}\\
    For the construction of the paradox, the modally fragile statement
    is sufficient, though. Note, however, that it is also possible
    to construct similar paradoxical cases without appealing to
    any modally-fragile axioms or theorems.
  \end{remark}

  This effectively undermines the intention of restricting @{text "\<lambda>"}-expressions
  to only propositional formulas:

  Although \mbox{@{text "[\<lambda>x \<exists>F xF & \<not>Fx]"}} is not part of the language, it is possible to
  formulate the following instead:

  \begin{equation}\tag{3}
    @{text "[\<lambda>y [\<lambda>p \<forall>p(p\<rightarrow>p)]\<iota>x(x = y & (\<exists>F yF & \<not>Fy))]"}
  \end{equation}

  If one considers 2 now, one can see that this @{text "\<lambda>"}-expressions behaves
  exactly the way that \mbox{@{text "[\<lambda>x \<exists>F xF & \<not>Fx]"}} would do, if it were part of the
  language (i.e. the result of @{text "\<beta>"}-reduction for \mbox{@{text "[\<lambda>x \<exists>F xF & \<not>Fx]"}} would be
  the same as the right hand side of 2 when applied to 3). So the @{text "\<lambda>"}-expression
  in 3 can be used to reproduce the paradox mentioned in section~\ref{russell-paradox}.
*}

subsection{* Possible Solutions *}

text{*
  Fortunately no theorems were derived in PLM, that actually depend on problematic
  @{text "\<lambda>"}-expressions as described above. Therefore it is possible to recover from the
  paradox without losing any theorems. At the time of writing it seems likely that
  a concept of \emph{proper} @{text "\<lambda>"}-expressions will be introduced to the theory (either explicitly
  or implicitly), and only \emph{proper} @{text "\<lambda>"}-expressions will be forced to have
  denotations and allow @{text "\<beta>"}-conversion. Problematic @{text "\<lambda>"}-expressions that would
  lead to paradoxes, would not be considered \emph{proper}. Several options are available to define
  the propriety of \emph{@{text "\<lambda>"}-expressions} and adjust PLM in full detail.

  As a consequence the purely syntactical distinction between propositional
  and non-propositional formulas is no longer sufficient to guarantee
  that any relation term has a denotation. The embedding of the theory supports
  the idea that an adequate definition of \emph{proper @{text "\<lambda>"}-expressions}
  could replace this distinction entirely yielding a much broader set of relations.
  The philosophical implications of such a radical modification of the theory
  have not yet been analysed entirely, though, and at the time of writing
  it is an open question whether such a modification may be implemented in
  future versions of PLM.

*}

section{* A Meta-Conjecture about Possible Worlds *}
  
  
chapter{* Technical Issues *}
  
section{* Limitations of Type Classes and Locales *}

section{* Case Distinctions by Type *}

section{* Structural Induction *}
  
(*<*)
end
(*>*)
