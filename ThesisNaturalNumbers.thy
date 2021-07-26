(*<*)
theory ThesisNaturalNumbers
  imports AOT_NaturalNumbers
begin
(*>*)

chapter\<open>Natural Numbers in AOT\<close>text\<open>\label{NaturalNumbers}\<close>

text\<open>
While AOT can represent mathematical theories including their deductive systems themselves
as @{emph \<open>abstract objects\<close>}, as mentioned in section (TODO: ref), it distinguishes this analysis of
@{emph \<open>Theoretical Mathematics\<close>} from the notion of @{emph \<open>Natural Mathematics\<close>}. @{emph \<open>Natural\<close>}
Mathematics consists of ordinary, pretheoretic claims about mathematical objects (TODO: cite PLM (303))
and arise directly as abstraction of the exemplification patterns of ordinary objects rather
than being based on the axioms of some mathematical theory.

Following this idea, the claim of PLM's Chapter 14 (TODO: cite) is that natural numbers and Peano
Arithmetic can be naturally defined within object theory and the laws they abide by up to and including
Second-Order Peano Arithmetic can be derived without having to appeal to any intrinsically mathematical
axioms or notions.

We have reproduced parts of this construction in our implementation@{footnote \<open>At the
time of writing the implementation encompasses the construction of natural numbers including
mathematical induction. We expect a full derivation of Second-Order Peano Arithmetic in the
foreseeable future.\<close>} and arrived at the following results:
\<^item> The construction of natural numbers is sound and mathematical induction is derivable.
\<^item> We could model the additional axioms required in the construction in our framework.
\<^item> We could generalize one of the aforementioned axioms, strengthening the theoretical basis and
  justification of the construction.
\<^item> We could suggest several amendments to the construction and discover and fix several
  minor errors and inconsistencies in the presentation.
\<close>
text\<open>
Interestingly, there are interactions between this construction and the paradox discovered
in~\cite{Thesis} and discussed in TODO: cite session. We will describe this interaction in more
detail in the following sections while reproducing the construction of Nodelman and Zalta and
thereby show how our work towards amending object theory to overcome the paradox was a prerequisite
for the current version of the construction. TODO: actually do that. Example: the elimination of the
Rigidity axioms, which were required for constructing modally rigid numbers, based on the extension
of relation comprehension and "Kirchner's Theorem", etc.

TODO: remark about forgoing details about significance of terms throughout the following chapter,
while PLM and the implementation make them explicit. Also think about how best to cite the implementation
throughout the text.
\<close>

section\<open>General Idea of the Construction\<close>

text\<open>
The strategy for constructing natural numbers in AOT follows the idea of Frege's Theorem. (TODO: cite.)
Frege showed that the Peano axioms can be derived from @{emph \<open>Hume's Principle\<close>} using Second-Order
Logic. Hume's Principle states that the number of @{term F}s is equal to the number of @{term G}s if and
only if @{term F} and @{term G} are @{emph \<open>equinumerous\<close>}. Two relations are @{emph \<open>equinumerous\<close>},
if and only if there is a one-to-one correspondence between them or, in other words, if and only if
there is a bijection between the objects exemplifying @{term F} and @{term G}. (TODO: add some citations).

Frege himself derived Hume's Principle from @{emph \<open>Basic Law V\<close>}, which together with second-order
logic leads to Russel's Paradox. However, deriving Peano arithmetic @{emph \<open>from\<close>} Hume's Principle
itself does not require @{emph \<open>Basic Law V\<close>}. In Chapter 14 PLM, Nodelman and Zalta propose a
definition of @{emph \<open>equinumerosity\<close>} and @{emph \<open>the number of @{term F}s\<close>} in object theory
and derive Hume's Principle. Based on that Natural Numbers and Peano Arithmetic become consistently
derivable as expected.
\<close>

section\<open>Equinumerosity of Relations\<close>

text\<open>On the basis of traditional mathematical training based on set theory and functional logic,
the seemingly most natural conception of @{emph \<open>equinumerosity\<close>} is based on the notion of a
bijection. Two properties are equinumerous, respectively they count the same number of objects,
if and only if there is a bijection between the sets of objects they exemplify.

However, this conception of equinumerosity relies on objects of theoretical mathematics
and their axiomatization (sets, functions, bijections). While object theory can in fact define
those notions as well, it takes relations to be the more primitive, fundamental concept and thereby
prefers a definition in terms of relations alone.

The concept of there being a bijection between the sets of objects two properties exemplify can 
equivalently be captured by the notion of there being a @{emph \<open>one-to-one correspondence\<close>} between
the properties.

A @{emph \<open>one-to-one correspondence\<close>} between the properties @{term F} and @{term G} is a relation
@{term R}, s.t. (1) for every object @{term x} that exemplifies @{term F}, there is a unique object
@{term y} exemplifying @{term G}, s.t. @{term x} bears @{term R} to @{term y} and conversely (2) for
every object @{term y} that exemplifies @{term G}, there is a unique object @{term x} exemplifying
@{term F}, s.t. @{term x} bears @{term R} to @{term y}. Formally:@{footnote \<open>Note that similar to
the previous sections we are again directly quoting theorems verified in the Isabelle theory.\<close>}

@{lemma[display] \<open>print_as_theorem \<guillemotleft>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> G \<equiv> \<forall>x ([F]x \<rightarrow> \<exists>!y ([G]y & [R]xy)) & \<forall>y ([G]y \<rightarrow> \<exists>!x ([F]x & [R]xy))\<guillemotright>\<close> by (auto dest: "&E" "1-1-cor"[THEN "\<equiv>\<^sub>d\<^sub>fE"] intro!: print_as_theoremI "\<equiv>I" "\<rightarrow>I" "&I" "cqt:2[const_var]"[axiom_inst] "1-1-cor"[THEN "\<equiv>\<^sub>d\<^sub>fI"])}

However, this unrestricted notion of one-to-one correspondence is not well suited for a definition
of equinumerosity that validates Hume's principle in AOT. The intuitive reason for this is that abstract
objects cannot be counted. In particular, recall that there are distinct, but
exemplification-indistinguishable abstract objects (TODO: make sure this is mentioned earlier):

@{thm[display] "aclassical2"[print_as_theorem]}

Based on this fact, we can prove that there is no one-to-one correspondence between @{term \<open>\<guillemotleft>A!\<guillemotright>\<close>}
and itself:@{footnote \<open>We choose this opportunity to showcase that reasoning in object theory using
our embedding in Isabelle is intuitively understandable. TODO: maybe add "once more"\<close>}
\<close>

AOT_theorem \<open>\<not>\<exists>R R |: A! \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> A!\<close>
proof(rule "raa-cor:2") \<comment> \<open>Proof by contradiction.\<close>
  AOT_assume \<open>\<exists>R R |: A! \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> A!\<close> \<comment> \<open>Assume the contrary.\<close>
  then AOT_obtain R where 0: \<open>R |: A! \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow> A!\<close> \<comment> \<open>Let @{term R} be a witness.\<close>
    using "\<exists>E" by metis 
  \<comment> \<open>By definition of a one-to-one correspondence it follows that:\<close>
  AOT_hence \<open>\<forall>x ([A!]x \<rightarrow> \<exists>!y ([A!]y & [R]xy))\<close>
    using "1-1-cor"[THEN "\<equiv>\<^sub>d\<^sub>fE"] "&E" by blast
  \<comment> \<open>Now let @{term a} and @{term b} be witnesses to the theorem cited earlier in the text.\<close>
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
So if @{emph \<open>equinumerosity\<close>} was contingent on the existence of a full one-to-one correspondence,
@{term \<open>\<guillemotleft>A!\<guillemotright>\<close>} would not be equinumerous to itself and consequently equinumerosity
would not be an equivalence relation. However, Frege's Theorem does rely on equinumerosity being
an equivalence relation. Fortunately, there is a natural solution to this issue.
As mentioned in the introduction of this chapter, natural mathematics arises from abstracting
patterns of @{emph \<open>ordinary\<close>} objects. And ordinary objects are what can naturally be counted.
Hence Nodelman and Zalta introduce the notion of one-to-one correspondences among the ordinary
objects. To that end, they introduce the restricted variables @{term u}, @{term v}, @{term r}, @{term s}
that range over only the ordinary objects.@{footnote \<open>Recall the discussion about reproducing
restricted variables in the embedding in: TODO.\<close>} Using these restricted variables, a one-to-one
correspondence among the ordinary objects can be defined in the same way as a full one-to-one
correspondence:

@{lemma[display] \<open>print_as_theorem \<guillemotleft>R |: F \<^sub>1\<^sub>-\<^sub>1\<longleftrightarrow>\<^sub>E G \<equiv> \<forall>u ([F]u \<rightarrow> \<exists>!v ([G]v & [R]uv)) & \<forall>v ([G]v \<rightarrow> \<exists>!u ([F]u & [R]uv))\<guillemotright>\<close> by (auto dest: "&E" "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fE"] intro!: print_as_theoremI "\<equiv>I" "\<rightarrow>I" "&I" "cqt:2[const_var]"[axiom_inst] "equi:2"[THEN "\<equiv>\<^sub>d\<^sub>fI"])}

Based on one-to-one correspondences on the ordinary objects, equinumerosity on the ordinary objects
can be defined and can indeed shown to be an equivalence relation: TODO: sketch the proofs at least
a bit? At least cite through the progression of theorems leading to them. This would be an opportunity
to mention the elimination of the rigidity axiom due made possible by results from the embedding.

@{thm[display] "equi:3"[of F G] "eq-part:1"[of _ F, print_as_theorem] "eq-part:2"[of _ F G, print_as_theorem] "eq-part:3"[of _ F G H, print_as_theorem]}
\<close>

section\<open>The Number of Fs and Hume's Theorem\<close>

text\<open>
To state Hume's Theorem additionally to the definition of @{emph \<open>equinumerosity\<close>} above,
a definition of @{emph \<open>The Number of @{term F}s\<close>} (written as @{term \<open>\<guillemotleft>#F\<guillemotright>\<close>}) is required.
To that end Nodelman and Zalta (following Frege) first define what it means for an object
to number a property as follows:

@{thm[display] "numbers[den]"[THEN "\<rightarrow>E", OF "cqt:2[const_var]"[axiom_inst], of _ x G, print_as_theorem]}

An abstract object @{term x} numbers a property @{term G}, if it encodes exactly those properties,
such that @{emph \<open>actually exemplifying\<close>} them is equinumerous to @{term G}.
An alternative choice would be to forgo the actuality operator and merely require that @{term x}
encodes exactly those properties that are equinumerous to @{term F} itself.@{footnote \<open>Note
that earlier derivations used this definition, but were amended in the more recent presentation
of number theory in PLM. TODO: Cite e.g. \url{http://mally.stanford.edu/Papers/numbers.pdf\<close>}.}
 However, this would have the undesirable consequence that numbering properties would depend on modal context. For a detailed
discussion of this issue refer to (TODO: cite PLM; maybe reproduce some of it here).

Now @{emph \<open>The Number of @{term G}s\<close>} can simply be defined as @{emph \<open>the\<close>} object that numbers
@{term G}:

@{thm[display] "num-def:1"}

Using these definitions Nodelman and Zalta can indeed derive Hume's theorem:

@{thm[display] "hume:2"[of F G]}

Note that, due to the fact that AOT's definite descriptions are modally rigid and refer to objects
in the actual world, this theorem is not modally strict.@{footnote \<open>This is signified by the turnstile
symbol @{text "\<^bold>\<turnstile>"}. Modally-strict theorems, in contrast, are signified by @{text "\<^bold>\<turnstile>\<^sub>\<box>"}. However,
for increased readability we adopt the convention that unmarked theorems are understood to be
modally-strict. We have configured Isabelle's pretty printing accordingly.\<close>} However, the following variant is a necessary fact (TODO: think about poking Zalta by equating modally strict and necessary):

@{thm[display] "hume-strict"[of _ F G, print_as_theorem]}

The details of this derivation are described in PLM TODO: cite and are implemented in our
embedding in TODO: cite.

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
  Given the fact that we defined numbers by means of the properties they number, which is in particular based
on the number of objects those properties exemplify, a natural definition of the number zero arises.
The number zero is the object that numbers the empty property, to be more precise the number of
@{emph \<open>being a non-self-identical ordinary object\<close>}.@{footnote \<open>To be precise being a
non-self-identical@{text \<open>\<^sub>E\<close>} object. This distincation is non-trivial: While @{thm ord_eq_e_eq[of _ x, print_as_theorem]} is a theorem,
due to the hyperintensionality of object theory, it does not have to be the case that
@{term \<open>\<guillemotleft>[\<lambda>x O!x & x \<noteq>\<^sub>E x]\<guillemotright>\<close>} and @{term \<open>\<guillemotleft>[\<lambda>x O!x & x \<noteq> x]\<guillemotright>\<close>} are the same property (as a matter of fact it is
not even asserted @{emph \<open>a priori\<close>} that the latter even denotes a property at all). So
@{term \<open>\<guillemotleft>#[\<lambda>x O!x & x \<noteq>\<^sub>E x]\<guillemotright>\<close>} and @{term \<open>\<guillemotleft>#[\<lambda>x O!x & x \<noteq> x]\<guillemotright>\<close>} are not the same object
@{emph \<open>a priori\<close>}, even though it is of course a theorem that they are identical. But this theorem
has to appeal to the fact that both properties are equinumerous and to Hume's Theorem.
Further examples of terms denoting zero are @{term \<open>\<guillemotleft>#[\<lambda>x x \<noteq> x]\<guillemotright>\<close>} and
@{term \<open>\<guillemotleft>#[\<lambda>x \<exists>p (p & \<not>p)]\<guillemotright>\<close>} also denote the same object. More generally we can prove that
@{thm "0F:3"[of _ F, print_as_theorem]} (TODO: cite proof), i.e. the number of any property
that's necessarily not exemplified by any ordinary object is zero.\<close>}

@{thm[display] "zero:1"}

Note that while the above definition introduces the number zero as (abstract) object, we have not
defined the notion of a @{emph \<open>Natural Number\<close>} yet, nor shown that the number zero indeed @{emph \<open>is\<close>} a
natural number. The definition of @{emph \<open>Natural Number\<close>} will rely on introducing a @{emph \<open>predecessor\<close>}
relation and, intuitively speaking, defining that an abstract object is a natural number, if there is
a series of objects starting at zero, ending at the given abstract object, s.t. two consecutive objects
in that series bear the predecessor relation to each other. While we will describe this construction
in detail in the following sections, we can already define the strictly more general@{footnote \<open>It will
be a theorem that @{term \<open>\<guillemotleft>#O!\<guillemotright>\<close>} is a natural cardinal that is infinite and not a natural number.\<close>} notion of a
@{emph \<open>Natural Cardinal\<close>} and it will immediately follow that zero is a natural cardinal.
An object @{term x} is a natural cardinal, just in case that there is a property @{term G},
s.t. @{term x} is the number of @{term G}s:

@{thm[display] card[of x]}

By the definition of the number zero, it becomes immediately apparent that zero is a natural cardinal:

@{thm[display] "zero-card"[print_as_theorem]}

\<close>

section\<open>Ancestral Relations and Transitive Closures\<close>

text\<open>
As mentioned above, @{emph \<open>Natural Numbers\<close>} will, informally speaking, be defined by the means of
series of objects that bear a (yet to be introduced) predecessor relation to each other.
However, traditionally, a series of objects relies on it being possible to index its objects using a
continuous sequence of natural numbers. Since our goal is to @{emph \<open>define\<close>} natural numbers, using
this traditional notion of a series is not an option.
Instead we construct @{emph \<open>ancestral relations\<close>}. In particular the @{emph \<open>strong ancestral\<close>} of
a relation will match the concept of the transitive closure of the relation.
Natural numbers will be defined as the objects to which the number zero bears the
@{emph \<open>weak ancestral\<close>} of the predecessor relation, i.e. the number zero itself and any
objects that are transitively preceded by zero.

The first step in this process is to define being a @{emph \<open>hereditary\<close>} property with respect to
a relation, which will lead to a definition of the @{emph \<open>strong ancestral\<close>} of a relation.

\<close>

subsection\<open>Properties that are Hereditary with respect to a Relation\<close>

text\<open>
A property @{term F} is @{emph \<open>hereditary\<close>} w.r.t. a relation @{term R}, if and only if for every pair
of objects @{term x} and @{term y}, s.t. @{term x} bears @{term R} to @{term y}, if @{term x} exemplifies
@{term F}, then @{term y} exemplifies @{term F}:

@{thm[display] "hered:1"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "&I", OF "cqt:2[const_var]"[axiom_inst], OF "cqt:2[const_var]"[axiom_inst], of _ F R, print_as_theorem]}


Intuitively, a relation @{term R} defines sequences of objects as follows: we call a list of
objects @{term x\<^sub>1}, ..., @{term x\<^sub>n} an @{term R}-induced sequence, if for every @{text "0 < i < n"}, 
@{term x\<^sub>i} bears @{term R} to @{text \<open>x\<^bsub>i+1\<^esub>\<close>}.
Then @{term F} being hereditary w.r.t @{term R} means that any @{term R}-induced sequence starting
in @{term F} (i.e. starting with an object exemplified by @{term F}), is completely contained in
@{term F} (i.e. every object in the sequence exemplifies @{term F} as well).

Or in other words, a property @{term F} is hereditary w.r.t a relation @{term R}, if "@{term F}-ness"
is inherited from objects to all objects that are @{term R}-related to them.
\<close>

subsection\<open>Strong Ancestral of a Relation and Transitive Closures\<close>

text\<open>
Using the above definition, we can introduce the @{emph \<open>Strong Ancestral\<close>} of a relation @{term R},
which will be written as @{term \<open>\<guillemotleft>[R]\<^sup>*\<guillemotright>\<close>}:

@{thm[display] "ances-df"}

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
a relation @{term R}, that may be more common in traditional mathematical training, namely:

The transitive closure of a relation @{term R} is the intersection of all transitive relations @{term R'} that
are contained in @{term R}.
As a matter of fact we can state this definition in AOT as well, and prove it to be equivalent to
the strong ancestral of @{term R}.

First we define being transitive for a relation as follows:
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
  \<comment> \<open>The following is a simple consequence of PLM's theorems about strong ancestral relations.\<close>
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
    \<comment> \<open>The following is an instance of another theorem about strong ancestral relations.\<close>
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

section\<open>Weak Ancestral of a Relation and the Non-Existence of a General Relation of Identity\<close>

text\<open>
As mentioned above the goal is to define being a Natural Number as either being zero or being an
object, s.t. zero bears the strong ancestral of the to-be-defined predecessor relation to it.
This matches the notion of the @{emph \<open>weak ancestral\<close>} of the predecessor relation. Traditionally
(TODO: cite Frege), the weak ancestral of a relation @{term \<open>\<guillemotleft>[R]\<^sup>+\<guillemotright>\<close>} is defined, s.t. an object @{term x}
bears @{term \<open>\<guillemotleft>[R]\<^sup>+\<guillemotright>\<close>} to an object @{term y}, if only if either @{term x} bears the strong ancestral
@{term \<open>\<guillemotleft>[R]\<^sup>*\<guillemotright>\<close>} to @{term y} or @{term \<open>x = y\<close>}.

However, in AOT there is no general relation of identity, i.e. @{term \<open>\<guillemotleft>[\<lambda>xy x = y]\<guillemotright>\<close>} does not
denote (TODO: refer to earlier discussion about this TBD). Consequently, the immediate candidate
for defining the weak ancestral of a relation @{term \<open>\<guillemotleft>[\<lambda>xy [R]\<^sup>*xy \<or> x = y]\<guillemotright>\<close>} provable does not denote
for any @{term R} with a strong ancestral that is not reflexive:@{footnote \<open>For trivial relations
@{term R}, e.g. for a relation @{term R} that is universally exemplified, the @{text \<open>\<lambda>\<close>}-expression
in question does trivially denote. Having a non-reflexive strong ancestral on the other hand is
not a necessary condition for the term to fail to denote, but sufficient for our discussion, since
the strong ancestral of the predecessor relation is not reflexive.\<close>}
\<close>

AOT_theorem \<open>\<forall>x \<not>[R\<^sup>*]xx \<rightarrow> \<not>[\<lambda>xy [R]\<^sup>*xy \<or> x = y]\<down>\<close>
proof(rule "\<rightarrow>I"; rule "raa-cor:2")
  AOT_assume non_reflexive: \<open>\<forall>x \<not>[R\<^sup>*]xx\<close>
  AOT_assume 0: \<open>[\<lambda>xy [R]\<^sup>*xy \<or> x = y]\<down>\<close>
  then AOT_obtain S where S_def: \<open>S = [\<lambda>xy [R]\<^sup>*xy \<or> x = y]\<close>
    using "free-thms:1"[THEN "\<equiv>E"(1)] "\<exists>E"[rotated] by blast
  \<comment> \<open>We use the established fact that there are distinct, but exemplification-indistinguishable abstract objects.\<close>
  AOT_obtain x y where 1: \<open>A!x & A!y & x \<noteq> y & \<forall>F ([F]x \<equiv> [F]y)\<close>
    using "aclassical2" "\<exists>E"[rotated] by blast
  AOT_have \<open>[S]xx\<close>
    by (rule "rule=E"[rotated, OF id_sym, OF S_def];
        safe intro!: "\<beta>\<leftarrow>C" 0 prod_denotesI "cqt:2[const_var]"[axiom_inst] "&I" "\<or>I"(2) "=I")
  moreover AOT_have \<open>\<not>[R]\<^sup>*xx\<close>
    using "\<forall>E"(2) non_reflexive by blast
  ultimately AOT_have \<open>[\<lambda>y [S]xy & \<not>[R]\<^sup>*xy]x\<close>
    by (safe intro!: "\<beta>\<leftarrow>C" "cqt:2" "&I")
  AOT_hence \<open>[\<lambda>y [S]xy & \<not>[R]\<^sup>*xy]y\<close>
    by (safe intro!: 1[THEN "&E"(2), THEN "\<forall>E"(1), THEN "\<equiv>E"(1)] "cqt:2")
  AOT_hence \<open>[S]xy & \<not>[R]\<^sup>*xy\<close> using "\<beta>\<rightarrow>C" by blast
  AOT_hence \<open>[\<lambda>xy [R]\<^sup>*xy \<or> x = y]xy\<close> and \<open>\<not>[R]\<^sup>*xy\<close>
    using "rule=E"[rotated, OF S_def] "&E" by fast+
  AOT_hence \<open>x = y\<close> using "\<beta>\<rightarrow>C" "\<or>E" by fast
  AOT_hence \<open>x = y & \<not>x = y\<close>
    using "&I" 1[THEN "&E"(1), THEN "&E"(2)] by (metis "=-infix" "\<equiv>\<^sub>d\<^sub>fE")
  AOT_thus \<open>p & \<not>p\<close> for p by (metis "raa-cor:1")
qed

text\<open>
For this reason Nodelman and Zalta proceed by introducing @{emph \<open>rigid one-to-one relations\<close>}.
Rigid one-to-one relations induce a notion of identity on their @{emph \<open>domain\<close>} that is consistent
with general identity (on this domain), but constitutes a denoting relation. (TODO: cite)
\<close>
subsection\<open>Rigid One-to-One Relations\<close>

text\<open>
For a relation to be @{emph \<open>one-to-one\<close>} is related to the notion of a function being injective.
A relation @{term R} is @{emph \<open>one-to-one\<close>}, if whenever two objects @{term x} and @{term y} bear
@{term R} to the same object @{term z}, then @{term x} and @{term y} are identical:

@{thm[display] "df-1-1:1"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "cqt:2[const_var]"[axiom_inst], of _ R, print_as_theorem]}

Note, however, that one-to-one relations are more general than injective functions, since the criterion
to be one-to-one does not imply that the relation is @{emph \<open>functional\<close>}, i.e. that each object
in its domain is related to exactly one object.

An object @{term x} is in the domain of a relation @{term R}, just in case that there is an
object @{term y}, s.t. @{term x} bears @{term R} to @{term y}:

@{thm[display] "df-1-1:5"[of x R, THEN "\<equiv>Df", print_as_theorem]}

While the predecessor relation will in fact be a functional relation, a relation that
relates a single object to all other objects, but no other object to any object, is an example of a
one-to-one relation that's succinctly non-functional.

However, in order to introduce a restricted notion of identity, functionality is not a requirement.
But the restricted identity we are about to define only makes sense for one-to-one relation. For that reason, we
introduce restricted variables for them and only define the restricted identity relative
to this restriction. Reasoning with non-rigid restricted variables, however, is cumbersome (TODO: cite discussion in PLM or 
sections above), so we define @{emph \<open>rigid one-to-one relations\<close>} as relations that are both one-to-one and rigid (we
restate the definition of rigid as well): (TODO: refer to earlier mentions of rigidity)

@{thm[display] "df-rigid-rel:1"[THEN "\<equiv>Df", THEN "\<equiv>S"(1), OF "cqt:2[const_var]"[axiom_inst], of _ R, print_as_theorem]}
@{thm[display] "df-1-1:2"[THEN "\<equiv>Df", of _ R, print_as_theorem]}

In the following we will use @{term \<R>} as a restricted variable ranging over rigid one-to-one relations.@{footnote \<open>Note
that AOT uses $\underline{R}$, however, in our framework choosing a fresh character is the simpler choice.\<close>}
\<close>

subsection\<open>Identity Restricted to the Domain of Rigid One-to-one Relations\<close>

(*<*)
AOT_theorem r_id_restr: \<open>x =\<^sub>\<R> y \<equiv> (InDomainOf(x,\<R>) & InDomainOf(y,\<R>) & x = y)\<close>
  by (auto intro!: "\<equiv>I" "\<rightarrow>I" "&I" dest: "id-R-thm:2"[THEN "\<rightarrow>E"] "&E" "id-R-thm:3"[THEN "\<rightarrow>E"]
                   "id-R-thm:4"[THEN "\<rightarrow>E", OF "\<or>I"(1), THEN "\<equiv>E"(2)])
(*>*)

text\<open>
For a variable @{term \<R>} that is restricted to rigid one-to-one relations, a restricted notion
of identity can now be defined as follows:

@{thm[display] "id-d-R"}

Note that in contrast to general identity, @{term \<R>}-identity is a proper relation.

By @{text \<beta>}-conversion and using infix notation, two objects @{term x} and @{term y} are
@{term \<R>}-identical, if there is an object they are both @{term \<R>}-related to:

@{thm[display] "id-R-thm:1"[of _ \<R> x y, print_as_theorem]}

Since @{term \<R>} is restricted to rigid one-to-one relations, the resulting identity relation is exactly the
restriction of general identity to the domain of @{term \<R>}:

@{thm[display] r_id_restr[of _ \<R> x y, print_as_theorem]}

Consequently, the defined identity is a partial equivalence relation that is
reflexive on the domain of the relation:

@{thm "id-R-thm:5"[of _ x \<R>, print_as_theorem]
      "id-R-thm:6"[of _ \<R> x y, print_as_theorem]
      "id-R-thm:7"[of _ \<R> x y z, print_as_theorem]}
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
Based on the concept of @{term \<R>}-identity, Nodelman and Zalta continue to define the @{emph \<open>weak ancestral\<close>} of a
relation @{term \<open>\<R>\<^sup>+\<close>} for rigid one-to-one relations as follows:

@{thm[display] "w-ances-df"}

Restricting to the domain of @{term \<R>}, two object are now exactly in the weak ancestral relation
@{term \<open>\<guillemotleft>[\<R>]\<^sup>+\<guillemotright>\<close>}, if they are either transitively @{term \<R>}-related (i.e. in the strong ancestral
relation @{term \<open>\<guillemotleft>[\<R>]\<^sup>*\<guillemotright>\<close>}) or identical:

@{thm[display] ances_in_domain[of _ x \<R> y, print_as_theorem]}
\<close>

section\<open>Generalized Induction\<close>

text\<open>
In order to understand the formulation of generalized induction, first consider the
following theorem that Nodelman and Zalta prove before even introducing weak ancestral relations,
but which already has "inductive character":

@{thm[display] "anc-her:3"[of _ F x R y, print_as_theorem]}

While this may not look like an inductive principle as stated, unfolding the definition of
@{text \<open>Hereditary\<close>} this is equivalent (under some trivial transformations) to the following:
\<close>

AOT_theorem \<open>[F]z & \<forall>x\<forall>y([R]xy \<rightarrow> ([F]x \<rightarrow> [F]y)) \<rightarrow> \<forall>y ([R]\<^sup>*zy \<rightarrow> [F]y)\<close>
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

Pretend for a moment that @{term R} could be a well-defined predecessor relation and @{term z} the number zero.
Then this theorem would imply that if (1) @{term F} holds for zero and
(2) for any @{term x} and @{term y}, s.t. @{term x} precedes @{term y}, if @{term x} exemplifies
@{term F}, then @{term y} exemplifies @{term F}, then @{term F} holds for all numbers transitively
preceded by zero (and since @{term F} also holds for zero by assumption this would trivially imply that
@{term F} holds for any natural number).

In principle, this is how mathematical induction will be derived.
However, it is inconvenient that the induction step in this formulation ranges over the full domain
of all objects. When arguing about an induction step, it is counter-intuitive to consider if and
in what way natural numbers may or may not be related to arbitrary objects.
By instantiating @{term F} to @{term \<open>\<guillemotleft>[\<lambda>x [F]x & [\<R>]\<^sup>+zx]\<guillemotright>\<close>}, the above can be
generalized to the following principle, which PLM states as @{emph \<open>Generalized Induction\<close>}
(TODO cite):@{footnote \<open>Note that (1) @{term \<open>\<guillemotleft>[\<R>]\<^sup>+zy\<guillemotright>\<close>} for any @{term y}
implies @{term \<open>\<guillemotleft>[\<R>]\<^sup>+zz\<guillemotright>\<close>}, yielding @{term \<open>\<guillemotleft>[\<lambda>x [F]x & [\<R>]\<^sup>+zx]z\<guillemotright>\<close>} in all cases in which the consequent
of the strengthened theorem does not trivially hold (i.e. if @{term \<open>\<guillemotleft>\<not>\<exists>y [\<R>]\<^sup>+zy\<guillemotright>\<close>}) and (2) that the consequent of
the weaker theorem can be strengthened since @{term \<open>\<guillemotleft>[\<R>]\<^sup>+zy\<guillemotright>\<close>} either
 implies (a) @{term \<open>z = y\<close>}, in which case @{term \<open>\<guillemotleft>[F]y\<guillemotright>\<close>} follows from the assumption @{term \<open>\<guillemotleft>[F]z\<guillemotright>\<close>},
or it implies (b) @{term \<open>\<guillemotleft>[\<R>]\<^sup>*zy\<guillemotright>\<close>}, in which case the consequent of the weaker principle yields @{term \<open>\<guillemotleft>[F]y\<guillemotright>\<close>}.
The additional fact that @{term \<open>\<guillemotleft>[\<R>]xy\<guillemotright>\<close>} and @{term \<open>\<guillemotleft>[\<R>]\<^sup>+zx\<guillemotright>\<close>} imply @{term \<open>\<guillemotleft>[\<R>]\<^sup>+zy\<guillemotright>\<close>} is sufficient to
arrive at the strengthened theorem.\<close>}

@{thm[display] "pre-ind"[of _ F z \<R>, print_as_theorem]}

We will show below that instantiating this generalized principle of induction to the predecessor relation
we are about to define, yields classical mathematical induction (relative to a defined notion of natural numbers).

Note, however, that while the predecessor relation will define a total order on its domain, the
generalized principle of induction can be applied more broadly: if we call an object that is
either @{term z} or transitively @{term \<R>}-related to @{term z} as part of the @{term \<R>}-series
starting at @{term z}, then the theorem shows that all objects on the @{term \<R>}-series
starting at @{term z} exemplify @{term F} just in case, @{term z} exemplifies @{term F} and
@{term F} is inherited from any object on an @{term \<R>}-series starting at @{term z} to any other such object
to which it is @{term \<R>}-related. TODO: try to make the generality clearer; applicability beyond total orders.
\<close>

section\<open>The Predecessor Relation\<close>

subsection\<open>Definition\<close>

text\<open>
While the definition of the predecessor relation is rather straightforward, the interesting question
will be whether it actually denotes a relation, which we will discuss in detail below. For the moment
assume that the @{text \<open>\<lambda>\<close>}-expression in the definiens of the following definition denotes:

@{thm[display] "pred-thm:1"}

So an object @{term x} precedes an object @{term y} just in case there is a property @{term F}
and an ordinary object @{term u}, s.t. @{term u} exemplifies @{term F}, @{term y} numbers @{term F}
and @{term x} numbers being an @{term F} other than @{term u} (written as @{term \<open>\<guillemotleft>[F]\<^sup>-\<^sup>u\<guillemotright>\<close>} which is
just defined as @{term \<open>\<guillemotleft>[\<lambda>z [F]z & z \<noteq>\<^sub>E u]\<guillemotright>\<close>}}.

This is a variant of Frege's definition of the successor relation (TODO cite)@{footnote \<open>Nodelman and
Zalta argue in favour of a predecessor relation due to the fact that in contrast to a successor relation,
the argument order of the predecessor relation matches the numerical order of objects in the relation.
Otherwise the notions are interchangeable, i.e. @{text \<open>Succeeds(y,x)\<close>} is exactly @{term \<open>\<guillemotleft>[\<P>]xy\<guillemotright>\<close>}.\<close>}.
The idea can be clarified by considering how the first natural numbers are related w.r.t this relation:
\<^item> The number Zero numbers properties that are not (actually) exemplified by any ordinary object. Hence there
  cannot be a property @{term F} that is exemplified by an object @{term u}, s.t. Zero numbers @{term F},
  which means that Zero is not preceded by any object.
\<^item> The number One numbers properties that are (actually) exemplified by a single ordinary object.@{footnote \<open>While
  we have not formally introduced any number other than Zero, we consider this intuitive understanding helpful
  in clarifying the idea of the predecessor relation. The number One will formally be introduced later in this chapter.\<close>}
  Hence any property @{term F} numbered by One is exemplified
  by some ordinary object @{term \<open>u\<close>} and @{term \<open>\<guillemotleft>[F]\<^sup>-\<^sup>u\<guillemotright>\<close>}, i.e. being an object exemplifying @{term F} other than @{term u},
  is not exemplified by any ordinary object. Hence Zero is the unique predecessor of One.
\<^item> The number Two numbers properties that are (actually) exemplified by two distinct ordinary objects.
  Being an object that exemplifies any of these properties other than any particular object the given
  property exemplifies, is a property exemplified by only one ordinary object, hence numbered by One, i.e.
  One preceeds Two, etc.
\<close>

subsection\<open>Assuring that the Predecessor Relation Denotes\<close>

text\<open>
It is important to realize that the @{text \<open>\<lambda>\<close>}-expression used in above definition does not
trivially denote a relation in AOT.
@{emph \<open>Numbering a property\<close>} is an encoding claim: an object numbers a property @{term G}, just in case
it encodes all properties, s.t. actually exemplifying it is equinumerous to @{term G}.
In general, encoding claims cannot be abstracted to denoting properties and relations (TODO: cite earlier discussion
on this).
In fact it is easy to see that the minimal model of AOT does not validate this axiom: the minimal
model contains one ordinary urelement (resp. one ordinary object) and one special urelement.
Since special urelements determine the exemplification extensions of abstract objects, there being
only one special urelement implies that all abstract objects exemplify the same properties and relations.
This implies in particular that either all objects are preceded by zero or no object is, in particular:
@{term \<open>\<guillemotleft>[\<P>]0 0\<guillemotright>\<close>} or @{term \<open>\<guillemotleft>\<not>\<exists>x [\<P>]0 x\<guillemotright>\<close>}. However, we have already (informally) argued above that zero is
not preceded by any object.@{footnote \<open>Both @{thm "no-pred-0:1"[print_as_theorem]} and @{thm "prec-facts:1"[print_as_theorem]} are formally 
derived TODO: cite.\<close>} Hence in this model it would have to hold that @{term \<open>\<guillemotleft>\<not>\<exists>x [\<P>]0 x\<guillemotright>\<close>}.
However, since the minimal model still contains one ordinary object, the number One can be constructed
and (again as argued above) is preceded by Zero, i.e. @{term \<open>\<guillemotleft>[\<P>]0 1\<guillemotright>\<close>}, which yields a contradiction.

Nodelman and Zalta assert that the predecessor relation denotes by axiom and emphasize that the relation
is not inherently mathematical and no mathematical primitives are needed to assert as an axiom axiom that
it denotes. (TODO cite PLM: pred). On the one hand they argue that expressions of the form
@{term \<open>\<guillemotleft>Numbers(y,F)\<guillemotright>\<close>}, while seemingly mathematical in nature, can be eliminated, since they are @{emph \<open>defined\<close>}
in terms of primitives of AOT. On the other hand they argue that the relation merely asserts the
existence of an ordering relation on abstract objects and ordering relations can in general be expressed in
entirely logical terms.

However, even if one concedes that the axiom is not inherently mathematical, it can be objected
that it is rather @{emph \<open>ad-hoc\<close>}: rather than asserting a general principle according to which
encoding claims can be abstracted to relations, it singles out a specific relation and this
relation is after all used to @{emph \<open>define\<close>} a concept that is very much mathematical in nature.
Furthermore, it is not trivial that the axiom is consistent: as we have already shown the minimal
model of AOT will not validate it.

Using our embedding we can, however, contribute to this situation in two ways:
\<^item> We can show that the axiom is consistent by constructing models that validate it.
\<^item> We can generalize the axiom to a comprehension principle for relations among abstract objects, s.t.
  it becomes a theorem that the predecessor relation in particular denotes. We are confident that
  we can thereby alleviate any remaining doubt on the non-mathematical character of the axiom.
\<close>

chapter\<open>Higher-Order Type-Theoretic Object Theory\<close>text\<open>\label{HigherOrderAOT}\<close>

text\<open>

\<close>

chapter\<open>Conclusion\<close>

text\<open>

\<close>

(*<*)
end
(*>*)