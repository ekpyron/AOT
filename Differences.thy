(*<*)
theory Differences
imports TAO_9_PLM
begin
(*>*)

(*<*)
(* Pretty printing settings for antiquotations. *)
notation (latex output)
  validity_in ("[\<^raw:\embeddedstyle{>_\<^raw:}> in _]")
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
(*>*)

section{* Terms and Variables *}

(*<*)
context PLM
begin
(*>*)

text{*
  The Principia explicitly distinguishes between terms and variables for all primitive types.
  Furthermore, it postulates  (\ref{PM-cqt}.2)\cite[p. 191]{PM}, that for every term @{text "\<tau>"}, 
  which is not a definite description, there exists (a variable) @{text "\<beta>"} that is equal to @{text "\<tau>"}:
  @{text "\<exists>\<beta> (\<beta> = \<tau>)"}. Thereby, any denoting term can be substituted for any variable
  (the substitution of identicals is an axiom). The only terms that may not denote
  are definite descriptions. 

  Mapping this distinction between terms and variable and the Principia's  notion of non-denoting
  terms to the (non-partial) functional logic of Isabelle/HOL, where generally every free variable symbol
  can be substituted by any term of the same type, is not trivial. (In fact, there is ongoing work
  to investigate whether the embedding of free logic in HOL as studied in the papers by Christoph and 
  Dana Scott could be fruitfully combined with the work presented here; the solution presented 
  here has been worked out independently).

  The solution in the current embedding is as follows: First, it does not explicitly distinguish between
  relation variables and relation terms and drops the corresponding axiom (\ref{PM-cqt}.2)\cite[p. 191]{PM},
  which implicitly holds in our context (note that this is the case, although the equality is not primitive,
  but defined: the statement @{term "\<^bold>\<exists> \<beta> . \<beta> \<^bold>= \<tau>"} for one-place relations for instance expands to
  @{term "\<^bold>\<exists> \<beta> . \<^bold>\<box>(\<^bold>\<forall> x. \<lbrace>x\<^sup>P,\<beta>\<rbrace> \<^bold>\<equiv> \<lbrace>x\<^sup>P,\<tau>\<rbrace>)"}. This still has to be proven, but without the distinction
  between variables and terms it suffices to show that @{term "\<^bold>\<box>(\<^bold>\<forall> x. \<lbrace>x\<^sup>P,\<tau>\<rbrace> \<^bold>\<equiv> \<lbrace>x\<^sup>P,\<tau>\<rbrace>)"} which
  follows from the remaining axioms). Consequently, the additional precondition  @{text "\<exists>\<beta> (\<beta> = \<tau>)"}
  in axiom (\ref{PM-cqt}.1)\cite[p. 190]{PM} is dropped as well.
  To address the issue of possibly non-denoting definite descriptions, the embedding distinguishes between the 
  types @{type \<nu>} and @{type \<kappa>}.  Roughly speaking, the type @{text \<nu>} corresponds to PLMs individual 
  variables, whereas the type @{text \<kappa>} corresponds to the Principia's individual terms.
  Constructs of type @{type \<nu>} always denote (individuals), whereas objects of type @{type \<kappa>} may 
  contain definite descriptions that may not denote. The condition under which an object of type
  @{type \<kappa>} denotes is internally stored/remembered by an annotation (Boolean flag).
  More precisely, the type @{type \<kappa>} is internally represented as a tuple of a
  Boolean and an object of type @{type \<nu>}). The decoration @{text "_\<^sup>P"} is used to represent
  only objects of @{type \<kappa>} that denote (internally @{text "x\<^sup>P"} maps @{text "x"} which is of
  type @{type \<nu>} to an object of type @{type \<kappa>} representing the tuple @{text "(True, x)"}).
  Consequently, any theorem of the Principia that uses individual variables can be represented
  in the embedding using a variable of type @{type \<nu>} decorated by @{text "_\<^sup>P"} (see also
  the section about axiom and theorem schemata below).
  
  In order to be able to substitute denoting definite descriptions for an expression
  like @{text "x\<^sup>P"}, the axiom @{text "cqt_5_mod"} assures the following:

  @{thm cqt_5_mod}
  
  @{thm (prem 1) cqt_5_mod} is an inductive predicate that is @{text "True"} if and only if
  @{text "\<psi>"} is a simple exemplification or encoding formula. In the functional setting
  this means that @{text "\<psi>"} is a function from @{type "\<kappa>"} to @{type "\<o>"} (the type of
  propositions) that is either the exemplification of an n-place relation by its argument
  (among other arbitrary objects for @{text "n > 1"}) or an encoding expression in its argument.
  @{text "cqt_5_mod"} therefore assures that an object of type @{type \<kappa>} can be substituted for
  an expression of the form @{text "x\<^sup>P"}, if it is contained in a true exemplification or encoding
  expression. The axiom itself is a logical consequence of the original axioms (\ref{PM-cqt}.2) and
  (\ref{PM-cqt}.5)\cite[p. 191]{PM}.

  One might think that dropping the additional precondition in axiom (\ref{PM-cqt}.1)\cite[p. 190]{PM}
  constitutes a problem for the embedding, as now any formula that is true for all individuals
  can directly be instantiated for a definite description. This is not the case, though.
  The embedding does not define quantification for the type @{type \<kappa>}, but only for the type
  @{type \<nu>}. Therefore, a function @{text "\<phi>"} in the expression @{text "\<^bold>\<forall> x . \<phi> x"}
  cannot be a function from @{type "\<kappa>"} to @{type "\<o>"}, but only from @{type "\<nu>"} to
  @{type "\<o>"}. The statement \emph{forall @{text "x"} it holds that @{text "x"} exemplifies
  @{text "F"}} is represented by @{text "\<^bold>\<forall> x . \<lparr>F,x\<^sup>P\<rparr>"} in the embedding and can only
  be instantiated for definite descriptions that can be substituted for an expression
  of the form @{text "x\<^sup>P"}, i.e. for definite descriptions that denote.

  Consequently, the modified axioms of quantification in the embedding are equivalent to,
  resp. correspond to, the original axioms (\ref{PM-cqt})\cite[p. 191]{PM}.

  The embedding could easily be modified to include a similar distinction for relation terms as
  well. The equivalent of the @{text "_\<^sup>P"} decoration for relations would then internally
  be the identity, as relation terms always denote. As this would introduce more complexity
  to the embedding and would not change its logical consequences, we decided not to include
  such a distinction in the embedding.

  However, the combination with a proper embedding of free logic (see above) 
  seems an interesting opportunity for future work. First investigations suggest
  that such a combination may make it possible to drop the current distinction
  between the types @{type "\<kappa>"} and @{type "\<nu>"} and the adjustment of the axioms.
*}

section{* Propositional Formulas and Lambda Expressions *}

text{*
  The Principia explicitly distinguishes between propositional formulas and formulas that may contain
  encoding subformulas. As outlined in \cite{rtt} there is no trivial solution for reproducing
  this distinction in the context of a functional logic.
  The embedding only uses one primitive type @{type "\<o>"} for propositions, and an expression
  of type @{type "\<o>"} \emph{may} contain encoding subformulas.
  The issue that arises here is that naively allowing lambda-expressions to contain encoding
  subformulas in combination with axiom (\ref{PM-A-objects}) leads to inconsistencies.
  The solution to this problem lies in the observation that any propositional formula as defined
  in the Principia (i.e. any formula \emph{not} containing encoding subformulas), can be represented
  by a function acting on \emph{urelements} in the Aczel-model of the theory, rather than a function
  acting on \emph{individuals}. Only encoding subformulas depend on the actual individuals, whereas
  all other expressions (i.e. exemplification subformulas) only depend on the urelements corresponding
  to the individuals.

  This way the lambda expressions of the embedded logic can be represented
  by lambda expressions in the meta-logic as: @{thm lambdabinder1.abs_eq[where x=\<phi>, rename_abs x]}

  Here, @{text "x"} is an individual object of type @{type "\<nu>"} and @{text "\<upsilon>\<nu>"}
  maps an urelement to some (undefined) individual in its preimage. This way
  @{text "\<phi>"} is a function acting on individuals (of type @{type "\<nu>"})
  and can thereby represent the matrix of any lambda-expressions of Principia.
  In the meta-logic this function is converted to a function acting on urlements, though, so
  the expression @{text "\<^bold>\<lambda>x. \<phi> x"} only implies \emph{being @{text "x"}, such that
  there exists some @{text "y"} that is mapped to the same urelement as @{text "x"}, and it holds
  that @{text "\<phi> y"}}. Conversely, only \emph{for all @{text "y"} that are mapped to the same
  urelement as @{text "x"} it holds that @{text "\<phi> y"}} is a sufficient condition to conclude
  that @{text "x"} exemplifies @{text "\<^bold>\<lambda>x. \<phi> x"}.

  As propositional formulas only depend on urelements, however, the resulting lambda-expressions
  can accurately represent the lambda-expressions of the Principia. Moreover, using the construction described
  above, lambda-expressions that do contain encoding subformulas do not lead to inconsistencies.

  It is interesting to note that the embedding suggests, that the restrictions on lambda-expressions
  in the Principia could in general be extended in a consistent way: instead of restricting lambda-expressions
  to propositional formulas entirely, it would be sufficient to disallow the occurrence of the
  \emph{bound variables} of the lambda-expression in an encoding subformula to avoid inconsistencies.

  The expression @{text "\<^bold>\<lambda>x. \<lparr>F,x\<^sup>P\<rparr> \<^bold>& \<lbrace>y\<^sup>P, G\<rbrace>"} can be formulated in the embedding and
  @{text "\<lparr>\<^bold>\<lambda>x. \<lparr>F,x\<^sup>P\<rparr> \<^bold>& \<lbrace>y\<^sup>P, G\<rbrace>, z\<^sup>P\<rparr>"} is equivalent to @{text "\<lparr>F,z\<^sup>P\<rparr> \<^bold>& \<lbrace>y\<^sup>P, G\<rbrace>"} as one
  would expect. Still these kinds of expressions are not part of PLM.
*}

section{* Theorem and Axiom Schemata *}

text{*
  As already mentioned above, in the logic of Isabelle/HOL generally every free variable symbol
  can be substituted by any term of the same type. Stating an axiom or theorem containing a free
  variable symbol (e.g. of type @{type "\<o>"}) therefore implicitly asserts that the statement is true
  for all objects of the same type (e.g. all propositions). Axiom (\ref{PM-pl}.1)\cite[p. 186]{PM})
  for instance can therefore simply be stated as the following:

  @{thm pl_1}

  This automatically asserts that all expressions of type @{type "\<o>"} can be substituted for 
  @{text "\<phi>"} or @{text "\<psi>"}, so the statement itself is in fact already the complete axiom schema.

  Consequently the equivalence of alphabetic variants as well as @{text "\<alpha>"}-Conversion implicitly
  hold in the context of Isabelle/HOL and don't have to be explicitly stated.

  Note that stating an axiom or theorem for a decorated variable @{text "x\<^sup>P"} as described in
  the previous sections, only allows objects of type @{type "\<nu>"} to be substituted for @{text "x"}.
  To substitute a definite description it first has to be assured that
  @{text "\<^bold>\<exists> x . (x\<^sup>P) \<^bold>= \<^bold>\<iota>x . \<phi> x"}, as the type of @{term "\<^bold>\<iota>x . \<phi> x"} is @{type "\<kappa>"} which is
  different from the type @{type "\<nu>"}.
*}

section{* Modally-Strict Proofs *}

text{*
  The deductive system PLM described in the Principia distinguishes between
  theorems that are \emph{modally-strict} and theorems that are not \emph{modally-strict}.
  A theorem is modally-strict if it can be derived from other modally-strict theorems or
  any of the axioms that are not necessitation-averse. Consequently, if a formula is a
  modally-strict theorem, then the same formula prefixed with the box-operator is a theorem
  of PLM (the corresponding meta-rule in PLM is called \emph{RN}). Conversely, if @{text "\<box>\<phi>"}
  is a theorem of PLM, this does \emph{not} imply that @{text "\<phi>"} is a modally-strict theorem
  (see the remark about the converse of RN (\ref{PM-RN-converse-rem})\cite[p. 213]{PM}).

  The embedding on the other hand explicitly models the modal logic of the theory with
  a primitive notion of possible worlds (i.e. Kripke semantics). The regular axioms are stated
  to be true in all possible worlds and therefore their necessitations are implicitly true,
  as the box-operator is semantically defined to mean truth in all possible worlds.
  The necessitation-averse axiom on the other hand is stated to be true only in the designated
  actual world, from which its necessitation is therefore not derivable.

  Consequently, modally-strict theorems can be stated and proven to be true for an \emph{arbitrary}
  possible world, whereas non-modally-strict theorems are stated and proven to be true for the
  actual world.

  In this representation, however, in contrast to PLM, the converse of \emph{RN} becomes true:
  If @{text "\<box>\<phi>"} is proven as a theorem (i.e. proven to be true in the designated actual world),
  then by the semantics of the box operator it follows that @{text "\<phi>"} is true for an arbitrary possible
  world, which is how modally-strict theorems are stated in the embedding.

  However, in Isabelle/HOL all dependencies necessary to prove a theorem are explicitly stated
  in its proof and we explicitly refrain from stating or using the converse of \emph{RN}
  (although automation suffers due to this restriction). All theorems that are derived for
  arbitrary possible worlds from the deductive system in the embedding therefore still correspond
  to modally-strict theorems in PLM.

  Using the meta-logic directly it would be possible to prove that theorems hold for
  an arbitrary possible world, that are not modally-strict theorems in PLM, though.

  This is not a flaw of the embedding per se, though. The notion of modal-strictness
  in PLM is purely proof-theoretical and based on the derivability of a theorem from
  other theorems. As the embedding explicitly gives all dependencies necessary to
  derive each theorem, it thereby exactly provides the information necessary to classify
  a theorem to be modally-strict or not. Semantically on the other hand, there is no
  equivalent to the distinction between modally-strict and non-strict theorems, so
  there is no way to judge whether a theorem is modally-strict solely based on its
  semantic truth evaluation in general.
*}

(*<*)
end
(*>*)

(*<*)
end
(*>*)
