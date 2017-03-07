(*<*)
theory Results
imports TAO_10_PossibleWorlds "~~/src/HOL/Library/LaTeXsugar" "~~/src/HOL/Library/OptionalSugar"
begin
(*>*)

(*<*)
notation (latex output)
  validity_in ("[\<^raw:\embeddedstyle{>_\<^raw:}> in _]")
(*>*)

section{* Corrections for PM *}
text{*
  Although the draft of Principia Metaphysica has a remarkably high quality
  we were able to identify some minor issues and typographical errors during the
  formalization.

  For example the following issue was noticed in the proof of the back implication of
  theorem (\ref{PM-ord=E2}). In the current draft of Principia Metaphysica the proof states:


  \emph{It suffices to prove the contrapositive.
  So assume @{text "[\<lambda>y y =\<^sub>E x] = [\<lambda>y y =\<^sub>E z]"}. Then by reasoning just given (inside the
  reductio), @{text "x =\<^sub>E z"}.} \cite[p.~477]{PM}.


  The back implication is @{text "([\<lambda>y y =\<^sub>E x] \<noteq> [\<lambda>y y =\<^sub>E z]) \<^bold>\<rightarrow> x \<noteq> z"}, though, and therefore
  the contrapositive @{text "x = z \<^bold>\<rightarrow> [\<lambda>y y =\<^sub>E x] = [\<lambda>y y =\<^sub>E z]"}. This can easily be proven
  by the substitution of identicals as demonstrated in our formalization. Nevertheless the proof
  in PM seems to have accidentally reversed the proof objective.

  Another issue in the current draft was found in the proof of theorem (\ref{PM-box-phi-a}.2).
  The proof states: \emph{So by theorem (\ref{PM-nec-exist-!}), it follows that:} \cite[p.~483]{PM}.
  The correct theorem to reference is (\ref{PM-!box-desc}), though. This kind of mistake can easily
  happen and can easily be missed in a review process. In the formalization in Isabelle on the other
  hand it immediately becomes apparent that the proof objective can not be solved by the stated
  theorem and the correct theorem can automatically be found.
*}

section{* Proof of a Meta-Conjecture *}

(*<*)
context PossibleWorlds
begin
(*>*)

text{*
  The Theory of Abstract Objects has a syntactic definition of possible worlds. Besides that
  it also has a semantic notion of possible worlds (i.e. a point in the Kripke semantics).

  During a discussion between Zalta and Woltzenlogel-Paleo the following meta-conjecture about possible
  worlds and their semantics in the Theory of Abstract Objects arose:

  \emph{For every syntactic possible world "w", there exists a semantic point "p" which is
        the denotation of "w".}

  Using the formalization of the theory it was not only possible to immediately confirm the
  conjecture, but even to extend it to the more general statement that there exists a natural
  bijection between syntactic and semantic possible worlds (in fact the equivalence had already
  independently become apparent in an earlier formalization of a proof of the fundamental theorem
  of possible worlds in the meta-logic of the embedding).

  Namely it is possible to show, that:

  \begin{itemize}
  \item For every syntactic possible world @{text "x"}, there exists a semantic possible world
  @{text "v"}, such that every proposition is semantically true in @{text "v"},
  if and only if it is syntactically true in @{text "x"}:

  @{thm SemanticPossibleWorldForSyntacticPossibleWorlds}

  \item For every semantic possible world @{text "v"}
  there exists a syntactic possible world @{text "x"}, such that every proposition
  is semantically true in @{text "v"} if and only if it is syntactically true in @{text "x"}:
  
  @{thm SyntacticPossibleWorldForSemanticPossibleWorlds}

  \end{itemize}

*}

(*<*)
end
(*>*)

(*<*)
end
(*>*)
