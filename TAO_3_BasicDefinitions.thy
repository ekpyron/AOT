(*<*)
theory TAO_3_BasicDefinitions
imports TAO_1_Embedding
begin
(*>*)

section{* Basic Definitions *}
text{* \label{TAO_BasicDefinitions} *}

subsection{* Derived Connectives *}
text{* \label{TAO_BasicDefinitions_DerivedConnectives} *}

definition conj::"\<o>\<Rightarrow>\<o>\<Rightarrow>\<o>" (infixl "\<^bold>&" 53) where
  "conj \<equiv> \<lambda> x y . \<^bold>\<not>(x \<^bold>\<rightarrow> \<^bold>\<not>y)"
definition disj::"\<o>\<Rightarrow>\<o>\<Rightarrow>\<o>" (infixl "\<^bold>\<or>" 52) where
  "disj \<equiv> \<lambda> x y . \<^bold>\<not>x \<^bold>\<rightarrow> y"
definition equiv::"\<o>\<Rightarrow>\<o>\<Rightarrow>\<o>" (infixl "\<^bold>\<equiv>" 51) where
  "equiv \<equiv> \<lambda> x y . (x \<^bold>\<rightarrow> y) \<^bold>& (y \<^bold>\<rightarrow> x)"
definition diamond::"\<o>\<Rightarrow>\<o>" ("\<^bold>\<diamond>_" [62] 63) where
  "diamond \<equiv> \<lambda> \<phi> . \<^bold>\<not>\<^bold>\<box>\<^bold>\<not>\<phi>"

named_theorems conn_defs
declare diamond_def[conn_defs] conj_def[conn_defs]
        disj_def[conn_defs] equiv_def[conn_defs]

subsection{* Abstract and Ordinary Objects *}
text{* \label{TAO_BasicDefinitions_AbstractOrdinary} *}

definition Ordinary :: "\<Pi>\<^sub>1" ("O!") where "Ordinary \<equiv> \<^bold>\<lambda>x. \<^bold>\<diamond>\<lparr>E!\<^sup>P,x\<^sup>P\<rparr>"
definition Abstract :: "\<Pi>\<^sub>1" ("A!") where "Abstract \<equiv> \<^bold>\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!\<^sup>P,x\<^sup>P\<rparr>"

(*<*)
end
(*>*)
