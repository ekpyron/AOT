(*<*)
theory AOT_commands
  imports AOT_model "HOL-Eisbach.Eisbach_Tools"
  keywords "AOT_define" :: thy_decl
       and "AOT_theorem" :: thy_goal
       and "AOT_lemma" :: thy_goal
       and "AOT_act_theorem" :: thy_goal
       and "AOT_act_lemma" :: thy_goal

       and "AOT_axiom" :: thy_goal
       and "AOT_act_axiom" :: thy_goal

       and "AOT_assume" :: prf_asm % "proof"
       and "AOT_have" :: prf_goal % "proof"
       and "AOT_hence" :: prf_goal % "proof"
       and "AOT_modally_strict {" :: prf_open % "proof"
       and "AOT_actually {" :: prf_open % "proof"
       and "AOT_obtain" :: prf_asm_goal % "proof"
       and "AOT_show" :: prf_asm_goal % "proof"
       and "AOT_thus" :: prf_asm_goal % "proof"

       and "AOT_find_theorems" :: diag
       and "thm_name" :: diag
       and "AOT_sledgehammer" :: diag
       and "AOT_sledgehammer_only" :: diag
       and "AOT_syntax_print_translations" :: thy_decl
       and "AOT_no_syntax_print_translations" :: thy_decl
begin
(*>*)

section\<open>Outer Syntax Commands\<close>

nonterminal AOT_prop
nonterminal \<phi>
nonterminal \<phi>'
nonterminal \<tau>
nonterminal \<tau>'
nonterminal "AOT_axiom"
nonterminal "AOT_act_axiom"
ML_file AOT_commands.ML
setup\<open>AOT_Theorems.setup\<close>
setup\<open>AOT_Definitions.setup\<close>
setup\<open>AOT_no_atp.setup\<close>

(*<*)
end
(*>*)