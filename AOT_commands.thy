theory AOT_commands
  imports AOT_model
  keywords "AOT_define" :: thy_decl
       and "AOT_theorem" :: thy_goal
       and "AOT_act_theorem" :: thy_goal

       and "AOT_assume" :: prf_asm % "proof"
       and "AOT_have" :: prf_goal % "proof"
       and "AOT_hence" :: prf_goal % "proof"
       and "AOT_modally_strict {" :: prf_open % "proof"
       and "AOT_obtain" :: prf_asm_goal % "proof"
       and "AOT_show" :: prf_asm_goal % "proof"
       and "AOT_thus" :: prf_asm_goal % "proof"

       and "thm_name" :: diag
       and "AOT_sledgehammer" :: diag
       and "AOT_sledgehammer_only" :: diag
begin

nonterminal AOT_prop
ML_file AOT_commands.ML
setup\<open>AOT_Theorems.setup\<close>
setup\<open>AOT_no_atp.setup\<close>

end
