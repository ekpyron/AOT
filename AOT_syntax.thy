theory AOT_syntax
  imports AOT_commands
  keywords "AOT_register_variable_name" :: thy_decl
       and "AOT_register_metavariable_name" :: thy_decl
       and "AOT_register_test" :: thy_decl
begin

ML\<open>
structure AOT_TermPrefix = Theory_Data (
  type T = (bool*(string*string)) Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.merge (K true)
);
structure AOT_IdentifierPrefix = Theory_Data (
  type T = (bool * (typ * sort list * sort) * (typ * sort list * sort)) Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.merge (K true)
);
let
  fun mksort lthy sort = Proof_Context.read_class lthy sort |> Lexicon.mark_class
  fun register_prefix meta ((prefix, unarySort), narySort) lthy = lthy |> Local_Theory.background_theory (
    AOT_TermPrefix.map (Symtab.update (prefix, (meta, (mksort lthy unarySort,mksort lthy narySort)))))

  fun read_arity (arity as (typ, _, sort)) lthy =
    if typ = "_" then (dummyT,[],Syntax.parse_sort lthy sort) else Proof_Context.read_arity lthy arity |> (fn (x,y,z) => (Syntax.parse_typ lthy x,y,z))

  fun register_test meta ((prefix, unaryArity), naryArity) lthy = let
    val _ = @{print} ("Prefix:", prefix)
    val unaryArity = read_arity unaryArity lthy
    val naryArity = (case naryArity of SOME arity => read_arity arity lthy | _ => unaryArity)
    val _ = @{print} (unaryArity, naryArity)
  in lthy |> Local_Theory.background_theory (
    AOT_IdentifierPrefix.map (Symtab.update (prefix, (meta, unaryArity, naryArity)))) end
  val scan_sort_constraint = ((Parse.$$$ "(" |-- Parse.arity --| Parse.$$$ ")") ||
    (Parse.sort >> (fn sort => ("_",[],sort))))
in
  Outer_Syntax.local_theory @{command_keyword AOT_register_variable_name} "Register AOT variable prefix."
  ((Parse.cartouche -- Parse.sort -- Parse.sort) >> register_prefix false);
  Outer_Syntax.local_theory @{command_keyword AOT_register_metavariable_name} "Register AOT meta-variable prefix."
  ((Parse.cartouche -- Parse.sort -- Parse.sort) >> register_prefix true);
  Outer_Syntax.local_theory @{command_keyword AOT_register_test} "Register AOT meta-variable prefix."
  ((Parse.short_ident -- scan_sort_constraint -- Scan.option scan_sort_constraint) >> register_test true)
end;
fun fetchTermPrefix ctxt name =
  Local_Theory.raw_theory_result (fn thy =>
    ((Symtab.lookup o AOT_TermPrefix.get) thy (hd (Symbol.explode name)), thy)
) ctxt
\<close>

AOT_register_test \<kappa> AOT_UnaryIndividualTerm AOT_IndividualTerm
AOT_register_test \<kappa> (rel :: (type) type)

AOT_register_variable_name \<open>x\<close> AOT_UnaryIndividualTerm AOT_IndividualTerm
AOT_register_variable_name \<open>y\<close> AOT_UnaryIndividualTerm AOT_IndividualTerm
AOT_register_variable_name \<open>z\<close> AOT_UnaryIndividualTerm AOT_IndividualTerm
AOT_register_variable_name \<open>\<nu>\<close> AOT_UnaryIndividualTerm AOT_IndividualTerm
AOT_register_variable_name \<open>\<mu>\<close> AOT_UnaryIndividualTerm AOT_IndividualTerm

AOT_register_metavariable_name \<open>\<kappa>\<close> AOT_UnaryIndividualTerm AOT_IndividualTerm

AOT_register_variable_name \<open>\<alpha>\<close> AOT_Term AOT_Term
AOT_register_variable_name \<open>\<beta>\<close> AOT_Term AOT_Term
AOT_register_variable_name \<open>\<gamma>\<close> AOT_Term AOT_Term
AOT_register_variable_name \<open>\<delta>\<close> AOT_Term AOT_Term

AOT_register_metavariable_name \<open>\<tau>\<close> AOT_Term AOT_Term
AOT_register_metavariable_name \<open>\<sigma>\<close> AOT_Term AOT_Term

AOT_register_variable_name \<open>F\<close> AOT_Term AOT_Term
AOT_register_variable_name \<open>G\<close> AOT_Term AOT_Term
AOT_register_variable_name \<open>H\<close> AOT_Term AOT_Term
AOT_register_metavariable_name \<open>\<Pi>\<close> AOT_Term AOT_Term

AOT_register_variable_name \<open>p\<close> AOT_Term AOT_Term
AOT_register_variable_name \<open>q\<close> AOT_Term AOT_Term
AOT_register_variable_name \<open>r\<close> AOT_Term AOT_Term
AOT_register_metavariable_name \<open>\<phi>\<close> AOT_Term AOT_Term
AOT_register_metavariable_name \<open>\<psi>\<close> AOT_Term AOT_Term
AOT_register_metavariable_name \<open>\<chi>\<close> AOT_Term AOT_Term
AOT_register_metavariable_name \<open>\<Theta>\<close> AOT_Term AOT_Term
AOT_register_metavariable_name \<open>\<zeta>\<close> AOT_Term AOT_Term
AOT_register_metavariable_name \<open>\<xi>\<close> AOT_Term AOT_Term

nonterminal \<phi>

syntax "_AOT_verbatim" :: \<open>any \<Rightarrow> \<phi>\<close> (\<open>\<guillemotleft>_\<guillemotright>\<close>)
syntax "_AOT_quoted" :: \<open>\<phi> \<Rightarrow> any\<close> (\<open>\<guillemotleft>_\<guillemotright>\<close>)

syntax "" :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>'(_')\<close>)

nonterminal \<tau>
syntax "_AOT_verbatim" :: \<open>any \<Rightarrow> \<tau>\<close> (\<open>\<guillemotleft>_\<guillemotright>\<close>)
syntax "_AOT_quoted" :: \<open>\<tau> \<Rightarrow> any\<close> (\<open>\<guillemotleft>_\<guillemotright>\<close>)

nonterminal \<kappa>\<^sub>s
nonterminal \<Pi>
nonterminal \<alpha>
syntax "" :: \<open>\<kappa>\<^sub>s \<Rightarrow> \<tau>\<close> ("_")
syntax "" :: \<open>\<Pi> \<Rightarrow> \<tau>\<close> ("_")
syntax "" :: \<open>\<phi> \<Rightarrow> \<tau>\<close> ("'(_')")

nonterminal exe_arg
nonterminal lambda_args
syntax "_AOT_term_var" :: \<open>id_position \<Rightarrow> \<tau>\<close> ("_")
syntax "_AOT_term_var" :: \<open>id_position \<Rightarrow> \<phi>\<close> ("_")
syntax "_AOT_exe_vars" :: \<open>id_position \<Rightarrow> exe_arg\<close> ("_")
syntax "_AOT_lambda_vars" :: \<open>id_position \<Rightarrow> lambda_args\<close> ("_")
syntax "_AOT_var" :: \<open>id_position \<Rightarrow> \<alpha>\<close> ("_")
syntax "_AOT_verbatim" :: \<open>any \<Rightarrow> \<alpha>\<close> (\<open>\<guillemotleft>_\<guillemotright>\<close>)

syntax "_AOT_valid" :: \<open>w \<Rightarrow> \<phi> \<Rightarrow> bool\<close> (\<open>[_ \<Turnstile> _]\<close>)

translations
  "[w \<Turnstile> \<phi>]" <= "CONST AOT_model_valid_in w \<phi>"


ML\<open>
fun decode_pos str =
  case (Term_Position.decode str) of SOME pos => pos
  | _ => raise Fail "expected position"
fun unconstrain_var (Ast.Appl [Ast.Constant "_constrain", Ast.Variable name, Ast.Variable pos]) = (name, decode_pos pos)
  | unconstrain_var ast = raise Ast.AST ("Expected position constrained variable.", [ast])
fun make_constrained_var sx = (Ast.Appl [Ast.Constant "_constrain", Ast.Variable (Symbol_Pos.implode sx), Ast.Variable (Term_Position.encode (Position.range_position (Symbol_Pos.range sx)))])
fun implode_pos x = (Symbol_Pos.implode_range (Symbol_Pos.range x) x) |> (fn (x,y) => (x,Position.range_position y))
fun splitFormulaParts x = x |> unconstrain_var |> Symbol_Pos.explode |>
   Scan.finite Symbol_Pos.stopper (Scan.repeat (
  (Scan.one (Symbol_Pos.symbol #> Symbol.is_letter) --
  (((Scan.repeat (Symbol_Pos.$$ "\<^sub>" -- (Scan.one (Symbol_Pos.symbol #> Symbol.is_digit)) >> (fn (x,y) => [x,y])) >> List.concat )
  -- (Scan.repeat (Symbol_Pos.$$ "'"))) >> (fn (x,y) => x@y)))))
fun parseFormulaParts x = (case splitFormulaParts x of (parts,[]) => parts |> map (fn (x,y) => implode_pos (x::y))
    | _ => raise Ast.AST ("Expected one or more variable or term names.", [x]))
fun foldAppl const = List.rev #> (fn list => fold (fn a => fn b => (Ast.mk_appl (Ast.Constant const) [a,b])) (tl list) (hd list))
fun dropConstraints (Const ("_constrain", _) $ x $ _) = dropConstraints x
  | dropConstraints (Const ("_constrainAbs", _) $ x $ _) = dropConstraints x
  | dropConstraints (Abs (a, b, x)) = Abs (a, b, dropConstraints x)
  | dropConstraints (x$y) = dropConstraints x $ dropConstraints y
  | dropConstraints x = x
\<close>


parse_ast_translation\<open>
let
fun constrain (name, pos) = Ast.mk_appl (Ast.Constant "_constrain") [Ast.Variable name, Ast.Variable (Term_Position.encode pos)]
fun splitExeVars [x] = x |> parseFormulaParts |> map constrain |> 
  map (fn x => Ast.mk_appl (Ast.Constant "_AOT_term_var") [x]) |>
  foldAppl "_AOT_exe_args"
fun splitLambdaVars [x] = x |> parseFormulaParts |> map constrain |> 
  map (fn x => Ast.mk_appl (Ast.Constant "_AOT_var") [x]) |>
  foldAppl \<^const_syntax>\<open>Pair\<close>
fun checkSingleVar [x] = x |> parseFormulaParts |> map constrain |>
  (fn [x] => Ast.mk_appl (Ast.Constant "_AOT_var") [x] | _ => raise Ast.AST ("Expected single variable.", [x]))
in
[
  (\<^syntax_const>\<open>_AOT_var\<close>, K checkSingleVar),
  (\<^syntax_const>\<open>_AOT_exe_vars\<close>, K splitExeVars),
  (\<^syntax_const>\<open>_AOT_lambda_vars\<close>, K splitLambdaVars)
]
end
\<close>

consts AOT_denotes :: \<open>'a::AOT_Term \<Rightarrow> \<o>\<close>
       AOT_imp :: \<open>[\<o>, \<o>] \<Rightarrow> \<o>\<close>
       AOT_not :: \<open>\<o> \<Rightarrow> \<o>\<close>
       AOT_box :: \<open>\<o> \<Rightarrow> \<o>\<close>
       AOT_act :: \<open>\<o> \<Rightarrow> \<o>\<close>
       AOT_forall :: \<open>('a::AOT_Term \<Rightarrow> \<o>) \<Rightarrow> \<o>\<close>
       AOT_eq :: \<open>'a::AOT_Term \<Rightarrow> 'a::AOT_Term \<Rightarrow> \<o>\<close>
       AOT_desc :: \<open>('a::AOT_UnaryIndividualTerm \<Rightarrow> \<o>) \<Rightarrow> 'a\<close>
       AOT_exe :: \<open><'a::AOT_IndividualTerm> \<Rightarrow> 'a \<Rightarrow> \<o>\<close>
       AOT_lambda :: \<open>('a::AOT_IndividualTerm \<Rightarrow> \<o>) \<Rightarrow> <'a>\<close>
       AOT_lambda0 :: \<open>\<o> \<Rightarrow> \<o>\<close>
       AOT_concrete :: \<open><'a::AOT_UnaryIndividualTerm>\<close>
nonterminal desc
nonterminal exe_args
nonterminal \<Pi>0
syntax AOT_denotes :: \<open>\<tau> \<Rightarrow> \<phi>\<close> (\<open>_\<down>\<close>)
       AOT_imp :: \<open>[\<phi>, \<phi>] \<Rightarrow> \<phi>\<close> (infixl \<open>\<rightarrow>\<close> 25)
       AOT_not :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>\<not>_\<close> [50] 50)
       AOT_not :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>~_\<close> [50] 50)
       AOT_box :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>\<box>_\<close> [49] 54)
       AOT_act :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>\<^bold>\<A>_\<close> [49] 54)
       "_AOT_all" :: \<open>\<alpha> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (\<open>\<forall>_ _\<close> [1,40])
       "_AOT_all_ellipse" :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (\<open>\<forall>_...\<forall>_ _\<close> [1,40])
       AOT_eq :: \<open>[\<tau>, \<tau>] \<Rightarrow> \<phi>\<close> (infixl \<open>=\<close> 50)
       "_AOT_desc" :: \<open>\<alpha> \<Rightarrow> \<phi> \<Rightarrow> desc\<close> ("\<^bold>\<iota>__" [1,1000])
       "" :: \<open>desc \<Rightarrow> \<kappa>\<^sub>s\<close> ("_")
       "_AOT_lambda" :: \<open>lambda_args \<Rightarrow> \<phi> \<Rightarrow> \<Pi>\<close> (\<open>[\<lambda>__]\<close>)
       "_explicitRelation" :: \<open>\<tau> \<Rightarrow> \<Pi>\<close> ("[_]")
       "" :: \<open>desc \<Rightarrow> exe_arg\<close> ("_")
       "" :: \<open>exe_arg \<Rightarrow> exe_args\<close> ("_")
       "_AOT_exe_args" :: \<open>exe_arg \<Rightarrow> exe_args \<Rightarrow> exe_args\<close> ("__")
       "_AOT_exe_arg_ellipse" :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> exe_arg\<close> ("_..._")
       "_AOT_lambda_arg_ellipse" :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> lambda_args\<close> ("_..._")
       "_AOT_term_ellipse" :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> \<tau>\<close> ("_..._")
       "_AOT_exe" :: \<open>\<Pi> \<Rightarrow> exe_args \<Rightarrow> \<phi>\<close> (\<open>__\<close>)
       "_AOT_enc" :: \<open>exe_args \<Rightarrow> \<Pi> \<Rightarrow> \<phi>\<close> (\<open>__\<close>)
       AOT_lambda0 :: \<open>\<phi> \<Rightarrow> \<Pi>0\<close> (\<open>[\<lambda> _]\<close>)
       "" :: \<open>\<Pi>0 \<Rightarrow> \<phi>\<close> ("_")
       "" :: \<open>\<Pi>0 \<Rightarrow> \<tau>\<close> ("_")
       AOT_concrete :: \<open>\<Pi>\<close> (\<open>E!\<close>)

translations
  "_AOT_all \<alpha> \<phi>" == "CONST AOT_forall (\<lambda> \<alpha> . \<phi>)"
  "_AOT_desc \<alpha> \<phi>" == "CONST AOT_desc (\<lambda> \<alpha> . \<phi>)"
  "_AOT_lambda \<alpha> \<phi>" == "CONST AOT_lambda (\<lambda> \<alpha> . \<phi>)"
  "_explicitRelation \<Pi>" => "\<Pi>"


nonterminal free_var
nonterminal free_vars
syntax "" :: \<open>desc \<Rightarrow> free_var\<close> ("_")
syntax "" :: \<open>\<Pi> \<Rightarrow> free_var\<close> ("_")
syntax "_appl" :: \<open>id_position \<Rightarrow> free_vars \<Rightarrow> \<phi>\<close> ("_'{_'}")
syntax "_appl" :: \<open>id_position \<Rightarrow> free_vars \<Rightarrow> \<tau>\<close> ("_'{_'}")
syntax "_AOT_term_var" :: \<open>id_position \<Rightarrow> free_var\<close> ("_")
syntax "" :: \<open>any \<Rightarrow> free_var\<close> ("\<guillemotleft>_\<guillemotright>")
syntax "" :: \<open>free_var \<Rightarrow> free_vars\<close> ("_")
syntax "_args" :: \<open>free_var \<Rightarrow> free_vars \<Rightarrow> free_vars\<close> ("_,_")
syntax "_AOT_free_var_ellipse" :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> free_var\<close> ("_..._")

ML\<open>
fun constrainSort trm sort = Const ("_constrain", dummyT) $ trm $ (Const ("_dummy_ofsort", dummyT) $ Const (sort, dummyT))
fun parseVar fstsnd ctxt [var as Const ("_constrain", _) $ Free (x,_) $ Free _] =
       constrainSort var (case fetchTermPrefix ctxt x of
          (SOME (meta,sortPair),_) =>
            if meta then raise Term.TERM ("Expected variable prefix, but got metavariable prefix.", [var])
            else fstsnd sortPair
          | _ => raise Term.TERM ("Unknown variable prefix.", [var]))
  | parseVar _ _ var = raise Term.TERM ("Expected constrained free variable.", var)

fun constrainTrm ctxt fstsnd (Free (var, _)) = (fn trm =>
      case fetchTermPrefix ctxt var of (SOME (meta,sortpair),_) =>
        if meta then
          constrainSort trm (fstsnd sortpair)
        else
          constrainSort (Const (\<^const_syntax>\<open>AOT_term_of_var\<close>, dummyT) $ trm) (fstsnd sortpair)
      | _ => raise Term.TERM ("Unknown variable or metavariable prefix.", [trm]))
  | constrainTrm _ _ (Bound _) = (fn var => var)
  | constrainTrm _ _ trm = raise Term.TERM ("Expected free or bound variable.", [trm])
fun processFrees ctxt (Const (\<^syntax_const>\<open>_AOT_term_var\<close>, _) $ v) = (constrainTrm ctxt fst (dropConstraints v) v)
  | processFrees ctxt (Const ("_AOT_term_vars", _) $ v) = (constrainTrm ctxt snd (dropConstraints v) v)
  | processFrees _ (Const (\<^syntax_const>\<open>_AOT_verbatim\<close>, _) $ v) = v
  | processFrees ctxt (x $ y) = processFrees ctxt x $ processFrees ctxt y
  | processFrees ctxt (Abs (x,y,z)) = Abs (x,y,processFrees ctxt z)
  | processFrees _ x = x
\<close>

(* TODO: move *)
nonterminal AOT_props
syntax (input) "_AOT_props" :: \<open>AOT_prop \<Rightarrow> AOT_props \<Rightarrow> AOT_props\<close> (infixr \<open>,\<close> 3)
syntax "_AOT_prop" :: \<open>\<phi> \<Rightarrow> AOT_prop\<close> (\<open>_\<close>)
       "" :: \<open>AOT_prop \<Rightarrow> AOT_props\<close> (\<open>_\<close>)
       "_AOT_derivable" :: "AOT_props \<Rightarrow> AOT_prop \<Rightarrow> AOT_prop" (infixl \<open>\<^bold>\<turnstile>\<close> 2)
       "_AOT_theorem" :: "\<phi> \<Rightarrow> AOT_prop" (\<open>\<^bold>\<turnstile>_\<close>)
       "_AOT_nec_theorem" :: "\<phi> \<Rightarrow> AOT_prop" (\<open>\<^bold>\<turnstile>\<^sub>\<box>_\<close>)
       "_AOT_equiv_def" :: \<open>\<phi> \<Rightarrow> \<phi> \<Rightarrow> AOT_prop\<close> (infixl \<open>\<equiv>\<^sub>d\<^sub>f\<close> 3)
       "_AOT_id_def" :: \<open>\<tau> \<Rightarrow> \<tau> \<Rightarrow> AOT_prop\<close> (infixl \<open>=\<^sub>d\<^sub>f\<close> 3)
       "_AOT_for_arbitrary" :: \<open>id_position \<Rightarrow> AOT_prop \<Rightarrow> AOT_prop\<close> (\<open>for arbitrary _: _\<close> [1000,1] 1)

translations
  "_AOT_props a b" => "CONST Pure.conjunction a b"

parse_translation\<open>
let
fun makeArgList (Const (\<^syntax_const>\<open>_AOT_exe_args\<close>, _) $ y $ z) = makeArgList y @ makeArgList z
  | makeArgList t = [t]
fun makePairs (x::[]) = x
  | makePairs (x::xs) = Const (\<^const_syntax>\<open>Pair\<close>, dummyT) $ x $ makePairs xs
fun makeExeArgs y = makePairs (makeArgList y)
fun parseExe ctxt [x,y] = (Const (\<^const_syntax>\<open>AOT_exe\<close>, dummyT) $ x $ makeExeArgs y)
fun parseEnc ctxt [x,y] = (Const ("AOT_enc", dummyT) $ makeExeArgs x $ y)
in
[
  (\<^syntax_const>\<open>_AOT_var\<close>, parseVar fst),
  ("_AOT_vars", parseVar snd),
  (\<^syntax_const>\<open>_AOT_valid\<close>, fn ctxt => fn [w,x] => \<^const>\<open>AOT_model_valid_in\<close> $ w $ processFrees ctxt x),
  (\<^syntax_const>\<open>_AOT_quoted\<close>, fn ctxt => fn [x] => processFrees ctxt x),
  (\<^syntax_const>\<open>_AOT_prop\<close>, fn ctxt => fn [x] => let
    val world = case (AOT_ProofData.get ctxt) of SOME w => w | _ => raise Fail "Expected world to be stored in the proof state."
    val trm = case x of (Const ("_AOT_term_var", _) $ (y as (Const ("_constrain", _) $ Free (name, _) $ pos))) =>
              if (hd (Symbol.explode name)) = "\<Gamma>" then SOME (HOLogic.mk_Trueprop y) else NONE | _ => NONE
    val trm = case trm of SOME trm => trm
        | _ => HOLogic.mk_Trueprop (@{const AOT_model_valid_in} $ world $ (processFrees ctxt x))
    in trm end),
  (\<^syntax_const>\<open>_AOT_theorem\<close>, fn ctxt => fn [x] => HOLogic.mk_Trueprop (@{const AOT_model_valid_in} $ @{const w\<^sub>0} $ (processFrees ctxt x))),
  (\<^syntax_const>\<open>_AOT_nec_theorem\<close>, fn ctxt => fn [x] => let
    val trm = processFrees ctxt x
    val world = singleton (Variable.variant_frees ctxt [trm]) ("v", @{typ w})
    val trm = HOLogic.mk_Trueprop (@{const AOT_model_valid_in} $ Free world $ trm)
    val trm = Term.absfree world trm
    val trm = Const (\<^const_name>\<open>Pure.all\<close>, dummyT) $ trm
    in trm end),
  (\<^syntax_const>\<open>_AOT_derivable\<close>, fn ctxt => fn [x,y] => let
    in @{const "Pure.imp"} $ x $ y end),
  (\<^syntax_const>\<open>_AOT_for_arbitrary\<close>, fn ctxt => fn [_ $ var $ pos,trm] => let
    val trm = Const (\<^const_name>\<open>Pure.all\<close>, dummyT) $ (Const ("_constrainAbs", dummyT) $ Term.absfree (Term.dest_Free var) trm $ pos)
    in trm end),
  (\<^syntax_const>\<open>_AOT_equiv_def\<close>, fn ctxt => fn [x,y] => HOLogic.mk_Trueprop (\<^const>\<open>AOT_model_equiv_def\<close> $ processFrees ctxt x $ processFrees ctxt y)),
  (\<^syntax_const>\<open>_AOT_exe\<close>, parseExe),
  (\<^syntax_const>\<open>_AOT_enc\<close>, parseEnc)
]
end
\<close>

ML\<open>
fun parseEllipseList constName _ [s,e] =
  let
    val (start_name, start_pos) = unconstrain_var s
    val (end_name, end_pos) = unconstrain_var e
    val _ = let val h = hd (Symbol.explode start_name) in
        if (h = hd (Symbol.explode end_name)) then h else raise Ast.AST ("Invalid ellipses.", [s,e])
      end
    val name = (Symbol_Pos.explode (start_name, start_pos)) @ (Symbol_Pos.explode (end_name, end_pos))
  in
    Ast.mk_appl (Ast.Constant constName) [make_constrained_var name]
  end
  | parseEllipseList _ _ _ = raise Fail "Invalid ellipse parsing."
\<close>

parse_ast_translation\<open>
[
  (\<^syntax_const>\<open>_AOT_exe_arg_ellipse\<close>, parseEllipseList "_AOT_term_vars"),
  (\<^syntax_const>\<open>_AOT_lambda_arg_ellipse\<close>, parseEllipseList "_AOT_vars"),
  (\<^syntax_const>\<open>_AOT_free_var_ellipse\<close>, parseEllipseList "_AOT_term_vars"),
  (\<^syntax_const>\<open>_AOT_term_ellipse\<close>, parseEllipseList "_AOT_term_vars"),
  (\<^syntax_const>\<open>_AOT_all_ellipse\<close>, fn ctx => fn [a,b,c] => Ast.mk_appl (Ast.Constant "_AOT_all") [parseEllipseList "_AOT_vars" ctx [a,b],c])
]
\<close>

translations
  (\<phi>) "\<tau>\<down>" <= "CONST AOT_denotes \<tau>"
  (\<phi>) "\<phi> \<rightarrow> \<psi>" <= "CONST AOT_imp \<phi> \<psi>"
  (\<phi>) "\<not>\<phi>" <= "CONST AOT_not \<phi>"
  (\<phi>) "\<box>\<phi>" <= "CONST AOT_box \<phi>"
  (\<phi>) "\<^bold>\<A>\<phi>" <= "CONST AOT_act \<phi>"
  (\<phi>) "\<forall>\<alpha> \<phi>" == "CONST AOT_forall (_abs \<alpha> \<phi>)"
  (\<phi>) "\<forall>\<alpha> \<phi>" <= "CONST AOT_forall (\<lambda>\<alpha>. \<phi>)"
  (\<phi>) "\<tau> = \<tau>'" <= "CONST AOT_eq \<tau> \<tau>'"
  (\<tau>) "\<^bold>\<iota>x \<phi>" == "CONST AOT_desc (\<lambda>x. \<phi>)"

print_translation \<open>
 [
  Syntax_Trans.preserve_binder_abs_tr' \<^const_syntax>\<open>AOT_forall\<close> \<^syntax_const>\<open>_AOT_all\<close>,
  Syntax_Trans.preserve_binder_abs_tr' \<^const_syntax>\<open>AOT_desc\<close> \<^syntax_const>\<open>_AOT_desc\<close>,
  Syntax_Trans.preserve_binder_abs_tr' \<^const_syntax>\<open>AOT_lambda\<close> \<^syntax_const>\<open>_AOT_lambda\<close>
 ]
\<close> \<comment> \<open>to avoid eta-contraction\<close>

parse_translation\<open>
let
fun parseIdDef ctxt [lhs, rhs] =
  let
    val lhs = processFrees ctxt lhs
    val rhs = processFrees ctxt rhs
    fun add_frees (Free _) frees = frees
      | add_frees (Const _) frees = frees
      | add_frees (Free _ $ args) frees = Term.add_frees args frees
      | add_frees (Const _ $ args) frees = Term.add_frees args frees
      | add_frees trm _ = raise Term.TERM ("Expected definition term.", [trm])
    val lhs' = dropConstraints lhs
    val rhs' = dropConstraints rhs
    val frees = add_frees lhs' []
    val _ = frees = add_frees rhs' frees orelse
            raise Term.TERM ("Invalid free variables on RHS.", [lhs,rhs])
    fun mkabs trm = if frees = [] then Const (\<^const_name>\<open>case_unit\<close>, dummyT) $ trm else
       fold_rev (fn (s, T) => fn t => Const (\<^const_name>\<open>case_prod\<close>, dummyT) $ Term.absfree (s, T) t)
                (List.rev (tl frees)) (Term.absfree (hd frees) trm)
    val lhs_abs = mkabs lhs
    val rhs_abs = mkabs rhs
  in
    Const (\<^const_name>\<open>AOT_model_id_def\<close>, dummyT) $ lhs_abs $ rhs_abs
  end
in
[(\<^syntax_const>\<open>_AOT_id_def\<close>, parseIdDef)]
end
\<close>

AOT_define AOT_dia :: \<open>\<phi> \<Rightarrow> \<phi>\<close> (\<open>\<diamond>_\<close> [49] 54) \<open>\<diamond>\<phi> \<equiv>\<^sub>d\<^sub>f \<not>\<box>\<not>\<phi>\<close>
AOT_define AOT_conj :: \<open>[\<phi>, \<phi>] \<Rightarrow> \<phi>\<close> (infixl \<open>&\<close> 35) \<open>\<phi> & \<psi> \<equiv>\<^sub>d\<^sub>f \<not>(\<phi> \<rightarrow> \<not>\<psi>)\<close>
AOT_define AOT_disj :: \<open>[\<phi>, \<phi>] \<Rightarrow> \<phi>\<close> (infixl \<open>\<or>\<close> 35) \<open>\<phi> \<or> \<psi> \<equiv>\<^sub>d\<^sub>f \<not>\<phi> \<rightarrow> \<psi>\<close>
AOT_define AOT_equiv :: \<open>[\<phi>, \<phi>] \<Rightarrow> \<phi>\<close> (infixl \<open>\<equiv>\<close> 20) \<open>\<phi> \<equiv> \<psi> \<equiv>\<^sub>d\<^sub>f (\<phi> \<rightarrow> \<psi>) & (\<psi> \<rightarrow> \<phi>)\<close>

AOT_define AOT_exists :: \<open>\<alpha> \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> ("\<exists>_ _" [1,40]) \<open>\<guillemotleft>AOT_exists \<phi>\<guillemotright> \<equiv>\<^sub>d\<^sub>f \<not>\<forall>\<alpha> \<not>\<phi>{\<alpha>}\<close>
translations
  "AOT_exists \<tau> \<phi>" == "CONST AOT_exists (_abs \<tau> \<phi>)"
syntax
   "_AOT_exists_ellipse" :: \<open>id_position \<Rightarrow> id_position \<Rightarrow> \<phi> \<Rightarrow> \<phi>\<close> (\<open>\<exists>_...\<exists>_ _\<close> [1,40])
parse_ast_translation\<open>[(\<^syntax_const>\<open>_AOT_exists_ellipse\<close>, fn ctx => fn [a,b,c] =>
  Ast.mk_appl (Ast.Constant "AOT_exists") [parseEllipseList "_AOT_vars" ctx [a,b],c])]\<close>
print_translation
  \<open>[Syntax_Trans.preserve_binder_abs_tr' \<^const_syntax>\<open>AOT_exists\<close> \<^syntax_const>\<open>AOT_exists\<close>]\<close>

end
