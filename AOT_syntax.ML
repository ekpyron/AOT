fun AOT_binder_trans thy bnd syntaxConst =
  (Lexicon.mark_const (Sign.full_name thy bnd),
   K (fn trms => Term.list_comb (Const (syntaxConst, dummyT),trms)))

datatype AOT_VariableKind = AOT_Variable of (term*term) option | AOT_MetaVariable
structure AOT_VariablePrefix = Theory_Data (
  type T = (AOT_VariableKind*string) Symtab.table
  val empty = Symtab.empty
  val extend = I
  (* TODO: probably better to remove conflicts than to ignore them *)
  val merge = Symtab.merge (K true)
);
structure AOT_PremiseSetPrefix = Theory_Data (
  type T = unit Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.merge (K true)
);
structure AOT_Constraints = Theory_Data (
  type T = (term*term) Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.merge (fn ((x,y),(x',y')) => x = x' andalso y = y')
)
structure AOT_Restriction = Theory_Data (
  type T = (term*term) Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.merge (fn ((x,y),(x',y')) => x = x' andalso y = y')
)

fun AOT_IsPremiseSetPrefix ctxt = Local_Theory.raw_theory_result
  (fn thy => (AOT_PremiseSetPrefix.get thy, thy)) ctxt
  |> fst |> Symtab.lookup #> Option.isSome

fun term_of_sort S =
  let
    val class = Syntax.const o Lexicon.mark_class;
    fun classes [c] = class c
      | classes (c :: cs) = Syntax.const "_classes" $ class c $ classes cs
      | classes _ = raise Fail "Unexpected.";
  in
    if S = dummyS then Syntax.const "_dummy_sort"
    else
      (case S of
        [] => Syntax.const "_topsort"
      | [c] => class c
      | cs => Syntax.const "_sort" $ classes cs)
  end
fun term_of (Type (a, Ts)) = 
      Term.list_comb (Syntax.const (Lexicon.mark_type a), map term_of Ts)
  | term_of (TFree ("'_dummy_",sort)) =
      (Const ("_dummy_ofsort", dummyT) $ term_of_sort sort)
  | term_of (t as TFree _) = (@{print} t; raise Term.TYPE ("", [t], []))
  | term_of (TVar _) = raise Fail "";

fun fetchTermCategory ctxt = Local_Theory.raw_theory_result (fn thy =>
  (Symtab.lookup (AOT_VariablePrefix.get thy), thy)) ctxt |> fst
fun maybeGetConstraint ctxt unary name = Local_Theory.raw_theory_result (fn thy => 
   ((if unary then Option.map fst else Option.map snd)
    (Symtab.lookup (AOT_Constraints.get thy) name), thy)) ctxt |> fst
fun getConstraint ctxt unary name =
  (case maybeGetConstraint ctxt unary name of SOME c => c |
   _ => raise Fail ("Unknown type category: " ^ name))

fun fetchTermConstraint ctxt name unary =
  Local_Theory.raw_theory_result (fn thy =>
    (Option.map (fn (meta, category) => (meta, getConstraint ctxt unary category))
    ((Symtab.lookup o AOT_VariablePrefix.get) thy (hd (Symbol.explode name))), thy)
) ctxt |> fst

fun register_constraint (name:string, (unaryConstraint,naryConstraint)) thy = (
let
fun trmOf constr = term_of (Syntax.parse_typ (Proof_Context.init_global thy) constr)
val unaryConstraint = trmOf unaryConstraint
val naryConstraint = (case naryConstraint of
  (SOME constraint) => trmOf constraint
  | _ => unaryConstraint
)
in 
AOT_Constraints.map (Symtab.update (name, (unaryConstraint, naryConstraint))) thy
end
)

fun register_variable_name meta (category, prefices) thy =
let
val restr = (Symtab.lookup (AOT_Restriction.get thy) category)
val kind = if meta then AOT_MetaVariable else AOT_Variable restr
in
   fold (fn prefix => AOT_VariablePrefix.map
      (Symtab.update (prefix, (kind, category)))) prefices thy
end
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_register_variable_names\<close>
  "Register variable names for type categories."
  (Parse.and_list1 ((Parse.short_ident --| Parse.$$$ ":" )
                    -- Scan.repeat1 Parse.short_ident)
   >> (Toplevel.theory o (fold (register_variable_name false))));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_register_metavariable_names\<close>
  "Register meta-variable names for type categories."
    (Parse.and_list1 ((Parse.short_ident --| Parse.$$$ ":")
                      -- Scan.repeat1 Parse.short_ident)
     >> (Toplevel.theory o (fold (register_variable_name true))));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_register_premise_set_names\<close>
  "Register names for premise sets."
  (Scan.repeat1 Parse.short_ident
   >> (Toplevel.theory o fold
          (fn prefix => AOT_PremiseSetPrefix.map (Symtab.update (prefix,())))));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_register_type_constraints\<close>
  "Register constraints for term types."
  (Parse.and_list1 ((Parse.short_ident --| Parse.$$$ ":")
                    -- (Parse.typ -- Scan.option Parse.typ))
  >> (Toplevel.theory o fold register_constraint));


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

local
fun constrain (name, pos) = Ast.mk_appl (Ast.Constant "_constrain") [Ast.Variable name, Ast.Variable (Term_Position.encode pos)]
in
fun AOT_split_exe_vars [x] = x |> parseFormulaParts |> map constrain |> 
  map (fn x => Ast.mk_appl (Ast.Constant "_AOT_term_var") [x]) |>
  foldAppl "_AOT_exe_args"
fun AOT_split_lambda_args [x] = x |> parseFormulaParts |> map constrain |> 
  map (fn x => Ast.mk_appl (Ast.Constant "_AOT_var") [x]) |>
  foldAppl \<^const_syntax>\<open>Pair\<close>
fun AOT_check_var [x] = x |> parseFormulaParts |> map constrain |>
  (fn [x] => Ast.mk_appl (Ast.Constant "_AOT_var") [x] | _ => raise Ast.AST ("Expected single variable.", [x]))
end

fun parseVar unary ctxt [var as Const ("_constrain", _) $ Free (x,_) $ Free _] =
        Const ("_constrain", dummyT) $ var $ (case fetchTermConstraint ctxt x unary of
            SOME (AOT_MetaVariable,_) => raise Term.TERM ("Expected variable prefix, but got metavariable prefix.", [var])
          | SOME (AOT_Variable _, constraint) => constraint
          | _ => raise Term.TERM ("Unknown variable prefix.", [var]))
  | parseVar _ _ var = raise Term.TERM ("Expected constrained free variable.", var)

fun constrainTrm ctxt forceMeta unary (Free (var, _)) = (fn trm =>
      case fetchTermConstraint ctxt var unary of
        SOME (AOT_MetaVariable,constraint) => Const ("_constrain", dummyT) $ trm $ constraint
      | SOME (AOT_Variable restr, constraint) =>
          if forceMeta then Const ("_constrain", dummyT) $ trm $ constraint
          else Const ("_constrain", dummyT) $ (Const (\<^const_name>\<open>AOT_term_of_var\<close>, dummyT) $ (case restr of SOME (_,r) => r $ trm | _ => trm)) $ constraint
      | _ => raise Term.TERM ("Unknown variable or metavariable prefix.", [trm]))
  | constrainTrm _ _ _ (Bound _) = (fn var => var)
  | constrainTrm _ _ _ trm = raise Term.TERM ("Expected free or bound variable.", [trm])
fun isPremiseVar ctxt (Free (var, _)) = AOT_IsPremiseSetPrefix ctxt (hd (Symbol.explode var))
  | isPremiseVar _ _ = false
fun getVarConstraint ctxt unary (Free (var, _)) = (case fetchTermConstraint ctxt var unary of
        SOME (AOT_MetaVariable,_) => NONE
      | SOME (AOT_Variable Rep_term,_) => Option.map fst Rep_term
      | _ => NONE)
  | getVarConstraint _ _ _ = NONE
fun getVarConstraints ctxt (Const (\<^syntax_const>\<open>_AOT_term_var\<close>, _) $ v) = (case (getVarConstraint ctxt true (dropConstraints v)) of SOME c => [(c,v)] | _ => [])
  | getVarConstraints ctxt (Const ("_AOT_term_vars", _) $ v) = (case (getVarConstraint ctxt true (dropConstraints v)) of SOME c => [(c,v)] | _ => [])
  | getVarConstraints _ (Const (\<^syntax_const>\<open>_AOT_verbatim\<close>, _) $ _) = []
  | getVarConstraints ctxt (x $ y)  = getVarConstraints ctxt x @ getVarConstraints ctxt y
  | getVarConstraints ctxt (Abs (_,_,z)) = getVarConstraints ctxt z
  | getVarConstraints _ _ = []
fun processFreesForceMeta forceMeta premiseVars ctxt (Const (\<^syntax_const>\<open>_AOT_term_var\<close>, _) $ v) = (
    if isPremiseVar ctxt (dropConstraints v) then (dropConstraints v, if List.find (fn x => x = v) premiseVars = NONE then v::premiseVars else premiseVars)
                         else (constrainTrm ctxt forceMeta true (dropConstraints v) v, premiseVars))
  | processFreesForceMeta forceMeta premiseVars ctxt (Const ("_AOT_term_vars", _) $ v) = (
    if isPremiseVar ctxt (dropConstraints v) then (v, if List.find (fn x => x = v) premiseVars = NONE then v::premiseVars else premiseVars)
     else (constrainTrm ctxt forceMeta false (dropConstraints v) v, premiseVars)
  )
  | processFreesForceMeta _ premiseVars _ (Const (\<^syntax_const>\<open>_AOT_verbatim\<close>, _) $ v) = (v, premiseVars)
  | processFreesForceMeta forceMeta premiseVars ctxt (x $ y)  = let
          val (x, premiseVars) = processFreesForceMeta forceMeta premiseVars ctxt x
          val (y, premiseVars) = processFreesForceMeta forceMeta premiseVars ctxt y
      in (x $ y, premiseVars) end
  | processFreesForceMeta forceMeta premiseVars ctxt (Abs (x,y,z)) = let
      val (z, premiseVars) = processFreesForceMeta forceMeta premiseVars ctxt z
      in (Abs (x,y,z), premiseVars) end
  | processFreesForceMeta _ premiseVars _ x = (x, premiseVars)
fun processFrees ctxt trm = (case processFreesForceMeta false [] ctxt trm of (r,[]) => r | _ => raise Term.TERM ("No premise set expected in term.", [trm]))
fun processFreesAlwaysMeta ctxt trm = (case processFreesForceMeta true [] ctxt trm of (r,[]) => r | _ => raise Term.TERM ("No premise set expected in term.", [trm]))
val processFreesAndPremises = processFreesForceMeta false []

local
fun makeArgList (Const (\<^syntax_const>\<open>_AOT_exe_args\<close>, _) $ y $ z) = makeArgList y @ makeArgList z
  | makeArgList t = [t]
fun makePairs (x::[]) = x
  | makePairs (x::xs) = Const (\<^const_syntax>\<open>Pair\<close>, dummyT) $ x $ makePairs xs
fun makeExeArgs y = makePairs (makeArgList y)
in
fun foldPremises world (Const (\<^syntax_const>\<open>_AOT_premises\<close>, _) $ p1 $ p2) y =
  @{const "Pure.imp"} $ (p1 $ world) $ foldPremises world p2 y
| foldPremises world x y =
  @{const "Pure.imp"} $ (x $ world) $ HOLogic.mk_Trueprop  (@{const AOT_model_valid_in} $ world $ y)
fun parseExe ctxt [x,y] = (Const (\<^const_syntax>\<open>AOT_exe\<close>, dummyT) $ x $ makeExeArgs y)
fun parseEnc ctxt [x,y] = (Const ("AOT_enc", dummyT) $ makeExeArgs x $ y)
fun parseEquivDef ctxt [lhs,rhs] =
  let
    val constraints = getVarConstraints ctxt lhs
    fun collectConstraints c [] = c
     | collectConstraints NONE ((x,y)::xs) = collectConstraints (SOME (x $ y)) xs
     | collectConstraints (SOME c) ((x,y)::xs) = collectConstraints (SOME (Const ("AOT_conj", dummyT) $  c $ (x $ y))) xs
    val rhs = (case collectConstraints NONE constraints of SOME c => Const ("AOT_conj", dummyT) $ c $ rhs | _ => rhs)
  in
  HOLogic.mk_Trueprop (\<^const>\<open>AOT_model_equiv_def\<close> $ processFreesAlwaysMeta ctxt lhs $ processFreesAlwaysMeta ctxt rhs)
  end
  | parseEquivDef _ terms = raise Term.TERM ("Expected definition arguments.", terms)
fun parseIdDef ctxt [lhs, rhs] =
  let
    val lhs = processFreesAlwaysMeta ctxt lhs
    val rhs = processFreesAlwaysMeta ctxt rhs
    fun add_frees (Free _) frees = frees
      | add_frees (Const _) frees = frees
      | add_frees (Free _ $ args) frees = Term.add_frees args frees
      | add_frees (Const _ $ args) frees = Term.add_frees args frees
      | add_frees (args $ args') frees = Term.add_frees args' (Term.add_frees args frees)
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
    (Const ("_constrain", dummyT) $
     Const (\<^const_name>\<open>AOT_model_id_def\<close>, dummyT) $
     (Const (\<^type_syntax>\<open>fun\<close>, dummyT) $
        (Const (\<^type_syntax>\<open>fun\<close>, dummyT) $ Const (\<^type_syntax>\<open>dummy\<close>, dummyT) $ (getConstraint ctxt false "Term")) $
        (Const (\<^type_syntax>\<open>dummy\<close>, dummyT)))
    )
    $ lhs_abs $ rhs_abs
  end
  | parseIdDef _ terms = raise Term.TERM ("Expected definition arguments.", terms)
end

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

datatype PrintVarKind = SingleVariable of string | Ellipses of string*string | Verbatim of string

fun printVarKind name = let
fun splitFormulaParts x = x |> Symbol.explode |>
   Scan.finite Symbol.stopper (Scan.repeat (
  (Scan.one (Symbol.is_letter) --
  (((Scan.repeat ($$ "\<^sub>" -- (Scan.one (Symbol.is_char)) >> (fn (x,y) => [x,y])) >> List.concat )
  -- (Scan.repeat ($$ "'"))) >> (fn (x,y) => x@y)))))
val parts = splitFormulaParts (Name.clean name)
val isSingleVariableName = case parts of
        ([_],[]) => true | _ => false
(* TODO: ellipses handling is very fragile *)
val (isEllipses,s,e) = case parts of
        ([(n,s),(m,e)],[]) => (n = m, n^String.concat s, m^String.concat e) | _ => (false,"","")
in
if isSingleVariableName then SingleVariable name else
if isEllipses then Ellipses (s,e)
else Verbatim name
end

local
fun addFunct (x,f) g = (x, fn y => g (f y))
fun unconstrain (Ast.Appl (Ast.Constant "_constrain"::x::tl)) = addFunct (unconstrain x) (fn x => Ast.Appl (Ast.Constant "_constrain"::x::tl))
  | unconstrain (Ast.Appl (Ast.Constant "_free"::[x])) = addFunct (unconstrain x) (fn x => Ast.Appl (Ast.Constant "_free"::[x]))
  | unconstrain (Ast.Appl (Ast.Constant "_bound"::[x])) = addFunct (unconstrain x) (fn x => Ast.Appl (Ast.Constant "_bound"::[x]))
  | unconstrain (Ast.Appl (Ast.Constant "_var"::[x])) = addFunct (unconstrain x) (fn x => Ast.Appl (Ast.Constant "_var"::[x]))
  | unconstrain trm = (trm, fn x => x)
fun isDefinedConst ctxt name = let
  val unmarkedName = Lexicon.unmark {case_class = fn str => NONE,
      case_type = fn name => NONE,
      case_const = fn name => SOME name,
      case_fixed = fn name => NONE,
      case_default = fn name => SOME name} name
  val cons = Option.mapPartial (fn name => try (Proof_Context.read_const {proper = true, strict = true} ctxt) name) unmarkedName
  val defined = case cons of
    SOME cons =>
      Termtab.defined (AOT_DefinedConstants.get (Proof_Context.theory_of ctxt)) cons
      orelse cons = @{const AOT_concrete}
    | _ => false
  in defined end
in
val AOT_print_individual_term = (fn ctxt =>
    (fn [trm as Ast.Appl (Ast.Constant \<^const_syntax>\<open>AOT_term_of_var\<close>::_)] => trm
    | [trm as Ast.Appl (Ast.Constant \<^syntax_const>\<open>_AOT_desc\<close>::_)] => trm
    | [trm as Ast.Appl (Ast.Constant \<^syntax_const>\<open>_AOT_free_var_ellipse\<close>::_)] => trm
    | [trm as Ast.Constant _] => trm
    | [trm] => (case unconstrain trm of (Ast.Variable name,c) => 
                  (case printVarKind name of SingleVariable x => c (Ast.Variable name) |
                    Ellipses (x,y) => (Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_exe_arg_ellipse\<close>) [
                c (Ast.Variable x),
                c (Ast.Variable y)])
              | _ => Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_quoted\<close>) [trm]
        ) 
        | (Ast.Constant name,c) => if isDefinedConst ctxt name then c (Ast.Constant name) else Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_quoted\<close>) [trm]
        |  (trm' as Ast.Appl (Ast.Constant name::_),c) =>
            (if isDefinedConst ctxt name then c trm' else Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_quoted\<close>) [trm])
        |  _ => Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_quoted\<close>) [trm])
    | trms => Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_quoted\<close>) trms))
val AOT_print_relation_term = (fn ctxt =>
    (fn [trm as Ast.Appl (Ast.Constant \<^const_syntax>\<open>AOT_term_of_var\<close>::_)] => Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_explicitRelation\<close>) [trm]
    | [trm as Ast.Appl (Ast.Constant \<^syntax_const>\<open>_AOT_lambda\<close>::_)] => trm
    | [trm as Ast.Appl (Ast.Constant \<^const_syntax>\<open>AOT_lambda\<close>::_)] => trm
    | [trm] => (case unconstrain trm of (Ast.Variable name,c) => 
                  (case printVarKind name of SingleVariable x => (Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_explicitRelation\<close>) [c (Ast.Variable name)])
                  | _ => Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_quoted\<close>) [trm]
        ) 
        | (Ast.Constant name,c) => if isDefinedConst ctxt name then c (Ast.Constant name) else Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_quoted\<close>) [trm]
        |  (trm' as Ast.Appl (Ast.Constant name::_),c) =>
            (if isDefinedConst ctxt name then (Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_explicitRelation\<close>) [c trm']) else Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_quoted\<close>) [trm])
        |  _ => Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_quoted\<close>) [trm])
    | trms => Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_quoted\<close>) trms))
val AOT_print_generic_term = (fn ctxt =>
    (fn [trm as Ast.Appl (Ast.Constant \<^const_syntax>\<open>AOT_term_of_var\<close>::_)] => Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_explicitRelation\<close>) [trm]
    | [trm as Ast.Appl (Ast.Constant \<^syntax_const>\<open>_AOT_desc\<close>::_)] => trm
    | [trm as Ast.Appl (Ast.Constant \<^syntax_const>\<open>_AOT_free_var_ellipse\<close>::_)] => trm
    | [trm as Ast.Appl (Ast.Constant \<^syntax_const>\<open>_AOT_lambda\<close>::_)] => trm
    | [trm as Ast.Appl (Ast.Constant \<^const_syntax>\<open>AOT_lambda\<close>::_)] => trm
    | [trm as Ast.Appl (Ast.Constant "_AOT_raw_appl"::_)] => trm
    | [trm] => (case unconstrain trm of (Ast.Variable name,c) => 
                  (case printVarKind name of SingleVariable x => c (Ast.Variable name) |
                    Ellipses (x,y) => (Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_exe_arg_ellipse\<close>) [
                c (Ast.Variable x),
                c (Ast.Variable y)])
              | _ => Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_quoted\<close>) [trm]
        ) 
        | (Ast.Constant name,c) => if isDefinedConst ctxt name then c (Ast.Constant name) else Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_quoted\<close>) [trm]
        |  (trm' as Ast.Appl (Ast.Constant name::_),c) =>
            (if isDefinedConst ctxt name then c trm' else Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_quoted\<close>) [trm])
        |  _ => Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_quoted\<close>) [trm])
    | trms => Ast.mk_appl (Ast.Constant \<^syntax_const>\<open>_AOT_quoted\<close>) trms))
end

fun AOT_preserve_binder_abs_tr' constName syntaxConst (ellipseConst,includesSyntaxConst) restrConnect = 
(constName, fn ctxt => fn terms =>
let
val term_opt = case terms of Abs (name, T, trm)::trms => 
let
val trm = case printVarKind name of SingleVariable name =>
    let
      val optBody = case fetchTermCategory ctxt (hd (Symbol.explode (name))) of SOME (AOT_Variable _, category) =>
        let
          val (restr, _) = Local_Theory.raw_theory_result (fn thy => (Symtab.lookup (AOT_Restriction.get thy) category, thy)) ctxt
        in
          case restr of SOME restr =>
            (case trm of (Const (c,_) $ x $ trm) =>
              if (c = restrConnect orelse Lexicon.unmark_const c = restrConnect (* TODO: better matching *))
              then
                (* TODO: is this matching good enough? *)
                if Term.could_unify (Abs ("x", dummyT, x), Abs ("x", dummyT,  Term.betapply (fst restr,(Bound 0)))) then
                  SOME trm
                else
                  NONE
              else NONE | _ => NONE)
          | _ => NONE
        end
        | _ => NONE
      val terms = case optBody of SOME trm => Abs (name, T, trm)::trms | _ => trms
    in
        snd (Syntax_Trans.preserve_binder_abs_tr' constName syntaxConst) ctxt terms
    end
  | Ellipses (s,e) =>
    let
     (* TODO: ellipses that are fix'ed loose their markup - try to circumvent *)
    val body = Term.subst_bound (Const (\<^syntax_const>\<open>_AOT_free_var_ellipse\<close>, dummyT) $ Syntax_Trans.mark_bound_body (s,dummyT) $ Syntax_Trans.mark_bound_body (e,dummyT),
    trm)
    in
      if includesSyntaxConst then
        list_comb (Syntax.const ellipseConst $ Syntax_Trans.mark_bound_abs (s,dummyT) $ 
        Syntax_Trans.mark_bound_abs (e,dummyT) $ body, trms)
      else
        list_comb (Syntax.const syntaxConst $ (Syntax.const ellipseConst $ Syntax_Trans.mark_bound_abs (s,dummyT) $ 
        Syntax_Trans.mark_bound_abs (e,dummyT)) $ body, trms)
    end
  | Verbatim _ => (* TODO *)
    snd (Syntax_Trans.preserve_binder_abs_tr' constName syntaxConst) ctxt terms
in SOME trm end
| _ => NONE
in
case term_opt of SOME trm => trm | _ =>
snd (Syntax_Trans.preserve_binder_abs_tr' constName syntaxConst) ctxt terms
end
)

fun AOT_restricted_binder const connect = fn ctxt => (fn [a, b] => Ast.mk_appl (Ast.Constant const) [
let
val b = case a of (Ast.Appl [Ast.Constant "_AOT_var", var]) => (
case fetchTermCategory ctxt (hd (Symbol.explode (fst (unconstrain_var var)))) of SOME (AOT_Variable _, category) =>
  let
  val (restr, _) = Local_Theory.raw_theory_result (fn thy => (Symtab.lookup (AOT_Restriction.get thy) category, thy)) ctxt
  in case restr of SOME _ => Ast.mk_appl (Ast.Constant connect) [Ast.mk_appl (Ast.mk_appl (Ast.Constant "_AOT_restriction") [Ast.Constant category]) [a], b] | _ => b end | _ => b) | _ => b
in
  Ast.mk_appl (Ast.Constant "_abs")  [a,b]
end] | _ => raise Match)

fun parseDDOT ctxt _ =
  let
    val trm = Proof_Context.get_fact_single ctxt (Facts.named (Long_Name.localN ^ Long_Name.separator ^ Auto_Bind.thisN))
    val trm = Thm.concl_of trm
    (* TODO: find a proper way to do this *)
    fun mapTerms (Free (x,typ)) = (case List.rev (String.explode x) of #"_" :: #"_" :: tl =>
      Free (String.implode (List.rev tl), typ) | _ => Free (x,typ))
      | mapTerms x = x
    val trm = Term.map_aterms mapTerms trm
    fun readThisRHS (Const ("HOL.Trueprop", _) $ (Const ("AOT_model.AOT_model_valid_in", _) $ _ $ (Const _ $ _ $ rhs))) = rhs
      | readThisRHS _ = raise Term.TERM ("Could not expand ... from term.", [trm])
  in
    readThisRHS trm
  end