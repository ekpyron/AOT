(*
This file contains modified parts of the Isabelle ML sources
which are distributed with Isabelle under the following conditions:

ISABELLE COPYRIGHT NOTICE, LICENCE AND DISCLAIMER.

Copyright (c) 1986-2021,
  University of Cambridge,
  Technische Universitaet Muenchen,
  and contributors.

  All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

* Redistributions of source code must retain the above copyright
notice, this list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright
notice, this list of conditions and the following disclaimer in the
documentation and/or other materials provided with the distribution.

* Neither the name of the University of Cambridge or the Technische
Universitaet Muenchen nor the names of their contributors may be used
to endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

fun AOT_item_by_name name = Option.map fst (List.find (fn (_,n) => n = name) AOT_items)
fun AOT_name_of_item id = Option.map snd (List.find (fn (i,_) => id = i) AOT_items)

val print_AOT_syntax = Attrib.setup_config_bool @{binding "show_AOT_syntax"} (K false)
local
    fun AOT_map_translation b (name:string, f) = (name, fn ctxt =>
      if Config.get ctxt print_AOT_syntax = b
      then f ctxt
      else raise Match)
in
val AOT_syntax_print_translations =
  map (fn (n,f:Proof.context -> term list -> term) =>
       AOT_map_translation true (n,f))
val AOT_syntax_typed_print_translations
  = map (fn (n,f:Proof.context -> typ -> term list -> term) =>
         AOT_map_translation true (n,f))
val AOT_syntax_print_ast_translations
  = map (fn (n,f:Proof.context -> Ast.ast list -> Ast.ast) =>
         AOT_map_translation true (n,f))
end

fun AOT_get_item_number name = let
val name = hd (String.fields (equal #"[") name)
val name = String.fields (equal #":") name
in case (AOT_item_by_name (hd name)) of (SOME id) => SOME (
fold (fn sub => fn str => str ^ "." ^ sub) (tl name) (Int.toString id)
) | _ => NONE end

fun AOT_print_item_number (name:string) = case (AOT_get_item_number name)
  of SOME str => Pretty.writeln (Pretty.str ("PLM item number (" ^ str ^ ")"))
  | _ => ()

fun add_AOT_print_rule AOTsyntax raw_rules thy = let
  val rules = map (fn (r, s) => let
    val head = Ast.head_of_rule (s,r)
  in (head, fn ctxt => fn asts =>
    if Config.get ctxt print_AOT_syntax = AOTsyntax then 
      let
        val orig = (Ast.mk_appl (Ast.Constant head) asts)
        val normalized = Ast.normalize ctxt
          (fn head' => if head = head' then [(s,r)] else []) orig
      in
        if orig = normalized then raise Match else normalized
      end
    else raise Match)
  end) raw_rules
in Sign.print_ast_translation rules thy end

local
         
val trans_pat =
  Scan.optional
    (\<^keyword>\<open>(\<close>
      |-- Parse.!!! (Parse.inner_syntax Parse.name --|
     \<^keyword>\<open>)\<close>)) "logic"
    -- Parse.inner_syntax Parse.string;

fun trans_arrow toks =
  ((\<^keyword>\<open>\<leftharpoondown>\<close> || \<^keyword>\<open><=\<close>)
    >> K Syntax.Print_Rule) toks;

val trans_line =
  trans_pat -- Parse.!!! (trans_arrow |-- trans_pat)
    >> (fn (left, right) => (left, right));

fun add_trans_rule AOTsyntax raw_rules thy =
let
  fun mapPair f (x, y) = (f x, f y)
  val ctxt = Proof_Context.init_global thy;
  val read_root = #1 o dest_Type o
    Proof_Context.read_type_name {proper = true, strict = false} ctxt;
  val raw_rules = map (mapPair (fn (r, s) =>
    (Syntax_Phases.parse_ast_pattern ctxt (read_root r, s)))) raw_rules
in add_AOT_print_rule AOTsyntax raw_rules thy end

val _ =
  Outer_Syntax.command
    \<^command_keyword>\<open>AOT_syntax_print_translations\<close>
    "add print translation rules for AOT syntax"
    (Scan.repeat1 trans_line >> (Toplevel.theory o add_trans_rule true));

val _ =
  Outer_Syntax.command
    \<^command_keyword>\<open>AOT_no_syntax_print_translations\<close>
    "add AOT print translation rules for non-AOT syntax"
    (Scan.repeat1 trans_line >> (Toplevel.theory o add_trans_rule false));
in end



structure AOT_Theorems = Named_Thms(
  val name = @{binding "AOT"}
  val description = "AOT Theorems"
)
structure AOT_Definitions = Named_Thms(
  val name = @{binding "AOT_defs"}
  val description = "AOT Definitions"
)
structure AOT_ProofData = Proof_Data
(type T = term option
 fun init _ = NONE)
fun AOT_note_theorems thms = Local_Theory.background_theory
  (Context.theory_map (fold AOT_Theorems.add_thm
    (map Drule.export_without_context (flat thms))))
fun AOT_note_definitions thms = Local_Theory.background_theory
  (Context.theory_map (fold AOT_Definitions.add_thm
    (map Drule.export_without_context (flat thms))))

structure AOT_DefinedConstants = Theory_Data (
  type T = Termtab.set
  val empty = Termtab.empty
  val extend = I
  val merge = Termtab.merge (K true)
);
fun AOT_note_defined_constant const =
  Local_Theory.background_theory (AOT_DefinedConstants.map (Termtab.insert_set const))

fun AOT_read_prop nonterminal ctxt prop = (let
    val ctxt' = Config.put Syntax.root nonterminal ctxt
    val trm = Syntax.parse_term ctxt' prop
    val typ = Term.fastype_of (Syntax.check_term ctxt' trm)
    val trm = if typ = @{typ prop} then trm else HOLogic.mk_Trueprop trm
  in trm end)
fun AOT_read_term nonterminal ctxt prop = (let
    val ctxt' = Config.put Syntax.root nonterminal ctxt
    val trm = Syntax.parse_term ctxt' prop
  in trm end)
fun AOT_check_prop nonterminal ctxt prop =
  AOT_read_prop nonterminal ctxt prop |> Syntax.check_prop ctxt;

let
fun close_form t =
  fold_rev (fn (s, T) => fn t => HOLogic.mk_all (s, T, t)) (Term.add_frees t []) t
fun remove_case_prod (Const (\<^const_name>\<open>case_prod\<close>, _) $ x) = remove_case_prod x
  | remove_case_prod (Const (\<^const_name>\<open>case_unit\<close>, _) $ x) = remove_case_prod x
  | remove_case_prod (Abs (a,b,c)) = Abs (a,b,remove_case_prod c)
  | remove_case_prod x = x

fun AOT_define_id (bnd,str,mx) (lhs,rhs,trm) ctxt =
let
  val bnd_str = Binding.name_of bnd
  val syn_typ = Syntax.parse_typ ctxt str

  val lhs = remove_case_prod lhs
  val rhs = remove_case_prod rhs

  fun filter (name,_) = not (name = \<^const_name>\<open>case_prod\<close>
      orelse name = \<^const_name>\<open>case_unit\<close>)
  val (const_name, const_typ) = case (List.filter filter (Term.add_consts lhs []))
    of [const] => const
    | _ => raise Term.TERM
      ("Expected a single constant on the LHS of the definition.", [lhs])

  val _ = Long_Name.base_name const_name = Long_Name.base_name bnd_str
    orelse raise Term.TERM ("Left-hand side does not contain the definiens.", [lhs])

  val (lhs_abs_vars, _) = Term.strip_abs lhs
  val (rhs_abs_vars, rhs_abs_body) = Term.strip_abs rhs
  val _ = lhs_abs_vars = rhs_abs_vars orelse raise Term.TERM
    ("Expected the LHS and RHS to abstract over the same free variables.", [lhs, rhs])
  val body = rhs_abs_body

  val witness = fold_rev (fn (s, T) => fn t => Term.absfree (s, T) t)
    lhs_abs_vars body
  val witness = Syntax.check_term ctxt witness

  (* Construct the choice specification theorem. *)
  val thm =
    let
      val cname = Long_Name.base_name const_name
      val vname = if Symbol_Pos.is_identifier cname then cname else "x"
      val trm = @{const Trueprop} $ HOLogic.mk_exists (vname, const_typ,
          Term.abstract_over (Const (const_name, const_typ), trm))
      val cwitness = Thm.cterm_of ctxt witness
      val witness_exI = Thm.instantiate'
        [SOME (Thm.ctyp_of_cterm cwitness)]
        [NONE,SOME cwitness] exI
      val simps = [
        @{thm AOT_model_id_def},
        @{thm AOT_model_nondenoing},
        @{thm AOT_model_denotes_prod_def},
        @{thm AOT_model_denotes_unit_def},
        @{thm case_unit_Unity}
      ]
      val thm = (Goal.prove ctxt [] [] trm (fn _ =>
        resolve_tac ctxt [witness_exI] 1
        THEN simp_tac (ctxt addsimps simps) 1))
      val match = Thm.match (Thm.cprop_of thm, Thm.cterm_of ctxt trm)
    in Drule.instantiate_normalize match thm end

  (* Add the choice specification and cleanup and export the resulting theorem. *)
  val oldctxt = ctxt
  val (thm, ctxt) = Local_Theory.background_theory_result (fn lthy => let
     val lthy = lthy |> Sign.add_consts [(bnd,const_typ,Mixfix.NoSyn)] |>
        Sign.syntax true Syntax.mode_default [(bnd_str,syn_typ,mx)] |>
        add_AOT_print_rule true [
          (Ast.Constant bnd_str, Ast.Constant (Lexicon.mark_const const_name))
        ]
     in
      Choice_Specification.add_specification [("",bnd_str,false)] (lthy, thm)
      |> apsnd Drule.export_without_context |> swap
     end) (Proof_Context.concealed ctxt)
in
  (ctxt |> Proof_Context.restore_naming oldctxt, thm)
end

fun AOT_define_equiv (bnd,str,mx) (lhs,rhs,trm) ctxt =
let
  val bnd_str = Binding.name_of bnd
  val syn_typ = Syntax.parse_typ ctxt str
  val (const_name, const_typ) = case (Term.add_consts lhs []) of [const] => const
    | _ => raise Term.TERM
      ("Expected a single constant on the LHS of the definition.", [lhs])
  
  (* TODO: figure out how to properly compare the constant name with the binding *)
  val _ = Long_Name.base_name const_name = Long_Name.base_name bnd_str
    orelse raise Term.TERM ("Left-hand side does not contain the definiens.", [lhs])
  
  (* Construct a witness for the choice specification theorem. *)
  val frees = Term.add_frees trm []
  val witness = let
    val w = case Term.variant_frees trm [("w", @{typ w})] of [w] => w
                | _ => raise Fail "Unexpected."
  in
    \<^const>\<open>AOT_model_proposition_choice\<close> $
    Term.absfree w (\<^const>\<open>AOT_model_valid_in\<close> $ Free w $ rhs)
  end
  val witness = fold_rev (fn (s, T) => fn t => Term.absfree (s, T) t)
    (List.rev frees) witness
  
  (* Construct the choice specification theorem. *)
  val thm =
  let
    val cname = Long_Name.base_name const_name
    val vname = if Symbol_Pos.is_identifier cname then cname else "x"
    val trm = @{const Trueprop} $ HOLogic.mk_exists (vname, const_typ,
        Term.abstract_over (Const (const_name, const_typ), close_form trm))
    val cwitness = Thm.cterm_of ctxt witness
    val witness_exI = Thm.instantiate'
      [SOME (Thm.ctyp_of_cterm cwitness)]
      [NONE,SOME cwitness] exI
    val simps = [
      @{thm AOT_model_equiv_def},
      @{thm AOT_model_proposition_choice_simp}
    ]
    val thm = (Goal.prove ctxt [] [] trm (fn _ =>
      resolve_tac ctxt [witness_exI] 1
      THEN simp_tac (ctxt addsimps simps) 1))
    val match = Thm.match (Thm.cprop_of thm, Thm.cterm_of ctxt trm)
  in
    Drule.instantiate_normalize match thm
  end
  
  (* Add the choice specification and cleanup and export the resulting theorem. *)
  val oldctxt = ctxt
  val (thm, ctxt) = Proof_Context.concealed ctxt |>
    Local_Theory.background_theory_result (fn lthy => let
     fun inst_all thy (name,typ) thm =
       let
         val cv = Thm.global_cterm_of thy (Free (name,typ))
         val cT = Thm.global_ctyp_of thy typ
         val spec' = Thm.instantiate' [SOME cT] [NONE, SOME cv] spec
       in thm RS spec' end
     fun remove_alls frees (thy, thm) = (thy, fold (inst_all thy) frees thm)
     val lthy = lthy |> Sign.add_consts [(bnd,const_typ,Mixfix.NoSyn)] |>
        Sign.syntax true Syntax.mode_default [(bnd_str,syn_typ,mx)] |>
        add_AOT_print_rule true [
          (Ast.Constant bnd_str, Ast.Constant (Lexicon.mark_const const_name))
        ]
     in
      Choice_Specification.add_specification [("",bnd_str,false)] (lthy, thm)
      |> remove_alls frees |> apsnd Drule.export_without_context |> swap
     end)
in
  (ctxt |> Proof_Context.restore_naming oldctxt, thm)
end

fun AOT_define (((bnd,str,mx),(thmbind,thmattrs)),defprop) ctxt =
  let
    val bnd_str = Binding.name_of bnd
    val syn_typ = Syntax.parse_typ ctxt str

    (* Add a generic constant and the requested syntax to a temporary context. *)
    val thy = Proof_Context.theory_of ctxt
    val thy' = Sign.add_consts [(bnd, @{typ 'a}, Mixfix.NoSyn)] thy
    val thy' = Sign.syntax true Syntax.mode_default [(bnd_str,syn_typ,mx)] thy'
    (* Try to parse the definition using the temporary context. *)
    val trm = AOT_check_prop @{nonterminal AOT_prop}
      (Proof_Context.init_global thy') defprop
    (* Extract lhs, rhs and the full definition from the parsed proposition
       and delegate. *)
    val (ctxt, thm) = case trm of (Const (\<^const_name>\<open>HOL.Trueprop\<close>, _) $ 
      (trm as Const (n, _) $ lhs $ rhs)) => 
          if n = \<^const_name>\<open>AOT_model_equiv_def\<close> then
            AOT_define_equiv (bnd,str,mx) (lhs,rhs,trm) ctxt
          else if n = \<^const_name>\<open>AOT_model_id_def\<close> then
            AOT_define_id (bnd,str,mx) (lhs,rhs,trm) ctxt
          else
            raise Term.TERM ("Expected AOT definition.", [trm])
      | _ => raise Term.TERM ("Expected AOT definition.", [trm])
    val thmbind = if Binding.is_empty thmbind then bnd else thmbind
    val _ = AOT_print_item_number (Binding.name_of thmbind)
  in
    ctxt |> Local_Theory.note ((thmbind, thmattrs), [thm]) |> snd |>
    AOT_note_theorems [[thm]] |> AOT_note_definitions [[thm]] |>
    AOT_note_defined_constant
      (Proof_Context.read_const {proper=true,strict=true} ctxt (Binding.name_of bnd))
  end
in
Outer_Syntax.local_theory
@{command_keyword AOT_define}
"AOT definition by equivalence."
(Parse.const_binding -- Parse_Spec.opt_thm_name ":" -- Parse.prop >> AOT_define)
end;

(* this is a stripped down version of Expression.read_statement
   that mainly replaces Syntax.parse_prop with AOT_read_prop
   and drops locale includes *)
local

fun mk_type T = (Logic.mk_type T, []);
fun mk_propp (p, pats) = (Type.constraint propT p, pats);

fun dest_type (T, []) = Logic.dest_type T
  | dest_type _ = raise Fail "Unexpected."
fun dest_propp (p, pats) = (p, pats);

fun finish_fixes (parms: (string * typ) list) = map (fn (binding, _, mx) =>
  let val x = Binding.name_of binding
  in (binding, AList.lookup (op =) parms x, mx) end);

fun finish_elem parms (Element.Fixes fixes) = Element.Fixes (finish_fixes parms fixes)
  | finish_elem _ (Element.Constrains _) = Element.Constrains []
  | finish_elem _ (Element.Assumes asms) = Element.Assumes asms
  | finish_elem _ (Element.Defines defs) = Element.Defines defs
  | finish_elem _ (elem as Element.Notes _) = elem
  | finish_elem _ (elem as Element.Lazy_Notes _) = elem;

fun extract_elem (Element.Fixes fixes) = map (#2 #> the_list #> map mk_type) fixes
  | extract_elem (Element.Constrains csts) = map (#2 #> single #> map mk_type) csts
  | extract_elem (Element.Assumes asms) = map (#2 #> map mk_propp) asms
  | extract_elem (Element.Defines defs) =
      map (fn (_, (t, ps)) => [mk_propp (t, ps)]) defs
  | extract_elem (Element.Notes _) = []
  | extract_elem (Element.Lazy_Notes _) = [];

fun restore_elem (Element.Fixes fixes, css) =
      (fixes ~~ css) |> map (fn ((x, _, mx), cs) =>
        (x, cs |> map dest_type |> try hd, mx)) |> Element.Fixes
  | restore_elem (Element.Constrains csts, css) =
      (csts ~~ css) |> map (fn ((x, _), cs) =>
        (x, cs |> map dest_type |> hd)) |> Element.Constrains
  | restore_elem (Element.Assumes asms, css) =
      (asms ~~ css) |> map (fn ((b, _), cs) =>
         (b, map dest_propp cs)) |> Element.Assumes
  | restore_elem (Element.Defines defs, css) =
      (defs ~~ css) |> map (fn ((b, _), [c]) =>
          (b, dest_propp c) | _ => raise Fail "Unexpected") |> Element.Defines
  | restore_elem (elem as Element.Notes _, _) = elem
  | restore_elem (elem as Element.Lazy_Notes _, _) = elem;

fun prep (_, pats) (ctxt, t :: ts) =
  let
    val ctxt' = Proof_Context.augment t ctxt
  in
    ((t, Syntax.check_props
            (Proof_Context.set_mode Proof_Context.mode_pattern ctxt') pats),
      (ctxt', ts))
  end
  | prep _ _ = raise Fail "Unexpected"

fun check cs ctxt =
  let
    val (cs', (ctxt', _)) = fold_map prep cs
      (ctxt, Syntax.check_terms
        (Proof_Context.set_mode Proof_Context.mode_schematic ctxt) (map fst cs));
  in (cs', ctxt') end;

fun check_autofix elems concl ctxt =
  let
    val elem_css = map extract_elem elems;
    val concl_cs = (map o map) mk_propp (map snd concl);
    (* Type inference *)
    val (css', ctxt') =
      (fold_burrow o fold_burrow) check (elem_css @ [concl_cs]) ctxt;
    val (elem_css', concl_cs') = chop (length elem_css) css' |> apsnd the_single;
  in
    ((map restore_elem (elems ~~ elem_css'),
      map fst concl ~~ concl_cs'), ctxt')
  end;

fun prepare_stmt prep_prop ctxt stmt =
  (case stmt of
    Element.Shows raw_shows =>
      raw_shows |> (map o apsnd o map) (fn (t, ps) =>
        (prep_prop (Proof_Context.set_mode Proof_Context.mode_schematic ctxt) t,
          map (prep_prop (Proof_Context.set_mode Proof_Context.mode_pattern ctxt)) ps))
  | Element.Obtains _ => raise Fail "unsupported");

fun parse_elem prep_typ prep_term ctxt =
  Element.map_ctxt
   {binding = I,
    typ = prep_typ ctxt,
    term = prep_term (Proof_Context.set_mode Proof_Context.mode_schematic ctxt),
    pattern = prep_term (Proof_Context.set_mode Proof_Context.mode_pattern ctxt),
    fact = I,
    attrib = I};

fun declare_elem prep_var (Element.Fixes fixes) ctxt =
      let val (vars, _) = fold_map prep_var fixes ctxt
      in ctxt |> Proof_Context.add_fixes vars |> snd end
  | declare_elem prep_var (Element.Constrains csts) ctxt =
      ctxt |> fold_map (fn (x, T) =>
        prep_var (Binding.name x, SOME T, NoSyn)) csts |> snd
  | declare_elem _ (Element.Assumes _) ctxt = ctxt
  | declare_elem _ (Element.Defines _) ctxt = ctxt
  | declare_elem _ (Element.Notes _) ctxt = ctxt
  | declare_elem _ (Element.Lazy_Notes _) ctxt = ctxt;

fun prep_full_context_statement
  parse_prop prop_root elem_root raw_elems raw_stmt ctxt1 =
  let

    fun prep_elem raw_elem ctxt =
      let
        val ctxt' = ctxt
          |> Context_Position.set_visible false
          |> declare_elem Proof_Context.read_var raw_elem
          |> Context_Position.restore_visible ctxt;
        val elems' = parse_elem Syntax.parse_typ (parse_prop elem_root) ctxt' raw_elem;
      in (elems', ctxt') end;

    val fors = fold_map Proof_Context.read_var [] ctxt1 |> fst;
    val ctxt2 = ctxt1 |> Proof_Context.add_fixes fors |> snd;
    val ctxt3 = ctxt2

    fun prep_stmt elems ctxt = check_autofix elems
      (prepare_stmt (parse_prop prop_root) ctxt raw_stmt) ctxt;

    val ((elems', concl), ctxt4) = ctxt3
      |> fold_map prep_elem raw_elems
      |-> prep_stmt;

    (* parameters from expression and elements *)

    val xs = maps (fn Element.Fixes fixes =>
      map (Variable.check_name o #1) fixes | _ => [])
      (Element.Fixes fors :: elems');
    val (parms, _) = fold_map Proof_Context.inferred_param xs ctxt4;

    val elems'' = map (finish_elem parms) elems';

  in (elems'', concl) end;
in

fun read_statement prop_root elem_root raw_elems raw_stmt ctxt =
  let
    val (elems, concl) = prep_full_context_statement
      AOT_read_prop prop_root elem_root raw_elems raw_stmt ctxt;
    val ctxt' = Proof_Context.set_stmt true ctxt
    val (elems, ctxt') = fold_map Element.activate elems ctxt'
    val _ = Proof_Context.restore_stmt ctxt ctxt'
  in (concl, elems, ctxt) end;

end

(* End of Expression.read_statement variant. *)

val long_keyword =
  Parse_Spec.includes >> K "" ||
  Parse_Spec.long_statement_keyword;

val long_statement =
  Scan.optional (Parse_Spec.opt_thm_name ":" --| Scan.ahead long_keyword)
    Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] --Parse_Spec.long_statement
    >> (fn ((binding, includes), (elems, concl)) =>
          (true, binding, includes, elems, concl))
val short_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
      (false, Binding.empty_atts, [], [Element.Fixes fixes, Element.Assumes assumes],
        Element.Shows shows))

fun setupStrictWorld ctxt = let
(* TODO: ideally not just a fixed name, but a variant name... *)
val (v,ctxt) = Proof_Context.add_fixes
  [(Binding.make ("ws", Position.none), SOME @{typ w}, Mixfix.NoSyn)] ctxt |>
  apfst the_single
in AOT_ProofData.put (SOME (Free (v, @{typ w}))) ctxt end
fun setupWeakWorld ctxt = AOT_ProofData.put (SOME @{const w\<^sub>0}) ctxt

fun mapStmt mapTerm _ (Element.Shows x) =
    Element.Shows (map (map (fn (trm, trms) =>
      (mapTerm trm, map mapTerm trms)) |> apsnd) x)
  | mapStmt mapTerm mapTyp (Element.Obtains x) =
    Element.Obtains (map ((fn (x, y) =>
      (map (fn (a,b,c) => (a, Option.map mapTyp b, c)) x, map mapTerm y)) |> apsnd) x)
fun mapCtxt mapTerm mapTyp ctxtElem = Element.map_ctxt
  {attrib = I, binding = I, fact = I, pattern = mapTerm, term = mapTerm, typ = mapTyp}
  ctxtElem

fun AOT_theorem_cmd axiom modallyStrict long afterQed thmBinding
  includes assumptions shows int ctxt =
  let
    val ctxt = Bundle.includes_cmd includes ctxt
    val ctxt = if modallyStrict then setupStrictWorld ctxt else setupWeakWorld ctxt
    val root = if axiom
      then (if modallyStrict
            then @{nonterminal "AOT_axiom"}
            else @{nonterminal "AOT_act_axiom"})
      else @{nonterminal AOT_prop}
    val (stmts,assumptions,ctxt) = read_statement
      root @{nonterminal AOT_prop} assumptions shows ctxt
    val _ = AOT_print_item_number (Binding.name_of (fst thmBinding))
    val _ = fold (fn ((bnd,_),_) => fn _ =>
      AOT_print_item_number (Binding.name_of bnd)) stmts ()
  in
    Specification.theorem long "AOT_theorem" NONE afterQed thmBinding []
      assumptions (Element.Shows stmts) int ctxt
  end

fun AOT_theorem spec note axiom modallyStrict descr =
  Outer_Syntax.local_theory_to_proof' spec ("state " ^ descr)
    ((long_statement || short_statement) >>
      (fn (long, binding, includes, elems, concl) =>
        (AOT_theorem_cmd axiom modallyStrict long
          (if note then AOT_note_theorems else K I) binding includes elems concl)));

val _ = AOT_theorem \<^command_keyword>\<open>AOT_lemma\<close> false false true
  "AOT modally-strict lemma";
val _ = AOT_theorem \<^command_keyword>\<open>AOT_theorem\<close> true false true
  "AOT modally-strict theorem";
val _ = AOT_theorem \<^command_keyword>\<open>AOT_act_lemma\<close> false false false
  "AOT modally-weak lemma";
val _ = AOT_theorem \<^command_keyword>\<open>AOT_act_theorem\<close> true false false
  "AOT modally-weak theorem"
val _ = AOT_theorem \<^command_keyword>\<open>AOT_axiom\<close> true true true
  "AOT modally-strict axiom";
val _ = AOT_theorem \<^command_keyword>\<open>AOT_act_axiom\<close> true true false
  "AOT modally-weak axiom"

local
val structured_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) => (fixes, assumes, shows));

fun prep_stmt (fixes, assumes, shows) ctxt = let
  val (concl, elems, _) = read_statement
    @{nonterminal AOT_prop} @{nonterminal AOT_prop}
    [Element.Fixes fixes, Element.Assumes assumes] (Element.Shows shows) ctxt
  val (fixes, assumes) =
    (fn ([Element.Fixes fixes, Element.Assumes assumes]) => (fixes, assumes)
      | _ => raise Fail "Unexpected.") elems
  fun mapAttr (a,[]) = (a,[])
    | mapAttr _ = raise Match (* Unimplemented *)
  val assumes = map (mapAttr |> apfst) assumes
  val concl = map (mapAttr |> apfst) concl
in (fixes, assumes, concl) end

fun gen_cmd kind stmt int state = let
    val (fixes, assumes, shows) = prep_stmt stmt (Proof.context_of state)
  in (kind true NONE (K I) fixes assumes shows int) state end
in
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_show\<close>
    "state local AOT goal, to refine pending subgoals"
    (structured_statement >> (fn stmt =>
      Toplevel.proof' (fn int => (gen_cmd Proof.show stmt int #> #2))));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_thus\<close> "alias of  \"then AOT_show\""
    (structured_statement >> (fn stmt =>
      Toplevel.proof' (fn int => Proof.chain #> (gen_cmd Proof.show stmt int #> #2))));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_have\<close> "state local AOT goal"
    (structured_statement >> (fn stmt =>
      Toplevel.proof' (fn int => (gen_cmd Proof.have stmt int #> #2))));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_hence\<close> "alias of  \"then AOT_have\""
    (structured_statement >> (fn stmt =>
      Toplevel.proof' (fn int => Proof.chain #> (gen_cmd Proof.have stmt int #> #2))));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_world\<close> "explicitly set world"
    (Parse.term >> (fn trm =>
       (Toplevel.proof' (fn _ => (Proof.map_context (fn ctxt => let
        val ctxt = AOT_ProofData.put (SOME (Syntax.read_term ctxt trm)) ctxt
        in ctxt end))))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_modally_strict {\<close>
    "begin explicit AOT modally-strict proof block"
    (Scan.succeed (Toplevel.proof (fn state => (Proof.map_context (fn ctxt => let
        val v = singleton (Variable.variant_frees ctxt []) ("ws", @{typ w}) |> fst
        val (_,ctxt) = Proof_Context.add_fixes
          [(Binding.make (v, Position.none), SOME @{typ w}, Mixfix.NoSyn)] ctxt
        val ctxt = AOT_ProofData.put (SOME (Free (v, @{typ w}))) ctxt
        in ctxt end) (Proof.begin_block state)))));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_actually {\<close>
    "begin explicit AOT modally-fragile proof block"
    (Scan.succeed (Toplevel.proof (fn state => (Proof.map_context (fn ctxt => let
        val ctxt = AOT_ProofData.put (SOME (@{const w\<^sub>0})) ctxt
        in ctxt end) (Proof.begin_block state)))));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_assume\<close> "assume AOT propositions"
    (structured_statement >> (fn stmt =>
      Toplevel.proof' (fn _ => fn state => (let
            val (fixes, assumes, shows) = prep_stmt stmt (Proof.context_of state)
        in Proof.assume fixes (map snd assumes) shows state end))));
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_obtain\<close> "generalized AOT elimination"
    (Parse.parbinding -- Scan.optional (Parse.vars --| Parse.where_) [] --
      structured_statement >> (fn ((a, b), stmt) => Toplevel.proof'
        (fn int => fn state => (let
          val ctxt = Proof.context_of state
          val b = map (fn (a,b,c) => (a,Option.map (Syntax.read_typ ctxt) b, c)) b
          val bnds = map (fn (a,_,_) => a) b
          val (_,ctxt) = Variable.add_fixes_binding bnds ctxt
          val (fixes, assumes, shows) = prep_stmt stmt ctxt
  in Obtain.obtain a b fixes (map snd assumes) shows int state end))));

end


val _ =
  Outer_Syntax.command \<^command_keyword>\<open>thm_name\<close> "print theorems"
    (Parse.thms1 >> (fn thms => Toplevel.keep (fn state => let
val ctxt = Toplevel.context_of state
val thms = Attrib.eval_thms ctxt thms
val trms = map Thm.full_prop_of thms
val result = maps (fn trm => let
val result = Find_Theorems.find_theorems ctxt NONE NONE true
  [(true, Find_Theorems.Pattern trm)] |> snd
val _ = (map (Pretty.writeln o Find_Theorems.pretty_thm ctxt) result)
in result end) trms
val strs = map (Long_Name.base_name o Facts.ref_name o fst) result
val _ = Pretty.writeln (Pretty.enum "" "" "" (map Pretty.str strs))
in () end)));

structure AOT_no_atp = Named_Thms(
  val name = @{binding "AOT_no_atp"}
  val description = "AOT Theorem Blacklist"
)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_sledgehammer\<close>
    "sledgehammer restricted to AOT abstraction layer"
    (Scan.succeed (Toplevel.keep_proof (fn state => let
val params = Sledgehammer_Commands.default_params (Toplevel.theory_of state) []
val ctxt = Toplevel.context_of state
fun all_facts_of ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val transfer = Global_Theory.transfer_theories thy;
    val global_facts = Global_Theory.facts_of thy;
  in
   (Facts.dest_all (Context.Proof ctxt) false [] global_facts
   |> maps Facts.selections
   |> map (apsnd transfer))
  end
val facts = all_facts_of ctxt
val add_facts = filter
  (fn fact => AOT_Theorems.member ctxt (snd fact)) facts |> map (fn (x,_) => (x,[]))
val del_facts = filter
  (fn fact => AOT_no_atp.member ctxt (snd fact)) facts |> map (fn (x,_) => (x,[]))
val ctxt = Toplevel.proof_of state
val _ = Sledgehammer.run_sledgehammer params Sledgehammer_Prover.Normal NONE 1
  {add = add_facts, del = del_facts, only = false} ctxt
in () end)))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_sledgehammer_only\<close>
    "sledgehammer restricted to AOT abstraction layer"
    (Scan.succeed (Toplevel.keep_proof (fn state => let
val params = Sledgehammer_Commands.default_params (Toplevel.theory_of state) []
val ctxt = Toplevel.context_of state
fun all_facts_of ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val transfer = Global_Theory.transfer_theories thy;
    val local_facts = Proof_Context.facts_of ctxt;
    val global_facts = Global_Theory.facts_of thy;
  in
   (Facts.dest_all (Context.Proof ctxt) false [global_facts] local_facts 
   |> maps Facts.selections
   |> map (apsnd transfer) |> map fst) @
   (Facts.dest_all (Context.Proof ctxt) false [] global_facts
   |> maps Facts.selections
   |> map (apsnd transfer)
   |> filter (AOT_Theorems.member ctxt o snd) |> map fst)
  end
val facts = all_facts_of ctxt
val result = map (fn x => (x,[])) facts
val ctxt = Toplevel.proof_of state
val _ = Sledgehammer.run_sledgehammer params Sledgehammer_Prover.Normal NONE 1
  {add = result, del = [], only = true} ctxt
in () end)))

local

fun readTermPattern ctxt str = (let
  val trm = case try (AOT_read_term @{nonterminal \<tau>'} ctxt) str of SOME x => x
            | NONE =>
              (case try (AOT_read_term @{nonterminal \<phi>'} ctxt) str of SOME x => x
               | NONE => (AOT_read_term @{nonterminal AOT_prop} ctxt) str)
  val trm = Syntax.check_term ctxt trm
  fun varifyTerm (Const (\<^const_name>\<open>AOT_term_of_var\<close>, Type ("fun", [_, t])) $
                  Free (x, _)) = Var ((x, 0), t)
    | varifyTerm (Free (x,t)) = Var ((x, 0), t)
    | varifyTerm (x $ y) = varifyTerm x $ varifyTerm y
    | varifyTerm (Abs (a, b, c)) = Abs(a, b, varifyTerm c)
    | varifyTerm z = z
  val trm = Term.map_types
    (Term.map_type_tfree (fn (str,sort) => TVar ((str, 0), sort))) trm
  val trm = varifyTerm trm
in trm end)

fun parseCriterion ctxt (Find_Theorems.Simp crit) =
    (Find_Theorems.Simp (readTermPattern ctxt crit))
  | parseCriterion ctxt (Find_Theorems.Pattern crit) =
    (Find_Theorems.Pattern (readTermPattern ctxt crit))
  | parseCriterion _ (Find_Theorems.Name x) = (Find_Theorems.Name x)
  | parseCriterion _ Find_Theorems.Intro = Find_Theorems.Intro
  | parseCriterion _ Find_Theorems.Elim = Find_Theorems.Elim
  | parseCriterion _ Find_Theorems.Dest = Find_Theorems.Dest
  | parseCriterion _ Find_Theorems.Solves = Find_Theorems.Solves


fun pretty_criterion ctxt (b, c) =
  let
    fun prfx s = if b then s else "-" ^ s;
  in
    (case c of
      Find_Theorems.Name name => Pretty.str (prfx "name: " ^ quote name)
    | Find_Theorems.Intro => Pretty.str (prfx "intro")
    | Find_Theorems.Elim => Pretty.str (prfx "elim")
    | Find_Theorems.Dest => Pretty.str (prfx "dest")
    | Find_Theorems.Solves => Pretty.str (prfx "solves")
    | Find_Theorems.Simp pat => Pretty.block [Pretty.str (prfx "simp:"), Pretty.brk 1,
        Pretty.quote (Syntax.pretty_term ctxt (Term.show_dummy_patterns pat))]
    | Find_Theorems.Pattern pat => Pretty.enclose (prfx "\"") "\""
        [Syntax.pretty_term ctxt (Term.show_dummy_patterns pat)])
  end;

datatype query = Criterion of (bool*string Find_Theorems.criterion) list |
                 Item of (int*string list)

fun pretty_theorems ctxt opt_lim rem_dups raw_spec =
let
  fun pretty_ref ctxt thmref =
    let
      val (name, sel) =
        (case thmref of
          Facts.Named ((name, _), sel) => (name, sel)
        | Facts.Fact _ => raise Fail "Illegal literal fact");
      val item = case
        AOT_get_item_number (Binding.name_of (Binding.qualified_name name))
        of SOME str => [Pretty.str ("("^str^")"), Pretty.str ":", Pretty.brk 1]
        | _ => []
    in
      item @ [Pretty.marks_str (#1 (Proof_Context.markup_extern_fact ctxt name), name),
        Pretty.str (Facts.string_of_selection sel), Pretty.str ":", Pretty.brk 1]
    end;
  fun tailToStr delim tail = (fold (fn field => fn str => str^delim^field) tail "")
  fun pretty_item (id, sub) = Pretty.str (
    "item: "^quote (Int.toString id^tailToStr "." sub)^
    " (name: "^quote ((the (AOT_name_of_item id))^tailToStr ":" sub)^")")
  fun pretty_thm ctxt (thmref, thm) =
    Pretty.block (pretty_ref ctxt thmref @ [Thm.pretty_thm ctxt thm])
  val (spec, prefix) = (case raw_spec of Item (item, tail) =>
      (case AOT_name_of_item item of SOME name =>
          let val fullName = name^tailToStr ":" tail
          in ([(true, Find_Theorems.Name fullName)], SOME fullName) end
          | _ => raise Fail "Unknown PLM item number.")
      | Criterion spec => (spec, NONE))
  val criteria = map (apsnd (parseCriterion ctxt)) spec
  val (opt_found, _) = Find_Theorems.find_theorems ctxt NONE (SOME 0) rem_dups criteria
  val (_, theorems) = Find_Theorems.find_theorems ctxt NONE opt_found rem_dups criteria
  val lim = the_default
    (Options.default_int \<^system_option>\<open>find_theorems_limit\<close>) opt_lim;
  val theorems = filter (fn (_,thm) => AOT_Theorems.member ctxt thm) theorems
  val theorems = case prefix of SOME prefix =>
    filter (fn (Facts.Named ((name, _), _), _) =>
      let val unqualified = (Binding.name_of (Binding.qualified_name name))
      in
      String.isPrefix prefix unqualified
      andalso (String.size unqualified <= String.size prefix orelse
        let
          val delim = String.sub (unqualified, String.size prefix)
        in delim = #":" orelse delim = #"[" end)
      end
      | _ => false) theorems
    | _ => theorems
  val found = length theorems
  val theorems = drop (Int.max (found - lim, 0)) theorems
  val returned = length theorems
    val tally_msg =
      (if found <= lim then "displaying " ^ string_of_int returned ^ " theorem(s)"
      else "found " ^ string_of_int found ^ " theorem(s)" ^
            (if returned < found
             then " (" ^ string_of_int returned ^ " displayed)"
             else ""));
    val position_markup = Position.markup (Position.thread_data ()) Markup.position;
  val pretty = Pretty.block
        (Pretty.fbreaks
          (Pretty.mark position_markup (Pretty.keyword1 "AOT_find_theorems") ::
            ((case raw_spec of Item (id, sub) =>
              [pretty_item (id, sub)] | _ => map (pretty_criterion ctxt) criteria)))) ::
    Pretty.str "" ::
    (if null theorems then [Pretty.str "found nothing"]
     else
       Pretty.str (tally_msg ^ ":") ::
       grouped 10 Par_List.map (Pretty.item o single o pretty_thm ctxt) (rev theorems))
in
  pretty |> Pretty.fbreaks |> curry Pretty.blk 0
end

val options =
  Scan.optional
    (Parse.$$$ "(" |--
      Parse.!!! (Scan.option Parse.nat --
        Scan.optional (Parse.reserved "with_dups" >> K false) true --| Parse.$$$ ")"))
    (NONE, true);

val item_parser = (Parse.nat >> (fn n => (n,[]))  || (Parse.string >> (
  fn str => let
    val fields = String.fields (equal #".") str
    val n = case (Int.fromString (hd fields)) of (SOME n) => n | _ => 0
    in (n, tl fields) end )))

val query_parser =
  ((Parse.reserved "item" |-- Parse.!!! (Parse.$$$ ":" |-- item_parser) >> Item) ||
  (Find_Theorems.query_parser >> Criterion))
  fun find_theorems ((opt_lim, rem_dups), spec) st =
     (Pretty.writeln
            (pretty_theorems (AOT_ProofData.put (SOME (Var (("ws", 0), @{typ w})))
                              (Proof.context_of (Find_Theorems.proof_state st)))
                             opt_lim rem_dups spec))
in
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>AOT_find_theorems\<close>
    "find theorems meeting specified criteria"
    (options -- query_parser >> (fn query =>
      Toplevel.keep (fn st => find_theorems query st)));

end

fun setup_AOT_no_atp thy = let
val all_facts_with_AOT_semantics =
  let
    val transfer = Global_Theory.transfer_theories thy;
    val global_facts = Global_Theory.facts_of thy;
  in
   (Facts.dest_all (Context.Theory thy) false [] global_facts
   |> maps Facts.selections
   |> map (apsnd transfer)
   |> filter (not o AOT_Theorems.member (Proof_Context.init_global thy) o snd))
  end
val all_facts_Main =
  let
    val transfer = Global_Theory.transfer_theories @{theory Main};
    val global_facts = Global_Theory.facts_of @{theory Main};
  in
   (Facts.dest_all (Context.Theory @{theory Main}) false [] global_facts
   |> maps Facts.selections
   |> map (apsnd transfer))
  end
val facts = filter
  (fn (elem,_) => not (List.exists (fn (elem',_) => elem = elem') all_facts_Main))
  all_facts_with_AOT_semantics
val thy = fold
  (fn fact => Context.theory_map (AOT_no_atp.add_thm fact))
  (map snd facts) thy
in thy end
