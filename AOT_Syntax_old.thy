theory AOT_Syntax_old
  imports AOT_Axioms
  keywords "AOT_syntax" :: thy_decl
       and "AOT_no_syntax" :: thy_decl
       and "AOT_notation" :: thy_decl
       and "AOT_no_notation" :: thy_decl
begin


consts StringTest :: "\<o> \<Rightarrow> \<o>" ("\<guillemotleft>_\<guillemotright>")

nonterminal AOT_any
syntax
  "" :: "'a \<Rightarrow> AOT_any" ("_")

ML\<open>
val _ = @{const_syntax String.Literal}
structure Data = Theory_Data (
  type T = Syntax.syntax
  val empty = Sign.syn_of @{theory} (*Syntax.empty_syntax*)
  val extend = I
  val merge = Syntax.merge_syntax
)
\<close>

ML\<open>

fun AOT_gen_syntax add list ctxt = (
let
    fun prep (c, T, mx) = (c, (Syntax.read_typ ctxt T), mx)
      handle ERROR msg => cat_error msg ("in syntax declaration " ^ quote c);
in
  Local_Theory.background_theory (fn thy => Data.map (fn syn =>
    Syntax.update_const_gram add (Sign.logical_types thy) Syntax.mode_default (map prep list) syn
  ) thy) ctxt
end
)

fun AOT_gen_notation add args ctxt = 
let
fun const_syntax _ (Free (x, T), mx) = SOME ((x, T, mx))
  | const_syntax ctxt (Const (c, _), mx) =
      (case try (Consts.type_scheme (Proof_Context.consts_of ctxt)) c of
        SOME T => SOME ((Lexicon.mark_const c, T, mx))
      | NONE => NONE)
  | const_syntax _ _ = NONE;
    val args = map (apfst (Proof_Context.read_const {proper = false, strict = false} ctxt)) args
    val args = map (apfst (Assumption.export_term ctxt (Local_Theory.target_of ctxt))) args
    val args = map (apsnd Mixfix.reset_pos) args;
    val args = (map_filter (const_syntax ctxt) args)
in
  Local_Theory.background_theory (fn thy => Data.map (fn syn =>
    Syntax.update_const_gram add (Sign.logical_types thy) Syntax.mode_default args syn
  ) thy) ctxt
end

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>AOT_syntax\<close> "add AOT syntax"
    (Scan.repeat1 Parse.const_decl >> AOT_gen_syntax true);
val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>AOT_no_syntax\<close> "delete AOT syntax"
    (Scan.repeat1 Parse.const_decl >> AOT_gen_syntax false);

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>AOT_notation\<close> "add AOT notation"
    (Parse.and_list1 (Parse.const -- Parse.mixfix)
      >> (fn (args) => AOT_gen_notation true args))
val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>AOT_no_notation\<close> "delete AOT notation"
    (Parse.and_list1 (Parse.const -- Parse.mixfix)
      >> (fn (args) => AOT_gen_notation false args))
\<close>

ML\<open>
(** markup logical entities **)

fun markup_class ctxt c =
  [Name_Space.markup (Type.class_space (Proof_Context.tsig_of ctxt)) c];

fun markup_type ctxt c =
  [Name_Space.markup (Type.type_space (Proof_Context.tsig_of ctxt)) c];

fun markup_const ctxt c =
  [Name_Space.markup (Consts.space_of (Proof_Context.consts_of ctxt)) c];

fun markup_free ctxt x =
  Variable.markup ctxt x ::
  (if Variable.is_body ctxt orelse Variable.is_fixed ctxt x
   then [Variable.markup_fixed ctxt x]
   else []);

fun markup_var xi = [Markup.name (Term.string_of_vname xi) Markup.var];

fun markup_bound def ps (name, id) =
  let val entity = Markup.entity Markup.boundN name in
    Markup.bound ::
      map (fn pos => Markup.properties (Position.entity_properties_of def id pos) entity) ps
  end;

fun markup_entity ctxt c =
  (case Syntax.lookup_const (Proof_Context.syn_of ctxt) c of
    SOME "" => []
  | SOME b => markup_entity ctxt b
  | NONE => c |> Lexicon.unmark
     {case_class = markup_class ctxt,
      case_type = markup_type ctxt,
      case_const = markup_const ctxt,
      case_fixed = markup_free ctxt,
      case_default = K []});


fun parsetree_to_ast ctxt trf parsetree =
  let
    val reports = Unsynchronized.ref ([]: Position.report_text list);
    fun report pos = Position.store_reports reports [pos];
    val append_reports = Position.append_reports reports;

    fun trans a args =
      (case trf a of
        NONE => Ast.mk_appl (Ast.Constant a) args
      | SOME f => f ctxt args);

    fun asts_of_token tok =
      if Lexicon.valued_token tok
      then [Ast.Variable (Lexicon.str_of_token tok)]
      else [];

    fun ast_of_position tok =
      Ast.Variable (Term_Position.encode (Lexicon.pos_of_token tok));

    fun ast_of_dummy a tok =
      Ast.Appl [Ast.Constant "_constrain", Ast.Constant a, ast_of_position tok];

    fun asts_of_position c tok =
      [Ast.Appl [Ast.Constant c, ast_of (Parser.Tip tok), ast_of_position tok]]

    and asts_of (Parser.Node ("_class_name", [Parser.Tip tok])) =
          let
            val pos = Lexicon.pos_of_token tok;
            val (c, rs) = Proof_Context.check_class ctxt (Lexicon.str_of_token tok, pos);
            val _ = append_reports rs;
          in [Ast.Constant (Lexicon.mark_class c)] end
      | asts_of (Parser.Node ("_type_name", [Parser.Tip tok])) =
          let
            val pos = Lexicon.pos_of_token tok;
            val (Type (c, _), rs) =
              Proof_Context.check_type_name {proper = true, strict = false} ctxt
                (Lexicon.str_of_token tok, pos);
            val _ = append_reports rs;
          in [Ast.Constant (Lexicon.mark_type c)] end
      | asts_of (Parser.Node ("_position", [Parser.Tip tok])) = asts_of_position "_constrain" tok
      | asts_of (Parser.Node ("_position_sort", [Parser.Tip tok])) = asts_of_position "_ofsort" tok
      | asts_of (Parser.Node (a as "\<^const>Pure.dummy_pattern", [Parser.Tip tok])) =
          [ast_of_dummy a tok]
      | asts_of (Parser.Node (a as "_idtdummy", [Parser.Tip tok])) =
          [ast_of_dummy a tok]
      | asts_of (Parser.Node ("_idtypdummy", pts as [Parser.Tip tok, _, _])) =
          [Ast.Appl (Ast.Constant "_constrain" :: ast_of_dummy "_idtdummy" tok :: maps asts_of pts)]
      | asts_of (Parser.Node (a, pts)) =
          let
            val _ = pts |> List.app
              (fn Parser.Node _ => () | Parser.Tip tok =>
                if Lexicon.valued_token tok then ()
                else report (Lexicon.pos_of_token tok) (markup_entity ctxt) a);
          in [trans a (maps asts_of pts)] end
      | asts_of (Parser.Tip tok) = asts_of_token tok

    and ast_of pt =
      (case asts_of pt of
        [ast] => ast
      | asts => raise Ast.AST ("parsetree_to_ast: malformed parsetree", asts));

    val ast = Exn.interruptible_capture ast_of parsetree;
  in (! reports, ast) end;

\<close>


ML\<open>
fun AOT_explode l =
let
 fun translate ((x,l)::("\<^sub>",1)::(n,1)::tl) = translate ((x^"\<^sub>"^n,l+2)::tl)
   | translate ((x,l)::("'",1)::tl) = translate ((x^"'",l+1)::tl)
   | translate (x::tl) = x::translate tl
   | translate nil = nil
in
translate (map (fn x => (x,1)) (Symbol.explode l))
end

fun AOT_subpos pos start len =
let
  val {offset = offset, end_offset = _, line = line, props = props} = Position.dest pos
in
  Position.make {offset = offset + start, end_offset = offset + start + len, line = line, props = props}
end
fun AOT_makeConstrain (name,len) pos start = Ast.Appl [(Ast.Constant "_constrain"), Ast.Variable name, Ast.Variable (Term_Position.encode (AOT_subpos pos start len))]

fun AOT_makeArgs pos start (hd :: nil) = AOT_makeConstrain hd pos start
  | AOT_makeArgs pos start ((hd as (name,len)) :: tail) = Ast.Appl [(Ast.Constant "Pair"), AOT_makeArgs pos start [hd], AOT_makeArgs pos (start + len) tail]
  | AOT_makeArgs pos start nil = raise Fail "Empty exemplification or encoding arguments."

fun AOT_makeArgList (Ast.Appl [(Ast.Constant "_constrain"), Ast.Variable vars, Ast.Variable constrain]) =
let
      val syms = AOT_explode vars
      val pos = YXML.parse constrain
      val pos = (case (Term_Position.decode (YXML.string_of pos)) of SOME pos => pos | _ => raise Fail "expected position")
in
  AOT_makeArgs pos 0 syms
end

fun translate_AOT_constrain var constrain =
let
  val isExe = Symbol.is_ascii_upper (hd (Symbol.explode var))
in
  if isExe
  then SOME (
    let
      val syms = AOT_explode var
      val pos = YXML.parse constrain
      val pos = (case (Term_Position.decode (YXML.string_of pos)) of SOME pos => pos | _ => raise Fail "expected position")
    in
    Ast.Appl [Ast.Constant "AOT_exe",
            AOT_makeConstrain (hd syms) pos 0,
            AOT_makeArgs pos (#2 (hd syms)) (drop 1 syms)]
    end
  ) else NONE
end

fun translate_AOT_binder binder bound constrain matrix = 
let
  val syms = AOT_explode bound
  val pos = YXML.parse constrain
  val pos = (case (Term_Position.decode (YXML.string_of pos)) of SOME pos => pos | _ => raise Fail "expected position")
  fun makeAbs pos start (hd :: nil) = Ast.Appl [ binder , Ast.Appl [ Ast.Constant "_abs", AOT_makeConstrain hd pos start, matrix] ]
    | makeAbs pos start ((hd as (name,len)) :: tail) =
      Ast.Appl [binder, Ast.Appl [ Ast.Constant "_abs", AOT_makeConstrain hd pos start, makeAbs pos (start+len) tail]]
in
makeAbs pos 0 syms
end

fun translate_AOT_lambda bound constrain matrix = 
let
  val syms = AOT_explode bound
  val pos = YXML.parse constrain
  val pos = (case (Term_Position.decode (YXML.string_of pos)) of SOME pos => pos | _ => raise Fail "expected position")
  fun makeAbs pos start (hd :: nil) = Ast.Appl [ Ast.Constant "_abs", AOT_makeConstrain hd pos start, matrix]
    | makeAbs pos start ((hd as (name,len)) :: tail) =
      Ast.Appl [Ast.Constant @{const_syntax case_prod}, Ast.Appl [ Ast.Constant "_abs", AOT_makeConstrain hd pos start, makeAbs pos (start+len) tail]]
in
  Ast.Appl [Ast.Constant @{const_syntax AOT_lambda}, makeAbs pos 0 syms]
end
\<close>

parse_ast_translation\<open>
let
fun
    translate ctx (ast as (Ast.Appl [Ast.Constant "_String", Ast.Appl [Ast.Constant "_constrain", Ast.Variable x, Ast.Variable pos]])) = (
let
  val _ = (@{print} ("Translate: ", x))
  val (syntax, ctx) = Local_Theory.background_theory_result (fn thy => (Data.get thy, thy)) ctx
  val str = String.substring (x,2,size x - 4)
  val pos = (case (Term_Position.decode pos) of SOME pos => pos | _ => raise Fail "expected position")
  val root = @{nonterminal AOT_any}
  val {offset = offset, line = line, end_offset = end_offset, props = props} = Position.dest pos
  val newStart = Position.make {offset = offset + 2, line = line, end_offset = offset + 2 , props = props}
  val newEnd = Position.make {offset = end_offset - 4, line = line, end_offset = end_offset - 4, props = props}
  val source = (Input.source false str (Position.range (newStart,newEnd)))
  val symbolList = Input.source_explode source;
  val tokenList = Syntax.tokenize syntax false symbolList
  val _ = Context_Position.reports ctx (map Lexicon.report_of_token tokenList);
  val _ = (@{print} ("Tokens: ", tokenList))
  val tokenList = (filter Lexicon.is_proper tokenList)
  val parseTree = Syntax.parse syntax root tokenList
  val _ = (@{print} ("ParseTree: ", parseTree))
  val (test,ast_res) = parsetree_to_ast ctx (Syntax.parse_ast_translation syntax) (hd parseTree)
  val ast = (case (Exn.get_res ast_res) of SOME ast => ast | NONE => raise Fail "ast")
  val _ = (@{print} ("AST: ", ast))
  fun makeAbs bound start offset = ()
  fun translate_ast (Ast.Constant x) = Ast.Constant x
    | translate_ast (Ast.Variable x) = Ast.Variable x
    | translate_ast (ast as (Ast.Appl [Ast.Constant "_constrain", Ast.Variable x, Ast.Variable pos])) = 
        (case (translate_AOT_constrain x pos) of (SOME ast) => ast | _ => ast)
    | translate_ast (ast as (Ast.Appl [Ast.Constant "_AOT_ex", Ast.Appl [Ast.Constant "_constrain", Ast.Variable bound, Ast.Variable pos], b])) = (
        translate_AOT_binder (Ast.Constant @{const_syntax AOT_ex}) bound pos (translate_ast b)
    )
    | translate_ast (ast as (Ast.Appl [Ast.Constant "_AOT_all", Ast.Appl [Ast.Constant "_constrain", Ast.Variable bound, Ast.Variable pos], b])) = (
        translate_AOT_binder (Ast.Constant @{const_syntax AOT_all}) bound pos (translate_ast b)
    )
    | translate_ast (ast as (Ast.Appl [Ast.Appl [Ast.Constant "_AOT_lambda", Ast.Appl [Ast.Constant "_constrain", Ast.Variable bound, Ast.Variable pos], b], constr])) = (
      Ast.Appl [Ast.Constant "AOT_exe",
        translate_AOT_lambda bound pos (translate_ast b),
        AOT_makeArgList constr
      ]
    )
    | translate_ast (ast as (Ast.Appl [Ast.Constant "_AOT_lambda", Ast.Appl [Ast.Constant "_constrain", Ast.Variable bound, Ast.Variable pos], b])) = (
        translate_AOT_lambda bound pos (translate_ast b)
    )

    | translate_ast (Ast.Appl x) = Ast.Appl (map translate_ast x)
  val ast = translate_ast ast
  val _ = (@{print} ("TranslatedAST: ", ast))
in
  ast
end
    )
  | translate ctx (ast as (Ast.Constant x)) = (@{print} ("CONST",ast); ast)
  | translate ctx (ast as (Ast.Variable x)) = (@{print} ("VAR",ast); ast)
  | translate ctx (ast as (Ast.Appl x)) = (Ast.Appl (map (translate ctx) x))
in
  [(@{const_syntax StringTest}, (fn ctx => fn list => translate ctx (hd list) )),
   (@{const_syntax AOT_valid_in}, (fn ctx => fn list => Ast.Appl [Ast.Constant @{const_syntax AOT_valid_in}, translate ctx (hd list), translate ctx (hd (tl list)) ]))]
end
\<close>

AOT_no_notation HOL.implies (infixr "\<longrightarrow>" 25)
AOT_syntax AOT_imp :: "[\<o>, \<o>] \<Rightarrow> \<o>" (infixl "\<longrightarrow>" 8)
AOT_syntax AOT_imp :: "[\<o>, \<o>] \<Rightarrow> \<o>" (infixl "\<rightarrow>" 8)

AOT_no_notation HOL.Ex (binder "\<exists>" 10)
AOT_no_notation HOL.All (binder "\<forall>" 10)
term "\<^bold>\<exists> x . v x"
AOT_syntax "_AOT_ex" :: "'a \<Rightarrow> \<o> \<Rightarrow> \<o>" ("\<exists>_ _" 10)
AOT_syntax "_AOT_all" :: "'a \<Rightarrow> \<o> \<Rightarrow> \<o>" ("\<forall>_ _" 10)
AOT_syntax "_AOT_lambda" :: "'a \<Rightarrow> \<o> \<Rightarrow> \<o>" ("[\<lambda>_ _]")

consts AOT_any :: "'a \<Rightarrow> 'b"
syntax "AOT_any" :: "'a \<Rightarrow> \<o> \<Rightarrow> \<o>" ("[\<lambda>_ _]")

term "(V [\<lambda> abc x])"

lemma "d" oops


declare[[show_sorts]]
typ "'a \<times> 'b"
lemma "\<And> F\<^sub>1. [v \<Turnstile> ''(\<forall> x (F\<^sub>1xyw \<rightarrow> \<exists> z F\<^sub>1xyz \<rightarrow> Hxyz)) \<rightarrow> [\<lambda> abc  Gabc]abc'']"
  oops

end
