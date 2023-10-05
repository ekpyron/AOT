theory ExportInfo
  imports AOT_misc
begin

local_setup\<open>fn ctxt =>
let
val thmToItems : (Symtab.set) Thmtab.table = Thmtab.empty
val thy = Proof_Context.theory_of ctxt
val global_facts = Global_Theory.facts_of thy;

val thmToItems = (Facts.dest_all (Context.Proof ctxt) false [] global_facts |>
  filter (fn (n, thms) => List.all (AOT_Theorems.member ctxt) thms andalso
    (Option.isSome (AOT_get_item_number (Binding.name_of (Binding.qualified_name n)))))
  |> fold (fn (n, thms) => fn thmtab => let
    val name = Binding.name_of (Binding.qualified_name n)
    val item = the (AOT_get_item_number name)
    val thmtab = fold (fn thm => fn thmtab => let
      in Thmtab.map_default (thm, Symtab.empty) (Symtab.insert_set item) thmtab end) thms thmtab
  in
    thmtab
  end)) Thmtab.empty

val thy = Proof_Context.theory_of ctxt
fun get_aot_facts ctxt =
let
val global_facts = Global_Theory.facts_of thy;
in
Facts.dest_all (Context.Proof ctxt) false [] global_facts |>
  map (fn (n, thms) => let
    val {theory_long_name = thy_name, pos = pos, ...} =
      Name_Space.the_entry (Facts.space_of global_facts) n
    val name = Binding.name_of (Binding.qualified_name n)
    val items = Symtab.keys (fold (fn thm => fn set =>
        case Thmtab.lookup thmToItems thm of SOME set' => Symtab.merge (op=) (set,set')
        | _ => set) thms Symtab.empty)
    val items = if name = "AOT" orelse name = "AOT_defs" then [] else items
  in
    (Binding.name_of (Binding.qualified_name thy_name), name, items, pos)
  end) |> filter (fn (_, _, items,_) => length items > 0 andalso length items < 10)
end

val facts = get_aot_facts ctxt
val blob = XML.blob (maps (fn (thyname,key,items,pos) =>
  [thyname,"|",key,"|"]@[String.concatWith " " items]@["\n"]) facts)
val blob2 = XML.blob (maps (fn (thyname,key,items,pos) =>
  [thyname,"|",key,"|", case Position.line_of pos of SOME x => Int.toString(x) | _ => "NONE"]@["\n"]) facts)
in
(Export.export thy (Path.binding0 (Path.make ["info"])) blob;
 Export.export thy (Path.binding0 (Path.make ["info2"])) blob2; ctxt)
end
\<close>

end