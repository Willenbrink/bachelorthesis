val term_pat_setup =
 let
   val parser = Args.context -- Scan.lift Args.embedded_inner_syntax
  
   fun term_pat (ctxt, str) =
   str |> Proof_Context.read_term_pattern ctxt
   |> ML_Syntax.print_term
   |> ML_Syntax.atomic
 in
 ML_Antiquotation.inline @{binding "term_pat"} (parser >> term_pat)
 end

val type_pat_setup =
  let
    val parser = Args.context -- Scan.lift Args.embedded_inner_syntax
    fun typ_pat (ctxt, str) =
    let val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
    in
      str
      |> Syntax.read_typ ctxt'
      |> ML_Syntax.print_typ
      |> ML_Syntax.atomic
    end
  in
  ML_Antiquotation.inline @{binding "typ_pat"} (parser >> typ_pat)
  end

local
  fun pp_pair (x, y) = Pretty.list "(" ")" [x, y]
  fun pp_list xs = Pretty.list "[" "]" xs
  fun pp_str s = Pretty.str s
  fun pp_qstr s = Pretty.quote (pp_str s)
  fun pp_int i = pp_str (string_of_int i)
  fun pp_sort S = pp_list (map pp_qstr S)
  fun pp_constr a args = Pretty.block [pp_str a, Pretty.brk 1, args]
in
  fun raw_pp_typ (TVar ((a, i), S)) =
        pp_constr "TVar" (pp_pair (pp_pair (pp_qstr a, pp_int i), pp_sort S))
    | raw_pp_typ (TFree (a, S)) =
        pp_constr "TFree" (pp_pair (pp_qstr a, pp_sort S))
    | raw_pp_typ (Type (a, tys)) =
        pp_constr "Type" (pp_pair (pp_qstr a, pp_list (map raw_pp_typ tys)))
end
