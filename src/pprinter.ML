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