theory Diagnostic
  imports Main
begin
ML \<open>
(* functions taken from Isabelle cookbook (https://nms.kcl.ac.uk/christian.urban/Cookbook/) *)

val pretty_term = Syntax.pretty_term
val pwriteln = Pretty.writeln
fun pretty_thm ctxt thm = pretty_term ctxt (Thm.prop_of thm)

fun pretty_thm_no_vars ctxt thm =
let
val ctxt' = Config.put show_question_marks false ctxt
in
pretty_term ctxt' (Thm.prop_of thm)
end

fun pretty_thms ctxt thms =
Pretty.block (Pretty.commas (map (pretty_thm ctxt) thms))
fun pretty_thms_no_vars ctxt thms =
Pretty.block (Pretty.commas (map (pretty_thm_no_vars ctxt) thms))

fun pretty_terms ctxt trms =
Pretty.block (Pretty.commas (map (pretty_term ctxt) trms))

fun pretty_cterm ctxt ctrm =
pretty_term ctxt (Thm.term_of ctrm)

fun pretty_cterms ctxt ctrms =
Pretty.block (Pretty.commas (map (pretty_cterm ctxt) ctrms))

fun timing_wrapper tac st = 
let
  val t_start = Timing.start ();
  val res = tac st;
  val t_end = Timing.result t_start;
in
  (writeln (Timing.message t_end); res)
end
\<close>
end