theory TypingML                                      
  imports TypingHelper HelperML
begin               

ML \<open>
fun assm_full_simp_solved_tac ctxt = (asm_full_simp_tac ctxt |> SOLVED')

fun binop_mono_tac ctxt lookup_assms func_assms =
  FIRST' [
  resolve_tac ctxt [@{thm TypVar}] THEN' (assm_full_simp_solved_tac (ctxt addsimps lookup_assms)),
  resolve_tac ctxt [@{thm TypBVar}] THEN' assm_full_simp_solved_tac ctxt,
  resolve_tac ctxt [@{thm TypPrim}] THEN' assm_full_simp_solved_tac ctxt,
  resolve_tac ctxt [@{thm TypBinOpMono}] THEN' assm_full_simp_solved_tac ctxt,
  resolve_tac ctxt [@{thm typ_funexp_helper}] THEN' (assm_full_simp_solved_tac (ctxt addsimps func_assms)) THEN'
    assm_full_simp_solved_tac ctxt THEN' assm_full_simp_solved_tac ctxt THEN' assm_full_simp_solved_tac ctxt,
  resolve_tac ctxt [@{thm TypOld}],
  resolve_tac ctxt [@{thm TypForall}],
  resolve_tac ctxt [@{thm TypForallT}],
  resolve_tac ctxt [@{thm TypExistsT}],
  resolve_tac ctxt [@{thm TypListNil}],
  resolve_tac ctxt [@{thm TypListCons}]
  ]

fun binop_poly_tac ctxt hint_thm =  
  resolve_tac ctxt ([@{thm typ_binop_poly_helper} OF [hint_thm]]) THEN'
  assm_full_simp_solved_tac ctxt

fun simulate_tac tac st =
  (case Seq.pull (tac st) of
            NONE => NONE
          | SOME (st', _) => SOME st')

(*
hint_thms must provide the type substitutions as theorems (see TypingHelper.thy)
for the equality operators, where the order is given from left to right
*)
fun typing_tac ctxt hint_thms lookup_assms func_assms i st =  
let val simp_solve_continue = 
   (case simulate_tac (assm_full_simp_solved_tac (ctxt addsimps [@{thm msubstT_opt_def}]) i) st of
      NONE => Seq.single st
    | SOME st' => typing_tac ctxt hint_thms lookup_assms func_assms i st'
   )
in
  (case simulate_tac (binop_mono_tac ctxt lookup_assms func_assms i) st of
    NONE => 
      (case hint_thms of
         [] => simp_solve_continue
       | (hint :: hint_rest) => 
         (case simulate_tac (binop_poly_tac ctxt hint i) st of
            NONE => simp_solve_continue
          | SOME st' => typing_tac ctxt hint_rest lookup_assms func_assms i st'))
   | SOME st' => typing_tac ctxt hint_thms lookup_assms func_assms i st'
  )
end
\<close>

end