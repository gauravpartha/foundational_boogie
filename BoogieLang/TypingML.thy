theory TypingML                                      
  imports TypingHelper HelperML
begin               

ML \<open>

fun binop_mono_tac ctxt lookup_assms func_assms =
  FIRST' [  
  resolve_tac ctxt [@{thm TypVar}] THEN' (assm_full_simp_solved_tac (ctxt addsimps lookup_assms)),
  resolve_tac ctxt [@{thm TypBVar}] THEN' assm_full_simp_solved_tac ctxt,
  resolve_tac ctxt [@{thm TypPrim}] THEN' assm_full_simp_solved_tac ctxt,
  resolve_tac ctxt [@{thm TypUnOp}],
  resolve_tac ctxt [@{thm TypBinOpMono}] THEN' assm_full_simp_solved_tac ctxt,
  resolve_tac ctxt [@{thm typ_funexp_helper}] THEN' (assm_full_simp_solved_tac (ctxt addsimps func_assms)) THEN'
    assm_full_simp_solved_tac ctxt THEN' assm_full_simp_solved_tac ctxt THEN' 
    (* goal: \<tau> = (msubstT_opt ty_params ret_ty) *)
    asm_full_simp_tac (ctxt addsimps [@{thm msubstT_opt_def}]) THEN'
  (* before this final tactic the goal is of the form \<open>map (msubstT_opt ty_params) args_ty\<close>, which we want to simplify fully *)
    asm_full_simp_tac (ctxt addsimps [@{thm msubstT_opt_def}]),
  resolve_tac ctxt [@{thm TypOld}],
  resolve_tac ctxt [@{thm TypForall}],
  resolve_tac ctxt [@{thm TypExists}],
  resolve_tac ctxt [@{thm TypForallT}],
  resolve_tac ctxt [@{thm TypExistsT}],
  resolve_tac ctxt [@{thm TypListNil}],
  resolve_tac ctxt [@{thm TypListCons}]
  ]

fun binop_poly_tac ctxt hint_thm =  
  resolve_tac ctxt ([@{thm typ_binop_poly_helper} OF [hint_thm]]) THEN'
  assm_full_simp_solved_tac ctxt

fun binop_poly_tac_no_hint ctxt =  
  resolve_tac ctxt ([@{thm typ_binop_poly_helper_empty}]) THEN'
  assm_full_simp_solved_tac ctxt

(*
hint_thms must provide the type substitutions as theorems (see TypingHelper.thy)
for the equality operators, where the order is given from left to right.

simulate_determ_tac is used to check whether a tactic succeeds (in which case typing_tac continues).
Note that this tactic does not track how many subgoals were generated and still need to be solved from
the initial subgoal. As a result, it is possible that the tactic solves a goal that was generated
from the original subgoal. We might want to adjust that.
*)
fun typing_tac ctxt hint_thms lookup_assms func_assms i st =  
let val simp_solve_continue = 
   (case simulate_determ_tac (assm_full_simp_solved_tac (ctxt addsimps [@{thm msubstT_opt_def}]) i) st of
      NONE => Seq.single st
    | SOME st' => typing_tac ctxt hint_thms lookup_assms func_assms i st'
   )
in
  (case simulate_determ_tac (binop_mono_tac ctxt lookup_assms func_assms i) st of
    NONE => 
      (case hint_thms of
         [] => simp_solve_continue
       | (hint :: hint_rest) => 
         (case simulate_determ_tac (binop_poly_tac ctxt hint i) st of
            NONE => simp_solve_continue
          | SOME st' => typing_tac ctxt hint_rest lookup_assms func_assms i st'))
   | SOME st' => typing_tac ctxt hint_thms lookup_assms func_assms i st'
  )
end

(* The following tactic is the same as typing_tac except where no hints are used for polymorphic 
   binary operators (i.e., equality and inequality). This is useful in cases where the identity 
   substitution is sufficient to type polymorphic binary operators. *)
fun typing_tac_no_hints ctxt lookup_assms func_assms i st =  
let val simp_solve_continue = 
   (case simulate_determ_tac (assm_full_simp_solved_tac (ctxt addsimps [@{thm msubstT_opt_def}]) i) st of
      NONE => Seq.single st
    | SOME st' => typing_tac_no_hints ctxt lookup_assms func_assms i st'
   )
in
  (case simulate_determ_tac (binop_mono_tac ctxt lookup_assms func_assms i) st of
    NONE => 
      (case simulate_determ_tac (binop_poly_tac_no_hint ctxt i) st of
            NONE => simp_solve_continue
          | SOME st' => typing_tac_no_hints ctxt  lookup_assms func_assms i st')
   | SOME st' => typing_tac_no_hints ctxt lookup_assms func_assms i st'
  )
end
\<close>

end