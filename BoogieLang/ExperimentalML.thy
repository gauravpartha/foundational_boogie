theory ExperimentalML
  imports Semantics Util VCHints
begin


ML\<open> (* taken from Cogent; add_simps adds simplification-rules into a given context. *)
fun add_simps [] ctxt = ctxt
 |  add_simps (thm::thms) ctxt = add_simps thms (Simplifier.add_simp thm ctxt)
\<close>

ML \<open>
fun b_reduce_expr_ml ctxt =
REPEAT o FIRST' [
eresolve_tac ctxt [@{thm RedBinOp_case}], 
eresolve_tac ctxt [@{thm RedFunOp_case}],
eresolve_tac ctxt [@{thm RedUnOp_case}], 
eresolve_tac ctxt [@{thm val_elim}],
eresolve_tac ctxt [@{thm cons_exp_elim2}],
eresolve_tac ctxt [@{thm RedVar_case}],
eresolve_tac ctxt [@{thm nil_exp_elim}]
]
\<close>

ML \<open>
fun b_prove_assert_expr_ml ctxt assms = 
REPEAT o FIRST' [
resolve_tac ctxt [@{thm RedVar}],
resolve_tac ctxt [@{thm RedVal}],
resolve_tac ctxt [@{thm RedBinOp}],
resolve_tac ctxt [@{thm RedUnOp}],
resolve_tac ctxt [@{thm RedFunOp}],
resolve_tac ctxt [@{thm RedExpListNil}],
resolve_tac ctxt [@{thm RedExpListCons}],
Clasimp.fast_force_tac (add_simps assms ctxt)
]
\<close>

ML \<open>
val test = make_elim (@{thm mp})
\<close>

(* b_assume_tac *)

ML \<open>
fun b_assume_base_tac inst_thm vc_elim ctxt global_assms i =
(resolve_tac ctxt [inst_thm] i) THEN
  (asm_full_simp_tac ctxt i) THEN
  (resolve_tac ctxt [vc_elim] i) THEN
  (b_reduce_expr_ml ctxt i) THEN
  (Clasimp.fast_force_tac (add_simps global_assms ctxt) i)

fun b_assume_foc_tac global_assms vc_elim i (focus: Subgoal.focus) =
let
  val (red :: vc :: _) = #prems(focus)
  val ctxt = #context(focus)
in
  (b_assume_base_tac (@{thm assume_ml} OF [red]) (vc_elim vc) ctxt global_assms i)
  handle THM _ => no_tac
end

fun apply_thm_n_times vc thm n =
 (if n <= 0 then vc else 
  (apply_thm_n_times (thm OF [vc]) thm (n-1))
 )
 

fun b_assume_simple_tac ctxt global_assms vc_elim =
  (Subgoal.FOCUS (b_assume_foc_tac global_assms vc_elim 1) ctxt 1) THEN
  eresolve0_tac [thin_rl] 1 THEN
  eresolve0_tac [thin_rl] 1 THEN
  eresolve0_tac [thin_rl] 1

fun b_assume_conjr_tac ctxt global_assms n =
  let val vc_elim = 
    fn (vc) => @{thm imp_conj_elim} OF [(apply_thm_n_times vc @{thm imp_conj_assoc} (n-1))]
  in
    (b_assume_simple_tac ctxt global_assms vc_elim)
  end
\<close>

(* assert_tac *)

ML \<open>
fun b_assert_base_tac inst_thm vc_expr ctxt global_assms i =
(resolve_tac ctxt [inst_thm] i) THEN
  (b_prove_assert_expr_ml ctxt (vc_expr@global_assms) i)

fun b_assert_foc_tac global_assms vc_elim i (focus: Subgoal.focus) =
let 
  val (red :: vc :: _) = #prems(focus)
  val ctxt = #context(focus)
in
 (b_assert_base_tac (@{thm assert_ml} OF [red]) [(@{thm conjunct1} OF [vc])] ctxt global_assms i) THEN
  (resolve_tac ctxt [(vc_elim OF [vc])] i)  
  handle THM _ => no_tac 
end

fun b_assert_tac ctxt global_assms vc_elim =
  (Subgoal.FOCUS (b_assert_foc_tac global_assms vc_elim 1) ctxt 1)  THEN
  eresolve0_tac [thin_rl] 1 THEN
  eresolve0_tac [thin_rl] 1

fun b_assert_no_conj_foc_tac global_assms i (focus: Subgoal.focus) =
let 
  val (red :: vc :: _) = #prems(focus) 
  val ctxt = #context(focus)
in
 (b_assert_base_tac (@{thm assert_ml} OF [red]) [vc] ctxt global_assms i)
  handle THM _ => no_tac 
end

fun b_assert_no_conj_tac ctxt global_assms =
  (SUBPROOF (b_assert_no_conj_foc_tac global_assms 1) ctxt 1) 
\<close>

ML \<open>
fun b_vc_hint_tac _ _ ([]: VcHint list) = all_tac
|  b_vc_hint_tac ctxt global_assms (x::xs) = 
  (case x of
    AssumeImplies => b_assume_simple_tac ctxt global_assms (fn (vc) => @{thm impE} OF [vc])
  | AssumeConj => b_assume_simple_tac ctxt global_assms (fn (vc) => @{thm imp_conj_elim} OF [vc])
  | AssumeConjR 0 => b_assume_simple_tac ctxt global_assms (fn (vc) => @{thm impE} OF [vc])
  | AssumeConjR n => 
     if n = 1 then
        b_assume_simple_tac ctxt global_assms (fn (vc) => @{thm imp_conj_elim} OF [vc])
     else
       b_assume_conjr_tac ctxt global_assms n
  | AssertNoConj => b_assert_no_conj_tac ctxt global_assms
  | AssertConj => b_assert_tac ctxt global_assms (@{thm conj_elim_2})
  | AssertSub => b_assert_tac ctxt global_assms (@{thm conj_imp_elim})
  ) THEN
   b_vc_hint_tac ctxt global_assms xs 
\<close>


ML \<open>
fun b_assert_foc_tac global_assms i (focus: Subgoal.focus) =
let 
  val (red :: vc :: _) = #prems(focus) 
  val ctxt = #context(focus)
  val inst_thm = @{thm assert_ml} OF [red]
in
 i |> 
 (
  resolve_tac ctxt [inst_thm] THEN'
  asm_full_simp_tac ctxt THEN'
  b_prove_assert_expr_ml ctxt (vc::global_assms)
 )
end
\<close>

ML \<open>
fun assert_tac ctxt global_assms =
  Subgoal.FOCUS (b_assert_foc_tac global_assms 1) ctxt 1
\<close>

end