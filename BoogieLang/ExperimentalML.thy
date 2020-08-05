theory ExperimentalML
  imports Semantics Util VCHints VCExprHelper
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
fun b_prove_assert_expr_simple_tac ctxt assms = 
REPEAT o FIRST' [
resolve_tac ctxt [@{thm RedVar}],
resolve_tac ctxt [@{thm RedLit}],
resolve_tac ctxt [@{thm RedBinOp}],
resolve_tac ctxt [@{thm RedUnOp}],
resolve_tac ctxt [@{thm RedFunOp}],
resolve_tac ctxt [@{thm RedExpListNil}],
resolve_tac ctxt [@{thm RedExpListCons}],
Clasimp.fast_force_tac (add_simps assms ctxt)
]
\<close>

ML \<open>
fun vc_expr_rel_select_tac red_expr_tac ctxt assms del_thms (t,i) =
  case (Logic.strip_assums_concl t) of
    Const (@{const_name "HOL.eq"},_) $ _ $ _ => (asm_full_simp_tac (add_simps assms ctxt) |> SOLVED') i
   | @{term "Trueprop"} $ t' => vc_expr_rel_select_tac red_expr_tac ctxt assms del_thms (t',i)
   | _ => red_expr_tac ctxt assms del_thms i

fun b_prove_assert_expr_simple_tac_2 ctxt assms del_thms =
REPEAT_ALL_NEW (SUBGOAL (vc_expr_rel_select_tac 
(fn ctxt => fn assms => fn del_thms => FIRST' [
resolve_tac ctxt [@{thm RedVar}] THEN' (asm_full_simp_tac ((ctxt addsimps assms delsimps del_thms))),
resolve_tac ctxt [@{thm RedLit}],
resolve_tac ctxt [@{thm RedBinOp}],
resolve_tac ctxt [@{thm RedUnOp}],
resolve_tac ctxt [@{thm RedFunOp}] THEN' (asm_full_simp_tac (ctxt addsimps assms delsimps del_thms)),
resolve_tac ctxt [@{thm RedExpListNil}],
resolve_tac ctxt [@{thm RedExpListCons}]
]) ctxt assms del_thms)
)
\<close>

ML \<open>
fun vc_expr_rel_red_tac ctxt assms del_thms = 
 FIRST' [
resolve_tac ctxt [@{thm RedVar}] THEN' (asm_full_simp_tac (ctxt addsimps assms delsimps del_thms) |> SOLVED'),
resolve_tac ctxt [@{thm RedLit}],
resolve_tac ctxt [@{thm conj_vc_rel}],
resolve_tac ctxt [@{thm disj_vc_rel}],
resolve_tac ctxt [@{thm imp_vc_rel}],
resolve_tac ctxt [@{thm not_vc_rel}],
resolve_tac ctxt [@{thm forall_vc_rel_int}] THEN' simp_tac (ctxt delsimps (@{thms simp_thms} @ del_thms)),
resolve_tac ctxt [@{thm forall_vc_rel_bool}] THEN' simp_tac (ctxt delsimps (@{thms simp_thms} @ del_thms)),
resolve_tac ctxt [@{thm exists_vc_rel_int}] THEN' simp_tac (ctxt delsimps (@{thms simp_thms} @ del_thms)),
resolve_tac ctxt [@{thm exists_vc_rel_int}] THEN' simp_tac (ctxt delsimps (@{thms simp_thms} @ del_thms)),

(*
resolve_tac ctxt [@{thm add_vc_rel}],
resolve_tac ctxt [@{thm sub_vc_rel}],
resolve_tac ctxt [@{thm mul_vc_rel}],
resolve_tac ctxt [@{thm uminus_vc_rel}],
*)
resolve_tac ctxt [@{thm RedFunOp}] THEN' (asm_full_simp_tac (ctxt addsimps assms delsimps del_thms) |> SOLVED'),
resolve_tac ctxt [@{thm RedExpListNil}],
resolve_tac ctxt [@{thm RedExpListCons}],
CHANGED o b_prove_assert_expr_simple_tac_2 ctxt assms []
(*(b_prove_assert_expr_simple_tac ctxt assms |> SOLVED')*)
]

fun b_vc_expr_rel_tac ctxt assms del_thms =
  REPEAT o SUBGOAL (vc_expr_rel_select_tac vc_expr_rel_red_tac ctxt assms del_thms)
                                    

(* prove \<Gamma> \<turnstile> \<langle>e, ns\<rangle> \<Down> BoolV vc  *)
fun b_prove_assert_expr_tac vc_expr ctxt global_assms i =
(resolve_tac ctxt [@{thm vc_to_expr} OF vc_expr] i) THEN
(b_vc_expr_rel_tac ctxt global_assms [] i)
\<close>

ML \<open>
val test = make_elim (@{thm mp})
\<close>

(* b_assume_tac *)

ML \<open>
fun b_assume_base_tac_2 inst_thm vc_elim ctxt global_assms i =
(resolve_tac ctxt [inst_thm] i) THEN 
  (asm_full_simp_tac ctxt i) THEN
  (resolve_tac ctxt [vc_elim] i) THEN
  (resolve_tac ctxt [@{thm expr_to_vc}] i) THEN
  (assume_tac ctxt i) THEN
  (b_vc_expr_rel_tac ctxt global_assms [] i)

fun b_assume_base_tac inst_thm vc_elim ctxt global_assms i =
(resolve_tac ctxt [inst_thm] i) THEN
  (asm_full_simp_tac ctxt i) THEN
  (resolve_tac ctxt [vc_elim] i) THEN
  (b_reduce_expr_ml ctxt i) THEN
  (Clasimp.fast_force_tac (add_simps global_assms ctxt) i)

fun b_assume_foc_tac_2 global_assms vc_elim i (focus: Subgoal.focus) =
let
  val (red :: vc :: _) = #prems(focus)
  val ctxt = #context(focus)
in
  (b_assume_base_tac_2 (@{thm assume_ml} OF [red]) (vc_elim vc) ctxt global_assms i)
  handle THM _ => no_tac
end

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

fun remove_n_assms n i = 
 (if n <= 0 then all_tac else eresolve0_tac [thin_rl] i THEN remove_n_assms (n-1) i)

fun b_assume_simple_tac_2 ctxt global_assms vc_elim n_assms_rem =
  (Subgoal.FOCUS (b_assume_foc_tac_2 global_assms vc_elim 1) ctxt 1) THEN   
   remove_n_assms n_assms_rem 1

fun b_assume_simple_tac ctxt global_assms vc_elim n_assms_rem =
  (Subgoal.FOCUS (b_assume_foc_tac global_assms vc_elim 1) ctxt 1) THEN
  remove_n_assms n_assms_rem 1

fun b_assume_conjr_tac b_assume_tac ctxt global_assms n =
  let val vc_elim = 
    fn (vc) => @{thm imp_conj_elim} OF [(apply_thm_n_times vc @{thm imp_conj_imp} (n-1))]
  in
    (b_assume_tac ctxt global_assms vc_elim 3)
  end
\<close>

(* assert_tac *)

ML \<open>
fun b_assert_base_tac_2 inst_thm vc_expr ctxt global_assms i =
(resolve_tac ctxt [inst_thm] i) THEN
  (b_prove_assert_expr_tac vc_expr ctxt global_assms i)

fun b_assert_base_tac inst_thm vc_expr ctxt global_assms i =
(resolve_tac ctxt [inst_thm] i) THEN
  (b_prove_assert_expr_simple_tac ctxt (vc_expr@global_assms) i)

fun b_assert_foc_tac b_assert_base_tac global_assms vc_elim i (focus: Subgoal.focus) =
let 
  val (red :: vc :: _) = #prems(focus)
  val ctxt = #context(focus)
in
 (b_assert_base_tac (@{thm assert_ml} OF [red]) [(@{thm conjunct1} OF [vc])] ctxt global_assms i) THEN
  (resolve_tac ctxt [(vc_elim OF [vc])] i)  
  handle THM _ => no_tac 
end

fun b_assert_tac b_assert_base_tac ctxt global_assms vc_elim =
  (Subgoal.FOCUS (b_assert_foc_tac b_assert_base_tac global_assms vc_elim 1) ctxt 1)  THEN
  eresolve0_tac [thin_rl] 1 THEN
  eresolve0_tac [thin_rl] 1

fun b_assert_no_conj_foc_tac b_assert_base_tac global_assms i (focus: Subgoal.focus) =
let 
  val (red :: vc :: _) = #prems(focus) 
  val ctxt = #context(focus)
in
 (b_assert_base_tac (@{thm assert_ml} OF [red]) [vc] ctxt global_assms i)
  handle THM _ => no_tac 
end

fun b_assert_no_conj_tac b_assert_tac ctxt global_assms =
  (Subgoal.FOCUS (b_assert_no_conj_foc_tac b_assert_tac global_assms 1) ctxt 1)
\<close>

ML \<open>
fun b_vc_hint_tac _ _ ctxt _ ([]: VcHint list) = 
  TRY (eresolve_tac ctxt [@{thm nil_cmd_elim}] 1 THEN asm_full_simp_tac ctxt 1)
| b_vc_hint_tac b_assume_tac b_assert_base_tac ctxt global_assms (x::xs) = 
  (case x of
    AssumeConjR 0 => b_assume_tac ctxt global_assms (fn (vc) => @{thm impE} OF [vc]) 3
  | AssumeConjR n => 
     if n = 1 then
        b_assume_tac ctxt global_assms (fn (vc) => @{thm imp_conj_elim} OF [vc]) 3
     else
       b_assume_conjr_tac b_assume_tac ctxt global_assms n
  | AssertNoConj => b_assert_no_conj_tac b_assert_base_tac ctxt global_assms
  | AssertConj => b_assert_tac b_assert_base_tac ctxt global_assms (@{thm conj_elim_2})
  | AssertSub => b_assert_tac b_assert_base_tac ctxt global_assms (@{thm conj_imp_elim})
  | AssumeFalse => (eresolve_tac ctxt [@{thm assume_false_cmds}] 1) THEN ALLGOALS (asm_full_simp_tac ctxt)
  | AssumeNot => b_assume_tac ctxt global_assms (fn (vc) => @{thm imp_not_elim} OF [vc]) 0 THEN 
      TRY (ALLGOALS (asm_full_simp_tac ctxt))
  | AssertFalse => SOLVED' (asm_full_simp_tac ctxt) 1
  | AssumeTrue => (eresolve_tac ctxt [@{thm assume_true_cmds}] 1) THEN (asm_full_simp_tac ctxt 1) THEN
                  rotate_tac 1 1
  | AssertTrue => (eresolve_tac ctxt [@{thm assert_true_cmds}] 1) THEN (rotate_tac 1 1)
  ) THEN
   b_vc_hint_tac b_assume_tac b_assert_base_tac ctxt global_assms xs 

val b_vc_hint_tac_1 = b_vc_hint_tac b_assume_simple_tac b_assert_base_tac
val b_vc_hint_tac_2 = b_vc_hint_tac b_assume_simple_tac_2 b_assert_base_tac_2
\<close>

end