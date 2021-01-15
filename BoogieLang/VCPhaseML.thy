theory VCPhaseML                                      
  imports Semantics Util VCHints VCExprHelper Diagnostic HelperML
begin

ML \<open>
(** tactics for end-to-endproof**)

fun vc_fun_corres_tac ctxt corres_thm interp_thm fun_mem_thm context_mem_thm =
 let val corres_thm_inst = corres_thm OF [(@{thm finterp_extract_1} OF [interp_thm, fun_mem_thm, context_mem_thm])] in
   resolve_tac ctxt [corres_thm_inst] THEN_ALL_NEW  (asm_full_simp_tac ctxt)
 end
\<close>

ML \<open>
(** Tactics for quantifiers **)

fun forall_basic_tac ctxt =
  FIRST'[
  resolve_tac ctxt [@{thm forall_vc_rel_int}],
  resolve_tac ctxt [@{thm forall_vc_rel_bool}]
(*  resolve_tac ctxt [@{thm exists_vc_rel_int}],
  resolve_tac ctxt [@{thm exists_vc_rel_int}] *)
  ];

fun quantifier_poly_tac quant_poly_thm ctxt =
  resolve_tac ctxt [quant_poly_thm] THEN' 
  asm_full_simp_tac ctxt THEN'
  asm_full_simp_tac ctxt;
  

(* we first repeat the basic tactic, since if there are only primitive type quantifiers, then there 
are no type guards (and thus, imp_vc should not be applied) *)
fun forall_main_tac ctxt forall_poly_thm i = 
  CHANGED
    ( (REPEAT_DETERM (forall_basic_tac ctxt i))  THEN (
       TRY
        (REPEAT_DETERM1 ((quantifier_poly_tac forall_poly_thm ctxt i) ORELSE (forall_basic_tac ctxt i)) THEN
        ((resolve_tac ctxt [@{thm imp_vc}] i THEN 
          asm_full_simp_tac ctxt i) ORELSE all_tac))
      )
    )
\<close>

ML \<open>
(** Tactics for proving \<Gamma> \<turnstile> \<langle>e, ns\<rangle> \<Down> BoolV vc  **)

(* TODO: this particular tactic could be implemented more efficiently by just checking if the list has two elements *)
fun tac_more_than_1_goal tac =
  tactic_ngoals (fn i => if i > 1 then tac else no_tac)

(* Hack: apply simplification only if goal is an equality and there are at least 2 subgoals 
         this is to avoid applying simplification in cases where we do not want to, but is brittle 
         and should be made cleaner *)
fun vc_expr_rel_select_tac ctxt red_expr_tac assms (t,i) =
  case (Logic.strip_assums_concl t) of
    Const (@{const_name "HOL.eq"},_) $ _ $ _ => (tac_more_than_1_goal (( asm_full_simp_tac (add_simps assms ctxt) |> SOLVED') i))
   | @{term "Trueprop"} $ t' => vc_expr_rel_select_tac ctxt red_expr_tac assms (t',i)
   | _ => red_expr_tac ctxt assms i

fun red_var_tac ctxt assms del_thms  =
resolve_tac ctxt [@{thm RedVar}] THEN' 
(asm_full_simp_tac ((ctxt addsimps (@{thm lookup_full_ext_env_same} :: assms) delsimps (@{thm full_ext_env.simps} :: del_thms))) |> SOLVED')

fun b_prove_assert_expr_simple_tac ctxt assms del_thms i =
REPEAT ( (SUBGOAL (vc_expr_rel_select_tac ctxt
(fn ctxt => fn assms => FIRST' [
red_var_tac ctxt assms del_thms,
resolve_tac ctxt [@{thm RedBVar}] THEN' (asm_full_simp_tac ((ctxt addsimps assms delsimps del_thms)) |> SOLVED'),
resolve_tac ctxt [@{thm RedLit}],
resolve_tac ctxt [@{thm RedBinOp}],
resolve_tac ctxt [@{thm RedUnOp}],
resolve_tac ctxt [@{thm RedFunOp}] THEN' (asm_full_simp_tac (ctxt addsimps assms delsimps del_thms) |> SOLVED'),
resolve_tac ctxt [@{thm RedExpListNil}],
resolve_tac ctxt [@{thm RedExpListCons}]
]) assms )
) i)

fun vc_expr_rel_red_tac ctxt assms forall_poly_thm del_thms = 
 FIRST' [
red_var_tac ctxt assms del_thms,
(resolve_tac ctxt [@{thm RedBVar}] THEN' (asm_full_simp_tac (ctxt addsimps assms delsimps del_thms) |> SOLVED')),
(resolve_tac ctxt [@{thm RedLit}]),
(* maybe check whether goal has binop and only then try binop tactics *)
(resolve_tac ctxt [@{thm conj_vc_rel}]),
(resolve_tac ctxt [@{thm disj_vc_rel}]),
(resolve_tac ctxt [@{thm imp_vc_rel}]),
(resolve_tac ctxt [@{thm not_vc_rel}]),
(resolve_tac ctxt [@{thm gt_vc_rel}]),
(resolve_tac ctxt [@{thm ge_vc_rel}]),
(resolve_tac ctxt [@{thm lt_vc_rel}]),
(resolve_tac ctxt [@{thm le_vc_rel}]),
(resolve_tac ctxt [@{thm eq_bool_vc_rel}]),
(resolve_tac ctxt [@{thm eq_int_vc_rel}]),
(resolve_tac ctxt [@{thm eq_abs_vc_rel}]),
(resolve_tac ctxt [@{thm iff_vc_rel}]),
(resolve_tac ctxt [@{thm forallt_vc}]),
(forall_main_tac ctxt forall_poly_thm),

(*
resolve_tac ctxt [@{thm add_vc_rel}],
resolve_tac ctxt [@{thm sub_vc_rel}],
resolve_tac ctxt [@{thm mul_vc_rel}],
resolve_tac ctxt [@{thm uminus_vc_rel}],
*)
(resolve_tac ctxt [@{thm RedFunOp}] THEN' (asm_full_simp_tac (ctxt addsimps assms delsimps del_thms) |> SOLVED')),
(resolve_tac ctxt [@{thm RedExpListNil}]),
(resolve_tac ctxt [@{thm RedExpListCons}]),
(CHANGED o b_prove_assert_expr_simple_tac ctxt assms [] |> SOLVED')
(*(b_prove_assert_expr_simple_tac ctxt assms |> SOLVED')*)
]

fun b_vc_expr_rel_tac ctxt assms forall_poly_thm del_thms =
  REPEAT o SUBGOAL (vc_expr_rel_select_tac ctxt  (fn ctxt => fn assms => vc_expr_rel_red_tac ctxt assms forall_poly_thm del_thms) assms )

(* rewrite VC based on expression hint *)

(* if goal is given by vc, potentially rewrite goal *)
fun expr_hint_assume_tac ctxt (expr_hint:ExprHint option) i =
  (case expr_hint of
    (SOME (RewriteVC thms)) => DETERM (resolve_tac ctxt thms i)
    | _ => all_tac
  );

(* given theorem vc, potentially return another theorem that is implied by it *)
fun expr_hint_assert_tac (expr_hint:ExprHint option) vc =
  (case expr_hint of
    (SOME (RewriteVC thms)) => OF_first thms vc
    | _ => SOME (vc)
  );
\<close>
  

ML \<open>
(** Tactics to deal with assume statements **)
fun b_assume_base_tac ctxt inst_thm vc_elim expr_hint global_assms forall_poly_thm i =
(resolve_tac ctxt [inst_thm] i) THEN 
  (asm_full_simp_tac ctxt i) THEN
  (resolve_tac ctxt [vc_elim] i) THEN
  (expr_hint_assume_tac ctxt expr_hint i) THEN
  (resolve_tac ctxt [@{thm expr_to_vc}] i) THEN
  (assume_tac ctxt i) THEN
  (b_vc_expr_rel_tac ctxt global_assms forall_poly_thm [] i)

fun b_assume_foc_tac global_assms forall_poly_thm vc_elim expr_hint i (focus: Subgoal.focus) =
let
  val (red :: vc :: _) = #prems(focus)
  val ctxt = #context(focus)
in
  (b_assume_base_tac ctxt (@{thm assume_ml} OF [red]) (vc_elim vc) expr_hint global_assms forall_poly_thm i)
  handle THM _ => no_tac
end

fun b_assume_simple_tac ctxt global_assms forall_poly_thm vc_elim expr_hint n_assms_rem =
  (Subgoal.FOCUS (b_assume_foc_tac global_assms forall_poly_thm vc_elim expr_hint 1) ctxt 1) THEN   
   remove_n_assms n_assms_rem 1


fun b_assume_conjr_tac ctxt global_assms forall_poly_thm expr_hint n =
  let val vc_elim = 
    fn (vc) => @{thm imp_conj_elim} OF [(apply_thm_n_times vc @{thm imp_conj_imp} (n-1))]
  in
    (b_assume_simple_tac ctxt global_assms forall_poly_thm vc_elim expr_hint 3)
  end
\<close>

ML \<open>
(** Tactics to deal with assert statements **)

fun b_prove_assert_expr_tac ctxt vc_expr global_assms forall_poly_thm i =
  (resolve_tac ctxt [@{thm vc_to_expr} OF [vc_expr]] i) THEN
  (b_vc_expr_rel_tac ctxt global_assms forall_poly_thm [] i)

fun b_assert_base_tac ctxt inst_thm vc_expr global_assms forall_poly_thm ehint i =
  (resolve_tac ctxt [inst_thm] i) THEN
  (let val vc_expr_new_option = expr_hint_assert_tac ehint vc_expr in 
  case vc_expr_new_option of 
     SOME vc_expr_new => b_prove_assert_expr_tac ctxt vc_expr_new global_assms forall_poly_thm i
  |  NONE => no_tac
  end)
 
fun b_assert_conj_foc_tac global_assms forall_poly_thm vc_elim ehint i (focus: Subgoal.focus) =
let 
  val (red :: vc :: _) = #prems(focus)
  val ctxt = #context(focus)
in
 (b_assert_base_tac ctxt (@{thm assert_ml} OF [red]) (@{thm conjunct1} OF [vc]) global_assms forall_poly_thm ehint i) THEN
  (resolve_tac ctxt [(vc_elim OF [vc])] i)  
  handle THM _ => no_tac 
end

fun b_assert_conj_tac ctxt global_assms forall_poly_thm vc_elim ehint =
  (Subgoal.FOCUS (b_assert_conj_foc_tac global_assms forall_poly_thm vc_elim ehint 1) ctxt 1)  THEN
  eresolve0_tac [thin_rl] 1 THEN
  eresolve0_tac [thin_rl] 1

fun b_assert_no_conj_foc_tac global_assms forall_poly_thm ehint i (focus: Subgoal.focus) =
let 
  val (red :: vc :: _) = #prems(focus) 
  val ctxt = #context(focus)
in
 (b_assert_base_tac ctxt (@{thm assert_ml} OF [red]) vc global_assms forall_poly_thm ehint i)
  handle THM _ => no_tac 
end

fun b_assert_no_conj_tac ctxt global_assms forall_poly_thm ehint =
  (Subgoal.FOCUS (b_assert_no_conj_foc_tac global_assms forall_poly_thm ehint 1) ctxt 1)
\<close>

ML \<open>
(** main tactic **)

fun boogie_vc_tac ctxt _ _ ([]: (VcHint * (ExprHint option)) list) =
  TRY (eresolve_tac ctxt [@{thm nil_cmd_elim}] 1 THEN asm_full_simp_tac ctxt 1)
| boogie_vc_tac ctxt global_assms forall_poly_thm (x::xs) = 
  (case x of
  (* assume statement normal *)
    (AssumeConjR 0, ehint) => b_assume_simple_tac ctxt global_assms forall_poly_thm (fn (vc) => @{thm impE} OF [vc]) ehint 3
  | (AssumeConjR n, ehint) => 
     if n = 1 then
        b_assume_simple_tac ctxt global_assms forall_poly_thm (fn (vc) => @{thm imp_conj_elim} OF [vc]) ehint 3
     else
       b_assume_conjr_tac ctxt global_assms forall_poly_thm ehint n
  (* assert statement normal *)
  | (AssertNoConj, ehint) => b_assert_no_conj_tac ctxt global_assms forall_poly_thm ehint
  | (AssertConj, ehint) => b_assert_conj_tac ctxt global_assms forall_poly_thm (@{thm conj_elim_2}) ehint
  | (AssertSub, ehint) => b_assert_conj_tac ctxt global_assms forall_poly_thm (@{thm conj_imp_elim}) ehint 
  (* special cases *)
  | (AssumeFalse, _) => (eresolve_tac ctxt [@{thm assume_false_cmds}] 1) THEN (ALLGOALS (asm_full_simp_tac ctxt))
  | (AssumeNot, ehint) => b_assume_simple_tac ctxt global_assms forall_poly_thm (fn (vc) => @{thm imp_not_elim} OF [vc]) ehint 0 THEN 
      TRY (ALLGOALS (asm_full_simp_tac ctxt))
  | (AssertFalse, _) => SOLVED' (asm_full_simp_tac ctxt) 1
  | (AssumeTrue, _) => (eresolve_tac ctxt [@{thm assume_true_cmds}] 1) THEN (asm_full_simp_tac ctxt 1) THEN
                  rotate_tac 1 1
  | (AssertTrue, _) => (eresolve_tac ctxt [@{thm assert_true_cmds}] 1) THEN (rotate_tac 1 1)
  ) THEN
   boogie_vc_tac ctxt global_assms forall_poly_thm xs
\<close>

end