theory HelperML
imports Main
begin

ML\<open> (* taken from Cogent; add_simps adds simplification-rules into a given context. *)
fun add_simps [] ctxt = ctxt
 |  add_simps (thm::thms) ctxt = add_simps thms (Simplifier.add_simp thm ctxt)

fun fastforce_tac ctxt thms = Clasimp.fast_force_tac (add_simps thms ctxt)
\<close>

ML 
\<open>
(* apply tactic that takes the number of goals as first input *)
fun tactic_ngoals tac st =
  let 
   val prop = Thm.prop_of st;
   val (As, _) = Logic.strip_horn prop
  in
   tac (length As) st
  end

(* repeat tactic exactly n times *)
fun repeat_n_tac 0 _  = all_tac
  | repeat_n_tac n tac = tac THEN repeat_n_tac (n-1) tac

fun repeat_n_tac' 0 _  = (fn _ => all_tac)
  | repeat_n_tac' n tac = tac THEN' repeat_n_tac' (n-1) tac

fun unfold_let_tac ctxt = simp_tac (Simplifier.add_simp @{thm Let_def} (empty_simpset ctxt))
\<close>

ML \<open>
fun apply_thm_n_times vc thm n =
 (if n <= 0 then vc else 
  (apply_thm_n_times (thm OF [vc]) thm (n-1))
 )

fun remove_n_assms n i = 
 (if n <= 0 then all_tac else eresolve0_tac [thin_rl] i THEN remove_n_assms (n-1) i)

(* applies "OF" to the first theorem for which the instantiation works *)
fun OF_first [] _ = NONE
 | OF_first (thm :: thms) vc =
    (SOME (thm OF [vc]))
    handle THM _ => OF_first thms vc
\<close>

end