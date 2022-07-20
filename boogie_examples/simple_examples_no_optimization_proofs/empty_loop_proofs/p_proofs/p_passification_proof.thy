theory p_passification_proof
imports Boogie_Lang.Semantics Boogie_Lang.Util p_before_ast_to_cfg_prog p_passive_prog Boogie_Lang.PassificationML p_vcphase_proof Boogie_Lang.PassificationEndToEnd
begin
definition R_old_list :: "(((vname) \<times> ((vname) + (lit)))list)"
  where
    "R_old_list  = []"
definition R_old
  where
    "R_old  = (map_of R_old_list)"
abbreviation \<Lambda>1
  where
    "\<Lambda>1  \<equiv> ((append p_before_ast_to_cfg_prog.constants_vdecls p_before_ast_to_cfg_prog.globals_vdecls),(append p_before_ast_to_cfg_prog.params_vdecls p_before_ast_to_cfg_prog.locals_vdecls))"
abbreviation \<Lambda>2
  where
    "\<Lambda>2  \<equiv> ((append p_before_ast_to_cfg_prog.constants_vdecls p_before_ast_to_cfg_prog.globals_vdecls),(append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls))"
declare One_nat_def[simp del]

lemma block_GeneratedUnifiedExit:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> p_before_passive_prog.block_0 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [] R R_old U0 D0 n_s)"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [])) (update_nstate_rel R []) R_old p_passive_prog.block_0 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding p_before_passive_prog.block_0_def p_passive_prog.block_0_def
apply (passive_rel_tac)
apply (unfold type_rel_def, simp, (intro conjI)?)
by simp

lemma block_anon3_LoopBody:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> p_before_passive_prog.block_1 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [] R R_old U0 D0 n_s)" and 
"((R 0) = (Some (Inr (LInt 0))))"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [])) (update_nstate_rel R []) R_old p_passive_prog.block_1 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding p_before_passive_prog.block_1_def p_passive_prog.block_1_def
apply (passive_rel_tac R_def: assms(3-))
apply (unfold type_rel_def, simp, (intro conjI)?)
by simp

lemma block_anon2:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> p_before_passive_prog.block_2 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [] R R_old U0 D0 n_s)" and 
"((R 0) = (Some (Inr (LInt 0))))"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [])) (update_nstate_rel R []) R_old p_passive_prog.block_2 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding p_before_passive_prog.block_2_def p_passive_prog.block_2_def
apply (passive_rel_tac R_def: assms(3-))
apply (unfold type_rel_def, simp, (intro conjI)?)
by simp

lemma block_anon3_LoopDone:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> p_before_passive_prog.block_3 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [] R R_old U0 D0 n_s)" and 
"((R 0) = (Some (Inr (LInt 0))))"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [])) (update_nstate_rel R []) R_old p_passive_prog.block_3 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding p_before_passive_prog.block_3_def p_passive_prog.block_3_def
apply (passive_rel_tac R_def: assms(3-))
apply (unfold type_rel_def, simp, (intro conjI)?)
by simp

lemma block_anon3_LoopHead:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> p_before_passive_prog.block_4 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [] R R_old U0 D0 n_s)" and 
"((R 0) = (Some (Inr (LInt 0))))"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [])) (update_nstate_rel R []) R_old p_passive_prog.block_4 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding p_before_passive_prog.block_4_def p_passive_prog.block_4_def
apply (passive_rel_tac R_def: assms(3-))
apply (unfold type_rel_def, simp, (intro conjI)?)
by simp

lemma block_anon0:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> p_before_passive_prog.block_5 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [] R R_old U0 D0 n_s)"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [])) (update_nstate_rel R [(0,(Inr (LInt 0)))]) R_old p_passive_prog.block_5 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding p_before_passive_prog.block_5_def p_passive_prog.block_5_def
apply (passive_rel_tac)
apply (unfold type_rel_def, simp, (intro conjI)?)
by simp

lemma block_0:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> p_before_passive_prog.block_6 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [] R R_old U0 D0 n_s)"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [])) (update_nstate_rel R []) R_old p_passive_prog.block_6 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding p_before_passive_prog.block_6_def p_passive_prog.block_6_def
apply (passive_rel_tac)
apply (unfold type_rel_def, simp, (intro conjI)?)
by simp

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> p_before_passive_prog.block_7 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [] R R_old U0 D0 n_s)"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [])) (update_nstate_rel R []) R_old p_passive_prog.block_7 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding p_before_passive_prog.block_7_def p_passive_prog.block_7_def
apply (passive_rel_tac)
apply (unfold type_rel_def, simp, (intro conjI)?)
by simp

lemma cfg_block_GeneratedUnifiedExit:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> p_before_passive_prog.proc_body ((Inl 0),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 1000 R R_old U0 D0 n_s)"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> p_passive_prog.proc_body u (Inl 0)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} [] (@{thm p_before_passive_prog.node_0},@{thm p_before_passive_prog.outEdges_0}) (@{thm p_passive_prog.node_0},@{thm p_passive_prog.outEdges_0}) @{thm block_GeneratedUnifiedExit} [] 1\<close>))

lemma cfg_block_anon3_LoopBody:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> p_before_passive_prog.proc_body ((Inl 1),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 1000 R R_old U0 D0 n_s)" and 
"((R 0) = (Some (Inr (LInt 0))))"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> p_passive_prog.proc_body u (Inl 1)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} @{thms assms(3-)} (@{thm p_before_passive_prog.node_1},@{thm p_before_passive_prog.outEdges_1}) (@{thm p_passive_prog.node_1},@{thm p_passive_prog.outEdges_1}) @{thm block_anon3_LoopBody} [
@{thm cfg_block_GeneratedUnifiedExit}] 1\<close>))

lemma cfg_block_anon2:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> p_before_passive_prog.proc_body ((Inl 2),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 1000 R R_old U0 D0 n_s)" and 
"((R 0) = (Some (Inr (LInt 0))))"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> p_passive_prog.proc_body u (Inl 2)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} @{thms assms(3-)} (@{thm p_before_passive_prog.node_2},@{thm p_before_passive_prog.outEdges_2}) (@{thm p_passive_prog.node_2},@{thm p_passive_prog.outEdges_2}) @{thm block_anon2} [
@{thm cfg_block_GeneratedUnifiedExit}] 1\<close>))

lemma cfg_block_anon3_LoopDone:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> p_before_passive_prog.proc_body ((Inl 3),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 1000 R R_old U0 D0 n_s)" and 
"((R 0) = (Some (Inr (LInt 0))))"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> p_passive_prog.proc_body u (Inl 3)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} @{thms assms(3-)} (@{thm p_before_passive_prog.node_3},@{thm p_before_passive_prog.outEdges_3}) (@{thm p_passive_prog.node_3},@{thm p_passive_prog.outEdges_3}) @{thm block_anon3_LoopDone} [
@{thm cfg_block_anon2}] 1\<close>))

lemma cfg_block_anon3_LoopHead:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> p_before_passive_prog.proc_body ((Inl 4),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 1000 R R_old U0 D0 n_s)" and 
"((R 0) = (Some (Inr (LInt 0))))"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> p_passive_prog.proc_body u (Inl 4)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} @{thms assms(3-)} (@{thm p_before_passive_prog.node_4},@{thm p_before_passive_prog.outEdges_4}) (@{thm p_passive_prog.node_4},@{thm p_passive_prog.outEdges_4}) @{thm block_anon3_LoopHead} [
@{thm cfg_block_anon3_LoopDone}, 
@{thm cfg_block_anon3_LoopBody}] 1\<close>))

lemma cfg_block_anon0:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> p_before_passive_prog.proc_body ((Inl 5),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 1000 R R_old U0 D0 n_s)"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> p_passive_prog.proc_body u (Inl 5)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} [] (@{thm p_before_passive_prog.node_5},@{thm p_before_passive_prog.outEdges_5}) (@{thm p_passive_prog.node_5},@{thm p_passive_prog.outEdges_5}) @{thm block_anon0} [
@{thm cfg_block_anon3_LoopHead}] 1\<close>))

lemma cfg_block_0:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> p_before_passive_prog.proc_body ((Inl 6),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 1000 R R_old U0 D0 n_s)"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> p_passive_prog.proc_body u (Inl 6)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} [] (@{thm p_before_passive_prog.node_6},@{thm p_before_passive_prog.outEdges_6}) (@{thm p_passive_prog.node_6},@{thm p_passive_prog.outEdges_6}) @{thm block_0} [
@{thm cfg_block_anon0}] 1\<close>))

lemma cfg_block_PreconditionGeneratedEntry:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> p_before_passive_prog.proc_body ((Inl 7),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 1000 R R_old U0 D0 n_s)"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> p_passive_prog.proc_body u (Inl 7)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} [] (@{thm p_before_passive_prog.node_7},@{thm p_before_passive_prog.outEdges_7}) (@{thm p_passive_prog.node_7},@{thm p_passive_prog.outEdges_7}) @{thm block_PreconditionGeneratedEntry} [
@{thm cfg_block_0}] 1\<close>))

locale glue_proof = 
fixes A :: "(('a)absval_ty_fun)" and M :: "(mbodyCFG proc_context)" and \<Gamma> :: "(('a)fun_interp)" and m' :: "((node) + (unit))" and ns :: "(('a)nstate)" and s' :: "(('a)state)"
assumes 
Red: "(red_cfg_multi A M ((append p_before_ast_to_cfg_prog.constants_vdecls p_before_ast_to_cfg_prog.globals_vdecls),(append p_before_ast_to_cfg_prog.params_vdecls p_before_ast_to_cfg_prog.locals_vdecls)) \<Gamma> [] p_before_passive_prog.proc_body ((Inl 7),(Normal ns)) (m',s'))" and 
VC: "(\<And> (vc_x::int). (vc.vc_PreconditionGeneratedEntry ))" and 
Closed: "(\<And> v. (closed ((type_of_val A) v)))" and 
NonEmptyTypes: "(\<And> t. ((closed t) \<Longrightarrow> (\<exists> v. (((type_of_val A) v) = t))))" and 
FInterp: "(fun_interp_wf A p_before_ast_to_cfg_prog.fdecls \<Gamma>)" and 
Axioms: "(axiom_assm A \<Gamma> p_before_ast_to_cfg_prog.constants_vdecls ns p_before_ast_to_cfg_prog.axioms)" and 
ParamsLocal: "(state_typ_wf A [] (local_state ns) (snd \<Lambda>1))" and 
ConstsGlobal: "(state_typ_wf A [] (global_state ns) (fst \<Lambda>1))" and 
BinderNs: "((binder_state ns) = Map.empty)" and 
OldGlobal: "((global_state ns) = (old_global_state ns))"
begin

definition R_list :: "(((vname) \<times> ((vname) + (lit)))list)"
  where
    "R_list  = []"
definition R_rel
  where
    "R_rel  = (map_of R_list)"
lemma inj_R_rel:
shows "(inj_on_defined R_rel)"
apply (rule injective_fun_to_list_2[OF R_rel_def])
by ((simp add: R_list_def del: distinct.simps))

lemma R_well_formed:
shows "(((R_rel x) = (Some z)) \<longrightarrow> (\<exists> \<tau>. ((z = (Inl x)) \<and> (((lookup_var_ty \<Lambda>1 x) = (Some \<tau>)) \<and> ((lookup_var_ty \<Lambda>2 x) = (Some \<tau>))))))"
apply (rule convert_fun_to_list[OF R_rel_def])
apply ((simp add:R_list_def))
apply ((intro conjI)?)
done

lemma R_wt:
shows "(rel_well_typed A \<Lambda>1 [] R_rel ns)"
apply (rule rel_well_typed_state_typ_wf[OF ParamsLocal ConstsGlobal])
using R_well_formed by auto

abbreviation U0
  where
    "U0  \<equiv> (initial_set A R_rel \<Lambda>1 \<Lambda>2 [] ns)"
lemma U0_ns_rel:
shows "(nstate_rel_states \<Lambda>1 \<Lambda>2 R_rel ns U0)"
unfolding nstate_rel_states_def nstate_rel_def
by ((simp add:BinderNs))

lemma U0_ns_old_rel:
shows "(nstate_old_rel_states \<Lambda>1 \<Lambda>2 R_old ns U0)"
apply (rule nstate_old_rel_states_helper[OF ConstsGlobal OldGlobal])
apply (simp only: fst_conv snd_conv p_before_passive_prog.globals_locals_disj)
apply (rule convert_fun_to_list[OF R_old_def])
unfolding R_old_list_def 
apply simp
apply (rule convert_fun_to_list[OF R_old_def])
unfolding R_old_list_def 
by simp

lemma closed_ty_passive_vars:
assumes 
"((lookup_var_ty \<Lambda>2 x) = (Some \<tau>))"
shows "(closed (instantiate [] \<tau>))"
apply (rule lookup_ty_pred[OF assms(1)])
unfolding p_before_ast_to_cfg_prog.constants_vdecls_def p_before_ast_to_cfg_prog.globals_vdecls_def
apply simp
unfolding p_passive_prog.params_vdecls_def p_passive_prog.locals_vdecls_def
by simp

lemma U0_non_empty:
shows "(U0 \<noteq> {})"
apply (rule init_set_non_empty)
apply (erule NonEmptyTypes)
apply (erule closed_ty_passive_vars)
using R_well_formed apply fastforce
apply (rule R_wt)
apply (rule inj_R_rel)
apply simp
apply (rule ConstsGlobal)
using R_well_formed apply fastforce
using p_before_passive_prog.globals_locals_disj apply auto[1]
using p_passive_prog.globals_locals_disj apply auto[1]
done

lemma max_rel_range:
shows "(\<forall> x. ((Set.member x (rel_range R_rel)) \<longrightarrow> (x \<le> 0)))"
 apply (rule rel_range_fun_to_list)
apply ((simp add:R_rel_def))
by ((simp add:R_list_def))

lemma end_to_end:
shows "(s' \<noteq> Failure)"
proof
assume A1: "(s' = Failure)"
have "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> [] p_passive_prog.proc_body u (Inl 7)))))"
apply (rule cfg_block_PreconditionGeneratedEntry[OF Red])
unfolding passive_lemma_assms_2_def
apply (intro conjI)?
apply (rule U0_ns_rel)
apply (rule U0_ns_old_rel)
apply (rule R_wt)
apply (rule init_state_dependent)
using helper_init_disj[OF max_rel_range p_before_ast_to_cfg_prog.globals_max]
apply simp
apply (rule U0_non_empty)
by ((simp_all add:R_rel_def R_list_def))?
with A1 obtain u mp' where uElem: "(Set.member u U0)" and AredPassive:"(red_cfg_multi A M \<Lambda>2 \<Gamma> [] p_passive_prog.proc_body ((Inl 7),(Normal u)) (mp',Failure))"
by (auto simp add: passive_sim_cfg_fail_def)
from p_vcphase_proof.end_to_end[OF AredPassive] have "(Failure \<noteq> Failure)"
 apply rule
using VC apply assumption
apply (rule Closed)
apply (erule NonEmptyTypes)
apply (rule FInterp)
apply (rule axiom_assm_aux[OF Axioms])
using uElem by simp_all
thus False by simp
qed


end


end
