theory nested_loop2_cfgtodag_proof
imports Boogie_Lang.Semantics Boogie_Lang.Util Boogie_Lang.BackedgeElim Boogie_Lang.TypingML nested_loop2_before_ast_to_cfg_prog nested_loop2_before_cfg_to_dag_prog nested_loop2_before_passive_prog nested_loop2_passification_proof nested_loop2_vcphase_proof
begin
locale cfg_to_dag_lemmas = 
fixes A :: "(('a)absval_ty_fun)" and \<Gamma> :: "(('a)fun_interp)"
assumes 
Wf_Fun: "(fun_interp_wf A nested_loop2_before_ast_to_cfg_prog.fdecls \<Gamma>)"
begin

abbreviation \<Lambda>1
  where
    "\<Lambda>1  \<equiv> ((append nested_loop2_before_ast_to_cfg_prog.constants_vdecls nested_loop2_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop2_before_ast_to_cfg_prog.params_vdecls nested_loop2_before_ast_to_cfg_prog.locals_vdecls))"
declare Nat.One_nat_def[simp del]

lemma cfg_block_GeneratedUnifiedExit:
assumes 
"(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.proc_body ((Inl 0),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(state_well_typed A \<Lambda>1 [] ns2)"
shows "(expr_all_sat A \<Lambda>1 \<Gamma> [] ns2 nested_loop2_before_ast_to_cfg_prog.post)"
unfolding expr_all_sat_def nested_loop2_before_ast_to_cfg_prog.post_def 
apply (rule cfg_dag_rel_post_invs_3)
apply (erule assms(1))
apply (rule nested_loop2_before_passive_prog.node_0)
apply simp
unfolding nested_loop2_before_passive_prog.block_0_def
by cfg_dag_rel_tac_single+

lemma block_anon6_LoopDone:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.block_11 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.block_1 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [] nested_loop2_before_passive_prog.block_1 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding nested_loop2_before_cfg_to_dag_prog.block_11_def nested_loop2_before_passive_prog.block_1_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
done

lemma cfg_block_anon6_LoopDone:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 11),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.proc_body ((Inl 1),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] nested_loop2_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_return_2[OF Red])
apply (rule nested_loop2_before_cfg_to_dag_prog.node_11)
apply (rule nested_loop2_before_passive_prog.node_1)
apply (erule DagVerifies)
apply (rule DagAssms)
apply (erule block_anon6_LoopDone)
apply assumption+
apply (rule nested_loop2_before_cfg_to_dag_prog.outEdges_11)
apply (rule nested_loop2_before_passive_prog.outEdges_1)
apply (erule cfg_block_GeneratedUnifiedExit)
by assumption


lemma Mods_anon8_LoopBody:
shows "(mods_contained_in (set [1]) nested_loop2_before_cfg_to_dag_prog.block_6)"
unfolding nested_loop2_before_cfg_to_dag_prog.block_6_def
by simp

lemma block_anon8_LoopBody:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.block_6 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.block_2 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [(BinOp (Var 1) Ge (Lit (LInt 0)))] nested_loop2_before_passive_prog.block_2 ns2 s' True)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding nested_loop2_before_cfg_to_dag_prog.block_6_def nested_loop2_before_passive_prog.block_2_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
apply (erule type_safety_top_level_inv[OF Wf_Fun nested_loop2_before_ast_to_cfg_prog.funcs_wf nested_loop2_before_ast_to_cfg_prog.var_context_wf])
apply (simp)
apply ((tactic \<open> typing_tac @{context} [] @{thms nested_loop2_before_ast_to_cfg_prog.l_y(2)} [] 1\<close>))

done

lemma cfg_block_anon8_LoopBody:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 6),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.proc_body ((Inl 2),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))" and 
IH_anon8_LoopHead: "(loop_ih A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body [1] [(BinOp (Var 1) Ge (Lit (LInt 0)))] nested_loop2_before_ast_to_cfg_prog.post ns1 s' 5 m' j)"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] nested_loop2_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_2[OF Red _ _ DagVerifies DagAssms])
apply (rule nested_loop2_before_cfg_to_dag_prog.node_6)
apply (rule nested_loop2_before_passive_prog.node_2)
apply (assumption+)
apply (rule block_anon8_LoopBody)
apply (assumption+)
apply (rule Mods_anon8_LoopBody)
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_6))
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_6))
apply (erule member_elim)
apply (rule loop_ih_apply[where ?j'="j-1"])
apply (rule IH_anon8_LoopHead)
apply (simp, simp)
unfolding dag_lemma_assms_def
apply (intro conjI, simp)
apply (rule nstate_same_on_sym)
apply (simp)
apply (simp)
apply (rule dag_lemma_assms_state_wt_1[OF DagAssms])
by (simp add: member_rec(2))


lemma Mods_anon4:
shows "(mods_contained_in (set [0,1]) nested_loop2_before_cfg_to_dag_prog.block_8)"
unfolding nested_loop2_before_cfg_to_dag_prog.block_8_def
by simp

lemma block_anon4:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.block_8 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.block_3 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [(BinOp (Var 0) Ge (Lit (LInt 0)))] nested_loop2_before_passive_prog.block_3 ns2 s' True)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding nested_loop2_before_cfg_to_dag_prog.block_8_def nested_loop2_before_passive_prog.block_3_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
apply (erule type_safety_top_level_inv[OF Wf_Fun nested_loop2_before_ast_to_cfg_prog.funcs_wf nested_loop2_before_ast_to_cfg_prog.var_context_wf])
apply (simp)
apply ((tactic \<open> typing_tac @{context} [] @{thms nested_loop2_before_ast_to_cfg_prog.l_x(2)} [] 1\<close>))

done

lemma cfg_block_anon4:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 8),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.proc_body ((Inl 3),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))" and 
IH_anon7_LoopHead: "(loop_ih A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body [0,1] [(BinOp (Var 0) Ge (Lit (LInt 0)))] nested_loop2_before_ast_to_cfg_prog.post ns1 s' 3 m' j)"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] nested_loop2_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_2[OF Red _ _ DagVerifies DagAssms])
apply (rule nested_loop2_before_cfg_to_dag_prog.node_8)
apply (rule nested_loop2_before_passive_prog.node_3)
apply (assumption+)
apply (rule block_anon4)
apply (assumption+)
apply (rule Mods_anon4)
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_8))
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_8))
apply (erule member_elim)
apply (rule loop_ih_apply[where ?j'="j-1"])
apply (rule IH_anon7_LoopHead)
apply (simp, simp)
unfolding dag_lemma_assms_def
apply (intro conjI, simp)
apply (rule nstate_same_on_sym)
apply (simp)
apply (simp)
apply (rule dag_lemma_assms_state_wt_1[OF DagAssms])
by (simp add: member_rec(2))


lemma Mods_anon8_LoopDone:
shows "(mods_contained_in (set [0,1]) nested_loop2_before_cfg_to_dag_prog.block_7)"
unfolding nested_loop2_before_cfg_to_dag_prog.block_7_def
by simp

lemma block_anon8_LoopDone:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.block_7 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.block_4 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [] nested_loop2_before_passive_prog.block_4 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding nested_loop2_before_cfg_to_dag_prog.block_7_def nested_loop2_before_passive_prog.block_4_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
done

lemma cfg_block_anon8_LoopDone:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 7),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.proc_body ((Inl 4),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))" and 
IH_anon7_LoopHead: "(loop_ih A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body [0,1] [(BinOp (Var 0) Ge (Lit (LInt 0)))] nested_loop2_before_ast_to_cfg_prog.post ns1 s' 3 m' j)"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] nested_loop2_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_2[OF Red _ _ DagVerifies DagAssms])
apply (rule nested_loop2_before_cfg_to_dag_prog.node_7)
apply (rule nested_loop2_before_passive_prog.node_4)
apply (assumption+)
apply (rule block_anon8_LoopDone)
apply (assumption+)
apply (rule Mods_anon8_LoopDone)
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_7))
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_7))
apply (erule member_elim)
apply simp
apply (erule allE[where x=3])
apply ((simp add:nested_loop2_before_passive_prog.outEdges_4))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_anon4)
apply simp
unfolding dag_lemma_assms_def
apply (intro conjI)
apply simp
apply simp
apply (fastforce)
apply (simp)
apply (simp)
apply (rule loop_ih_convert_pred)
using IH_anon7_LoopHead apply simp
apply simp
apply (rule dag_lemma_assms_state_wt_1[OF DagAssms])
by (simp add: member_rec(2))


lemma Mods_anon8_LoopHead:
shows "(mods_contained_in (set [1]) nested_loop2_before_cfg_to_dag_prog.block_5)"
unfolding nested_loop2_before_cfg_to_dag_prog.block_5_def
by simp

lemma block_anon8_LoopHead:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.block_5 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.block_5 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [1] [(BinOp (Var 1) Ge (Lit (LInt 0)))] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [] nested_loop2_before_passive_prog.block_5 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding nested_loop2_before_cfg_to_dag_prog.block_5_def nested_loop2_before_passive_prog.block_5_def
apply cfg_dag_rel_tac_single+
apply simp
apply ((simp add:nested_loop2_before_ast_to_cfg_prog.l_y(1)))
apply simp
done

lemma cfg_block_anon8_LoopHead:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 5),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [1] [(BinOp (Var 1) Ge (Lit (LInt 0)))] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.proc_body ((Inl 5),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))" and 
IH_anon7_LoopHead: "(loop_ih A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body [0,1] [(BinOp (Var 0) Ge (Lit (LInt 0)))] nested_loop2_before_ast_to_cfg_prog.post ns1 s' 3 m' j)"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] nested_loop2_before_ast_to_cfg_prog.post m' s')"
using Red DagAssms assms(4-)
proof (induction j arbitrary: ns1 rule: less_induct)
case (less j)
show ?case
proof (cases j)
case 0 with less.prems(1) show ?thesis unfolding Semantics.valid_configuration_def by auto
next
case (Suc j')
from less(3) have StateRel1:"(nstate_same_on \<Lambda>1 ns1 ns2 (set [1]))"by (simp add: dag_lemma_assms_def)
from less(3) have StateWt2:"(state_well_typed A \<Lambda>1 [] ns2)"by (simp add: dag_lemma_assms_def)
show ?thesis
apply (rule cfg_dag_helper_2[OF less(2) _ _ DagVerifies less(3)])
apply (rule nested_loop2_before_cfg_to_dag_prog.node_5)
apply (rule nested_loop2_before_passive_prog.node_5)
apply (assumption+)
apply (rule block_anon8_LoopHead)
apply (assumption+)
apply (rule Mods_anon8_LoopHead)
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_5))
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_5))
apply (erule member_elim)
apply simp
apply (erule allE[where x=4])
apply ((simp add:nested_loop2_before_passive_prog.outEdges_5))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_anon8_LoopDone)
apply simp
unfolding dag_lemma_assms_def
apply (intro conjI)
apply simp
apply simp
apply (fastforce)
apply (simp)
apply (simp)
apply (rule loop_ih_convert_subset_pred)
using less(4) apply simp
apply assumption
apply (rule dag_lemma_assms_state_wt_1[OF less(3)])
apply simp
apply (erule member_elim)
apply simp
apply (erule allE[where x=2])
apply ((simp add:nested_loop2_before_passive_prog.outEdges_5))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_anon8_LoopBody)
apply simp
unfolding dag_lemma_assms_def
apply (intro conjI)
apply simp
apply simp
apply (fastforce)
apply (simp)
apply (simp)
apply (rule loop_ih_prove)
apply (rule less.IH)
apply (erule strictly_smaller_helper, assumption, assumption)
unfolding dag_lemma_assms_def
apply (intro conjI, simp)
apply (rule nstate_same_on_transitive_2[OF _ _ StateRel1])
apply ((fastforce, simp, simp))
apply (rule dag_lemma_assms_state_wt_2[OF less(3)])
apply (rule loop_ih_convert_subset_smaller_2)
using less(4) apply simp
apply (simp, fastforce, assumption)
apply (rule dag_lemma_assms_state_wt_1[OF less(3)])
apply simp
by (simp add: member_rec(2))
qed
qed


lemma Mods_anon7_LoopBody:
shows "(mods_contained_in (set [0,1]) nested_loop2_before_cfg_to_dag_prog.block_4)"
unfolding nested_loop2_before_cfg_to_dag_prog.block_4_def
by simp

lemma block_anon7_LoopBody:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.block_4 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.block_6 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [(BinOp (Var 1) Ge (Lit (LInt 0)))] nested_loop2_before_passive_prog.block_6 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding nested_loop2_before_cfg_to_dag_prog.block_4_def nested_loop2_before_passive_prog.block_6_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
apply (erule type_safety_top_level_inv[OF Wf_Fun nested_loop2_before_ast_to_cfg_prog.funcs_wf nested_loop2_before_ast_to_cfg_prog.var_context_wf])
apply (simp)
apply ((tactic \<open> typing_tac @{context} [] @{thms nested_loop2_before_ast_to_cfg_prog.l_y(2)} [] 1\<close>))

done

lemma cfg_block_anon7_LoopBody:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 4),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.proc_body ((Inl 6),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))" and 
IH_anon7_LoopHead: "(loop_ih A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body [0,1] [(BinOp (Var 0) Ge (Lit (LInt 0)))] nested_loop2_before_ast_to_cfg_prog.post ns1 s' 3 m' j)"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] nested_loop2_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_2[OF Red _ _ DagVerifies DagAssms])
apply (rule nested_loop2_before_cfg_to_dag_prog.node_4)
apply (rule nested_loop2_before_passive_prog.node_6)
apply (assumption+)
apply (rule block_anon7_LoopBody)
apply (assumption+)
apply (rule Mods_anon7_LoopBody)
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_4))
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_4))
apply (erule member_elim)
apply simp
apply (erule allE[where x=5])
apply ((simp add:nested_loop2_before_passive_prog.outEdges_6))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_anon8_LoopHead)
apply simp
unfolding dag_lemma_assms_def
apply (intro conjI)
apply simp
apply (erule nstate_same_on_empty_subset)
apply (fastforce)
apply (simp)
apply (simp)
apply (rule loop_ih_convert_pred)
using IH_anon7_LoopHead apply simp
apply simp
apply (rule dag_lemma_assms_state_wt_1[OF DagAssms])
by (simp add: member_rec(2))


lemma Mods_anon5:
shows "(mods_contained_in (set [0,1]) nested_loop2_before_cfg_to_dag_prog.block_10)"
unfolding nested_loop2_before_cfg_to_dag_prog.block_10_def
by simp

lemma block_anon5:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.block_10 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.block_7 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [] nested_loop2_before_passive_prog.block_7 ns2 s' True)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding nested_loop2_before_cfg_to_dag_prog.block_10_def nested_loop2_before_passive_prog.block_7_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
done

lemma cfg_block_anon5:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 10),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.proc_body ((Inl 7),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))" and 
IH_anon6_LoopHead: "(loop_ih A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body [0,1] [] nested_loop2_before_ast_to_cfg_prog.post ns1 s' 1 m' j)"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] nested_loop2_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_2[OF Red _ _ DagVerifies DagAssms])
apply (rule nested_loop2_before_cfg_to_dag_prog.node_10)
apply (rule nested_loop2_before_passive_prog.node_7)
apply (assumption+)
apply (rule block_anon5)
apply (assumption+)
apply (rule Mods_anon5)
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_10))
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_10))
apply (erule member_elim)
apply (rule loop_ih_apply[where ?j'="j-1"])
apply (rule IH_anon6_LoopHead)
apply (simp, simp)
unfolding dag_lemma_assms_def
apply (intro conjI, simp)
apply (rule nstate_same_on_sym)
apply (simp)
apply (simp)
apply (rule dag_lemma_assms_state_wt_1[OF DagAssms])
by (simp add: member_rec(2))


lemma Mods_anon7_LoopDone:
shows "(mods_contained_in (set [0,1]) nested_loop2_before_cfg_to_dag_prog.block_9)"
unfolding nested_loop2_before_cfg_to_dag_prog.block_9_def
by simp

lemma block_anon7_LoopDone:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.block_9 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.block_8 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [] nested_loop2_before_passive_prog.block_8 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding nested_loop2_before_cfg_to_dag_prog.block_9_def nested_loop2_before_passive_prog.block_8_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
done

lemma cfg_block_anon7_LoopDone:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 9),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.proc_body ((Inl 8),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))" and 
IH_anon6_LoopHead: "(loop_ih A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body [0,1] [] nested_loop2_before_ast_to_cfg_prog.post ns1 s' 1 m' j)"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] nested_loop2_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_2[OF Red _ _ DagVerifies DagAssms])
apply (rule nested_loop2_before_cfg_to_dag_prog.node_9)
apply (rule nested_loop2_before_passive_prog.node_8)
apply (assumption+)
apply (rule block_anon7_LoopDone)
apply (assumption+)
apply (rule Mods_anon7_LoopDone)
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_9))
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_9))
apply (erule member_elim)
apply simp
apply (erule allE[where x=7])
apply ((simp add:nested_loop2_before_passive_prog.outEdges_8))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_anon5)
apply simp
unfolding dag_lemma_assms_def
apply (intro conjI)
apply simp
apply simp
apply (fastforce)
apply (simp)
apply (simp)
apply (rule loop_ih_convert_pred)
using IH_anon6_LoopHead apply simp
apply simp
apply (rule dag_lemma_assms_state_wt_1[OF DagAssms])
by (simp add: member_rec(2))


lemma Mods_anon7_LoopHead:
shows "(mods_contained_in (set [0,1]) nested_loop2_before_cfg_to_dag_prog.block_3)"
unfolding nested_loop2_before_cfg_to_dag_prog.block_3_def
by simp

lemma block_anon7_LoopHead:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.block_3 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.block_9 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [0,1] [(BinOp (Var 0) Ge (Lit (LInt 0)))] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [] nested_loop2_before_passive_prog.block_9 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding nested_loop2_before_cfg_to_dag_prog.block_3_def nested_loop2_before_passive_prog.block_9_def
apply cfg_dag_rel_tac_single+
apply simp
apply ((simp add:nested_loop2_before_ast_to_cfg_prog.l_x(1)))
apply ((simp add:nested_loop2_before_ast_to_cfg_prog.l_y(1)))
apply simp
done

lemma cfg_block_anon7_LoopHead:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 3),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [0,1] [(BinOp (Var 0) Ge (Lit (LInt 0)))] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.proc_body ((Inl 9),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))" and 
IH_anon6_LoopHead: "(loop_ih A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body [0,1] [] nested_loop2_before_ast_to_cfg_prog.post ns1 s' 1 m' j)"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] nested_loop2_before_ast_to_cfg_prog.post m' s')"
using Red DagAssms assms(4-)
proof (induction j arbitrary: ns1 rule: less_induct)
case (less j)
show ?case
proof (cases j)
case 0 with less.prems(1) show ?thesis unfolding Semantics.valid_configuration_def by auto
next
case (Suc j')
from less(3) have StateRel1:"(nstate_same_on \<Lambda>1 ns1 ns2 (set [0,1]))"by (simp add: dag_lemma_assms_def)
from less(3) have StateWt2:"(state_well_typed A \<Lambda>1 [] ns2)"by (simp add: dag_lemma_assms_def)
show ?thesis
apply (rule cfg_dag_helper_2[OF less(2) _ _ DagVerifies less(3)])
apply (rule nested_loop2_before_cfg_to_dag_prog.node_3)
apply (rule nested_loop2_before_passive_prog.node_9)
apply (assumption+)
apply (rule block_anon7_LoopHead)
apply (assumption+)
apply (rule Mods_anon7_LoopHead)
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_3))
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_3))
apply (erule member_elim)
apply simp
apply (erule allE[where x=8])
apply ((simp add:nested_loop2_before_passive_prog.outEdges_9))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_anon7_LoopDone)
apply simp
unfolding dag_lemma_assms_def
apply (intro conjI)
apply simp
apply simp
apply (fastforce)
apply (simp)
apply (simp)
apply (rule loop_ih_convert_subset_pred)
using less(4) apply simp
apply assumption
apply (rule dag_lemma_assms_state_wt_1[OF less(3)])
apply simp
apply (erule member_elim)
apply simp
apply (erule allE[where x=6])
apply ((simp add:nested_loop2_before_passive_prog.outEdges_9))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_anon7_LoopBody)
apply simp
unfolding dag_lemma_assms_def
apply (intro conjI)
apply simp
apply simp
apply (fastforce)
apply (simp)
apply (simp)
apply (rule loop_ih_prove)
apply (rule less.IH)
apply (erule strictly_smaller_helper, assumption, assumption)
unfolding dag_lemma_assms_def
apply (intro conjI, simp)
apply (rule nstate_same_on_transitive_2[OF _ _ StateRel1])
apply ((fastforce, simp, simp))
apply (rule dag_lemma_assms_state_wt_2[OF less(3)])
apply (rule loop_ih_convert_subset_smaller_2)
using less(4) apply simp
apply (simp, fastforce, assumption)
apply (rule dag_lemma_assms_state_wt_1[OF less(3)])
apply simp
by (simp add: member_rec(2))
qed
qed


lemma Mods_anon6_LoopBody:
shows "(mods_contained_in (set [0,1]) nested_loop2_before_cfg_to_dag_prog.block_2)"
unfolding nested_loop2_before_cfg_to_dag_prog.block_2_def
by simp

lemma block_anon6_LoopBody:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.block_2 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.block_10 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [(BinOp (Var 0) Ge (Lit (LInt 0)))] nested_loop2_before_passive_prog.block_10 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding nested_loop2_before_cfg_to_dag_prog.block_2_def nested_loop2_before_passive_prog.block_10_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
apply (erule type_safety_top_level_inv[OF Wf_Fun nested_loop2_before_ast_to_cfg_prog.funcs_wf nested_loop2_before_ast_to_cfg_prog.var_context_wf])
apply (simp)
apply ((tactic \<open> typing_tac @{context} [] @{thms nested_loop2_before_ast_to_cfg_prog.l_x(2)} [] 1\<close>))

done

lemma cfg_block_anon6_LoopBody:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 2),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.proc_body ((Inl 10),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))" and 
IH_anon6_LoopHead: "(loop_ih A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body [0,1] [] nested_loop2_before_ast_to_cfg_prog.post ns1 s' 1 m' j)"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] nested_loop2_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_2[OF Red _ _ DagVerifies DagAssms])
apply (rule nested_loop2_before_cfg_to_dag_prog.node_2)
apply (rule nested_loop2_before_passive_prog.node_10)
apply (assumption+)
apply (rule block_anon6_LoopBody)
apply (assumption+)
apply (rule Mods_anon6_LoopBody)
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_2))
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_2))
apply (erule member_elim)
apply simp
apply (erule allE[where x=9])
apply ((simp add:nested_loop2_before_passive_prog.outEdges_10))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_anon7_LoopHead)
apply simp
unfolding dag_lemma_assms_def
apply (intro conjI)
apply simp
apply (erule nstate_same_on_empty_subset)
apply (fastforce)
apply (simp)
apply (simp)
apply (rule loop_ih_convert_pred)
using IH_anon6_LoopHead apply simp
apply simp
apply (rule dag_lemma_assms_state_wt_1[OF DagAssms])
by (simp add: member_rec(2))


lemma Mods_anon6_LoopHead:
shows "(mods_contained_in (set [0,1]) nested_loop2_before_cfg_to_dag_prog.block_1)"
unfolding nested_loop2_before_cfg_to_dag_prog.block_1_def
by simp

lemma block_anon6_LoopHead:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.block_1 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.block_11 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [0,1] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [] nested_loop2_before_passive_prog.block_11 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding nested_loop2_before_cfg_to_dag_prog.block_1_def nested_loop2_before_passive_prog.block_11_def
apply cfg_dag_rel_tac_single+
apply simp
apply ((simp add:nested_loop2_before_ast_to_cfg_prog.l_x(1)))
apply ((simp add:nested_loop2_before_ast_to_cfg_prog.l_y(1)))
apply simp
done

lemma cfg_block_anon6_LoopHead:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 1),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [0,1] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.proc_body ((Inl 11),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] nested_loop2_before_ast_to_cfg_prog.post m' s')"
using Red DagAssms
proof (induction j arbitrary: ns1 rule: less_induct)
case (less j)
show ?case
proof (cases j)
case 0 with less.prems(1) show ?thesis unfolding Semantics.valid_configuration_def by auto
next
case (Suc j')
from less(3) have StateRel1:"(nstate_same_on \<Lambda>1 ns1 ns2 (set [0,1]))"by (simp add: dag_lemma_assms_def)
from less(3) have StateWt2:"(state_well_typed A \<Lambda>1 [] ns2)"by (simp add: dag_lemma_assms_def)
show ?thesis
apply (rule cfg_dag_helper_2[OF less(2) _ _ DagVerifies less(3)])
apply (rule nested_loop2_before_cfg_to_dag_prog.node_1)
apply (rule nested_loop2_before_passive_prog.node_11)
apply (assumption+)
apply (rule block_anon6_LoopHead)
apply (assumption+)
apply (rule Mods_anon6_LoopHead)
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_1))
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_1))
apply (erule member_elim)
apply simp
apply (erule allE[where x=1])
apply ((simp add:nested_loop2_before_passive_prog.outEdges_11))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_anon6_LoopDone)
apply simp
unfolding dag_lemma_assms_def
apply (intro conjI)
apply simp
apply simp
apply (fastforce)
apply (simp)
apply (simp)
apply (erule member_elim)
apply simp
apply (erule allE[where x=10])
apply ((simp add:nested_loop2_before_passive_prog.outEdges_11))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_anon6_LoopBody)
apply simp
unfolding dag_lemma_assms_def
apply (intro conjI)
apply simp
apply simp
apply (fastforce)
apply (simp)
apply (simp)
apply (rule loop_ih_prove)
apply (rule less.IH)
apply (erule strictly_smaller_helper, assumption, assumption)
unfolding dag_lemma_assms_def
apply (intro conjI, simp)
apply (rule nstate_same_on_transitive_2[OF _ _ StateRel1])
apply ((fastforce, simp, simp))
apply (rule dag_lemma_assms_state_wt_2[OF less(3)])
by (simp add: member_rec(2))
qed
qed


lemma block_anon0:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.block_0 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.block_12 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [] nested_loop2_before_passive_prog.block_12 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding nested_loop2_before_cfg_to_dag_prog.block_0_def nested_loop2_before_passive_prog.block_12_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
done

lemma cfg_block_anon0:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.proc_body ((Inl 12),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] nested_loop2_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_1[OF Red _ _ DagVerifies DagAssms])
apply (rule nested_loop2_before_cfg_to_dag_prog.node_0)
apply (rule nested_loop2_before_passive_prog.node_12)
apply (assumption+)
apply (rule block_anon0)
apply (assumption+)
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_0))
apply ((simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_0))
apply (erule member_elim)
apply simp
apply (erule allE[where x=11])
apply ((simp add:nested_loop2_before_passive_prog.outEdges_12))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_anon6_LoopHead)
apply simp
unfolding dag_lemma_assms_def
apply (intro conjI)
apply simp
apply (erule nstate_same_on_empty_subset)
apply (fastforce)
apply (simp)
apply (simp)
by (simp add: member_rec(2))


lemma cfg_block_0:
assumes 
"(\<forall> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.proc_body ((Inl 13),(Normal ns2)) (m2',s2')) \<longrightarrow> (s2' \<noteq> Failure)))" and 
"(nstate_same_on \<Lambda>1 ns1 ns2 {})" and 
"(state_well_typed A \<Lambda>1 [] ns1)" and 
"(state_well_typed A \<Lambda>1 [] ns2)" and 
"((\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.proc_body ((Inl 12),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure))) \<Longrightarrow> R)"
shows "R"
using assms
apply (rule cfg_dag_empty_propagate_helper)
apply (assumption, simp)
apply ((simp add:nested_loop2_before_passive_prog.outEdges_13))
by ((simp add:nested_loop2_before_passive_prog.node_13 nested_loop2_before_passive_prog.block_13_def))

lemma entry_lemma:
assumes 
"(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) j (m',s'))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
"(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] nested_loop2_before_passive_prog.proc_body ((Inl 14),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(expr_all_sat A \<Lambda>1 \<Gamma> [] ns2 nested_loop2_before_ast_to_cfg_prog.pres)"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] nested_loop2_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_entry)
apply (rule nested_loop2_before_passive_prog.node_14)
apply (erule assms(3))
apply (rule assms(2))
unfolding nested_loop2_before_passive_prog.block_14_def
apply (rule assume_pres_normal[where ?es=nested_loop2_before_ast_to_cfg_prog.pres])
apply (rule assms(4))
unfolding nested_loop2_before_ast_to_cfg_prog.pres_def
apply simp
apply (rule nested_loop2_before_passive_prog.outEdges_14)
apply ((simp add:nested_loop2_before_passive_prog.node_13 nested_loop2_before_passive_prog.block_13_def))
apply (rule nested_loop2_before_passive_prog.outEdges_13)
by (rule cfg_block_anon0[OF assms(1-2)])


end

abbreviation \<Lambda>0
  where
    "\<Lambda>0  \<equiv> ((append nested_loop2_before_ast_to_cfg_prog.constants_vdecls nested_loop2_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop2_before_ast_to_cfg_prog.params_vdecls nested_loop2_before_ast_to_cfg_prog.locals_vdecls))"
lemma end_to_end_theorem_aux:
assumes 
Red: "(red_cfg_multi A M ((append nested_loop2_before_ast_to_cfg_prog.constants_vdecls nested_loop2_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop2_before_ast_to_cfg_prog.params_vdecls nested_loop2_before_ast_to_cfg_prog.locals_vdecls)) \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns)) (m',s'))" and 
VC: "(\<And> (vc_x::int) (vc_y::int) (vc_x_0::int) (vc_y_0::int) (vc_x_1::int) (vc_y_1::int) (vc_y_2::int) (vc_y_3::int) (vc_x_2::int). (vc.vc_anon0 vc_x_0 vc_x_1 vc_y_1 vc_y_2 vc_x_2 vc_y_3))" and 
Closed: "(\<And> v. (closed ((type_of_val A) v)))" and 
NonEmptyTypes: "(\<And> t. ((closed t) \<Longrightarrow> (\<exists> v. (((type_of_val A) v) = t))))" and 
FInterp: "(fun_interp_wf A nested_loop2_before_ast_to_cfg_prog.fdecls \<Gamma>)" and 
Axioms: "(axiom_assm A \<Gamma> nested_loop2_before_ast_to_cfg_prog.constants_vdecls (ns::(('a)nstate)) nested_loop2_before_ast_to_cfg_prog.axioms)" and 
Precondition: "(expr_all_sat A \<Lambda>0 \<Gamma> [] ns nested_loop2_before_ast_to_cfg_prog.pres)" and 
ParamsLocal: "(state_typ_wf A [] (local_state ns) (snd \<Lambda>0))" and 
ConstsGlobal: "(state_typ_wf A [] (global_state ns) (fst \<Lambda>0))" and 
OldGlobal: "((global_state ns) = (old_global_state ns))" and 
BinderNs: "((binder_state ns) = Map.empty)"
shows "(Semantics.valid_configuration A \<Lambda>0 \<Gamma> [] nested_loop2_before_ast_to_cfg_prog.post m' s')"
proof -
from Red obtain j where Aux:"(red_cfg_k_step A M ((append nested_loop2_before_ast_to_cfg_prog.constants_vdecls nested_loop2_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop2_before_ast_to_cfg_prog.params_vdecls nested_loop2_before_ast_to_cfg_prog.locals_vdecls)) \<Gamma> [] nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns)) j (m',s'))"
by (meson rtranclp_imp_relpowp)
show ?thesis
apply (rule cfg_to_dag_lemmas.entry_lemma)
unfolding cfg_to_dag_lemmas_def
apply (rule FInterp)
apply (rule Aux)
apply (rule dag_lemma_assms_same)
unfolding state_well_typed_def
apply (intro conjI)
using ParamsLocal apply simp
using ConstsGlobal apply simp
using ConstsGlobal OldGlobal apply simp
using BinderNs apply simp
apply (rule nested_loop2_passification_proof.glue_proof.end_to_end)
unfolding glue_proof_def
apply (intro conjI)
apply assumption
using VC apply simp
using Closed apply simp
using NonEmptyTypes apply simp
apply (rule FInterp)
using Axioms apply simp
using ParamsLocal apply simp
using ConstsGlobal apply simp
using BinderNs apply simp
using OldGlobal apply simp
using Precondition apply simp
done
qed



end
