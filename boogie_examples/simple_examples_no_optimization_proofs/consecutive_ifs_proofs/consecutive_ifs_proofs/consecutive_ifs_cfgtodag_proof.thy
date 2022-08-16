theory consecutive_ifs_cfgtodag_proof
imports Boogie_Lang.Semantics Boogie_Lang.Util Boogie_Lang.BackedgeElim Boogie_Lang.TypingML consecutive_ifs_before_ast_to_cfg_prog consecutive_ifs_before_cfg_to_dag_prog consecutive_ifs_before_passive_prog consecutive_ifs_passification_proof consecutive_ifs_vcphase_proof
begin
locale cfg_to_dag_lemmas = 
fixes A :: "(('a)absval_ty_fun)" and \<Gamma> :: "(('a)fun_interp)"
assumes 
Wf_Fun: "(fun_interp_wf A consecutive_ifs_before_ast_to_cfg_prog.fdecls \<Gamma>)"
begin

abbreviation \<Lambda>1
  where
    "\<Lambda>1  \<equiv> ((append consecutive_ifs_before_ast_to_cfg_prog.constants_vdecls consecutive_ifs_before_ast_to_cfg_prog.globals_vdecls),(append consecutive_ifs_before_ast_to_cfg_prog.params_vdecls consecutive_ifs_before_ast_to_cfg_prog.locals_vdecls))"
declare Nat.One_nat_def[simp del]

lemma cfg_block_GeneratedUnifiedExit:
assumes 
"(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_passive_prog.proc_body ((Inl 0),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(state_well_typed A \<Lambda>1 [] ns2)"
shows "(expr_all_sat A \<Lambda>1 \<Gamma> [] ns2 consecutive_ifs_before_ast_to_cfg_prog.post)"
unfolding expr_all_sat_def consecutive_ifs_before_ast_to_cfg_prog.post_def 
apply (rule cfg_dag_rel_post_invs_3)
apply (erule assms(1))
apply (rule consecutive_ifs_before_passive_prog.node_0)
apply simp
unfolding consecutive_ifs_before_passive_prog.block_0_def
by cfg_dag_rel_tac_single+

lemma block_anon7_Then:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_cfg_to_dag_prog.block_4 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_passive_prog.block_1 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [] consecutive_ifs_before_passive_prog.block_1 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding consecutive_ifs_before_cfg_to_dag_prog.block_4_def consecutive_ifs_before_passive_prog.block_1_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
done

lemma cfg_block_anon7_Then:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_cfg_to_dag_prog.proc_body ((Inl 4),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_passive_prog.proc_body ((Inl 1),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] consecutive_ifs_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_return_2[OF Red])
apply (rule consecutive_ifs_before_cfg_to_dag_prog.node_4)
apply (rule consecutive_ifs_before_passive_prog.node_1)
apply (erule DagVerifies)
apply (rule DagAssms)
apply (erule block_anon7_Then)
apply assumption+
apply (rule consecutive_ifs_before_cfg_to_dag_prog.outEdges_4)
apply (rule consecutive_ifs_before_passive_prog.outEdges_1)
apply (erule cfg_block_GeneratedUnifiedExit)
by assumption


lemma block_anon7_Else:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_cfg_to_dag_prog.block_5 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_passive_prog.block_2 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [] consecutive_ifs_before_passive_prog.block_2 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding consecutive_ifs_before_cfg_to_dag_prog.block_5_def consecutive_ifs_before_passive_prog.block_2_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
done

lemma cfg_block_anon7_Else:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_cfg_to_dag_prog.proc_body ((Inl 5),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_passive_prog.proc_body ((Inl 2),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] consecutive_ifs_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_return_2[OF Red])
apply (rule consecutive_ifs_before_cfg_to_dag_prog.node_5)
apply (rule consecutive_ifs_before_passive_prog.node_2)
apply (erule DagVerifies)
apply (rule DagAssms)
apply (erule block_anon7_Else)
apply assumption+
apply (rule consecutive_ifs_before_cfg_to_dag_prog.outEdges_5)
apply (rule consecutive_ifs_before_passive_prog.outEdges_2)
apply (erule cfg_block_GeneratedUnifiedExit)
by assumption


lemma block_anon3:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_cfg_to_dag_prog.block_3 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_passive_prog.block_3 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [] consecutive_ifs_before_passive_prog.block_3 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding consecutive_ifs_before_cfg_to_dag_prog.block_3_def consecutive_ifs_before_passive_prog.block_3_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
done

lemma cfg_block_anon3:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_cfg_to_dag_prog.proc_body ((Inl 3),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_passive_prog.proc_body ((Inl 3),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] consecutive_ifs_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_1[OF Red _ _ DagVerifies DagAssms])
apply (rule consecutive_ifs_before_cfg_to_dag_prog.node_3)
apply (rule consecutive_ifs_before_passive_prog.node_3)
apply (assumption+)
apply (rule block_anon3)
apply (assumption+)
apply ((simp add:consecutive_ifs_before_cfg_to_dag_prog.outEdges_3))
apply ((simp add:consecutive_ifs_before_cfg_to_dag_prog.outEdges_3))
apply (erule member_elim)
apply simp
apply (erule allE[where x=1])
apply ((simp add:consecutive_ifs_before_passive_prog.outEdges_3))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_anon7_Then)
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
apply (erule allE[where x=2])
apply ((simp add:consecutive_ifs_before_passive_prog.outEdges_3))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_anon7_Else)
apply simp
unfolding dag_lemma_assms_def
apply (intro conjI)
apply simp
apply simp
apply (fastforce)
apply (simp)
apply (simp)
by (simp add: member_rec(2))


lemma block_anon6_Then:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_cfg_to_dag_prog.block_1 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_passive_prog.block_4 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [] consecutive_ifs_before_passive_prog.block_4 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding consecutive_ifs_before_cfg_to_dag_prog.block_1_def consecutive_ifs_before_passive_prog.block_4_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
done

lemma cfg_block_anon6_Then:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_cfg_to_dag_prog.proc_body ((Inl 1),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_passive_prog.proc_body ((Inl 4),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] consecutive_ifs_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_1[OF Red _ _ DagVerifies DagAssms])
apply (rule consecutive_ifs_before_cfg_to_dag_prog.node_1)
apply (rule consecutive_ifs_before_passive_prog.node_4)
apply (assumption+)
apply (rule block_anon6_Then)
apply (assumption+)
apply ((simp add:consecutive_ifs_before_cfg_to_dag_prog.outEdges_1))
apply ((simp add:consecutive_ifs_before_cfg_to_dag_prog.outEdges_1))
apply (erule member_elim)
apply simp
apply (erule allE[where x=3])
apply ((simp add:consecutive_ifs_before_passive_prog.outEdges_4))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_anon3)
apply simp
unfolding dag_lemma_assms_def
apply (intro conjI)
apply simp
apply simp
apply (fastforce)
apply (simp)
apply (simp)
by (simp add: member_rec(2))


lemma block_anon6_Else:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_cfg_to_dag_prog.block_2 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_passive_prog.block_5 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [] consecutive_ifs_before_passive_prog.block_5 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding consecutive_ifs_before_cfg_to_dag_prog.block_2_def consecutive_ifs_before_passive_prog.block_5_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
done

lemma cfg_block_anon6_Else:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_cfg_to_dag_prog.proc_body ((Inl 2),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_passive_prog.proc_body ((Inl 5),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] consecutive_ifs_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_1[OF Red _ _ DagVerifies DagAssms])
apply (rule consecutive_ifs_before_cfg_to_dag_prog.node_2)
apply (rule consecutive_ifs_before_passive_prog.node_5)
apply (assumption+)
apply (rule block_anon6_Else)
apply (assumption+)
apply ((simp add:consecutive_ifs_before_cfg_to_dag_prog.outEdges_2))
apply ((simp add:consecutive_ifs_before_cfg_to_dag_prog.outEdges_2))
apply (erule member_elim)
apply simp
apply (erule allE[where x=3])
apply ((simp add:consecutive_ifs_before_passive_prog.outEdges_5))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_anon3)
apply simp
unfolding dag_lemma_assms_def
apply (intro conjI)
apply simp
apply simp
apply (fastforce)
apply (simp)
apply (simp)
by (simp add: member_rec(2))


lemma block_anon0:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_cfg_to_dag_prog.block_0 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_passive_prog.block_6 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [] consecutive_ifs_before_passive_prog.block_6 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding consecutive_ifs_before_cfg_to_dag_prog.block_0_def consecutive_ifs_before_passive_prog.block_6_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
done

lemma cfg_block_anon0:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_passive_prog.proc_body ((Inl 6),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] consecutive_ifs_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_1[OF Red _ _ DagVerifies DagAssms])
apply (rule consecutive_ifs_before_cfg_to_dag_prog.node_0)
apply (rule consecutive_ifs_before_passive_prog.node_6)
apply (assumption+)
apply (rule block_anon0)
apply (assumption+)
apply ((simp add:consecutive_ifs_before_cfg_to_dag_prog.outEdges_0))
apply ((simp add:consecutive_ifs_before_cfg_to_dag_prog.outEdges_0))
apply (erule member_elim)
apply simp
apply (erule allE[where x=4])
apply ((simp add:consecutive_ifs_before_passive_prog.outEdges_6))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_anon6_Then)
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
apply (erule allE[where x=5])
apply ((simp add:consecutive_ifs_before_passive_prog.outEdges_6))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_anon6_Else)
apply simp
unfolding dag_lemma_assms_def
apply (intro conjI)
apply simp
apply simp
apply (fastforce)
apply (simp)
apply (simp)
by (simp add: member_rec(2))


lemma cfg_block_0:
assumes 
"(\<forall> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_passive_prog.proc_body ((Inl 7),(Normal ns2)) (m2',s2')) \<longrightarrow> (s2' \<noteq> Failure)))" and 
"(nstate_same_on \<Lambda>1 ns1 ns2 {})" and 
"(state_well_typed A \<Lambda>1 [] ns1)" and 
"(state_well_typed A \<Lambda>1 [] ns2)" and 
"((\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_passive_prog.proc_body ((Inl 6),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure))) \<Longrightarrow> R)"
shows "R"
using assms
apply (rule cfg_dag_empty_propagate_helper)
apply (assumption, simp)
apply ((simp add:consecutive_ifs_before_passive_prog.outEdges_7))
by ((simp add:consecutive_ifs_before_passive_prog.node_7 consecutive_ifs_before_passive_prog.block_7_def))

lemma entry_lemma:
assumes 
"(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) j (m',s'))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
"(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] consecutive_ifs_before_passive_prog.proc_body ((Inl 8),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(expr_all_sat A \<Lambda>1 \<Gamma> [] ns2 consecutive_ifs_before_ast_to_cfg_prog.pres)"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] consecutive_ifs_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_entry)
apply (rule consecutive_ifs_before_passive_prog.node_8)
apply (erule assms(3))
apply (rule assms(2))
unfolding consecutive_ifs_before_passive_prog.block_8_def
apply (rule assume_pres_normal[where ?es=consecutive_ifs_before_ast_to_cfg_prog.pres])
apply (rule assms(4))
unfolding consecutive_ifs_before_ast_to_cfg_prog.pres_def
apply simp
apply (rule consecutive_ifs_before_passive_prog.outEdges_8)
apply ((simp add:consecutive_ifs_before_passive_prog.node_7 consecutive_ifs_before_passive_prog.block_7_def))
apply (rule consecutive_ifs_before_passive_prog.outEdges_7)
by (rule cfg_block_anon0[OF assms(1-2)])


end

abbreviation \<Lambda>0
  where
    "\<Lambda>0  \<equiv> ((append consecutive_ifs_before_ast_to_cfg_prog.constants_vdecls consecutive_ifs_before_ast_to_cfg_prog.globals_vdecls),(append consecutive_ifs_before_ast_to_cfg_prog.params_vdecls consecutive_ifs_before_ast_to_cfg_prog.locals_vdecls))"
lemma end_to_end_theorem_aux:
assumes 
Red: "(red_cfg_multi A M ((append consecutive_ifs_before_ast_to_cfg_prog.constants_vdecls consecutive_ifs_before_ast_to_cfg_prog.globals_vdecls),(append consecutive_ifs_before_ast_to_cfg_prog.params_vdecls consecutive_ifs_before_ast_to_cfg_prog.locals_vdecls)) \<Gamma> [] consecutive_ifs_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns)) (m',s'))" and 
VC: "(\<And> (vc_x::int) (vc_x_0::int) (vc_x_1::int). (vc.vc_anon0 ))" and 
Closed: "(\<And> v. (closed ((type_of_val A) v)))" and 
NonEmptyTypes: "(\<And> t. ((closed t) \<Longrightarrow> (\<exists> v. (((type_of_val A) v) = t))))" and 
FInterp: "(fun_interp_wf A consecutive_ifs_before_ast_to_cfg_prog.fdecls \<Gamma>)" and 
Axioms: "(axiom_assm A \<Gamma> consecutive_ifs_before_ast_to_cfg_prog.constants_vdecls (ns::(('a)nstate)) consecutive_ifs_before_ast_to_cfg_prog.axioms)" and 
Precondition: "(expr_all_sat A \<Lambda>0 \<Gamma> [] ns consecutive_ifs_before_ast_to_cfg_prog.pres)" and 
ParamsLocal: "(state_typ_wf A [] (local_state ns) (snd \<Lambda>0))" and 
ConstsGlobal: "(state_typ_wf A [] (global_state ns) (fst \<Lambda>0))" and 
OldGlobal: "((global_state ns) = (old_global_state ns))" and 
BinderNs: "((binder_state ns) = Map.empty)"
shows "(Semantics.valid_configuration A \<Lambda>0 \<Gamma> [] consecutive_ifs_before_ast_to_cfg_prog.post m' s')"
proof -
from Red obtain j where Aux:"(red_cfg_k_step A M ((append consecutive_ifs_before_ast_to_cfg_prog.constants_vdecls consecutive_ifs_before_ast_to_cfg_prog.globals_vdecls),(append consecutive_ifs_before_ast_to_cfg_prog.params_vdecls consecutive_ifs_before_ast_to_cfg_prog.locals_vdecls)) \<Gamma> [] consecutive_ifs_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns)) j (m',s'))"
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
apply (rule consecutive_ifs_passification_proof.glue_proof.end_to_end)
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
