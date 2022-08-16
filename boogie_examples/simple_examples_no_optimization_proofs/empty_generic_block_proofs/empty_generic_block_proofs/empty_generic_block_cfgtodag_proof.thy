theory empty_generic_block_cfgtodag_proof
imports Boogie_Lang.Semantics Boogie_Lang.Util Boogie_Lang.BackedgeElim Boogie_Lang.TypingML empty_generic_block_before_ast_to_cfg_prog empty_generic_block_before_cfg_to_dag_prog empty_generic_block_before_passive_prog empty_generic_block_passification_proof empty_generic_block_vcphase_proof
begin
locale cfg_to_dag_lemmas = 
fixes A :: "(('a)absval_ty_fun)" and \<Gamma> :: "(('a)fun_interp)"
assumes 
Wf_Fun: "(fun_interp_wf A empty_generic_block_before_ast_to_cfg_prog.fdecls \<Gamma>)"
begin

abbreviation \<Lambda>1
  where
    "\<Lambda>1  \<equiv> ((append empty_generic_block_before_ast_to_cfg_prog.constants_vdecls empty_generic_block_before_ast_to_cfg_prog.globals_vdecls),(append empty_generic_block_before_ast_to_cfg_prog.params_vdecls empty_generic_block_before_ast_to_cfg_prog.locals_vdecls))"
declare Nat.One_nat_def[simp del]

lemma block_label2:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] empty_generic_block_before_cfg_to_dag_prog.block_2 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] empty_generic_block_before_passive_prog.block_0 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [] empty_generic_block_before_passive_prog.block_0 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding empty_generic_block_before_cfg_to_dag_prog.block_2_def empty_generic_block_before_passive_prog.block_0_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
done

lemma cfg_block_label2:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] empty_generic_block_before_cfg_to_dag_prog.proc_body ((Inl 2),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] empty_generic_block_before_passive_prog.proc_body ((Inl 0),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] empty_generic_block_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_return_1[OF assms(1)])
apply (rule empty_generic_block_before_cfg_to_dag_prog.node_2)
apply (rule empty_generic_block_before_passive_prog.node_0)
apply (erule DagVerifies)
apply (rule DagAssms)
unfolding empty_generic_block_before_ast_to_cfg_prog.post_def
apply (rule block_label2)
apply assumption+
by (rule empty_generic_block_before_cfg_to_dag_prog.outEdges_2)


lemma block_label1:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] empty_generic_block_before_cfg_to_dag_prog.block_1 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] empty_generic_block_before_passive_prog.block_1 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [] empty_generic_block_before_passive_prog.block_1 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding empty_generic_block_before_cfg_to_dag_prog.block_1_def empty_generic_block_before_passive_prog.block_1_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
done

lemma cfg_block_label1:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] empty_generic_block_before_cfg_to_dag_prog.proc_body ((Inl 1),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] empty_generic_block_before_passive_prog.proc_body ((Inl 1),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] empty_generic_block_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_1[OF Red _ _ DagVerifies DagAssms])
apply (rule empty_generic_block_before_cfg_to_dag_prog.node_1)
apply (rule empty_generic_block_before_passive_prog.node_1)
apply (assumption+)
apply (rule block_label1)
apply (assumption+)
apply ((simp add:empty_generic_block_before_cfg_to_dag_prog.outEdges_1))
apply ((simp add:empty_generic_block_before_cfg_to_dag_prog.outEdges_1))
apply (erule member_elim)
apply simp
apply (erule allE[where x=0])
apply ((simp add:empty_generic_block_before_passive_prog.outEdges_1))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_label2)
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
"(red_cmd_list A M \<Lambda>1 \<Gamma> [] empty_generic_block_before_cfg_to_dag_prog.block_0 (Normal ns1) s')" and 
"(\<And> s2'. ((red_cmd_list A M \<Lambda>1 \<Gamma> [] empty_generic_block_before_passive_prog.block_2 (Normal ns2) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)"
shows "(dag_lemma_conclusion A M \<Lambda>1 \<Gamma> [] [] empty_generic_block_before_passive_prog.block_2 ns2 s' False)"
using assms
apply (rule dag_rel_block_lemma_compact, simp)
unfolding empty_generic_block_before_cfg_to_dag_prog.block_0_def empty_generic_block_before_passive_prog.block_2_def
apply cfg_dag_rel_tac_single+
apply simp
apply simp
done

lemma cfg_block_anon0:
assumes 
Red: "(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] empty_generic_block_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) j (m',s'))" and 
DagAssms: "(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
DagVerifies: "(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] empty_generic_block_before_passive_prog.proc_body ((Inl 2),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] empty_generic_block_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_1[OF Red _ _ DagVerifies DagAssms])
apply (rule empty_generic_block_before_cfg_to_dag_prog.node_0)
apply (rule empty_generic_block_before_passive_prog.node_2)
apply (assumption+)
apply (rule block_anon0)
apply (assumption+)
apply ((simp add:empty_generic_block_before_cfg_to_dag_prog.outEdges_0))
apply ((simp add:empty_generic_block_before_cfg_to_dag_prog.outEdges_0))
apply (erule member_elim)
apply simp
apply (erule allE[where x=1])
apply ((simp add:empty_generic_block_before_passive_prog.outEdges_2))
apply ((simp add:member_rec(1)))
apply (rule cfg_block_label1)
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
"(\<forall> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] empty_generic_block_before_passive_prog.proc_body ((Inl 3),(Normal ns2)) (m2',s2')) \<longrightarrow> (s2' \<noteq> Failure)))" and 
"(nstate_same_on \<Lambda>1 ns1 ns2 {})" and 
"(state_well_typed A \<Lambda>1 [] ns1)" and 
"(state_well_typed A \<Lambda>1 [] ns2)" and 
"((\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] empty_generic_block_before_passive_prog.proc_body ((Inl 2),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure))) \<Longrightarrow> R)"
shows "R"
using assms
apply (rule cfg_dag_empty_propagate_helper)
apply (assumption, simp)
apply ((simp add:empty_generic_block_before_passive_prog.outEdges_3))
by ((simp add:empty_generic_block_before_passive_prog.node_3 empty_generic_block_before_passive_prog.block_3_def))

lemma entry_lemma:
assumes 
"(red_cfg_k_step A M \<Lambda>1 \<Gamma> [] empty_generic_block_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) j (m',s'))" and 
"(dag_lemma_assms A \<Lambda>1 \<Gamma> [] [] [] ns1 ns2)" and 
"(\<And> m2' s2'. ((red_cfg_multi A M \<Lambda>1 \<Gamma> [] empty_generic_block_before_passive_prog.proc_body ((Inl 4),(Normal ns2)) (m2',s2')) \<Longrightarrow> (s2' \<noteq> Failure)))" and 
"(expr_all_sat A \<Lambda>1 \<Gamma> [] ns2 empty_generic_block_before_ast_to_cfg_prog.pres)"
shows "(Semantics.valid_configuration A \<Lambda>1 \<Gamma> [] empty_generic_block_before_ast_to_cfg_prog.post m' s')"
apply (rule cfg_dag_helper_entry)
apply (rule empty_generic_block_before_passive_prog.node_4)
apply (erule assms(3))
apply (rule assms(2))
unfolding empty_generic_block_before_passive_prog.block_4_def
apply (rule assume_pres_normal[where ?es=empty_generic_block_before_ast_to_cfg_prog.pres])
apply (rule assms(4))
unfolding empty_generic_block_before_ast_to_cfg_prog.pres_def
apply simp
apply (rule empty_generic_block_before_passive_prog.outEdges_4)
apply ((simp add:empty_generic_block_before_passive_prog.node_3 empty_generic_block_before_passive_prog.block_3_def))
apply (rule empty_generic_block_before_passive_prog.outEdges_3)
by (rule cfg_block_anon0[OF assms(1-2)])


end

abbreviation \<Lambda>0
  where
    "\<Lambda>0  \<equiv> ((append empty_generic_block_before_ast_to_cfg_prog.constants_vdecls empty_generic_block_before_ast_to_cfg_prog.globals_vdecls),(append empty_generic_block_before_ast_to_cfg_prog.params_vdecls empty_generic_block_before_ast_to_cfg_prog.locals_vdecls))"
lemma end_to_end_theorem_aux:
assumes 
Red: "(red_cfg_multi A M ((append empty_generic_block_before_ast_to_cfg_prog.constants_vdecls empty_generic_block_before_ast_to_cfg_prog.globals_vdecls),(append empty_generic_block_before_ast_to_cfg_prog.params_vdecls empty_generic_block_before_ast_to_cfg_prog.locals_vdecls)) \<Gamma> [] empty_generic_block_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns)) (m',s'))" and 
VC: "(\<And> (vc_x::int). (vc.vc_anon0 ))" and 
Closed: "(\<And> v. (closed ((type_of_val A) v)))" and 
NonEmptyTypes: "(\<And> t. ((closed t) \<Longrightarrow> (\<exists> v. (((type_of_val A) v) = t))))" and 
FInterp: "(fun_interp_wf A empty_generic_block_before_ast_to_cfg_prog.fdecls \<Gamma>)" and 
Axioms: "(axiom_assm A \<Gamma> empty_generic_block_before_ast_to_cfg_prog.constants_vdecls (ns::(('a)nstate)) empty_generic_block_before_ast_to_cfg_prog.axioms)" and 
Precondition: "(expr_all_sat A \<Lambda>0 \<Gamma> [] ns empty_generic_block_before_ast_to_cfg_prog.pres)" and 
ParamsLocal: "(state_typ_wf A [] (local_state ns) (snd \<Lambda>0))" and 
ConstsGlobal: "(state_typ_wf A [] (global_state ns) (fst \<Lambda>0))" and 
OldGlobal: "((global_state ns) = (old_global_state ns))" and 
BinderNs: "((binder_state ns) = Map.empty)"
shows "(Semantics.valid_configuration A \<Lambda>0 \<Gamma> [] empty_generic_block_before_ast_to_cfg_prog.post m' s')"
proof -
from Red obtain j where Aux:"(red_cfg_k_step A M ((append empty_generic_block_before_ast_to_cfg_prog.constants_vdecls empty_generic_block_before_ast_to_cfg_prog.globals_vdecls),(append empty_generic_block_before_ast_to_cfg_prog.params_vdecls empty_generic_block_before_ast_to_cfg_prog.locals_vdecls)) \<Gamma> [] empty_generic_block_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns)) j (m',s'))"
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
apply (rule empty_generic_block_passification_proof.glue_proof.end_to_end)
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
