theory assert_false_in_if_3_asttocfg_proof
imports Boogie_Lang.Ast Boogie_Lang.Ast_Cfg_Transformation Boogie_Lang.Semantics Boogie_Lang.Util Boogie_Lang.BackedgeElim Boogie_Lang.TypingML assert_false_in_if_3_before_ast_to_cfg_prog assert_false_in_if_3_before_cfg_to_dag_prog assert_false_in_if_3_cfgtodag_proof assert_false_in_if_3_passification_proof assert_false_in_if_3_vcphase_proof
begin
locale ast_to_cfg_lemmas = 
fixes A :: "(('a)absval_ty_fun)" and \<Gamma> :: "(('a)fun_interp)"
assumes 
Wf_Fun: "(fun_interp_wf A assert_false_in_if_3_before_ast_to_cfg_prog.fdecls \<Gamma>)"
begin

abbreviation \<Lambda>1
  where
    "\<Lambda>1  \<equiv> ((append assert_false_in_if_3_before_ast_to_cfg_prog.constants_vdecls assert_false_in_if_3_before_ast_to_cfg_prog.globals_vdecls),(append assert_false_in_if_3_before_ast_to_cfg_prog.params_vdecls assert_false_in_if_3_before_ast_to_cfg_prog.locals_vdecls))"
declare Nat.One_nat_def[simp del]

lemma rel_assert_false_in_if_3_before_ast_to_cfg_prog_bigblock_3:
assumes 
astStep: "(red_bigblock A M \<Lambda>1 \<Gamma> [] T (assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_3,cont0,(Normal ns1)) (reached_bb,reached_cont,reached_state))" and 
cfgBlockDoesntFail: "(\<And> s2'. ((red_cmd_list A M' \<Lambda>1 \<Gamma> [] assert_false_in_if_3_before_cfg_to_dag_prog.block_3 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "((reached_state \<noteq> Failure) \<and> (\<forall> ns1'. ((reached_state = (Normal ns1')) \<longrightarrow> (red_cmd_list A M' \<Lambda>1 \<Gamma> [] assert_false_in_if_3_before_cfg_to_dag_prog.block_3 (Normal ns1) (Normal ns1')))))"
apply (rule block_local_rel_generic)
apply (rule Rel_Main_test[of assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_3])
apply (simp add: assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_3_def assert_false_in_if_3_before_cfg_to_dag_prog.block_3_def)
apply ((simp add: assert_false_in_if_3_before_cfg_to_dag_prog.block_3_def)+)
apply (rule astStep)
apply (rule cfgBlockDoesntFail)
apply ((simp add: assert_false_in_if_3_before_cfg_to_dag_prog.block_3_def assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_3_def)+)
done


lemma global_rel_assert_false_in_if_3_before_ast_to_cfg_prog_bigblock_3:
assumes 
astTrace: "(red_bigblock_k_step A M \<Lambda>1 \<Gamma> [] T (assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_3,cont_3,(Normal ns1)) j (reached_bb,reached_cont,reached_state))" and 
cfgDoesntFail: "(\<And> m' s'. ((red_cfg_multi A M' \<Lambda>1 \<Gamma> [] assert_false_in_if_3_before_cfg_to_dag_prog.proc_body ((Inl 3),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)))" and 
cfgSatisfiesPosts: "(\<And> m' s'. ((red_cfg_multi A M' \<Lambda>1 \<Gamma> [] assert_false_in_if_3_before_cfg_to_dag_prog.proc_body ((Inl 3),(Normal ns1)) (m',s')) \<Longrightarrow> ((is_final_config (m',s')) \<Longrightarrow> (\<forall> ns_end. ((s' = (Normal ns_end)) \<longrightarrow> (expr_all_sat A \<Lambda>1 \<Gamma> [] ns_end assert_false_in_if_3_before_ast_to_cfg_prog.post))))))"
shows "(Ast.valid_configuration A \<Lambda>1 \<Gamma> [] assert_false_in_if_3_before_ast_to_cfg_prog.post reached_bb reached_cont reached_state)"
proof -
show ?thesis
apply (rule generic_ending_block_global_rel)
apply (rule Rel_Main_test[of assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_3])
apply (simp add: assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_3_def)
apply (simp)
apply (rule astTrace)
apply (simp add: assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_3_def)
apply (simp)
apply (simp)
apply (rule cont_3_def)
apply (rule assert_false_in_if_3_before_cfg_to_dag_prog.node_3)
apply (rule disjI1)
apply (rule assert_false_in_if_3_before_cfg_to_dag_prog.block_3_def)
apply (rule assert_false_in_if_3_before_cfg_to_dag_prog.outEdges_3)
apply (rule cfgDoesntFail)
apply (simp)
apply (rule cfgSatisfiesPosts)
apply ((simp)+)
apply (simp add: assert_false_in_if_3_before_cfg_to_dag_prog.node_3)
apply (rule rel_assert_false_in_if_3_before_ast_to_cfg_prog_bigblock_3)
apply assumption+

done
qed

lemma global_rel_assert_false_in_if_3_before_ast_to_cfg_prog_bigblock_2:
assumes 
astTrace: "(red_bigblock_k_step A M \<Lambda>1 \<Gamma> [] T (assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_2,cont_2,(Normal ns1)) j (reached_bb,reached_cont,reached_state))" and 
cfgDoesntFail: "(\<And> m' s'. ((red_cfg_multi A M' \<Lambda>1 \<Gamma> [] assert_false_in_if_3_before_cfg_to_dag_prog.proc_body ((Inl 2),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)))" and 
cfgSatisfiesPosts: "(\<And> m' s'. ((red_cfg_multi A M' \<Lambda>1 \<Gamma> [] assert_false_in_if_3_before_cfg_to_dag_prog.proc_body ((Inl 2),(Normal ns1)) (m',s')) \<Longrightarrow> ((is_final_config (m',s')) \<Longrightarrow> (\<forall> ns_end. ((s' = (Normal ns_end)) \<longrightarrow> (expr_all_sat A \<Lambda>1 \<Gamma> [] ns_end assert_false_in_if_3_before_ast_to_cfg_prog.post))))))"
shows "(Ast.valid_configuration A \<Lambda>1 \<Gamma> [] assert_false_in_if_3_before_ast_to_cfg_prog.post reached_bb reached_cont reached_state)"
proof -
show ?thesis 
apply (rule block_global_rel_generic)
apply (rule Rel_Invs[of assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_2])
apply (simp add: assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_2_def)

apply (rule astTrace)
apply (simp add: assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_2_def)
apply (rule assert_false_in_if_3_before_cfg_to_dag_prog.node_2)
apply (rule disjI1)
apply (rule assert_false_in_if_3_before_cfg_to_dag_prog.block_2_def)
apply (rule cfgDoesntFail)
apply ((simp)+)
apply (rule cfgSatisfiesPosts, blast)
apply ((simp)+)
apply (rule cont_2_def)
apply (simp add: assert_false_in_if_3_before_cfg_to_dag_prog.node_2)



apply ((erule allE[where x = 3])+)
apply ((simp add: assert_false_in_if_3_before_cfg_to_dag_prog.outEdges_2)+)
apply (simp add: member_rec(1))
apply (rule global_rel_assert_false_in_if_3_before_ast_to_cfg_prog_bigblock_3)
apply (simp)
apply blast+





done
qed

lemma rel_assert_false_in_if_3_before_ast_to_cfg_prog_bigblock_1:
assumes 
astStep: "(red_bigblock A M \<Lambda>1 \<Gamma> [] T (assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_1,cont0,(Normal ns1)) (reached_bb,reached_cont,reached_state))" and 
cfgBlockDoesntFail: "(\<And> s2'. ((red_cmd_list A M' \<Lambda>1 \<Gamma> [] assert_false_in_if_3_before_cfg_to_dag_prog.block_1 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "((reached_state \<noteq> Failure) \<and> (\<forall> ns1'. ((reached_state = (Normal ns1')) \<longrightarrow> (red_cmd_list A M' \<Lambda>1 \<Gamma> [] assert_false_in_if_3_before_cfg_to_dag_prog.block_1 (Normal ns1) (Normal ns1')))))"
apply (rule block_local_rel_generic)
apply (rule Rel_Main_test[of assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_1])
apply (simp add: assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_1_def assert_false_in_if_3_before_cfg_to_dag_prog.block_1_def)
apply ((simp add: assert_false_in_if_3_before_cfg_to_dag_prog.block_1_def)+)
apply (rule astStep)
apply (rule cfgBlockDoesntFail)
apply ((simp add: assert_false_in_if_3_before_cfg_to_dag_prog.block_1_def assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_1_def)+)
done


lemma global_rel_assert_false_in_if_3_before_ast_to_cfg_prog_bigblock_1:
assumes 
astTrace: "(red_bigblock_k_step A M \<Lambda>1 \<Gamma> [] T (assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_1,cont_1,(Normal ns1)) j (reached_bb,reached_cont,reached_state))" and 
cfgDoesntFail: "(\<And> m' s'. ((red_cfg_multi A M' \<Lambda>1 \<Gamma> [] assert_false_in_if_3_before_cfg_to_dag_prog.proc_body ((Inl 1),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)))" and 
cfgSatisfiesPosts: "(\<And> m' s'. ((red_cfg_multi A M' \<Lambda>1 \<Gamma> [] assert_false_in_if_3_before_cfg_to_dag_prog.proc_body ((Inl 1),(Normal ns1)) (m',s')) \<Longrightarrow> ((is_final_config (m',s')) \<Longrightarrow> (\<forall> ns_end. ((s' = (Normal ns_end)) \<longrightarrow> (expr_all_sat A \<Lambda>1 \<Gamma> [] ns_end assert_false_in_if_3_before_ast_to_cfg_prog.post))))))"
shows "(Ast.valid_configuration A \<Lambda>1 \<Gamma> [] assert_false_in_if_3_before_ast_to_cfg_prog.post reached_bb reached_cont reached_state)"
proof -
show ?thesis 
apply (rule block_global_rel_generic)
apply (rule Rel_Main_test[of assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_1])
apply (simp add: assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_1_def)
apply (simp)
apply (rule astTrace)
apply (simp add: assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_1_def)
apply (rule assert_false_in_if_3_before_cfg_to_dag_prog.node_1)
apply (rule disjI1)
apply (rule assert_false_in_if_3_before_cfg_to_dag_prog.block_1_def)
apply (rule cfgDoesntFail)
apply ((simp)+)
apply (rule cfgSatisfiesPosts, blast)
apply ((simp)+)
apply (rule cont_1_def)
apply (simp add: assert_false_in_if_3_before_cfg_to_dag_prog.node_1)
apply (rule rel_assert_false_in_if_3_before_ast_to_cfg_prog_bigblock_1)
apply assumption
apply (simp)
apply ((erule allE[where x = 3])+)
apply ((simp add: assert_false_in_if_3_before_cfg_to_dag_prog.outEdges_1)+)
apply (simp add: member_rec(1))
apply (rule global_rel_assert_false_in_if_3_before_ast_to_cfg_prog_bigblock_3)
apply (simp)
apply blast+





done
qed

lemma rel_assert_false_in_if_3_before_ast_to_cfg_prog_bigblock_0:
assumes 
astStep: "(red_bigblock A M \<Lambda>1 \<Gamma> [] T (assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_0,cont0,(Normal ns1)) (reached_bb,reached_cont,reached_state))" and 
cfgBlockDoesntFail: "(\<And> s2'. ((red_cmd_list A M' \<Lambda>1 \<Gamma> [] assert_false_in_if_3_before_cfg_to_dag_prog.block_0 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "((reached_state \<noteq> Failure) \<and> (\<forall> ns1'. ((reached_state = (Normal ns1')) \<longrightarrow> (red_cmd_list A M' \<Lambda>1 \<Gamma> [] assert_false_in_if_3_before_cfg_to_dag_prog.block_0 (Normal ns1) (Normal ns1')))))"
apply (rule block_local_rel_generic)
apply (rule Rel_Main_test[of assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_0])
apply (simp add: assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_0_def assert_false_in_if_3_before_cfg_to_dag_prog.block_0_def)
apply ((simp add: assert_false_in_if_3_before_cfg_to_dag_prog.block_0_def)+)
apply (rule astStep)
apply (rule cfgBlockDoesntFail)
apply ((simp add: assert_false_in_if_3_before_cfg_to_dag_prog.block_0_def assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_0_def)+)
done


lemma global_rel_assert_false_in_if_3_before_ast_to_cfg_prog_bigblock_0:
assumes 
astTrace: "(red_bigblock_k_step A M \<Lambda>1 \<Gamma> [] T (assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_0,cont_0,(Normal ns1)) j (reached_bb,reached_cont,reached_state))" and 
cfgDoesntFail: "(\<And> m' s'. ((red_cfg_multi A M' \<Lambda>1 \<Gamma> [] assert_false_in_if_3_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)))" and 
cfgSatisfiesPosts: "(\<And> m' s'. ((red_cfg_multi A M' \<Lambda>1 \<Gamma> [] assert_false_in_if_3_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) (m',s')) \<Longrightarrow> ((is_final_config (m',s')) \<Longrightarrow> (\<forall> ns_end. ((s' = (Normal ns_end)) \<longrightarrow> (expr_all_sat A \<Lambda>1 \<Gamma> [] ns_end assert_false_in_if_3_before_ast_to_cfg_prog.post))))))"
shows "(Ast.valid_configuration A \<Lambda>1 \<Gamma> [] assert_false_in_if_3_before_ast_to_cfg_prog.post reached_bb reached_cont reached_state)"
proof -
show ?thesis
apply (rule block_global_rel_if_successor)
apply (rule Rel_Main_test[of assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_0 _ assert_false_in_if_3_before_cfg_to_dag_prog.block_0])
apply (simp add: assert_false_in_if_3_before_cfg_to_dag_prog.block_0_def assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_0_def)
apply (simp add: assert_false_in_if_3_before_cfg_to_dag_prog.block_0_def)
apply (rule astTrace)
apply (simp add: assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_0_def)
apply (rule assert_false_in_if_3_before_cfg_to_dag_prog.node_0)
apply (rule disjI1)



apply (simp add: assert_false_in_if_3_before_cfg_to_dag_prog.block_0_def)







apply (rule cfgDoesntFail, simp)
apply (rule cfgSatisfiesPosts, blast)
apply ((simp)+)
apply (simp add: assert_false_in_if_3_before_cfg_to_dag_prog.node_0)
apply (rule rel_assert_false_in_if_3_before_ast_to_cfg_prog_bigblock_0)
apply (simp add: assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_0_def)
apply ((simp)+)


apply (rule disjE, simp)
apply ((erule allE[where x = 1])+)
apply ((simp add: assert_false_in_if_3_before_cfg_to_dag_prog.outEdges_0)+)
apply (simp add: member_rec(1))
apply (rule conjE)
apply ((simp)+)
apply (rule global_rel_assert_false_in_if_3_before_ast_to_cfg_prog_bigblock_1)
apply (simp add: cont_0_def assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_1_def cont_1_def )
apply blast+






apply ((erule allE[where x = 2])+)
apply ((simp add: assert_false_in_if_3_before_cfg_to_dag_prog.outEdges_0)+)
apply (simp add: member_rec(1))
apply (rule conjE)
apply ((simp)+)
apply (rule global_rel_assert_false_in_if_3_before_ast_to_cfg_prog_bigblock_2)
apply (simp add: cont_0_def assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_2_def cont_2_def )
apply blast+





done
qed


end

abbreviation \<Lambda>0
  where
    "\<Lambda>0  \<equiv> ((append assert_false_in_if_3_before_ast_to_cfg_prog.constants_vdecls assert_false_in_if_3_before_ast_to_cfg_prog.globals_vdecls),(append assert_false_in_if_3_before_ast_to_cfg_prog.params_vdecls assert_false_in_if_3_before_ast_to_cfg_prog.locals_vdecls))"
lemma end_to_end_theorem_aux_ast:
assumes 
Red: "(rtranclp (red_bigblock A M ((append assert_false_in_if_3_before_ast_to_cfg_prog.constants_vdecls assert_false_in_if_3_before_ast_to_cfg_prog.globals_vdecls),(append assert_false_in_if_3_before_ast_to_cfg_prog.params_vdecls assert_false_in_if_3_before_ast_to_cfg_prog.locals_vdecls)) \<Gamma> [] T) (assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_0,cont_0,(Normal ns)) (reached_bb,reached_cont,reached_state))" and 
VC: "(\<And> (vc_x::int) (vc_x_0::int). (vc.vc_anon0 ))" and 
Closed: "(\<And> v. (closed ((type_of_val A) v)))" and 
NonEmptyTypes: "(\<And> t. ((closed t) \<Longrightarrow> (\<exists> v. (((type_of_val A) v) = t))))" and 
FInterp: "(fun_interp_wf A assert_false_in_if_3_before_ast_to_cfg_prog.fdecls \<Gamma>)" and 
Axioms: "(axiom_assm A \<Gamma> assert_false_in_if_3_before_ast_to_cfg_prog.constants_vdecls (ns::(('a)nstate)) assert_false_in_if_3_before_ast_to_cfg_prog.axioms)" and 
Precondition: "(expr_all_sat A \<Lambda>0 \<Gamma> [] ns assert_false_in_if_3_before_ast_to_cfg_prog.pres)" and 
ParamsLocal: "(state_typ_wf A [] (local_state ns) (snd \<Lambda>0))" and 
ConstsGlobal: "(state_typ_wf A [] (global_state ns) (fst \<Lambda>0))" and 
OldGlobal: "((global_state ns) = (old_global_state ns))" and 
BinderNs: "((binder_state ns) = Map.empty)"
shows "(Ast.valid_configuration A \<Lambda>0 \<Gamma> [] assert_false_in_if_3_before_ast_to_cfg_prog.post reached_bb reached_cont reached_state)"
proof -
from Red obtain j where Aux:"(red_bigblock_k_step A M ((append assert_false_in_if_3_before_ast_to_cfg_prog.constants_vdecls assert_false_in_if_3_before_ast_to_cfg_prog.globals_vdecls),(append assert_false_in_if_3_before_ast_to_cfg_prog.params_vdecls assert_false_in_if_3_before_ast_to_cfg_prog.locals_vdecls)) \<Gamma> [] T (assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_0,cont_0,(Normal ns)) j (reached_bb,reached_cont,reached_state))"
by (meson rtranclp_imp_relpowp)
show ?thesis
apply (rule ast_to_cfg_lemmas.global_rel_assert_false_in_if_3_before_ast_to_cfg_prog_bigblock_0)
unfolding ast_to_cfg_lemmas_def
apply (rule FInterp)
apply (rule Aux)
apply (rule valid_config_implies_not_failure)
apply (rule end_to_end_theorem_aux)
apply (simp add: assert_false_in_if_3_before_ast_to_cfg_prog.params_vdecls_def assert_false_in_if_3_before_ast_to_cfg_prog.locals_vdecls_def assert_false_in_if_3_before_cfg_to_dag_prog.params_vdecls_def assert_false_in_if_3_before_cfg_to_dag_prog.locals_vdecls_def)
using VC apply simp
using Closed apply simp
using NonEmptyTypes apply simp
apply (rule FInterp)
using Axioms apply simp
using Precondition apply (simp add: assert_false_in_if_3_before_ast_to_cfg_prog.params_vdecls_def assert_false_in_if_3_before_ast_to_cfg_prog.locals_vdecls_def assert_false_in_if_3_before_cfg_to_dag_prog.params_vdecls_def assert_false_in_if_3_before_cfg_to_dag_prog.locals_vdecls_def assert_false_in_if_3_before_ast_to_cfg_prog.pres_def assert_false_in_if_3_before_cfg_to_dag_prog.pres_def)
using ParamsLocal apply (simp add: assert_false_in_if_3_before_ast_to_cfg_prog.params_vdecls_def assert_false_in_if_3_before_ast_to_cfg_prog.locals_vdecls_def assert_false_in_if_3_before_cfg_to_dag_prog.params_vdecls_def assert_false_in_if_3_before_cfg_to_dag_prog.locals_vdecls_def)
using ConstsGlobal apply (simp add: assert_false_in_if_3_before_ast_to_cfg_prog.params_vdecls_def assert_false_in_if_3_before_ast_to_cfg_prog.locals_vdecls_def assert_false_in_if_3_before_cfg_to_dag_prog.params_vdecls_def assert_false_in_if_3_before_cfg_to_dag_prog.locals_vdecls_def)
using OldGlobal apply simp
using BinderNs apply simp
apply (rule valid_config_implies_satisfied_posts)
apply (rule end_to_end_theorem_aux)
apply (simp add: assert_false_in_if_3_before_ast_to_cfg_prog.params_vdecls_def assert_false_in_if_3_before_ast_to_cfg_prog.locals_vdecls_def assert_false_in_if_3_before_cfg_to_dag_prog.params_vdecls_def assert_false_in_if_3_before_cfg_to_dag_prog.locals_vdecls_def)
using VC apply simp
using Closed apply simp
using NonEmptyTypes apply simp
apply (rule FInterp)
using Axioms apply simp
using Precondition apply (simp add: assert_false_in_if_3_before_ast_to_cfg_prog.params_vdecls_def assert_false_in_if_3_before_ast_to_cfg_prog.locals_vdecls_def assert_false_in_if_3_before_cfg_to_dag_prog.params_vdecls_def assert_false_in_if_3_before_cfg_to_dag_prog.locals_vdecls_def assert_false_in_if_3_before_ast_to_cfg_prog.pres_def assert_false_in_if_3_before_cfg_to_dag_prog.pres_def)
using ParamsLocal apply (simp add: assert_false_in_if_3_before_ast_to_cfg_prog.params_vdecls_def assert_false_in_if_3_before_ast_to_cfg_prog.locals_vdecls_def assert_false_in_if_3_before_cfg_to_dag_prog.params_vdecls_def assert_false_in_if_3_before_cfg_to_dag_prog.locals_vdecls_def)
using ConstsGlobal apply (simp add: assert_false_in_if_3_before_ast_to_cfg_prog.params_vdecls_def assert_false_in_if_3_before_ast_to_cfg_prog.locals_vdecls_def assert_false_in_if_3_before_cfg_to_dag_prog.params_vdecls_def assert_false_in_if_3_before_cfg_to_dag_prog.locals_vdecls_def)
using OldGlobal apply simp
using BinderNs apply simp+
done
qed


lemma initialization:
assumes 
"(rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T) (init_ast [bigblock_0,bigblock_3] ns) (reached_bb,reached_cont,reached_state))"
shows "(rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T) (assert_false_in_if_3_before_ast_to_cfg_prog.bigblock_0,cont_0,(Normal ns)) (reached_bb,reached_cont,reached_state))"
using assms
by (simp add: cont_0_def cont_3_def )

lemma end_to_end_theorem_ast:
assumes 
VC: "(\<And> (vc_x::int) (vc_x_0::int). (vc.vc_anon0 ))"
shows "(\<And> A. (proc_is_correct (A::(('a)absval_ty_fun)) assert_false_in_if_3_before_ast_to_cfg_prog.fdecls assert_false_in_if_3_before_ast_to_cfg_prog.constants_vdecls assert_false_in_if_3_before_ast_to_cfg_prog.globals_vdecls assert_false_in_if_3_before_ast_to_cfg_prog.axioms assert_false_in_if_3_before_ast_to_cfg_prog.ast_proc Ast.proc_body_satisfies_spec))"
apply (rule end_to_end_util2[OF end_to_end_theorem_aux_ast])
apply (rule initialization)
unfolding assert_false_in_if_3_before_ast_to_cfg_prog.ast_proc_def
apply assumption using VC apply simp  apply assumption+
by (simp_all add: exprs_to_only_checked_spec_1 exprs_to_only_checked_spec_2 assert_false_in_if_3_before_ast_to_cfg_prog.ast_proc_def assert_false_in_if_3_before_ast_to_cfg_prog.proc_body_def)


end
