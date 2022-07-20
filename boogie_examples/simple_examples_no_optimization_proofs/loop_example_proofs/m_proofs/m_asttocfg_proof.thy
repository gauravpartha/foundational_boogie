theory m_asttocfg_proof
imports Boogie_Lang.Ast Boogie_Lang.Ast_Cfg_Transformation Boogie_Lang.Semantics Boogie_Lang.Util Boogie_Lang.BackedgeElim Boogie_Lang.TypingML m_before_ast_to_cfg_prog m_before_cfg_to_dag_prog m_cfgtodag_proof m_passification_proof m_vcphase_proof
begin
locale ast_to_cfg_lemmas = 
fixes A :: "(('a)absval_ty_fun)" and \<Gamma> :: "(('a)fun_interp)"
assumes 
Wf_Fun: "(fun_interp_wf A m_before_ast_to_cfg_prog.fdecls \<Gamma>)"
begin

abbreviation \<Lambda>1
  where
    "\<Lambda>1  \<equiv> ((append m_before_ast_to_cfg_prog.constants_vdecls m_before_ast_to_cfg_prog.globals_vdecls),(append m_before_ast_to_cfg_prog.params_vdecls m_before_ast_to_cfg_prog.locals_vdecls))"
declare Nat.One_nat_def[simp del]

lemma rel_m_before_ast_to_cfg_prog_bigblock_3:
assumes 
astStep: "(red_bigblock A M \<Lambda>1 \<Gamma> [] T (m_before_ast_to_cfg_prog.bigblock_3,cont0,(Normal ns1)) (reached_bb,reached_cont,reached_state))" and 
cfgBlockDoesntFail: "(\<And> s2'. ((red_cmd_list A M' \<Lambda>1 \<Gamma> [] m_before_cfg_to_dag_prog.block_4 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "((reached_state \<noteq> Failure) \<and> (\<forall> ns1'. ((reached_state = (Normal ns1')) \<longrightarrow> (red_cmd_list A M' \<Lambda>1 \<Gamma> [] m_before_cfg_to_dag_prog.block_4 (Normal ns1) (Normal ns1')))))"
apply (rule block_local_rel_generic)
apply (rule Rel_Main_test[of m_before_ast_to_cfg_prog.bigblock_3])
apply (simp add: m_before_ast_to_cfg_prog.bigblock_3_def m_before_cfg_to_dag_prog.block_4_def)
apply ((simp add: m_before_cfg_to_dag_prog.block_4_def)+)
apply (rule astStep)
apply (rule cfgBlockDoesntFail)
apply ((simp add: m_before_cfg_to_dag_prog.block_4_def m_before_ast_to_cfg_prog.bigblock_3_def)+)
done


lemma global_rel_m_before_ast_to_cfg_prog_bigblock_3:
assumes 
astTrace: "(red_bigblock_k_step A M \<Lambda>1 \<Gamma> [] T (m_before_ast_to_cfg_prog.bigblock_3,cont_3,(Normal ns1)) j (reached_bb,reached_cont,reached_state))" and 
cfgDoesntFail: "(\<And> m' s'. ((red_cfg_multi A M' \<Lambda>1 \<Gamma> [] m_before_cfg_to_dag_prog.proc_body ((Inl 4),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)))" and 
cfgSatisfiesPosts: "(\<And> m' s'. ((red_cfg_multi A M' \<Lambda>1 \<Gamma> [] m_before_cfg_to_dag_prog.proc_body ((Inl 4),(Normal ns1)) (m',s')) \<Longrightarrow> ((is_final_config (m',s')) \<Longrightarrow> (\<forall> ns_end. ((s' = (Normal ns_end)) \<longrightarrow> (expr_all_sat A \<Lambda>1 \<Gamma> [] ns_end m_before_ast_to_cfg_prog.post))))))"
shows "(Ast.valid_configuration A \<Lambda>1 \<Gamma> [] m_before_ast_to_cfg_prog.post reached_bb reached_cont reached_state)"
proof -
show ?thesis
apply (rule generic_ending_block_global_rel)
apply (rule Rel_Main_test[of m_before_ast_to_cfg_prog.bigblock_3])
apply (simp add: m_before_ast_to_cfg_prog.bigblock_3_def)
apply (simp)
apply (rule astTrace)
apply (simp add: m_before_ast_to_cfg_prog.bigblock_3_def)
apply (simp)
apply (simp)
apply (rule cont_3_def)
apply (rule m_before_cfg_to_dag_prog.node_4)
apply (rule disjI1)
apply (rule m_before_cfg_to_dag_prog.block_4_def)
apply (rule m_before_cfg_to_dag_prog.outEdges_4)
apply (rule cfgDoesntFail)
apply (simp)
apply (rule cfgSatisfiesPosts)
apply ((simp)+)
apply (simp add: m_before_cfg_to_dag_prog.node_4)
apply (rule rel_m_before_ast_to_cfg_prog_bigblock_3)
apply assumption+

done
qed

lemma rel_m_before_ast_to_cfg_prog_bigblock_2:
assumes 
astStep: "(red_bigblock A M \<Lambda>1 \<Gamma> [] T (m_before_ast_to_cfg_prog.bigblock_2,cont0,(Normal ns1)) (reached_bb,reached_cont,reached_state))" and 
cfgBlockDoesntFail: "(\<And> s2'. ((red_cmd_list A M' \<Lambda>1 \<Gamma> [] m_before_cfg_to_dag_prog.block_2 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" and 
guardHint: "(red_expr A \<Lambda>1 \<Gamma> [] (BinOp (Var 0) Lt (Var 1)) ns1 (BoolV True))"
shows "((reached_state \<noteq> Failure) \<and> (\<forall> ns1'. ((reached_state = (Normal ns1')) \<longrightarrow> (red_cmd_list A M' \<Lambda>1 \<Gamma> [] m_before_cfg_to_dag_prog.block_2 (Normal ns1) (Normal ns1')))))"
unfolding m_before_cfg_to_dag_prog.block_2_def
apply (rule guard_holds_push_through_assumption)
apply (rule block_local_rel_generic)
apply (rule Rel_Main_test[of m_before_ast_to_cfg_prog.bigblock_2])
apply (simp add: m_before_ast_to_cfg_prog.bigblock_2_def)
apply (simp+)
apply (rule astStep)
apply (rule push_through_assumption_test1, rule cfgBlockDoesntFail)
apply (simp add: m_before_cfg_to_dag_prog.block_2_def)
apply ((simp add: assms(3) m_before_ast_to_cfg_prog.bigblock_2_def)+)
done


lemma global_rel_m_before_ast_to_cfg_prog_bigblock_2:
assumes 
astTrace: "(red_bigblock_k_step A M \<Lambda>1 \<Gamma> [] T (m_before_ast_to_cfg_prog.bigblock_2,cont_2,(Normal ns1)) j (reached_bb,reached_cont,reached_state))" and 
cfgDoesntFail: "(\<And> m' s'. ((red_cfg_multi A M' \<Lambda>1 \<Gamma> [] m_before_cfg_to_dag_prog.proc_body ((Inl 2),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)))" and 
cfgSatisfiesPosts: "(\<And> m' s'. ((red_cfg_multi A M' \<Lambda>1 \<Gamma> [] m_before_cfg_to_dag_prog.proc_body ((Inl 2),(Normal ns1)) (m',s')) \<Longrightarrow> ((is_final_config (m',s')) \<Longrightarrow> (\<forall> ns_end. ((s' = (Normal ns_end)) \<longrightarrow> (expr_all_sat A \<Lambda>1 \<Gamma> [] ns_end m_before_ast_to_cfg_prog.post))))))" and 
guardHint: "(red_expr A \<Lambda>1 \<Gamma> [] (BinOp (Var 0) Lt (Var 1)) ns1 (BoolV True))" and 
inductionHypothesis: "(loop_IH j A M M' \<Lambda>1 \<Gamma> [] T m_before_ast_to_cfg_prog.bigblock_1 cont_1 m_before_cfg_to_dag_prog.proc_body 1 m_before_ast_to_cfg_prog.post reached_bb reached_cont reached_state)"
shows "(Ast.valid_configuration A \<Lambda>1 \<Gamma> [] m_before_ast_to_cfg_prog.post reached_bb reached_cont reached_state)"
proof -
show ?thesis 
apply (rule block_global_rel_generic)
apply (rule Rel_Main_test[of m_before_ast_to_cfg_prog.bigblock_2])
apply (simp add: m_before_ast_to_cfg_prog.bigblock_2_def)
apply (simp)
apply (rule astTrace)
apply (simp add: m_before_ast_to_cfg_prog.bigblock_2_def)
apply (rule m_before_cfg_to_dag_prog.node_2)
apply (rule disjI2)
apply (rule disjI1)
apply (rule conjI)
apply (rule m_before_cfg_to_dag_prog.block_2_def)
apply (rule conjI)
apply (simp)
apply (rule guardHint)
apply (rule cfgDoesntFail)
apply ((simp)+)
apply (rule cfgSatisfiesPosts, blast)
apply ((simp)+)
apply (rule cont_2_def)
apply (simp add: m_before_cfg_to_dag_prog.node_2)
apply (rule rel_m_before_ast_to_cfg_prog_bigblock_2)
apply assumption
apply (simp)
apply (rule guardHint)
apply ((erule allE[where x=1])+)
apply (simp add: m_before_cfg_to_dag_prog.outEdges_2)
apply (simp add: member_rec(1))
apply (rule loop_IH_apply)
apply (rule inductionHypothesis)
apply ((simp)+)
done
qed

lemma global_rel_m_before_ast_to_cfg_prog_bigblock_1:
assumes 
astTrace: "(red_bigblock_k_step A M \<Lambda>1 \<Gamma> [] T (m_before_ast_to_cfg_prog.bigblock_1,cont_1,(Normal ns1)) j (reached_bb,reached_cont,reached_state))" and 
cfgDoesntFail: "(\<And> m' s'. ((red_cfg_multi A M' \<Lambda>1 \<Gamma> [] m_before_cfg_to_dag_prog.proc_body ((Inl 1),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)))" and 
cfgSatisfiesPosts: "(\<And> m' s'. ((red_cfg_multi A M' \<Lambda>1 \<Gamma> [] m_before_cfg_to_dag_prog.proc_body ((Inl 1),(Normal ns1)) (m',s')) \<Longrightarrow> ((is_final_config (m',s')) \<Longrightarrow> (\<forall> ns_end. ((s' = (Normal ns_end)) \<longrightarrow> (expr_all_sat A \<Lambda>1 \<Gamma> [] ns_end m_before_ast_to_cfg_prog.post))))))"
shows "(Ast.valid_configuration A \<Lambda>1 \<Gamma> [] m_before_ast_to_cfg_prog.post reached_bb reached_cont reached_state)"
using assms
proof (induction j arbitrary: ns1 rule: less_induct)
case (less j)
then show ?case
proof (cases j)
case 0
then show ?thesis
using valid_configuration_def less.prems(1) is_final.elims(2) cont_1_def by fastforce
next
case (Suc j')
show ?thesis
apply (rule block_global_rel_loop_head )
apply (rule Rel_Invs[of m_before_ast_to_cfg_prog.bigblock_1 _ _ _ m_before_cfg_to_dag_prog.block_1])
apply (simp add:m_before_ast_to_cfg_prog.bigblock_1_def m_before_cfg_to_dag_prog.block_1_def)
apply (rule less(2))
apply (rule less(3), simp)
apply (rule less(4), simp)
apply (simp)
apply (simp add:m_before_ast_to_cfg_prog.bigblock_1_def)
apply simp                 
apply (rule block_local_rel_loop_head)
apply (rule Rel_Invs[of m_before_ast_to_cfg_prog.bigblock_1])
apply ((simp add:m_before_ast_to_cfg_prog.bigblock_1_def)+)
apply ((simp add:m_before_cfg_to_dag_prog.block_1_def m_before_cfg_to_dag_prog.node_1)+)
apply (rule cont_1_def)
apply (erule disjE)



apply ((erule allE[where x = 2])+)
apply ((simp add:m_before_cfg_to_dag_prog.outEdges_1)+)
apply (simp add:member_rec(1))
apply (erule conjE)
apply (rule global_rel_m_before_ast_to_cfg_prog_bigblock_2)
apply (simp add: cont_1_def m_before_ast_to_cfg_prog.bigblock_2_def cont_2_def )
apply ((blast)+)
apply (rule loop_IH_prove)
apply (rule less.IH)
apply (erule strictly_smaller_helper2)
apply (simp)
unfolding cont_1_def cont_2_def
apply (simp)
apply (blast)
apply (blast)


apply ((erule allE[where x = 3])+)
apply ((simp add:m_before_cfg_to_dag_prog.outEdges_1)+)
apply (simp add:member_rec(1))
apply (erule conjE)
apply (rule ending_after_skipping_endblock2)
apply ((simp)+)
apply (blast)
apply (blast)
apply (simp)
apply (simp)
apply (rule global_rel_m_before_ast_to_cfg_prog_bigblock_3)
apply (blast)



apply (rule correctness_propagates_through_assumption)
apply blast
apply (simp add: m_before_cfg_to_dag_prog.node_3)
apply (simp add: m_before_cfg_to_dag_prog.block_3_def)
apply (rule neg_lt)
apply (simp)
apply (simp add: m_before_cfg_to_dag_prog.outEdges_3)
apply ((simp add: member_rec)+)
apply (rule correctness_propagates_through_assumption3)
apply blast
apply (simp add: m_before_cfg_to_dag_prog.node_3)
apply (simp add: m_before_cfg_to_dag_prog.block_3_def)
apply (rule neg_lt)
apply (simp)
apply (simp add: m_before_cfg_to_dag_prog.outEdges_3)
apply ((simp add: member_rec)+)
done
qed
qed

lemma rel_m_before_ast_to_cfg_prog_bigblock_0:
assumes 
astStep: "(red_bigblock A M \<Lambda>1 \<Gamma> [] T (m_before_ast_to_cfg_prog.bigblock_0,cont0,(Normal ns1)) (reached_bb,reached_cont,reached_state))" and 
cfgBlockDoesntFail: "(\<And> s2'. ((red_cmd_list A M' \<Lambda>1 \<Gamma> [] m_before_cfg_to_dag_prog.block_0 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "((reached_state \<noteq> Failure) \<and> (\<forall> ns1'. ((reached_state = (Normal ns1')) \<longrightarrow> (red_cmd_list A M' \<Lambda>1 \<Gamma> [] m_before_cfg_to_dag_prog.block_0 (Normal ns1) (Normal ns1')))))"
apply (rule block_local_rel_generic)
apply (rule Rel_Main_test[of m_before_ast_to_cfg_prog.bigblock_0])
apply (simp add: m_before_ast_to_cfg_prog.bigblock_0_def m_before_cfg_to_dag_prog.block_0_def)
apply ((simp add: m_before_cfg_to_dag_prog.block_0_def)+)
apply (rule astStep)
apply (rule cfgBlockDoesntFail)
apply ((simp add: m_before_cfg_to_dag_prog.block_0_def m_before_ast_to_cfg_prog.bigblock_0_def)+)
done


lemma global_rel_m_before_ast_to_cfg_prog_bigblock_0:
assumes 
astTrace: "(red_bigblock_k_step A M \<Lambda>1 \<Gamma> [] T (m_before_ast_to_cfg_prog.bigblock_0,cont_0,(Normal ns1)) j (reached_bb,reached_cont,reached_state))" and 
cfgDoesntFail: "(\<And> m' s'. ((red_cfg_multi A M' \<Lambda>1 \<Gamma> [] m_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)))" and 
cfgSatisfiesPosts: "(\<And> m' s'. ((red_cfg_multi A M' \<Lambda>1 \<Gamma> [] m_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) (m',s')) \<Longrightarrow> ((is_final_config (m',s')) \<Longrightarrow> (\<forall> ns_end. ((s' = (Normal ns_end)) \<longrightarrow> (expr_all_sat A \<Lambda>1 \<Gamma> [] ns_end m_before_ast_to_cfg_prog.post))))))"
shows "(Ast.valid_configuration A \<Lambda>1 \<Gamma> [] m_before_ast_to_cfg_prog.post reached_bb reached_cont reached_state)"
proof -
show ?thesis
apply (rule block_global_rel_while_successor)
apply (rule astTrace)
apply (rule Rel_Main_test[of m_before_ast_to_cfg_prog.bigblock_0 _ m_before_cfg_to_dag_prog.block_0])
apply (simp add: m_before_ast_to_cfg_prog.bigblock_0_def m_before_cfg_to_dag_prog.block_0_def)
apply (simp add: m_before_ast_to_cfg_prog.bigblock_0_def m_before_cfg_to_dag_prog.block_0_def)
apply (simp add: m_before_ast_to_cfg_prog.bigblock_0_def m_before_cfg_to_dag_prog.block_0_def)
apply (simp add: m_before_cfg_to_dag_prog.block_0_def)
apply (rule m_before_cfg_to_dag_prog.node_0)
apply (rule disjI1)



apply (simp add: m_before_cfg_to_dag_prog.block_0_def)







apply (rule cfgDoesntFail, simp)
apply (rule cfgSatisfiesPosts, blast)
apply ((simp)+)
apply (simp add: m_before_cfg_to_dag_prog.node_0)
apply (rule rel_m_before_ast_to_cfg_prog_bigblock_0)
apply (simp add: m_before_ast_to_cfg_prog.bigblock_0_def)
apply ((simp)+)

apply ((erule allE[where x = 1])+)
apply ((simp add: m_before_cfg_to_dag_prog.outEdges_0)+)
apply (simp add: member_rec(1))
apply (rule global_rel_m_before_ast_to_cfg_prog_bigblock_1)
apply (simp add: m_before_ast_to_cfg_prog.bigblock_1_def cont_0_def cont_1_def)
apply blast+





done
qed


end

abbreviation \<Lambda>0
  where
    "\<Lambda>0  \<equiv> ((append m_before_ast_to_cfg_prog.constants_vdecls m_before_ast_to_cfg_prog.globals_vdecls),(append m_before_ast_to_cfg_prog.params_vdecls m_before_ast_to_cfg_prog.locals_vdecls))"
lemma end_to_end_theorem_aux_ast:
assumes 
Red: "(rtranclp (red_bigblock A M ((append m_before_ast_to_cfg_prog.constants_vdecls m_before_ast_to_cfg_prog.globals_vdecls),(append m_before_ast_to_cfg_prog.params_vdecls m_before_ast_to_cfg_prog.locals_vdecls)) \<Gamma> [] T) (m_before_ast_to_cfg_prog.bigblock_0,cont_0,(Normal ns)) (reached_bb,reached_cont,reached_state))" and 
VC: "(\<And> (vc_i::int) (vc_n::int) (vc_i_0::int) (vc_i_1::int). (vc.vc_PreconditionGeneratedEntry vc_n vc_i_0 vc_i_1))" and 
Closed: "(\<And> v. (closed ((type_of_val A) v)))" and 
NonEmptyTypes: "(\<And> t. ((closed t) \<Longrightarrow> (\<exists> v. (((type_of_val A) v) = t))))" and 
FInterp: "(fun_interp_wf A m_before_ast_to_cfg_prog.fdecls \<Gamma>)" and 
Axioms: "(axiom_assm A \<Gamma> m_before_ast_to_cfg_prog.constants_vdecls (ns::(('a)nstate)) m_before_ast_to_cfg_prog.axioms)" and 
Precondition: "(expr_all_sat A \<Lambda>0 \<Gamma> [] ns m_before_ast_to_cfg_prog.pres)" and 
ParamsLocal: "(state_typ_wf A [] (local_state ns) (snd \<Lambda>0))" and 
ConstsGlobal: "(state_typ_wf A [] (global_state ns) (fst \<Lambda>0))" and 
OldGlobal: "((global_state ns) = (old_global_state ns))" and 
BinderNs: "((binder_state ns) = Map.empty)"
shows "(Ast.valid_configuration A \<Lambda>0 \<Gamma> [] m_before_ast_to_cfg_prog.post reached_bb reached_cont reached_state)"
proof -
from Red obtain j where Aux:"(red_bigblock_k_step A M ((append m_before_ast_to_cfg_prog.constants_vdecls m_before_ast_to_cfg_prog.globals_vdecls),(append m_before_ast_to_cfg_prog.params_vdecls m_before_ast_to_cfg_prog.locals_vdecls)) \<Gamma> [] T (m_before_ast_to_cfg_prog.bigblock_0,cont_0,(Normal ns)) j (reached_bb,reached_cont,reached_state))"
by (meson rtranclp_imp_relpowp)
show ?thesis
apply (rule ast_to_cfg_lemmas.global_rel_m_before_ast_to_cfg_prog_bigblock_0)
unfolding ast_to_cfg_lemmas_def
apply (rule FInterp)
apply (rule Aux)
apply (rule valid_config_implies_not_failure)
apply (rule end_to_end_theorem_aux)
apply (simp add: m_before_ast_to_cfg_prog.params_vdecls_def m_before_ast_to_cfg_prog.locals_vdecls_def m_before_cfg_to_dag_prog.params_vdecls_def m_before_cfg_to_dag_prog.locals_vdecls_def)
using VC apply simp
using Closed apply simp
using NonEmptyTypes apply simp
apply (rule FInterp)
using Axioms apply simp
using Precondition apply (simp add: m_before_ast_to_cfg_prog.params_vdecls_def m_before_ast_to_cfg_prog.locals_vdecls_def m_before_cfg_to_dag_prog.params_vdecls_def m_before_cfg_to_dag_prog.locals_vdecls_def m_before_ast_to_cfg_prog.pres_def m_before_cfg_to_dag_prog.pres_def)
using ParamsLocal apply (simp add: m_before_ast_to_cfg_prog.params_vdecls_def m_before_ast_to_cfg_prog.locals_vdecls_def m_before_cfg_to_dag_prog.params_vdecls_def m_before_cfg_to_dag_prog.locals_vdecls_def)
using ConstsGlobal apply (simp add: m_before_ast_to_cfg_prog.params_vdecls_def m_before_ast_to_cfg_prog.locals_vdecls_def m_before_cfg_to_dag_prog.params_vdecls_def m_before_cfg_to_dag_prog.locals_vdecls_def)
using OldGlobal apply simp
using BinderNs apply simp
apply (rule valid_config_implies_satisfied_posts)
apply (rule end_to_end_theorem_aux)
apply (simp add: m_before_ast_to_cfg_prog.params_vdecls_def m_before_ast_to_cfg_prog.locals_vdecls_def m_before_cfg_to_dag_prog.params_vdecls_def m_before_cfg_to_dag_prog.locals_vdecls_def)
using VC apply simp
using Closed apply simp
using NonEmptyTypes apply simp
apply (rule FInterp)
using Axioms apply simp
using Precondition apply (simp add: m_before_ast_to_cfg_prog.params_vdecls_def m_before_ast_to_cfg_prog.locals_vdecls_def m_before_cfg_to_dag_prog.params_vdecls_def m_before_cfg_to_dag_prog.locals_vdecls_def m_before_ast_to_cfg_prog.pres_def m_before_cfg_to_dag_prog.pres_def)
using ParamsLocal apply (simp add: m_before_ast_to_cfg_prog.params_vdecls_def m_before_ast_to_cfg_prog.locals_vdecls_def m_before_cfg_to_dag_prog.params_vdecls_def m_before_cfg_to_dag_prog.locals_vdecls_def)
using ConstsGlobal apply (simp add: m_before_ast_to_cfg_prog.params_vdecls_def m_before_ast_to_cfg_prog.locals_vdecls_def m_before_cfg_to_dag_prog.params_vdecls_def m_before_cfg_to_dag_prog.locals_vdecls_def)
using OldGlobal apply simp
using BinderNs apply simp+
done
qed


lemma initialization:
assumes 
"(rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T) (init_ast [bigblock_0,bigblock_3] ns) (reached_bb,reached_cont,reached_state))"
shows "(rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T) (m_before_ast_to_cfg_prog.bigblock_0,cont_0,(Normal ns)) (reached_bb,reached_cont,reached_state))"
using assms
by (simp add: cont_0_def cont_3_def )

lemma end_to_end_theorem_ast:
assumes 
VC: "(\<And> (vc_i::int) (vc_n::int) (vc_i_0::int) (vc_i_1::int). (vc.vc_PreconditionGeneratedEntry vc_n vc_i_0 vc_i_1))"
shows "(\<And> A. (proc_is_correct (A::(('a)absval_ty_fun)) m_before_ast_to_cfg_prog.fdecls m_before_ast_to_cfg_prog.constants_vdecls m_before_ast_to_cfg_prog.globals_vdecls m_before_ast_to_cfg_prog.axioms m_before_ast_to_cfg_prog.ast_proc Ast.proc_body_satisfies_spec))"
apply (rule end_to_end_util2[OF end_to_end_theorem_aux_ast])
apply (rule initialization)
unfolding m_before_ast_to_cfg_prog.ast_proc_def
apply assumption using VC apply simp  apply assumption+
by (simp_all add: exprs_to_only_checked_spec_1 exprs_to_only_checked_spec_2 m_before_ast_to_cfg_prog.ast_proc_def m_before_ast_to_cfg_prog.proc_body_def)


end
