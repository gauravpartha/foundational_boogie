theory p_asttocfg_proof
imports Boogie_Lang.Ast Boogie_Lang.Ast_Cfg_Transformation Boogie_Lang.Semantics Boogie_Lang.Util Boogie_Lang.BackedgeElim Boogie_Lang.TypingML p_before_ast_to_cfg_prog p_before_cfg_to_dag_prog p_cfgtodag_proof p_passification_proof p_vcphase_proof
begin
locale ast_to_cfg_lemmas = 
fixes A :: "(('a)absval_ty_fun)" and \<Gamma> :: "(('a)fun_interp)"
assumes 
Wf_Fun: "(fun_interp_wf A p_before_ast_to_cfg_prog.fdecls \<Gamma>)"
begin

abbreviation \<Lambda>1
  where
    "\<Lambda>1  \<equiv> ((append p_before_ast_to_cfg_prog.constants_vdecls p_before_ast_to_cfg_prog.globals_vdecls),(append p_before_ast_to_cfg_prog.params_vdecls p_before_ast_to_cfg_prog.locals_vdecls))"
declare Nat.One_nat_def[simp del]

lemma rel_p_before_ast_to_cfg_prog_bigblock_0:
assumes 
astStep: "(red_bigblock A M \<Lambda>1 \<Gamma> [] T (p_before_ast_to_cfg_prog.bigblock_0,cont0,(Normal ns1)) (reached_bb,reached_cont,reached_state))" and 
cfgBlockDoesntFail: "(\<And> s2'. ((red_cmd_list A M' \<Lambda>1 \<Gamma> [] p_before_cfg_to_dag_prog.block_0 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))"
shows "((reached_state \<noteq> Failure) \<and> (\<forall> ns1'. ((reached_state = (Normal ns1')) \<longrightarrow> (red_cmd_list A M' \<Lambda>1 \<Gamma> [] p_before_cfg_to_dag_prog.block_0 (Normal ns1) (Normal ns1')))))"
apply (rule block_local_rel_generic)
apply (rule Rel_Main_test[of p_before_ast_to_cfg_prog.bigblock_0])
apply (simp add: p_before_ast_to_cfg_prog.bigblock_0_def p_before_cfg_to_dag_prog.block_0_def)
apply ((simp add: p_before_cfg_to_dag_prog.block_0_def)+)
apply (rule astStep)
apply (rule cfgBlockDoesntFail)
apply ((simp add: p_before_cfg_to_dag_prog.block_0_def p_before_ast_to_cfg_prog.bigblock_0_def)+)
done


lemma global_rel_p_before_ast_to_cfg_prog_bigblock_0:
assumes 
astTrace: "(red_bigblock_k_step A M \<Lambda>1 \<Gamma> [] T (p_before_ast_to_cfg_prog.bigblock_0,cont_0,(Normal ns1)) j (reached_bb,reached_cont,reached_state))" and 
cfgDoesntFail: "(\<And> m' s'. ((red_cfg_multi A M' \<Lambda>1 \<Gamma> [] p_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)))" and 
cfgSatisfiesPosts: "(\<And> m' s'. ((red_cfg_multi A M' \<Lambda>1 \<Gamma> [] p_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) (m',s')) \<Longrightarrow> ((is_final_config (m',s')) \<Longrightarrow> (\<forall> ns_end. ((s' = (Normal ns_end)) \<longrightarrow> (expr_all_sat A \<Lambda>1 \<Gamma> [] ns_end p_before_ast_to_cfg_prog.post))))))"
shows "(Ast.valid_configuration A \<Lambda>1 \<Gamma> [] p_before_ast_to_cfg_prog.post reached_bb reached_cont reached_state)"
proof -
show ?thesis
apply (rule generic_ending_block_global_rel)
apply (rule Rel_Main_test[of p_before_ast_to_cfg_prog.bigblock_0])
apply (simp add: p_before_ast_to_cfg_prog.bigblock_0_def)
apply (simp)
apply (rule astTrace)
apply (simp add: p_before_ast_to_cfg_prog.bigblock_0_def)
apply (simp)
apply (simp)
apply (rule cont_0_def)
apply (rule p_before_cfg_to_dag_prog.node_0)
apply (rule disjI1)
apply (rule p_before_cfg_to_dag_prog.block_0_def)
apply (rule p_before_cfg_to_dag_prog.outEdges_0)
apply (rule cfgDoesntFail)
apply (simp)
apply (rule cfgSatisfiesPosts)
apply ((simp)+)
apply (simp add: p_before_cfg_to_dag_prog.node_0)
apply (rule rel_p_before_ast_to_cfg_prog_bigblock_0)
apply assumption+

done
qed


end

abbreviation \<Lambda>0
  where
    "\<Lambda>0  \<equiv> ((append p_before_ast_to_cfg_prog.constants_vdecls p_before_ast_to_cfg_prog.globals_vdecls),(append p_before_ast_to_cfg_prog.params_vdecls p_before_ast_to_cfg_prog.locals_vdecls))"
lemma end_to_end_theorem_aux_ast:
assumes 
Red: "(rtranclp (red_bigblock A M ((append p_before_ast_to_cfg_prog.constants_vdecls p_before_ast_to_cfg_prog.globals_vdecls),(append p_before_ast_to_cfg_prog.params_vdecls p_before_ast_to_cfg_prog.locals_vdecls)) \<Gamma> [] T) (p_before_ast_to_cfg_prog.bigblock_0,cont_0,(Normal ns)) (reached_bb,reached_cont,reached_state))" and 
VC: "(\<And> (vc_x::int) (vc_a::int) (vc_f::(int => bool)). (vc.vc_PreconditionGeneratedEntry vc_f vc_a))" and 
Closed: "(\<And> v. (closed ((type_of_val A) v)))" and 
NonEmptyTypes: "(\<And> t. ((closed t) \<Longrightarrow> (\<exists> v. (((type_of_val A) v) = t))))" and 
FInterp: "(fun_interp_wf A p_before_ast_to_cfg_prog.fdecls \<Gamma>)" and 
Axioms: "(axiom_assm A \<Gamma> p_before_ast_to_cfg_prog.constants_vdecls (ns::(('a)nstate)) p_before_ast_to_cfg_prog.axioms)" and 
Precondition: "(expr_all_sat A \<Lambda>0 \<Gamma> [] ns p_before_ast_to_cfg_prog.pres)" and 
ParamsLocal: "(state_typ_wf A [] (local_state ns) (snd \<Lambda>0))" and 
ConstsGlobal: "(state_typ_wf A [] (global_state ns) (fst \<Lambda>0))" and 
OldGlobal: "((global_state ns) = (old_global_state ns))" and 
BinderNs: "((binder_state ns) = Map.empty)"
shows "(Ast.valid_configuration A \<Lambda>0 \<Gamma> [] p_before_ast_to_cfg_prog.post reached_bb reached_cont reached_state)"
proof -
from Red obtain j where Aux:"(red_bigblock_k_step A M ((append p_before_ast_to_cfg_prog.constants_vdecls p_before_ast_to_cfg_prog.globals_vdecls),(append p_before_ast_to_cfg_prog.params_vdecls p_before_ast_to_cfg_prog.locals_vdecls)) \<Gamma> [] T (p_before_ast_to_cfg_prog.bigblock_0,cont_0,(Normal ns)) j (reached_bb,reached_cont,reached_state))"
by (meson rtranclp_imp_relpowp)
show ?thesis
apply (rule ast_to_cfg_lemmas.global_rel_p_before_ast_to_cfg_prog_bigblock_0)
unfolding ast_to_cfg_lemmas_def
apply (rule FInterp)
apply (rule Aux)
apply (rule valid_config_implies_not_failure)
apply (rule end_to_end_theorem_aux)
apply (simp add: p_before_ast_to_cfg_prog.params_vdecls_def p_before_ast_to_cfg_prog.locals_vdecls_def p_before_cfg_to_dag_prog.params_vdecls_def p_before_cfg_to_dag_prog.locals_vdecls_def)
using VC apply simp
using Closed apply simp
using NonEmptyTypes apply simp
apply (rule FInterp)
using Axioms apply simp
using Precondition apply (simp add: p_before_ast_to_cfg_prog.params_vdecls_def p_before_ast_to_cfg_prog.locals_vdecls_def p_before_cfg_to_dag_prog.params_vdecls_def p_before_cfg_to_dag_prog.locals_vdecls_def p_before_ast_to_cfg_prog.pres_def p_before_cfg_to_dag_prog.pres_def)
using ParamsLocal apply (simp add: p_before_ast_to_cfg_prog.params_vdecls_def p_before_ast_to_cfg_prog.locals_vdecls_def p_before_cfg_to_dag_prog.params_vdecls_def p_before_cfg_to_dag_prog.locals_vdecls_def)
using ConstsGlobal apply (simp add: p_before_ast_to_cfg_prog.params_vdecls_def p_before_ast_to_cfg_prog.locals_vdecls_def p_before_cfg_to_dag_prog.params_vdecls_def p_before_cfg_to_dag_prog.locals_vdecls_def)
using OldGlobal apply simp
using BinderNs apply simp
apply (rule valid_config_implies_satisfied_posts)
apply (rule end_to_end_theorem_aux)
apply (simp add: p_before_ast_to_cfg_prog.params_vdecls_def p_before_ast_to_cfg_prog.locals_vdecls_def p_before_cfg_to_dag_prog.params_vdecls_def p_before_cfg_to_dag_prog.locals_vdecls_def)
using VC apply simp
using Closed apply simp
using NonEmptyTypes apply simp
apply (rule FInterp)
using Axioms apply simp
using Precondition apply (simp add: p_before_ast_to_cfg_prog.params_vdecls_def p_before_ast_to_cfg_prog.locals_vdecls_def p_before_cfg_to_dag_prog.params_vdecls_def p_before_cfg_to_dag_prog.locals_vdecls_def p_before_ast_to_cfg_prog.pres_def p_before_cfg_to_dag_prog.pres_def)
using ParamsLocal apply (simp add: p_before_ast_to_cfg_prog.params_vdecls_def p_before_ast_to_cfg_prog.locals_vdecls_def p_before_cfg_to_dag_prog.params_vdecls_def p_before_cfg_to_dag_prog.locals_vdecls_def)
using ConstsGlobal apply (simp add: p_before_ast_to_cfg_prog.params_vdecls_def p_before_ast_to_cfg_prog.locals_vdecls_def p_before_cfg_to_dag_prog.params_vdecls_def p_before_cfg_to_dag_prog.locals_vdecls_def)
using OldGlobal apply simp
using BinderNs apply simp+
done
qed


lemma initialization:
assumes 
"(rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T) (init_ast [bigblock_0] ns) (reached_bb,reached_cont,reached_state))"
shows "(rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T) (p_before_ast_to_cfg_prog.bigblock_0,cont_0,(Normal ns)) (reached_bb,reached_cont,reached_state))"
using assms
by (simp add: cont_0_def )

lemma end_to_end_theorem_ast:
assumes 
VC: "(\<And> (vc_x::int) (vc_a::int) (vc_f::(int => bool)). (vc.vc_PreconditionGeneratedEntry vc_f vc_a))"
shows "(\<And> A. (proc_is_correct (A::(('a)absval_ty_fun)) p_before_ast_to_cfg_prog.fdecls p_before_ast_to_cfg_prog.constants_vdecls p_before_ast_to_cfg_prog.globals_vdecls p_before_ast_to_cfg_prog.axioms p_before_ast_to_cfg_prog.ast_proc Ast.proc_body_satisfies_spec))"
apply (rule end_to_end_util2[OF end_to_end_theorem_aux_ast])
apply (rule initialization)
unfolding p_before_ast_to_cfg_prog.ast_proc_def
apply assumption using VC apply simp  apply assumption+
by (simp_all add: exprs_to_only_checked_spec_1 exprs_to_only_checked_spec_2 p_before_ast_to_cfg_prog.ast_proc_def p_before_ast_to_cfg_prog.proc_body_def)


end
