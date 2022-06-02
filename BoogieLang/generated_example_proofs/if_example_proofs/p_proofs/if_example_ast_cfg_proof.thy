theory if_example_ast_cfg_proof
  imports Main
          Boogie_Lang.Ast
          Boogie_Lang.Semantics
          Boogie_Lang.Ast_Cfg_Transformation
          "../global_data" 
          p_before_cfg_to_dag_prog 
          if_example_before_ast_cfg
          p_cfgtodag_proof
          "/home/alex/Isabelle_10-Nov-2021/lib/Apply_Trace_Cmd"
          p_before_passive_prog 
          p_passification_proof 
          p_vcphase_proof

begin
declare Nat.One_nat_def[simp del]

definition bigblock_then 
  where "bigblock_then \<equiv> BigBlock None [(Assign 0 (Lit (LInt 10)))] None None"

definition bigblock_else
  where "bigblock_else \<equiv> BigBlock None [(Assign 0 (Lit (LInt 1)))] None None"

lemma bigblock0_local_rel:
  assumes Red_bb0_to: 
      "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bigblock0, KSeq bigblock1 KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red0_impl: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_before_cfg_to_dag_prog.block_0 (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)" 
  shows "reached_state \<noteq> Failure \<and> 
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>p_before_cfg_to_dag_prog.block_0, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))"
proof -
  show ?thesis 
    apply (rule block_local_rel_generic) 
           apply (rule Rel_Main_test[of bigblock0])
            apply (simp add: bigblock0_def p_before_cfg_to_dag_prog.block_0_def)
           apply (simp add: p_before_cfg_to_dag_prog.block_0_def)
          apply simp
         apply simp
        apply (rule Red_bb0_to)
       apply (rule Red0_impl)
       apply (simp add: bigblock0_def p_before_cfg_to_dag_prog.block_0_def)+
    done
qed


lemma bigblock_then_local_rel:
  assumes Red_bb0_to: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bigblock_then, KSeq bigblock1 KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red0_impl: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_before_cfg_to_dag_prog.block_3 (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)" 
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 0) Gt (Lit (LInt 5))), ns1\<rangle> \<Down> LitV (LBool True)"
  shows "reached_state \<noteq> Failure \<and> 
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>p_before_cfg_to_dag_prog.block_3, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
proof -
  show ?thesis
    apply (simp add: p_before_cfg_to_dag_prog.block_3_def)
    apply (rule guard_holds_push_through_assumption)
      apply (rule block_local_rel_generic)
             apply (rule Rel_Main_test[of bigblock_then])
             apply (simp add: bigblock_then_def)
            apply simp
           apply simp+
          apply (rule Red_bb0_to)
         apply (rule push_through_assumption_test1, rule Red0_impl)
         apply (simp add: p_before_cfg_to_dag_prog.block_3_def)
           apply (simp add: trace_is_possible bigblock_then_def)+
    done
qed

lemma bigblock_else_local_rel:
  assumes Red_bb0_to: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bigblock_else, KSeq bigblock1 KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red0_impl: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_before_cfg_to_dag_prog.block_1 (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)" 
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 0) Gt (Lit (LInt 5))), ns1\<rangle> \<Down> LitV (LBool False)"
  shows "reached_state \<noteq> Failure \<and> 
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>p_before_cfg_to_dag_prog.block_1, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))"
proof -
  show ?thesis
    apply (simp add: p_before_cfg_to_dag_prog.block_1_def)
    apply (rule guard_fails_push_through_assumption)
      apply (rule block_local_rel_generic)
             apply (rule Rel_Main_test[of bigblock_else])
             apply (simp add: bigblock_else_def)
            apply simp
           apply simp+
          apply (rule Red_bb0_to)
         apply (rule Red0_impl)
         apply (simp add: p_before_cfg_to_dag_prog.block_1_def)
         apply (rule push_through_assumption1)
             apply simp
            apply (rule neg_gt2)
          apply (rule trace_is_possible)
         apply simp
        apply (simp add: bigblock_else_def)
        apply simp+
     apply (rule neg_gt2)
    apply (rule trace_is_possible)
    done
qed

lemma bigblock1_local_rel:
  assumes Red_bb0_to: 
      "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bigblock1, KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red0_impl: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_before_cfg_to_dag_prog.block_2 (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)" 
  shows "reached_state \<noteq> Failure \<and> 
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>p_before_cfg_to_dag_prog.block_2, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))"
proof -
  show ?thesis 
    apply (rule block_local_rel_generic) 
           apply (rule Rel_Main_test[of bigblock1])
            apply (simp add: bigblock1_def p_before_cfg_to_dag_prog.block_2_def)
           apply (simp add: p_before_cfg_to_dag_prog.block_2_def)
          apply simp
         apply simp
        apply (rule Red_bb0_to)
       apply (rule Red0_impl)
       apply (simp add: bigblock1_def p_before_cfg_to_dag_prog.block_2_def)+
    done
qed

lemma block2_global_rel:
  assumes concrete_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock1, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_before_cfg_to_dag_prog.proc_body ((Inl 2),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)" 
  and cfg_satisfies_post: "\<And>m' s'.
                 (A,M,\<Lambda>,\<Gamma>,\<Omega>,p_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 2, Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                 is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns_end) if_example_before_ast_cfg.post)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> if_example_before_ast_cfg.post reached_bb reached_cont reached_state)" 
  using assms
proof -
  show ?thesis
    apply (rule generic_ending_block_global_rel)
         apply (rule Rel_Main_test[of bigblock1 _ p_before_cfg_to_dag_prog.block_2])
             apply (simp add: bigblock1_def p_before_cfg_to_dag_prog.block_2_def)
            apply (simp add: p_before_cfg_to_dag_prog.block_2_def)
        apply (rule concrete_trace)
       apply (simp add: bigblock1_def)
         apply simp
        apply (rule disjI1)
        apply (rule p_before_cfg_to_dag_prog.node_2)
       apply (rule p_before_cfg_to_dag_prog.outEdges_2)
    apply (rule cfg_is_correct)
      apply simp
     apply (rule cfg_satisfies_post, blast)
     apply simp
    apply (simp add: p_before_cfg_to_dag_prog.node_2)
    apply (rule bigblock1_local_rel)
     apply assumption+
    done
qed


lemma block_then_global_rel:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock_then, KSeq bigblock1 KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_before_cfg_to_dag_prog.proc_body ((Inl 3),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and cfg_satisfies_post: "\<And>m' s'.
                 (A,M,\<Lambda>,\<Gamma>,\<Omega>,p_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 3, Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                 is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns_end) if_example_before_ast_cfg.post)"
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 0) Gt (Lit (LInt 5))), ns1\<rangle> \<Down> LitV (LBool True)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> if_example_before_ast_cfg.post reached_bb reached_cont reached_state)" 
proof -
  have node3_loc: "node_to_block p_before_cfg_to_dag_prog.proc_body ! 3 = [(Assume (BinOp (Var 0) Gt (Lit (LInt 5)))),(Assign 0 (Lit (LInt 10)))]" 
    by (simp add: p_before_cfg_to_dag_prog.block_3_def p_before_cfg_to_dag_prog.node_3)
  show ?thesis 
    apply (rule block_global_rel_generic)
           apply (rule Rel_Main_test[of bigblock_then])
             apply (simp add: bigblock_then_def)
            apply simp
          apply (rule assms(1))
         apply (simp add: bigblock_then_def)
        apply (rule disjI2)
        apply (rule disjI1)
        apply (rule conjI)
         apply (rule node3_loc)
        apply (rule conjI)
         apply simp
        apply (rule trace_is_possible)
       apply (rule assms(2))
        apply simp+
       apply (rule cfg_satisfies_post, blast)
       apply simp+
     apply (simp add: p_before_cfg_to_dag_prog.node_3)
     apply (rule bigblock_then_local_rel)
       apply assumption
      apply simp
     apply (rule trace_is_possible)
    apply (erule allE[where x=2])+
    apply (simp add: p_before_cfg_to_dag_prog.outEdges_3)
    apply (simp add: member_rec(1))
    apply (rule block2_global_rel)
      apply assumption
     apply blast+
    done
qed


lemma block_else_global_rel:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock_else, KSeq bigblock1 KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_before_cfg_to_dag_prog.proc_body ((Inl 1),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and cfg_satisfies_post: "\<And>m' s'.
                 (A,M,\<Lambda>,\<Gamma>,\<Omega>,p_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 1, Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                 is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns_end) if_example_before_ast_cfg.post)"
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 0) Gt (Lit (LInt 5))), ns1\<rangle> \<Down> LitV (LBool False)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> if_example_before_ast_cfg.post reached_bb reached_cont reached_state)" 
proof -
  have node1_loc: "node_to_block p_before_cfg_to_dag_prog.proc_body ! 1 = [(Assume (BinOp (Lit (LInt 5)) Ge (Var 0))),(Assign 0 (Lit (LInt 1)))]" 
    by (simp add: p_before_cfg_to_dag_prog.block_1_def p_before_cfg_to_dag_prog.node_1)
  show ?thesis
    apply (rule block_global_rel_generic)
           apply (rule Rel_Main_test[of bigblock_else])
             apply (simp add: bigblock_else_def)
            apply simp
          apply (rule assms(1))
         apply (simp add: bigblock_else_def)
        apply (rule disjI2)
        apply (rule disjI2)
        apply (rule conjI)
         apply (rule node1_loc)
        apply (rule conjI)
         apply simp
        apply (rule conjI)
         apply (rule neg_gt2)
        apply (rule trace_is_possible)
       apply (rule assms(2))
        apply simp+
       apply (rule cfg_satisfies_post, blast)
       apply simp+
     apply (simp add: p_before_cfg_to_dag_prog.node_1)
     apply (rule bigblock_else_local_rel)
       apply assumption
      apply simp
     apply (rule trace_is_possible)
    apply (erule allE[where x=2])+
    apply (simp add: p_before_cfg_to_dag_prog.outEdges_1)
    apply (simp add: member_rec(1))
    apply (rule block2_global_rel)
      apply assumption
    apply blast+
    done
qed


lemma block0_global_rel:
  assumes  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock0, KSeq bigblock1 KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_satisfies_post: "\<And>m' s'.
                 (A,M,\<Lambda>,\<Gamma>,\<Omega>,p_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 0, Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                 is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns_end) if_example_before_ast_cfg.post)"
  shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> if_example_before_ast_cfg.post reached_bb reached_cont reached_state)" 
proof -
  show ?thesis 
    apply (rule block_global_rel_if_successor)
           apply (rule Rel_Main_test[of bigblock0 _ p_before_cfg_to_dag_prog.block_0])
             apply (simp add: bigblock0_def p_before_cfg_to_dag_prog.block_0_def) 
    apply (simp add: p_before_cfg_to_dag_prog.block_0_def)
          apply (rule ast_trace)
          apply (simp add: bigblock0_def)
         apply (rule disjI1)
        apply (rule p_before_cfg_to_dag_prog.node_0)
       apply (rule assms(1))
        apply simp
       apply (rule cfg_satisfies_post, blast)
       apply simp+
     apply (simp add: p_before_cfg_to_dag_prog.node_0)
     apply (rule bigblock0_local_rel)
      apply (simp add: bigblock0_def)
     apply assumption
    apply simp
    apply (rule disjE)
      apply assumption

     apply (erule allE[where x=3])+
     apply (simp add:p_before_cfg_to_dag_prog.outEdges_0)
     apply (simp add:member_rec(1))
     apply (rule conjE)
      apply assumption
     apply simp
     apply (rule block_then_global_rel)
       apply (simp add: bigblock_then_def)
       apply simp
      apply blast
     apply assumption
   
    apply (erule allE[where x=1])+
    apply (simp add:p_before_cfg_to_dag_prog.outEdges_0)
    apply (simp add:member_rec(1))
    apply (rule conjE)
     apply assumption
    apply (rule block_else_global_rel)
      apply (simp add: bigblock_else_def)
      apply simp
     apply blast
    apply (simp add: false_equals_not_true)
    done
qed

abbreviation \<Lambda>0
  where
    "\<Lambda>0  \<equiv> ((append global_data.constants_vdecls global_data.globals_vdecls),(append if_example_before_ast_cfg.params_vdecls if_example_before_ast_cfg.locals_vdecls))"
lemma end_to_end_theorem_aux3:
assumes 
Red: "rtranclp (red_bigblock A M ((append global_data.constants_vdecls global_data.globals_vdecls),(append if_example_before_ast_cfg.params_vdecls if_example_before_ast_cfg.locals_vdecls)) \<Gamma> [] if_example_before_ast_cfg.proc_body) (bigblock0, (KSeq bigblock1 KStop), Normal ns) (end_bb, end_cont, end_state)" and 
VC: "(\<And> (vc_x::int) (vc_x_0::int) (vc_x_1::int). (vc.vc_anon0 vc_x_0 vc_x_1))" and 
Closed: "(\<And> v. (closed ((type_of_val A) v)))" and 
NonEmptyTypes: "(\<And> t. ((closed t) \<Longrightarrow> (\<exists> v. (((type_of_val A) v) = t))))" and 
FInterp: "(fun_interp_wf A global_data.fdecls \<Gamma>)" and 
Axioms: "(axiom_assm A \<Gamma> global_data.constants_vdecls (ns::(('a)nstate)) global_data.axioms)" and 
Precondition: "(expr_all_sat A \<Lambda>0 \<Gamma> [] ns if_example_before_ast_cfg.pres)" and 
ParamsLocal: "(state_typ_wf A [] (local_state ns) (snd \<Lambda>0))" and 
ConstsGlobal: "(state_typ_wf A [] (global_state ns) (fst \<Lambda>0))" and 
OldGlobal: "((global_state ns) = (old_global_state ns))" and 
BinderNs: "((binder_state ns) = Map.empty)"
shows "(valid_configuration A \<Lambda>0 \<Gamma> [] if_example_before_ast_cfg.post end_bb end_cont end_state)"
proof -
from Red obtain j where Aux:"(A,M,((append global_data.constants_vdecls global_data.globals_vdecls),(append if_example_before_ast_cfg.params_vdecls if_example_before_ast_cfg.locals_vdecls)),\<Gamma>,[],if_example_before_ast_cfg.proc_body \<turnstile> (bigblock0, (KSeq bigblock1 KStop), Normal ns) -n\<longrightarrow>^j (end_bb, end_cont, end_state))"
by (meson rtranclp_imp_relpowp)
  show ?thesis
apply (rule block0_global_rel)
defer
apply (rule Aux)
apply (rule valid_config_implies_not_failure)
apply (rule end_to_end_theorem_aux)
apply (simp add: if_example_before_ast_cfg.params_vdecls_def if_example_before_ast_cfg.locals_vdecls_def
                 p_before_cfg_to_dag_prog.params_vdecls_def p_before_cfg_to_dag_prog.locals_vdecls_def)
using VC apply simp
using Closed apply simp
using NonEmptyTypes apply simp
apply (rule FInterp)
using Axioms apply simp
using Precondition apply (simp add: if_example_before_ast_cfg.params_vdecls_def if_example_before_ast_cfg.locals_vdecls_def
                                    p_before_cfg_to_dag_prog.params_vdecls_def p_before_cfg_to_dag_prog.locals_vdecls_def
                                    if_example_before_ast_cfg.pres_def p_before_cfg_to_dag_prog.pres_def)
using ParamsLocal apply (simp add: if_example_before_ast_cfg.params_vdecls_def if_example_before_ast_cfg.locals_vdecls_def
                                    p_before_cfg_to_dag_prog.params_vdecls_def p_before_cfg_to_dag_prog.locals_vdecls_def)
using ConstsGlobal apply simp
using OldGlobal apply simp
using BinderNs apply simp
done
qed

lemma initialization:                              
  assumes "rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T) (init_ast [bigblock0, bigblock1] ns1) (reached_bb, reached_cont, reached_state)"
  shows "rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T) (bigblock0, KSeq bigblock1 KStop, Normal ns1) (reached_bb, reached_cont, reached_state)" 
  using assms 
  by simp


lemma end_to_end_theorem3:
assumes 
VC: "(\<And> (vc_x::int) (vc_x_0::int) (vc_x_1::int). (vc.vc_anon0 vc_x_0 vc_x_1))"
shows "(\<And> A. (proc_is_correct (A::(('a)absval_ty_fun)) global_data.fdecls global_data.constants_vdecls global_data.globals_vdecls global_data.axioms if_example_before_ast_cfg.proc_ast))"
apply (rule end_to_end_util2[OF end_to_end_theorem_aux3])
apply (rule initialization)
unfolding if_example_before_ast_cfg.proc_body_def
apply assumption using VC apply simp  apply assumption+
apply (simp_all add: 
      exprs_to_only_checked_spec_1 exprs_to_only_checked_spec_2
      if_example_before_ast_cfg.proc_ast_def if_example_before_ast_cfg.proc_body_def)
done
end
