theory nested_if_ast_cfg_proof
  imports Main
          Boogie_Lang.Ast
          Boogie_Lang.Semantics
          Boogie_Lang.Ast_Cfg_Transformation
          "../global_data" 
          nested_if_before_cfg_to_dag_prog 
          nested_if_before_ast_cfg
          nested_if_cfgtodag_proof
          "/home/alex/Isabelle_10-Nov-2021/lib/Apply_Trace_Cmd"

begin
declare Nat.One_nat_def[simp del]

definition outer_then where
  "outer_then = (BigBlock None [] 
                      (Some (ParsedIf 
                            (Some (BinOp (Var 1) Gt (Lit (LInt 0)))) 
                            [(BigBlock None [(Assign 1 (BinOp (Var 1) Add (Var 0)))] None None)]
                            [(BigBlock None [(Assign 1 (Var 0))] None None)] ) )
                       None )"

definition outer_else where
  "outer_else = (BigBlock None [] None None)"

definition inner_then where
  "inner_then = (BigBlock None [(Assign 1 (BinOp (Var 1) Add (Var 0)))] None None)"

definition inner_else where
  "inner_else = (BigBlock None [(Assign 1 (Var 0))] None None)"

lemma bigblock0_local_rel:
  assumes Red_bb0_to: 
      "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bigblock0, KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red0_impl: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> nested_if_before_cfg_to_dag_prog.block_0 (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)" 
  shows "reached_state \<noteq> Failure \<and> 
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>nested_if_before_cfg_to_dag_prog.block_0, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))"
proof -
  show ?thesis 
    apply (rule block_local_rel_generic) 
           apply (rule Rel_Main_test[of bigblock0])
            apply (simp add: bigblock0_def nested_if_before_cfg_to_dag_prog.block_0_def)
           apply (simp add: nested_if_before_cfg_to_dag_prog.block_0_def)
          apply simp
         apply simp
        apply (rule Red_bb0_to)
       apply (rule Red0_impl, simp)
      apply (simp add: bigblock0_def)
     apply simp
    apply (simp add: nested_if_before_cfg_to_dag_prog.block_0_def)
    done
qed

lemma inner_then_local_rel:
  assumes Red_bb0_to: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (inner_then, KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red0_impl: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> nested_if_before_cfg_to_dag_prog.block_4 (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)" 
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 1) Gt (Lit (LInt 0))), ns1\<rangle> \<Down> LitV (LBool True)"
  shows "reached_state \<noteq> Failure \<and> 
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>nested_if_before_cfg_to_dag_prog.block_4, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
proof -
  show ?thesis
    apply (simp add: nested_if_before_cfg_to_dag_prog.block_4_def)
    apply (rule guard_holds_push_through_assumption)
      apply (rule block_local_rel_generic)
             apply (rule Rel_Main_test[of inner_then])
             apply (simp add: inner_then_def)
            apply simp
           apply simp+
          apply (rule Red_bb0_to)
         apply (rule push_through_assumption_test1, rule Red0_impl)
         apply (simp add: nested_if_before_cfg_to_dag_prog.block_4_def)
           apply (simp add: trace_is_possible inner_then_def)+
    done
qed

lemma inner_else_local_rel:
  assumes Red_bb0_to: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (inner_else, KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red0_impl: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> nested_if_before_cfg_to_dag_prog.block_3 (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)" 
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 1) Gt (Lit (LInt 0))), ns1\<rangle> \<Down> LitV (LBool False)"
  shows "reached_state \<noteq> Failure \<and> 
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>nested_if_before_cfg_to_dag_prog.block_3, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))"
proof -
  show ?thesis
    apply (simp add: nested_if_before_cfg_to_dag_prog.block_3_def)
    apply (rule guard_fails_push_through_assumption)
      apply (rule block_local_rel_generic)
             apply (rule Rel_Main_test[of inner_else])
             apply (simp add: inner_else_def)
            apply simp
           apply simp+
          apply (rule Red_bb0_to)
         apply (rule Red0_impl)
         apply (simp add: nested_if_before_cfg_to_dag_prog.block_3_def)
         apply (rule push_through_assumption1)
             apply simp
            apply (rule neg_gt2)
          apply (rule trace_is_possible)
         apply simp
        apply (simp add: inner_else_def)
        apply simp+
     apply (rule neg_gt2)
    apply (rule trace_is_possible)
    done
qed

lemma outer_else_global_rel:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (outer_else, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> nested_if_before_cfg_to_dag_prog.proc_body ((Inl 1),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and cfg_satisfies_post: "\<And>m' s'.
                           (A,M,\<Lambda>,\<Gamma>,\<Omega>,nested_if_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 1, Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                           is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns_end) nested_if_before_ast_cfg.post)"
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 0) Gt (Lit (LInt 0))), ns1\<rangle> \<Down> LitV (LBool False)"
shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> nested_if_before_ast_cfg.post reached_bb reached_cont reached_state)" 
proof -                                                            
  have node1_loc: "node_to_block nested_if_before_cfg_to_dag_prog.proc_body ! 1 = [(Assume (BinOp (Lit (LInt 0)) Ge (Var 0)))]" 
    by (simp add: nested_if_before_cfg_to_dag_prog.block_1_def nested_if_before_cfg_to_dag_prog.node_1)
  show ?thesis
  apply (rule generic_ending_block_global_rel)
           apply (rule Rel_Invs[of outer_else])
           apply (simp add: outer_else_def)
          apply (rule assms(1))
          apply (simp add: outer_else_def)
         apply simp
        apply (rule disjI2)
        apply (rule disjI2)
        apply (rule conjI)
         apply (rule node1_loc)
        apply (rule conjI)
         apply simp
        apply (rule conjI)
         apply (rule neg_gt2)
        apply (rule trace_is_possible)
       apply (simp add: nested_if_before_cfg_to_dag_prog.outEdges_1)
       apply (rule assms(2))
      apply simp+
     apply (rule cfg_satisfies_post, blast)
     apply (simp add: nested_if_before_cfg_to_dag_prog.node_1)
     apply (rule end_static)
      apply (simp add: outer_else_def)
    done
qed

lemma inner_else_global_rel:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inner_else, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> nested_if_before_cfg_to_dag_prog.proc_body ((Inl 3),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and cfg_satisfies_post: "\<And>m' s'.
                           (A,M,\<Lambda>,\<Gamma>,\<Omega>,nested_if_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 3, Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                           is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns_end) nested_if_before_ast_cfg.post)"
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 1) Gt (Lit (LInt 0))), ns1\<rangle> \<Down> LitV (LBool False)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> nested_if_before_ast_cfg.post reached_bb reached_cont reached_state)" 
proof -
  have node3_loc: "node_to_block nested_if_before_cfg_to_dag_prog.proc_body ! 3 = [(Assume (BinOp (Lit (LInt 0)) Ge (Var 1))),(Assign 1 (Var 0))]" 
    by (simp add: nested_if_before_cfg_to_dag_prog.block_3_def nested_if_before_cfg_to_dag_prog.node_3)
  show ?thesis
    apply (rule generic_ending_block_global_rel)
           apply (rule Rel_Main_test[of inner_else])
             apply (simp add: inner_else_def)
            apply simp
          apply (rule assms(1))
          apply (simp add: inner_else_def)
         apply simp
        apply (rule disjI2)
        apply (rule disjI2)
        apply (rule conjI)
         apply (rule node3_loc)
        apply (rule conjI)
         apply simp
        apply (rule conjI)
         apply (rule neg_gt2)
        apply (rule trace_is_possible)
       apply (simp add: nested_if_before_cfg_to_dag_prog.outEdges_3)
       apply (rule assms(2))
      apply simp+
     apply (rule cfg_satisfies_post, blast)
     apply (simp add: nested_if_before_cfg_to_dag_prog.node_3)+
     apply (rule inner_else_local_rel)
       apply assumption
      apply simp
     apply (rule trace_is_possible)
    done
qed

lemma inner_then_global_rel:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inner_then, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> nested_if_before_cfg_to_dag_prog.proc_body ((Inl 4),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and cfg_satisfies_post: "\<And>m' s'.
                           (A,M,\<Lambda>,\<Gamma>,\<Omega>,nested_if_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 4, Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                           is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns_end) nested_if_before_ast_cfg.post)"
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 1) Gt (Lit (LInt 0))), ns1\<rangle> \<Down> LitV (LBool True)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> nested_if_before_ast_cfg.post reached_bb reached_cont reached_state)" 
proof -
  have node4_loc: "node_to_block nested_if_before_cfg_to_dag_prog.proc_body ! 4 = [(Assume (BinOp (Var 1) Gt (Lit (LInt 0)))),(Assign 1 (BinOp (Var 1) Add (Var 0)))]" 
    by (simp add: nested_if_before_cfg_to_dag_prog.block_4_def nested_if_before_cfg_to_dag_prog.node_4)
  show ?thesis
    apply (rule generic_ending_block_global_rel)
           apply (rule Rel_Main_test[of inner_then])
             apply (simp add: inner_then_def)
            apply simp
          apply (rule assms(1))
          apply (simp add: inner_then_def)
         apply simp
        apply (rule disjI2)
        apply (rule disjI1)
        apply (rule conjI)
         apply (rule node4_loc)
        apply (rule conjI)
         apply simp
        apply (rule trace_is_possible)
       apply (simp add: nested_if_before_cfg_to_dag_prog.outEdges_4)
       apply (rule assms(2))
      apply simp+
     apply (rule cfg_satisfies_post, blast)
     apply (simp add: nested_if_before_cfg_to_dag_prog.node_4)+
     apply (rule inner_then_local_rel)
       apply assumption
      apply simp
     apply (rule trace_is_possible)
    done
qed

lemma outer_then_global_rel:
  assumes  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> nested_if_before_cfg_to_dag_prog.proc_body ((Inl 2),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and cfg_satisfies_post: "\<And>m' s'.
                           (A,M,\<Lambda>,\<Gamma>,\<Omega>,nested_if_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 2, Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                           is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns_end) nested_if_before_ast_cfg.post)"
  and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (outer_then, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 0) Gt (Lit (LInt 0))), ns1\<rangle> \<Down> LitV (LBool True)"
  shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> nested_if_before_ast_cfg.post reached_bb reached_cont reached_state)" 
proof -
  have node2_loc: "node_to_block nested_if_before_cfg_to_dag_prog.proc_body ! 2 = [(Assume (BinOp (Var 0) Gt (Lit (LInt 0))))]" 
    by (simp add: nested_if_before_cfg_to_dag_prog.block_2_def nested_if_before_cfg_to_dag_prog.node_2)
  show ?thesis 
    apply (rule block_global_rel_if_successor)
           apply (rule Rel_Invs[of outer_then])
           apply (simp add: outer_then_def) 
          apply (rule ast_trace)
          apply (simp add: outer_then_def)
         apply (rule disjI2)
         apply (rule disjI1)
         apply (rule conjI)
          apply (rule node2_loc)
         apply (rule conjI)
          apply simp
         apply (rule trace_is_possible)
        apply (rule assms(1))
        apply simp
       apply (rule cfg_satisfies_post, blast)
       apply simp
      apply simp
     apply simp
    apply simp
    apply (rule disjE)
      apply assumption

     apply (erule allE[where x=4])+
     apply (simp add:nested_if_before_cfg_to_dag_prog.outEdges_2)
     apply (simp add:member_rec(1))
     apply (rule conjE)
      apply assumption
     apply simp
     apply (rule inner_then_global_rel)
       apply (simp add: inner_then_def)
       apply simp
      apply blast
     apply assumption
   
    apply (erule allE[where x=3])+
    apply (simp add:nested_if_before_cfg_to_dag_prog.outEdges_2)
    apply (simp add:member_rec(1))
    apply (rule conjE)
     apply assumption
    apply (rule inner_else_global_rel)
      apply (simp add: inner_else_def)
      apply simp+
     apply blast+
    done
qed

lemma entry_block_global_rel:
  assumes  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> nested_if_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and cfg_satisfies_post: "\<And>m' s'.
                           (A,M,\<Lambda>,\<Gamma>,\<Omega>,nested_if_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 0, Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                           is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns_end) nested_if_before_ast_cfg.post)"
  and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock0, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> nested_if_before_ast_cfg.post reached_bb reached_cont reached_state)" 
proof -
  have node0_loc: "node_to_block nested_if_before_cfg_to_dag_prog.proc_body ! 0 = [(Havoc 0),(Havoc 1)]" 
    by (simp add: nested_if_before_cfg_to_dag_prog.block_0_def nested_if_before_cfg_to_dag_prog.node_0)
  show ?thesis 
    apply (rule block_global_rel_if_successor)
           apply (rule Rel_Main_test[of bigblock0])
             apply (simp add: bigblock0_def)
            apply simp
          apply (rule ast_trace)
          apply (simp add: bigblock0_def)
         apply (rule disjI1)
          apply (rule node0_loc)
        apply (rule assms(1))
        apply simp
       apply (rule cfg_satisfies_post, blast)
       apply simp
       apply simp
      apply simp
    apply (simp add: nested_if_before_cfg_to_dag_prog.node_0)
     apply (rule bigblock0_local_rel)
      apply (simp add: bigblock0_def)
     apply simp+
    apply (rule disjE)
      apply assumption

     apply (erule allE[where x=2])+
     apply (simp add:nested_if_before_cfg_to_dag_prog.outEdges_0)
     apply (simp add:member_rec(1))
     apply (rule conjE)
      apply assumption
     apply simp
     apply (rule outer_then_global_rel)
        apply auto[1]
       apply blast
       apply (simp add: outer_then_def)
      apply simp
   
    apply (erule allE[where x=1])+
    apply (simp add:nested_if_before_cfg_to_dag_prog.outEdges_0)
    apply (simp add:member_rec(1))
    apply (rule conjE)
     apply assumption
    apply (rule outer_else_global_rel)
      apply (simp add: outer_else_def)
      apply simp+
     apply blast+
    done
qed

end