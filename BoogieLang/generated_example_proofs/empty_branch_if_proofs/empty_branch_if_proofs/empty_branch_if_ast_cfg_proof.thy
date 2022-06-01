theory empty_branch_if_ast_cfg_proof
  imports Main
          Boogie_Lang.Ast
          Boogie_Lang.Semantics
          Boogie_Lang.Ast_Cfg_Transformation
          "../global_data" 
          empty_branch_if_before_cfg_to_dag_prog 
          empty_branch_if_before_ast_cfg
          empty_branch_if_cfgtodag_proof
          "/home/alex/Isabelle_10-Nov-2021/lib/Apply_Trace_Cmd"

begin
declare Nat.One_nat_def[simp del]

definition bigblock_then 
  where "bigblock_then \<equiv> BigBlock None [] None None"

definition bigblock_else
  where "bigblock_else \<equiv> BigBlock None [(Assign 0 (Lit (LInt 6)))] None None"

lemma bigblock0_local_rel:
  assumes Red_bb0_to: 
      "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bigblock0, KSeq bigblock1 KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red0_impl: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> empty_branch_if_before_cfg_to_dag_prog.block_0 (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)" 
  shows "reached_state \<noteq> Failure \<and> 
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>empty_branch_if_before_cfg_to_dag_prog.block_0, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))"
proof -
  show ?thesis 
    apply (rule block_local_rel_generic) 
           apply (rule Rel_Main_test[of bigblock0])
           apply (simp add: bigblock0_def empty_branch_if_before_cfg_to_dag_prog.block_0_def)
          apply simp
         apply simp
        apply (rule Red_bb0_to)
       apply (rule Red0_impl)
       apply (simp add: bigblock0_def empty_branch_if_before_cfg_to_dag_prog.block_0_def)+
    done
qed

lemma bigblock_else_local_rel:
  assumes Red_bb0_to: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bigblock_else, KSeq bigblock1 KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red0_impl: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> empty_branch_if_before_cfg_to_dag_prog.block_1 (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)" 
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 0) Gt (Lit (LInt 5))), ns1\<rangle> \<Down> LitV (LBool False)"
  shows "reached_state \<noteq> Failure \<and> 
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>empty_branch_if_before_cfg_to_dag_prog.block_1, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))"
proof -
  show ?thesis
    apply (simp add: empty_branch_if_before_cfg_to_dag_prog.block_1_def)
    apply (rule guard_fails_push_through_assumption)
      apply (rule block_local_rel_generic)
             apply (rule Rel_Main_test[of bigblock_else])
             apply (simp add: bigblock_else_def)
            apply simp
           apply simp
          apply (rule Red_bb0_to)
         apply (rule Red0_impl)
         apply (simp add: empty_branch_if_before_cfg_to_dag_prog.block_1_def)
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
  and Red0_impl: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> empty_branch_if_before_cfg_to_dag_prog.block_2 (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)" 
  shows "reached_state \<noteq> Failure \<and> 
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>empty_branch_if_before_cfg_to_dag_prog.block_2, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))"
proof -
  show ?thesis 
    apply (rule block_local_rel_generic) 
           apply (rule Rel_Main_test[of bigblock1])
           apply (simp add: bigblock1_def empty_branch_if_before_cfg_to_dag_prog.block_2_def)
          apply simp
         apply simp
        apply (rule Red_bb0_to)
       apply (rule Red0_impl)
       apply (simp add: bigblock1_def empty_branch_if_before_cfg_to_dag_prog.block_2_def)+
    done
qed

lemma block2_global_rel:
  assumes concrete_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock1, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> empty_branch_if_before_cfg_to_dag_prog.proc_body ((Inl 2),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)" 
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)" 
  using assms
proof -
  show ?thesis
    apply (rule generic_ending_block_global_rel)
         apply (rule Rel_Main_test[of bigblock1 _ empty_branch_if_before_cfg_to_dag_prog.block_2])
         apply (simp add: bigblock1_def empty_branch_if_before_cfg_to_dag_prog.block_2_def)
        apply (rule concrete_trace)
       apply (simp add: bigblock1_def)
         apply simp
        apply (rule disjI1)
        apply (rule empty_branch_if_before_cfg_to_dag_prog.node_2)
       apply (rule empty_branch_if_before_cfg_to_dag_prog.outEdges_2)
    apply (rule cfg_is_correct)
      apply simp+
    apply (simp add: empty_branch_if_before_cfg_to_dag_prog.node_2)
    apply (rule bigblock1_local_rel)
     apply assumption+
    done
qed


lemma block_then_global_rel:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock_then, KSeq bigblock1 KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> empty_branch_if_before_cfg_to_dag_prog.proc_body ((Inl 3),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 0) Gt (Lit (LInt 5))), ns1\<rangle> \<Down> LitV (LBool True)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)" 
proof -                    
  have node3_loc: "node_to_block empty_branch_if_before_cfg_to_dag_prog.proc_body ! 3 = [(Assume (BinOp (Var 0) Gt (Lit (LInt 5))))]" 
    by (simp add: empty_branch_if_before_cfg_to_dag_prog.block_3_def empty_branch_if_before_cfg_to_dag_prog.node_3)
  show ?thesis 
    apply (rule block_global_rel_generic)
           apply (rule Rel_Main_test[of bigblock_then])
           apply (simp add: bigblock_then_def)
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
        apply simp
       apply simp
      apply simp
     apply simp
    apply (erule allE[where x=2])
    apply (rule block2_global_rel)
     apply assumption
    apply (simp add: empty_branch_if_before_cfg_to_dag_prog.outEdges_3)
    apply (simp add: member_rec(1))
    done
qed


lemma block_else_global_rel:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock_else, KSeq bigblock1 KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> empty_branch_if_before_cfg_to_dag_prog.proc_body ((Inl 1),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 0) Gt (Lit (LInt 5))), ns1\<rangle> \<Down> LitV (LBool False)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)" 
proof -
  have node1_loc: "node_to_block empty_branch_if_before_cfg_to_dag_prog.proc_body ! 1 = [(Assume (BinOp (Lit (LInt 5)) Ge (Var 0))),(Assign 0 (Lit (LInt 6)))]" 
    by (simp add: empty_branch_if_before_cfg_to_dag_prog.block_1_def empty_branch_if_before_cfg_to_dag_prog.node_1)
  show ?thesis
    apply (rule block_global_rel_generic)
           apply (rule Rel_Main_test[of bigblock_else])
           apply (simp add: bigblock_else_def)
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
     apply (simp add: empty_branch_if_before_cfg_to_dag_prog.node_1)
     apply (rule bigblock_else_local_rel)
       apply assumption
      apply simp
     apply (rule trace_is_possible)
    apply (erule allE[where x=2])
    apply (rule block2_global_rel)
     apply assumption
    apply (simp add: empty_branch_if_before_cfg_to_dag_prog.outEdges_1)
    apply (simp add: member_rec(1))
    done
qed


lemma block0_global_rel:
  assumes  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> empty_branch_if_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock0, KSeq bigblock1 KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> empty_branch_if_before_cfg_to_dag_prog.post reached_bb reached_cont reached_state)" 
proof -
  show ?thesis 
    apply (rule block_global_rel_if_successor)
           apply (rule Rel_Main_test[of bigblock0 _ empty_branch_if_before_cfg_to_dag_prog.block_0])
           apply (simp add: bigblock0_def empty_branch_if_before_cfg_to_dag_prog.block_0_def)
          apply (rule ast_trace)
          apply (simp add: bigblock0_def)
         apply (rule disjI1)
        apply (rule empty_branch_if_before_cfg_to_dag_prog.node_0)
        apply (rule assms(1))
        apply simp
    unfolding empty_branch_if_before_cfg_to_dag_prog.post_def
       apply simp+
     apply (simp add: empty_branch_if_before_cfg_to_dag_prog.node_0)
     apply (rule bigblock0_local_rel)
      apply (simp add: bigblock0_def)
     apply assumption
    apply simp
    apply (rule disjE)
      apply assumption

     apply (erule allE[where x=3])
     apply (simp add:empty_branch_if_before_cfg_to_dag_prog.outEdges_0)
     apply (simp add:member_rec(1))
     apply (rule conjE)
      apply assumption
    unfolding empty_branch_if_before_cfg_to_dag_prog.post_def
     apply (rule block_then_global_rel)
       apply (simp add: bigblock_then_def)       
      apply simp
     apply assumption
   
    apply (erule allE[where x=1])
    apply (simp add:empty_branch_if_before_cfg_to_dag_prog.outEdges_0)
    apply (simp add:member_rec(1))
    apply (rule conjE)
     apply assumption
    apply (rule block_else_global_rel)
      apply (simp add: bigblock_else_def)
     apply simp+
    done
qed