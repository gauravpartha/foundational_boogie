theory no_guard_empty_branch_if_ast_cfg_proof
  imports Main
          Boogie_Lang.Ast
          Boogie_Lang.Semantics
          Boogie_Lang.Ast_Cfg_Transformation
          "../global_data" 
          no_guard_empty_branch_if_before_cfg_to_dag_prog 
          no_guard_empty_branch_if_before_ast_cfg
          no_guard_empty_branch_if_cfgtodag_proof
          "/home/alex/Isabelle_10-Nov-2021/lib/Apply_Trace_Cmd"

begin
declare Nat.One_nat_def[simp del]

definition bigblock_then 
  where "bigblock_then \<equiv> BigBlock None [] None None"

definition bigblock_else
  where "bigblock_else \<equiv> BigBlock None [(Assign 0 (Lit (LInt 6)))] None None"

lemma bigblock0_local_rel:
  assumes Red_bb0_to: 
      "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bigblock0, KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red0_impl: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> no_guard_empty_branch_if_before_cfg_to_dag_prog.block_0 (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)" 
  shows "reached_state \<noteq> Failure \<and> 
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>no_guard_empty_branch_if_before_cfg_to_dag_prog.block_0, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))"
proof -
  show ?thesis 
    apply (rule block_local_rel_generic) 
           apply (rule Rel_Main_test[of bigblock0])
           apply (simp add: bigblock0_def no_guard_empty_branch_if_before_cfg_to_dag_prog.block_0_def)
          apply simp
         apply simp
        apply (rule Red_bb0_to)
       apply (rule Red0_impl)
       apply (simp add: bigblock0_def no_guard_empty_branch_if_before_cfg_to_dag_prog.block_0_def)+
    done
qed

lemma bigblock_else_local_rel:
  assumes Red_bb0_to: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bigblock_else, KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red0_impl: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> no_guard_empty_branch_if_before_cfg_to_dag_prog.block_1 (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)" 
  shows "reached_state \<noteq> Failure \<and> 
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>no_guard_empty_branch_if_before_cfg_to_dag_prog.block_1, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))"
proof -
  show ?thesis
      apply (rule block_local_rel_generic)
             apply (rule Rel_Main_test[of bigblock_else])
             apply (simp add: bigblock_else_def no_guard_empty_branch_if_before_cfg_to_dag_prog.block_1_def)
            apply simp
           apply simp
          apply (rule Red_bb0_to)
         apply (rule Red0_impl)
       apply (simp add: bigblock_else_def no_guard_empty_branch_if_before_cfg_to_dag_prog.block_1_def)+
    done
qed

lemma block_then_global_rel:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock_then, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> no_guard_empty_branch_if_before_cfg_to_dag_prog.proc_body ((Inl 2),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)"                
proof -
  have node2_loc: "node_to_block no_guard_empty_branch_if_before_cfg_to_dag_prog.proc_body ! 2 = []" 
    by (simp add: no_guard_empty_branch_if_before_cfg_to_dag_prog.block_2_def no_guard_empty_branch_if_before_cfg_to_dag_prog.node_2)
  show ?thesis
    apply (rule generic_ending_block_global_rel)
            apply (rule Rel_Main_test[of bigblock_then])
            apply (simp add: bigblock_then_def)
           apply (rule assms(1))
          apply (simp add: bigblock_then_def)
         apply simp
        apply (rule disjI1)
         apply (rule node2_loc)
       apply (rule no_guard_empty_branch_if_before_cfg_to_dag_prog.outEdges_2)
      apply (rule assms(2), simp)
     apply simp
    apply (simp add: bigblock_then_def)
    apply (simp add: end_static)
    done
qed


lemma block_else_global_rel:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock_else, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> no_guard_empty_branch_if_before_cfg_to_dag_prog.proc_body ((Inl 1),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)" 
proof -
  have node1_loc: "node_to_block no_guard_empty_branch_if_before_cfg_to_dag_prog.proc_body ! 1 = [(Assign 0 (Lit (LInt 6)))]" 
    by (simp add: no_guard_empty_branch_if_before_cfg_to_dag_prog.block_1_def no_guard_empty_branch_if_before_cfg_to_dag_prog.node_1)
  show ?thesis
    apply (rule generic_ending_block_global_rel)
           apply (rule Rel_Main_test[of bigblock_else])
           apply (simp add: bigblock_else_def)
          apply (rule assms(1))
          apply (simp add: bigblock_else_def)
         apply simp
        apply (rule disjI1)
        apply (rule node1_loc)
       apply (simp add: no_guard_empty_branch_if_before_cfg_to_dag_prog.outEdges_1)
       apply (rule assms(2))
       apply simp+
     apply (simp add: no_guard_empty_branch_if_before_cfg_to_dag_prog.node_1)
     apply (rule bigblock_else_local_rel)
       apply assumption
      apply simp
    done
qed


lemma block0_global_rel:
  assumes  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> no_guard_empty_branch_if_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock0, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)" 
proof -
  show ?thesis 
    apply (rule block_global_rel_if_successor)
           apply (rule Rel_Main_test[of bigblock0 _ no_guard_empty_branch_if_before_cfg_to_dag_prog.block_0])
           apply (simp add: bigblock0_def no_guard_empty_branch_if_before_cfg_to_dag_prog.block_0_def)
          apply (rule ast_trace)
          apply (simp add: bigblock0_def)
         apply (rule disjI1)
        apply (rule no_guard_empty_branch_if_before_cfg_to_dag_prog.node_0)
       apply (rule assms(1))
        apply simp+
     apply (simp add: no_guard_empty_branch_if_before_cfg_to_dag_prog.node_0)
     apply (rule bigblock0_local_rel)
      apply (simp add: bigblock0_def)
     apply assumption
    apply simp
    apply (rule disjE)
      apply assumption

     apply (erule allE[where x=2])
     apply (simp add:no_guard_empty_branch_if_before_cfg_to_dag_prog.outEdges_0)
     apply (simp add:member_rec(1))
    unfolding no_guard_empty_branch_if_before_cfg_to_dag_prog.post_def
     apply (rule block_then_global_rel)
       apply (simp add: bigblock_then_def)       
      apply simp
   
    apply (erule allE[where x=1])
    apply (simp add:no_guard_empty_branch_if_before_cfg_to_dag_prog.outEdges_0)
    apply (simp add:member_rec(1))
    apply (rule block_else_global_rel)
      apply (simp add: bigblock_else_def)
     apply simp
    done
qed