theory consecutive_ifs_ast_cfg_proof
  imports Main
          Boogie_Lang.Ast
          Boogie_Lang.Semantics
          Boogie_Lang.Ast_Cfg_Transformation
          "../global_data" 
          consecutive_ifs_before_cfg_to_dag_prog 
          consecutive_ifs_before_ast_cfg
          consecutive_ifs_cfgtodag_proof
          "/home/alex/Isabelle_10-Nov-2021/lib/Apply_Trace_Cmd"

begin

abbreviation bigblock_then0 
  where "bigblock_then0 \<equiv> BigBlock None [(Assign 0 (Lit (LInt 5)))] None None"

abbreviation bigblock_else0
  where "bigblock_else0 \<equiv> BigBlock None [] None None"

abbreviation bigblock_then1 
  where "bigblock_then1 \<equiv> BigBlock None [(Assign 0 (Lit (LInt 1)))] None None"

abbreviation bigblock_else1
  where "bigblock_else1 \<equiv> BigBlock None [(Assign 0 (UnOp UMinus (Lit (LInt 1))))] None None"

lemma bigblock0_local_rel:
  assumes Red_bb0_to: 
      "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bigblock0, KSeq bigblock1 KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red0_impl: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> [Havoc 0] (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)" 
  shows "reached_state \<noteq> Failure \<and> 
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>[Havoc 0], Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))"
proof -
  have "ast_cfg_rel None [] bigblock0 consecutive_ifs_before_cfg_to_dag_prog.block_0" 
    unfolding consecutive_ifs_before_cfg_to_dag_prog.block_0_def
    by (rule Rel_Main_test)
  then show ?thesis 
    using assms
    unfolding consecutive_ifs_before_cfg_to_dag_prog.block_0_def
    by (auto simp: block_local_rel_generic) 
qed


lemma bigblock_then0_local_rel:
  assumes Red_bb0_to: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bigblock_then0, KSeq bigblock1 KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red0_impl: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_cfg_to_dag_prog.block_5 (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)" 
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 0) Gt (Lit (LInt 0))), ns1\<rangle> \<Down> LitV (LBool True)"
  shows "reached_state \<noteq> Failure \<and> 
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>consecutive_ifs_before_cfg_to_dag_prog.block_5, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
proof -
  have syntactic_rel: "ast_cfg_rel None [] bigblock_then0 [(Assign 0 (Lit (LInt 5)))]" 
    by (rule Rel_Main_test)
  show ?thesis
    unfolding consecutive_ifs_before_cfg_to_dag_prog.block_5_def 
    apply (rule block_local_rel_guard_true[OF syntactic_rel _ _ _  trace_is_possible Red_bb0_to Red0_impl])
    unfolding consecutive_ifs_before_cfg_to_dag_prog.block_5_def 
    by simp_all
qed

lemma bigblock_then1_local_rel:
  assumes Red_bb0_to: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bigblock_then1, KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red0_impl: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_cfg_to_dag_prog.block_4 (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)" 
  shows "reached_state \<noteq> Failure \<and> 
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>consecutive_ifs_before_cfg_to_dag_prog.block_4, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
proof -
  have syntactic_rel: "ast_cfg_rel None [] bigblock_then1 [(Assign 0 (Lit (LInt 1)))]" 
    by (rule Rel_Main_test)
  show ?thesis
    unfolding consecutive_ifs_before_cfg_to_dag_prog.block_4_def 
    apply (rule block_local_rel_generic)
          apply (rule syntactic_rel)
         apply simp
        apply simp
       apply simp
      apply simp
     apply (rule Red_bb0_to)
    by (simp add: Red0_impl consecutive_ifs_before_cfg_to_dag_prog.block_4_def)
qed

lemma bigblock_else1_local_rel:
  assumes Red_bb0_to: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bigblock_else1, KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red0_impl: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_cfg_to_dag_prog.block_3 (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)" 
  shows "reached_state \<noteq> Failure \<and> 
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>consecutive_ifs_before_cfg_to_dag_prog.block_3, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
proof -
  have syntactic_rel: "ast_cfg_rel None [] bigblock_else1 [(Assign 0 (UnOp UMinus (Lit (LInt 1))))]" 
    by (rule Rel_Main_test)
  show ?thesis
    unfolding consecutive_ifs_before_cfg_to_dag_prog.block_3_def 
    apply (rule block_local_rel_generic)
          apply (rule syntactic_rel)
         apply simp
        apply simp
       apply simp
      apply simp
     apply (rule Red_bb0_to)
    by (simp add: Red0_impl consecutive_ifs_before_cfg_to_dag_prog.block_3_def)
qed


lemma block_then1_global_rel:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock_then1, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_cfg_to_dag_prog.proc_body ((Inl 4),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)" 
proof -
  have syntactic_rel: "ast_cfg_rel None [] bigblock_then1 [(Assign 0 (Lit (LInt 1)))]"
    by (simp add: Rel_Main_test)
  have succ: "(out_edges(consecutive_ifs_before_cfg_to_dag_prog.proc_body) ! 4) = []" 
    by (simp add: consecutive_ifs_before_cfg_to_dag_prog.outEdges_4) 
  have node_4_local: "node_to_block(consecutive_ifs_before_cfg_to_dag_prog.proc_body) ! 4 = [Assign 0 (Lit (LInt 1))]"
    by (simp add: consecutive_ifs_before_cfg_to_dag_prog.block_4_def consecutive_ifs_before_cfg_to_dag_prog.node_4)

  show ?thesis 
    apply (rule generic_ending_block_global_rel)
        apply (rule syntactic_rel)
       apply (rule assms(1))
      apply simp
     apply (rule node_4_local)
    apply (rule assms(2))
    apply simp
    done
qed

lemma block_else1_global_rel:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock_else1, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_cfg_to_dag_prog.proc_body ((Inl 3),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)" 
proof -
  have syntactic_rel: "ast_cfg_rel None [] bigblock_else1  [(Assign 0 (UnOp UMinus (Lit (LInt 1))))]"
    by (simp add: Rel_Main_test)
  have succ: "(out_edges(consecutive_ifs_before_cfg_to_dag_prog.proc_body) ! 3) = []" 
    by (simp add: consecutive_ifs_before_cfg_to_dag_prog.outEdges_3) 
  have node_3_local: "node_to_block(consecutive_ifs_before_cfg_to_dag_prog.proc_body) ! 3 = [(Assign 0 (UnOp UMinus (Lit (LInt 1))))]"
    by (simp add: consecutive_ifs_before_cfg_to_dag_prog.block_3_def consecutive_ifs_before_cfg_to_dag_prog.node_3)

  show ?thesis 
    apply (rule generic_ending_block_global_rel)
        apply (rule syntactic_rel)
       apply (rule assms(1))
      apply simp
     apply (rule node_3_local)
    apply (rule assms(2))
    apply simp
    done
qed


lemma block1_global_rel:
  assumes  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_cfg_to_dag_prog.proc_body ((Inl 2),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock1, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_cfg_to_dag_prog.post reached_bb reached_cont reached_state)" 
proof -
  have cmds: "node_to_block(consecutive_ifs_before_cfg_to_dag_prog.proc_body) ! 2 = []" 
    using consecutive_ifs_before_cfg_to_dag_prog.block_2_def consecutive_ifs_before_cfg_to_dag_prog.node_2 by auto
  have syntactic_rel: "ast_cfg_rel None [] bigblock1 []"  
    by (simp add: Rel_Main_test)
  have succ: "(out_edges(consecutive_ifs_before_cfg_to_dag_prog.proc_body) ! 2) = [4, 3]" 
    using consecutive_ifs_before_cfg_to_dag_prog.outEdges_2 by auto 
  show ?thesis 
    apply (rule block_global_rel_if_successor)
          apply (rule syntactic_rel)
         apply (rule ast_trace)
        apply (rule cmds)
       apply (rule assms(1))
       apply simp
      apply simp
     apply simp
    apply simp
    apply (rule disjE)
      apply assumption

     apply (erule allE[where x=4])
     apply (simp add:succ)
     apply (simp add:member_rec(1))
    unfolding consecutive_ifs_before_cfg_to_dag_prog.post_def
     apply (rule block_then1_global_rel)
      apply assumption
     apply simp
   
    apply (erule allE[where x=3])
    apply (simp del: Nat.One_nat_def add:succ)
    apply (simp del: Nat.One_nat_def add:member_rec(1))
    apply (rule block_else1_global_rel)
     apply assumption
    apply simp
    done
qed

end