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
declare Nat.One_nat_def[simp del]

definition bigblock_then0 
  where "bigblock_then0 \<equiv> BigBlock None [(Assign 0 (Lit (LInt 5)))] None None"

definition bigblock_else0
  where "bigblock_else0 \<equiv> BigBlock None [] None None"

definition bigblock_then1 
  where "bigblock_then1 \<equiv> BigBlock None [(Assign 0 (Lit (LInt 1)))] None None"

definition bigblock_else1
  where "bigblock_else1 \<equiv> BigBlock None [(Assign 0 (UnOp UMinus (Lit (LInt 1))))] None None"

lemma bigblock0_local_rel:
  assumes Red_bb0_to: 
      "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bigblock0, KSeq bigblock1 KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red0_impl: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_cfg_to_dag_prog.block_0 (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)" 
  shows "reached_state \<noteq> Failure \<and> 
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>consecutive_ifs_before_cfg_to_dag_prog.block_0, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))"
proof -
  show ?thesis 
    apply (rule block_local_rel_generic) 
           apply (rule Rel_Main_test[of bigblock0])
            apply (simp add: bigblock0_def consecutive_ifs_before_cfg_to_dag_prog.block_0_def)
           apply (simp add: consecutive_ifs_before_cfg_to_dag_prog.block_0_def)
          apply simp
         apply simp
        apply (rule Red_bb0_to)
       apply (rule Red0_impl)
       apply (simp add: bigblock0_def consecutive_ifs_before_cfg_to_dag_prog.block_0_def)+
    done
qed


lemma bigblock_then0_local_rel:
  assumes Red_bb0_to: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bigblock_then0, KSeq bigblock1 KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red0_impl: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_cfg_to_dag_prog.block_5 (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)" 
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 0) Gt (Lit (LInt 0))), ns1\<rangle> \<Down> LitV (LBool True)"
  shows "reached_state \<noteq> Failure \<and> 
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>consecutive_ifs_before_cfg_to_dag_prog.block_5, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
proof -
  show ?thesis
    apply (simp add: consecutive_ifs_before_cfg_to_dag_prog.block_5_def)
    apply (rule guard_holds_push_through_assumption)
      apply (rule block_local_rel_generic)
             apply (rule Rel_Main_test[of bigblock_then0])
             apply (simp add: bigblock_then0_def)
            apply simp
           apply simp+
          apply (rule Red_bb0_to)
         apply (rule push_through_assumption_test1, rule Red0_impl)
         apply (simp add: consecutive_ifs_before_cfg_to_dag_prog.block_5_def)
           apply (simp add: trace_is_possible bigblock_then0_def)+
    done
qed                                                                                 

lemma bigblock_then1_local_rel:
  assumes Red_bb0_to: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bigblock_then1, KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red0_impl: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_cfg_to_dag_prog.block_4 (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)" 
  shows "reached_state \<noteq> Failure \<and> 
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>consecutive_ifs_before_cfg_to_dag_prog.block_4, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
proof -
  show ?thesis
      apply (rule block_local_rel_generic)
             apply (rule Rel_Main_test[of bigblock_then1])
            apply (simp add: bigblock_then1_def consecutive_ifs_before_cfg_to_dag_prog.block_4_def)
           apply (simp add: consecutive_ifs_before_cfg_to_dag_prog.block_4_def)
          apply simp
         apply simp
        apply (rule Red_bb0_to)
       apply (rule Red0_impl)
       apply (simp add: consecutive_ifs_before_cfg_to_dag_prog.block_4_def bigblock_then1_def)+
    done
qed 

lemma bigblock_else1_local_rel:
  assumes Red_bb0_to: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bigblock_else1, KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red0_impl: "(\<And> s2'.(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_cfg_to_dag_prog.block_3 (Normal ns1) s2') \<Longrightarrow> s2' \<noteq> Failure)" 
  shows "reached_state \<noteq> Failure \<and> 
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>consecutive_ifs_before_cfg_to_dag_prog.block_3, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
proof -
  show ?thesis
      apply (rule block_local_rel_generic)
             apply (rule Rel_Main_test[of bigblock_else1])
            apply (simp add: bigblock_else1_def consecutive_ifs_before_cfg_to_dag_prog.block_3_def)
           apply (simp add: consecutive_ifs_before_cfg_to_dag_prog.block_3_def)
          apply simp
         apply simp
        apply (rule Red_bb0_to)
       apply (rule Red0_impl)
       apply (simp add: consecutive_ifs_before_cfg_to_dag_prog.block_3_def bigblock_else1_def)+
    done
qed 


lemma block_then1_global_rel:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock_then1, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_cfg_to_dag_prog.proc_body ((Inl 4),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and cfg_satisfies_post: "\<And>m' s'.
                             (A,M,\<Lambda>,\<Gamma>,\<Omega>,consecutive_ifs_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 4, Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                             is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns_end) consecutive_ifs_before_ast_cfg.post)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_ast_cfg.post reached_bb reached_cont reached_state)" 
proof -
  show ?thesis
    apply (rule generic_ending_block_global_rel)
         apply (rule Rel_Main_test[of bigblock_then1 _ consecutive_ifs_before_cfg_to_dag_prog.block_4])
             apply (simp add: bigblock_then1_def consecutive_ifs_before_cfg_to_dag_prog.block_4_def)
            apply (simp add: consecutive_ifs_before_cfg_to_dag_prog.block_4_def)
           apply (rule assms(1))
          apply (simp add: bigblock_then1_def)
         apply simp
        apply (rule disjI1)
        apply (rule consecutive_ifs_before_cfg_to_dag_prog.node_4)
       apply (rule consecutive_ifs_before_cfg_to_dag_prog.outEdges_4)
      apply (rule assms(2))
      apply simp+
     apply (rule cfg_satisfies_post, blast)
     apply (simp add: consecutive_ifs_before_cfg_to_dag_prog.node_4)+
    apply (rule bigblock_then1_local_rel)
     apply assumption+
    done
qed

lemma block_else1_global_rel:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock_else1, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_cfg_to_dag_prog.proc_body ((Inl 3),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and cfg_satisfies_post: "\<And>m' s'.
                             (A,M,\<Lambda>,\<Gamma>,\<Omega>,consecutive_ifs_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 3, Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                             is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns_end) consecutive_ifs_before_ast_cfg.post)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_ast_cfg.post reached_bb reached_cont reached_state)" 
proof -
  show ?thesis
    apply (rule generic_ending_block_global_rel)
         apply (rule Rel_Main_test[of bigblock_else1 _ consecutive_ifs_before_cfg_to_dag_prog.block_3])
             apply (simp add: bigblock_else1_def consecutive_ifs_before_cfg_to_dag_prog.block_3_def)
            apply (simp add: consecutive_ifs_before_cfg_to_dag_prog.block_3_def)
        apply (rule assms(1))
          apply (simp add: bigblock_else1_def)
         apply simp
        apply (rule disjI1)
        apply (rule consecutive_ifs_before_cfg_to_dag_prog.node_3)
       apply (rule consecutive_ifs_before_cfg_to_dag_prog.outEdges_3)
      apply (rule assms(2))
      apply simp+
    apply (rule cfg_satisfies_post, blast)
    apply (simp add: consecutive_ifs_before_cfg_to_dag_prog.node_3)+
    apply (rule bigblock_else1_local_rel)
     apply assumption+
    done
qed


lemma block1_global_rel:
  assumes  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_cfg_to_dag_prog.proc_body ((Inl 2),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and cfg_satisfies_post: "\<And>m' s'.
                           (A,M,\<Lambda>,\<Gamma>,\<Omega>,consecutive_ifs_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 2, Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                           is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns_end) consecutive_ifs_before_ast_cfg.post)"
  and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock1, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_ast_cfg.post reached_bb reached_cont reached_state)" 
proof -
  have node2_loc: "node_to_block consecutive_ifs_before_cfg_to_dag_prog.proc_body ! 2 = []" 
    by (simp add: consecutive_ifs_before_cfg_to_dag_prog.block_2_def consecutive_ifs_before_cfg_to_dag_prog.node_2)
  show ?thesis 
    apply (rule block_global_rel_if_successor)
           apply (rule Rel_Invs[of bigblock1])
           apply (simp add: bigblock1_def) 
          apply (rule ast_trace)
          apply (simp add: bigblock1_def)
         apply (rule disjI1)
          apply (rule node2_loc)
        apply (rule assms(1))
        apply simp
       apply (rule cfg_satisfies_post,blast)
       apply simp
       apply simp
      apply simp
    apply (simp add: consecutive_ifs_before_cfg_to_dag_prog.node_2)
    apply (rule disjE)
      apply assumption

     apply (erule allE[where x=4])+
     apply (simp add:consecutive_ifs_before_cfg_to_dag_prog.outEdges_2)+
     apply (simp add:member_rec(1))
     apply (rule block_then1_global_rel)
       apply (simp add: bigblock_then1_def)
      apply simp
    apply (blast)
   
    apply (erule allE[where x=3])+
    apply (simp add:consecutive_ifs_before_cfg_to_dag_prog.outEdges_2)+
    apply (simp add:member_rec(1))
    apply (rule block_else1_global_rel)
      apply (simp add: bigblock_else1_def)
     apply simp+
    apply blast
    done
qed

lemma block_then0_global_rel:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock_then0, KSeq bigblock1 KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_cfg_to_dag_prog.proc_body ((Inl 5),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and cfg_satisfies_post: "\<And>m' s'.
                           (A,M,\<Lambda>,\<Gamma>,\<Omega>,consecutive_ifs_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 5, Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                           is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns_end) consecutive_ifs_before_ast_cfg.post)"
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 0) Gt (Lit (LInt 0))), ns1\<rangle> \<Down> LitV (LBool True)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_ast_cfg.post reached_bb reached_cont reached_state)" 
proof -
  have node5_loc: "node_to_block consecutive_ifs_before_cfg_to_dag_prog.proc_body ! 5 = [(Assume (BinOp (Var 0) Gt (Lit (LInt 0)))),(Assign 0 (Lit (LInt 5)))]" 
    by (simp add: consecutive_ifs_before_cfg_to_dag_prog.block_5_def consecutive_ifs_before_cfg_to_dag_prog.node_5)
  show ?thesis 
    apply (rule block_global_rel_generic)
           apply (rule Rel_Main_test[of bigblock_then0])
             apply (simp add: bigblock_then0_def)
            apply simp
          apply (rule assms(1))
         apply (simp add: bigblock_then0_def)
        apply (rule disjI2)
        apply (rule disjI1)
        apply (rule conjI)
         apply (rule node5_loc)
        apply (rule conjI)
         apply simp
        apply (rule trace_is_possible)
       apply (rule assms(2))
        apply simp+
       apply (rule cfg_satisfies_post, blast)
       apply (simp add: consecutive_ifs_before_cfg_to_dag_prog.node_5)+
     apply (rule bigblock_then0_local_rel)
       apply assumption
      apply simp
     apply (rule trace_is_possible)
    apply (erule allE[where x=2])+
    apply (simp add: consecutive_ifs_before_cfg_to_dag_prog.outEdges_5)+
     apply (simp add: member_rec(1))
    apply (rule block1_global_rel)
      apply auto[1]
     apply blast
    apply simp
    done
qed

lemma block_else0_global_rel:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock_else0, KSeq bigblock1 KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_cfg_to_dag_prog.proc_body ((Inl 1),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and cfg_satisfies_post: "\<And>m' s'.
                           (A,M,\<Lambda>,\<Gamma>,\<Omega>,consecutive_ifs_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 1, Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                           is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns_end) consecutive_ifs_before_ast_cfg.post)"
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 0) Gt (Lit (LInt 0))), ns1\<rangle> \<Down> LitV (LBool False)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_ast_cfg.post reached_bb reached_cont reached_state)" 
proof -
  have node1_loc: "node_to_block consecutive_ifs_before_cfg_to_dag_prog.proc_body ! 1 = [(Assume (BinOp (Lit (LInt 0)) Ge (Var 0)))]" 
    by (simp add: consecutive_ifs_before_cfg_to_dag_prog.block_1_def consecutive_ifs_before_cfg_to_dag_prog.node_1)
  show ?thesis
    apply (rule block_global_rel_generic)
           apply (rule Rel_Invs[of bigblock_else0])
           apply (simp add: bigblock_else0_def)
          apply (rule assms(1))
         apply (simp add: bigblock_else0_def)
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
    apply (erule allE[where x=2])+
    apply (simp add: consecutive_ifs_before_cfg_to_dag_prog.outEdges_1)+
     apply (simp add: member_rec(1))
    apply (rule block1_global_rel)
      apply auto[1]
     apply blast
    apply simp
    done
qed

lemma block0_global_rel:
  assumes  "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bigblock0, KSeq bigblock1 KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_satisfies_post: "\<And>m' s'.
                           (A,M,\<Lambda>,\<Gamma>,\<Omega>,consecutive_ifs_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 0, Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                           is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns_end) consecutive_ifs_before_ast_cfg.post)"
  shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> consecutive_ifs_before_ast_cfg.post reached_bb reached_cont reached_state)" 
proof -
  have node0_loc: "node_to_block consecutive_ifs_before_cfg_to_dag_prog.proc_body ! 0 = [(Havoc 0)]" 
    by (simp add: consecutive_ifs_before_cfg_to_dag_prog.block_0_def consecutive_ifs_before_cfg_to_dag_prog.node_0)
  show ?thesis 
    apply (rule block_global_rel_if_successor)
           apply (rule Rel_Main_test[of bigblock0])
             apply (simp add: bigblock0_def)
            apply (simp add: consecutive_ifs_before_cfg_to_dag_prog.block_0_def)
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
     apply (simp add: consecutive_ifs_before_cfg_to_dag_prog.node_0)
     apply (rule bigblock0_local_rel)
      apply (simp add: bigblock0_def)
     apply simp
    apply (rule disjE)
      apply assumption

     apply (erule allE[where x=5])
     apply (erule allE[where x=5])
     apply (simp add:consecutive_ifs_before_cfg_to_dag_prog.outEdges_0)+
     apply (simp add:member_rec(1))
     apply (rule block_then0_global_rel)
       apply (simp add: bigblock_then0_def)
      apply blast+
   
    apply (erule allE[where x=1])
    apply (erule allE[where x=1])
    apply (simp add:consecutive_ifs_before_cfg_to_dag_prog.outEdges_0)+
    apply (simp add:member_rec(1))
    apply (rule block_else0_global_rel)
      apply (simp add: bigblock_else0_def)
     apply blast+
    done
qed

end