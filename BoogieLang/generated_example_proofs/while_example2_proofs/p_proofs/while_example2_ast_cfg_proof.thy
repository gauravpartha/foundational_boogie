theory while_example2_ast_cfg_proof
  imports Main 
          Boogie_Lang.Ast
          Boogie_Lang.Semantics
          Boogie_Lang.Ast_Cfg_Transformation
          "../global_data" 
          p_before_cfg_to_dag_prog 
          while_example2_before_ast_cfg
          p_cfgtodag_proof
          "/home/alex/Isabelle_10-Nov-2021/lib/Apply_Trace_Cmd"
          p_before_passive_prog 
          p_passification_proof 
          p_vcphase_proof

begin
declare Nat.One_nat_def[simp del]

abbreviation \<Lambda>1_local
  where
    "\<Lambda>1_local  \<equiv> ((append global_data.constants_vdecls global_data.globals_vdecls),(append while_example2_before_ast_cfg.params_vdecls while_example2_before_ast_cfg.locals_vdecls))"

definition body_bb1 
  where "body_bb1 \<equiv> BigBlock None [(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1))))] None None"

definition body_bb2 
  where "body_bb2 \<equiv> BigBlock None [(Assign 0 (BinOp (Var 0) Add (Lit (LInt 1))))] None None"

definition unwrapped_bigblock1 where
  "unwrapped_bigblock1 \<equiv> 
            (BigBlock None [] 
            (Some (ParsedWhile (Some (BinOp (Var 0) Lt (Lit (LInt 0)))) 
                      [(BinOp (Var 0) Le (Lit (LInt 0)))]
                      [BigBlock None [(Assign 0 (BinOp (Var 0) Add (Lit (LInt 1))))] None None]))
             None)"

definition loop_only_bigblock0 where
  "loop_only_bigblock0 \<equiv> 
            (BigBlock None [] 
            (Some (WhileWrapper
                  (ParsedWhile (Some (BinOp (Var 0) Gt (Lit (LInt 0)))) 
                  [(BinOp (Var 0) Ge (Lit (LInt 0)))]
                  [BigBlock None [(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1))))] None None]))) 
             None)"

definition unwrapped_bigblock0 where
  "unwrapped_bigblock0 \<equiv> 
            (BigBlock None [] 
            (Some (ParsedWhile (Some (BinOp (Var 0) Gt (Lit (LInt 0)))) 
                      [(BinOp (Var 0) Ge (Lit (LInt 0)))]
                      [BigBlock None [(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1))))] None None])) 
             None)"

lemma bb0_local_rel:
  assumes Red_bb: "red_bigblock A M \<Lambda>1_local \<Gamma> \<Omega> T (bigblock0, cont0, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.block_0 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" 
  shows "reached_state \<noteq> Failure  \<and>
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>p_before_cfg_to_dag_prog.block_0, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
proof -
  show ?thesis 
    apply (rule block_local_rel_generic)
           apply (rule Rel_Main_test[of bigblock0 _ p_before_cfg_to_dag_prog.block_0])
            apply (simp add: bigblock0_def p_before_cfg_to_dag_prog.block_0_def)
           apply (simp add: p_before_cfg_to_dag_prog.block_0_def)
          apply simp+
        apply (rule Red_bb)
       apply (rule Red_impl, simp)
      apply (simp add: bigblock0_def)
     apply simp
    apply (simp add: p_before_cfg_to_dag_prog.block_0_def)
    done
qed

lemma first_loop_body_bb_local_rel:
  assumes Red_bb: "red_bigblock A M \<Lambda>1_local \<Gamma> \<Omega> T (body_bb1, cont0, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.block_2 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" 
  and trace_is_possible: "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>Var 0 \<guillemotleft>Gt\<guillemotright> Lit (LInt 0),ns1\<rangle> \<Down> BoolV True"
  shows "reached_state \<noteq> Failure  \<and>
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>p_before_cfg_to_dag_prog.block_2, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
proof -
  show ?thesis 
    unfolding p_before_cfg_to_dag_prog.block_2_def 
    apply (rule guard_holds_push_through_assumption)
      apply (rule block_local_rel_generic)
             apply (rule Rel_Main_test[of body_bb1])
             apply (simp add: body_bb1_def)
            apply simp
           apply simp+
          apply (rule Red_bb)
         apply (rule push_through_assumption_test1, rule Red_impl)
            apply (simp add: p_before_cfg_to_dag_prog.block_2_def)
           apply (simp add: trace_is_possible body_bb1_def)+
    done
qed 

lemma second_loop_body_bb_local_rel:
  assumes Red_bb: "red_bigblock A M \<Lambda>1_local \<Gamma> \<Omega> T (body_bb2, cont0, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.block_5 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" 
  and trace_is_possible: "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>Var 0 \<guillemotleft>Lt\<guillemotright> Lit (LInt 0),ns1\<rangle> \<Down> BoolV True"
  shows "reached_state \<noteq> Failure  \<and>
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>p_before_cfg_to_dag_prog.block_5, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
proof -
  show ?thesis 
    unfolding p_before_cfg_to_dag_prog.block_5_def 
    apply (rule guard_holds_push_through_assumption)
      apply (rule block_local_rel_generic)
             apply (rule Rel_Main_test[of body_bb2])
             apply (simp add: body_bb2_def)
            apply simp
           apply simp+
          apply (rule Red_bb)
         apply (rule push_through_assumption_test1, rule Red_impl)
            apply (simp add: p_before_cfg_to_dag_prog.block_5_def)
           apply (simp add: trace_is_possible body_bb2_def)+
    done
qed

lemma bb2_local_rel:
  assumes Red_bb: "red_bigblock A M \<Lambda>1_local \<Gamma> \<Omega> T (bigblock2 , KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.block_6 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" 
  and trace_is_possible: "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 0) Lt (Lit (LInt 0))), ns1\<rangle> \<Down> BoolV False"
  shows "reached_state \<noteq> Failure  \<and>
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>p_before_cfg_to_dag_prog.block_6, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
proof -
  show ?thesis
    apply (simp add: p_before_cfg_to_dag_prog.block_6_def)
    apply (rule guard_fails_push_through_assumption)
      apply (rule block_local_rel_generic)
             apply (rule Rel_Main_test[of bigblock2])
             apply (simp add: bigblock2_def)
            apply simp
           apply simp+
          apply (rule Red_bb)
         apply (rule Red_impl)
         apply (simp add: p_before_cfg_to_dag_prog.block_6_def)
         apply (rule push_through_assumption1)
             apply simp
            apply (rule neg_lt2)
          apply (rule trace_is_possible)
         apply simp
        apply (simp add: bigblock2_def)
        apply simp+
     apply (rule neg_lt2)
    apply (rule trace_is_possible)
    done
qed

lemma bb2_global_rel:
  assumes concrete_trace: "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (bigblock2, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.proc_body ((Inl 6),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and cfg_satisfies_post: "\<And>m' s'.
                             (A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,p_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 6, Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                             is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) while_example2_before_ast_cfg.post)"
  and trace_is_possible: "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 0) Lt (Lit (LInt 0))), ns1\<rangle> \<Down> BoolV False"
  shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> while_example2_before_ast_cfg.post reached_bb reached_cont reached_state)" 
  using assms
proof -
  have node6_loc: "node_to_block p_before_cfg_to_dag_prog.proc_body ! 6 = [(Assume (BinOp (Lit (LInt 0)) Le (Var 0))),(Assert (BinOp (Var 0) Eq (Lit (LInt 0))))]" 
    by (simp add: p_before_cfg_to_dag_prog.block_6_def p_before_cfg_to_dag_prog.node_6)
  show ?thesis
    apply (rule generic_ending_block_global_rel)
         apply (rule Rel_Main_test[of bigblock2])
             apply (simp add: bigblock2_def)
            apply simp
           apply (rule assms(1))
          apply (simp add: bigblock2_def)+
        apply (rule disjI2)
        apply (rule disjI2)
        apply (rule conjI)
         apply (rule node6_loc)
        apply (rule conjI)
         apply simp
        apply (rule conjI)
         apply (rule neg_lt2)
        apply (rule trace_is_possible)
       apply (rule p_before_cfg_to_dag_prog.outEdges_6)
    apply (rule cfg_is_correct)
      apply simp
     apply (rule cfg_satisfies_post)
     apply simp+
    apply (simp add: p_before_cfg_to_dag_prog.node_6)
    apply (rule bb2_local_rel)
      apply assumption+
    apply (rule trace_is_possible)
    done
qed



lemma second_loop_body_global_rel:
  assumes j_step_ast_trace: "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (body_bb2, (KSeq unwrapped_bigblock1 (KEndBlock (KSeq bigblock2 KStop))), Normal ns1) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.proc_body ((Inl 5),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and cfg_satisfies_post: "\<And>m' s'.
                             (A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,p_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 5, Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                             is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end while_example2_before_ast_cfg.post)"
  and trace_is_possible: "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>Var 0 \<guillemotleft>Lt\<guillemotright> Lit (LInt 0),ns1\<rangle> \<Down> BoolV True"
  and loop_ih:
        "\<And>k ns1''. k < j \<Longrightarrow>
        (A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile>(unwrapped_bigblock1, (KEndBlock (KSeq bigblock2 KStop)), Normal ns1'') -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state)) \<Longrightarrow>
        (\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.proc_body ((Inl 4),(Normal ns1'')) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)) \<Longrightarrow>  
        (\<And>m' s'.
                 (A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,p_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 4, Normal ns1'') -n\<rightarrow>* (m', s')) \<Longrightarrow>
                 is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end while_example2_before_ast_cfg.post)) \<Longrightarrow>
        (Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> while_example2_before_ast_cfg.post reached_bb reached_cont reached_state)" 
  shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> while_example2_before_ast_cfg.post reached_bb reached_cont reached_state)"
proof -
  have node5_loc: "node_to_block p_before_cfg_to_dag_prog.proc_body ! 5 = [(Assume (BinOp (Var 0) Lt (Lit (LInt 0)))),(Assign 0 (BinOp (Var 0) Add (Lit (LInt 1))))]" 
    by (simp add: p_before_cfg_to_dag_prog.block_5_def p_before_cfg_to_dag_prog.node_5)
  show ?thesis 
    apply (rule block_global_rel_generic)
           apply (rule Rel_Main_test[of body_bb2])
             apply (simp add: body_bb2_def)
            apply simp
          apply (rule assms(1))
         apply (simp add: body_bb2_def)
        apply (rule disjI2)
        apply (rule disjI1)
        apply (rule conjI)
         apply (rule node5_loc)
        apply (rule conjI)
         apply simp
        apply (rule trace_is_possible)
       apply (rule assms(2))
        apply simp+
       apply (rule assms(3))
        apply simp+
     apply (simp add: p_before_cfg_to_dag_prog.node_5)
     apply (rule second_loop_body_bb_local_rel)
       apply assumption
      apply simp
     apply (rule trace_is_possible)
    apply (erule allE[where x=4])+
    apply (simp add: p_before_cfg_to_dag_prog.outEdges_5)
    apply (simp add: member_rec(1))
    apply (rule loop_ih)
       apply (simp)+
    apply blast
    done
qed

lemma second_loop_head_global_rel:
  assumes j_step_ast_trace: "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (unwrapped_bigblock1, (KEndBlock (KSeq bigblock2 KStop)), Normal ns1) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.proc_body ((Inl 4),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and cfg_sat_post: "\<And>m2 s2.
       A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,p_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 4, Normal ns1) -n\<rightarrow>* (m2, s2) \<Longrightarrow>
       is_final_config (m2, s2) \<Longrightarrow> \<forall>ns_end. s2 = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) while_example2_before_ast_cfg.post"
  shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> while_example2_before_ast_cfg.post reached_bb reached_cont reached_state)"
  using assms
proof (induction j arbitrary: ns1 rule: less_induct)
  case (less j)
  then show ?case 
  proof (cases j)
    case 0
    then show ?thesis
      using Ast.valid_configuration_def less.prems(1) by fastforce
  next
    case (Suc j')
    show ?thesis
      apply (rule block_global_rel_loop_head)
              apply (rule Rel_Invs[of unwrapped_bigblock1 _ _ _ p_before_cfg_to_dag_prog.block_4])
              apply (simp add: unwrapped_bigblock1_def)
             apply (rule less(2))
            apply (rule less(3), simp)
           apply (rule less(4), simp)
           apply simp
           apply (simp add: unwrapped_bigblock1_def)
          apply simp                 
         apply (rule block_local_rel_loop_head)
              apply (rule Rel_Invs[of unwrapped_bigblock1])
              apply (simp add: unwrapped_bigblock1_def)
           apply (simp add: unwrapped_bigblock1_def)
           apply simp
           apply (simp add: p_before_cfg_to_dag_prog.block_4_def)
          apply simp
         apply simp
        apply (simp add: p_before_cfg_to_dag_prog.block_4_def)
       apply (simp add: p_before_cfg_to_dag_prog.node_4)
        apply (simp add: p_before_cfg_to_dag_prog.block_4_def)
       apply simp
      apply(rule disjE)
        apply assumption

       apply (erule allE[where x = 5])+
       apply (simp add:p_before_cfg_to_dag_prog.outEdges_4)+
       apply (simp add:member_rec(1))+
       apply (rule conjE)
        apply assumption
       apply simp
       apply (rule second_loop_body_global_rel)
          apply (simp add: body_bb2_def)
          apply simp
         apply blast
        apply assumption
       apply (rule less.IH)
         apply (erule strictly_smaller_helper2)
          apply assumption
         apply assumption
        apply assumption
       apply assumption
       apply simp

      apply (erule allE[where x = 6])+
      apply (simp add:p_before_cfg_to_dag_prog.outEdges_4)+
      apply (simp add:member_rec(1))+
      apply (rule conjE)
       apply assumption
      apply simp
      apply (rule ending_after_skipping_endblock2)
          apply assumption
          apply simp
         apply simp
         apply blast
        apply blast
       apply simp
      apply (rule bb2_global_rel)
         apply simp+
      apply blast+
      done
   qed
qed
 

lemma first_loop_body_global_rel:
  assumes j_step_ast_trace: 
    "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (body_bb1, (KSeq unwrapped_bigblock0 cont0), Normal ns1) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.proc_body ((Inl 2),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and cfg_satisfies_post: "\<And>m' s'.
                             (A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,p_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 2, Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                             is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end while_example2_before_ast_cfg.post)"
  and trace_is_possible: "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>Var 0 \<guillemotleft>Gt\<guillemotright> Lit (LInt 0), ns1\<rangle> \<Down> BoolV True"
  and loop_ih_assm: "loop_IH j A M \<Lambda>1_local \<Gamma> \<Omega> T unwrapped_bigblock0 cont0 
                                               p_before_cfg_to_dag_prog.proc_body 1 while_example2_before_ast_cfg.post reached_bb reached_cont reached_state"
  shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> while_example2_before_ast_cfg.post reached_bb reached_cont reached_state)"
proof -
  have node2_loc: "node_to_block p_before_cfg_to_dag_prog.proc_body ! 2 = [(Assume (BinOp (Var 0) Gt (Lit (LInt 0)))),(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1))))]" 
    by (simp add: p_before_cfg_to_dag_prog.block_2_def p_before_cfg_to_dag_prog.node_2)
  show ?thesis 
    apply (rule block_global_rel_generic)
           apply (rule Rel_Main_test[of body_bb1])
             apply (simp add: body_bb1_def)
            apply simp
          apply (rule assms(1))
         apply (simp add: body_bb1_def)
        apply (rule disjI2)
        apply (rule disjI1)
         apply (rule conjI)
         apply (rule node2_loc)
        apply (rule conjI)
         apply simp
        apply (rule trace_is_possible)
       apply (rule assms(2))
    apply simp+
       apply (rule cfg_satisfies_post)
        apply blast+
     apply (simp add: p_before_cfg_to_dag_prog.node_2)
     apply (rule first_loop_body_bb_local_rel)
       apply assumption
      apply simp
     apply (rule trace_is_possible)
    apply (erule allE[where x=1])+
    apply (simp add: p_before_cfg_to_dag_prog.outEdges_2)+
    apply (simp add: member_rec(1))
    apply (rule loop_IH_apply)
        apply (rule loop_ih_assm)
       apply simp
      apply simp
     apply simp
    apply simp
    done
qed

lemma first_loop_head_global_rel:
  assumes j_step_ast_trace: 
    "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (unwrapped_bigblock0, (KEndBlock (KSeq bigblock1 (KSeq bigblock2 KStop))), Normal ns1) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.proc_body ((Inl 1),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and cfg_satisfies_post: "\<And>m' s'.
                             (A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,p_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 1, Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                             is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end while_example2_before_ast_cfg.post)"
  shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega>  while_example2_before_ast_cfg.post reached_bb reached_cont reached_state)"
  using assms 
proof (induction j arbitrary: ns1 rule: less_induct)
  case (less j)
  then show ?case 
  proof (cases j)
    case 0
    then show ?thesis
      using valid_configuration_def less.prems(1) by fastforce
  next
    case (Suc j')
    show ?thesis
      apply (rule block_global_rel_loop_head) 
               apply (rule Rel_Invs[of unwrapped_bigblock0 _ _ _ p_before_cfg_to_dag_prog.block_1])
              apply (simp add: unwrapped_bigblock0_def p_before_cfg_to_dag_prog.block_1_def)
             apply (rule less(2))
            apply (rule less(3), simp)
           apply (rule less(4), simp)
           apply simp
            apply (simp add: unwrapped_bigblock0_def)
          apply simp                 
         apply (rule block_local_rel_loop_head)
             apply (rule Rel_Invs[of unwrapped_bigblock0])
            apply (simp add: unwrapped_bigblock0_def)+
          apply (simp add: p_before_cfg_to_dag_prog.block_1_def p_before_cfg_to_dag_prog.node_1)+
      apply(rule disjE)
        apply assumption
    
       apply (erule allE[where x = 2])+
       apply (simp add: p_before_cfg_to_dag_prog.outEdges_1)+
       apply (simp add:member_rec(1))
       apply (rule conjE)
        apply assumption
       apply simp
       apply (rule first_loop_body_global_rel)
          apply (simp add: body_bb1_def)
          apply simp
         apply blast
        apply assumption
       apply (rule loop_IH_prove)
       apply (rule less.IH)
         apply (erule strictly_smaller_helper2)
          apply assumption
         apply assumption
        apply simp
       apply blast

      apply (erule allE[where x = 3])+
      apply (simp add: p_before_cfg_to_dag_prog.outEdges_1)+
      apply (simp add:member_rec(1))
      apply (rule conjE)
       apply assumption
      apply simp
      apply (rule ending_after_skipping_endblock_and_unwrapping)
              apply assumption
             apply (simp add: bigblock1_def bigblock2_def)
            apply simp
            apply assumption
           apply blast
           apply simp
         apply (simp add: p_before_cfg_to_dag_prog.node_3)
         apply (simp add: p_before_cfg_to_dag_prog.block_3_def)
        apply (rule neg_gt2)
       apply (simp add: p_before_cfg_to_dag_prog.outEdges_3)
       apply (simp add: member_rec)
      apply (rule second_loop_head_global_rel)
        apply (simp add: unwrapped_bigblock1_def bigblock2_def)
       apply (rule correctness_propagates_through_assumption)
            apply assumption
           apply (simp add: p_before_cfg_to_dag_prog.node_3)
          apply simp+
      sorry
(*
      apply (rule correctness_propagates_through_assumption3)
            apply simp+
      done
*)
  qed
qed

lemma entry_block_global_rel:
  assumes j_step_ast_trace: 
    "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (bigblock0, (KSeq bigblock1 (KSeq bigblock2 KStop)), Normal ns1) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and cfg_satisfies_post: "\<And>m' s'.
                             (A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,p_before_cfg_to_dag_prog.proc_body \<turnstile>(Inl 0, Normal ns1) -n\<rightarrow>* (m', s')) \<Longrightarrow>
                             is_final_config (m', s') \<Longrightarrow> (\<forall>ns_end. s' = Normal ns_end \<longrightarrow> (expr_all_sat A \<Lambda>1_local \<Gamma> \<Omega> ns_end) while_example2_before_ast_cfg.post)"
  shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> while_example2_before_ast_cfg.post reached_bb reached_cont reached_state)"
  using assms
proof -
  show ?thesis
    apply (rule block_global_rel_while_successor)
          apply (rule j_step_ast_trace)
          apply (rule Rel_Main_test[of bigblock0 _ p_before_cfg_to_dag_prog.block_0])
          apply (simp add: bigblock0_def p_before_cfg_to_dag_prog.block_0_def)
           apply (simp add: bigblock0_def p_before_cfg_to_dag_prog.block_0_def)
          apply (simp add: bigblock0_def p_before_cfg_to_dag_prog.block_0_def)
        apply (simp add: p_before_cfg_to_dag_prog.block_0_def)
       apply (rule disjI1)
       apply (rule p_before_cfg_to_dag_prog.node_0)
       apply (rule cfg_is_correct, simp)
      apply (rule cfg_satisfies_post, blast)
      apply simp
     apply (simp add: p_before_cfg_to_dag_prog.node_0)
     apply (rule bb0_local_rel)
      apply assumption
     apply simp
    apply (rule first_loop_head_global_rel)
      apply (simp add: unwrapped_bigblock0_def)
     apply (simp add: p_before_cfg_to_dag_prog.outEdges_0)
     apply (simp add: member_rec(1))
    apply (erule allE[where x = 1])+
    apply (simp add: p_before_cfg_to_dag_prog.outEdges_0)
    apply (simp add: member_rec(1))
    apply blast
    done
qed

abbreviation \<Lambda>0_local
  where
    "\<Lambda>0_local  \<equiv> ((append global_data.constants_vdecls global_data.globals_vdecls),(append while_example2_before_ast_cfg.params_vdecls while_example2_before_ast_cfg.locals_vdecls))"
lemma end_to_end_theorem_aux2:
assumes 
Red: "rtranclp (red_bigblock A M \<Lambda>0_local \<Gamma> [] while_example2_before_ast_cfg.proc_body) 
               (bigblock0, (KSeq bigblock1 (KSeq bigblock2 KStop)), Normal ns) 
               (end_bb, end_cont, end_state)" and 
VC: "(\<And> (vc_x::int) (vc_x_0::int) (vc_x_1::int) (vc_x_2::int) (vc_x_3::int) (vc_x_4::int). (vc.vc_PreconditionGeneratedEntry vc_x_0 vc_x_1 vc_x_3 vc_x_4 vc_x_2))" and 
Closed: "(\<And> v. (closed ((type_of_val A) v)))" and 
NonEmptyTypes: "(\<And> t. ((closed t) \<Longrightarrow> (\<exists> v. (((type_of_val A) v) = t))))" and 
FInterp: "(fun_interp_wf A global_data.fdecls \<Gamma>)" and 
Axioms: "(axiom_assm A \<Gamma> global_data.constants_vdecls (ns::(('a)nstate)) global_data.axioms)" and 
Precondition: "(expr_all_sat A \<Lambda>0_local \<Gamma> [] ns while_example2_before_ast_cfg.pres)" and 
ParamsLocal: "(state_typ_wf A [] (local_state ns) (snd \<Lambda>0_local))" and 
ConstsGlobal: "(state_typ_wf A [] (global_state ns) (fst \<Lambda>0_local))" and 
OldGlobal: "((global_state ns) = (old_global_state ns))" and 
BinderNs: "((binder_state ns) = Map.empty)"
shows "(Ast.valid_configuration A \<Lambda>0_local \<Gamma> [] while_example2_before_ast_cfg.post end_bb end_cont end_state)"
proof -
  from Red obtain j where 
    Aux:"(A,M,((append global_data.constants_vdecls global_data.globals_vdecls),(append while_example2_before_ast_cfg.params_vdecls while_example2_before_ast_cfg.locals_vdecls)),\<Gamma>,[],while_example2_before_ast_cfg.proc_body \<turnstile> (bigblock0, (KSeq bigblock1 (KSeq bigblock2 KStop)), Normal ns) -n\<longrightarrow>^j (end_bb, end_cont, end_state))"
by (meson rtranclp_imp_relpowp)
  show ?thesis
apply (rule entry_block_global_rel)
      apply (rule Aux)

apply (rule valid_config_implies_not_failure)
apply (rule end_to_end_theorem_aux)
apply (simp add: while_example2_before_ast_cfg.params_vdecls_def while_example2_before_ast_cfg.locals_vdecls_def 
                 p_before_cfg_to_dag_prog.params_vdecls_def  p_before_cfg_to_dag_prog.locals_vdecls_def)
using VC apply simp
using Closed apply simp
using NonEmptyTypes apply simp
apply (rule FInterp)
using Axioms apply simp
using Precondition apply (simp add: while_example2_before_ast_cfg.params_vdecls_def while_example2_before_ast_cfg.locals_vdecls_def 
                                   p_before_cfg_to_dag_prog.params_vdecls_def  p_before_cfg_to_dag_prog.locals_vdecls_def
                                   while_example2_before_ast_cfg.pres_def p_before_cfg_to_dag_prog.pres_def)
using ParamsLocal apply (simp add: while_example2_before_ast_cfg.params_vdecls_def while_example2_before_ast_cfg.locals_vdecls_def 
                                   p_before_cfg_to_dag_prog.params_vdecls_def  p_before_cfg_to_dag_prog.locals_vdecls_def)
using ConstsGlobal apply (simp add: while_example2_before_ast_cfg.params_vdecls_def while_example2_before_ast_cfg.locals_vdecls_def 
                                   p_before_cfg_to_dag_prog.params_vdecls_def  p_before_cfg_to_dag_prog.locals_vdecls_def)
using OldGlobal apply simp
  using BinderNs apply simp

  apply (rule valid_config_implies_satisfied_posts)
apply (rule end_to_end_theorem_aux)
apply (simp add: while_example2_before_ast_cfg.params_vdecls_def while_example2_before_ast_cfg.locals_vdecls_def 
                 p_before_cfg_to_dag_prog.params_vdecls_def  p_before_cfg_to_dag_prog.locals_vdecls_def)
using VC apply simp
using Closed apply simp
using NonEmptyTypes apply simp
apply (rule FInterp)
using Axioms apply simp
using Precondition apply (simp add: while_example2_before_ast_cfg.params_vdecls_def while_example2_before_ast_cfg.locals_vdecls_def 
                                   p_before_cfg_to_dag_prog.params_vdecls_def  p_before_cfg_to_dag_prog.locals_vdecls_def
                                   while_example2_before_ast_cfg.pres_def p_before_cfg_to_dag_prog.pres_def)
using ParamsLocal apply (simp add: while_example2_before_ast_cfg.params_vdecls_def while_example2_before_ast_cfg.locals_vdecls_def 
                                   p_before_cfg_to_dag_prog.params_vdecls_def  p_before_cfg_to_dag_prog.locals_vdecls_def)
using ConstsGlobal apply (simp add: while_example2_before_ast_cfg.params_vdecls_def while_example2_before_ast_cfg.locals_vdecls_def 
                                   p_before_cfg_to_dag_prog.params_vdecls_def  p_before_cfg_to_dag_prog.locals_vdecls_def)
using OldGlobal apply simp
  using BinderNs apply simp+
done
qed

lemma initialization:                              
  assumes "rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T) (init_ast [bigblock0, bigblock1, bigblock2] ns1) (reached_bb, reached_cont, reached_state)"
  shows "rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T) (bigblock0, KSeq bigblock1 (KSeq bigblock2 KStop), Normal ns1) (reached_bb, reached_cont, reached_state)" 
  using assms
  by simp
 

lemma end_to_end_theorem2:
assumes 
VC: "(\<And> (vc_x::int) (vc_x_0::int) (vc_x_1::int) (vc_x_2::int) (vc_x_3::int) (vc_x_4::int). (vc.vc_PreconditionGeneratedEntry vc_x_0 vc_x_1 vc_x_3 vc_x_4 vc_x_2))"
shows "(\<And> A. (Ast.proc_is_correct (A::(('a)absval_ty_fun)) global_data.fdecls global_data.constants_vdecls global_data.globals_vdecls global_data.axioms while_example2_before_ast_cfg.proc_ast))"
apply (rule end_to_end_util2[OF end_to_end_theorem_aux2])
apply (rule initialization)
unfolding while_example2_before_ast_cfg.proc_body_def
apply assumption using VC apply simp  apply assumption+
apply (simp_all add: 
      exprs_to_only_checked_spec_1 exprs_to_only_checked_spec_2
      while_example2_before_ast_cfg.proc_ast_def while_example2_before_ast_cfg.proc_body_def)
done

end