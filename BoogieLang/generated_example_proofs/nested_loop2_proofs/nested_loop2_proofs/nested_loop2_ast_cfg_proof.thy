theory nested_loop2_ast_cfg_proof
  imports Main 
          Boogie_Lang.Ast
          Boogie_Lang.Semantics
          Boogie_Lang.Ast_Cfg_Transformation
          "../global_data" 
          nested_loop2_before_cfg_to_dag_prog 
          nested_loop2_before_ast_cfg
          nested_loop2_cfgtodag_proof
          "/home/alex/Isabelle_10-Nov-2021/lib/Apply_Trace_Cmd"

begin
declare Nat.One_nat_def[simp del]

abbreviation \<Lambda>1_local
  where
    "\<Lambda>1_local  \<equiv> ((append global_data.constants_vdecls global_data.globals_vdecls),(append nested_loop2_before_cfg_to_dag_prog.params_vdecls nested_loop2_before_cfg_to_dag_prog.locals_vdecls))"

definition outer_body_bb1 
  where "outer_body_bb1 \<equiv> 
                     (BigBlock None [] 
                     (Some (WhileWrapper 
                           (ParsedWhile (Some (BinOp (Var 1) Gt (Lit (LInt 0))))
                            [(BinOp (Var 1) Ge (Lit (LInt 0)))] 
                            [BigBlock None [(Assign 1 (BinOp (Var 1) Sub (Lit (LInt 1))))] None None]))) 
                      None)"

definition outer_body_bb2
  where "outer_body_bb2 \<equiv> (BigBlock None [(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1))))] None None)"

definition outer_body_bb1_unwrapped where
  "outer_body_bb1_unwrapped \<equiv> 
                   (BigBlock None [] 
                   (Some (ParsedWhile (Some (BinOp (Var 1) Gt (Lit (LInt 0))))
                          [(BinOp (Var 1) Ge (Lit (LInt 0)))] 
                          [BigBlock None [(Assign 1 (BinOp (Var 1) Sub (Lit (LInt 1))))] None None])) 
                    None)"

definition inner_body_bb1 
  where "inner_body_bb1 \<equiv> (BigBlock None [(Assign 1 (BinOp (Var 1) Sub (Lit (LInt 1))))] None None)"

definition loop_only_bigblock0 where
  "loop_only_bigblock0 \<equiv> 
                      (BigBlock None []
                      (Some (WhileWrapper 
                            (ParsedWhile (Some (BinOp (Var 0) Gt (Lit (LInt 0)))) 
                            [(BinOp (Var 0) Ge (Lit (LInt 0)))]
                            [(BigBlock None [] 
                             (Some (WhileWrapper 
                                   (ParsedWhile (Some (BinOp (Var 1) Gt (Lit (LInt 0))))
                                    [(BinOp (Var 1) Ge (Lit (LInt 0)))] 
                                    [BigBlock None [(Assign 1 (BinOp (Var 1) Sub (Lit (LInt 1))))] None None]))) 
                             None),
                             (BigBlock None [(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1))))] None None)]))) 
                       None)"

definition bb0_unwrapped where
  "bb0_unwrapped \<equiv> (BigBlock None []
                    (Some (ParsedWhile (Some (BinOp (Var 0) Gt (Lit (LInt 0)))) 
                          [(BinOp (Var 0) Ge (Lit (LInt 0)))]
                          [(BigBlock None [] 
                           (Some (WhileWrapper 
                                 (ParsedWhile (Some (BinOp (Var 1) Gt (Lit (LInt 0))))
                                  [(BinOp (Var 1) Ge (Lit (LInt 0)))] 
                                  [BigBlock None [(Assign 1 (BinOp (Var 1) Sub (Lit (LInt 1))))] None None]))) 
                           None),
                           (BigBlock None [(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1))))] None None)])) 
                     None)"

definition empty_bb where
  "empty_bb \<equiv> (BigBlock None [] None None)"

lemma bb0_local_rel:
  assumes Red_bb: "red_bigblock A M \<Lambda>1_local \<Gamma> \<Omega> T (bigblock0, cont0, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda>1_local \<Gamma> \<Omega> nested_loop2_before_cfg_to_dag_prog.block_0 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" 
  shows "reached_state \<noteq> Failure  \<and>
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>nested_loop2_before_cfg_to_dag_prog.block_0, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
proof -
  show ?thesis 
    apply (rule block_local_rel_generic)
           apply (rule Rel_Main_test[of bigblock0 _ nested_loop2_before_cfg_to_dag_prog.block_0])
           apply (simp add: bigblock0_def nested_loop2_before_cfg_to_dag_prog.block_0_def)
          apply (simp add: nested_loop2_before_cfg_to_dag_prog.block_0_def)+
        apply (rule Red_bb)
       apply (rule Red_impl, simp)
      apply (simp add: nested_loop2_before_ast_cfg.bigblock0_def)
     apply simp
    apply (simp add: nested_loop2_before_cfg_to_dag_prog.block_0_def)
    done
qed

lemma inner_body_bb1_local_rel:
  assumes Red_bb: "red_bigblock A M \<Lambda>1_local \<Gamma> \<Omega> T (inner_body_bb1, cont0, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda>1_local \<Gamma> \<Omega> nested_loop2_before_cfg_to_dag_prog.block_6 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" 
  and trace_is_possible: "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 1) Gt (Lit (LInt 0))),ns1\<rangle> \<Down> BoolV True"
  shows "reached_state \<noteq> Failure  \<and>
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>nested_loop2_before_cfg_to_dag_prog.block_6, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
proof -
  show ?thesis 
    unfolding nested_loop2_before_cfg_to_dag_prog.block_6_def
    apply (rule guard_holds_push_through_assumption)
      apply (rule block_local_rel_generic)
             apply (rule Rel_Main_test[of inner_body_bb1])
             apply (simp add: inner_body_bb1_def)
            apply simp
           apply simp+
          apply (rule Red_bb)
         apply (rule push_through_assumption_test1, rule Red_impl)
            apply (simp add: nested_loop2_before_cfg_to_dag_prog.block_6_def)
           apply (simp add: trace_is_possible inner_body_bb1_def)+
    done
qed

lemma outer_body_bb2_local_rel:
  assumes Red_bb: "red_bigblock A M \<Lambda>1_local \<Gamma> \<Omega> T (outer_body_bb2 , KSeq bb0_unwrapped (KEndBlock KStop), (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda>1_local \<Gamma> \<Omega> nested_loop2_before_cfg_to_dag_prog.block_7 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" 
  and trace_is_possible: "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 1) Gt (Lit (LInt 0))), ns1\<rangle> \<Down> BoolV False"
  shows "reached_state \<noteq> Failure  \<and>
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>nested_loop2_before_cfg_to_dag_prog.block_7, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
proof -
  show ?thesis 
    unfolding nested_loop2_before_cfg_to_dag_prog.block_7_def 
    apply (rule guard_fails_push_through_assumption)
      apply (rule block_local_rel_generic)
             apply (rule Rel_Main_test[of outer_body_bb2])
             apply (simp add: outer_body_bb2_def)
            apply simp
           apply simp+
          apply (rule Red_bb)
         apply (rule Red_impl)
         apply (simp add: nested_loop2_before_cfg_to_dag_prog.block_7_def)
         apply (rule push_through_assumption1)
             apply simp
            apply (rule neg_gt2)
          apply (rule trace_is_possible)
         apply simp
        apply (simp add: outer_body_bb2_def)
        apply simp+
     apply (rule neg_gt2)
    apply (rule trace_is_possible)
    done
qed


lemma end_global_rel: 
  assumes Red_bb: "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (empty_bb, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 9),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and trace_is_possible: "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>(Lit (LBool True)), ns1\<rangle> \<Down> BoolV False"
shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)"
proof -
  have node3_loc: "node_to_block nested_loop2_before_cfg_to_dag_prog.proc_body ! 9 = [(Assume (UnOp Not (Lit (LBool True))))]" 
    by (simp add: nested_loop2_before_cfg_to_dag_prog.block_9_def nested_loop2_before_cfg_to_dag_prog.node_9)
  show ?thesis
    apply (rule generic_ending_block_global_rel)
            apply (rule Rel_Invs[of empty_bb])
            apply (simp add: empty_bb_def)
           apply (rule Red_bb)
          apply (simp add: empty_bb_def)
         apply simp
        apply (rule disjI2)
        apply (rule disjI2)
        apply (rule conjI)
         apply (rule node3_loc)
        apply (rule conjI)
         apply simp
        apply (rule conjI)
         defer
        apply (rule trace_is_possible)
       apply (rule nested_loop2_before_cfg_to_dag_prog.outEdges_9)
      apply (rule cfg_is_correct, simp)
     apply simp
    apply (simp add: empty_bb_def)
     apply (simp add: end_static)
    apply simp
    done
qed


lemma outer_body_bb2_global_rel:
  assumes concrete_trace: "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (outer_body_bb2, KSeq bb0_unwrapped (KEndBlock KStop), (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 7),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and trace_is_possible: "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 1) Gt (Lit (LInt 0))), ns1\<rangle> \<Down> BoolV False"
  and loop_ih:
        "\<And>k ns1'. k < j \<Longrightarrow>
        (A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile>(bb0_unwrapped, (KEndBlock KStop), Normal ns1') -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state)) \<Longrightarrow>
        (\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 3),(Normal ns1')) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)) \<Longrightarrow>
        (Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)" 
  shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)" 
  using assms
proof -
  have node5_loc: "node_to_block nested_loop2_before_cfg_to_dag_prog.proc_body ! 7 = [(Assume (BinOp (Lit (LInt 0)) Ge (Var 1))),(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1))))]" 
    by (simp add: nested_loop2_before_cfg_to_dag_prog.block_7_def nested_loop2_before_cfg_to_dag_prog.node_7)
  show ?thesis 
    apply (rule block_global_rel_generic)
           apply (rule Rel_Main_test[of outer_body_bb2])
             apply (simp add: outer_body_bb2_def)
            defer
          apply (rule assms(1))
         apply (simp add: outer_body_bb2_def)
        apply (rule disjI2)
        apply (rule disjI2)
        apply (rule conjI)
         apply (rule node5_loc)
        apply (rule conjI)
         apply simp
        apply (rule conjI)
         apply (rule neg_gt2)
        apply (rule trace_is_possible)
       apply (rule assms(2))
       apply simp+
     apply (simp add: nested_loop2_before_cfg_to_dag_prog.node_7)
     apply (rule outer_body_bb2_local_rel)
       apply assumption
      apply simp
     apply (rule trace_is_possible)
    apply (erule allE[where x=3])
    apply (simp add: nested_loop2_before_cfg_to_dag_prog.outEdges_7)
    apply (simp add: member_rec(1))
    apply (rule loop_ih)
      apply simp+
    done
qed


lemma inner_loop_body_global_rel:
  assumes j_step_ast_trace: 
          "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (inner_body_bb1, (KSeq outer_body_bb1_unwrapped (KEndBlock (KSeq outer_body_bb2 (KSeq bb0_unwrapped (KEndBlock KStop))))), Normal ns1) -n\<longrightarrow>^j 
                                 (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 6),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and trace_is_possible: "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 1) Gt (Lit (LInt 0))),ns1\<rangle> \<Down> BoolV True"
  and loop_ih:
        "\<And>k ns1''. k < j \<Longrightarrow>
        (A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile>(outer_body_bb1_unwrapped, (KEndBlock (KSeq outer_body_bb2 (KSeq bb0_unwrapped (KEndBlock KStop)))), Normal ns1'') -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state)) \<Longrightarrow>
        (\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 5),(Normal ns1'')) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)) \<Longrightarrow>
        (Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)" 
  shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)"
proof -
  have node5_loc: "node_to_block nested_loop2_before_cfg_to_dag_prog.proc_body ! 6 = 
                   [(Assume (BinOp (Var 1) Gt (Lit (LInt 0)))),(Assign 1 (BinOp (Var 1) Sub (Lit (LInt 1))))]" 
    by (simp add: nested_loop2_before_cfg_to_dag_prog.block_6_def nested_loop2_before_cfg_to_dag_prog.node_6)
  show ?thesis 
    apply (rule block_global_rel_generic)
           apply (rule Rel_Main_test[of inner_body_bb1])
             apply (simp add: inner_body_bb1_def)
            defer
          apply (rule assms(1))
         apply (simp add: inner_body_bb1_def)
        apply (rule disjI2)
        apply (rule disjI1)
        apply (rule conjI)
         apply (rule node5_loc)
        apply (rule conjI)
         apply simp
        apply (rule trace_is_possible)
       apply (rule assms(2))
       apply simp+
     apply (simp add: nested_loop2_before_cfg_to_dag_prog.node_6)
     apply (rule inner_body_bb1_local_rel)
       apply assumption
      apply simp
     apply (rule trace_is_possible)

    apply (erule allE[where x=5])
    apply (simp add: nested_loop2_before_cfg_to_dag_prog.outEdges_6)
    apply (simp add: member_rec(1))
    apply (rule loop_ih)
      apply simp+
    done
qed


lemma inner_loop_head_global_rel:
  assumes j_step_ast_trace: "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (outer_body_bb1_unwrapped, (KEndBlock (KSeq outer_body_bb2 (KSeq bb0_unwrapped (KEndBlock KStop)))), Normal ns1) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 5),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and loop_ih:
        "\<And>k ns1'. k < j \<Longrightarrow>
        (A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile>(bb0_unwrapped, KEndBlock KStop, Normal ns1') -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state)) \<Longrightarrow>
        (\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 3),(Normal ns1')) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)) \<Longrightarrow>
        (Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)" 
  shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)"
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
              apply (rule Rel_Invs[of outer_body_bb1_unwrapped _ _ _ nested_loop2_before_cfg_to_dag_prog.block_5])
              apply (simp add: outer_body_bb1_unwrapped_def nested_loop2_before_cfg_to_dag_prog.block_5_def)
             apply (rule less(2))
            apply (rule less(3), simp)
           apply simp
           apply (simp add: outer_body_bb1_unwrapped_def)
          apply simp
         apply (rule block_local_rel_loop_head)
             apply (rule Rel_Invs[of outer_body_bb1_unwrapped])
             apply (simp add: outer_body_bb1_unwrapped_def)
            apply (simp add: outer_body_bb1_unwrapped_def)
           apply (simp)
          apply (rule nested_loop2_before_cfg_to_dag_prog.block_5_def)
         apply (simp, simp)
       apply (simp add: nested_loop2_before_cfg_to_dag_prog.node_5)
      apply(rule disjE)
        apply assumption

       apply (erule allE[where x = 6])
       apply (simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_5)
       apply (simp add:member_rec(1))
       apply (rule conjE)
        apply assumption
       apply simp
       apply (rule inner_loop_body_global_rel) 
          apply (simp add: inner_body_bb1_def)
         apply simp
        apply assumption
       apply (rule less.IH)
         apply (rule strictly_smaller_helper2)
           apply assumption
          apply assumption
         apply assumption
        apply assumption
       apply (rule less.prems(3))
         apply (rule strictly_smaller_helper3)
           apply assumption+

      apply (erule allE[where x = 7])
      apply (simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_5)
      apply (simp add:member_rec(1))
      apply (rule conjE)
       apply assumption
      apply simp
      apply (rule ending_after_skipping_endblock2)
           apply assumption
          apply assumption
         apply simp
         apply blast
        apply simp
       apply assumption
      apply (rule outer_body_bb2_global_rel)
         apply assumption+
      apply (rule less.prems(3))
        apply (rule strictly_smaller_helper4)
          apply assumption+
      done
  qed
qed

lemma inner_loop_head_global_rel_wrapped:
  assumes j_step_ast_trace: "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (outer_body_bb1, (KSeq outer_body_bb2 (KSeq bb0_unwrapped (KEndBlock KStop))), Normal ns1) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 5),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and loop_ih:
        "\<And>k ns1'. k < j \<Longrightarrow>
        (A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile>(bb0_unwrapped, KEndBlock KStop, Normal ns1') -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state)) \<Longrightarrow>
        (\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 3),(Normal ns1')) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)) \<Longrightarrow>
        (Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)" 
  shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)"
  apply (rule ending3)
     apply (rule j_step_ast_trace)
    apply (simp add: outer_body_bb1_def)
    apply (rule cfg_is_correct, simp)
   apply simp
  apply (rule inner_loop_head_global_rel)
    apply (simp add: outer_body_bb1_unwrapped_def)
   apply assumption
  apply (rule loop_ih)
    apply (rule strictly_smaller_helper2)
     apply assumption+
  done

lemma outer_loop_head_global_rel:
  assumes j_step_ast_trace: 
    "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (bb0_unwrapped, KEndBlock KStop, Normal ns1) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 3),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)"
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
              apply (rule Rel_Invs[of bb0_unwrapped])
              apply (simp add: bb0_unwrapped_def)
             apply (rule less(2))
            apply (rule less(3), simp)
           apply simp
           apply (simp add: bb0_unwrapped_def)
          apply simp
         apply (rule block_local_rel_loop_head)
              apply (rule Rel_Invs[of bb0_unwrapped])
              apply (simp add: bb0_unwrapped_def)
            apply (simp add: bb0_unwrapped_def)
           apply (simp, simp, simp)
       apply (simp add: nested_loop2_before_cfg_to_dag_prog.node_3)
       apply (simp add: nested_loop2_before_cfg_to_dag_prog.block_3_def)
      apply(rule disjE)
        apply assumption
    
       apply (erule allE[where x = 4])
       apply (simp add: nested_loop2_before_cfg_to_dag_prog.outEdges_3)
       apply (simp add:member_rec(1))
       apply (rule conjE)
        apply assumption
       apply simp
       apply (rule inner_loop_head_global_rel_wrapped)
         apply (simp add: outer_body_bb1_def outer_body_bb2_def)
        apply (rule correctness_propagates_through_assumption2)
            apply assumption
           apply (simp add: nested_loop2_before_cfg_to_dag_prog.node_4)
           apply (simp add: nested_loop2_before_cfg_to_dag_prog.block_4_def)
          apply assumption
         apply (simp add: nested_loop2_before_cfg_to_dag_prog.outEdges_4)
         apply (simp add: member_rec)
        apply assumption
       apply (rule less.IH)
         apply (rule strictly_smaller_helper2)
          apply assumption+

      apply (erule allE[where x = 8])
      apply (simp add:nested_loop2_before_cfg_to_dag_prog.outEdges_3)
      apply (simp add:member_rec(1))
      apply (rule conjE)
       apply assumption
      apply simp
      apply (rule ending_after_skipping_endblock)
           apply assumption
          apply simp
         apply simp
         apply blast
        apply simp
       apply simp
      apply (rule end_global_rel)
        apply (simp add: empty_bb_def)+
      done
  qed
qed

lemma entry_block_global_rel:
  assumes j_step_ast_trace: "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (bigblock0, KStop, Normal ns1) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> nested_loop2_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> nested_loop2_before_cfg_to_dag_prog.post reached_bb reached_cont reached_state)"
  using assms
proof -
  show ?thesis
    unfolding nested_loop2_before_cfg_to_dag_prog.post_def
    apply (rule block_global_rel_while_successor)
           apply (rule j_step_ast_trace)
          apply (rule Rel_Main_test[of bigblock0 _ nested_loop2_before_cfg_to_dag_prog.block_0])
          apply (simp add: bigblock0_def nested_loop2_before_cfg_to_dag_prog.block_0_def)
         apply (simp add: bigblock0_def nested_loop2_before_cfg_to_dag_prog.block_0_def)
        apply (simp add: nested_loop2_before_cfg_to_dag_prog.block_0_def)
       apply (rule disjI1)
       apply (rule nested_loop2_before_cfg_to_dag_prog.node_0)
       apply (rule cfg_is_correct, simp)
      apply simp
     apply (simp add: nested_loop2_before_cfg_to_dag_prog.node_0)
     apply (rule bb0_local_rel)
      apply assumption
     apply simp
    apply (rule outer_loop_head_global_rel)
     apply (simp add: bb0_unwrapped_def)
    apply (simp add: nested_loop2_before_cfg_to_dag_prog.outEdges_0)
    apply (simp add: member_rec(1))
    done
qed