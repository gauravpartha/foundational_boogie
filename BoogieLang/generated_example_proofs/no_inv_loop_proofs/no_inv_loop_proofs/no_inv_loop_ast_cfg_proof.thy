theory no_inv_loop_ast_cfg_proof
  imports Main 
          Boogie_Lang.Ast
          Boogie_Lang.Semantics
          Boogie_Lang.Ast_Cfg_Transformation
          "../global_data" 
          no_inv_loop_before_cfg_to_dag_prog 
          no_inv_loop_before_ast_cfg
          no_inv_loop_cfgtodag_proof
          "/home/alex/Isabelle_10-Nov-2021/lib/Apply_Trace_Cmd"

begin
declare Nat.One_nat_def[simp del]

abbreviation \<Lambda>1_local
  where
    "\<Lambda>1_local  \<equiv> ((append global_data.constants_vdecls global_data.globals_vdecls),(append no_inv_loop_before_ast_cfg.params_vdecls no_inv_loop_before_ast_cfg.locals_vdecls))"

definition body_bb1 
  where "body_bb1 \<equiv> BigBlock None [(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1))))] None None"

definition loop_only_bigblock0 
  where
    "loop_only_bigblock0 = BigBlock None []
                    (Some (WhileWrapper 
                          (ParsedWhile (Some (BinOp (Var 0) Gt (Lit (LInt 0)))) [] [BigBlock None [(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1))))] None None])))
                     None"

definition unwrapped_bigblock0 
  where
    "unwrapped_bigblock0 = BigBlock None []
                    (Some (ParsedWhile (Some (BinOp (Var 0) Gt (Lit (LInt 0)))) [] [BigBlock None [(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1))))] None None]))
                     None"

definition empty_bb 
  where
    "empty_bb = BigBlock None [] None None"

lemma bb0_local_rel:
  assumes Red_bb: "red_bigblock A M \<Lambda>1_local \<Gamma> \<Omega> T (bigblock0, cont0, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda>1_local \<Gamma> \<Omega> no_inv_loop_before_cfg_to_dag_prog.block_0 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" 
  shows "reached_state \<noteq> Failure  \<and>
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>no_inv_loop_before_cfg_to_dag_prog.block_0, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
proof -
  show ?thesis 
    apply (rule block_local_rel_generic)
           apply (rule Rel_Main_test[of bigblock0 _ no_inv_loop_before_cfg_to_dag_prog.block_0])
           apply (simp add: bigblock0_def no_inv_loop_before_cfg_to_dag_prog.block_0_def)
          apply simp+
        apply (rule Red_bb)
       apply (rule Red_impl, simp)
      apply (simp add: bigblock0_def)
     apply simp
    apply (simp add: no_inv_loop_before_cfg_to_dag_prog.block_0_def)
    done
qed

lemma loop_body_bb_local_rel:
  assumes Red_bb: "red_bigblock A M \<Lambda>1_local \<Gamma> \<Omega> T (body_bb1, cont0, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda>1_local \<Gamma> \<Omega> no_inv_loop_before_cfg_to_dag_prog.block_2 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" 
  and trace_is_possible: "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>Var 0 \<guillemotleft>Gt\<guillemotright> Lit (LInt 0),ns1\<rangle> \<Down> BoolV True"
  shows "reached_state \<noteq> Failure  \<and>
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>no_inv_loop_before_cfg_to_dag_prog.block_2, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
proof -
  show ?thesis 
    unfolding no_inv_loop_before_cfg_to_dag_prog.block_2_def 
    apply (rule guard_holds_push_through_assumption)
      apply (rule block_local_rel_generic)
             apply (rule Rel_Main_test[of body_bb1])
             apply (simp add: body_bb1_def)
            apply simp
           apply simp
          apply (rule Red_bb)
         apply (rule push_through_assumption_test1, rule Red_impl)
            apply (simp add: no_inv_loop_before_cfg_to_dag_prog.block_2_def)
           apply (simp add: trace_is_possible body_bb1_def)+
    done
qed

lemma end_global_rel: 
  assumes Red_bb: "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (empty_bb, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> no_inv_loop_before_cfg_to_dag_prog.proc_body ((Inl 3),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and trace_is_possible: "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>(BinOp (Var 0) Gt (Lit (LInt 0))), ns1\<rangle> \<Down> BoolV False"
shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)"
proof -
  have node3_loc: "node_to_block no_inv_loop_before_cfg_to_dag_prog.proc_body ! 3 = [(Assume (BinOp (Lit (LInt 0)) Ge (Var 0)))]" 
    by (simp add: no_inv_loop_before_cfg_to_dag_prog.block_3_def no_inv_loop_before_cfg_to_dag_prog.node_3)
  show ?thesis
    apply (rule generic_ending_block_global_rel)
            apply (rule Rel_Main_test[of empty_bb])
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
         apply (rule neg_gt2)
        apply (rule trace_is_possible)
       apply (rule no_inv_loop_before_cfg_to_dag_prog.outEdges_3)
      apply (rule cfg_is_correct, simp)
     apply simp
    apply (simp add: empty_bb_def)
    apply (simp add: end_static)
    done
qed



lemma second_loop_body_global_rel:
  assumes j_step_ast_trace: "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (body_bb1, (KSeq unwrapped_bigblock0 (KEndBlock KStop)), Normal ns1) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> no_inv_loop_before_cfg_to_dag_prog.proc_body ((Inl 2),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and trace_is_possible: "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>Var 0 \<guillemotleft>Gt\<guillemotright> Lit (LInt 0),ns1\<rangle> \<Down> BoolV True"
  and loop_ih:
        "\<And>k ns1''. k < j \<Longrightarrow>
        (A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile>(unwrapped_bigblock0, (KEndBlock KStop), Normal ns1'') -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state)) \<Longrightarrow>
        (\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> no_inv_loop_before_cfg_to_dag_prog.proc_body ((Inl 1),(Normal ns1'')) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)) \<Longrightarrow>
        (Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)" 
  shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)"
proof -
  have node2_loc: "node_to_block no_inv_loop_before_cfg_to_dag_prog.proc_body ! 2 = [(Assume (BinOp (Var 0) Gt (Lit (LInt 0)))),(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1))))]" 
    by (simp add: no_inv_loop_before_cfg_to_dag_prog.block_2_def no_inv_loop_before_cfg_to_dag_prog.node_2)
  show ?thesis 
    apply (rule block_global_rel_generic)
           apply (rule Rel_Main_test[of body_bb1])
           apply (simp add: body_bb1_def)
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
     apply (simp add: no_inv_loop_before_cfg_to_dag_prog.node_2)
     apply (rule loop_body_bb_local_rel)
       apply assumption
      apply simp
     apply (rule trace_is_possible)
    apply (erule allE[where x=1])
    apply (simp add: no_inv_loop_before_cfg_to_dag_prog.outEdges_2)
    apply (simp add: member_rec(1))
    apply (rule loop_ih)
      apply simp+
    done
qed

lemma second_loop_head_global_rel:
  assumes j_step_ast_trace: "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (unwrapped_bigblock0, (KEndBlock KStop), Normal ns1) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> no_inv_loop_before_cfg_to_dag_prog.proc_body ((Inl 1),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
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
              apply (rule Rel_Invs[of unwrapped_bigblock0 _ _ _ no_inv_loop_before_cfg_to_dag_prog.block_1])
              apply (simp add: unwrapped_bigblock0_def)
             apply (rule less(2))
            apply (rule less(3), simp)
           apply simp
           apply (simp add: unwrapped_bigblock0_def)
          apply simp                 
         apply (rule block_local_rel_loop_head)
              apply (rule Rel_Invs[of unwrapped_bigblock0])
              apply (simp add: unwrapped_bigblock0_def)
           apply (simp add: unwrapped_bigblock0_def)
           apply simp
           apply (simp add: no_inv_loop_before_cfg_to_dag_prog.block_1_def)
          apply simp
         apply simp
        apply (simp add: no_inv_loop_before_cfg_to_dag_prog.block_1_def)
       apply (simp add: no_inv_loop_before_cfg_to_dag_prog.node_1)
       apply (simp add: no_inv_loop_before_cfg_to_dag_prog.block_1_def)
      apply(rule disjE)
        apply assumption

       apply (erule allE[where x = 2])
       apply (simp add:no_inv_loop_before_cfg_to_dag_prog.outEdges_1)
       apply (simp add:member_rec(1))
       apply (rule conjE)
        apply assumption
       apply simp
       apply (rule second_loop_body_global_rel)
          apply (simp add: body_bb1_def)
         apply simp
        apply assumption
       apply (rule less.IH)
         apply (erule strictly_smaller_helper2)
         apply assumption+

      apply (erule allE[where x = 3])
      apply (simp add:no_inv_loop_before_cfg_to_dag_prog.outEdges_1)
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
       apply assumption
      apply (rule end_global_rel)
        apply (simp add: empty_bb_def)+
      done
   qed
 qed

lemma entry_block_global_rel:
  assumes j_step_ast_trace: 
    "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (bigblock0, KStop, Normal ns1) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> no_inv_loop_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> no_inv_loop_before_ast_cfg.post reached_bb reached_cont reached_state)"
  using assms
proof -
  show ?thesis
    unfolding no_inv_loop_before_ast_cfg.post_def
    apply (rule block_global_rel_while_successor)
          apply (rule j_step_ast_trace)
          apply (rule Rel_Main_test[of bigblock0 _ no_inv_loop_before_cfg_to_dag_prog.block_0])
          apply (simp add: bigblock0_def no_inv_loop_before_cfg_to_dag_prog.block_0_def)
         apply (simp add: bigblock0_def no_inv_loop_before_cfg_to_dag_prog.block_0_def)
        apply (simp add: no_inv_loop_before_cfg_to_dag_prog.block_0_def)
       apply (rule disjI1)
       apply (rule no_inv_loop_before_cfg_to_dag_prog.node_0)
       apply (rule cfg_is_correct, simp)
      apply simp
     apply (simp add: no_inv_loop_before_cfg_to_dag_prog.node_0)
     apply (rule bb0_local_rel)
      apply assumption
     apply simp
    apply (rule second_loop_head_global_rel)
     apply (simp add: unwrapped_bigblock0_def)
    apply (simp add: no_inv_loop_before_cfg_to_dag_prog.outEdges_0)
    apply (simp add: member_rec(1))
    done
qed


end