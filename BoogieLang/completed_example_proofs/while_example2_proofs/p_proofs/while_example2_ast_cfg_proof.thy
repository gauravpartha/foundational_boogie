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


(*
locale ast_to_cfg_lemmas = 
fixes A :: "(('a)absval_ty_fun)" and \<Gamma> :: "(('a)fun_interp)"
assumes 
Wf_Fun: "(fun_interp_wf A global_data.fdecls \<Gamma>)"
*)
begin


abbreviation \<Lambda>1_local
  where
    "\<Lambda>1_local  \<equiv> ((append global_data.constants_vdecls global_data.globals_vdecls),(append p_before_cfg_to_dag_prog.params_vdecls p_before_cfg_to_dag_prog.locals_vdecls))"

abbreviation body_bb1 
  where "body_bb1 \<equiv> BigBlock None [(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1))))] None None"

abbreviation body_bb2 
  where "body_bb2 \<equiv> BigBlock None [(Assign 0 (BinOp (Var 0) Add (Lit (LInt 1))))] None None"

abbreviation unwrapped_bigblock1 where
  "unwrapped_bigblock1 \<equiv> 
            (BigBlock None [] 
            (Some (ParsedWhile (Some (BinOp (Var 0) Lt (Lit (LInt 0)))) 
                      [(BinOp (Var 0) Le (Lit (LInt 0)))]
                      [BigBlock None [(Assign 0 (BinOp (Var 0) Add (Lit (LInt 1))))] None None]))
             None)"

abbreviation loop_only_bigblock0 where
  "loop_only_bigblock0 \<equiv> 
            (BigBlock None [] 
            (Some (WhileWrapper
                  (ParsedWhile (Some (BinOp (Var 0) Gt (Lit (LInt 0)))) 
                  [(BinOp (Var 0) Ge (Lit (LInt 0)))]
                  [BigBlock None [(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1))))] None None]))) 
             None)"

abbreviation unwrapped_bigblock0 where
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
  have syntactic_rel: "ast_cfg_rel None [] bigblock0 p_before_cfg_to_dag_prog.block_0" 
    unfolding p_before_cfg_to_dag_prog.block_0_def by (rule Rel_Main_test) 
  then show ?thesis 
    using assms
    unfolding p_before_cfg_to_dag_prog.block_0_def
    by (auto simp: block_local_rel_generic)
qed

lemma first_loop_body_bb_local_rel:
  assumes Red_bb: "red_bigblock A M \<Lambda>1_local \<Gamma> \<Omega> T (body_bb1, cont0, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.block_2 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" 
  and trace_is_possible: "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>Var 0 \<guillemotleft>Gt\<guillemotright> Lit (LInt 0),ns1\<rangle> \<Down> BoolV True"
  shows "reached_state \<noteq> Failure  \<and>
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>p_before_cfg_to_dag_prog.block_2, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
proof -
  have syntactic_rel: "ast_cfg_rel None [] body_bb1 [(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1))))]" 
    by (rule Rel_Main_test) 

  show ?thesis 
    unfolding p_before_cfg_to_dag_prog.block_2_def
    apply (rule block_local_rel_guard_true)
            apply (rule syntactic_rel)
           apply simp
          apply simp
         apply simp
      apply (rule trace_is_possible)
     apply (rule Red_bb)
    apply (rule Red_impl)
    unfolding p_before_cfg_to_dag_prog.block_2_def
    by simp
qed 

lemma second_loop_body_bb_local_rel:
  assumes Red_bb: "red_bigblock A M \<Lambda>1_local \<Gamma> \<Omega> T (body_bb2, cont0, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.block_5 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" 
  and trace_is_possible: "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>Var 0 \<guillemotleft>Lt\<guillemotright> Lit (LInt 0),ns1\<rangle> \<Down> BoolV True"
  shows "reached_state \<noteq> Failure  \<and>
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>p_before_cfg_to_dag_prog.block_5, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
proof -
  have syntactic_rel: "ast_cfg_rel None [] body_bb2 [(Assign 0 (BinOp (Var 0) Add (Lit (LInt 1))))]" 
    by (rule Rel_Main_test) 

  show ?thesis 
    unfolding p_before_cfg_to_dag_prog.block_5_def
    apply (rule block_local_rel_guard_true)
            apply (rule syntactic_rel)
           apply simp
          apply simp
         apply simp
        apply (rule trace_is_possible)
      apply (rule Red_bb)
      apply (rule Red_impl)
      unfolding p_before_cfg_to_dag_prog.block_5_def
      by simp
qed

lemma bb2_local_rel:
  assumes Red_bb: "red_bigblock A M \<Lambda>1_local \<Gamma> \<Omega> T (bigblock2 , KStop, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.block_6 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" 
  and trace_is_possible: "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp Not (BinOp (Var 0) Lt (Lit (LInt 0))), ns1\<rangle> \<Down> BoolV True"
  shows "reached_state \<noteq> Failure  \<and>
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>p_before_cfg_to_dag_prog.block_6, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
proof -
  have syntactic_rel: "ast_cfg_rel None [] bigblock2 [(Assert (BinOp (Var 0) Eq (Lit (LInt 0))))]" 
    unfolding p_before_cfg_to_dag_prog.block_6_def
    by (rule Rel_Main_test) 
  have guard_equiv: "UnOp Not (BinOp (Var 0) Lt (Lit (LInt 0))) \<sim> (Lit (LInt 0) \<guillemotleft>Le\<guillemotright> Var 0)" 
    by (rule neg_lt2) 

  show ?thesis 
    unfolding p_before_cfg_to_dag_prog.block_6_def
    apply (rule block_local_rel_guard_false)
            apply (rule syntactic_rel)
           apply simp
          apply simp
        apply (rule guard_equiv)
       apply simp
      apply (rule trace_is_possible)
     apply (rule Red_bb)
    apply (rule Red_impl)
    unfolding p_before_cfg_to_dag_prog.block_6_def
    by simp
qed

lemma bb2_global_rel:
  assumes concrete_trace: "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (bigblock2, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.proc_body ((Inl 6),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and trace_is_possible: "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp Not (BinOp (Var 0) Lt (Lit (LInt 0))), ns1\<rangle> \<Down> BoolV True"
  shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)" 
  using assms
proof -
  have syn_rel: "ast_cfg_rel None [] bigblock2 [(Assert (BinOp (Var 0) Eq (Lit (LInt 0))))]" by (simp add: Rel_Main_test)
  have cmds: "node_to_block p_before_cfg_to_dag_prog.proc_body ! 6 = [(Assume (BinOp (Lit (LInt 0)) Le (Var 0))),(Assert (BinOp (Var 0) Eq (Lit (LInt 0))))]" 
    using p_before_cfg_to_dag_prog.block_6_def p_before_cfg_to_dag_prog.node_6 by auto

  show ?thesis
    apply (rule generic_ending_block_after_loop_global_rel)
             apply (rule syn_rel)
            apply simp
           apply simp
          apply simp
         apply (rule cmds)
        apply simp
       apply (rule neg_lt2[of "(Var 0)" "(Lit (LInt 0))"])
        apply(rule trace_is_possible)
       apply (rule concrete_trace)
      apply (rule cfg_is_correct)
    apply simp
    done
qed



lemma second_loop_body_global_rel:
  assumes j_step_ast_trace: "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (body_bb2, (KSeq unwrapped_bigblock1 (KEndBlock (KSeq bigblock2 KStop))), Normal ns1) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.proc_body ((Inl 5),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and trace_is_possible: "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>Var 0 \<guillemotleft>Lt\<guillemotright> Lit (LInt 0),ns1\<rangle> \<Down> BoolV True"
  and loop_ih:
        "\<And>k ns1''. k < j \<Longrightarrow>
        (A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile>(unwrapped_bigblock1, (KEndBlock (KSeq bigblock2 KStop)), Normal ns1'') -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state)) \<Longrightarrow>
        (\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.proc_body ((Inl 4),(Normal ns1'')) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)) \<Longrightarrow>
        (Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)" 
  shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)"
proof -
  have syn_rel: "ast_cfg_rel None [] body_bb2 [(Assign 0 (BinOp (Var 0) Add (Lit (LInt 1))))]" by (simp add: Rel_Main_test)
  have cmds: "node_to_block p_before_cfg_to_dag_prog.proc_body ! 5 = [(Assume (BinOp (Var 0) Lt (Lit (LInt 0)))),(Assign 0 (BinOp (Var 0) Add (Lit (LInt 1))))]" 
    using p_before_cfg_to_dag_prog.block_5_def p_before_cfg_to_dag_prog.node_5 by fastforce
  show ?thesis
    apply (rule block_global_rel_if_true)
               apply (rule syn_rel)
              apply (rule j_step_ast_trace)
             apply simp
            apply simp
           apply (rule cmds)
          apply simp
         apply (rule cfg_is_correct)
         apply simp
        apply simp
       apply simp
      apply (rule trace_is_possible)
     apply (rule block_local_rel_guard_true)
           apply (rule syn_rel)
          apply (simp, simp, simp)
       apply (rule trace_is_possible)
      apply assumption
     apply assumption
    apply (simp add: p_before_cfg_to_dag_prog.outEdges_5)
    apply (simp add: member_rec)
    apply (rule loop_ih)
      apply auto
    done
qed

lemma second_loop_head_global_rel:
  assumes j_step_ast_trace: "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (unwrapped_bigblock1, (KEndBlock (KSeq bigblock2 KStop)), Normal ns1) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.proc_body ((Inl 4),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
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
    have ast_cfg_rel_concrete sorry

    have transfer_all: "(\<forall>m3 s3 n ns. ((A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)) \<Longrightarrow> 
                        (\<And>m3 s3 n ns. ((A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns) -n\<rightarrow>* (m3, s3)) \<Longrightarrow> s3 \<noteq> Failure))" by auto

    have node_4_helper: "node_to_block p_before_cfg_to_dag_prog.proc_body ! 4 = [Assert (Var 0 \<guillemotleft>Le\<guillemotright> Lit (LInt 0))]" 
      by (simp add: p_before_cfg_to_dag_prog.block_4_def p_before_cfg_to_dag_prog.node_4)
    show ?thesis
      apply (rule block_global_rel_loop_head)
             apply (rule Rel_Invs)
            apply (rule less(2))
           apply (rule less(3))
           apply simp
          apply simp                 
         apply (rule block_local_rel_loop_head)
            apply (rule Rel_Invs)
           apply simp
          apply simp
         apply simp
        apply simp
       apply simp
       apply (rule node_4_helper)
      apply(rule disjE)
        apply assumption

       apply (erule allE[where x = 5])
       apply (simp add:p_before_cfg_to_dag_prog.outEdges_4)
       apply (simp add:member_rec(1))
       apply (rule conjE)
        apply assumption
       apply simp
       apply (rule second_loop_body_global_rel)
          apply assumption
         apply simp
        apply assumption
       apply (rule less.IH)
         apply (erule strictly_smaller_helper2)
         apply assumption
         apply assumption
       apply assumption

      apply (erule allE[where x = 6])
      apply (simp add:p_before_cfg_to_dag_prog.outEdges_4)
      apply (simp add:member_rec(1))
      apply (rule conjE)
       apply assumption
      apply simp
      apply (rule ending)
          apply assumption
         apply assumption 
        (* using allE impCE notE HOL.refl subst sym swap arity_type_nat impI notI rev_mp RedVar_case RedBinOp_case arity_type_state arity_type_val *)
        apply blast
        apply assumption
       apply (simp add: bb2_global_rel)
   (* TODO: Here auto works after deferring, otherwise it doesn't, why? 
      Answer: it works without deferring as well but then it changes the other subgoals also. 'subgoal by auto' doesn't work. Why? *)
   (* apply_trace auto *)
      done
  qed
qed

lemma first_loop_body_global_rel:
  assumes j_step_ast_trace: 
    "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (body_bb1, (KSeq unwrapped_bigblock0 (KEndBlock (KSeq bigblock1 (KSeq bigblock2 KStop)))), Normal ns1) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.proc_body ((Inl 2),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and trace_is_possible: "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>Var 0 \<guillemotleft>Gt\<guillemotright> Lit (LInt 0), ns1\<rangle> \<Down> BoolV True"
  and loop_ih:
        "\<And>k ns1''. k < j \<Longrightarrow>
        (A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile>(unwrapped_bigblock0, (KEndBlock (KSeq bigblock1 (KSeq bigblock2 KStop))), Normal ns1'') -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state)) \<Longrightarrow>
        (\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.proc_body ((Inl 1),(Normal ns1'')) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)) \<Longrightarrow>
        (Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)"  shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)"
proof -
  have syn_rel: "ast_cfg_rel None [] body_bb1 [(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1))))]" by (simp add: Rel_Main_test)
  have cmds: "node_to_block p_before_cfg_to_dag_prog.proc_body ! 2 = [(Assume (BinOp (Var 0) Gt (Lit (LInt 0)))),(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1))))]" 
    using p_before_cfg_to_dag_prog.block_2_def p_before_cfg_to_dag_prog.node_2 by fastforce
  show ?thesis
    apply (rule block_global_rel_if_true)
               apply (rule syn_rel)
              apply (rule j_step_ast_trace)
             apply simp
            apply simp
           apply (rule cmds)
          apply simp
         apply (rule cfg_is_correct)
         apply simp
        apply simp
       apply simp
      apply (rule trace_is_possible)
     apply (rule block_local_rel_guard_true)
           apply (rule syn_rel)
          apply (simp, simp, simp)
       apply (rule trace_is_possible)
      apply assumption
     apply assumption
    apply (simp add: p_before_cfg_to_dag_prog.outEdges_2)
    apply (simp add: member_rec)
    apply (rule loop_ih)
      apply auto
    done
qed


lemma correctness_propagates_through_assumption_concrete:
  assumes "\<forall>m s. (A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,p_before_cfg_to_dag_prog.proc_body \<turnstile> (Inl 3, Normal ns1) -n\<rightarrow>* (m, s)) \<longrightarrow> s \<noteq> Failure"
      and "node_to_block p_before_cfg_to_dag_prog.proc_body ! 3 = [Assume c]"
      and "UnOp Not guard \<sim> c"
      and "A,\<Lambda>1_local,\<Gamma>,\<Omega> \<turnstile> \<langle>guard, ns1\<rangle> \<Down> BoolV False"
    shows "\<And>m1 s1. (A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,p_before_cfg_to_dag_prog.proc_body \<turnstile> (Inl 4, Normal ns1) -n\<rightarrow>* (m1, s1)) \<Longrightarrow> s1 \<noteq> Failure"
  using assms
proof -
  have succ: "List.member [4] 4" by (simp add: member_rec(1))
  fix m1 s1
  assume prem: "(A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,p_before_cfg_to_dag_prog.proc_body \<turnstile> (Inl 4, Normal ns1) -n\<rightarrow>* (m1, s1))"
  show "s1 \<noteq> Failure"
  apply (rule correctness_propagates_through_assumption)
       apply (rule assms(1))
      apply (rule assms(2))
     apply (rule assms(3))
    apply (rule assms(4))
     apply (simp add: p_before_cfg_to_dag_prog.outEdges_3)
     apply (rule succ)
    apply (rule prem)
    done
qed

lemma first_loop_head_global_rel:
  assumes j_step_ast_trace: 
    "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (unwrapped_bigblock0, (KEndBlock (KSeq bigblock1 (KSeq bigblock2 KStop))), Normal ns1) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.proc_body ((Inl 1),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
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
    have out_edges_Suc0: "((nth (out_edges p_before_cfg_to_dag_prog.proc_body) (Suc 0)) = [3,2])" using p_before_cfg_to_dag_prog.outEdges_1 by auto
    have node_3_helper: "node_to_block p_before_cfg_to_dag_prog.proc_body ! 3 = [(Assume (BinOp (Lit (LInt 0)) Ge (Var 0)))]" 
      using p_before_cfg_to_dag_prog.block_3_def p_before_cfg_to_dag_prog.node_3 by auto
    have node_1_helper: "node_to_block p_before_cfg_to_dag_prog.proc_body ! (Suc 0) = [Assert (Var 0 \<guillemotleft>Ge\<guillemotright> Lit (LInt 0))]" 
      using p_before_cfg_to_dag_prog.block_1_def p_before_cfg_to_dag_prog.node_1 by auto
    have succ_helper: "List.member [4] 4"by (simp add: member_rec(1))
    show ?thesis
      apply (rule block_global_rel_loop_head) 
             apply (rule Rel_Invs)
            apply (rule less(2))
           apply (rule less(3))
           apply simp
          apply simp                 
         apply (rule block_local_rel_loop_head)
            apply (rule Rel_Invs)
           apply simp
          apply simp
         apply simp
        apply simp
       apply simp
       apply (rule node_1_helper)
      apply(rule disjE)
        apply assumption
    
       apply (erule allE[where x = 2])
       apply (simp add: out_edges_Suc0)
       apply (simp add:member_rec(1))
       apply (rule conjE)
        apply assumption
       apply simp
       apply (rule first_loop_body_global_rel)
          apply assumption
         apply simp
        apply assumption
       apply (rule less.IH)
         apply (erule strictly_smaller_helper2)
         apply assumption
         apply assumption
       apply assumption

      apply (erule allE[where x = 3])
      apply (simp add:out_edges_Suc0)
      apply (simp add:member_rec(1))
      apply (rule conjE)
       apply assumption
      apply simp
      apply (rule ending2)
             apply assumption
            apply assumption
           apply assumption
          apply assumption
         apply (rule node_3_helper)
        apply (rule neg_gt2)
       apply (simp add: p_before_cfg_to_dag_prog.outEdges_3)
       apply (rule succ_helper)
      by (simp add: second_loop_head_global_rel)
  qed
qed

lemma entry_block_global_rel:
  assumes j_step_ast_trace: 
    "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (bigblock0, (KSeq bigblock1 (KSeq bigblock2 KStop)), Normal ns1) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.proc_body ((Inl 0),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> p_before_cfg_to_dag_prog.post reached_bb reached_cont reached_state)"
  using assms
proof -
  have node_0_helper: "node_to_block p_before_cfg_to_dag_prog.proc_body ! 0 = [Havoc 0]" 
    by (simp add: p_before_cfg_to_dag_prog.block_0_def p_before_cfg_to_dag_prog.node_0)
  have "[Havoc 0] = p_before_cfg_to_dag_prog.block_0" by (simp only: p_before_cfg_to_dag_prog.block_0_def) 
  show ?thesis
    unfolding p_before_cfg_to_dag_prog.post_def
    apply (rule block_global_rel_while_successor)
          apply (rule j_step_ast_trace)
         apply (rule Rel_Main_test)
        apply simp
       apply (rule node_0_helper)
      apply (rule cfg_is_correct)
      apply simp
     apply (simp only: \<open>[Havoc 0] = p_before_cfg_to_dag_prog.block_0\<close>)
     apply (rule bb0_local_rel)
      apply (simp only: \<open>[Havoc 0] = p_before_cfg_to_dag_prog.block_0\<close>)
     apply assumption
    apply (simp del: Nat.One_nat_def add: p_before_cfg_to_dag_prog.outEdges_0)
    apply (simp del: Nat.One_nat_def add: member_rec)
    apply (rule first_loop_head_global_rel)
     apply assumption
    (* TODO: Again, why does auto work only in the end here? *)
    by auto
qed

abbreviation \<Lambda>0_local
  where
    "\<Lambda>0_local  \<equiv> ((append global_data.constants_vdecls global_data.globals_vdecls),(append p_before_cfg_to_dag_prog.params_vdecls p_before_cfg_to_dag_prog.locals_vdecls))"
lemma end_to_end_theorem_aux2:
assumes 
Red: "rtranclp (red_bigblock 
      A M ((append global_data.constants_vdecls global_data.globals_vdecls),(append p_before_cfg_to_dag_prog.params_vdecls p_before_cfg_to_dag_prog.locals_vdecls)) \<Gamma> [] 
            while_example2_before_ast_cfg.proc_body) 
      (bigblock0, (KSeq bigblock1 (KSeq bigblock2 KStop)), Normal ns) (end_bb, end_cont, end_state)" and 
VC: "(\<And> (vc_x::int) (vc_x_0::int) (vc_x_1::int) (vc_x_2::int) (vc_x_3::int) (vc_x_4::int). (vc.vc_PreconditionGeneratedEntry vc_x_0 vc_x_1 vc_x_3 vc_x_4 vc_x_2))" and 
Closed: "(\<And> v. (closed ((type_of_val A) v)))" and 
NonEmptyTypes: "(\<And> t. ((closed t) \<Longrightarrow> (\<exists> v. (((type_of_val A) v) = t))))" and 
FInterp: "(fun_interp_wf A global_data.fdecls \<Gamma>)" and 
Axioms: "(axiom_assm A \<Gamma> global_data.constants_vdecls (ns::(('a)nstate)) global_data.axioms)" and 
Precondition: "(expr_all_sat A \<Lambda>0_local \<Gamma> [] ns p_before_cfg_to_dag_prog.pres)" and 
ParamsLocal: "(state_typ_wf A [] (local_state ns) (snd \<Lambda>0_local))" and 
ConstsGlobal: "(state_typ_wf A [] (global_state ns) (fst \<Lambda>0_local))" and 
OldGlobal: "((global_state ns) = (old_global_state ns))" and 
BinderNs: "((binder_state ns) = Map.empty)"
shows "(Ast.valid_configuration A \<Lambda>0_local \<Gamma> [] p_before_cfg_to_dag_prog.post end_bb end_cont end_state)"
proof -
  from Red obtain j where 
    Aux:"(A,M,((append global_data.constants_vdecls global_data.globals_vdecls),(append p_before_cfg_to_dag_prog.params_vdecls p_before_cfg_to_dag_prog.locals_vdecls)),\<Gamma>,[],while_example2_before_ast_cfg.proc_body \<turnstile> (bigblock0, (KSeq bigblock1 (KSeq bigblock2 KStop)), Normal ns) -n\<longrightarrow>^j (end_bb, end_cont, end_state))"
by (meson rtranclp_imp_relpowp)
  show ?thesis
apply (rule entry_block_global_rel)
apply (rule Aux)
apply (rule valid_config_implies_not_failure)
apply (rule end_to_end_theorem_aux)
apply assumption
using VC apply simp
using Closed apply simp
using NonEmptyTypes apply simp
apply (rule FInterp)
using Axioms apply simp
using Precondition apply simp
using ParamsLocal apply simp
using ConstsGlobal apply simp
using OldGlobal apply simp
using BinderNs apply simp
done
qed

lemma initialization:                              
  assumes "rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T) (init_ast [bigblock0, bigblock1, bigblock2] ns1) (reached_bb, reached_cont, reached_state)"
  shows "rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T) (bigblock0, KSeq bigblock1 (KSeq bigblock2 KStop), Normal ns1) (reached_bb, reached_cont, reached_state)" 
proof -
  have "rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T) (bigblock0, convert_list_to_cont (rev [bigblock1, bigblock2]) KStop, Normal ns1) (reached_bb, reached_cont, reached_state)"
    using assms by fastforce
  hence "rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T) (bigblock0, convert_list_to_cont (rev [bigblock1]) (KSeq bigblock2 KStop), Normal ns1) (reached_bb, reached_cont, reached_state)"
    by simp
  thus ?thesis by simp
qed
 

lemma end_to_end_theorem2:
assumes 
VC: "(\<And> (vc_x::int) (vc_x_0::int) (vc_x_1::int) (vc_x_2::int) (vc_x_3::int) (vc_x_4::int). (vc.vc_PreconditionGeneratedEntry vc_x_0 vc_x_1 vc_x_3 vc_x_4 vc_x_2))"
shows "(\<And> A. (Ast.proc_is_correct (A::(('a)absval_ty_fun)) global_data.fdecls global_data.constants_vdecls global_data.globals_vdecls global_data.axioms while_example2_before_ast_cfg.proc_ast))"
apply (rule end_to_end_util2[OF end_to_end_theorem_aux2])
apply (rule initialization)
unfolding while_example2_before_ast_cfg.proc_body_def
apply assumption using VC apply simp  apply assumption+
  unfolding p_before_cfg_to_dag_prog.pres_def p_before_cfg_to_dag_prog.post_def
       apply (simp_all add: 
              exprs_to_only_checked_spec_1 exprs_to_only_checked_spec_2
              while_example2_before_ast_cfg.proc_ast_def while_example2_before_ast_cfg.proc_body_def 
              while_example2_before_ast_cfg.pres_def while_example2_before_ast_cfg.post_def
              p_before_cfg_to_dag_prog.params_vdecls_def p_before_cfg_to_dag_prog.locals_vdecls_def
              while_example2_before_ast_cfg.params_vdecls_def while_example2_before_ast_cfg.locals_vdecls_def)
  done

end