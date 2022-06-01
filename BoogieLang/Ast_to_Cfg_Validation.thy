theory Ast_to_Cfg_Validation
   imports Main
          "Boogie_Lang.Ast"
          "Boogie_Lang.Semantics"
          "Boogie_Lang.BackedgeElim"
          "Boogie_Lang.Ast_Cfg_Transformation"
          "Boogie_Lang.Lang"
begin 

fun local_validation :: "bigblock \<Rightarrow> block \<Rightarrow> expr option \<Rightarrow> expr option \<Rightarrow> 'a absval_ty_fun \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> 'a nstate \<Rightarrow> bool" where
  "local_validation ast_block cfg_block guard_option transformed_guard_option A \<Lambda> \<Gamma> \<Omega> ns = 
     (case guard_option of 
        Some guard \<Rightarrow> 
          (case transformed_guard_option of
              Some transformed_guard \<Rightarrow>        
                    (\<exists> cmd cmds. (cfg_block = cmd#cmds) \<and> 
                    (ast_cfg_rel None [] ast_block cmds) \<and> 
                    ((UnOp Not guard) \<sim> transformed_guard) \<and> 
                    (cmd = Assume transformed_guard))
          |   None \<Rightarrow> 
                    (\<exists> cmd cmds. (cfg_block = cmd#cmds) \<and> 
                    (ast_cfg_rel None [] ast_block cmds) \<and> 
                    (cmd = Assume guard))) 
     |  None \<Rightarrow>        
              (\<exists> cmd cmds. (cfg_block = cmd#cmds) \<and> 
              (ast_cfg_rel None [] ast_block cmds)))"

(*
lemma block_global_rel_if_false:
  assumes block_rel: "ast_cfg_rel None [] bb cs2"
  and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, cont0, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and "bb = (BigBlock name cs1 any_str any_tr)"
  and "cs1 \<noteq> Nil"
  and "cs2 \<noteq> Nil"
  and "node_to_block(G) ! n = cs3"
  and "cs3 = (c#cs2)"
  and cfg_correct: "(\<And> m2 s2. ((red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G (Inl n, Normal ns1) (m2, s2)) \<Longrightarrow> (s2 \<noteq> Failure)))"
  and trivial_bb_successor: "(cont0 = KSeq bb1 cont1) \<and> any_str = None \<and> any_tr = None"
  and "c = Assume some_cmd"
  and "(UnOp Not block_guard) \<sim> some_cmd"
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(UnOp Not block_guard), ns1\<rangle> \<Down> LitV (LBool True)"
  and block_local_rel: 
        "\<And> reached_bb_inter reached_cont_inter reached_state_inter. (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb, cont0, (Normal ns1)) (reached_bb_inter, reached_cont_inter, reached_state_inter)) \<Longrightarrow> 
        (\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cs3 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure))) \<Longrightarrow>   
        (reached_state_inter \<noteq> Failure  \<and> (\<forall>ns1'. reached_state_inter = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs3, Normal ns1\<rangle> [\<rightarrow>] Normal ns1')))"
  and succ_correct: 
       "\<And>  ns1'' k.
        k < j \<Longrightarrow> 
        \<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), Normal ns1'') -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)) \<Longrightarrow>
        A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb1, cont1, (Normal ns1'')) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state) \<Longrightarrow> 
        (Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
     shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
*)

(*
lemma block_global_rel_if_true:
  assumes block_rel: "ast_cfg_rel None [] bb cs2"
  and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, cont0, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and "bb = (BigBlock name cs1 any_str any_tr)"
  and "cs1 \<noteq> Nil"
  and "cs2 \<noteq> Nil"
  and "node_to_block(G) ! n = cs3"
  and "cs3 = c#cs2"
  and cfg_correct: "(\<And> m2 s2. ((red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G (Inl n, Normal ns1) (m2, s2)) \<Longrightarrow> (s2 \<noteq> Failure)))"
  and trivial_bb_successor: "(cont0 = KSeq bb1 cont1) \<and> any_str = None \<and> any_tr = None"
  and "c = Assume block_guard"
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>block_guard, ns1\<rangle> \<Down> LitV (LBool True)"
  and block_local_rel: 
        "\<And> reached_bb_inter reached_cont_inter reached_state_inter. (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb, cont0, (Normal ns1)) (reached_bb_inter, reached_cont_inter, reached_state_inter)) \<Longrightarrow> 
        (\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cs3 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure))) \<Longrightarrow>   
        (reached_state_inter \<noteq> Failure  \<and> (\<forall>ns1'. reached_state_inter = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs3, Normal ns1\<rangle> [\<rightarrow>] Normal ns1')))"
  and succ_correct: 
       "\<And>  ns1'' k.
        k < j \<Longrightarrow> 
        \<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), Normal ns1'') -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)) \<Longrightarrow>
        A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb1, cont1, (Normal ns1'')) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state) \<Longrightarrow> 
        (Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
     shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
*)

(*
lemma block_global_rel_generic:
  assumes block_rel: "ast_cfg_rel None [] bb cs2"
  and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, cont0, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and "bb = (BigBlock name cs1 any_str any_tr)"
  and "cs1 \<noteq> Nil"
  and "cs2 \<noteq> Nil"
  and "node_to_block(G) ! n = cs2"
  and cfg_correct: "(\<And> m2 s2. ((red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G (Inl n, Normal ns1) (m2, s2)) \<Longrightarrow> (s2 \<noteq> Failure)))"
  and trivial_bb_successor: "(cont0 = KSeq bb1 cont1) \<and> any_str = None \<and> any_tr = None"
  and block_local_rel: 
        "\<And> reached_bb_inter reached_cont_inter reached_state_inter. (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb, cont0, (Normal ns1)) (reached_bb_inter, reached_cont_inter, reached_state_inter)) \<Longrightarrow> 
        (\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cs2 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure))) \<Longrightarrow>   
        (reached_state_inter \<noteq> Failure  \<and> (\<forall>ns1'. reached_state_inter = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns1\<rangle> [\<rightarrow>] Normal ns1')))"
  and succ_correct: 
       "\<And>  ns1'' k.
        k < j \<Longrightarrow> 
        \<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), Normal ns1'') -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)) \<Longrightarrow>
        A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb1, cont1, (Normal ns1'')) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state) \<Longrightarrow> 
        (Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
*)

(*
lemma block_global_rel_while_successor:
  assumes j_step_ast_trace: 
      "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, cont1, Normal ns1) -n\<longrightarrow>^j 
                      (reached_bb, reached_cont, reached_state)"
  and syn_rel: "ast_cfg_rel None [] bb cmds"
  and "bb = (BigBlock name cmds (Some (WhileWrapper (ParsedWhile guard invs (body_bb0#body_bbs)))) None)"
  and "cmds \<noteq> []"
  and "node_to_block G ! n = cmds"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G ((Inl n),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and block_local_rel:
    "\<And> reached_bb_inter reached_cont_inter reached_state_inter. 
    (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb, cont1, (Normal ns1)) (reached_bb_inter, reached_cont_inter, reached_state_inter)) \<Longrightarrow> 
    (\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cmds (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure))) \<Longrightarrow>   
    (reached_state_inter \<noteq> Failure  \<and> (\<forall>ns1'. reached_state_inter = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(node_to_block G ! n), Normal ns1\<rangle> [\<rightarrow>] Normal ns1')))"
  and global_rel_succ:
        "\<And> ns2 k.
         k < j \<Longrightarrow>
         (\<forall>msuc2. List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl msuc2, Normal ns2) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)) \<Longrightarrow>
         A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> ((BigBlock name [] (Some (ParsedWhile guard invs (body_bb0#body_bbs))) None), KEndBlock cont1, Normal ns2) -n\<longrightarrow>^k 
                      (reached_bb, reached_cont, reached_state) \<Longrightarrow> 
         (valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
      shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
*)

(*
lemma block_global_rel_loop_head:
  assumes block_rel: "ast_cfg_rel None assertions bb assertions"
  and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, KEndBlock cont1, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_correct: "(\<And> m2 s2. ((red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G (Inl n, Normal ns1) (m2, s2)) \<Longrightarrow> (s2 \<noteq> Failure)))"
  and "bb = (BigBlock name [] any_str any_tr)"
  (* TODO: You're requiring that the loop isn't empty! What if it is? *)
  and bb_successor_while: "any_str = Some (ParsedWhile cont_guard invs (bb0#body_bbs))"
  and block_local_rel:
    "\<And> reached_bb_inter reached_cont_inter reached_state_inter. (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb, KEndBlock cont1, (Normal ns1)) (reached_bb_inter, reached_cont_inter, reached_state_inter)) \<Longrightarrow> 
    (\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> assertions (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure))) \<Longrightarrow>   
    (reached_state_inter \<noteq> Failure  \<and> (\<forall>ns1'. reached_state_inter = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>assertions, Normal ns1\<rangle> [\<rightarrow>] Normal ns1')))"
  and "node_to_block(G) ! n = assertions"
  and succ_correct: 
   "\<And> ns1'' loop_guard j'. 
    j = Suc j' \<Longrightarrow>
    (\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), Normal ns1'') -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure))) \<Longrightarrow>
    ((cont_guard = Some loop_guard) \<and> 
      (red_expr A \<Lambda> \<Gamma> \<Omega> loop_guard ns1'' (BoolV True)) \<and> 
      A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb0, convert_list_to_cont (bb#(rev body_bbs)) (KEndBlock cont1), (Normal ns1'')) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)) \<or> 
    ((cont_guard = Some loop_guard) \<and> 
      (red_expr A \<Lambda> \<Gamma> \<Omega> loop_guard ns1'' (BoolV False)) \<and> 
      A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> ((BigBlock name [] None None), KEndBlock cont1, (Normal ns1'')) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)) \<or>
    ((cont_guard = None) \<and> 
     ((A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> ((BigBlock name [] None None), KEndBlock cont1, (Normal ns1'')) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)) \<or>
      (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb0, convert_list_to_cont (bb#(rev body_bbs)) (KEndBlock cont1), (Normal ns1'')) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state))))  \<Longrightarrow>  
    (Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)" 
*)

(*
lemma block_global_rel_if_successor:
  assumes block_rel: "ast_cfg_rel None [] bb cs2"
  and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, cont0, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and "bb = (BigBlock name cs1 any_str any_tr)"
  and "node_to_block(G) ! n = cs2"
  and cfg_correct: "(\<And> m2 s2. ((red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G (Inl n, Normal ns1) (m2, s2)) \<Longrightarrow> (s2 \<noteq> Failure)))"
  and bb_successor_if: "any_str = Some (ParsedIf cont_guard (then0#then_bbs) (else0#else_bbs))"
  and block_local_rel:
        "\<And> reached_bb_inter reached_cont_inter reached_state_inter. (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name cs1 any_str any_tr), cont0, (Normal ns1)) (reached_bb_inter, reached_cont_inter, reached_state_inter)) \<Longrightarrow> 
        (\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cs2 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure))) \<Longrightarrow> 
        cs1 \<noteq> [] \<Longrightarrow> cs2 \<noteq> [] \<Longrightarrow>  
        (reached_state_inter \<noteq> Failure  \<and> (\<forall>ns1'. reached_state_inter = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns1\<rangle> [\<rightarrow>] Normal ns1')))"
  and succ_correct: 
       "\<And> ns1'' block_guard k.
         k < j \<Longrightarrow> 
        (\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), Normal ns1'') -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure))) \<Longrightarrow>
        ((cont_guard = Some block_guard) \<and> 
          (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1'' (BoolV True)) \<and> 
          A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (then0, convert_list_to_cont (rev then_bbs) cont0, (Normal ns1'')) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state)) \<or> 
        ((cont_guard = Some block_guard) \<and> 
          (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1'' (BoolV False)) \<and> 
          A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (else0, convert_list_to_cont (rev else_bbs) cont0, (Normal ns1'')) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state)) \<or>
        ( (cont_guard = None) \<and> 
          ((A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (then0, convert_list_to_cont (rev then_bbs) cont0, (Normal ns1'')) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state)) \<or>
          (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (else0, convert_list_to_cont (rev else_bbs) cont0, (Normal ns1'')) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state))) ) \<Longrightarrow>  
        (Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)" 
*)

fun global_validation :: "ast_procedure \<Rightarrow> procedure \<Rightarrow> expr option \<Rightarrow> expr option \<Rightarrow> 'a absval_ty_fun \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> 'a nstate \<Rightarrow> bool" where
  "global_validation ast_proc cfg_proc guard_option transformed_guard_option A \<Lambda> \<Gamma> \<Omega> ns = 
    (case proc_body(ast_proc) of
      None \<Rightarrow> 
             (case Lang.proc_body(cfg_proc) of
               None \<Rightarrow> True 
             | Some (locals, mCFG) \<Rightarrow> False)
    | Some (locals, (bb#bbs)) \<Rightarrow>
             (case Lang.proc_body(cfg_proc) of
               None \<Rightarrow> False
             | Some (locals, mCFG) \<Rightarrow> 
                                     (local_validation bb (node_to_block(mCFG) ! (entry(mCFG))) guard_option transformed_guard_option A \<Lambda> \<Gamma> \<Omega> ns) \<and> 
                                      False)
    | Some (locals, []) \<Rightarrow> False )"
            



end