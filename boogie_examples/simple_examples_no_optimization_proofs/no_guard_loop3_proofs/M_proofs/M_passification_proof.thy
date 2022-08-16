theory M_passification_proof
imports Boogie_Lang.Semantics Boogie_Lang.Util M_before_ast_to_cfg_prog M_passive_prog Boogie_Lang.PassificationML M_vcphase_proof Boogie_Lang.PassificationEndToEnd
begin
definition R_old_list :: "(((vname) \<times> ((vname) + (lit)))list)"
  where
    "R_old_list  = []"
definition R_old
  where
    "R_old  = (map_of R_old_list)"
abbreviation \<Lambda>1
  where
    "\<Lambda>1  \<equiv> ((append M_before_ast_to_cfg_prog.constants_vdecls M_before_ast_to_cfg_prog.globals_vdecls),(append M_before_ast_to_cfg_prog.params_vdecls M_before_ast_to_cfg_prog.locals_vdecls))"
abbreviation \<Lambda>2
  where
    "\<Lambda>2  \<equiv> ((append M_before_ast_to_cfg_prog.constants_vdecls M_before_ast_to_cfg_prog.globals_vdecls),(append M_passive_prog.params_vdecls M_passive_prog.locals_vdecls))"
declare One_nat_def[simp del]

lemma block_GeneratedUnifiedExit:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.block_0 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [] R R_old U0 D0 n_s)"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [])) (update_nstate_rel R []) R_old M_passive_prog.block_0 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding M_before_passive_prog.block_0_def M_passive_prog.block_0_def
apply (passive_rel_tac)
apply (unfold type_rel_def, simp, (intro conjI)?)
by simp

lemma block_anon6_LoopDone:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.block_1 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [] R R_old U0 D0 n_s)" and 
"((R 1) = (Some (Inl 6)))"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [])) (update_nstate_rel R []) R_old M_passive_prog.block_1 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding M_before_passive_prog.block_1_def M_passive_prog.block_1_def
apply (passive_rel_tac R_def: assms(3-))
apply (unfold type_rel_def, simp, (intro conjI)?)
by simp

lemma block_anon8_Then:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.block_2 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [12] R R_old U0 D0 n_s)" and 
"((R 2) = (Some (Inl 5)))" and 
"((R 0) = (Some (Inl 11)))"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [12])) (update_nstate_rel R [(1,(Inl 12))]) R_old M_passive_prog.block_2 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding M_before_passive_prog.block_2_def M_passive_prog.block_2_def
apply (passive_rel_tac R_def: assms(3-))
apply (unfold type_rel_def, simp, (intro conjI)?)
apply ((simp add:M_before_ast_to_cfg_prog.l_y(2) M_passive_prog.l_y_3(2)))
by simp

lemma block_anon8_Else:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.block_3 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [] R R_old U0 D0 n_s)" and 
"((R 0) = (Some (Inl 11)))"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [])) (update_nstate_rel R []) R_old M_passive_prog.block_3 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding M_before_passive_prog.block_3_def M_passive_prog.block_3_def
apply (passive_rel_tac R_def: assms(3-))
apply (unfold type_rel_def, simp, (intro conjI)?)
by simp

lemma block_anon7_LoopBody:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.block_4 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [11] R R_old U0 D0 n_s)" and 
"((R 2) = (Some (Inl 5)))" and 
"((R 0) = (Some (Inl 10)))" and 
"((R 1) = (Some (Inl 9)))"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [11])) (update_nstate_rel R [(0,(Inl 11))]) R_old M_passive_prog.block_4 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding M_before_passive_prog.block_4_def M_passive_prog.block_4_def
apply (passive_rel_tac R_def: assms(3-))
apply (unfold type_rel_def, simp, (intro conjI)?)
apply ((simp add:M_before_ast_to_cfg_prog.l_x(2) M_passive_prog.l_x_4(2)))
by simp

lemma block_anon5:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.block_5 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [] R R_old U0 D0 n_s)"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [])) (update_nstate_rel R []) R_old M_passive_prog.block_5 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding M_before_passive_prog.block_5_def M_passive_prog.block_5_def
apply (passive_rel_tac)
apply (unfold type_rel_def, simp, (intro conjI)?)
by simp

lemma block_anon7_LoopDone:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.block_6 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [] R R_old U0 D0 n_s)"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [])) (update_nstate_rel R []) R_old M_passive_prog.block_6 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding M_before_passive_prog.block_6_def M_passive_prog.block_6_def
apply (passive_rel_tac)
apply (unfold type_rel_def, simp, (intro conjI)?)
by simp

lemma block_anon7_LoopHead:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.block_7 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [9,10] R R_old U0 D0 n_s)" and 
"((R 2) = (Some (Inl 5)))"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [9,10])) (update_nstate_rel R [(1,(Inl 9)),(0,(Inl 10))]) R_old M_passive_prog.block_7 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding M_before_passive_prog.block_7_def M_passive_prog.block_7_def
apply (passive_rel_tac R_def: assms(3-))
apply (unfold type_rel_def, simp, (intro conjI)?)
apply ((simp add:M_before_ast_to_cfg_prog.l_y(2) M_passive_prog.l_y_2(2)))
apply ((simp add:M_before_ast_to_cfg_prog.l_x(2) M_passive_prog.l_x_3(2)))
by simp

lemma block_anon6_LoopBody:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.block_8 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [8] R R_old U0 D0 n_s)" and 
"((R 2) = (Some (Inl 5)))" and 
"((R 0) = (Some (Inl 7)))" and 
"((R 1) = (Some (Inl 6)))"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [8])) (update_nstate_rel R [(0,(Inl 8))]) R_old M_passive_prog.block_8 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding M_before_passive_prog.block_8_def M_passive_prog.block_8_def
apply (passive_rel_tac R_def: assms(3-))
apply (unfold type_rel_def, simp, (intro conjI)?)
apply ((simp add:M_before_ast_to_cfg_prog.l_x(2) M_passive_prog.l_x_2(2)))
by simp

lemma block_anon6_LoopHead:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.block_9 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [6,7] R R_old U0 D0 n_s)" and 
"((R 2) = (Some (Inl 5)))"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [6,7])) (update_nstate_rel R [(1,(Inl 6)),(0,(Inl 7))]) R_old M_passive_prog.block_9 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding M_before_passive_prog.block_9_def M_passive_prog.block_9_def
apply (passive_rel_tac R_def: assms(3-))
apply (unfold type_rel_def, simp, (intro conjI)?)
apply ((simp add:M_before_ast_to_cfg_prog.l_y(2) M_passive_prog.l_y_1(2)))
apply ((simp add:M_before_ast_to_cfg_prog.l_x(2) M_passive_prog.l_x_1(2)))
by simp

lemma block_anon0:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.block_10 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [3,4,5] R R_old U0 D0 n_s)"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [3,4,5])) (update_nstate_rel R [(0,(Inl 3)),(1,(Inl 4)),(2,(Inl 5))]) R_old M_passive_prog.block_10 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding M_before_passive_prog.block_10_def M_passive_prog.block_10_def
apply (passive_rel_tac)
apply (unfold type_rel_def, simp, (intro conjI)?)
apply ((simp add:M_before_ast_to_cfg_prog.l_x(2) M_passive_prog.l_x_0(2)))
apply ((simp add:M_before_ast_to_cfg_prog.l_y(2) M_passive_prog.l_y_0(2)))
apply ((simp add:M_before_ast_to_cfg_prog.l_z(2) M_passive_prog.l_z_0(2)))
by simp

lemma block_0:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.block_11 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [] R R_old U0 D0 n_s)"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [])) (update_nstate_rel R []) R_old M_passive_prog.block_11 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding M_before_passive_prog.block_11_def M_passive_prog.block_11_def
apply (passive_rel_tac)
apply (unfold type_rel_def, simp, (intro conjI)?)
by simp

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.block_12 (Normal n_s) s')" and 
"(passive_lemma_assms A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> [] R R_old U0 D0 n_s)"
shows "(passive_block_conclusion A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> U0 (Set.union D0 (set [])) (update_nstate_rel R []) R_old M_passive_prog.block_12 s')"
apply (rule passification_block_lemma_compact[OF assms(1-2)])
unfolding M_before_passive_prog.block_12_def M_passive_prog.block_12_def
apply (passive_rel_tac)
apply (unfold type_rel_def, simp, (intro conjI)?)
by simp

lemma cfg_block_GeneratedUnifiedExit:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.proc_body ((Inl 0),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 1000 R R_old U0 D0 n_s)"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> M_passive_prog.proc_body u (Inl 0)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} [] (@{thm M_before_passive_prog.node_0},@{thm M_before_passive_prog.outEdges_0}) (@{thm M_passive_prog.node_0},@{thm M_passive_prog.outEdges_0}) @{thm block_GeneratedUnifiedExit} [] 1\<close>))

lemma cfg_block_anon6_LoopDone:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.proc_body ((Inl 1),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 1000 R R_old U0 D0 n_s)" and 
"((R 1) = (Some (Inl 6)))"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> M_passive_prog.proc_body u (Inl 1)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} @{thms assms(3-)} (@{thm M_before_passive_prog.node_1},@{thm M_before_passive_prog.outEdges_1}) (@{thm M_passive_prog.node_1},@{thm M_passive_prog.outEdges_1}) @{thm block_anon6_LoopDone} [
@{thm cfg_block_GeneratedUnifiedExit}] 1\<close>))

lemma cfg_block_anon8_Then:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.proc_body ((Inl 2),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 12 R R_old U0 D0 n_s)" and 
"((R 2) = (Some (Inl 5)))" and 
"((R 0) = (Some (Inl 11)))"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> M_passive_prog.proc_body u (Inl 2)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} @{thms assms(3-)} (@{thm M_before_passive_prog.node_2},@{thm M_before_passive_prog.outEdges_2}) (@{thm M_passive_prog.node_2},@{thm M_passive_prog.outEdges_2}) @{thm block_anon8_Then} [
@{thm cfg_block_GeneratedUnifiedExit}] 1\<close>))

lemma cfg_block_anon8_Else:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.proc_body ((Inl 3),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 1000 R R_old U0 D0 n_s)" and 
"((R 0) = (Some (Inl 11)))"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> M_passive_prog.proc_body u (Inl 3)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} @{thms assms(3-)} (@{thm M_before_passive_prog.node_3},@{thm M_before_passive_prog.outEdges_3}) (@{thm M_passive_prog.node_3},@{thm M_passive_prog.outEdges_3}) @{thm block_anon8_Else} [
@{thm cfg_block_GeneratedUnifiedExit}] 1\<close>))

lemma cfg_block_anon7_LoopBody:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.proc_body ((Inl 4),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 11 R R_old U0 D0 n_s)" and 
"((R 2) = (Some (Inl 5)))" and 
"((R 0) = (Some (Inl 10)))" and 
"((R 1) = (Some (Inl 9)))"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> M_passive_prog.proc_body u (Inl 4)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} @{thms assms(3-)} (@{thm M_before_passive_prog.node_4},@{thm M_before_passive_prog.outEdges_4}) (@{thm M_passive_prog.node_4},@{thm M_passive_prog.outEdges_4}) @{thm block_anon7_LoopBody} [
@{thm cfg_block_anon8_Then}, 
@{thm cfg_block_anon8_Else}] 1\<close>))

lemma cfg_block_anon5:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.proc_body ((Inl 5),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 1000 R R_old U0 D0 n_s)"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> M_passive_prog.proc_body u (Inl 5)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} [] (@{thm M_before_passive_prog.node_5},@{thm M_before_passive_prog.outEdges_5}) (@{thm M_passive_prog.node_5},@{thm M_passive_prog.outEdges_5}) @{thm block_anon5} [
@{thm cfg_block_GeneratedUnifiedExit}] 1\<close>))

lemma cfg_block_anon7_LoopDone:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.proc_body ((Inl 6),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 1000 R R_old U0 D0 n_s)"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> M_passive_prog.proc_body u (Inl 6)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} [] (@{thm M_before_passive_prog.node_6},@{thm M_before_passive_prog.outEdges_6}) (@{thm M_passive_prog.node_6},@{thm M_passive_prog.outEdges_6}) @{thm block_anon7_LoopDone} [
@{thm cfg_block_anon5}] 1\<close>))

lemma cfg_block_anon7_LoopHead:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.proc_body ((Inl 7),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 9 R R_old U0 D0 n_s)" and 
"((R 2) = (Some (Inl 5)))"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> M_passive_prog.proc_body u (Inl 7)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} @{thms assms(3-)} (@{thm M_before_passive_prog.node_7},@{thm M_before_passive_prog.outEdges_7}) (@{thm M_passive_prog.node_7},@{thm M_passive_prog.outEdges_7}) @{thm block_anon7_LoopHead} [
@{thm cfg_block_anon7_LoopDone}, 
@{thm cfg_block_anon7_LoopBody}] 1\<close>))

lemma cfg_block_anon6_LoopBody:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.proc_body ((Inl 8),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 8 R R_old U0 D0 n_s)" and 
"((R 2) = (Some (Inl 5)))" and 
"((R 0) = (Some (Inl 7)))" and 
"((R 1) = (Some (Inl 6)))"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> M_passive_prog.proc_body u (Inl 8)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} @{thms assms(3-)} (@{thm M_before_passive_prog.node_8},@{thm M_before_passive_prog.outEdges_8}) (@{thm M_passive_prog.node_8},@{thm M_passive_prog.outEdges_8}) @{thm block_anon6_LoopBody} [
@{thm cfg_block_anon7_LoopHead}] 1\<close>))

lemma cfg_block_anon6_LoopHead:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.proc_body ((Inl 9),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 6 R R_old U0 D0 n_s)" and 
"((R 2) = (Some (Inl 5)))"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> M_passive_prog.proc_body u (Inl 9)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} @{thms assms(3-)} (@{thm M_before_passive_prog.node_9},@{thm M_before_passive_prog.outEdges_9}) (@{thm M_passive_prog.node_9},@{thm M_passive_prog.outEdges_9}) @{thm block_anon6_LoopHead} [
@{thm cfg_block_anon6_LoopDone}, 
@{thm cfg_block_anon6_LoopBody}] 1\<close>))

lemma cfg_block_anon0:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.proc_body ((Inl 10),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 3 R R_old U0 D0 n_s)"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> M_passive_prog.proc_body u (Inl 10)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} [] (@{thm M_before_passive_prog.node_10},@{thm M_before_passive_prog.outEdges_10}) (@{thm M_passive_prog.node_10},@{thm M_passive_prog.outEdges_10}) @{thm block_anon0} [
@{thm cfg_block_anon6_LoopHead}] 1\<close>))

lemma cfg_block_0:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.proc_body ((Inl 11),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 3 R R_old U0 D0 n_s)"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> M_passive_prog.proc_body u (Inl 11)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} [] (@{thm M_before_passive_prog.node_11},@{thm M_before_passive_prog.outEdges_11}) (@{thm M_passive_prog.node_11},@{thm M_passive_prog.outEdges_11}) @{thm block_0} [
@{thm cfg_block_anon0}] 1\<close>))

lemma cfg_block_PreconditionGeneratedEntry:
assumes 
"(red_cfg_multi A M \<Lambda>1 \<Gamma> \<Omega> M_before_passive_prog.proc_body ((Inl 12),(Normal n_s)) (m',s'))" and 
"(passive_lemma_assms_2 A M \<Lambda>1 \<Lambda>2 \<Gamma> \<Omega> 3 R R_old U0 D0 n_s)"
shows "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> \<Omega> M_passive_prog.proc_body u (Inl 12)))))"
by ((tactic \<open> cfg_lemma_tac @{context} @{thm assms(1)} @{thm assms(2)} [] (@{thm M_before_passive_prog.node_12},@{thm M_before_passive_prog.outEdges_12}) (@{thm M_passive_prog.node_12},@{thm M_passive_prog.outEdges_12}) @{thm block_PreconditionGeneratedEntry} [
@{thm cfg_block_0}] 1\<close>))

locale glue_proof = 
fixes A :: "(('a)absval_ty_fun)" and M :: "(mbodyCFG proc_context)" and \<Gamma> :: "(('a)fun_interp)" and m' :: "((node) + (unit))" and ns :: "(('a)nstate)" and s' :: "(('a)state)"
assumes 
Red: "(red_cfg_multi A M ((append M_before_ast_to_cfg_prog.constants_vdecls M_before_ast_to_cfg_prog.globals_vdecls),(append M_before_ast_to_cfg_prog.params_vdecls M_before_ast_to_cfg_prog.locals_vdecls)) \<Gamma> [] M_before_passive_prog.proc_body ((Inl 12),(Normal ns)) (m',s'))" and 
VC: "(\<And> (vc_x::int) (vc_y::int) (vc_z::int) (vc_x_0::int) (vc_y_0::int) (vc_z_0::int) (vc_y_1::int) (vc_x_1::int) (vc_x_2::int) (vc_y_2::int) (vc_x_3::int) (vc_x_4::int) (vc_y_3::int). (vc.vc_anon0 ))" and 
Closed: "(\<And> v. (closed ((type_of_val A) v)))" and 
NonEmptyTypes: "(\<And> t. ((closed t) \<Longrightarrow> (\<exists> v. (((type_of_val A) v) = t))))" and 
FInterp: "(fun_interp_wf A M_before_ast_to_cfg_prog.fdecls \<Gamma>)" and 
Axioms: "(axiom_assm A \<Gamma> M_before_ast_to_cfg_prog.constants_vdecls ns M_before_ast_to_cfg_prog.axioms)" and 
ParamsLocal: "(state_typ_wf A [] (local_state ns) (snd \<Lambda>1))" and 
ConstsGlobal: "(state_typ_wf A [] (global_state ns) (fst \<Lambda>1))" and 
BinderNs: "((binder_state ns) = Map.empty)" and 
OldGlobal: "((global_state ns) = (old_global_state ns))"
begin

definition R_list :: "(((vname) \<times> ((vname) + (lit)))list)"
  where
    "R_list  = []"
definition R_rel
  where
    "R_rel  = (map_of R_list)"
lemma inj_R_rel:
shows "(inj_on_defined R_rel)"
apply (rule injective_fun_to_list_2[OF R_rel_def])
by ((simp add: R_list_def del: distinct.simps))

lemma R_well_formed:
shows "(((R_rel x) = (Some z)) \<longrightarrow> (\<exists> \<tau>. ((z = (Inl x)) \<and> (((lookup_var_ty \<Lambda>1 x) = (Some \<tau>)) \<and> ((lookup_var_ty \<Lambda>2 x) = (Some \<tau>))))))"
apply (rule convert_fun_to_list[OF R_rel_def])
apply ((simp add:R_list_def))
apply ((intro conjI)?)
done

lemma R_wt:
shows "(rel_well_typed A \<Lambda>1 [] R_rel ns)"
apply (rule rel_well_typed_state_typ_wf[OF ParamsLocal ConstsGlobal])
using R_well_formed by auto

abbreviation U0
  where
    "U0  \<equiv> (initial_set A R_rel \<Lambda>1 \<Lambda>2 [] ns)"
lemma U0_ns_rel:
shows "(nstate_rel_states \<Lambda>1 \<Lambda>2 R_rel ns U0)"
unfolding nstate_rel_states_def nstate_rel_def
by ((simp add:BinderNs))

lemma U0_ns_old_rel:
shows "(nstate_old_rel_states \<Lambda>1 \<Lambda>2 R_old ns U0)"
apply (rule nstate_old_rel_states_helper[OF ConstsGlobal OldGlobal])
apply (simp only: fst_conv snd_conv M_before_passive_prog.globals_locals_disj)
apply (rule convert_fun_to_list[OF R_old_def])
unfolding R_old_list_def 
apply simp
apply (rule convert_fun_to_list[OF R_old_def])
unfolding R_old_list_def 
by simp

lemma closed_ty_passive_vars:
assumes 
"((lookup_var_ty \<Lambda>2 x) = (Some \<tau>))"
shows "(closed (instantiate [] \<tau>))"
apply (rule lookup_ty_pred[OF assms(1)])
unfolding M_before_ast_to_cfg_prog.constants_vdecls_def M_before_ast_to_cfg_prog.globals_vdecls_def
apply simp
unfolding M_passive_prog.params_vdecls_def M_passive_prog.locals_vdecls_def
by simp

lemma U0_non_empty:
shows "(U0 \<noteq> {})"
apply (rule init_set_non_empty)
apply (erule NonEmptyTypes)
apply (erule closed_ty_passive_vars)
using R_well_formed apply fastforce
apply (rule R_wt)
apply (rule inj_R_rel)
apply simp
apply (rule ConstsGlobal)
using R_well_formed apply fastforce
using M_before_passive_prog.globals_locals_disj apply auto[1]
using M_passive_prog.globals_locals_disj apply auto[1]
done

lemma max_rel_range:
shows "(\<forall> x. ((Set.member x (rel_range R_rel)) \<longrightarrow> (x \<le> 0)))"
 apply (rule rel_range_fun_to_list)
apply ((simp add:R_rel_def))
by ((simp add:R_list_def))

lemma end_to_end:
shows "(s' \<noteq> Failure)"
proof
assume A1: "(s' = Failure)"
have "((s' = Failure) \<longrightarrow> (\<exists> u. ((Set.member u U0) \<and> (passive_sim_cfg_fail A M \<Lambda>2 \<Gamma> [] M_passive_prog.proc_body u (Inl 12)))))"
apply (rule cfg_block_PreconditionGeneratedEntry[OF Red])
unfolding passive_lemma_assms_2_def
apply (intro conjI)?
apply (rule U0_ns_rel)
apply (rule U0_ns_old_rel)
apply (rule R_wt)
apply (rule init_state_dependent)
using helper_init_disj[OF max_rel_range M_before_ast_to_cfg_prog.globals_max]
apply simp
apply (rule U0_non_empty)
by ((simp_all add:R_rel_def R_list_def))?
with A1 obtain u mp' where uElem: "(Set.member u U0)" and AredPassive:"(red_cfg_multi A M \<Lambda>2 \<Gamma> [] M_passive_prog.proc_body ((Inl 12),(Normal u)) (mp',Failure))"
by (auto simp add: passive_sim_cfg_fail_def)
from M_vcphase_proof.end_to_end[OF AredPassive] have "(Failure \<noteq> Failure)"
 apply rule
using VC apply assumption
apply (rule Closed)
apply (erule NonEmptyTypes)
apply (rule FInterp)
apply (rule axiom_assm_aux[OF Axioms])
using uElem by simp_all
thus False by simp
qed


end


end
