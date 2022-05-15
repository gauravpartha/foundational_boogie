theory p_passive_prog
imports Boogie_Lang.Semantics Boogie_Lang.Util p_before_passive_prog
begin
definition block_0
  where
    "block_0  = []"
definition block_1
  where
    "block_1  = [(Assume (BinOp (Var 2) Gt (Lit (LInt 0)))),(Assume (BinOp (Var 4) Eq (BinOp (Var 2) Sub (Lit (LInt 1))))),(Assert (BinOp (Var 4) Ge (Lit (LInt 0)))),(Assume (Lit (LBool False)))]"
definition block_2
  where
    "block_2  = [(Assume (BinOp (Lit (LInt 0)) Le (Var 3))),(Assert (BinOp (Var 3) Eq (Lit (LInt 0))))]"
definition block_3
  where
    "block_3  = [(Assume (BinOp (Var 3) Lt (Lit (LInt 0)))),(Assume (BinOp (Var 5) Eq (BinOp (Var 3) Add (Lit (LInt 1))))),(Assert (BinOp (Var 5) Le (Lit (LInt 0)))),(Assume (Lit (LBool False)))]"
definition block_4
  where
    "block_4  = [(Assume (BinOp (Var 3) Le (Lit (LInt 0))))]"
definition block_5
  where
    "block_5  = [(Assume (BinOp (Lit (LInt 0)) Ge (Var 2))),(Assert (BinOp (Var 2) Le (Lit (LInt 0))))]"
definition block_6
  where
    "block_6  = [(Assume (BinOp (Var 2) Ge (Lit (LInt 0))))]"
definition block_7
  where
    "block_7  = [(Assert (BinOp (Var 1) Ge (Lit (LInt 0))))]"
definition block_8
  where
    "block_8  = []"
definition block_9
  where
    "block_9  = []"
definition outEdges
  where
    "outEdges  = [[],[0],[0],[0],[2,3],[4],[5,1],[6],[7],[8]]"
definition node_to_blocks
  where
    "node_to_blocks  = [block_0,block_1,block_2,block_3,block_4,block_5,block_6,block_7,block_8,block_9]"
definition proc_body
  where
    "proc_body  = (|entry = 9,out_edges = outEdges,node_to_block = node_to_blocks|)"
lemma node_0:
shows "((nth (node_to_block proc_body) 0) = block_0)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_1:
shows "((nth (node_to_block proc_body) 1) = block_1)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_2:
shows "((nth (node_to_block proc_body) 2) = block_2)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_3:
shows "((nth (node_to_block proc_body) 3) = block_3)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_4:
shows "((nth (node_to_block proc_body) 4) = block_4)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_5:
shows "((nth (node_to_block proc_body) 5) = block_5)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_6:
shows "((nth (node_to_block proc_body) 6) = block_6)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_7:
shows "((nth (node_to_block proc_body) 7) = block_7)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_8:
shows "((nth (node_to_block proc_body) 8) = block_8)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_9:
shows "((nth (node_to_block proc_body) 9) = block_9)"
by (simp add:proc_body_def node_to_blocks_def)

lemma outEdges_0:
shows "((nth (out_edges proc_body) 0) = [])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_1:
shows "((nth (out_edges proc_body) 1) = [0])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_2:
shows "((nth (out_edges proc_body) 2) = [0])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_3:
shows "((nth (out_edges proc_body) 3) = [0])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_4:
shows "((nth (out_edges proc_body) 4) = [2,3])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_5:
shows "((nth (out_edges proc_body) 5) = [4])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_6:
shows "((nth (out_edges proc_body) 6) = [5,1])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_7:
shows "((nth (out_edges proc_body) 7) = [6])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_8:
shows "((nth (out_edges proc_body) 8) = [7])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_9:
shows "((nth (out_edges proc_body) 9) = [8])"
by (simp add:proc_body_def outEdges_def)

definition params_vdecls :: "(vdecls)"
  where
    "params_vdecls  = []"
definition locals_vdecls :: "(vdecls)"
  where
    "locals_vdecls  = [(0,(TPrim TInt),(None )),(1,(TPrim TInt),(None )),(2,(TPrim TInt),(None )),(4,(TPrim TInt),(None )),(3,(TPrim TInt),(None )),(5,(TPrim TInt),(None ))]"
lemma locals_min_aux:
shows "(((map fst (append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls)) \<noteq> []) \<longrightarrow> ((Min (set (map fst (append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls)))) \<ge> 0))"
unfolding p_passive_prog.params_vdecls_def p_passive_prog.locals_vdecls_def
by simp

lemma locals_min:
shows "(\<forall> x. ((Set.member x (set (map fst (append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls)))) \<longrightarrow> (x \<ge> 0)))"
using locals_min_aux helper_min
by blast

lemma globals_locals_disj:
shows "((Set.inter (set (map fst (append global_data.constants_vdecls global_data.globals_vdecls))) (set (map fst (append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls)))) = {})"
unfolding global_data.constants_vdecls_def global_data.globals_vdecls_def
by simp

lemma m_x:
shows "((map_of (append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls) 0) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_x_0:
shows "((map_of (append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls) 1) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_x_1:
shows "((map_of (append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls) 2) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_x_2:
shows "((map_of (append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls) 4) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_x_3:
shows "((map_of (append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls) 3) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_x_4:
shows "((map_of (append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls) 5) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma l_x:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls)) 0) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls)) 0) = (Some (TPrim TInt)))"
using globals_locals_disj m_x
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_x_0:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls)) 1) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls)) 1) = (Some (TPrim TInt)))"
using globals_locals_disj m_x_0
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_x_1:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls)) 2) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls)) 2) = (Some (TPrim TInt)))"
using globals_locals_disj m_x_1
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_x_2:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls)) 4) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls)) 4) = (Some (TPrim TInt)))"
using globals_locals_disj m_x_2
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_x_3:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls)) 3) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls)) 3) = (Some (TPrim TInt)))"
using globals_locals_disj m_x_3
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_x_4:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls)) 5) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls)) 5) = (Some (TPrim TInt)))"
using globals_locals_disj m_x_4
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)


end
