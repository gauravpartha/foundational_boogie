theory nested_loop3_passive_prog
imports Boogie_Lang.Semantics Boogie_Lang.Util nested_loop3_before_ast_to_cfg_prog
begin
definition block_0
  where
    "block_0  = []"
definition block_1
  where
    "block_1  = [(Assume (BinOp (Lit (LInt 0)) Ge (Var 4)))]"
definition block_2
  where
    "block_2  = [(Assume (BinOp (Var 10) Gt (Lit (LInt 0)))),(Assume (BinOp (Var 11) Eq (BinOp (Var 9) Sub (Lit (LInt 1))))),(Assume (BinOp (Var 12) Eq (BinOp (Var 10) Sub (Lit (LInt 1))))),(Assert (BinOp (Var 12) Ge (Lit (LInt 0)))),(Assume (Lit (LBool False)))]"
definition block_3
  where
    "block_3  = [(Assume (BinOp (Var 13) Eq (BinOp (Var 6) Sub (Lit (LInt 1))))),(Assert (BinOp (Var 13) Ge (Lit (LInt 0)))),(Assume (Lit (LBool False)))]"
definition block_4
  where
    "block_4  = [(Assume (BinOp (Lit (LInt 0)) Ge (Var 10)))]"
definition block_5
  where
    "block_5  = [(Assume (BinOp (Var 10) Ge (Lit (LInt 0))))]"
definition block_6
  where
    "block_6  = [(Assume (BinOp (Var 6) Gt (Lit (LInt 0)))),(Assert (BinOp (Var 8) Ge (Lit (LInt 0))))]"
definition block_7
  where
    "block_7  = [(Assume (Lit (LBool False)))]"
definition block_8
  where
    "block_8  = [(Assume (BinOp (Lit (LInt 0)) Ge (Var 6)))]"
definition block_9
  where
    "block_9  = [(Assume (BinOp (Var 6) Ge (Lit (LInt 0))))]"
definition block_10
  where
    "block_10  = [(Assume (BinOp (Var 4) Gt (Lit (LInt 0)))),(Assert (BinOp (Var 3) Ge (Lit (LInt 0))))]"
definition block_11
  where
    "block_11  = []"
definition block_12
  where
    "block_12  = []"
definition block_13
  where
    "block_13  = []"
definition block_14
  where
    "block_14  = []"
definition outEdges
  where
    "outEdges  = [[],[0],[0],[0],[3],[4,2],[5],[0],[7],[8,6],[9],[1,10],[11],[12],[13]]"
definition node_to_blocks
  where
    "node_to_blocks  = [block_0,block_1,block_2,block_3,block_4,block_5,block_6,block_7,block_8,block_9,block_10,block_11,block_12,block_13,block_14]"
definition proc_body
  where
    "proc_body  = (|entry = 14,out_edges = outEdges,node_to_block = node_to_blocks|)"
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

lemma node_10:
shows "((nth (node_to_block proc_body) 10) = block_10)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_11:
shows "((nth (node_to_block proc_body) 11) = block_11)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_12:
shows "((nth (node_to_block proc_body) 12) = block_12)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_13:
shows "((nth (node_to_block proc_body) 13) = block_13)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_14:
shows "((nth (node_to_block proc_body) 14) = block_14)"
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
shows "((nth (out_edges proc_body) 4) = [3])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_5:
shows "((nth (out_edges proc_body) 5) = [4,2])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_6:
shows "((nth (out_edges proc_body) 6) = [5])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_7:
shows "((nth (out_edges proc_body) 7) = [0])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_8:
shows "((nth (out_edges proc_body) 8) = [7])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_9:
shows "((nth (out_edges proc_body) 9) = [8,6])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_10:
shows "((nth (out_edges proc_body) 10) = [9])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_11:
shows "((nth (out_edges proc_body) 11) = [1,10])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_12:
shows "((nth (out_edges proc_body) 12) = [11])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_13:
shows "((nth (out_edges proc_body) 13) = [12])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_14:
shows "((nth (out_edges proc_body) 14) = [13])"
by (simp add:proc_body_def outEdges_def)

definition params_vdecls :: "(vdecls)"
  where
    "params_vdecls  = []"
definition locals_vdecls :: "(vdecls)"
  where
    "locals_vdecls  = [(0,(TPrim TInt),(None )),(1,(TPrim TInt),(None )),(2,(TPrim TInt),(None )),(3,(TPrim TInt),(None )),(4,(TPrim TInt),(None )),(5,(TPrim TInt),(None )),(6,(TPrim TInt),(None )),(7,(TPrim TInt),(None )),(8,(TPrim TInt),(None )),(9,(TPrim TInt),(None )),(10,(TPrim TInt),(None )),(11,(TPrim TInt),(None )),(12,(TPrim TInt),(None )),(13,(TPrim TInt),(None ))]"
lemma locals_min_aux:
shows "(((map fst (append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) \<noteq> []) \<longrightarrow> ((Min (set (map fst (append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)))) \<ge> 0))"
unfolding nested_loop3_passive_prog.params_vdecls_def nested_loop3_passive_prog.locals_vdecls_def
by simp

lemma locals_min:
shows "(\<forall> x. ((Set.member x (set (map fst (append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)))) \<longrightarrow> (x \<ge> 0)))"
using locals_min_aux helper_min
by blast

lemma globals_locals_disj:
shows "((Set.inter (set (map fst (append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls))) (set (map fst (append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)))) = {})"
unfolding nested_loop3_before_ast_to_cfg_prog.constants_vdecls_def nested_loop3_before_ast_to_cfg_prog.globals_vdecls_def
by simp

lemma m_x:
shows "((map_of (append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls) 0) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_y:
shows "((map_of (append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls) 1) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_z:
shows "((map_of (append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls) 2) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_x_0:
shows "((map_of (append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls) 3) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_z_0:
shows "((map_of (append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls) 4) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_y_0:
shows "((map_of (append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls) 5) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_x_1:
shows "((map_of (append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls) 6) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_z_1:
shows "((map_of (append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls) 7) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_y_1:
shows "((map_of (append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls) 8) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_z_2:
shows "((map_of (append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls) 9) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_y_2:
shows "((map_of (append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls) 10) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_z_3:
shows "((map_of (append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls) 11) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_y_3:
shows "((map_of (append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls) 12) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_x_2:
shows "((map_of (append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls) 13) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma l_x:
shows "((lookup_var_decl ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 0) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 0) = (Some (TPrim TInt)))"
using globals_locals_disj m_x
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_y:
shows "((lookup_var_decl ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 1) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 1) = (Some (TPrim TInt)))"
using globals_locals_disj m_y
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_z:
shows "((lookup_var_decl ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 2) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 2) = (Some (TPrim TInt)))"
using globals_locals_disj m_z
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_x_0:
shows "((lookup_var_decl ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 3) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 3) = (Some (TPrim TInt)))"
using globals_locals_disj m_x_0
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_z_0:
shows "((lookup_var_decl ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 4) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 4) = (Some (TPrim TInt)))"
using globals_locals_disj m_z_0
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_y_0:
shows "((lookup_var_decl ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 5) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 5) = (Some (TPrim TInt)))"
using globals_locals_disj m_y_0
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_x_1:
shows "((lookup_var_decl ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 6) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 6) = (Some (TPrim TInt)))"
using globals_locals_disj m_x_1
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_z_1:
shows "((lookup_var_decl ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 7) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 7) = (Some (TPrim TInt)))"
using globals_locals_disj m_z_1
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_y_1:
shows "((lookup_var_decl ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 8) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 8) = (Some (TPrim TInt)))"
using globals_locals_disj m_y_1
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_z_2:
shows "((lookup_var_decl ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 9) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 9) = (Some (TPrim TInt)))"
using globals_locals_disj m_z_2
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_y_2:
shows "((lookup_var_decl ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 10) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 10) = (Some (TPrim TInt)))"
using globals_locals_disj m_y_2
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_z_3:
shows "((lookup_var_decl ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 11) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 11) = (Some (TPrim TInt)))"
using globals_locals_disj m_z_3
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_y_3:
shows "((lookup_var_decl ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 12) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 12) = (Some (TPrim TInt)))"
using globals_locals_disj m_y_3
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_x_2:
shows "((lookup_var_decl ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 13) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls),(append nested_loop3_passive_prog.params_vdecls nested_loop3_passive_prog.locals_vdecls)) 13) = (Some (TPrim TInt)))"
using globals_locals_disj m_x_2
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)


end
