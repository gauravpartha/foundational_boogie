theory triangle_passive_prog
imports Boogie_Lang.Semantics Boogie_Lang.Util triangle_before_passive_prog
begin
definition block_0
  where
    "block_0  = [(Assert (BinOp (Var 7) Eq (BinOp (BinOp (Var 0) Mul (BinOp (Var 0) Sub (Lit (LInt 1)))) Div (Lit (LInt 2)))))]"
definition block_1
  where
    "block_1  = [(Assume (BinOp (Var 0) Le (Var 4))),(Assume (BinOp (Var 7) Eq (Var 3)))]"
definition block_2
  where
    "block_2  = [(Assume (BinOp (Var 4) Lt (Var 0))),(Assume (BinOp (Var 5) Eq (BinOp (Var 3) Add (Var 4)))),(Assume (BinOp (Var 6) Eq (BinOp (Var 4) Add (Lit (LInt 1))))),(Assert (BinOp (Var 5) Eq (BinOp (BinOp (Var 6) Mul (BinOp (Var 6) Sub (Lit (LInt 1)))) Div (Lit (LInt 2))))),(Assert (BinOp (Var 6) Le (Var 0))),(Assume (Lit (LBool False))),(Assume (BinOp (Var 7) Eq (Var 5)))]"
definition block_3
  where
    "block_3  = [(Assume (BinOp (Var 3) Eq (BinOp (BinOp (Var 4) Mul (BinOp (Var 4) Sub (Lit (LInt 1)))) Div (Lit (LInt 2))))),(Assume (BinOp (Var 4) Le (Var 0)))]"
definition block_4
  where
    "block_4  = [(Assert (BinOp (Lit (LInt 0)) Eq (BinOp (BinOp (Lit (LInt 0)) Mul (BinOp (Lit (LInt 0)) Sub (Lit (LInt 1)))) Div (Lit (LInt 2))))),(Assert (BinOp (Lit (LInt 0)) Le (Var 0)))]"
definition block_5
  where
    "block_5  = []"
definition block_6
  where
    "block_6  = [(Assume (BinOp (Var 0) Ge (Lit (LInt 0))))]"
definition outEdges
  where
    "outEdges  = [[],[0],[0],[1,2],[3],[4],[5]]"
definition node_to_blocks
  where
    "node_to_blocks  = [block_0,block_1,block_2,block_3,block_4,block_5,block_6]"
definition proc_body
  where
    "proc_body  = (|entry = 6,out_edges = outEdges,node_to_block = node_to_blocks|)"
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
shows "((nth (out_edges proc_body) 3) = [1,2])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_4:
shows "((nth (out_edges proc_body) 4) = [3])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_5:
shows "((nth (out_edges proc_body) 5) = [4])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_6:
shows "((nth (out_edges proc_body) 6) = [5])"
by (simp add:proc_body_def outEdges_def)

definition params_vdecls :: "(vdecls)"
  where
    "params_vdecls  = [(0,(TPrim TInt),(None ))]"
definition locals_vdecls :: "(vdecls)"
  where
    "locals_vdecls  = [(1,(TPrim TInt),(None )),(3,(TPrim TInt),(None )),(4,(TPrim TInt),(None )),(5,(TPrim TInt),(None )),(6,(TPrim TInt),(None )),(7,(TPrim TInt),(None )),(2,(TPrim TInt),(None ))]"
lemma locals_min_aux:
shows "(((map fst (append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)) \<noteq> []) \<longrightarrow> ((Min (set (map fst (append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)))) \<ge> 0))"
unfolding triangle_passive_prog.params_vdecls_def triangle_passive_prog.locals_vdecls_def
by simp

lemma locals_min:
shows "(\<forall> x. ((Set.member x (set (map fst (append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)))) \<longrightarrow> (x \<ge> 0)))"
using locals_min_aux helper_min
by blast

lemma globals_locals_disj:
shows "((Set.inter (set (map fst (append global_data.constants_vdecls global_data.globals_vdecls))) (set (map fst (append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)))) = {})"
unfolding global_data.constants_vdecls_def global_data.globals_vdecls_def
by simp

lemma m_n:
shows "((map_of (append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls) 0) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_m:
shows "((map_of (append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls) 1) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_t_0:
shows "((map_of (append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls) 3) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_m_0:
shows "((map_of (append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls) 4) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_t_1:
shows "((map_of (append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls) 5) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_m_1:
shows "((map_of (append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls) 6) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_t_2:
shows "((map_of (append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls) 7) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_t:
shows "((map_of (append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls) 2) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma l_n:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)) 0) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)) 0) = (Some (TPrim TInt)))"
using globals_locals_disj m_n
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_m:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)) 1) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)) 1) = (Some (TPrim TInt)))"
using globals_locals_disj m_m
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_t_0:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)) 3) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)) 3) = (Some (TPrim TInt)))"
using globals_locals_disj m_t_0
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_m_0:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)) 4) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)) 4) = (Some (TPrim TInt)))"
using globals_locals_disj m_m_0
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_t_1:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)) 5) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)) 5) = (Some (TPrim TInt)))"
using globals_locals_disj m_t_1
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_m_1:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)) 6) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)) 6) = (Some (TPrim TInt)))"
using globals_locals_disj m_m_1
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_t_2:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)) 7) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)) 7) = (Some (TPrim TInt)))"
using globals_locals_disj m_t_2
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_t:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)) 2) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)) 2) = (Some (TPrim TInt)))"
using globals_locals_disj m_t
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)


end
