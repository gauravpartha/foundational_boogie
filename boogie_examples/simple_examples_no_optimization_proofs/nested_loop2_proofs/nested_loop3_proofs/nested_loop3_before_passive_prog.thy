theory nested_loop3_before_passive_prog
imports Boogie_Lang.Semantics Boogie_Lang.Util nested_loop3_before_ast_to_cfg_prog
begin
definition block_0
  where
    "block_0  = []"
definition block_1
  where
    "block_1  = [(Assume (BinOp (Lit (LInt 0)) Ge (Var 2)))]"
definition block_2
  where
    "block_2  = [(Assume (BinOp (Var 1) Gt (Lit (LInt 0)))),(Assign 2 (BinOp (Var 2) Sub (Lit (LInt 1)))),(Assign 1 (BinOp (Var 1) Sub (Lit (LInt 1)))),(Assert (BinOp (Var 1) Ge (Lit (LInt 0)))),(Assume (Lit (LBool False)))]"
definition block_3
  where
    "block_3  = [(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1)))),(Assert (BinOp (Var 0) Ge (Lit (LInt 0)))),(Assume (Lit (LBool False)))]"
definition block_4
  where
    "block_4  = [(Assume (BinOp (Lit (LInt 0)) Ge (Var 1)))]"
definition block_5
  where
    "block_5  = [(Havoc 2),(Havoc 1),(Assume (BinOp (Var 1) Ge (Lit (LInt 0))))]"
definition block_6
  where
    "block_6  = [(Assume (BinOp (Var 0) Gt (Lit (LInt 0)))),(Assert (BinOp (Var 1) Ge (Lit (LInt 0))))]"
definition block_7
  where
    "block_7  = [(Assume (Lit (LBool False)))]"
definition block_8
  where
    "block_8  = [(Assume (BinOp (Lit (LInt 0)) Ge (Var 0)))]"
definition block_9
  where
    "block_9  = [(Havoc 0),(Havoc 2),(Havoc 1),(Assume (BinOp (Var 0) Ge (Lit (LInt 0))))]"
definition block_10
  where
    "block_10  = [(Assume (BinOp (Var 2) Gt (Lit (LInt 0)))),(Assert (BinOp (Var 0) Ge (Lit (LInt 0))))]"
definition block_11
  where
    "block_11  = [(Havoc 0),(Havoc 2),(Havoc 1)]"
definition block_12
  where
    "block_12  = [(Assign 0 (Lit (LInt 10))),(Assign 1 (Lit (LInt 10))),(Assign 2 (Lit (LInt 10)))]"
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

lemma locals_min_aux:
shows "(((map fst (append nested_loop3_before_ast_to_cfg_prog.params_vdecls nested_loop3_before_ast_to_cfg_prog.locals_vdecls)) \<noteq> []) \<longrightarrow> ((Min (set (map fst (append nested_loop3_before_ast_to_cfg_prog.params_vdecls nested_loop3_before_ast_to_cfg_prog.locals_vdecls)))) \<ge> 0))"
unfolding nested_loop3_before_ast_to_cfg_prog.params_vdecls_def nested_loop3_before_ast_to_cfg_prog.locals_vdecls_def
by simp

lemma locals_min:
shows "(\<forall> x. ((Set.member x (set (map fst (append nested_loop3_before_ast_to_cfg_prog.params_vdecls nested_loop3_before_ast_to_cfg_prog.locals_vdecls)))) \<longrightarrow> (x \<ge> 0)))"
using locals_min_aux helper_min
by blast

lemma globals_locals_disj:
shows "((Set.inter (set (map fst (append nested_loop3_before_ast_to_cfg_prog.constants_vdecls nested_loop3_before_ast_to_cfg_prog.globals_vdecls))) (set (map fst (append nested_loop3_before_ast_to_cfg_prog.params_vdecls nested_loop3_before_ast_to_cfg_prog.locals_vdecls)))) = {})"
unfolding nested_loop3_before_ast_to_cfg_prog.constants_vdecls_def nested_loop3_before_ast_to_cfg_prog.globals_vdecls_def
by simp


end
