theory M_before_passive_prog
imports Boogie_Lang.Semantics Boogie_Lang.Util M_before_ast_to_cfg_prog
begin
definition block_0
  where
    "block_0  = []"
definition block_1
  where
    "block_1  = [(Assume (BinOp (Var 1) Gt (Lit (LInt 10)))),(Assign 0 (BinOp (Var 0) Mul (Lit (LInt 10)))),(Assume (Lit (LBool False)))]"
definition block_2
  where
    "block_2  = [(Assign 0 (BinOp (BinOp (Var 0) Add (Var 1)) Add (Var 2))),(Assume (Lit (LBool False)))]"
definition block_3
  where
    "block_3  = [(Assume (BinOp (BinOp (Var 0) Sub (Lit (LInt 10))) Gt (Lit (LInt 200)))),(Assign 1 (BinOp (Var 2) Add (Lit (LInt 7))))]"
definition block_4
  where
    "block_4  = [(Assume (BinOp (Lit (LInt 200)) Ge (BinOp (Var 0) Sub (Lit (LInt 10)))))]"
definition block_5
  where
    "block_5  = []"
definition block_6
  where
    "block_6  = [(Assume (BinOp (Lit (LInt 10)) Ge (Var 1)))]"
definition block_7
  where
    "block_7  = [(Havoc 0)]"
definition block_8
  where
    "block_8  = []"
definition block_9
  where
    "block_9  = [(Assign 2 (BinOp (Var 2) Sub (Lit (LInt 2))))]"
definition block_10
  where
    "block_10  = []"
definition block_11
  where
    "block_11  = [(Havoc 0),(Havoc 1)]"
definition block_12
  where
    "block_12  = [(Havoc 0),(Havoc 1),(Havoc 2)]"
definition block_13
  where
    "block_13  = []"
definition block_14
  where
    "block_14  = []"
definition outEdges
  where
    "outEdges  = [[],[0],[0],[2],[2],[3,4],[5],[6,1],[7],[0],[9],[10,8],[11],[12],[13]]"
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
shows "((nth (out_edges proc_body) 3) = [2])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_4:
shows "((nth (out_edges proc_body) 4) = [2])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_5:
shows "((nth (out_edges proc_body) 5) = [3,4])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_6:
shows "((nth (out_edges proc_body) 6) = [5])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_7:
shows "((nth (out_edges proc_body) 7) = [6,1])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_8:
shows "((nth (out_edges proc_body) 8) = [7])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_9:
shows "((nth (out_edges proc_body) 9) = [0])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_10:
shows "((nth (out_edges proc_body) 10) = [9])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_11:
shows "((nth (out_edges proc_body) 11) = [10,8])"
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
shows "(((map fst (append M_before_ast_to_cfg_prog.params_vdecls M_before_ast_to_cfg_prog.locals_vdecls)) \<noteq> []) \<longrightarrow> ((Min (set (map fst (append M_before_ast_to_cfg_prog.params_vdecls M_before_ast_to_cfg_prog.locals_vdecls)))) \<ge> 0))"
unfolding M_before_ast_to_cfg_prog.params_vdecls_def M_before_ast_to_cfg_prog.locals_vdecls_def
by simp

lemma locals_min:
shows "(\<forall> x. ((Set.member x (set (map fst (append M_before_ast_to_cfg_prog.params_vdecls M_before_ast_to_cfg_prog.locals_vdecls)))) \<longrightarrow> (x \<ge> 0)))"
using locals_min_aux helper_min
by blast

lemma globals_locals_disj:
shows "((Set.inter (set (map fst (append M_before_ast_to_cfg_prog.constants_vdecls M_before_ast_to_cfg_prog.globals_vdecls))) (set (map fst (append M_before_ast_to_cfg_prog.params_vdecls M_before_ast_to_cfg_prog.locals_vdecls)))) = {})"
unfolding M_before_ast_to_cfg_prog.constants_vdecls_def M_before_ast_to_cfg_prog.globals_vdecls_def
by simp


end
