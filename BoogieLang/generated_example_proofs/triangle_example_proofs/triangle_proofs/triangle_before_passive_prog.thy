theory triangle_before_passive_prog
imports Boogie_Lang.Semantics Boogie_Lang.Util triangle_before_cfg_to_dag_prog
begin
definition block_0
  where
    "block_0  = [(Assert (BinOp (Var 2) Eq (BinOp (BinOp (Var 0) Mul (BinOp (Var 0) Sub (Lit (LInt 1)))) Div (Lit (LInt 2)))))]"
definition block_1
  where
    "block_1  = [(Assume (BinOp (Var 0) Le (Var 1)))]"
definition block_2
  where
    "block_2  = [(Assume (BinOp (Var 1) Lt (Var 0))),(Assign 2 (BinOp (Var 2) Add (Var 1))),(Assign 1 (BinOp (Var 1) Add (Lit (LInt 1)))),(Assert (BinOp (Var 2) Eq (BinOp (BinOp (Var 1) Mul (BinOp (Var 1) Sub (Lit (LInt 1)))) Div (Lit (LInt 2))))),(Assert (BinOp (Var 1) Le (Var 0))),(Assume (Lit (LBool False)))]"
definition block_3
  where
    "block_3  = [(Havoc 2),(Havoc 1),(Assume (BinOp (Var 2) Eq (BinOp (BinOp (Var 1) Mul (BinOp (Var 1) Sub (Lit (LInt 1)))) Div (Lit (LInt 2))))),(Assume (BinOp (Var 1) Le (Var 0)))]"
definition block_4
  where
    "block_4  = [(Assign 1 (Lit (LInt 0))),(Assign 2 (Lit (LInt 0))),(Assert (BinOp (Var 2) Eq (BinOp (BinOp (Var 1) Mul (BinOp (Var 1) Sub (Lit (LInt 1)))) Div (Lit (LInt 2))))),(Assert (BinOp (Var 1) Le (Var 0)))]"
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

lemma locals_min_aux:
shows "(((map fst (append triangle_before_cfg_to_dag_prog.params_vdecls triangle_before_cfg_to_dag_prog.locals_vdecls)) \<noteq> []) \<longrightarrow> ((Min (set (map fst (append triangle_before_cfg_to_dag_prog.params_vdecls triangle_before_cfg_to_dag_prog.locals_vdecls)))) \<ge> 0))"
unfolding triangle_before_cfg_to_dag_prog.params_vdecls_def triangle_before_cfg_to_dag_prog.locals_vdecls_def
by simp

lemma locals_min:
shows "(\<forall> x. ((Set.member x (set (map fst (append triangle_before_cfg_to_dag_prog.params_vdecls triangle_before_cfg_to_dag_prog.locals_vdecls)))) \<longrightarrow> (x \<ge> 0)))"
using locals_min_aux helper_min
by blast

lemma globals_locals_disj:
shows "((Set.inter (set (map fst (append global_data.constants_vdecls global_data.globals_vdecls))) (set (map fst (append triangle_before_cfg_to_dag_prog.params_vdecls triangle_before_cfg_to_dag_prog.locals_vdecls)))) = {})"
unfolding global_data.constants_vdecls_def global_data.globals_vdecls_def
by simp


end
