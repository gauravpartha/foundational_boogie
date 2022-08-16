theory assert_false_in_if_3_passive_prog
imports Boogie_Lang.Semantics Boogie_Lang.Util assert_false_in_if_3_before_ast_to_cfg_prog
begin
definition block_0
  where
    "block_0  = [(Assert (BinOp (Lit (LInt 7)) Eq (Lit (LInt 7))))]"
definition block_1
  where
    "block_1  = [(Assert (Lit (LBool False)))]"
definition block_2
  where
    "block_2  = []"
definition block_3
  where
    "block_3  = []"
definition block_4
  where
    "block_4  = []"
definition block_5
  where
    "block_5  = []"
definition outEdges
  where
    "outEdges  = [[],[0],[0],[1,2],[3],[4]]"
definition node_to_blocks
  where
    "node_to_blocks  = [block_0,block_1,block_2,block_3,block_4,block_5]"
definition proc_body
  where
    "proc_body  = (|entry = 5,out_edges = outEdges,node_to_block = node_to_blocks|)"
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

definition params_vdecls :: "(vdecls)"
  where
    "params_vdecls  = []"
definition locals_vdecls :: "(vdecls)"
  where
    "locals_vdecls  = [(0,(TPrim TInt),(None )),(1,(TPrim TInt),(None ))]"
lemma locals_min_aux:
shows "(((map fst (append assert_false_in_if_3_passive_prog.params_vdecls assert_false_in_if_3_passive_prog.locals_vdecls)) \<noteq> []) \<longrightarrow> ((Min (set (map fst (append assert_false_in_if_3_passive_prog.params_vdecls assert_false_in_if_3_passive_prog.locals_vdecls)))) \<ge> 0))"
unfolding assert_false_in_if_3_passive_prog.params_vdecls_def assert_false_in_if_3_passive_prog.locals_vdecls_def
by simp

lemma locals_min:
shows "(\<forall> x. ((Set.member x (set (map fst (append assert_false_in_if_3_passive_prog.params_vdecls assert_false_in_if_3_passive_prog.locals_vdecls)))) \<longrightarrow> (x \<ge> 0)))"
using locals_min_aux helper_min
by blast

lemma globals_locals_disj:
shows "((Set.inter (set (map fst (append assert_false_in_if_3_before_ast_to_cfg_prog.constants_vdecls assert_false_in_if_3_before_ast_to_cfg_prog.globals_vdecls))) (set (map fst (append assert_false_in_if_3_passive_prog.params_vdecls assert_false_in_if_3_passive_prog.locals_vdecls)))) = {})"
unfolding assert_false_in_if_3_before_ast_to_cfg_prog.constants_vdecls_def assert_false_in_if_3_before_ast_to_cfg_prog.globals_vdecls_def
by simp

lemma m_x:
shows "((map_of (append assert_false_in_if_3_passive_prog.params_vdecls assert_false_in_if_3_passive_prog.locals_vdecls) 0) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_x_0:
shows "((map_of (append assert_false_in_if_3_passive_prog.params_vdecls assert_false_in_if_3_passive_prog.locals_vdecls) 1) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma l_x:
shows "((lookup_var_decl ((append assert_false_in_if_3_before_ast_to_cfg_prog.constants_vdecls assert_false_in_if_3_before_ast_to_cfg_prog.globals_vdecls),(append assert_false_in_if_3_passive_prog.params_vdecls assert_false_in_if_3_passive_prog.locals_vdecls)) 0) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append assert_false_in_if_3_before_ast_to_cfg_prog.constants_vdecls assert_false_in_if_3_before_ast_to_cfg_prog.globals_vdecls),(append assert_false_in_if_3_passive_prog.params_vdecls assert_false_in_if_3_passive_prog.locals_vdecls)) 0) = (Some (TPrim TInt)))"
using globals_locals_disj m_x
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_x_0:
shows "((lookup_var_decl ((append assert_false_in_if_3_before_ast_to_cfg_prog.constants_vdecls assert_false_in_if_3_before_ast_to_cfg_prog.globals_vdecls),(append assert_false_in_if_3_passive_prog.params_vdecls assert_false_in_if_3_passive_prog.locals_vdecls)) 1) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append assert_false_in_if_3_before_ast_to_cfg_prog.constants_vdecls assert_false_in_if_3_before_ast_to_cfg_prog.globals_vdecls),(append assert_false_in_if_3_passive_prog.params_vdecls assert_false_in_if_3_passive_prog.locals_vdecls)) 1) = (Some (TPrim TInt)))"
using globals_locals_disj m_x_0
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)


end
