theory p_before_passive_prog
imports Boogie_Lang.Semantics Boogie_Lang.Util p_before_ast_to_cfg_prog
begin
definition block_0
  where
    "block_0  = [(Assume (FunExp ''f'' [] [(Var 1)])),(Assert (FunExp ''f'' [] [(Var 1)]))]"
definition block_1
  where
    "block_1  = []"
definition block_2
  where
    "block_2  = []"
definition outEdges
  where
    "outEdges  = [[],[0],[1]]"
definition node_to_blocks
  where
    "node_to_blocks  = [block_0,block_1,block_2]"
definition proc_body
  where
    "proc_body  = (|entry = 2,out_edges = outEdges,node_to_block = node_to_blocks|)"
lemma node_0:
shows "((nth (node_to_block proc_body) 0) = block_0)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_1:
shows "((nth (node_to_block proc_body) 1) = block_1)"
by (simp add:proc_body_def node_to_blocks_def)

lemma node_2:
shows "((nth (node_to_block proc_body) 2) = block_2)"
by (simp add:proc_body_def node_to_blocks_def)

lemma outEdges_0:
shows "((nth (out_edges proc_body) 0) = [])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_1:
shows "((nth (out_edges proc_body) 1) = [0])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_2:
shows "((nth (out_edges proc_body) 2) = [1])"
by (simp add:proc_body_def outEdges_def)

lemma locals_min_aux:
shows "(((map fst (append p_before_ast_to_cfg_prog.params_vdecls p_before_ast_to_cfg_prog.locals_vdecls)) \<noteq> []) \<longrightarrow> ((Min (set (map fst (append p_before_ast_to_cfg_prog.params_vdecls p_before_ast_to_cfg_prog.locals_vdecls)))) \<ge> 0))"
unfolding p_before_ast_to_cfg_prog.params_vdecls_def p_before_ast_to_cfg_prog.locals_vdecls_def
by simp

lemma locals_min:
shows "(\<forall> x. ((Set.member x (set (map fst (append p_before_ast_to_cfg_prog.params_vdecls p_before_ast_to_cfg_prog.locals_vdecls)))) \<longrightarrow> (x \<ge> 0)))"
using locals_min_aux helper_min
by blast

lemma globals_locals_disj:
shows "((Set.inter (set (map fst (append p_before_ast_to_cfg_prog.constants_vdecls p_before_ast_to_cfg_prog.globals_vdecls))) (set (map fst (append p_before_ast_to_cfg_prog.params_vdecls p_before_ast_to_cfg_prog.locals_vdecls)))) = {})"
unfolding p_before_ast_to_cfg_prog.constants_vdecls_def p_before_ast_to_cfg_prog.globals_vdecls_def
by simp


end
