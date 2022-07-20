theory trivial_assert_false_passive_prog
imports Boogie_Lang.Semantics Boogie_Lang.Util trivial_assert_false_before_ast_to_cfg_prog
begin
definition block_0
  where
    "block_0  = [(Assert (Lit (LBool False)))]"
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

definition params_vdecls :: "(vdecls)"
  where
    "params_vdecls  = []"
definition locals_vdecls :: "(vdecls)"
  where
    "locals_vdecls  = []"
lemma locals_min_aux:
shows "(((map fst (append trivial_assert_false_passive_prog.params_vdecls trivial_assert_false_passive_prog.locals_vdecls)) \<noteq> []) \<longrightarrow> ((Min (set (map fst (append trivial_assert_false_passive_prog.params_vdecls trivial_assert_false_passive_prog.locals_vdecls)))) \<ge> 0))"
unfolding trivial_assert_false_passive_prog.params_vdecls_def trivial_assert_false_passive_prog.locals_vdecls_def
by simp

lemma locals_min:
shows "(\<forall> x. ((Set.member x (set (map fst (append trivial_assert_false_passive_prog.params_vdecls trivial_assert_false_passive_prog.locals_vdecls)))) \<longrightarrow> (x \<ge> 0)))"
using locals_min_aux helper_min
by blast

lemma globals_locals_disj:
shows "((Set.inter (set (map fst (append trivial_assert_false_before_ast_to_cfg_prog.constants_vdecls trivial_assert_false_before_ast_to_cfg_prog.globals_vdecls))) (set (map fst (append trivial_assert_false_passive_prog.params_vdecls trivial_assert_false_passive_prog.locals_vdecls)))) = {})"
unfolding trivial_assert_false_before_ast_to_cfg_prog.constants_vdecls_def trivial_assert_false_before_ast_to_cfg_prog.globals_vdecls_def
by simp


end
