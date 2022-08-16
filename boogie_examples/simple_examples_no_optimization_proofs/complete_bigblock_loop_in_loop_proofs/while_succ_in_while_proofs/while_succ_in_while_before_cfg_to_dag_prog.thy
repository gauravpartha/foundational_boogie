theory while_succ_in_while_before_cfg_to_dag_prog
imports Boogie_Lang.Semantics Boogie_Lang.TypeSafety Boogie_Lang.Util "../global_data"
begin
definition block_0
  where
    "block_0  = [(Havoc 0),(Havoc 1)]"
definition block_1
  where
    "block_1  = []"
definition block_2
  where
    "block_2  = [(Assume (BinOp (Var 0) Gt (Lit (LInt 0)))),(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1))))]"
definition block_3
  where
    "block_3  = []"
definition block_4
  where
    "block_4  = [(Assume (BinOp (Var 1) Gt (Lit (LInt 0)))),(Assign 1 (BinOp (Var 1) Sub (Lit (LInt 1))))]"
definition block_5
  where
    "block_5  = [(Assume (BinOp (Lit (LInt 0)) Ge (Var 1)))]"
definition block_6
  where
    "block_6  = []"
definition block_7
  where
    "block_7  = [(Assume (BinOp (Lit (LInt 0)) Ge (Var 0)))]"
definition block_8
  where
    "block_8  = [(Assert (BinOp (Var 0) Eq (Lit (LInt 0))))]"
definition outEdges
  where
    "outEdges  = [[1],[7,2],[3],[5,4],[3],[6],[1],[8],[]]"
definition node_to_blocks
  where
    "node_to_blocks  = [block_0,block_1,block_2,block_3,block_4,block_5,block_6,block_7,block_8]"
definition proc_body
  where
    "proc_body  = (|entry = 0,out_edges = outEdges,node_to_block = node_to_blocks|)"
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

lemma outEdges_0:
shows "((nth (out_edges proc_body) 0) = [1])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_1:
shows "((nth (out_edges proc_body) 1) = [7,2])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_2:
shows "((nth (out_edges proc_body) 2) = [3])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_3:
shows "((nth (out_edges proc_body) 3) = [5,4])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_4:
shows "((nth (out_edges proc_body) 4) = [3])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_5:
shows "((nth (out_edges proc_body) 5) = [6])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_6:
shows "((nth (out_edges proc_body) 6) = [1])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_7:
shows "((nth (out_edges proc_body) 7) = [8])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_8:
shows "((nth (out_edges proc_body) 8) = [])"
by (simp add:proc_body_def outEdges_def)

definition pres
  where
    "pres  = []"
definition post
  where
    "post  = []"
definition params_vdecls :: "(vdecls)"
  where
    "params_vdecls  = []"
definition locals_vdecls :: "(vdecls)"
  where
    "locals_vdecls  = [(0,(TPrim TInt),(None )),(1,(TPrim TInt),(None ))]"
definition axioms
  where
    "axioms  = []"
definition fdecls
  where
    "fdecls  = []"
definition globals_vdecls :: "(vdecls)"
  where
    "globals_vdecls  = []"
definition constants_vdecls :: "(vdecls)"
  where
    "constants_vdecls  = []"
lemma globals_max_aux:
shows "(((map fst (append while_succ_in_while_before_cfg_to_dag_prog.constants_vdecls while_succ_in_while_before_cfg_to_dag_prog.globals_vdecls)) \<noteq> []) \<longrightarrow> ((Max (set (map fst (append while_succ_in_while_before_cfg_to_dag_prog.constants_vdecls while_succ_in_while_before_cfg_to_dag_prog.globals_vdecls)))) \<le> 0))"
unfolding while_succ_in_while_before_cfg_to_dag_prog.constants_vdecls_def while_succ_in_while_before_cfg_to_dag_prog.globals_vdecls_def
by simp

lemma globals_max:
shows "(\<forall> x. ((Set.member x (set (map fst (append while_succ_in_while_before_cfg_to_dag_prog.constants_vdecls while_succ_in_while_before_cfg_to_dag_prog.globals_vdecls)))) \<longrightarrow> (x \<le> 0)))"
using globals_max_aux helper_max
by blast

lemma locals_min_aux:
shows "(((map fst (append while_succ_in_while_before_cfg_to_dag_prog.params_vdecls while_succ_in_while_before_cfg_to_dag_prog.locals_vdecls)) \<noteq> []) \<longrightarrow> ((Min (set (map fst (append while_succ_in_while_before_cfg_to_dag_prog.params_vdecls while_succ_in_while_before_cfg_to_dag_prog.locals_vdecls)))) \<ge> 0))"
unfolding while_succ_in_while_before_cfg_to_dag_prog.params_vdecls_def while_succ_in_while_before_cfg_to_dag_prog.locals_vdecls_def
by simp

lemma locals_min:
shows "(\<forall> x. ((Set.member x (set (map fst (append while_succ_in_while_before_cfg_to_dag_prog.params_vdecls while_succ_in_while_before_cfg_to_dag_prog.locals_vdecls)))) \<longrightarrow> (x \<ge> 0)))"
using locals_min_aux helper_min
by blast

lemma globals_locals_disj:
shows "((Set.inter (set (map fst (append while_succ_in_while_before_cfg_to_dag_prog.constants_vdecls while_succ_in_while_before_cfg_to_dag_prog.globals_vdecls))) (set (map fst (append while_succ_in_while_before_cfg_to_dag_prog.params_vdecls while_succ_in_while_before_cfg_to_dag_prog.locals_vdecls)))) = {})"
unfolding while_succ_in_while_before_cfg_to_dag_prog.constants_vdecls_def while_succ_in_while_before_cfg_to_dag_prog.globals_vdecls_def
by simp

lemma funcs_wf:
shows "((list_all (comp wf_fdecl snd) fdecls) )"
unfolding fdecls_def
by simp

lemma consts_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) while_succ_in_while_before_cfg_to_dag_prog.constants_vdecls) )"
unfolding while_succ_in_while_before_cfg_to_dag_prog.constants_vdecls_def
by simp

lemma globals_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) while_succ_in_while_before_cfg_to_dag_prog.globals_vdecls) )"
unfolding while_succ_in_while_before_cfg_to_dag_prog.globals_vdecls_def
by simp

lemma params_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) while_succ_in_while_before_cfg_to_dag_prog.params_vdecls) )"
unfolding while_succ_in_while_before_cfg_to_dag_prog.params_vdecls_def
by simp

lemma locals_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) while_succ_in_while_before_cfg_to_dag_prog.locals_vdecls) )"
unfolding while_succ_in_while_before_cfg_to_dag_prog.locals_vdecls_def
by simp

lemma var_context_wf:
shows "(\<forall> x \<tau>. (((lookup_var_ty ((append while_succ_in_while_before_cfg_to_dag_prog.constants_vdecls while_succ_in_while_before_cfg_to_dag_prog.globals_vdecls),(append while_succ_in_while_before_cfg_to_dag_prog.params_vdecls while_succ_in_while_before_cfg_to_dag_prog.locals_vdecls)) x) = (Some \<tau>)) \<longrightarrow> ((wf_ty 0) \<tau>)))"
apply (rule lookup_ty_pred_2)
by ((simp_all add:consts_wf globals_wf params_wf locals_wf))

lemma m_x:
shows "((map_of (append while_succ_in_while_before_cfg_to_dag_prog.params_vdecls while_succ_in_while_before_cfg_to_dag_prog.locals_vdecls) 0) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_y:
shows "((map_of (append while_succ_in_while_before_cfg_to_dag_prog.params_vdecls while_succ_in_while_before_cfg_to_dag_prog.locals_vdecls) 1) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma l_x:
shows "((lookup_var_decl ((append while_succ_in_while_before_cfg_to_dag_prog.constants_vdecls while_succ_in_while_before_cfg_to_dag_prog.globals_vdecls),(append while_succ_in_while_before_cfg_to_dag_prog.params_vdecls while_succ_in_while_before_cfg_to_dag_prog.locals_vdecls)) 0) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append while_succ_in_while_before_cfg_to_dag_prog.constants_vdecls while_succ_in_while_before_cfg_to_dag_prog.globals_vdecls),(append while_succ_in_while_before_cfg_to_dag_prog.params_vdecls while_succ_in_while_before_cfg_to_dag_prog.locals_vdecls)) 0) = (Some (TPrim TInt)))"
using globals_locals_disj m_x
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_y:
shows "((lookup_var_decl ((append while_succ_in_while_before_cfg_to_dag_prog.constants_vdecls while_succ_in_while_before_cfg_to_dag_prog.globals_vdecls),(append while_succ_in_while_before_cfg_to_dag_prog.params_vdecls while_succ_in_while_before_cfg_to_dag_prog.locals_vdecls)) 1) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append while_succ_in_while_before_cfg_to_dag_prog.constants_vdecls while_succ_in_while_before_cfg_to_dag_prog.globals_vdecls),(append while_succ_in_while_before_cfg_to_dag_prog.params_vdecls while_succ_in_while_before_cfg_to_dag_prog.locals_vdecls)) 1) = (Some (TPrim TInt)))"
using globals_locals_disj m_y
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

definition proc :: "(mbodyCFG procedure)"
  where
    "proc  = (|proc_ty_args = 0,proc_args = while_succ_in_while_before_cfg_to_dag_prog.params_vdecls,proc_rets = [],proc_modifs = [],proc_pres = (exprs_to_only_checked_spec while_succ_in_while_before_cfg_to_dag_prog.pres),proc_posts = (exprs_to_only_checked_spec while_succ_in_while_before_cfg_to_dag_prog.post),proc_body = (Some (while_succ_in_while_before_cfg_to_dag_prog.locals_vdecls,while_succ_in_while_before_cfg_to_dag_prog.proc_body))|)"

end
