theory M_before_cfg_to_dag_prog
imports Boogie_Lang.Semantics Boogie_Lang.TypeSafety Boogie_Lang.Util "../global_data"
begin
definition block_0
  where
    "block_0  = [(Havoc 0),(Havoc 1),(Havoc 2)]"
definition block_1
  where
    "block_1  = []"
definition block_2
  where
    "block_2  = [(Assume (BinOp (Var 1) Gt (Lit (LInt 10)))),(Assign 0 (BinOp (Var 0) Mul (Lit (LInt 10))))]"
definition block_3
  where
    "block_3  = []"
definition block_4
  where
    "block_4  = [(Assign 0 (BinOp (BinOp (Var 0) Add (Var 1)) Add (Var 2)))]"
definition block_5
  where
    "block_5  = [(Assume (BinOp (BinOp (Var 0) Sub (Lit (LInt 10))) Gt (Lit (LInt 200)))),(Assign 1 (BinOp (Var 2) Add (Lit (LInt 7))))]"
definition block_6
  where
    "block_6  = [(Assume (BinOp (Lit (LInt 200)) Ge (BinOp (Var 0) Sub (Lit (LInt 10)))))]"
definition block_7
  where
    "block_7  = []"
definition block_8
  where
    "block_8  = []"
definition block_9
  where
    "block_9  = [(Assume (BinOp (Lit (LInt 10)) Ge (Var 1)))]"
definition outEdges
  where
    "outEdges  = [[1],[9,2],[3],[7,4],[5,6],[3],[3],[8],[1],[]]"
definition node_to_blocks
  where
    "node_to_blocks  = [block_0,block_1,block_2,block_3,block_4,block_5,block_6,block_7,block_8,block_9]"
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

lemma node_9:
shows "((nth (node_to_block proc_body) 9) = block_9)"
by (simp add:proc_body_def node_to_blocks_def)

lemma outEdges_0:
shows "((nth (out_edges proc_body) 0) = [1])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_1:
shows "((nth (out_edges proc_body) 1) = [9,2])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_2:
shows "((nth (out_edges proc_body) 2) = [3])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_3:
shows "((nth (out_edges proc_body) 3) = [7,4])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_4:
shows "((nth (out_edges proc_body) 4) = [5,6])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_5:
shows "((nth (out_edges proc_body) 5) = [3])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_6:
shows "((nth (out_edges proc_body) 6) = [3])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_7:
shows "((nth (out_edges proc_body) 7) = [8])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_8:
shows "((nth (out_edges proc_body) 8) = [1])"
by (simp add:proc_body_def outEdges_def)

lemma outEdges_9:
shows "((nth (out_edges proc_body) 9) = [])"
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
    "locals_vdecls  = [(0,(TPrim TInt),(None )),(1,(TPrim TInt),(None )),(2,(TPrim TInt),(None ))]"
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
shows "(((map fst (append M_before_cfg_to_dag_prog.constants_vdecls M_before_cfg_to_dag_prog.globals_vdecls)) \<noteq> []) \<longrightarrow> ((Max (set (map fst (append M_before_cfg_to_dag_prog.constants_vdecls M_before_cfg_to_dag_prog.globals_vdecls)))) \<le> 0))"
unfolding M_before_cfg_to_dag_prog.constants_vdecls_def M_before_cfg_to_dag_prog.globals_vdecls_def
by simp

lemma globals_max:
shows "(\<forall> x. ((Set.member x (set (map fst (append M_before_cfg_to_dag_prog.constants_vdecls M_before_cfg_to_dag_prog.globals_vdecls)))) \<longrightarrow> (x \<le> 0)))"
using globals_max_aux helper_max
by blast

lemma locals_min_aux:
shows "(((map fst (append M_before_cfg_to_dag_prog.params_vdecls M_before_cfg_to_dag_prog.locals_vdecls)) \<noteq> []) \<longrightarrow> ((Min (set (map fst (append M_before_cfg_to_dag_prog.params_vdecls M_before_cfg_to_dag_prog.locals_vdecls)))) \<ge> 0))"
unfolding M_before_cfg_to_dag_prog.params_vdecls_def M_before_cfg_to_dag_prog.locals_vdecls_def
by simp

lemma locals_min:
shows "(\<forall> x. ((Set.member x (set (map fst (append M_before_cfg_to_dag_prog.params_vdecls M_before_cfg_to_dag_prog.locals_vdecls)))) \<longrightarrow> (x \<ge> 0)))"
using locals_min_aux helper_min
by blast

lemma globals_locals_disj:
shows "((Set.inter (set (map fst (append M_before_cfg_to_dag_prog.constants_vdecls M_before_cfg_to_dag_prog.globals_vdecls))) (set (map fst (append M_before_cfg_to_dag_prog.params_vdecls M_before_cfg_to_dag_prog.locals_vdecls)))) = {})"
unfolding M_before_cfg_to_dag_prog.constants_vdecls_def M_before_cfg_to_dag_prog.globals_vdecls_def
by simp

lemma funcs_wf:
shows "((list_all (comp wf_fdecl snd) fdecls) )"
unfolding fdecls_def
by simp

lemma consts_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) M_before_cfg_to_dag_prog.constants_vdecls) )"
unfolding M_before_cfg_to_dag_prog.constants_vdecls_def
by simp

lemma globals_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) M_before_cfg_to_dag_prog.globals_vdecls) )"
unfolding M_before_cfg_to_dag_prog.globals_vdecls_def
by simp

lemma params_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) M_before_cfg_to_dag_prog.params_vdecls) )"
unfolding M_before_cfg_to_dag_prog.params_vdecls_def
by simp

lemma locals_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) M_before_cfg_to_dag_prog.locals_vdecls) )"
unfolding M_before_cfg_to_dag_prog.locals_vdecls_def
by simp

lemma var_context_wf:
shows "(\<forall> x \<tau>. (((lookup_var_ty ((append M_before_cfg_to_dag_prog.constants_vdecls M_before_cfg_to_dag_prog.globals_vdecls),(append M_before_cfg_to_dag_prog.params_vdecls M_before_cfg_to_dag_prog.locals_vdecls)) x) = (Some \<tau>)) \<longrightarrow> ((wf_ty 0) \<tau>)))"
apply (rule lookup_ty_pred_2)
by ((simp_all add:consts_wf globals_wf params_wf locals_wf))

lemma m_x:
shows "((map_of (append M_before_cfg_to_dag_prog.params_vdecls M_before_cfg_to_dag_prog.locals_vdecls) 0) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_y:
shows "((map_of (append M_before_cfg_to_dag_prog.params_vdecls M_before_cfg_to_dag_prog.locals_vdecls) 1) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_z:
shows "((map_of (append M_before_cfg_to_dag_prog.params_vdecls M_before_cfg_to_dag_prog.locals_vdecls) 2) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma l_x:
shows "((lookup_var_decl ((append M_before_cfg_to_dag_prog.constants_vdecls M_before_cfg_to_dag_prog.globals_vdecls),(append M_before_cfg_to_dag_prog.params_vdecls M_before_cfg_to_dag_prog.locals_vdecls)) 0) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append M_before_cfg_to_dag_prog.constants_vdecls M_before_cfg_to_dag_prog.globals_vdecls),(append M_before_cfg_to_dag_prog.params_vdecls M_before_cfg_to_dag_prog.locals_vdecls)) 0) = (Some (TPrim TInt)))"
using globals_locals_disj m_x
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_y:
shows "((lookup_var_decl ((append M_before_cfg_to_dag_prog.constants_vdecls M_before_cfg_to_dag_prog.globals_vdecls),(append M_before_cfg_to_dag_prog.params_vdecls M_before_cfg_to_dag_prog.locals_vdecls)) 1) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append M_before_cfg_to_dag_prog.constants_vdecls M_before_cfg_to_dag_prog.globals_vdecls),(append M_before_cfg_to_dag_prog.params_vdecls M_before_cfg_to_dag_prog.locals_vdecls)) 1) = (Some (TPrim TInt)))"
using globals_locals_disj m_y
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_z:
shows "((lookup_var_decl ((append M_before_cfg_to_dag_prog.constants_vdecls M_before_cfg_to_dag_prog.globals_vdecls),(append M_before_cfg_to_dag_prog.params_vdecls M_before_cfg_to_dag_prog.locals_vdecls)) 2) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append M_before_cfg_to_dag_prog.constants_vdecls M_before_cfg_to_dag_prog.globals_vdecls),(append M_before_cfg_to_dag_prog.params_vdecls M_before_cfg_to_dag_prog.locals_vdecls)) 2) = (Some (TPrim TInt)))"
using globals_locals_disj m_z
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

definition proc :: "(mbodyCFG procedure)"
  where
    "proc  = (|proc_ty_args = 0,proc_args = M_before_cfg_to_dag_prog.params_vdecls,proc_rets = [],proc_modifs = [],proc_pres = (exprs_to_only_checked_spec M_before_cfg_to_dag_prog.pres),proc_posts = (exprs_to_only_checked_spec M_before_cfg_to_dag_prog.post),proc_body = (Some (M_before_cfg_to_dag_prog.locals_vdecls,M_before_cfg_to_dag_prog.proc_body))|)"

end
