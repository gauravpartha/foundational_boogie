theory p_before_cfg_to_dag_prog
imports Boogie_Lang.Semantics Boogie_Lang.TypeSafety Boogie_Lang.Util "../global_data"
begin
definition block_0
  where
    "block_0  = [(Assume (FunExp ''f'' [] [(Var 0)])),(Assume (FunExp ''g'' [] [(Var 1)])),(Assert (FunExp ''f'' [] [(Var 0)])),(Assert (FunExp ''g'' [] [(Var 1)]))]"
definition outEdges
  where
    "outEdges  = [[]]"
definition node_to_blocks
  where
    "node_to_blocks  = [block_0]"
definition proc_body
  where
    "proc_body  = (|entry = 0,out_edges = outEdges,node_to_block = node_to_blocks|)"
lemma node_0:
shows "((nth (node_to_block proc_body) 0) = block_0)"
by (simp add:proc_body_def node_to_blocks_def)

lemma outEdges_0:
shows "((nth (out_edges proc_body) 0) = [])"
by (simp add:proc_body_def outEdges_def)

definition pres
  where
    "pres  = []"
definition post
  where
    "post  = []"
definition params_vdecls :: "(vdecls)"
  where
    "params_vdecls  = [(2,(TPrim TInt),(None ))]"
definition locals_vdecls :: "(vdecls)"
  where
    "locals_vdecls  = []"
definition axioms
  where
    "axioms  = []"
definition fdecls
  where
    "fdecls  = [(''f'',0,[(TPrim TInt)],(TPrim TBool)),(''g'',0,[(TPrim TBool)],(TPrim TBool))]"
definition globals_vdecls :: "(vdecls)"
  where
    "globals_vdecls  = [(0,(TPrim TInt),(None )),(1,(TPrim TBool),(None ))]"
definition constants_vdecls :: "(vdecls)"
  where
    "constants_vdecls  = []"
lemma globals_max_aux:
shows "(((map fst (append p_before_cfg_to_dag_prog.constants_vdecls p_before_cfg_to_dag_prog.globals_vdecls)) \<noteq> []) \<longrightarrow> ((Max (set (map fst (append p_before_cfg_to_dag_prog.constants_vdecls p_before_cfg_to_dag_prog.globals_vdecls)))) \<le> 1))"
unfolding p_before_cfg_to_dag_prog.constants_vdecls_def p_before_cfg_to_dag_prog.globals_vdecls_def
by simp

lemma globals_max:
shows "(\<forall> x. ((Set.member x (set (map fst (append p_before_cfg_to_dag_prog.constants_vdecls p_before_cfg_to_dag_prog.globals_vdecls)))) \<longrightarrow> (x \<le> 1)))"
using globals_max_aux helper_max
by blast

lemma locals_min_aux:
shows "(((map fst (append p_before_cfg_to_dag_prog.params_vdecls p_before_cfg_to_dag_prog.locals_vdecls)) \<noteq> []) \<longrightarrow> ((Min (set (map fst (append p_before_cfg_to_dag_prog.params_vdecls p_before_cfg_to_dag_prog.locals_vdecls)))) \<ge> 2))"
unfolding p_before_cfg_to_dag_prog.params_vdecls_def p_before_cfg_to_dag_prog.locals_vdecls_def
by simp

lemma locals_min:
shows "(\<forall> x. ((Set.member x (set (map fst (append p_before_cfg_to_dag_prog.params_vdecls p_before_cfg_to_dag_prog.locals_vdecls)))) \<longrightarrow> (x \<ge> 2)))"
using locals_min_aux helper_min
by blast

lemma globals_locals_disj:
shows "((Set.inter (set (map fst (append p_before_cfg_to_dag_prog.constants_vdecls p_before_cfg_to_dag_prog.globals_vdecls))) (set (map fst (append p_before_cfg_to_dag_prog.params_vdecls p_before_cfg_to_dag_prog.locals_vdecls)))) = {})"
using p_before_cfg_to_dag_prog.locals_min p_before_cfg_to_dag_prog.globals_max
by fastforce

lemma funcs_wf:
shows "((list_all (comp wf_fdecl snd) fdecls) )"
unfolding fdecls_def
by simp

lemma consts_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) p_before_cfg_to_dag_prog.constants_vdecls) )"
unfolding p_before_cfg_to_dag_prog.constants_vdecls_def
by simp

lemma globals_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) p_before_cfg_to_dag_prog.globals_vdecls) )"
unfolding p_before_cfg_to_dag_prog.globals_vdecls_def
by simp

lemma params_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) p_before_cfg_to_dag_prog.params_vdecls) )"
unfolding p_before_cfg_to_dag_prog.params_vdecls_def
by simp

lemma locals_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) p_before_cfg_to_dag_prog.locals_vdecls) )"
unfolding p_before_cfg_to_dag_prog.locals_vdecls_def
by simp

lemma var_context_wf:
shows "(\<forall> x \<tau>. (((lookup_var_ty ((append p_before_cfg_to_dag_prog.constants_vdecls p_before_cfg_to_dag_prog.globals_vdecls),(append p_before_cfg_to_dag_prog.params_vdecls p_before_cfg_to_dag_prog.locals_vdecls)) x) = (Some \<tau>)) \<longrightarrow> ((wf_ty 0) \<tau>)))"
apply (rule lookup_ty_pred_2)
by ((simp_all add:consts_wf globals_wf params_wf locals_wf))

lemma m_x:
shows "((map_of (append p_before_cfg_to_dag_prog.params_vdecls p_before_cfg_to_dag_prog.locals_vdecls) 2) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma mfun_f:
shows "((map_of fdecls ''f'') = (Some (0,[(TPrim TInt)],(TPrim TBool))))"
by (simp add:fdecls_def)

lemma mfun_g:
shows "((map_of fdecls ''g'') = (Some (0,[(TPrim TBool)],(TPrim TBool))))"
by (simp add:fdecls_def)

lemma m_a:
shows "((map_of (append p_before_cfg_to_dag_prog.constants_vdecls p_before_cfg_to_dag_prog.globals_vdecls) 0) = (Some ((TPrim TInt),(None ))))"
by (simp add:p_before_cfg_to_dag_prog.constants_vdecls_def p_before_cfg_to_dag_prog.globals_vdecls_def)

lemma m_b:
shows "((map_of (append p_before_cfg_to_dag_prog.constants_vdecls p_before_cfg_to_dag_prog.globals_vdecls) 1) = (Some ((TPrim TBool),(None ))))"
by (simp add:p_before_cfg_to_dag_prog.constants_vdecls_def p_before_cfg_to_dag_prog.globals_vdecls_def)

lemma l_x:
shows "((lookup_var_decl ((append p_before_cfg_to_dag_prog.constants_vdecls p_before_cfg_to_dag_prog.globals_vdecls),(append p_before_cfg_to_dag_prog.params_vdecls p_before_cfg_to_dag_prog.locals_vdecls)) 2) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append p_before_cfg_to_dag_prog.constants_vdecls p_before_cfg_to_dag_prog.globals_vdecls),(append p_before_cfg_to_dag_prog.params_vdecls p_before_cfg_to_dag_prog.locals_vdecls)) 2) = (Some (TPrim TInt)))"
using globals_locals_disj m_x
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_a:
shows "((lookup_var_decl ((append p_before_cfg_to_dag_prog.constants_vdecls p_before_cfg_to_dag_prog.globals_vdecls),(append p_before_cfg_to_dag_prog.params_vdecls p_before_cfg_to_dag_prog.locals_vdecls)) 0) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append p_before_cfg_to_dag_prog.constants_vdecls p_before_cfg_to_dag_prog.globals_vdecls),(append p_before_cfg_to_dag_prog.params_vdecls p_before_cfg_to_dag_prog.locals_vdecls)) 0) = (Some (TPrim TInt)))"
using globals_locals_disj m_a
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_b:
shows "((lookup_var_decl ((append p_before_cfg_to_dag_prog.constants_vdecls p_before_cfg_to_dag_prog.globals_vdecls),(append p_before_cfg_to_dag_prog.params_vdecls p_before_cfg_to_dag_prog.locals_vdecls)) 1) = (Some ((TPrim TBool),(None ))))" and "((lookup_var_ty ((append p_before_cfg_to_dag_prog.constants_vdecls p_before_cfg_to_dag_prog.globals_vdecls),(append p_before_cfg_to_dag_prog.params_vdecls p_before_cfg_to_dag_prog.locals_vdecls)) 1) = (Some (TPrim TBool)))"
using globals_locals_disj m_b
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

definition proc :: "(mbodyCFG procedure)"
  where
    "proc  = (|proc_ty_args = 0,proc_args = p_before_cfg_to_dag_prog.params_vdecls,proc_rets = [],proc_modifs = [],proc_pres = (exprs_to_only_checked_spec p_before_cfg_to_dag_prog.pres),proc_posts = (exprs_to_only_checked_spec p_before_cfg_to_dag_prog.post),proc_body = (Some (p_before_cfg_to_dag_prog.locals_vdecls,p_before_cfg_to_dag_prog.proc_body))|)"

end
