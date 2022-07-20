theory trivial_assume_false_before_cfg_to_dag_prog
imports Boogie_Lang.Semantics Boogie_Lang.TypeSafety Boogie_Lang.Util "../global_data"
begin
definition block_0
  where
    "block_0  = [(Assume (Lit (LBool False)))]"
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
    "params_vdecls  = []"
definition locals_vdecls :: "(vdecls)"
  where
    "locals_vdecls  = []"
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
shows "(((map fst (append trivial_assume_false_before_cfg_to_dag_prog.constants_vdecls trivial_assume_false_before_cfg_to_dag_prog.globals_vdecls)) \<noteq> []) \<longrightarrow> ((Max (set (map fst (append trivial_assume_false_before_cfg_to_dag_prog.constants_vdecls trivial_assume_false_before_cfg_to_dag_prog.globals_vdecls)))) \<le> 0))"
unfolding trivial_assume_false_before_cfg_to_dag_prog.constants_vdecls_def trivial_assume_false_before_cfg_to_dag_prog.globals_vdecls_def
by simp

lemma globals_max:
shows "(\<forall> x. ((Set.member x (set (map fst (append trivial_assume_false_before_cfg_to_dag_prog.constants_vdecls trivial_assume_false_before_cfg_to_dag_prog.globals_vdecls)))) \<longrightarrow> (x \<le> 0)))"
using globals_max_aux helper_max
by blast

lemma locals_min_aux:
shows "(((map fst (append trivial_assume_false_before_cfg_to_dag_prog.params_vdecls trivial_assume_false_before_cfg_to_dag_prog.locals_vdecls)) \<noteq> []) \<longrightarrow> ((Min (set (map fst (append trivial_assume_false_before_cfg_to_dag_prog.params_vdecls trivial_assume_false_before_cfg_to_dag_prog.locals_vdecls)))) \<ge> 0))"
unfolding trivial_assume_false_before_cfg_to_dag_prog.params_vdecls_def trivial_assume_false_before_cfg_to_dag_prog.locals_vdecls_def
by simp

lemma locals_min:
shows "(\<forall> x. ((Set.member x (set (map fst (append trivial_assume_false_before_cfg_to_dag_prog.params_vdecls trivial_assume_false_before_cfg_to_dag_prog.locals_vdecls)))) \<longrightarrow> (x \<ge> 0)))"
using locals_min_aux helper_min
by blast

lemma globals_locals_disj:
shows "((Set.inter (set (map fst (append trivial_assume_false_before_cfg_to_dag_prog.constants_vdecls trivial_assume_false_before_cfg_to_dag_prog.globals_vdecls))) (set (map fst (append trivial_assume_false_before_cfg_to_dag_prog.params_vdecls trivial_assume_false_before_cfg_to_dag_prog.locals_vdecls)))) = {})"
unfolding trivial_assume_false_before_cfg_to_dag_prog.constants_vdecls_def trivial_assume_false_before_cfg_to_dag_prog.globals_vdecls_def
by simp

lemma funcs_wf:
shows "((list_all (comp wf_fdecl snd) fdecls) )"
unfolding fdecls_def
by simp

lemma consts_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) trivial_assume_false_before_cfg_to_dag_prog.constants_vdecls) )"
unfolding trivial_assume_false_before_cfg_to_dag_prog.constants_vdecls_def
by simp

lemma globals_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) trivial_assume_false_before_cfg_to_dag_prog.globals_vdecls) )"
unfolding trivial_assume_false_before_cfg_to_dag_prog.globals_vdecls_def
by simp

lemma params_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) trivial_assume_false_before_cfg_to_dag_prog.params_vdecls) )"
unfolding trivial_assume_false_before_cfg_to_dag_prog.params_vdecls_def
by simp

lemma locals_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) trivial_assume_false_before_cfg_to_dag_prog.locals_vdecls) )"
unfolding trivial_assume_false_before_cfg_to_dag_prog.locals_vdecls_def
by simp

lemma var_context_wf:
shows "(\<forall> x \<tau>. (((lookup_var_ty ((append trivial_assume_false_before_cfg_to_dag_prog.constants_vdecls trivial_assume_false_before_cfg_to_dag_prog.globals_vdecls),(append trivial_assume_false_before_cfg_to_dag_prog.params_vdecls trivial_assume_false_before_cfg_to_dag_prog.locals_vdecls)) x) = (Some \<tau>)) \<longrightarrow> ((wf_ty 0) \<tau>)))"
apply (rule lookup_ty_pred_2)
by ((simp_all add:consts_wf globals_wf params_wf locals_wf))

definition proc :: "(mbodyCFG procedure)"
  where
    "proc  = (|proc_ty_args = 0,proc_args = trivial_assume_false_before_cfg_to_dag_prog.params_vdecls,proc_rets = [],proc_modifs = [],proc_pres = (exprs_to_only_checked_spec trivial_assume_false_before_cfg_to_dag_prog.pres),proc_posts = (exprs_to_only_checked_spec trivial_assume_false_before_cfg_to_dag_prog.post),proc_body = (Some (trivial_assume_false_before_cfg_to_dag_prog.locals_vdecls,trivial_assume_false_before_cfg_to_dag_prog.proc_body))|)"

end
