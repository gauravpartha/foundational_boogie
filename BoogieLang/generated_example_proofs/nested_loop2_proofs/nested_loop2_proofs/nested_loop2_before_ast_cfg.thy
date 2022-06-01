theory nested_loop2_before_ast_cfg
  imports
    Boogie_Lang.Ast
    Boogie_Lang.Semantics 
    Boogie_Lang.TypeSafety 
    Boogie_Lang.Util 
    "../global_data"
begin

definition bigblock0 
  where "bigblock0 \<equiv> BigBlock None [(Assign 0 (Lit (LInt 10))),(Assign 1 (Lit (LInt 10)))]
                     (Some (WhileWrapper 
                           (ParsedWhile (Some ((Lit (LBool True))))
                            []
                            [(BigBlock None []
                             (Some (WhileWrapper 
                                   (ParsedWhile (Some (BinOp (Var 0) Gt (Lit (LInt 0)))) 
                                   [(BinOp (Var 0) Ge (Lit (LInt 0)))]
                                   [(BigBlock None [] 
                                    (Some (WhileWrapper 
                                         (ParsedWhile (Some (BinOp (Var 1) Gt (Lit (LInt 0))))
                                          [(BinOp (Var 1) Ge (Lit (LInt 0)))] 
                                          [BigBlock None [(Assign 1 (BinOp (Var 1) Sub (Lit (LInt 1))))] None None]))) 
                                     None),
                                   (BigBlock None [(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1))))] None None)]))) 
                              None)])))
                       None"

definition proc_body
  where
    "proc_body = bigblock0 # []"


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
lemma locals_min_aux:
shows "(((map fst (append nested_loop2_before_ast_cfg.params_vdecls nested_loop2_before_ast_cfg.locals_vdecls)) \<noteq> []) \<longrightarrow> ((Min (set (map fst (append nested_loop2_before_ast_cfg.params_vdecls nested_loop2_before_ast_cfg.locals_vdecls)))) \<ge> 0))"
unfolding nested_loop2_before_ast_cfg.params_vdecls_def nested_loop2_before_ast_cfg.locals_vdecls_def
by simp

lemma locals_min:
shows "(\<forall> x. ((Set.member x (set (map fst (append nested_loop2_before_ast_cfg.params_vdecls nested_loop2_before_ast_cfg.locals_vdecls)))) \<longrightarrow> (x \<ge> 0)))"
using locals_min_aux helper_min
by blast

lemma globals_locals_disj:
shows "((Set.inter (set (map fst (append global_data.constants_vdecls global_data.globals_vdecls))) (set (map fst (append nested_loop2_before_ast_cfg.params_vdecls nested_loop2_before_ast_cfg.locals_vdecls)))) = {})"
unfolding global_data.constants_vdecls_def global_data.globals_vdecls_def
by simp

lemma consts_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) global_data.constants_vdecls) )"
unfolding global_data.constants_vdecls_def
by simp

lemma globals_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) global_data.globals_vdecls) )"
unfolding global_data.globals_vdecls_def
by simp

lemma params_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) nested_loop2_before_ast_cfg.params_vdecls) )"
unfolding nested_loop2_before_ast_cfg.params_vdecls_def
by simp

lemma locals_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) nested_loop2_before_ast_cfg.locals_vdecls) )"
unfolding nested_loop2_before_ast_cfg.locals_vdecls_def
by simp

lemma var_context_wf:
shows "(\<forall> x \<tau>. (((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append nested_loop2_before_ast_cfg.params_vdecls nested_loop2_before_ast_cfg.locals_vdecls)) x) = (Some \<tau>)) \<longrightarrow> ((wf_ty 0) \<tau>)))"
apply (rule lookup_ty_pred_2)
by ((simp_all add:consts_wf globals_wf params_wf locals_wf))

lemma m_x:
shows "((map_of (append nested_loop2_before_ast_cfg.params_vdecls nested_loop2_before_ast_cfg.locals_vdecls) 0) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma m_y:
shows "((map_of (append nested_loop2_before_ast_cfg.params_vdecls nested_loop2_before_ast_cfg.locals_vdecls) 1) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma l_x:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append nested_loop2_before_ast_cfg.params_vdecls nested_loop2_before_ast_cfg.locals_vdecls)) 0) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append nested_loop2_before_ast_cfg.params_vdecls nested_loop2_before_ast_cfg.locals_vdecls)) 0) = (Some (TPrim TInt)))"
using globals_locals_disj m_x
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

lemma l_y:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append nested_loop2_before_ast_cfg.params_vdecls nested_loop2_before_ast_cfg.locals_vdecls)) 1) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append nested_loop2_before_ast_cfg.params_vdecls nested_loop2_before_ast_cfg.locals_vdecls)) 1) = (Some (TPrim TInt)))"
using globals_locals_disj m_y
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

definition proc_ast :: "(ast_procedure)"
  where
    "proc_ast  = (|proc_ty_args = 0,proc_args = nested_loop2_before_ast_cfg.params_vdecls,proc_rets = [],proc_modifs = [],proc_pres = (exprs_to_only_checked_spec nested_loop2_before_ast_cfg.pres),proc_posts = (exprs_to_only_checked_spec nested_loop2_before_ast_cfg.post),proc_body = (Some (nested_loop2_before_ast_cfg.locals_vdecls,nested_loop2_before_ast_cfg.proc_body))|)"

end