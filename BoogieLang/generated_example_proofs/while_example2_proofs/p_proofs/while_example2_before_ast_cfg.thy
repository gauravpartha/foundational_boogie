theory while_example2_before_ast_cfg
  imports Main 
          "Boogie_Lang.Ast"
          "Boogie_Lang.Semantics"
          "../global_data"

begin

definition bigblock0
  where "bigblock0 \<equiv> 
          (BigBlock None [(Havoc 0)] 
            (Some (WhileWrapper 
                  (ParsedWhile (Some (BinOp (Var 0) Gt (Lit (LInt 0)))) 
                  [(BinOp (Var 0) Ge (Lit (LInt 0)))]
                  [BigBlock None [(Assign 0 (BinOp (Var 0) Sub (Lit (LInt 1))))] None None]))) 
             None)"

definition bigblock1
  where "bigblock1 \<equiv> 
          (BigBlock None [] 
            (Some (WhileWrapper (ParsedWhile (Some (BinOp (Var 0) Lt (Lit (LInt 0)))) 
                      [(BinOp (Var 0) Le (Lit (LInt 0)))]
                      [BigBlock None [(Assign 0 (BinOp (Var 0) Add (Lit (LInt 1))))] None None]))) 
             None)"

definition bigblock2
  where "bigblock2 \<equiv> 
          (BigBlock None [(Assert (BinOp (Var 0) Eq (Lit (LInt 0))))] None None)"

definition proc_body
  where
    "proc_body = bigblock0 #  bigblock1 # bigblock2 # []"

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
    "locals_vdecls  = [(0,(TPrim TInt),None)]"

lemma locals_min_aux:
shows "(((map fst (append while_example2_before_ast_cfg.params_vdecls while_example2_before_ast_cfg.locals_vdecls)) \<noteq> []) \<longrightarrow> ((Min (set (map fst (append while_example2_before_ast_cfg.params_vdecls while_example2_before_ast_cfg.locals_vdecls)))) \<ge> 0))"
unfolding while_example2_before_ast_cfg.params_vdecls_def while_example2_before_ast_cfg.locals_vdecls_def
by simp

lemma locals_min:
shows "(\<forall> x. ((Set.member x (set (map fst (append while_example2_before_ast_cfg.params_vdecls while_example2_before_ast_cfg.locals_vdecls)))) \<longrightarrow> (x \<ge> 0)))"
using locals_min_aux helper_min
by blast

lemma globals_locals_disj:
shows "((Set.inter (set (map fst (append global_data.constants_vdecls global_data.globals_vdecls))) (set (map fst (append while_example2_before_ast_cfg.params_vdecls while_example2_before_ast_cfg.locals_vdecls)))) = {})"
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
shows "((list_all (comp (wf_ty 0) (comp fst snd)) while_example2_before_ast_cfg.params_vdecls) )"
unfolding while_example2_before_ast_cfg.params_vdecls_def
by simp

lemma locals_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) while_example2_before_ast_cfg.locals_vdecls) )"
unfolding while_example2_before_ast_cfg.locals_vdecls_def
by simp

lemma var_context_wf:
shows "(\<forall> x \<tau>. (((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append while_example2_before_ast_cfg.params_vdecls while_example2_before_ast_cfg.locals_vdecls)) x) = (Some \<tau>)) \<longrightarrow> ((wf_ty 0) \<tau>)))"
apply (rule lookup_ty_pred_2)
by ((simp_all add:consts_wf globals_wf params_wf locals_wf))

lemma m_x:
shows "((map_of (append while_example2_before_ast_cfg.params_vdecls while_example2_before_ast_cfg.locals_vdecls) 0) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma l_x:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append while_example2_before_ast_cfg.params_vdecls while_example2_before_ast_cfg.locals_vdecls)) 0) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append while_example2_before_ast_cfg.params_vdecls while_example2_before_ast_cfg.locals_vdecls)) 0) = (Some (TPrim TInt)))"
using globals_locals_disj m_x
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

definition proc_ast :: "ast_procedure"
  where
    "proc_ast  = (|proc_ty_args = 0,proc_args = while_example2_before_ast_cfg.params_vdecls,proc_rets = [],proc_modifs = [],proc_pres = (exprs_to_only_checked_spec while_example2_before_ast_cfg.pres),proc_posts = (exprs_to_only_checked_spec while_example2_before_ast_cfg.post),proc_body = (Some (while_example2_before_ast_cfg.locals_vdecls,while_example2_before_ast_cfg.proc_body))|)"



end