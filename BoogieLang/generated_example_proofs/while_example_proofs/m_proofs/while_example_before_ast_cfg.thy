theory while_example_before_ast_cfg
  imports Main 
          "/home/alex/boogie_related/foundational_boogie/BoogieLang/Ast"
          "/home/alex/boogie_related/foundational_boogie/BoogieLang/Semantics"
          "/home/alex/boogie_related/foundational_boogie/BoogieLang/generated_example_proofs/while_example_proofs/global_data"

begin

definition bigblock0
  where "bigblock0 = 
          (BigBlock None [(Assign 0 (Lit (LInt 0))), (Assume (BinOp (Var 1) Gt (Lit (LInt 0))))] 
            (Some (ParsedWhile (Some (BinOp (Var 0) Lt (Var 1))) 
                      [(BinOp (Var 0) Le (Var 1))]
                      [BigBlock None [(Assign 0 (BinOp (Var 0) Add (Lit (LInt 1))))] None None])) 
             None)"

definition bigblock1
  where "bigblock1 = 
          (BigBlock None [(Assert (BinOp (Var 0) Ge (Var 1)))] None None)"

definition proc_body
  where
    "proc_body = bigblock0 #  bigblock1  # []"

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
shows "(((map fst (append while_example_before_ast_cfg.params_vdecls while_example_before_ast_cfg.locals_vdecls)) \<noteq> []) \<longrightarrow> ((Min (set (map fst (append while_example_before_ast_cfg.params_vdecls while_example_before_ast_cfg.locals_vdecls)))) \<ge> 0))"
unfolding while_example_before_ast_cfg.params_vdecls_def while_example_before_ast_cfg.locals_vdecls_def
by simp

lemma locals_min:
shows "(\<forall> x. ((Set.member x (set (map fst (append while_example_before_ast_cfg.params_vdecls while_example_before_ast_cfg.locals_vdecls)))) \<longrightarrow> (x \<ge> 0)))"
using locals_min_aux helper_min
by blast

lemma globals_locals_disj:
shows "((Set.inter (set (map fst (append global_data.constants_vdecls global_data.globals_vdecls))) (set (map fst (append while_example_before_ast_cfg.params_vdecls while_example_before_ast_cfg.locals_vdecls)))) = {})"
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
shows "((list_all (comp (wf_ty 0) (comp fst snd)) while_example_before_ast_cfg.params_vdecls) )"
unfolding while_example_before_ast_cfg.params_vdecls_def
by simp

lemma locals_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) while_example_before_ast_cfg.locals_vdecls) )"
unfolding while_example_before_ast_cfg.locals_vdecls_def
by simp

lemma var_context_wf:
shows "(\<forall> x \<tau>. (((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append while_example_before_ast_cfg.params_vdecls while_example_before_ast_cfg.locals_vdecls)) x) = (Some \<tau>)) \<longrightarrow> ((wf_ty 0) \<tau>)))"
apply (rule lookup_ty_pred_2)
by ((simp_all add:consts_wf globals_wf params_wf locals_wf))

lemma m_x:
shows "((map_of (append while_example_before_ast_cfg.params_vdecls while_example_before_ast_cfg.locals_vdecls) 0) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma l_x:
shows "((lookup_var_decl ((append global_data.constants_vdecls global_data.globals_vdecls),(append while_example_before_ast_cfg.params_vdecls while_example_before_ast_cfg.locals_vdecls)) 0) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append global_data.constants_vdecls global_data.globals_vdecls),(append while_example_before_ast_cfg.params_vdecls while_example_before_ast_cfg.locals_vdecls)) 0) = (Some (TPrim TInt)))"
using globals_locals_disj m_x
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

definition proc :: "ast_procedure"
  where
    "proc  = (|proc_ty_args = 0,proc_args = while_example_before_ast_cfg.params_vdecls,proc_rets = [],proc_modifs = [],proc_pres = (exprs_to_only_checked_spec while_example_before_ast_cfg.pres),proc_posts = (exprs_to_only_checked_spec while_example_before_ast_cfg.post),proc_body = (Some (while_example_before_ast_cfg.locals_vdecls,while_example_before_ast_cfg.proc_body))|)"
