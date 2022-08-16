theory p_before_ast_to_cfg_prog
imports Boogie_Lang.Ast Boogie_Lang.Semantics Boogie_Lang.TypeSafety Boogie_Lang.Util "../global_data"
begin
definition bigblock_0
  where
    "bigblock_0  = (BigBlock (None ) [(Assign 0 (Lit (LInt 0)))] (Some (WhileWrapper (ParsedWhile (Some (BinOp (Var 0) Gt (Lit (LInt 0)))) [(BinOp (Var 0) Ge (Lit (LInt 0)))] [(BigBlock (None ) [] (None ) (None ))]))) (None ))"
definition bigblock_1
  where
    "bigblock_1  = (BigBlock (None ) [] (Some (ParsedWhile (Some (BinOp (Var 0) Gt (Lit (LInt 0)))) [(BinOp (Var 0) Ge (Lit (LInt 0)))] [(BigBlock (None ) [] (None ) (None ))])) (None ))"
definition bigblock_2
  where
    "bigblock_2  = (BigBlock (None ) [] (None ) (None ))"
definition bigblock_3
  where
    "bigblock_3  = (BigBlock (None ) [(Assert (BinOp (Var 0) Eq (Lit (LInt 0))))] (None ) (None ))"
definition cont_3
  where
    "cont_3  = KStop"
definition cont_0
  where
    "cont_0  = (KSeq bigblock_3 cont_3)"
definition cont_1
  where
    "cont_1  = (KEndBlock (KSeq bigblock_3 cont_3 ))"
definition cont_2
  where
    "cont_2  = (KSeq bigblock_1 cont_1)"
definition proc_body
  where
    "proc_body  = [bigblock_0,bigblock_3]"
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
    "locals_vdecls  = [(0,(TPrim TInt),(None ))]"
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
shows "(((map fst (append p_before_ast_to_cfg_prog.constants_vdecls p_before_ast_to_cfg_prog.globals_vdecls)) \<noteq> []) \<longrightarrow> ((Max (set (map fst (append p_before_ast_to_cfg_prog.constants_vdecls p_before_ast_to_cfg_prog.globals_vdecls)))) \<le> 0))"
unfolding p_before_ast_to_cfg_prog.constants_vdecls_def p_before_ast_to_cfg_prog.globals_vdecls_def
by simp

lemma globals_max:
shows "(\<forall> x. ((Set.member x (set (map fst (append p_before_ast_to_cfg_prog.constants_vdecls p_before_ast_to_cfg_prog.globals_vdecls)))) \<longrightarrow> (x \<le> 0)))"
using globals_max_aux helper_max
by blast

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

lemma funcs_wf:
shows "((list_all (comp wf_fdecl snd) fdecls) )"
unfolding fdecls_def
by simp

lemma consts_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) p_before_ast_to_cfg_prog.constants_vdecls) )"
unfolding p_before_ast_to_cfg_prog.constants_vdecls_def
by simp

lemma globals_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) p_before_ast_to_cfg_prog.globals_vdecls) )"
unfolding p_before_ast_to_cfg_prog.globals_vdecls_def
by simp

lemma params_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) p_before_ast_to_cfg_prog.params_vdecls) )"
unfolding p_before_ast_to_cfg_prog.params_vdecls_def
by simp

lemma locals_wf:
shows "((list_all (comp (wf_ty 0) (comp fst snd)) p_before_ast_to_cfg_prog.locals_vdecls) )"
unfolding p_before_ast_to_cfg_prog.locals_vdecls_def
by simp

lemma var_context_wf:
shows "(\<forall> x \<tau>. (((lookup_var_ty ((append p_before_ast_to_cfg_prog.constants_vdecls p_before_ast_to_cfg_prog.globals_vdecls),(append p_before_ast_to_cfg_prog.params_vdecls p_before_ast_to_cfg_prog.locals_vdecls)) x) = (Some \<tau>)) \<longrightarrow> ((wf_ty 0) \<tau>)))"
apply (rule lookup_ty_pred_2)
by ((simp_all add:consts_wf globals_wf params_wf locals_wf))

lemma m_x:
shows "((map_of (append p_before_ast_to_cfg_prog.params_vdecls p_before_ast_to_cfg_prog.locals_vdecls) 0) = (Some ((TPrim TInt),(None ))))"
by (simp add:params_vdecls_def locals_vdecls_def)

lemma l_x:
shows "((lookup_var_decl ((append p_before_ast_to_cfg_prog.constants_vdecls p_before_ast_to_cfg_prog.globals_vdecls),(append p_before_ast_to_cfg_prog.params_vdecls p_before_ast_to_cfg_prog.locals_vdecls)) 0) = (Some ((TPrim TInt),(None ))))" and "((lookup_var_ty ((append p_before_ast_to_cfg_prog.constants_vdecls p_before_ast_to_cfg_prog.globals_vdecls),(append p_before_ast_to_cfg_prog.params_vdecls p_before_ast_to_cfg_prog.locals_vdecls)) 0) = (Some (TPrim TInt)))"
using globals_locals_disj m_x
by (simp_all add: lookup_var_decl_global_2 lookup_var_decl_local lookup_var_decl_ty_Some)

definition ast_proc :: "(ast procedure)"
  where
    "ast_proc  = (|proc_ty_args = 0,proc_args = p_before_ast_to_cfg_prog.params_vdecls,proc_rets = [],proc_modifs = [],proc_pres = (exprs_to_only_checked_spec p_before_ast_to_cfg_prog.pres),proc_posts = (exprs_to_only_checked_spec p_before_ast_to_cfg_prog.post),proc_body = (Some (p_before_ast_to_cfg_prog.locals_vdecls,p_before_ast_to_cfg_prog.proc_body))|)"

end
