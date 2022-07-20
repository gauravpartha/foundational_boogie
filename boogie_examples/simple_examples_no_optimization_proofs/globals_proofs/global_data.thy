theory global_data
imports Boogie_Lang.Semantics Boogie_Lang.TypeSafety Boogie_Lang.Util
begin
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
shows "(((map fst (append global_data.constants_vdecls global_data.globals_vdecls)) \<noteq> []) \<longrightarrow> ((Max (set (map fst (append global_data.constants_vdecls global_data.globals_vdecls)))) \<le> 1))"
unfolding global_data.constants_vdecls_def global_data.globals_vdecls_def
by simp

lemma globals_max:
shows "(\<forall> x. ((Set.member x (set (map fst (append global_data.constants_vdecls global_data.globals_vdecls)))) \<longrightarrow> (x \<le> 1)))"
using globals_max_aux helper_max
by blast

lemma funcs_wf:
shows "((list_all (comp wf_fdecl snd) fdecls) )"
unfolding fdecls_def
by simp

lemma mfun_f:
shows "((map_of fdecls ''f'') = (Some (0,[(TPrim TInt)],(TPrim TBool))))"
by (simp add:fdecls_def)

lemma mfun_g:
shows "((map_of fdecls ''g'') = (Some (0,[(TPrim TBool)],(TPrim TBool))))"
by (simp add:fdecls_def)

lemma m_a:
shows "((map_of (append global_data.constants_vdecls global_data.globals_vdecls) 0) = (Some ((TPrim TInt),(None ))))"
by (simp add:global_data.constants_vdecls_def global_data.globals_vdecls_def)

lemma m_b:
shows "((map_of (append global_data.constants_vdecls global_data.globals_vdecls) 1) = (Some ((TPrim TBool),(None ))))"
by (simp add:global_data.constants_vdecls_def global_data.globals_vdecls_def)


end
