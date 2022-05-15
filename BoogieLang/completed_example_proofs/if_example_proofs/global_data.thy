theory global_data
  imports "/home/alex/boogie_related/foundational_boogie/BoogieLang/Semantics" 
          "/home/alex/boogie_related/foundational_boogie/BoogieLang/TypeSafety" 
          "/home/alex/boogie_related/foundational_boogie/BoogieLang/Util" 
begin
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
shows "(((map fst (append global_data.constants_vdecls global_data.globals_vdecls)) \<noteq> []) \<longrightarrow> ((Max (set (map fst (append global_data.constants_vdecls global_data.globals_vdecls)))) \<le> 0))"
unfolding global_data.constants_vdecls_def global_data.globals_vdecls_def
by simp

lemma globals_max:
shows "(\<forall> x. ((Set.member x (set (map fst (append global_data.constants_vdecls global_data.globals_vdecls)))) \<longrightarrow> (x \<le> 0)))"
using globals_max_aux helper_max
by blast

lemma funcs_wf:
shows "((list_all (comp wf_fdecl snd) fdecls) )"
unfolding fdecls_def
by simp


end
