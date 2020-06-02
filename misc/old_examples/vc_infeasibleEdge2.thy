theory vc_infeasibleEdge2
imports Semantics Util
begin
locale vc = 
fixes x :: "int" and y_0 :: "int" and y_1 :: "int"
begin

definition vc_anon0
  where
    "vc_anon0  = True"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry  = vc_anon0"
lemma vc_correct:

shows "vc_PreconditionGeneratedEntry"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def)
oops


end

lemma anon0_correct:
assumes 
"(red_cmd_list \<Gamma> [(Assume (Val (BoolV False)))] (Normal n_s) s')"
shows "(s' = Magic)"
using assms
apply cases
apply (handle_cmd_list_full?)
  by (auto?)

lemma anon0_correct:
assumes 
"(red_cmd_list \<Gamma> [(Assume (Val (BoolV False))), (Assume (BinOp (Var ''y_0'') Eq (BinOp (Var ''x'') Add (Val (IntV 1))))), (Assume (BinOp (Var ''y_1'') Eq (BinOp (Var ''y_0'') Add (Val (IntV 2))))), (Assert (BinOp (Var ''y_1'') Lt (Var ''x'')))] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''y_0'') = (Some (IntV vc_y_0)))" and 
"((n_s ''y_1'') = (Some (IntV vc_y_1)))" and 
"(vc.vc_anon0 )"
shows "(s' = Magic)"
using assms
apply cases
apply (simp only: vc.vc_anon0_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma PreconditionGeneratedEntry_correct:
assumes 
"(red_cmd_list \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''y_0'') = (Some (IntV vc_y_0)))" and 
"((n_s ''y_1'') = (Some (IntV vc_y_1)))" and 
"(vc.vc_PreconditionGeneratedEntry )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 )))))"
using assms
apply cases
apply (simp only: vc.vc_PreconditionGeneratedEntry_def)
apply (handle_cmd_list_full?)
by (auto?)


end
