theory infeasible_edge
imports Semantics Util
begin
locale vc = 
fixes x :: "int" and y_0 :: "int" and y_1 :: "int" and y_2 :: "int"
begin

definition vc_anon4_Then
  where
    "vc_anon4_Then  = True"
definition vc_anon4_Else
  where
    "vc_anon4_Else  = (((0::int) \<ge> x) \<longrightarrow> (((y_1 = (x + (2::int))) \<and> (y_2 = (y_1 + (3::int)))) \<longrightarrow> (y_2 = (x + (5::int)))))"
definition vc_anon0
  where
    "vc_anon0  = (vc_anon4_Then \<and> vc_anon4_Else)"
lemma vc_correct:

shows "vc_anon0"
apply (simp only: vc_anon0_def vc_anon4_Else_def vc_anon4_Then_def)
  by simp

end

locale passification = 
fixes n_s :: "((vname) => ((val)option))" and vc_x :: "int" and vc_y :: "int" and vc_y_0 :: "int" and vc_y_1 :: "int" and vc_y_2 :: "int"
assumes 
S0: "((n_s ''x'') = (Some (IntV vc_x)))" and 
S1: "((n_s ''y'') = (Some (IntV vc_y)))" and 
S2: "((n_s ''y_0'') = (Some (IntV vc_y_0)))" and 
S3: "((n_s ''y_1'') = (Some (IntV vc_y_1)))" and 
S4: "((n_s ''y_2'') = (Some (IntV vc_y_2)))"
begin

lemmas state_assms = S0 S1 S2 S3 S4
lemma block_anon4_Then:
assumes 
"(red_cmd_list \<Gamma> [(Assume (BinOp (Var ''x'') Gt (Val (IntV 0)))), (Assume (Val (BoolV False))), (Assume (BinOp (Var ''y_0'') Eq (BinOp (Var ''x'') Add (Val (IntV 1)))))] (Normal n_s) s')" and 
"(vc.vc_anon4_Then )"
shows "(s' = Magic)"
using assms state_assms
apply cases
apply (simp only: vc.vc_anon4_Then_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon4_Else:
assumes 
"(red_cmd_list \<Gamma> [(Assume (BinOp (Val (IntV 0)) Ge (Var ''x''))), (Assume (BinOp (Var ''y_1'') Eq (BinOp (Var ''x'') Add (Val (IntV 2))))), (Assume (BinOp (Var ''y_2'') Eq (BinOp (Var ''y_1'') Add (Val (IntV 3))))), (Assert (BinOp (Var ''y_2'') Eq (BinOp (Var ''x'') Add (Val (IntV 5)))))] (Normal n_s) s')" and 
"(vc.vc_anon4_Else vc_x vc_y_1 vc_y_2)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms state_assms
apply cases
apply (simp only: vc.vc_anon4_Else_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Gamma> [] (Normal n_s) s')" and 
"(vc.vc_anon0 vc_x vc_y_1 vc_y_2)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon4_Then ) \<and> (vc.vc_anon4_Else vc_x vc_y_1 vc_y_2))))))"
using assms state_assms
apply cases
apply (simp only: vc.vc_anon0_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_GeneratedUnifiedExit:
assumes 
"(red_cmd_list \<Gamma> [] (Normal n_s) s')"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms
apply cases
by auto

lemma block_anon0_0:
assumes 
"(red_cmd_list \<Gamma> [] (Normal n_s) s')" and 
"((vc.vc_anon4_Then ) \<and> (vc.vc_anon4_Else vc_x vc_y_1 vc_y_2))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon4_Then ) \<and> (vc.vc_anon4_Else vc_x vc_y_1 vc_y_2))))))"
using assms
apply cases
by auto

lemma block_0:
assumes 
"(red_cmd_list \<Gamma> [] (Normal n_s) s')" and 
"((vc.vc_anon4_Then ) \<and> (vc.vc_anon4_Else vc_x vc_y_1 vc_y_2))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon4_Then ) \<and> (vc.vc_anon4_Else vc_x vc_y_1 vc_y_2))))))"
using assms
apply cases
by auto

end


end
