theory vc_sum
imports Semantics Util
begin
locale vc = 
fixes n :: "int" and i :: "int" and i_0 :: "int" and res_0 :: "int" and res_1 :: "int" and i_1 :: "int"
begin

definition vc_anon7_Then
  where
    "vc_anon7_Then  = True"
definition vc_anon8_Then
  where
    "vc_anon8_Then  = True"
definition vc_anon9_Then
  where
    "vc_anon9_Then  = ((i_0 \<le> (n + (1::int))) \<longrightarrow> (((((res_0 * (2::int)) = ((i_0 - (1::int)) * i_0)) \<and> (i_0 \<le> n)) \<and> ((res_1 = (res_0 + i_0)) \<and> (i_1 = (i_0 + (1::int))))) \<longrightarrow> ((i_1 \<le> (n + (1::int))) \<and> ((i_1 \<le> (n + (1::int))) \<longrightarrow> ((res_1 * (2::int)) = ((i_1 - (1::int)) * i_1))))))"
definition vc_anon9_Else
  where
    "vc_anon9_Else  = ((\<not> (i_0 \<le> n)) \<longrightarrow> (((i_0 \<le> (n + (1::int))) \<and> ((res_0 * (2::int)) = ((i_0 - (1::int)) * i_0))) \<longrightarrow> ((res_0 * (2::int)) = (n * (n + (1::int))))))"
definition vc_anon7_Else
  where
    "vc_anon7_Else  = (((0::int) \<le> (n + (1::int))) \<and> (((0::int) \<le> (n + (1::int))) \<longrightarrow> ((((0::int) * (2::int)) = (((0::int) - (1::int)) * (0::int))) \<and> ((((0::int) * (2::int)) = (((0::int) - (1::int)) * (0::int))) \<longrightarrow> ((vc_anon8_Then \<and> vc_anon9_Then) \<and> vc_anon9_Else)))))"
definition vc_anon0
  where
    "vc_anon0  = (((0::int) \<le> n) \<longrightarrow> (vc_anon7_Then \<and> vc_anon7_Else))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry  = vc_anon0"
lemma vc_correct:

shows "vc_PreconditionGeneratedEntry"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def vc_anon7_Else_def vc_anon9_Else_def vc_anon9_Then_def vc_anon8_Then_def vc_anon7_Then_def)
  by (smt mult.commute semiring_normalization_rules(3))

end

lemma anon7_Then_correct:
assumes 
"(red_cmd_list \<Gamma> [(Assume (BinOp (BinOp (Var ''res'') Mul (Val (IntV 2))) Eq (BinOp (Var ''n'') Mul (BinOp (Var ''n'') Add (Val (IntV 1)))))), (Assume (Val (BoolV False)))] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"((n_s ''i_0'') = (Some (IntV vc_i_0)))" and 
"((n_s ''res_0'') = (Some (IntV vc_res_0)))" and 
"((n_s ''res_1'') = (Some (IntV vc_res_1)))" and 
"((n_s ''i_1'') = (Some (IntV vc_i_1)))" and 
"(vc.vc_anon7_Then )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms
apply cases
apply (simp only: vc.vc_anon7_Then_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma anon8_Then_correct:
assumes 
"(red_cmd_list \<Gamma> [(Assume (BinOp (Var ''i_0'') Le (BinOp (Var ''n'') Add (Val (IntV 1))))), (Assume (BinOp (BinOp (Var ''res_0'') Mul (Val (IntV 2))) Eq (BinOp (BinOp (Var ''i_0'') Sub (Val (IntV 1))) Mul (Var ''i_0'')))), (Assume (Val (BoolV False)))] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"((n_s ''i_0'') = (Some (IntV vc_i_0)))" and 
"((n_s ''res_0'') = (Some (IntV vc_res_0)))" and 
"((n_s ''res_1'') = (Some (IntV vc_res_1)))" and 
"((n_s ''i_1'') = (Some (IntV vc_i_1)))" and 
"(vc.vc_anon8_Then )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms
apply cases
apply (simp only: vc.vc_anon8_Then_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma anon9_Then_correct:
assumes 
"(red_cmd_list \<Gamma> [(Assume (BinOp (Var ''i_0'') Le (BinOp (Var ''n'') Add (Val (IntV 1))))), (Assume (BinOp (BinOp (Var ''res_0'') Mul (Val (IntV 2))) Eq (BinOp (BinOp (Var ''i_0'') Sub (Val (IntV 1))) Mul (Var ''i_0'')))), (Assume (BinOp (Var ''i_0'') Le (Var ''n''))), (Assume (BinOp (Var ''res_1'') Eq (BinOp (Var ''res_0'') Add (Var ''i_0'')))), (Assume (BinOp (Var ''i_1'') Eq (BinOp (Var ''i_0'') Add (Val (IntV 1))))), (Assert (BinOp (Var ''i_1'') Le (BinOp (Var ''n'') Add (Val (IntV 1))))), (Assert (BinOp (BinOp (Var ''res_1'') Mul (Val (IntV 2))) Eq (BinOp (BinOp (Var ''i_1'') Sub (Val (IntV 1))) Mul (Var ''i_1'')))), (Assume (Val (BoolV False)))] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"((n_s ''i_0'') = (Some (IntV vc_i_0)))" and 
"((n_s ''res_0'') = (Some (IntV vc_res_0)))" and 
"((n_s ''res_1'') = (Some (IntV vc_res_1)))" and 
"((n_s ''i_1'') = (Some (IntV vc_i_1)))" and 
"(vc.vc_anon9_Then vc_n vc_i_0 vc_res_0 vc_res_1 vc_i_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms
apply cases
apply (simp only: vc.vc_anon9_Then_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma anon9_Else_correct:
assumes 
"(red_cmd_list \<Gamma> [(Assume (UnOp Not (BinOp (Var ''i_0'') Le (Var ''n'')))), (Assume (BinOp (Var ''i_0'') Le (BinOp (Var ''n'') Add (Val (IntV 1))))), (Assume (BinOp (BinOp (Var ''res_0'') Mul (Val (IntV 2))) Eq (BinOp (BinOp (Var ''i_0'') Sub (Val (IntV 1))) Mul (Var ''i_0'')))), (Assert (BinOp (BinOp (Var ''res_0'') Mul (Val (IntV 2))) Eq (BinOp (Var ''n'') Mul (BinOp (Var ''n'') Add (Val (IntV 1))))))] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"((n_s ''i_0'') = (Some (IntV vc_i_0)))" and 
"((n_s ''res_0'') = (Some (IntV vc_res_0)))" and 
"((n_s ''res_1'') = (Some (IntV vc_res_1)))" and 
"((n_s ''i_1'') = (Some (IntV vc_i_1)))" and 
"(vc.vc_anon9_Else vc_n vc_i_0 vc_res_0)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms
apply cases
apply (simp only: vc.vc_anon9_Else_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma anon7_Else_correct:
assumes 
"(red_cmd_list \<Gamma> [(Assert (BinOp (Val (IntV 0)) Le (BinOp (Var ''n'') Add (Val (IntV 1))))), (Assert (BinOp (BinOp (Val (IntV 0)) Mul (Val (IntV 2))) Eq (BinOp (BinOp (Val (IntV 0)) Sub (Val (IntV 1))) Mul (Val (IntV 0)))))] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"((n_s ''i_0'') = (Some (IntV vc_i_0)))" and 
"((n_s ''res_0'') = (Some (IntV vc_res_0)))" and 
"((n_s ''res_1'') = (Some (IntV vc_res_1)))" and 
"((n_s ''i_1'') = (Some (IntV vc_i_1)))" and 
"(vc.vc_anon7_Else vc_n vc_i_0 vc_res_0 vc_res_1 vc_i_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (((vc.vc_anon8_Then ) \<and> (vc.vc_anon9_Then vc_n vc_i_0 vc_res_0 vc_res_1 vc_i_1)) \<and> (vc.vc_anon9_Else vc_n vc_i_0 vc_res_0))))))"
using assms
apply cases
apply (simp only: vc.vc_anon7_Else_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma anon0_correct:
assumes 
"(red_cmd_list \<Gamma> [(Assume (BinOp (Val (IntV 0)) Le (Var ''n'')))] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"((n_s ''i_0'') = (Some (IntV vc_i_0)))" and 
"((n_s ''res_0'') = (Some (IntV vc_res_0)))" and 
"((n_s ''res_1'') = (Some (IntV vc_res_1)))" and 
"((n_s ''i_1'') = (Some (IntV vc_i_1)))" and 
"(vc.vc_anon0 vc_n vc_i_0 vc_res_0 vc_res_1 vc_i_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon7_Then ) \<and> (vc.vc_anon7_Else vc_n vc_i_0 vc_res_0 vc_res_1 vc_i_1))))))"
using assms
apply cases
apply (simp only: vc.vc_anon0_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma PreconditionGeneratedEntry_correct:
assumes 
"(red_cmd_list \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"((n_s ''i_0'') = (Some (IntV vc_i_0)))" and 
"((n_s ''res_0'') = (Some (IntV vc_res_0)))" and 
"((n_s ''res_1'') = (Some (IntV vc_res_1)))" and 
"((n_s ''i_1'') = (Some (IntV vc_i_1)))" and 
"(vc.vc_PreconditionGeneratedEntry vc_n vc_i_0 vc_res_0 vc_res_1 vc_i_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 vc_n vc_i_0 vc_res_0 vc_res_1 vc_i_1)))))"
using assms
apply cases
apply (simp only: vc.vc_PreconditionGeneratedEntry_def)
apply (handle_cmd_list_full?)
by (auto?)


end
