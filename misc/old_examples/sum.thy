theory sum
imports Semantics Util
begin
locale vc
begin

definition vc_anon7_Then
  where
    "vc_anon7_Then  = True"
definition vc_anon8_Then
  where
    "vc_anon8_Then  = True"
definition vc_anon9_Then
  where
    "vc_anon9_Then i_0 n res_0 res_1 i_1 = ((i_0 \<le> (n + (1::int))) \<longrightarrow> (((((res_0 * (2::int)) = ((i_0 - (1::int)) * i_0)) \<and> (i_0 \<le> n)) \<and> ((res_1 = (res_0 + i_0)) \<and> (i_1 = (i_0 + (1::int))))) \<longrightarrow> ((i_1 \<le> (n + (1::int))) \<and> ((i_1 \<le> (n + (1::int))) \<longrightarrow> ((res_1 * (2::int)) = ((i_1 - (1::int)) * i_1))))))"
definition vc_anon9_Else
  where
    "vc_anon9_Else i_0 n res_0 = ((\<not> (i_0 \<le> n)) \<longrightarrow> (((i_0 \<le> (n + (1::int))) \<and> ((res_0 * (2::int)) = ((i_0 - (1::int)) * i_0))) \<longrightarrow> ((res_0 * (2::int)) = (n * (n + (1::int))))))"
definition vc_anon7_Else
  where
    "vc_anon7_Else n i_0 res_0 res_1 i_1 = (((0::int) \<le> (n + (1::int))) \<and> (((0::int) \<le> (n + (1::int))) \<longrightarrow> ((((0::int) * (2::int)) = (((0::int) - (1::int)) * (0::int))) \<and> ((((0::int) * (2::int)) = (((0::int) - (1::int)) * (0::int))) \<longrightarrow> (((vc_anon8_Then ) \<and> (vc_anon9_Then i_0 n res_0 res_1 i_1)) \<and> (vc_anon9_Else i_0 n res_0))))))"
definition vc_anon0
  where
    "vc_anon0 n i_0 res_0 res_1 i_1 = (((0::int) \<le> n) \<longrightarrow> ((vc_anon7_Then ) \<and> (vc_anon7_Else n i_0 res_0 res_1 i_1)))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry n i_0 res_0 res_1 i_1 = (vc_anon0 n i_0 res_0 res_1 i_1)"
lemma vc_correct:

shows "(vc_PreconditionGeneratedEntry n i_0 res_0 res_1 i_1)"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def vc_anon7_Else_def vc_anon9_Else_def vc_anon9_Then_def vc_anon8_Then_def vc_anon7_Then_def)
oops


end

locale vc_passive
begin

definition vc_anon7_Then
  where
    "vc_anon7_Then  = True"
definition vc_anon8_Then
  where
    "vc_anon8_Then  = True"
definition vc_anon9_Then
  where
    "vc_anon9_Then n = (\<forall> i_0 res_0 res_1 i_1. ((i_0 \<le> (n + (1::int))) \<longrightarrow> (((((res_0 * (2::int)) = ((i_0 - (1::int)) * i_0)) \<and> (i_0 \<le> n)) \<and> ((res_1 = (res_0 + i_0)) \<and> (i_1 = (i_0 + (1::int))))) \<longrightarrow> ((i_1 \<le> (n + (1::int))) \<and> ((i_1 \<le> (n + (1::int))) \<longrightarrow> ((res_1 * (2::int)) = ((i_1 - (1::int)) * i_1)))))))"
definition vc_anon9_Else
  where
    "vc_anon9_Else n = (\<forall> i_0 res_0. ((\<not> (i_0 \<le> n)) \<longrightarrow> (((i_0 \<le> (n + (1::int))) \<and> ((res_0 * (2::int)) = ((i_0 - (1::int)) * i_0))) \<longrightarrow> ((res_0 * (2::int)) = (n * (n + (1::int)))))))"
definition vc_anon7_Else
  where
    "vc_anon7_Else n = (((0::int) \<le> (n + (1::int))) \<and> (((0::int) \<le> (n + (1::int))) \<longrightarrow> ((((0::int) * (2::int)) = (((0::int) - (1::int)) * (0::int))) \<and> ((((0::int) * (2::int)) = (((0::int) - (1::int)) * (0::int))) \<longrightarrow> (((vc_anon8_Then ) \<and> (vc_anon9_Then n)) \<and> (vc_anon9_Else n))))))"
definition vc_anon0
  where
    "vc_anon0  = (\<forall> n. (((0::int) \<le> n) \<longrightarrow> ((vc_anon7_Then ) \<and> (vc_anon7_Else n))))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry  = (vc_anon0 )"
lemma vc_correct:

shows "(vc_PreconditionGeneratedEntry )"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def vc_anon7_Else_def vc_anon9_Else_def vc_anon9_Then_def vc_anon8_Then_def vc_anon7_Then_def)
oops


end

locale beforePassive = 
fixes \<Lambda> :: "(var_context)" and \<Gamma> :: "(fun_context)"
assumes 
V0: "((\<Lambda> ''i'') = (Some TInt))" and 
V1: "((\<Lambda> ''res'') = (Some TInt))" and 
V2: "((\<Lambda> ''n'') = (Some TInt))"
begin

lemmas var_assms = V0 V1 V2
lemma block_GeneratedUnifiedExit:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')"
shows "(s' \<noteq> Failure)"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon7_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (BinOp (Var ''res'') Mul (Val (IntV 2))) Eq (BinOp (Var ''n'') Mul (BinOp (Var ''n'') Add (Val (IntV 1)))))), 
(Assume (Val (BoolV False)))] (Normal n_s) s')" and 
"((n_s ''res'') = (Some (IntV vc_res)))" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"(vc_passive.vc_anon7_Then )"
shows "(s' = Magic)"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon7_Then_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon8_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''i'') Le (BinOp (Var ''n'') Add (Val (IntV 1))))), 
(Assume (BinOp (BinOp (Var ''res'') Mul (Val (IntV 2))) Eq (BinOp (BinOp (Var ''i'') Sub (Val (IntV 1))) Mul (Var ''i'')))), 
(Assume (Val (BoolV False)))] (Normal n_s) s')" and 
"((n_s ''res'') = (Some (IntV vc_res)))" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"(vc_passive.vc_anon8_Then )"
shows "(s' = Magic)"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon8_Then_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon9_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''i'') Le (BinOp (Var ''n'') Add (Val (IntV 1))))), 
(Assume (BinOp (BinOp (Var ''res'') Mul (Val (IntV 2))) Eq (BinOp (BinOp (Var ''i'') Sub (Val (IntV 1))) Mul (Var ''i'')))), 
(Assume (BinOp (Var ''i'') Le (Var ''n''))), 
(Assign [(''res'', (BinOp (Var ''res'') Add (Var ''i'')))]), 
(Assign [(''i'', (BinOp (Var ''i'') Add (Val (IntV 1))))]), 
(Assert (BinOp (Var ''i'') Le (BinOp (Var ''n'') Add (Val (IntV 1))))), 
(Assert (BinOp (BinOp (Var ''res'') Mul (Val (IntV 2))) Eq (BinOp (BinOp (Var ''i'') Sub (Val (IntV 1))) Mul (Var ''i'')))), 
(Assume (Val (BoolV False)))] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''res'') = (Some (IntV vc_res)))" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
(*"(\<forall> i_0 res_0 res_1 i_1. ((i_0 \<le> (n + (1::int))) \<longrightarrow>
 (((((res_0 * (2::int)) = ((i_0 - (1::int)) * i_0)) \<and> (i_0 \<le> n)) \<and> ((res_1 = (res_0 + i_0)) \<and> (i_1 = (i_0 + (1::int))))) \<longrightarrow>
 ((i_1 \<le> (n + (1::int))) \<and> ((i_1 \<le> (n + (1::int))) \<longrightarrow> ((res_1 * (2::int)) = ((i_1 - (1::int)) * i_1)))))))"*)
"(\<forall>  res_0 res_1 i_1. ((vc_i \<le> (n + (1::int))) \<longrightarrow>
 (((((res_0 * (2::int)) = ((vc_i - (1::int)) * vc_i)) \<and> (vc_i \<le> n)) \<and> ((res_1 = (res_0 + vc_i)) \<and> (i_1 = (vc_i + (1::int))))) \<longrightarrow>
 ((i_1 \<le> (n + (1::int))) \<and> ((i_1 \<le> (n + (1::int))) \<longrightarrow> ((res_1 * (2::int)) = ((i_1 - (1::int)) * i_1)))))))"
shows "(s' = Magic)"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon9_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (UnOp Not (BinOp (Var ''i'') Le (Var ''n'')))), 
(Assume (BinOp (Var ''i'') Le (BinOp (Var ''n'') Add (Val (IntV 1))))), 
(Assume (BinOp (BinOp (Var ''res'') Mul (Val (IntV 2))) Eq (BinOp (BinOp (Var ''i'') Sub (Val (IntV 1))) Mul (Var ''i'')))), 
(Assert (BinOp (BinOp (Var ''res'') Mul (Val (IntV 2))) Eq (BinOp (Var ''n'') Mul (BinOp (Var ''n'') Add (Val (IntV 1))))))] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''res'') = (Some (IntV vc_res)))" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"(vc_passive.vc_anon9_Else vc_n)"
shows "(s' \<noteq> Failure)"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon9_Else_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon8_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''res'') = (Some (IntV vc_res)))" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"((vc_passive.vc_anon9_Then vc_n) \<and> (vc_passive.vc_anon9_Else vc_n))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_n vc_res vc_i. (((((n_s' ''n'') = (Some (IntV vc_n))) \<and> ((n_s' ''res'') = (Some (IntV vc_res)))) \<and> ((n_s' ''i'') = (Some (IntV vc_i)))) \<and> ((vc_passive.vc_anon9_Then vc_n) \<and> (vc_passive.vc_anon9_Else vc_n)))))))"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon7_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assign [(''res'', (Val (IntV 0)))]), 
(Assign [(''i'', (Val (IntV 0)))]), 
(Assert (BinOp (Var ''i'') Le (BinOp (Var ''n'') Add (Val (IntV 1))))), 
(Assert (BinOp (BinOp (Var ''res'') Mul (Val (IntV 2))) Eq (BinOp (BinOp (Var ''i'') Sub (Val (IntV 1))) Mul (Var ''i'')))), 
(Havoc ''i''), 
(Havoc ''res'')] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"(vc_passive.vc_anon7_Else vc_n)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_n vc_res vc_i. (((((n_s' ''n'') = (Some (IntV vc_n))) \<and> ((n_s' ''res'') = (Some (IntV vc_res)))) \<and> ((n_s' ''i'') = (Some (IntV vc_i)))) \<and> (((vc_passive.vc_anon8_Then ) \<and> (vc_passive.vc_anon9_Then vc_n)) \<and> (vc_passive.vc_anon9_Else vc_n)))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon7_Else_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Val (IntV 0)) Le (Var ''n'')))] (Normal n_s) s')" and 
"((n_s ''res'') = (Some (IntV vc_res)))" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"(vc_passive.vc_anon0 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_n vc_res. ((((n_s' ''n'') = (Some (IntV vc_n))) \<and> ((n_s' ''res'') = (Some (IntV vc_res)))) \<and> ((vc_passive.vc_anon7_Then ) \<and> (vc_passive.vc_anon7_Else vc_n)))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon0_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''res'') = (Some (IntV vc_res)))" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"(vc_passive.vc_anon0 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_res vc_n. ((((n_s' ''res'') = (Some (IntV vc_res))) \<and> ((n_s' ''n'') = (Some (IntV vc_n)))) \<and> (vc_passive.vc_anon0 ))))))"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''res'') = (Some (IntV vc_res)))" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"(vc_passive.vc_PreconditionGeneratedEntry )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_res vc_n. ((((n_s' ''res'') = (Some (IntV vc_res))) \<and> ((n_s' ''n'') = (Some (IntV vc_n)))) \<and> (vc_passive.vc_anon0 ))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_PreconditionGeneratedEntry_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)


end


end
