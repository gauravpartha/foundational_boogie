theory passify_simple
imports Semantics Util
begin
locale vc
begin

definition vc_anon3_Then
  where
    "vc_anon3_Then x_0 y = ((x_0 = (y + (1::int))) \<longrightarrow> (x_0 \<ge> (0::int)))"
definition vc_anon3_Else
  where
    "vc_anon3_Else x_1 y = ((x_1 = ((0::int) - y)) \<longrightarrow> (x_1 < (0::int)))"
definition vc_anon0
  where
    "vc_anon0 y x_0 x_1 = ((y > (0::int)) \<longrightarrow> ((vc_anon3_Then x_0 y) \<and> (vc_anon3_Else x_1 y)))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry y x_0 x_1 = (vc_anon0 y x_0 x_1)"
lemma vc_correct:

shows "(vc_PreconditionGeneratedEntry y x_0 x_1)"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def vc_anon3_Else_def vc_anon3_Then_def)
oops


end

locale vc_passive
begin

definition vc_anon3_Then
  where
    "vc_anon3_Then y = (\<forall> x_0. ((x_0 = (y + (1::int))) \<longrightarrow> (x_0 \<ge> (0::int))))"
definition vc_anon3_Else
  where
    "vc_anon3_Else y = (\<forall> x_1. ((x_1 = ((0::int) - y)) \<longrightarrow> (x_1 < (0::int))))"
definition vc_anon0
  where
    "vc_anon0  = (\<forall> y. ((y > (0::int)) \<longrightarrow> ((vc_anon3_Then y) \<and> (vc_anon3_Else y))))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry  = (vc_anon0 )"
lemma vc_correct:

shows "(vc_PreconditionGeneratedEntry )"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def vc_anon3_Else_def vc_anon3_Then_def)
oops


end

locale beforePassive = 
fixes \<Lambda> :: "(var_context)" and \<Gamma> :: "(fun_context)"
assumes 
V0: "((\<Lambda> ''x'') = (Some TInt))" and 
V1: "((\<Lambda> ''y'') = (Some TInt))"
begin

lemmas var_assms = V0 V1
lemma block_GeneratedUnifiedExit:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')"
shows "(s' \<noteq> Failure)"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon3_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assign [(''x'', (BinOp (Var ''y'') Add (Val (IntV 1))))]), 
(Assert (BinOp (Var ''x'') Ge (Val (IntV 0))))] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"(vc_passive.vc_anon3_Then vc_y)"
shows "(s' \<noteq> Failure)"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon3_Then_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon3_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assign [(''x'', (BinOp (Val (IntV 0)) Sub (Var ''y'')))]), 
(Assert (BinOp (Var ''x'') Lt (Val (IntV 0))))] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"(vc_passive.vc_anon3_Else vc_y)"
shows "(s' \<noteq> Failure)"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon3_Else_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''y'') Gt (Val (IntV 0))))] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"(vc_passive.vc_anon0 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_y. (((n_s' ''y'') = (Some (IntV vc_y))) \<and> ((vc_passive.vc_anon3_Then vc_y) \<and> (vc_passive.vc_anon3_Else vc_y)))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon0_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"(vc_passive.vc_anon0 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_y. (((n_s' ''y'') = (Some (IntV vc_y))) \<and> (vc_passive.vc_anon0 ))))))"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"(vc_passive.vc_PreconditionGeneratedEntry )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_y. (((n_s' ''y'') = (Some (IntV vc_y))) \<and> (vc_passive.vc_anon0 ))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_PreconditionGeneratedEntry_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)


end


end
