theory constant_prop_branch_2
imports Semantics Util
begin
locale vc
begin

definition vc_anon3
  where
    "vc_anon3 x_3 = ((x_3 = (2::int)) \<or> (x_3 = (3::int)))"
definition vc_anon4_Then
  where
    "vc_anon4_Then x_1 x_0 x_3 = (((x_1 = (x_0 + (1::int))) \<and> (x_3 = x_1)) \<longrightarrow> (vc_anon3 x_3))"
definition vc_anon4_Else
  where
    "vc_anon4_Else x_2 x_0 x_3 = (((x_2 = (x_0 + (2::int))) \<and> (x_3 = x_2)) \<longrightarrow> (vc_anon3 x_3))"
definition vc_anon0
  where
    "vc_anon0 x_0 x_1 x_3 x_2 = ((x_0 = ((0::int) + (1::int))) \<longrightarrow> ((vc_anon4_Then x_1 x_0 x_3) \<and> (vc_anon4_Else x_2 x_0 x_3)))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry x_0 x_1 x_3 x_2 = (vc_anon0 x_0 x_1 x_3 x_2)"
lemma vc_correct:

shows "(vc_PreconditionGeneratedEntry x_0 x_1 x_3 x_2)"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def vc_anon4_Else_def vc_anon4_Then_def vc_anon3_def)
oops


end

locale vc_passive
begin

definition vc_anon3
  where
    "vc_anon3 x_3 = ((x_3 = (2::int)) \<or> (x_3 = (3::int)))"
definition vc_anon4_Then
  where
    "vc_anon4_Then x_0 = (\<forall> x_1 x_3. (((x_1 = (x_0 + (1::int))) \<and> (x_3 = x_1)) \<longrightarrow> (vc_anon3 x_3)))"
definition vc_anon4_Else
  where
    "vc_anon4_Else x_0 = (\<forall> x_2 x_3. (((x_2 = (x_0 + (2::int))) \<and> (x_3 = x_2)) \<longrightarrow> (vc_anon3 x_3)))"
definition vc_anon0
  where
    "vc_anon0  = (\<forall> x_0. ((x_0 = ((0::int) + (1::int))) \<longrightarrow> ((vc_anon4_Then x_0) \<and> (vc_anon4_Else x_0))))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry  = (vc_anon0 )"
lemma vc_correct:

shows "(vc_PreconditionGeneratedEntry )"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def vc_anon4_Else_def vc_anon4_Then_def vc_anon3_def)
oops


end

locale beforePassive = 
fixes \<Lambda> :: "(var_context)" and \<Gamma> :: "(fun_context)"
assumes 
V0: "((\<Lambda> ''x'') = (Some TInt))"
begin

lemmas var_assms = V0
lemma block_anon3:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assert (BinOp (BinOp (Var ''x'') Eq (Val (IntV 2))) Or (BinOp (Var ''x'') Eq (Val (IntV 3)))))] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_anon3 vc_x)"
shows "(s' \<noteq> Failure)"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon3_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon4_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assign [(''x'', (BinOp (Var ''x'') Add (Val (IntV 1))))])] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_anon4_Then vc_x)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_x. (((n_s' ''x'') = (Some (IntV vc_x))) \<and> (vc_passive.vc_anon3 vc_x))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon4_Then_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon4_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assign [(''x'', (BinOp (Var ''x'') Add (Val (IntV 2))))])] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_anon4_Else vc_x)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_x. (((n_s' ''x'') = (Some (IntV vc_x))) \<and> (vc_passive.vc_anon3 vc_x))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon4_Else_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assign [(''x'', (Val (IntV 0)))]), 
(Assign [(''x'', (BinOp (Var ''x'') Add (Val (IntV 1))))])] (Normal n_s) s')" and 
"(vc_passive.vc_anon0 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_x. (((n_s' ''x'') = (Some (IntV vc_x))) \<and> ((vc_passive.vc_anon4_Then vc_x) \<and> (vc_passive.vc_anon4_Else vc_x)))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon0_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"(vc_passive.vc_anon0 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (vc_passive.vc_anon0 ))))"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"(vc_passive.vc_PreconditionGeneratedEntry )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (vc_passive.vc_anon0 ))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_PreconditionGeneratedEntry_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)


end


end
