theory constant_prop_branch_5
imports Semantics Util
begin
locale vc
begin

definition vc_anon3
  where
    "vc_anon3 z_2 q = ((z_2 \<ge> (0::int)) \<and> ((z_2 \<ge> (0::int)) \<longrightarrow> ((q \<ge> (0::int)) \<and> ((q \<ge> (0::int)) \<longrightarrow> (q \<ge> (0::int))))))"
definition vc_anon4_Then
  where
    "vc_anon4_Then z_0 z q z_2 = ((z_0 = (z + (1::int))) \<longrightarrow> (((q \<ge> (0::int)) \<and> (z_2 = z_0)) \<longrightarrow> (vc_anon3 z_2 q)))"
definition vc_anon4_Else
  where
    "vc_anon4_Else z_1 z q z_2 = ((z_1 = (z + (2::int))) \<longrightarrow> (((q \<ge> (0::int)) \<and> (z_2 = z_1)) \<longrightarrow> (vc_anon3 z_2 q)))"
definition vc_anon0
  where
    "vc_anon0 z z_0 q z_2 z_1 = ((z \<ge> (0::int)) \<longrightarrow> ((vc_anon4_Then z_0 z q z_2) \<and> (vc_anon4_Else z_1 z q z_2)))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry z z_0 q z_2 z_1 = (vc_anon0 z z_0 q z_2 z_1)"
lemma vc_correct:

shows "(vc_PreconditionGeneratedEntry z z_0 q z_2 z_1)"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def vc_anon4_Else_def vc_anon4_Then_def vc_anon3_def)
oops


end

locale vc_passive
begin

definition vc_anon3
  where
    "vc_anon3 z_2 q = ((z_2 \<ge> (0::int)) \<and> ((z_2 \<ge> (0::int)) \<longrightarrow> ((q \<ge> (0::int)) \<and> ((q \<ge> (0::int)) \<longrightarrow> (q \<ge> (0::int))))))"
definition vc_anon4_Then
  where
    "vc_anon4_Then z = (\<forall> z_0 q z_2. ((z_0 = (z + (1::int))) \<longrightarrow> (((q \<ge> (0::int)) \<and> (z_2 = z_0)) \<longrightarrow> (vc_anon3 z_2 q))))"
definition vc_anon4_Else
  where
    "vc_anon4_Else z = (\<forall> z_1 q z_2. ((z_1 = (z + (2::int))) \<longrightarrow> (((q \<ge> (0::int)) \<and> (z_2 = z_1)) \<longrightarrow> (vc_anon3 z_2 q))))"
definition vc_anon0
  where
    "vc_anon0  = (\<forall> z. ((z \<ge> (0::int)) \<longrightarrow> ((vc_anon4_Then z) \<and> (vc_anon4_Else z))))"
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
V0: "((\<Lambda> ''x'') = (Some TInt))" and 
V1: "((\<Lambda> ''z'') = (Some TInt))" and 
V2: "((\<Lambda> ''q'') = (Some TInt))" and 
V3: "((\<Lambda> ''r'') = (Some TInt))"
begin

lemmas var_assms = V0 V1 V2 V3
lemma block_anon3:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assert (BinOp (Var ''z'') Ge (Val (IntV 0)))), 
(Assert (BinOp (Var ''x'') Ge (Val (IntV 0)))), 
(Assert (BinOp (Var ''r'') Ge (Val (IntV 0))))] (Normal n_s) s')" and 
"((n_s ''r'') = (n_s ''q''))" and 
"((n_s ''x'') = (n_s ''q''))" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"((n_s ''q'') = (Some (IntV vc_q)))" and 
"(vc_passive.vc_anon3 vc_z vc_q)"
shows "(s' \<noteq> Failure)"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon3_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon4_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assign [(''z'', (BinOp (Var ''z'') Add (Val (IntV 1))))]), 
(Assume (BinOp (Var ''q'') Ge (Val (IntV 0))))] (Normal n_s) s')" and 
"((n_s ''r'') = (n_s ''q''))" and 
"((n_s ''x'') = (n_s ''q''))" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"((n_s ''q'') = (Some (IntV vc_q)))" and 
"(vc_passive.vc_anon4_Then vc_z)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_z vc_q. ((((((n_s' ''r'') = (n_s' ''q'')) \<and> ((n_s' ''x'') = (n_s' ''q''))) \<and> ((n_s' ''z'') = (Some (IntV vc_z)))) \<and> ((n_s' ''q'') = (Some (IntV vc_q)))) \<and> (vc_passive.vc_anon3 vc_z vc_q))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon4_Then_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon4_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assign [(''z'', (BinOp (Var ''z'') Add (Val (IntV 2))))]), 
(Assume (BinOp (Var ''q'') Ge (Val (IntV 0))))] (Normal n_s) s')" and 
"((n_s ''r'') = (n_s ''q''))" and 
"((n_s ''x'') = (n_s ''q''))" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"((n_s ''q'') = (Some (IntV vc_q)))" and 
"(vc_passive.vc_anon4_Else vc_z)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_z vc_q. ((((((n_s' ''r'') = (n_s' ''q'')) \<and> ((n_s' ''x'') = (n_s' ''q''))) \<and> ((n_s' ''z'') = (Some (IntV vc_z)))) \<and> ((n_s' ''q'') = (Some (IntV vc_q)))) \<and> (vc_passive.vc_anon3 vc_z vc_q))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon4_Else_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''z'') Ge (Val (IntV 0)))), 
(Assign [(''r'', (Var ''q''))]), 
(Assign [(''x'', (Var ''r''))])] (Normal n_s) s')" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"((n_s ''q'') = (Some (IntV vc_q)))" and 
"(vc_passive.vc_anon0 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_z vc_q. ((((((n_s' ''r'') = (n_s' ''q'')) \<and> ((n_s' ''x'') = (n_s' ''q''))) \<and> ((n_s' ''z'') = (Some (IntV vc_z)))) \<and> ((n_s' ''q'') = (Some (IntV vc_q)))) \<and> ((vc_passive.vc_anon4_Then vc_z) \<and> (vc_passive.vc_anon4_Else vc_z)))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon0_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"((n_s ''q'') = (Some (IntV vc_q)))" and 
"(vc_passive.vc_anon0 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_z vc_q. ((((n_s' ''z'') = (Some (IntV vc_z))) \<and> ((n_s' ''q'') = (Some (IntV vc_q)))) \<and> (vc_passive.vc_anon0 ))))))"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"((n_s ''q'') = (Some (IntV vc_q)))" and 
"(vc_passive.vc_PreconditionGeneratedEntry )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_z vc_q. ((((n_s' ''z'') = (Some (IntV vc_z))) \<and> ((n_s' ''q'') = (Some (IntV vc_q)))) \<and> (vc_passive.vc_anon0 ))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_PreconditionGeneratedEntry_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)


end


end
