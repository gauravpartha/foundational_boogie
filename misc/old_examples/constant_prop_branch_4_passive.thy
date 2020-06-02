theory constant_prop_branch_4_passive
imports Semantics Util
begin
locale vc
begin

definition vc_anon3_Then
  where
    "vc_anon3_Then  = (((0::int) + (0::int)) \<ge> (0::int))"
definition vc_anon3_Else
  where
    "vc_anon3_Else z = (z \<ge> (0::int))"
definition vc_anon0
  where
    "vc_anon0 z = ((z \<ge> (0::int)) \<longrightarrow> ((vc_anon3_Then ) \<and> (vc_anon3_Else z)))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry z = (vc_anon0 z)"
lemma vc_correct:

shows "(vc_PreconditionGeneratedEntry z)"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def vc_anon3_Else_def vc_anon3_Then_def)
oops


end

locale passification = 
fixes \<Lambda> :: "(var_context)" and \<Gamma> :: "(fun_context)" and n_s :: "((vname) => ((val)option))" and vc_x :: "int" and vc_z :: "int" and vc_q :: "int"
assumes 
G0: "((n_s ''vc_x'') = (Some (IntV vc_x)))" and 
G1: "((n_s ''vc_z'') = (Some (IntV vc_z)))" and 
G2: "((n_s ''vc_q'') = (Some (IntV vc_q)))"
begin

lemmas global_assms = G0 G1 G2
lemma block_anon3_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assert (BinOp (BinOp (Val (IntV 0)) Add (Val (IntV 0))) Ge (Val (IntV 0))))] (Normal n_s) s')" and 
"(vc.vc_anon3_Then )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon3_Then_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon3_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assert (BinOp (Var ''vc_z'') Ge (Val (IntV 0))))] (Normal n_s) s')" and 
"(vc.vc_anon3_Else vc_z)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon3_Else_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''vc_z'') Ge (Val (IntV 0))))] (Normal n_s) s')" and 
"(vc.vc_anon0 vc_z)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon3_Then ) \<and> (vc.vc_anon3_Else vc_z))))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon0_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"(vc.vc_PreconditionGeneratedEntry vc_z)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 vc_z)))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_PreconditionGeneratedEntry_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_GeneratedUnifiedExit:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms
apply cases
by auto

lemma block_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"(vc.vc_anon0 vc_z)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 vc_z)))))"
using assms
apply cases
by auto


end


end
