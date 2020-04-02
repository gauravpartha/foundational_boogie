theory passify_simple_passive
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
  by smt


end

locale passification = 
fixes \<Lambda> :: "(var_context)" and \<Gamma> :: "(fun_context)" and n_s :: "((vname) => ((val)option))" and vc_y :: "int" and vc_x :: "int" and vc_x_0 :: "int" and vc_x_1 :: "int"
assumes 
G0: "((n_s ''vc_y'') = (Some (IntV vc_y)))" and 
G1: "((n_s ''vc_x'') = (Some (IntV vc_x)))" and 
G2: "((n_s ''vc_x_0'') = (Some (IntV vc_x_0)))" and 
G3: "((n_s ''vc_x_1'') = (Some (IntV vc_x_1)))"
begin

lemmas global_assms = G0 G1 G2 G3
lemma block_anon3_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''vc_x_0'') Eq (BinOp (Var ''vc_y'') Add (Val (IntV 1))))), 
(Assert (BinOp (Var ''vc_x_0'') Ge (Val (IntV 0))))] (Normal n_s) s')" and 
"(vc.vc_anon3_Then vc_x_0 vc_y)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon3_Then_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon3_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''vc_x_1'') Eq (BinOp (Val (IntV 0)) Sub (Var ''vc_y'')))), 
(Assert (BinOp (Var ''vc_x_1'') Lt (Val (IntV 0))))] (Normal n_s) s')" and 
"(vc.vc_anon3_Else vc_x_1 vc_y)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon3_Else_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''vc_y'') Gt (Val (IntV 0))))] (Normal n_s) s')" and 
"(vc.vc_anon0 vc_y vc_x_0 vc_x_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon3_Then vc_x_0 vc_y) \<and> (vc.vc_anon3_Else vc_x_1 vc_y))))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon0_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"(vc.vc_PreconditionGeneratedEntry vc_y vc_x_0 vc_x_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 vc_y vc_x_0 vc_x_1)))))"
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
"(vc.vc_anon0 vc_y vc_x_0 vc_x_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 vc_y vc_x_0 vc_x_1)))))"
using assms
apply cases
by auto


end


end
