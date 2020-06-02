theory goto_simple_passive
imports Semantics Util
begin
locale vc
begin

definition vc_loopBody
  where
    "vc_loopBody i_1 n i_2 = (((i_1 < n) \<and> (i_2 = (i_1 + (1::int)))) \<longrightarrow> (i_2 > (0::int)))"
definition vc_afterLoop
  where
    "vc_afterLoop i_1 n = ((i_1 \<ge> n) \<longrightarrow> ((i_1 + (1::int)) > (1::int)))"
definition vc_loopHead
  where
    "vc_loopHead i_1 n i_2 = ((((1::int) \<le> i_1) \<and> (i_1 > (0::int))) \<longrightarrow> ((vc_loopBody i_1 n i_2) \<and> (vc_afterLoop i_1 n)))"
definition vc_anon0
  where
    "vc_anon0 k i_0 i_1 n i_2 = (((k \<ge> (0::int)) \<and> (i_0 = (k + (1::int)))) \<longrightarrow> ((i_0 > (0::int)) \<and> ((i_0 > (0::int)) \<longrightarrow> (vc_loopHead i_1 n i_2))))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry k i_0 i_1 n i_2 = (vc_anon0 k i_0 i_1 n i_2)"
lemma vc_correct:

shows "(vc_PreconditionGeneratedEntry k i_0 i_1 n i_2)"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def vc_loopHead_def vc_afterLoop_def vc_loopBody_def)
oops


end

locale passification = 
fixes \<Lambda> :: "(var_context)" and \<Gamma> :: "(fun_context)" and n_s :: "((vname) => ((val)option))" and vc_n :: "int" and vc_k :: "int" and vc_i :: "int" and vc_i_0 :: "int" and vc_i_1 :: "int" and vc_i_2 :: "int"
assumes 
G0: "((n_s ''vc_n'') = (Some (IntV vc_n)))" and 
G1: "((n_s ''vc_k'') = (Some (IntV vc_k)))" and 
G2: "((n_s ''vc_i'') = (Some (IntV vc_i)))" and 
G3: "((n_s ''vc_i_0'') = (Some (IntV vc_i_0)))" and 
G4: "((n_s ''vc_i_1'') = (Some (IntV vc_i_1)))" and 
G5: "((n_s ''vc_i_2'') = (Some (IntV vc_i_2)))"
begin

lemmas global_assms = G0 G1 G2 G3 G4 G5
lemma block_loopBody:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''vc_i_1'') Lt (Var ''vc_n''))), 
(Assume (BinOp (Var ''vc_i_2'') Eq (BinOp (Var ''vc_i_1'') Add (Val (IntV 1))))), 
(Assert (BinOp (Var ''vc_i_2'') Gt (Val (IntV 0)))), 
(Assume (Val (BoolV False)))] (Normal n_s) s')" and 
"(vc.vc_loopBody vc_i_1 vc_n vc_i_2)"
shows "(s' = Magic)"
using assms global_assms
apply cases
apply (simp only: vc.vc_loopBody_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_afterLoop:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''vc_i_1'') Ge (Var ''vc_n''))), 
(Assert (BinOp (BinOp (Var ''vc_i_1'') Add (Val (IntV 1))) Gt (Val (IntV 1))))] (Normal n_s) s')" and 
"(vc.vc_afterLoop vc_i_1 vc_n)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_afterLoop_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_loopHead:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Val (IntV 1)) Le (Var ''vc_i_1''))), 
(Assume (BinOp (Var ''vc_i_1'') Gt (Val (IntV 0))))] (Normal n_s) s')" and 
"(vc.vc_loopHead vc_i_1 vc_n vc_i_2)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_loopBody vc_i_1 vc_n vc_i_2) \<and> (vc.vc_afterLoop vc_i_1 vc_n))))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_loopHead_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''vc_k'') Ge (Val (IntV 0)))), 
(Assume (BinOp (Var ''vc_i_0'') Eq (BinOp (Var ''vc_k'') Add (Val (IntV 1))))), 
(Assert (BinOp (Var ''vc_i_0'') Gt (Val (IntV 0))))] (Normal n_s) s')" and 
"(vc.vc_anon0 vc_k vc_i_0 vc_i_1 vc_n vc_i_2)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_loopHead vc_i_1 vc_n vc_i_2)))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon0_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"(vc.vc_PreconditionGeneratedEntry vc_k vc_i_0 vc_i_1 vc_n vc_i_2)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 vc_k vc_i_0 vc_i_1 vc_n vc_i_2)))))"
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
"(vc.vc_anon0 vc_k vc_i_0 vc_i_1 vc_n vc_i_2)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 vc_k vc_i_0 vc_i_1 vc_n vc_i_2)))))"
using assms
apply cases
by auto


end


end
