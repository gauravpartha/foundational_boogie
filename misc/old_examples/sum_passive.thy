theory sum_passive
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

locale passification = 
fixes \<Lambda> :: "(var_context)" and \<Gamma> :: "(fun_context)" and n_s :: "((vname) => ((val)option))" and vc_n :: "int" and vc_i :: "int" and vc_i_0 :: "int" and vc_res_0 :: "int" and vc_res_1 :: "int" and vc_i_1 :: "int" and vc_res :: "int"
assumes 
G0: "((n_s ''vc_n'') = (Some (IntV vc_n)))" and 
G1: "((n_s ''vc_i'') = (Some (IntV vc_i)))" and 
G2: "((n_s ''vc_i_0'') = (Some (IntV vc_i_0)))" and 
G3: "((n_s ''vc_res_0'') = (Some (IntV vc_res_0)))" and 
G4: "((n_s ''vc_res_1'') = (Some (IntV vc_res_1)))" and 
G5: "((n_s ''vc_i_1'') = (Some (IntV vc_i_1)))" and 
G6: "((n_s ''vc_res'') = (Some (IntV vc_res)))"
begin

lemmas global_assms = G0 G1 G2 G3 G4 G5 G6
lemma block_anon7_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (BinOp (Var ''vc_res'') Mul (Val (IntV 2))) Eq (BinOp (Var ''vc_n'') Mul (BinOp (Var ''vc_n'') Add (Val (IntV 1)))))), 
(Assume (Val (BoolV False)))] (Normal n_s) s')" and 
"(vc.vc_anon7_Then )"
shows "(s' = Magic)"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon7_Then_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon8_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''vc_i_0'') Le (BinOp (Var ''vc_n'') Add (Val (IntV 1))))), 
(Assume (BinOp (BinOp (Var ''vc_res_0'') Mul (Val (IntV 2))) Eq (BinOp (BinOp (Var ''vc_i_0'') Sub (Val (IntV 1))) Mul (Var ''vc_i_0'')))), 
(Assume (Val (BoolV False)))] (Normal n_s) s')" and 
"(vc.vc_anon8_Then )"
shows "(s' = Magic)"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon8_Then_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon9_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''vc_i_0'') Le (BinOp (Var ''vc_n'') Add (Val (IntV 1))))), 
(Assume (BinOp (BinOp (Var ''vc_res_0'') Mul (Val (IntV 2))) Eq (BinOp (BinOp (Var ''vc_i_0'') Sub (Val (IntV 1))) Mul (Var ''vc_i_0'')))), 
(Assume (BinOp (Var ''vc_i_0'') Le (Var ''vc_n''))), 
(Assume (BinOp (Var ''vc_res_1'') Eq (BinOp (Var ''vc_res_0'') Add (Var ''vc_i_0'')))), 
(Assume (BinOp (Var ''vc_i_1'') Eq (BinOp (Var ''vc_i_0'') Add (Val (IntV 1))))), 
(Assert (BinOp (Var ''vc_i_1'') Le (BinOp (Var ''vc_n'') Add (Val (IntV 1))))), 
(Assert (BinOp (BinOp (Var ''vc_res_1'') Mul (Val (IntV 2))) Eq (BinOp (BinOp (Var ''vc_i_1'') Sub (Val (IntV 1))) Mul (Var ''vc_i_1'')))), 
(Assume (Val (BoolV False)))] (Normal n_s) s')" and 
"(vc.vc_anon9_Then vc_i_0 vc_n vc_res_0 vc_res_1 vc_i_1)"
shows "(s' = Magic)"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon9_Then_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon9_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (UnOp Not (BinOp (Var ''vc_i_0'') Le (Var ''vc_n'')))), 
(Assume (BinOp (Var ''vc_i_0'') Le (BinOp (Var ''vc_n'') Add (Val (IntV 1))))), 
(Assume (BinOp (BinOp (Var ''vc_res_0'') Mul (Val (IntV 2))) Eq (BinOp (BinOp (Var ''vc_i_0'') Sub (Val (IntV 1))) Mul (Var ''vc_i_0'')))), 
(Assert (BinOp (BinOp (Var ''vc_res_0'') Mul (Val (IntV 2))) Eq (BinOp (Var ''vc_n'') Mul (BinOp (Var ''vc_n'') Add (Val (IntV 1))))))] (Normal n_s) s')" and 
"(vc.vc_anon9_Else vc_i_0 vc_n vc_res_0)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon9_Else_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon7_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assert (BinOp (Val (IntV 0)) Le (BinOp (Var ''vc_n'') Add (Val (IntV 1))))), 
(Assert (BinOp (BinOp (Val (IntV 0)) Mul (Val (IntV 2))) Eq (BinOp (BinOp (Val (IntV 0)) Sub (Val (IntV 1))) Mul (Val (IntV 0)))))] (Normal n_s) s')" and 
"(vc.vc_anon7_Else vc_n vc_i_0 vc_res_0 vc_res_1 vc_i_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (((vc.vc_anon8_Then ) \<and> (vc.vc_anon9_Then vc_i_0 vc_n vc_res_0 vc_res_1 vc_i_1)) \<and> (vc.vc_anon9_Else vc_i_0 vc_n vc_res_0))))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon7_Else_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Val (IntV 0)) Le (Var ''vc_n'')))] (Normal n_s) s')" and 
"(vc.vc_anon0 vc_n vc_i_0 vc_res_0 vc_res_1 vc_i_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon7_Then ) \<and> (vc.vc_anon7_Else vc_n vc_i_0 vc_res_0 vc_res_1 vc_i_1))))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon0_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"(vc.vc_PreconditionGeneratedEntry vc_n vc_i_0 vc_res_0 vc_res_1 vc_i_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 vc_n vc_i_0 vc_res_0 vc_res_1 vc_i_1)))))"
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

lemma block_anon8_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((vc.vc_anon9_Then vc_i_0 vc_n vc_res_0 vc_res_1 vc_i_1) \<and> (vc.vc_anon9_Else vc_i_0 vc_n vc_res_0))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon9_Then vc_i_0 vc_n vc_res_0 vc_res_1 vc_i_1) \<and> (vc.vc_anon9_Else vc_i_0 vc_n vc_res_0))))))"
using assms
apply cases
by auto

lemma block_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"(vc.vc_anon0 vc_n vc_i_0 vc_res_0 vc_res_1 vc_i_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 vc_n vc_i_0 vc_res_0 vc_res_1 vc_i_1)))))"
using assms
apply cases
by auto


end


end
