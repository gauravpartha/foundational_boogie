theory assign_exp_passive
imports Semantics Util
begin
locale vc
begin

definition vc_anon0
  where
    "vc_anon0 x x1_0 x2_0 x3_0 x4_0 x5_0 x6_0 x7_0 x8_0 x9_0 x10_0 = ((x > (0::int)) \<longrightarrow> (((x1_0 = (x + x)) \<and> (x2_0 = (x1_0 + x1_0))) \<longrightarrow> (((((x3_0 = (x2_0 + x2_0)) \<and> (x4_0 = (x3_0 + x3_0))) \<and> ((x5_0 = (x4_0 + x4_0)) \<and> (x6_0 = (x5_0 + x5_0)))) \<and> (((x7_0 = (x6_0 + x6_0)) \<and> (x8_0 = (x7_0 + x7_0))) \<and> ((x9_0 = (x8_0 + x8_0)) \<and> (x10_0 = (x9_0 + x9_0))))) \<longrightarrow> (x10_0 \<ge> (0::int)))))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry x x1_0 x2_0 x3_0 x4_0 x5_0 x6_0 x7_0 x8_0 x9_0 x10_0 = (vc_anon0 x x1_0 x2_0 x3_0 x4_0 x5_0 x6_0 x7_0 x8_0 x9_0 x10_0)"
lemma vc_correct:

shows "(vc_PreconditionGeneratedEntry x x1_0 x2_0 x3_0 x4_0 x5_0 x6_0 x7_0 x8_0 x9_0 x10_0)"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def)
oops


end

locale passification = 
fixes \<Lambda> :: "(var_context)" and \<Gamma> :: "(fun_context)" and n_s :: "((vname) => ((val)option))" and vc_x :: "int" and vc_x1 :: "int" and vc_x2 :: "int" and vc_x3 :: "int" and vc_x4 :: "int" and vc_x5 :: "int" and vc_x6 :: "int" and vc_x7 :: "int" and vc_x8 :: "int" and vc_x9 :: "int" and vc_x10 :: "int" and vc_x1_0 :: "int" and vc_x2_0 :: "int" and vc_x3_0 :: "int" and vc_x4_0 :: "int" and vc_x5_0 :: "int" and vc_x6_0 :: "int" and vc_x7_0 :: "int" and vc_x8_0 :: "int" and vc_x9_0 :: "int" and vc_x10_0 :: "int"
assumes 
G0: "((n_s ''vc_x'') = (Some (IntV vc_x)))" and 
G1: "((n_s ''vc_x1'') = (Some (IntV vc_x1)))" and 
G2: "((n_s ''vc_x2'') = (Some (IntV vc_x2)))" and 
G3: "((n_s ''vc_x3'') = (Some (IntV vc_x3)))" and 
G4: "((n_s ''vc_x4'') = (Some (IntV vc_x4)))" and 
G5: "((n_s ''vc_x5'') = (Some (IntV vc_x5)))" and 
G6: "((n_s ''vc_x6'') = (Some (IntV vc_x6)))" and 
G7: "((n_s ''vc_x7'') = (Some (IntV vc_x7)))" and 
G8: "((n_s ''vc_x8'') = (Some (IntV vc_x8)))" and 
G9: "((n_s ''vc_x9'') = (Some (IntV vc_x9)))" and 
G10: "((n_s ''vc_x10'') = (Some (IntV vc_x10)))" and 
G11: "((n_s ''vc_x1_0'') = (Some (IntV vc_x1_0)))" and 
G12: "((n_s ''vc_x2_0'') = (Some (IntV vc_x2_0)))" and 
G13: "((n_s ''vc_x3_0'') = (Some (IntV vc_x3_0)))" and 
G14: "((n_s ''vc_x4_0'') = (Some (IntV vc_x4_0)))" and 
G15: "((n_s ''vc_x5_0'') = (Some (IntV vc_x5_0)))" and 
G16: "((n_s ''vc_x6_0'') = (Some (IntV vc_x6_0)))" and 
G17: "((n_s ''vc_x7_0'') = (Some (IntV vc_x7_0)))" and 
G18: "((n_s ''vc_x8_0'') = (Some (IntV vc_x8_0)))" and 
G19: "((n_s ''vc_x9_0'') = (Some (IntV vc_x9_0)))" and 
G20: "((n_s ''vc_x10_0'') = (Some (IntV vc_x10_0)))"
begin

lemmas global_assms = G0 G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 G16 G17 G18 G19 G20
lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''vc_x'') Gt (Val (IntV 0)))), 
(Assume (BinOp (Var ''vc_x1_0'') Eq (BinOp (Var ''vc_x'') Add (Var ''vc_x'')))), 
(Assume (BinOp (Var ''vc_x2_0'') Eq (BinOp (Var ''vc_x1_0'') Add (Var ''vc_x1_0'')))), 
(Assume (BinOp (Var ''vc_x3_0'') Eq (BinOp (Var ''vc_x2_0'') Add (Var ''vc_x2_0'')))), 
(Assume (BinOp (Var ''vc_x4_0'') Eq (BinOp (Var ''vc_x3_0'') Add (Var ''vc_x3_0'')))), 
(Assume (BinOp (Var ''vc_x5_0'') Eq (BinOp (Var ''vc_x4_0'') Add (Var ''vc_x4_0'')))), 
(Assume (BinOp (Var ''vc_x6_0'') Eq (BinOp (Var ''vc_x5_0'') Add (Var ''vc_x5_0'')))), 
(Assume (BinOp (Var ''vc_x7_0'') Eq (BinOp (Var ''vc_x6_0'') Add (Var ''vc_x6_0'')))), 
(Assume (BinOp (Var ''vc_x8_0'') Eq (BinOp (Var ''vc_x7_0'') Add (Var ''vc_x7_0'')))), 
(Assume (BinOp (Var ''vc_x9_0'') Eq (BinOp (Var ''vc_x8_0'') Add (Var ''vc_x8_0'')))), 
(Assume (BinOp (Var ''vc_x10_0'') Eq (BinOp (Var ''vc_x9_0'') Add (Var ''vc_x9_0'')))), 
(Assert (BinOp (Var ''vc_x10_0'') Ge (Val (IntV 0))))] (Normal n_s) s')" and 
"(vc.vc_anon0 vc_x vc_x1_0 vc_x2_0 vc_x3_0 vc_x4_0 vc_x5_0 vc_x6_0 vc_x7_0 vc_x8_0 vc_x9_0 vc_x10_0)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon0_def)
apply (handle_cmd_list_full)
by auto

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"(vc.vc_PreconditionGeneratedEntry vc_x vc_x1_0 vc_x2_0 vc_x3_0 vc_x4_0 vc_x5_0 vc_x6_0 vc_x7_0 vc_x8_0 vc_x9_0 vc_x10_0)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 vc_x vc_x1_0 vc_x2_0 vc_x3_0 vc_x4_0 vc_x5_0 vc_x6_0 vc_x7_0 vc_x8_0 vc_x9_0 vc_x10_0)))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_PreconditionGeneratedEntry_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"(vc.vc_anon0 vc_x vc_x1_0 vc_x2_0 vc_x3_0 vc_x4_0 vc_x5_0 vc_x6_0 vc_x7_0 vc_x8_0 vc_x9_0 vc_x10_0)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 vc_x vc_x1_0 vc_x2_0 vc_x3_0 vc_x4_0 vc_x5_0 vc_x6_0 vc_x7_0 vc_x8_0 vc_x9_0 vc_x10_0)))))"
using assms
apply cases
by auto


end


end
