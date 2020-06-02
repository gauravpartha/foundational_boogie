theory infeasible_edge_3_passive
imports Semantics Util
begin
locale vc
begin

definition vc_anon4_Then
  where
    "vc_anon4_Then x = (((x > (0::int)) \<and> (x < (0::int))) \<longrightarrow> ((\<not> (x = (1::int))) \<and> (\<not> (\<not> (x = (1::int))))))"
definition vc_anon4_Else
  where
    "vc_anon4_Else x y_0 z_0 = (((0::int) \<ge> x) \<longrightarrow> (((y_0 = ((2::int) * x)) \<and> (z_0 = (y_0 + (1::int)))) \<longrightarrow> (z_0 = (((2::int) * x) + (1::int)))))"
definition vc_anon0
  where
    "vc_anon0 x y_0 z_0 = ((vc_anon4_Then x) \<and> (vc_anon4_Else x y_0 z_0))"
lemma vc_correct:

shows "(vc_anon0 x y_0 z_0)"
apply (simp only: vc_anon0_def vc_anon4_Else_def vc_anon4_Then_def)
oops


end

locale passification = 
fixes \<Lambda> :: "(var_context)" and \<Gamma> :: "(fun_context)" and n_s :: "((vname) => ((val)option))" and vc_x :: "int" and vc_y :: "int" and vc_z :: "int" and vc_y_0 :: "int" and vc_z_0 :: "int"
assumes 
G0: "((n_s ''vc_x'') = (Some (IntV vc_x)))" and 
G1: "((n_s ''vc_y'') = (Some (IntV vc_y)))" and 
G2: "((n_s ''vc_z'') = (Some (IntV vc_z)))" and 
G3: "((n_s ''vc_y_0'') = (Some (IntV vc_y_0)))" and 
G4: "((n_s ''vc_z_0'') = (Some (IntV vc_z_0)))"
begin

lemmas global_assms = G0 G1 G2 G3 G4
lemma block_anon4_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''vc_x'') Gt (Val (IntV 0)))), 
(Assume (BinOp (Var ''vc_x'') Lt (Val (IntV 0)))), 
(Assert (UnOp Not (BinOp (Var ''vc_x'') Eq (Val (IntV 1))))), 
(Assert (Val (BoolV False)))] (Normal n_s) s')" and 
"(vc.vc_anon4_Then vc_x)"
shows "(s' = Magic)"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon4_Then_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon4_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Val (IntV 0)) Ge (Var ''vc_x''))), 
(Assume (BinOp (Var ''vc_y_0'') Eq (BinOp (Val (IntV 2)) Mul (Var ''vc_x'')))), 
(Assume (BinOp (Var ''vc_z_0'') Eq (BinOp (Var ''vc_y_0'') Add (Val (IntV 1))))), 
(Assert (BinOp (Var ''vc_z_0'') Eq (BinOp (BinOp (Val (IntV 2)) Mul (Var ''vc_x'')) Add (Val (IntV 1)))))] (Normal n_s) s')" and 
"(vc.vc_anon4_Else vc_x vc_y_0 vc_z_0)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon4_Else_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"(vc.vc_anon0 vc_x vc_y_0 vc_z_0)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon4_Then vc_x) \<and> (vc.vc_anon4_Else vc_x vc_y_0 vc_z_0))))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon0_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_GeneratedUnifiedExit:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms
apply cases
by auto

lemma block_anon0_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((vc.vc_anon4_Then vc_x) \<and> (vc.vc_anon4_Else vc_x vc_y_0 vc_z_0))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon4_Then vc_x) \<and> (vc.vc_anon4_Else vc_x vc_y_0 vc_z_0))))))"
using assms
apply cases
by auto

lemma block_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((vc.vc_anon4_Then vc_x) \<and> (vc.vc_anon4_Else vc_x vc_y_0 vc_z_0))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon4_Then vc_x) \<and> (vc.vc_anon4_Else vc_x vc_y_0 vc_z_0))))))"
using assms
apply cases
by auto


end


end
