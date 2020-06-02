theory m_branch_1_passive
imports Semantics Util
begin
locale vc = 
fixes f :: "(int => int)"
begin

definition vc_anon3
  where
    "vc_anon3 x y = (((1::int) \<le> x) \<longrightarrow> (((1::int) \<le> y) \<and> (((1::int) \<le> y) \<longrightarrow> ((x = (3::int)) \<longrightarrow> (y = (4::int))))))"
definition vc_anon4_Then
  where
    "vc_anon4_Then x y = ((((0::int) \<le> x) \<and> (y = (x + (1::int)))) \<longrightarrow> (vc_anon3 x y))"
definition vc_anon4_Else
  where
    "vc_anon4_Else x y = (((x < (0::int)) \<and> (y \<le> (0::int))) \<longrightarrow> (vc_anon3 x y))"
definition vc_anon0
  where
    "vc_anon0 x y = ((vc_anon4_Then x y) \<and> (vc_anon4_Else x y))"
lemma vc_correct:

shows "(vc_anon0 x y)"
apply (simp only: vc_anon0_def vc_anon4_Else_def vc_anon4_Then_def vc_anon3_def)
oops


end

locale passification = 
fixes \<Lambda> :: "(var_context)" and \<Gamma> :: "(fun_context)" and n_s :: "((vname) => ((val)option))" and f :: "(((val)list) => ((val)option))" and vc_f :: "(int => int)" and vc_x :: "int" and vc_y :: "int"
assumes 
G0: "(((snd \<Gamma>) ''f'') = (Some f))" and 
G1: "(\<forall> farg0. ((f [(IntV farg0)]) = (Some (IntV (vc_f farg0)))))" and 
G2: "((n_s ''vc_x'') = (Some (IntV vc_x)))" and 
G3: "((n_s ''vc_y'') = (Some (IntV vc_y)))"
begin

lemmas global_assms = G0 G1 G2 G3
lemma block_anon3:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Val (IntV 1)) Le (Var ''vc_x''))), 
(Assert (BinOp (Val (IntV 1)) Le (Var ''vc_y''))), 
(Assume (BinOp (Var ''vc_x'') Eq (Val (IntV 3)))), 
(Assert (BinOp (Var ''vc_y'') Eq (Val (IntV 4))))] (Normal n_s) s')" and 
"(vc.vc_anon3 vc_x vc_y)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon3_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon4_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Val (IntV 0)) Le (Var ''vc_x''))), 
(Assume (BinOp (Var ''vc_y'') Eq (BinOp (Var ''vc_x'') Add (Val (IntV 1)))))] (Normal n_s) s')" and 
"(vc.vc_anon4_Then vc_x vc_y)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon3 vc_x vc_y)))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon4_Then_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon4_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''vc_x'') Lt (Val (IntV 0)))), 
(Assume (BinOp (Var ''vc_y'') Le (Val (IntV 0))))] (Normal n_s) s')" and 
"(vc.vc_anon4_Else vc_x vc_y)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon3 vc_x vc_y)))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon4_Else_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"(vc.vc_anon0 vc_x vc_y)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon4_Then vc_x vc_y) \<and> (vc.vc_anon4_Else vc_x vc_y))))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon0_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon0_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((vc.vc_anon4_Then vc_x vc_y) \<and> (vc.vc_anon4_Else vc_x vc_y))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon4_Then vc_x vc_y) \<and> (vc.vc_anon4_Else vc_x vc_y))))))"
using assms
apply cases
by auto

lemma block_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((vc.vc_anon4_Then vc_x vc_y) \<and> (vc.vc_anon4_Else vc_x vc_y))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon4_Then vc_x vc_y) \<and> (vc.vc_anon4_Else vc_x vc_y))))))"
using assms
apply cases
by auto


end


end
