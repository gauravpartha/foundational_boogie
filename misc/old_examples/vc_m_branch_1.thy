theory vc_m_branch_1
imports Semantics Util
begin
locale vc = 
fixes x :: "int" and y :: "int" and f :: "(int => int)"
begin

definition vc_anon3
  where
    "vc_anon3  = ((1 \<le> x) \<longrightarrow> ((1 \<le> y) \<and> ((1 \<le> y) \<longrightarrow> ((x = 3) \<longrightarrow> (y = 4)))))"
definition vc_anon4_Then
  where
    "vc_anon4_Then  = (((0 \<le> x) \<and> (y = (x + 1))) \<longrightarrow> vc_anon3)"
definition vc_anon4_Else
  where
    "vc_anon4_Else  = (((x < 0) \<and> (y \<le> 0)) \<longrightarrow> vc_anon3)"
definition vc_anon0
  where
    "vc_anon0  = (vc_anon4_Then \<and> vc_anon4_Else)"

end

lemma anon3_correct:
assumes 
"(red_cmd_list \<Gamma> [(Assume (BinOp (Val (IntV 1)) Le (Var ''x''))), (Assert (BinOp (Val (IntV 1)) Le (Var ''y''))), (Assume (BinOp (Var ''x'') Eq (Val (IntV 3)))), (Assert (BinOp (Var ''y'') Eq (Val (IntV 4))))] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"(((snd \<Gamma>) ''f'') = (Some isa_f))" and 
"(\<forall> farg0. ((isa_f [(IntV farg0)]) = (Some (IntV (vc_f farg0)))))" and 
"(vc.vc_anon3 vc_x vc_y)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms
  apply cases
  apply (simp only: vc.vc_anon3_def)  
  apply (handle_cmd_list_full+)
  by (auto?)

lemma anon4_Then_correct:
assumes 
"(red_cmd_list \<Gamma> [(Assume (BinOp (Val (IntV 0)) Le (Var ''x''))), (Assume (BinOp (Var ''y'') Eq (BinOp (Var ''x'') Add (Val (IntV 1)))))] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"(((snd \<Gamma>) ''f'') = (Some isa_f))" and 
"(\<forall> farg0. ((isa_f [(IntV farg0)]) = (Some (IntV (vc_f farg0)))))" and 
"(vc.vc_anon4_Then vc_x vc_y)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon3 vc_x vc_y)))))"
using assms
  apply cases
  apply (simp only: vc.vc_anon4_Then_def)
apply (handle_cmd_list_full+)
  by (auto?)

lemma anon4_Else_correct:
assumes 
"(red_cmd_list \<Gamma> [(Assume (BinOp (Var ''x'') Lt (Val (IntV 0)))), (Assume (BinOp (Var ''y'') Le (Val (IntV 0))))] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"(((snd \<Gamma>) ''f'') = (Some isa_f))" and 
"(\<forall> farg0. ((isa_f [(IntV farg0)]) = (Some (IntV (vc_f farg0)))))" and 
"(vc.vc_anon4_Else vc_x vc_y)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon3 vc_x vc_y)))))"
using assms
  apply cases
  apply (simp only: vc.vc_anon4_Else_def)
  apply (handle_cmd_list_full+)
  by (auto?)

lemma anon0_correct:
assumes 
"(red_cmd_list \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"(((snd \<Gamma>) ''f'') = (Some isa_f))" and 
"(\<forall> farg0. ((isa_f [(IntV farg0)]) = (Some (IntV (vc_f farg0)))))" and 
"(vc.vc_anon0 vc_x vc_y)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon4_Then vc_x vc_y) \<and> (vc.vc_anon4_Else vc_x vc_y))))))"
using assms
  apply cases
  apply (simp only: vc.vc_anon0_def)
  by auto

end
