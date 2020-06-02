theory goto1
imports Semantics Util
begin
locale vc = 
fixes x :: "int" and y :: "int"
begin

definition vc_Label3
  where
    "vc_Label3  = True"
definition vc_Label1
  where
    "vc_Label1  = ((x > (0::int)) \<longrightarrow> vc_Label3)"
definition vc_Label2
  where
    "vc_Label2  = ((y > (0::int)) \<longrightarrow> vc_Label3)"
definition vc_anon0
  where
    "vc_anon0  = (vc_Label1 \<and> vc_Label2)"
lemma vc_correct:

shows "vc_anon0"
apply (simp only: vc_anon0_def vc_Label2_def vc_Label1_def vc_Label3_def)
  by auto


end

locale passification = 
fixes n_s :: "((vname) => ((val)option))" and vc_x :: "int" and vc_y :: "int"
assumes 
S0: "((n_s ''x'') = (Some (IntV vc_x)))" and 
S1: "((n_s ''y'') = (Some (IntV vc_y)))"
begin

lemmas state_assms = S0 S1
lemma block_Label3:
assumes 
"(red_cmd_list \<Gamma> [(Assume (BinOp (BinOp (Var ''x'') Add (Var ''y'')) Gt (Val (IntV 0))))] (Normal n_s) s')" and 
"(vc.vc_Label3 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms state_assms
apply cases
apply (simp only: vc.vc_Label3_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_Label1:
assumes 
"(red_cmd_list \<Gamma> [(Assume (BinOp (Var ''x'') Gt (Val (IntV 0))))] (Normal n_s) s')" and 
"(vc.vc_Label1 vc_x)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_Label3 )))))"
using assms state_assms
apply cases
apply (simp only: vc.vc_Label1_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_Label2:
assumes 
"(red_cmd_list \<Gamma> [(Assume (BinOp (Var ''y'') Gt (Val (IntV 0))))] (Normal n_s) s')" and 
"(vc.vc_Label2 vc_y)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_Label3 )))))"
using assms state_assms
apply cases
apply (simp only: vc.vc_Label2_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Gamma> [] (Normal n_s) s')" and 
"(vc.vc_anon0 vc_x vc_y)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_Label1 vc_x) \<and> (vc.vc_Label2 vc_y))))))"
using assms state_assms
apply cases
apply (simp only: vc.vc_anon0_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon0_0:
assumes 
"(red_cmd_list \<Gamma> [] (Normal n_s) s')" and 
"((vc.vc_Label1 vc_x) \<and> (vc.vc_Label2 vc_y))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_Label1 vc_x) \<and> (vc.vc_Label2 vc_y))))))"
using assms
apply cases
by auto

lemma block_0:
assumes 
"(red_cmd_list \<Gamma> [] (Normal n_s) s')" and 
"((vc.vc_Label1 vc_x) \<and> (vc.vc_Label2 vc_y))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_Label1 vc_x) \<and> (vc.vc_Label2 vc_y))))))"
using assms
apply cases
by auto


end


end
