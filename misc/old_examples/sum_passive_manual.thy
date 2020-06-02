theory sum_passive_manual        
imports Semantics Util
begin
locale vc = 
fixes n :: "int" and i_0 :: "int" and res_0 :: "int" and res_1 :: "int" and i_1 :: "int"
begin

definition vc_anon7_Then
  where
    "vc_anon7_Then  = True"
definition vc_anon8_Then
  where
    "vc_anon8_Then  = True"
definition vc_anon9_suc
  where
    "vc_anon9_suc = (i_1 + res_1 > 0 \<longrightarrow> res_1 > 0)"
definition vc_anon9_Then
  where
    "vc_anon9_Then  = ((i_0 \<le> (n + (1::int))) \<longrightarrow> (((((res_0 * (2::int)) = ((i_0 - (1::int)) * i_0)) \<and> (i_0 \<le> n)) \<and> ((res_1 = (res_0 + i_0)) \<and> (i_1 = (i_0 + (1::int))))) \<longrightarrow> ((i_1 \<le> (n + (1::int))) \<and> ((i_1 \<le> (n + (1::int))) \<longrightarrow> ((res_1 * (2::int)) = ((i_1 - (1::int)) * i_1))))))"
definition vc_anon9_Else
  where
    "vc_anon9_Else  = ((\<not> (i_0 \<le> n)) \<longrightarrow> (((i_0 \<le> (n + (1::int))) \<and> ((res_0 * (2::int)) = ((i_0 - (1::int)) * i_0))) \<longrightarrow> ((res_0 * (2::int)) = (n * (n + (1::int))))))"
definition vc_anon7_Else
  where
    "vc_anon7_Else  = (((0::int) \<le> (n + (1::int))) \<and> (((0::int) \<le> (n + (1::int))) \<longrightarrow> ((((0::int) * (2::int)) = (((0::int) - (1::int)) * (0::int))) \<and> ((((0::int) * (2::int)) = (((0::int) - (1::int)) * (0::int))) \<longrightarrow> ((vc_anon8_Then \<and> vc_anon9_Then) \<and> vc_anon9_Else)))))"
definition vc_anon0
  where
    "vc_anon0  = (((0::int) \<le> n) \<longrightarrow> (vc_anon7_Then \<and> vc_anon7_Else))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry  = vc_anon0"
lemma vc_correct:

shows "vc_PreconditionGeneratedEntry"
  apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def vc_anon7_Else_def vc_anon9_Else_def vc_anon9_Then_def vc_anon8_Then_def vc_anon7_Then_def)
  by (smt mult.commute semiring_normalization_rules(3))



end


locale vc_passive = 
fixes n :: "int"
begin

definition vc_anon7_Then
  where
    "vc_anon7_Then  = True"
definition vc_anon8_Then
  where
    "vc_anon8_Then  = True"
definition vc_anon9_suc
  where
    "vc_anon9_suc i_1 res_1 = (i_1 + res_1 > 0 \<longrightarrow> res_1 > 0)"
definition vc_anon9_Then
  where
    "vc_anon9_Then i_0 res_0 = (\<forall> i_1 res_1. ((i_0 \<le> (n + (1::int))) \<longrightarrow> (((((res_0 * (2::int)) = ((i_0 - (1::int)) * i_0)) \<and> (i_0 \<le> n)) \<and> ((res_1 = (res_0 + i_0)) \<and> (i_1 = (i_0 + (1::int))))) \<longrightarrow> ((i_1 \<le> (n + (1::int))) \<and> ((i_1 \<le> (n + (1::int))) \<longrightarrow> ((res_1 * (2::int)) = ((i_1 - (1::int)) * i_1))
                                              \<and> vc_anon9_suc i_1 res_1)))))"
definition vc_anon9_Else :: "int \<Rightarrow> int \<Rightarrow> bool"
  where
    "vc_anon9_Else i_0 res_0  = ((\<not> (i_0 \<le> n)) \<longrightarrow> (((i_0 \<le> (n + (1::int))) \<and> ((res_0 * (2::int)) = ((i_0 - (1::int)) * i_0))) \<longrightarrow> ((res_0 * (2::int)) = (n * (n + (1::int))))))"
definition vc_anon7_Else
  where
    "vc_anon7_Else  = (\<forall> i_0 res_0. (((0::int) \<le> (n + (1::int))) \<and> (((0::int) \<le> (n + (1::int))) \<longrightarrow> ((((0::int) * (2::int)) = (((0::int) - (1::int)) * (0::int))) \<and> ((((0::int) * (2::int)) = (((0::int) - (1::int)) * (0::int))) \<longrightarrow> ((vc_anon8_Then \<and> vc_anon9_Then i_0 res_0) \<and> vc_anon9_Else i_0 res_0))))))"
definition vc_anon0 :: bool
  where
    "vc_anon0  = (((0::int) \<le> n) \<longrightarrow> (vc_anon7_Then \<and> vc_anon7_Else))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry  = vc_anon0"

definition test :: "int \<Rightarrow> bool"
  where
    "test i = (i \<le> 4)"

definition test4
  where
    "test4 = (\<forall>(i::int). test i)"

lemma vc_correct:

shows "vc_PreconditionGeneratedEntry"
  oops


end

thm vc_passive.vc_anon7_Else_def

locale beforePassive =
fixes \<Lambda> :: var_context
assumes A1:"\<Lambda> ''n'' = Some TInt" and A2:"\<Lambda> ''i'' = Some TInt" and A3:"\<Lambda> ''res'' = Some TInt"
begin

lemmas var_assms = A1 A2 A3

lemma block_anon7_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (BinOp (Var ''res'') Mul (Val (IntV 2))) Eq (BinOp (Var ''n'') Mul (BinOp (Var ''n'') Add (Val (IntV 1)))))), 
(Assume (Val (BoolV False)))] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''i'') = (Some (IntV vc_i_0)))" and 
"((n_s ''res'') = (Some (IntV vc_res_0)))" and
"(vc_passive.vc_anon7_Then )"
shows "(s' = Magic)"
using assms
apply cases
apply (simp only: vc_passive.vc_anon7_Then_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon8_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''i'') Le (BinOp (Var ''n'') Add (Val (IntV 1))))), 
(Assume (BinOp (BinOp (Var ''res'') Mul (Val (IntV 2))) Eq (BinOp (BinOp (Var ''i'') Sub (Val (IntV 1))) Mul (Var ''i'')))), 
(Assume (Val (BoolV False)))] (Normal n_s) s')" and  
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''i'') = (Some (IntV vc_i_0)))" and 
"((n_s ''res'') = (Some (IntV vc_res_0)))" and
"(vc_passive.vc_anon8_Then )"
shows "(s' = Magic)"
using assms
apply cases
apply (simp only: vc_passive.vc_anon8_Then_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon9_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (UnOp Not (BinOp (Var ''i'') Le (Var ''n'')))), 
(Assume (BinOp (Var ''i'') Le (BinOp (Var ''n'') Add (Val (IntV 1))))), 
(Assume (BinOp (BinOp (Var ''res'') Mul (Val (IntV 2))) Eq (BinOp (BinOp (Var ''i'') Sub (Val (IntV 1))) Mul (Var ''i'')))), 
(Assert (BinOp (BinOp (Var ''res'') Mul (Val (IntV 2))) Eq (BinOp (Var ''n'') Mul (BinOp (Var ''n'') Add (Val (IntV 1))))))] (Normal n_s) s')" and  
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''i'') = (Some (IntV vc_i_0)))" and 
"((n_s ''res'') = (Some (IntV vc_res_0)))" and
"(vc_passive.vc_anon9_Else vc_n vc_i_0 vc_res_0)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms
apply cases
apply (simp only: vc_passive.vc_anon9_Else_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Val (IntV 0)) Le (Var ''n'')))] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''i'') = (Some (IntV vc_i_0)))" and 
"((n_s ''res'') = (Some (IntV vc_res_0)))" and
"(vc_passive.vc_anon0 vc_n)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc_passive.vc_anon7_Then ) \<and> (vc_passive.vc_anon7_Else vc_n))))))"
using assms
apply cases
apply (simp only: vc_passive.vc_anon0_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''i'') = (Some (IntV vc_i_0)))" and 
"((n_s ''res'') = (Some (IntV vc_res_0)))" and
"(vc_passive.vc_PreconditionGeneratedEntry vc_n)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc_passive.vc_anon0 vc_n )))))"
using assms
apply cases
apply (simp only: vc_passive.vc_PreconditionGeneratedEntry_def)
  by (auto?)


lemma block_anon7_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assign [(''res'', Val (IntV 0))]), 
(Assign [(''i'', (Val (IntV 0)))]), 
(Assert (BinOp (Var ''i'') Le (BinOp (Var ''n'') Add (Val (IntV 1))))), 
(Assert (BinOp (BinOp (Var ''res'') Mul (Val (IntV 2))) Eq (BinOp (BinOp (Var ''i'') Sub (Val (IntV 1))) Mul (Var ''i'')))), 
(Havoc ''i''), 
(Havoc ''res'')] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and
"(vc_passive.vc_anon7_Else vc_n)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (
 (n_s' ''n'' = Some (IntV vc_n)) \<and>
 (\<exists> vc_i_0 vc_res_0.
 (n_s' ''i'' = Some (IntV vc_i_0)) \<and>
 (n_s' ''res'' = Some (IntV vc_res_0)) \<and>   
 (((vc_passive.vc_anon8_Then ) \<and> (vc_passive.vc_anon9_Then vc_n vc_i_0 vc_res_0)) \<and> (vc_passive.vc_anon9_Else vc_n vc_i_0 vc_res_0)))))))"
using assms
apply cases
apply (simp only: vc_passive.vc_anon7_Else_def)
  apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)


lemma block_anon9_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''i'') Le (BinOp (Var ''n'') Add (Val (IntV 1))))), 
(Assume (BinOp (BinOp (Var ''res'') Mul (Val (IntV 2))) Eq (BinOp (BinOp (Var ''i'') Sub (Val (IntV 1))) Mul (Var ''i'')))), 
(Assume (BinOp (Var ''i'') Le (Var ''n''))), 
(Assign [(''res'', (BinOp (Var ''res'') Add (Var ''i'')))]), 
(Assign [(''i'', (BinOp (Var ''i'') Add (Val (IntV 1))))]), 
(Assert (BinOp (Var ''i'') Le (BinOp (Var ''n'') Add (Val (IntV 1))))), 
(Assert (BinOp (BinOp (Var ''res'') Mul (Val (IntV 2))) Eq (BinOp (BinOp (Var ''i'') Sub (Val (IntV 1))) Mul (Var ''i''))))
] (Normal n_s) s')" and  
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''i'') = (Some (IntV vc_i_0)))" and 
"((n_s ''res'') = (Some (IntV vc_res_0)))" and
"(vc_passive.vc_anon9_Then vc_n vc_i_0 vc_res_0)"
shows "(s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow>
(\<exists> vc_i_1 vc_res_1. 
 n_s' ''i'' = Some(IntV (vc_i_1)) \<and>
 n_s' ''res'' = Some(IntV (vc_res_1)) \<and>
 vc_passive.vc_anon9_suc vc_i_1 vc_res_1)))"
using assms
apply cases
apply (simp only: vc_passive.vc_anon9_Then_def)
apply (handle_cmd_list_full)
by (auto?)

end

end
