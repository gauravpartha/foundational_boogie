theory assign_exp
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

locale vc_passive
begin

definition vc_anon0
  where
    "vc_anon0  = (\<forall> x x1_0 x2_0 x3_0 x4_0 x5_0 x6_0 x7_0 x8_0 x9_0 x10_0. ((x > (0::int)) \<longrightarrow> (((x1_0 = (x + x)) \<and> (x2_0 = (x1_0 + x1_0))) \<longrightarrow> (((((x3_0 = (x2_0 + x2_0)) \<and> (x4_0 = (x3_0 + x3_0))) \<and> ((x5_0 = (x4_0 + x4_0)) \<and> (x6_0 = (x5_0 + x5_0)))) \<and> (((x7_0 = (x6_0 + x6_0)) \<and> (x8_0 = (x7_0 + x7_0))) \<and> ((x9_0 = (x8_0 + x8_0)) \<and> (x10_0 = (x9_0 + x9_0))))) \<longrightarrow> (x10_0 \<ge> (0::int))))))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry  = (vc_anon0 )"
lemma vc_correct:

shows "(vc_PreconditionGeneratedEntry )"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def)
oops


end

locale beforePassive = 
fixes \<Lambda> :: "(var_context)" and \<Gamma> :: "(fun_context)"
assumes 
V0: "((\<Lambda> ''x1'') = (Some TInt))" and 
V1: "((\<Lambda> ''x2'') = (Some TInt))" and 
V2: "((\<Lambda> ''x3'') = (Some TInt))" and 
V3: "((\<Lambda> ''x4'') = (Some TInt))" and 
V4: "((\<Lambda> ''x5'') = (Some TInt))" and 
V5: "((\<Lambda> ''x6'') = (Some TInt))" and 
V6: "((\<Lambda> ''x7'') = (Some TInt))" and 
V7: "((\<Lambda> ''x8'') = (Some TInt))" and 
V8: "((\<Lambda> ''x9'') = (Some TInt))" and 
V9: "((\<Lambda> ''x10'') = (Some TInt))" and 
V10: "((\<Lambda> ''x'') = (Some TInt))"
begin

lemmas var_assms = V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10
lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''x'') Gt (Val (IntV 0)))), 
(Assign [(''x1'', (BinOp (Var ''x'') Add (Var ''x'')))]), 
(Assign [(''x2'', (BinOp (Var ''x1'') Add (Var ''x1'')))]), 
(Assign [(''x3'', (BinOp (Var ''x2'') Add (Var ''x2'')))]), 
(Assign [(''x4'', (BinOp (Var ''x3'') Add (Var ''x3'')))]), 
(Assign [(''x5'', (BinOp (Var ''x4'') Add (Var ''x4'')))]), 
(Assign [(''x6'', (BinOp (Var ''x5'') Add (Var ''x5'')))]), 
(Assign [(''x7'', (BinOp (Var ''x6'') Add (Var ''x6'')))]), 
(Assign [(''x8'', (BinOp (Var ''x7'') Add (Var ''x7'')))]), 
(Assign [(''x9'', (BinOp (Var ''x8'') Add (Var ''x8'')))]), 
(Assign [(''x10'', (BinOp (Var ''x9'') Add (Var ''x9'')))]), 
(Assert (BinOp (Var ''x10'') Ge (Val (IntV 0))))] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_anon0 )" and 
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
shows "(s' \<noteq> Failure)"
using assms 
apply cases
  apply (simp only: vc_passive.vc_anon0_def)
  (*apply (handle_cmd_list_full v_assms: var_assms)?*)
  apply (handle_assume_full)
  apply (erule RedCmdListCons_case, handle_assign_full)+
  apply (erule RedCmdListCons_case)
  apply (drule assert_correct_2)
  apply assumption
  apply (rule RedBinOp)
   apply (rule RedVar)
   apply fastforce
  apply (rule RedVal)
  apply fastforce
  by auto
  
lemma block_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_anon0 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_x. (((n_s' ''x'') = (Some (IntV vc_x))) \<and> (vc_passive.vc_anon0 ))))))"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_PreconditionGeneratedEntry )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_x. (((n_s' ''x'') = (Some (IntV vc_x))) \<and> (vc_passive.vc_anon0 ))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_PreconditionGeneratedEntry_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)


end


end
