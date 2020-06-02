theory goto_nested
imports Semantics Util
begin
locale vc
begin

definition vc_finalBlock
  where
    "vc_finalBlock i_6 = ((i_6 + (1::int)) > (1::int))"
definition vc_afterLoop
  where
    "vc_afterLoop i_1 n i_6 = (((i_1 \<ge> n) \<and> (i_6 = i_1)) \<longrightarrow> (vc_finalBlock i_6))"
definition vc_loopBodyEnd
  where
    "vc_loopBodyEnd j_2 n i_4 i_2 k = (((j_2 \<ge> n) \<and> (i_4 = (i_2 + k))) \<longrightarrow> (i_4 > (0::int)))"
definition vc_loopBodyNestedEnd
  where
    "vc_loopBodyNestedEnd i_5 i_3 j_2 j_3 = (((i_5 = ((i_3 + j_2) + (1::int))) \<and> (j_3 = (j_2 + (1::int)))) \<longrightarrow> ((i_5 > (0::int)) \<and> ((i_5 > (0::int)) \<longrightarrow> (j_3 > (0::int)))))"
definition vc_loopBodyNestedStart__2_loopHead
  where
    "vc_loopBodyNestedStart__2_loopHead i_3 = (i_3 > (0::int))"
definition vc_loopBodyNestedStart__2_finalBlock
  where
    "vc_loopBodyNestedStart__2_finalBlock i_6 i_3 = ((i_6 = i_3) \<longrightarrow> (vc_finalBlock i_6))"
definition vc_loopBodyNestedStart
  where
    "vc_loopBodyNestedStart j_2 n i_3 i_2 i_5 j_3 i_6 = (((j_2 < n) \<and> (i_3 = (i_2 + (1::int)))) \<longrightarrow> (((vc_loopBodyNestedEnd i_5 i_3 j_2 j_3) \<and> (vc_loopBodyNestedStart__2_loopHead i_3)) \<and> (vc_loopBodyNestedStart__2_finalBlock i_6 i_3)))"
definition vc_loopHeadNested
  where
    "vc_loopHeadNested i_2 j_2 n i_3 i_5 j_3 i_6 i_4 k = (((i_2 > (0::int)) \<and> (j_2 > (0::int))) \<longrightarrow> ((vc_loopBodyNestedStart j_2 n i_3 i_2 i_5 j_3 i_6) \<and> (vc_loopBodyEnd j_2 n i_4 i_2 k)))"
definition vc_loopBodyStart
  where
    "vc_loopBodyStart i_1 n j_1 i_2 j_2 i_3 i_5 j_3 i_6 i_4 k = (((i_1 < n) \<and> (j_1 > (0::int))) \<longrightarrow> ((i_1 > (0::int)) \<and> ((i_1 > (0::int)) \<longrightarrow> ((j_1 > (0::int)) \<and> ((j_1 > (0::int)) \<longrightarrow> (vc_loopHeadNested i_2 j_2 n i_3 i_5 j_3 i_6 i_4 k))))))"
definition vc_loopHead
  where
    "vc_loopHead i_1 n j_1 i_2 j_2 i_3 i_5 j_3 i_6 i_4 k = ((i_1 > (0::int)) \<longrightarrow> ((vc_loopBodyStart i_1 n j_1 i_2 j_2 i_3 i_5 j_3 i_6 i_4 k) \<and> (vc_afterLoop i_1 n i_6)))"
definition vc_anon0
  where
    "vc_anon0 k i_0 i_1 n j_1 i_2 j_2 i_3 i_5 j_3 i_6 i_4 = (((k \<ge> (0::int)) \<and> (i_0 = (k + (1::int)))) \<longrightarrow> ((i_0 > (0::int)) \<and> ((i_0 > (0::int)) \<longrightarrow> (vc_loopHead i_1 n j_1 i_2 j_2 i_3 i_5 j_3 i_6 i_4 k))))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry k i_0 i_1 n j_1 i_2 j_2 i_3 i_5 j_3 i_6 i_4 = (vc_anon0 k i_0 i_1 n j_1 i_2 j_2 i_3 i_5 j_3 i_6 i_4)"
lemma vc_correct:

shows "(vc_PreconditionGeneratedEntry k i_0 i_1 n j_1 i_2 j_2 i_3 i_5 j_3 i_6 i_4)"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def vc_loopHead_def vc_loopBodyStart_def vc_loopHeadNested_def vc_loopBodyNestedStart_def vc_loopBodyNestedStart__2_finalBlock_def vc_loopBodyNestedStart__2_loopHead_def vc_loopBodyNestedEnd_def vc_loopBodyEnd_def vc_afterLoop_def vc_finalBlock_def)
oops


end

locale vc_passive
begin

definition vc_finalBlock
  where
    "vc_finalBlock i_6 = ((i_6 + (1::int)) > (1::int))"
definition vc_afterLoop
  where
    "vc_afterLoop i_1 = (\<forall> n i_6. (((i_1 \<ge> n) \<and> (i_6 = i_1)) \<longrightarrow> (vc_finalBlock i_6)))"
definition vc_loopBodyEnd
  where
    "vc_loopBodyEnd j_2 n i_2 k = (\<forall> i_4. (((j_2 \<ge> n) \<and> (i_4 = (i_2 + k))) \<longrightarrow> (i_4 > (0::int))))"
definition vc_loopBodyNestedEnd
  where
    "vc_loopBodyNestedEnd i_3 j_2 = (\<forall> i_5 j_3. (((i_5 = ((i_3 + j_2) + (1::int))) \<and> (j_3 = (j_2 + (1::int)))) \<longrightarrow> ((i_5 > (0::int)) \<and> ((i_5 > (0::int)) \<longrightarrow> (j_3 > (0::int))))))"
definition vc_loopBodyNestedStart__2_loopHead
  where
    "vc_loopBodyNestedStart__2_loopHead i_3 = (i_3 > (0::int))"
definition vc_loopBodyNestedStart__2_finalBlock
  where
    "vc_loopBodyNestedStart__2_finalBlock i_3 = (\<forall> i_6. ((i_6 = i_3) \<longrightarrow> (vc_finalBlock i_6)))"
definition vc_loopBodyNestedStart
  where
    "vc_loopBodyNestedStart j_2 n i_2 = (\<forall> i_3. (((j_2 < n) \<and> (i_3 = (i_2 + (1::int)))) \<longrightarrow> (((vc_loopBodyNestedEnd i_3 j_2) \<and> (vc_loopBodyNestedStart__2_loopHead i_3)) \<and> (vc_loopBodyNestedStart__2_finalBlock i_3))))"
definition vc_loopHeadNested
  where
    "vc_loopHeadNested n k = (\<forall> i_2 j_2. (((i_2 > (0::int)) \<and> (j_2 > (0::int))) \<longrightarrow> ((vc_loopBodyNestedStart j_2 n i_2) \<and> (vc_loopBodyEnd j_2 n i_2 k))))"
definition vc_loopBodyStart
  where
    "vc_loopBodyStart i_1 k = (\<forall> n j_1. (((i_1 < n) \<and> (j_1 > (0::int))) \<longrightarrow> ((i_1 > (0::int)) \<and> ((i_1 > (0::int)) \<longrightarrow> ((j_1 > (0::int)) \<and> ((j_1 > (0::int)) \<longrightarrow> (vc_loopHeadNested n k)))))))"
definition vc_loopHead
  where
    "vc_loopHead k = (\<forall> i_1. ((i_1 > (0::int)) \<longrightarrow> ((vc_loopBodyStart i_1 k) \<and> (vc_afterLoop i_1))))"
definition vc_anon0
  where
    "vc_anon0  = (\<forall> k i_0. (((k \<ge> (0::int)) \<and> (i_0 = (k + (1::int)))) \<longrightarrow> ((i_0 > (0::int)) \<and> ((i_0 > (0::int)) \<longrightarrow> (vc_loopHead k)))))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry  = (vc_anon0 )"
lemma vc_correct:

shows "(vc_PreconditionGeneratedEntry )"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def vc_loopHead_def vc_loopBodyStart_def vc_loopHeadNested_def vc_loopBodyNestedStart_def vc_loopBodyNestedStart__2_finalBlock_def vc_loopBodyNestedStart__2_loopHead_def vc_loopBodyNestedEnd_def vc_loopBodyEnd_def vc_afterLoop_def vc_finalBlock_def)
oops


end

locale beforePassive = 
fixes \<Lambda> :: "(var_context)" and \<Gamma> :: "(fun_context)"
assumes 
V0: "((\<Lambda> ''i'') = (Some TInt))" and 
V1: "((\<Lambda> ''j'') = (Some TInt))" and 
V2: "((\<Lambda> ''n'') = (Some TInt))" and 
V3: "((\<Lambda> ''k'') = (Some TInt))"
begin

lemmas var_assms = V0 V1 V2 V3
lemma block_GeneratedUnifiedExit:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')"
shows "(s' \<noteq> Failure)"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_finalBlock:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assert (BinOp (BinOp (Var ''i'') Add (Val (IntV 1))) Gt (Val (IntV 1))))] (Normal n_s) s')" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"(vc_passive.vc_finalBlock vc_i)"
shows "(s' \<noteq> Failure)"
using assms 
apply cases
apply (simp only: vc_passive.vc_finalBlock_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_afterLoop:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''i'') Ge (Var ''n'')))] (Normal n_s) s')" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"(vc_passive.vc_afterLoop vc_i)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_i. (((n_s' ''i'') = (Some (IntV vc_i))) \<and> (vc_passive.vc_finalBlock vc_i))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_afterLoop_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_loopBodyEnd:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''j'') Ge (Var ''n''))), 
(Assign [(''i'', (BinOp (Var ''i'') Add (Var ''k'')))]), 
(Assert (BinOp (Var ''i'') Gt (Val (IntV 0)))), 
(Assume (Val (BoolV False)))] (Normal n_s) s')" and 
"((n_s ''j'') = (Some (IntV vc_j)))" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"((n_s ''k'') = (Some (IntV vc_k)))" and 
"(vc_passive.vc_loopBodyEnd vc_j vc_n vc_i vc_k)"
shows "(s' = Magic)"
using assms 
apply cases
apply (simp only: vc_passive.vc_loopBodyEnd_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_loopBodyNestedEnd:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assign [(''i'', (BinOp (BinOp (Var ''i'') Add (Var ''j'')) Add (Val (IntV 1))))]), 
(Assign [(''j'', (BinOp (Var ''j'') Add (Val (IntV 1))))]), 
(Assert (BinOp (Var ''i'') Gt (Val (IntV 0)))), 
(Assert (BinOp (Var ''j'') Gt (Val (IntV 0)))), 
(Assume (Val (BoolV False)))] (Normal n_s) s')" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"((n_s ''j'') = (Some (IntV vc_j)))" and 
"(vc_passive.vc_loopBodyNestedEnd vc_i vc_j)"
shows "(s' = Magic)"
using assms 
apply cases
apply (simp only: vc_passive.vc_loopBodyNestedEnd_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_loopBodyNestedStart__2_loopHead:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assert (BinOp (Var ''i'') Gt (Val (IntV 0)))), 
(Assume (Val (BoolV False)))] (Normal n_s) s')" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"(vc_passive.vc_loopBodyNestedStart__2_loopHead vc_i)"
shows "(s' = Magic)"
using assms 
apply cases
apply (simp only: vc_passive.vc_loopBodyNestedStart__2_loopHead_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_loopBodyNestedStart__2_finalBlock:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"(vc_passive.vc_loopBodyNestedStart__2_finalBlock vc_i)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_i. (((n_s' ''i'') = (Some (IntV vc_i))) \<and> (vc_passive.vc_finalBlock vc_i))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_loopBodyNestedStart__2_finalBlock_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_loopBodyNestedStart:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''j'') Lt (Var ''n''))), 
(Assign [(''i'', (BinOp (Var ''i'') Add (Val (IntV 1))))])] (Normal n_s) s')" and 
"((n_s ''j'') = (Some (IntV vc_j)))" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"(vc_passive.vc_loopBodyNestedStart vc_j vc_n vc_i)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_i vc_j. ((((n_s' ''i'') = (Some (IntV vc_i))) \<and> ((n_s' ''j'') = (Some (IntV vc_j)))) \<and> (((vc_passive.vc_loopBodyNestedEnd vc_i vc_j) \<and> (vc_passive.vc_loopBodyNestedStart__2_loopHead vc_i)) \<and> (vc_passive.vc_loopBodyNestedStart__2_finalBlock vc_i)))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_loopBodyNestedStart_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_loopHeadNested:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Havoc ''i''), 
(Havoc ''j''), 
(Assume (BinOp (Var ''i'') Gt (Val (IntV 0)))), 
(Assume (BinOp (Var ''j'') Gt (Val (IntV 0))))] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''k'') = (Some (IntV vc_k)))" and 
"(vc_passive.vc_loopHeadNested vc_n vc_k)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_j vc_n vc_i vc_k. ((((((n_s' ''j'') = (Some (IntV vc_j))) \<and> ((n_s' ''n'') = (Some (IntV vc_n)))) \<and> ((n_s' ''i'') = (Some (IntV vc_i)))) \<and> ((n_s' ''k'') = (Some (IntV vc_k)))) \<and> ((vc_passive.vc_loopBodyNestedStart vc_j vc_n vc_i) \<and> (vc_passive.vc_loopBodyEnd vc_j vc_n vc_i vc_k)))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_loopHeadNested_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_loopBodyStart:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''i'') Lt (Var ''n''))), 
(Havoc ''j''), 
(Assume (BinOp (Var ''j'') Gt (Val (IntV 0)))), 
(Assert (BinOp (Var ''i'') Gt (Val (IntV 0)))), 
(Assert (BinOp (Var ''j'') Gt (Val (IntV 0))))] (Normal n_s) s')" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"((n_s ''k'') = (Some (IntV vc_k)))" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"(vc_passive.vc_loopBodyStart vc_i vc_k)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_n vc_k. ((((n_s' ''n'') = (Some (IntV vc_n))) \<and> ((n_s' ''k'') = (Some (IntV vc_k)))) \<and> (vc_passive.vc_loopHeadNested vc_n vc_k))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_loopBodyStart_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by fastforce

lemma block_loopHead:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Havoc ''i''), 
(Havoc ''j''), 
(Assume (BinOp (Var ''i'') Gt (Val (IntV 0))))] (Normal n_s) s')" and 
"((n_s ''k'') = (Some (IntV vc_k)))" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"(vc_passive.vc_loopHead vc_k)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_i vc_k vc_n. (((((n_s' ''i'') = (Some (IntV vc_i))) \<and> ((n_s' ''k'') = (Some (IntV vc_k)))) \<and> ((n_s' ''n'') = (Some (IntV vc_n)))) \<and> ((vc_passive.vc_loopBodyStart vc_i vc_k) \<and> (vc_passive.vc_afterLoop vc_i)))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_loopHead_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''k'') Ge (Val (IntV 0)))), 
(Assign [(''i'', (BinOp (Var ''k'') Add (Val (IntV 1))))]), 
(Assert (BinOp (Var ''i'') Gt (Val (IntV 0))))] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''k'') = (Some (IntV vc_k)))" and 
"(vc_passive.vc_anon0 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_k vc_n. ((((n_s' ''k'') = (Some (IntV vc_k))) \<and> ((n_s' ''n'') = (Some (IntV vc_n)))) \<and> (vc_passive.vc_loopHead vc_k))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon0_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''k'') = (Some (IntV vc_k)))" and 
"(vc_passive.vc_anon0 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_n vc_k. ((((n_s' ''n'') = (Some (IntV vc_n))) \<and> ((n_s' ''k'') = (Some (IntV vc_k)))) \<and> (vc_passive.vc_anon0 ))))))"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''k'') = (Some (IntV vc_k)))" and 
"(vc_passive.vc_PreconditionGeneratedEntry )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_n vc_k. ((((n_s' ''n'') = (Some (IntV vc_n))) \<and> ((n_s' ''k'') = (Some (IntV vc_k)))) \<and> (vc_passive.vc_anon0 ))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_PreconditionGeneratedEntry_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)


end

locale progLocale
begin

fun outEdges_goto_nested
  where
    "outEdges_goto_nested (Suc(Suc(Suc(Suc(Suc(Suc(Suc(Suc(0))))))))) = {(Suc(Suc(Suc(Suc(Suc(0))))))}"
    |"outEdges_goto_nested (Suc(Suc(Suc(Suc(Suc(Suc(Suc(0)))))))) = {(Suc(Suc(Suc(Suc(Suc(Suc(Suc(Suc(0))))))))), (Suc(0)), (Suc(Suc(Suc(0))))}"
    |"outEdges_goto_nested (Suc(Suc(Suc(Suc(Suc(Suc(0))))))) = {(Suc(0))}"
    |"outEdges_goto_nested (Suc(Suc(Suc(Suc(Suc(0)))))) = {(Suc(Suc(Suc(Suc(Suc(Suc(Suc(0)))))))), (Suc(Suc(Suc(Suc(Suc(Suc(0)))))))}"
    |"outEdges_goto_nested (Suc(Suc(Suc(Suc(0))))) = {(Suc(Suc(Suc(Suc(Suc(0))))))}"
    |"outEdges_goto_nested (Suc(Suc(Suc(0)))) = {}"
    |"outEdges_goto_nested (Suc(Suc(0))) = {(Suc(Suc(Suc(0))))}"
    |"outEdges_goto_nested (Suc(0)) = {(Suc(Suc(Suc(Suc(0))))), (Suc(Suc(0)))}"
    |"outEdges_goto_nested (0) = {(Suc(0))}"
    |"outEdges_goto_nested _ = {}"
fun nodeToBlocks_goto_nested
  where
    "nodeToBlocks_goto_nested (Suc(Suc(Suc(Suc(Suc(Suc(Suc(Suc(0))))))))) = (Some [(Assign [(''i'', (BinOp (BinOp (Var ''i'') Add (Var ''j'')) Add (Val (IntV 1))))]), 
(Assign [(''j'', (BinOp (Var ''j'') Add (Val (IntV 1))))])])"
    |"nodeToBlocks_goto_nested (Suc(Suc(Suc(Suc(Suc(Suc(Suc(0)))))))) = (Some [(Assume (BinOp (Var ''j'') Lt (Var ''n''))), 
(Assign [(''i'', (BinOp (Var ''i'') Add (Val (IntV 1))))])])"
    |"nodeToBlocks_goto_nested (Suc(Suc(Suc(Suc(Suc(Suc(0))))))) = (Some [(Assume (BinOp (Var ''j'') Ge (Var ''n''))), 
(Assign [(''i'', (BinOp (Var ''i'') Add (Var ''k'')))])])"
    |"nodeToBlocks_goto_nested (Suc(Suc(Suc(Suc(Suc(0)))))) = (Some [(Assert (BinOp (Var ''i'') Gt (Val (IntV 0)))), 
(Assert (BinOp (Var ''j'') Gt (Val (IntV 0))))])"
    |"nodeToBlocks_goto_nested (Suc(Suc(Suc(Suc(0))))) = (Some [(Assume (BinOp (Var ''i'') Lt (Var ''n''))), 
(Havoc ''j''), 
(Assume (BinOp (Var ''j'') Gt (Val (IntV 0))))])"
    |"nodeToBlocks_goto_nested (Suc(Suc(Suc(0)))) = (Some [(Assert (BinOp (BinOp (Var ''i'') Add (Val (IntV 1))) Gt (Val (IntV 1))))])"
    |"nodeToBlocks_goto_nested (Suc(Suc(0))) = (Some [(Assume (BinOp (Var ''i'') Ge (Var ''n'')))])"
    |"nodeToBlocks_goto_nested (Suc(0)) = (Some [(Assert (BinOp (Var ''i'') Gt (Val (IntV 0))))])"
    |"nodeToBlocks_goto_nested (0) = (Some [(Assume (BinOp (Var ''k'') Ge (Val (IntV 0)))), 
(Assign [(''i'', (BinOp (Var ''k'') Add (Val (IntV 1))))])])"
    |"nodeToBlocks_goto_nested _ = (None )"
fun funDecl_goto_nested
  where
    "funDecl_goto_nested _ = (None )"
fun inParams_goto_nested
  where
    "inParams_goto_nested ''n'' = (Some TInt)"
    |"inParams_goto_nested ''k'' = (Some TInt)"
    |"inParams_goto_nested _ = (None )"
fun localVars_goto_nested
  where
    "localVars_goto_nested ''i'' = (Some TInt)"
    |"localVars_goto_nested ''j'' = (Some TInt)"
    |"localVars_goto_nested _ = (None )"
definition ProgramM
  where
    "ProgramM  = (Program funDecl_goto_nested [(''goto_nested'', inParams_goto_nested, localVars_goto_nested, (|entry = 0, nodes = {(Suc(Suc(Suc(Suc(Suc(Suc(Suc(Suc(0))))))))), (Suc(Suc(Suc(Suc(Suc(Suc(Suc(0)))))))), (Suc(Suc(Suc(Suc(Suc(Suc(0))))))), (Suc(Suc(Suc(Suc(Suc(0)))))), (Suc(Suc(Suc(Suc(0))))), (Suc(Suc(Suc(0)))), (Suc(Suc(0))), (Suc(0)), (0)}, out_edges = outEdges_goto_nested, node_to_block = nodeToBlocks_goto_nested|))])"

abbreviation Entry
  where "Entry \<equiv> 0"

abbreviation LH
  where "LH \<equiv> Suc(0)"

abbreviation AfterLoop
  where "AfterLoop \<equiv> Suc(Suc 0)"

abbreviation Exit
  where "Exit \<equiv> Suc(Suc(Suc 0))"

abbreviation LB_1
  where "LB_1 \<equiv> Suc(Suc(Suc(Suc 0)))"

abbreviation LHN
  where "LHN \<equiv> (Suc(Suc(Suc(Suc(Suc(0))))))"

abbreviation LB_2
  where "LB_2 \<equiv> Suc(Suc(Suc(Suc(Suc(Suc(0))))))"

abbreviation LBN_1
  where "LBN_1 \<equiv> Suc(Suc(Suc(Suc(Suc(Suc(Suc(0)))))))"

abbreviation LBN_2
  where "LBN_2 \<equiv> (Suc(Suc(Suc(Suc(Suc(Suc(Suc(Suc(0)))))))))"

lemma finalBlock_correct: 
  assumes A1:"\<Lambda>, \<Gamma>, G \<turnstile> (Inl Exit, Normal n_s) -n\<rightarrow>* (m, s')" and
   A2:"((n_s ''i'') = (Some (IntV vc_i)))" and 
   A3:"((n_s ''n'') = (Some (IntV vc_n)))" and 
   A4: "(vc_passive.vc_finalBlock vc_i)"
  shows "s' \<noteq> Failure"
  using A1
  oops
(*proof (cases rule: converse_rtranclpE)*)

lemma afterLoop_correct:
  assumes A1:"\<Lambda>, \<Gamma>, G \<turnstile> (Inl AfterLoop, Normal n_s) -n\<rightarrow>* (m, s')" and
   A2:"((n_s ''i'') = (Some (IntV vc_i)))" and 
   A3:"((n_s ''n'') = (Some (IntV vc_n)))" and 
   A4: "(vc_passive.vc_afterLoop vc_i)"
 shows "s' \<noteq> Failure"
  oops

lemma loopBodyNested_correct:
assumes A1:"\<Lambda>, \<Gamma>, G \<turnstile> (Inl LBN_1, Normal n_s) -n\<rightarrow>* (m, s')" and
   "((n_s ''i'') = (Some (IntV vc_i)))" and 
   "((n_s ''n'') = (Some (IntV vc_n)))" and 
   "((n_s ''k'') = (Some (IntV vc_k)))" and
   "((n_s ''j'') = (Some (IntV vc_j)))" and
   "(vc_passive.vc_loopBodyNestedStart vc_j vc_n vc_i)" and
  IH_outer: "\<And>k' ns2 vc_i'. k' \<le> j \<Longrightarrow>
    \<Lambda>,\<Gamma>,G \<turnstile>(Inl LH, Normal ns2) -n\<rightarrow>^k' (m', s') \<Longrightarrow>
    ns2 ''n'' = Some (IntV vc_n) \<Longrightarrow> ((ns2 ''k'') = (Some (IntV vc_k))) \<Longrightarrow>
    ns2 ''i'' = Some (IntV vc_i') \<Longrightarrow>
    \<Gamma> \<turnstile> \<langle>Var ''i'' \<guillemotleft>Gt\<guillemotright> (Val (IntV 0)),ns2\<rangle> \<Down> BoolV True \<Longrightarrow> s' \<noteq> Failure"
  IH_inner: 
shows "s' \<noteq> Failure"


lemma loopHeadNested_correct:
  assumes A1: "\<Lambda>, \<Gamma>, G \<turnstile> (Inl LHN, Normal n_s) -n\<rightarrow>^j (m', s')" and
   A2:"((n_s ''i'') = (Some (IntV vc_i)))" and 
   A3:"((n_s ''k'') = (Some (IntV vc_k)))" and 
   A4:"((n_s ''n'') = (Some (IntV vc_n)))" and
   A5: "n_s ''j'' = Some (IntV vc_j)" and
      "vc_passive.vc_loopHeadNested vc_n vc_k" and
   Inv1: "\<Gamma> \<turnstile> \<langle>Var ''i'' \<guillemotleft>Gt\<guillemotright> (Val (IntV 0)), n_s\<rangle> \<Down> BoolV True" and
   Inv2: "\<Gamma> \<turnstile> \<langle>Var ''j'' \<guillemotleft>Gt\<guillemotright> (Val (IntV 0)), n_s\<rangle> \<Down> BoolV True" and 
   IH_outer: "\<And>k' ns2 vc_i'. k' \<le> j \<Longrightarrow>
    \<Lambda>,\<Gamma>,G \<turnstile>(Inl LH, Normal ns2) -n\<rightarrow>^k' (m', s') \<Longrightarrow>
    ns2 ''n'' = Some (IntV vc_n) \<Longrightarrow> ((ns2 ''k'') = (Some (IntV vc_k))) \<Longrightarrow>
    ns2 ''i'' = Some (IntV vc_i') \<Longrightarrow>
    \<Gamma> \<turnstile> \<langle>Var ''i'' \<guillemotleft>Gt\<guillemotright> (Val (IntV 0)),ns2\<rangle> \<Down> BoolV True \<Longrightarrow> s' \<noteq> Failure"
   shows "s' \<noteq> Failure"
  using assms
  proof(induction j arbitrary: n_s vc_i vc_j rule: less_induct)
  case (less x ns')
  show ?case
  proof (cases x)
    case 0
    with less.prems(1) show ?thesis by auto
  next
    case (Suc k)
    with less.prems(1) obtain z where 
        "(\<Lambda>, \<Gamma>, G \<turnstile> (Inl LHN, Normal ns') -n\<rightarrow> z)" and B2:"(\<Lambda>, \<Gamma>, G \<turnstile> z -n\<rightarrow>^k (m', s'))"
      by (meson relpowp_Suc_E2)
    from B2 have B3:"(\<Lambda>, \<Gamma>, G \<turnstile> z -n\<rightarrow>* (m', s'))" by (meson relpowp_imp_rtranclp)
    (*from \<open>x = Suc k\<close> and less.IH*) have
     IH2: "\<And>k' ns2 vc_i' vc_j'. k' \<le> k \<Longrightarrow>
    \<Lambda>,\<Gamma>,G \<turnstile>(Inl LHN, Normal ns2) -n\<rightarrow>^k' (m', s') \<Longrightarrow>
    ns2 ''n'' = Some (IntV vc_n) \<Longrightarrow> ((ns2 ''k'') = (Some (IntV vc_k))) \<Longrightarrow>
    ns2 ''i'' = Some (IntV vc_i') \<Longrightarrow> ((ns2 ''j'') = (Some (IntV vc_j'))) \<Longrightarrow>
    \<Gamma> \<turnstile> \<langle>Var ''i'' \<guillemotleft>Gt\<guillemotright> (Val (IntV 0)),ns2\<rangle> \<Down> BoolV True \<Longrightarrow> 
    \<Gamma> \<turnstile> \<langle>Var ''j'' \<guillemotleft>Gt\<guillemotright> (Val (IntV 0)),ns2\<rangle> \<Down> BoolV True \<Longrightarrow>
    s' \<noteq> Failure"
    proof -
      fix k' ns2 vc_i' vc_j'
      assume C2:"k' \<le> k"
      "\<Lambda>,\<Gamma>,G \<turnstile>(Inl LHN, Normal ns2) -n\<rightarrow>^k' (m', s')"
     "ns2 ''n'' = Some (IntV vc_n)"
      "((ns2 ''k'') = (Some (IntV vc_k)))"
     "ns2 ''i'' = Some (IntV vc_i')"
      "((ns2 ''j'') = (Some (IntV vc_j')))"
      "\<Gamma> \<turnstile> \<langle>Var ''i'' \<guillemotleft>Gt\<guillemotright> (Val (IntV 0)),ns2\<rangle> \<Down> BoolV True"
      "\<Gamma> \<turnstile> \<langle>Var ''j'' \<guillemotleft>Gt\<guillemotright> (Val (IntV 0)),ns2\<rangle> \<Down> BoolV True"
      show "s' \<noteq> Failure"
      proof (rule less.IH)
        from \<open>k' \<le> k\<close> \<open>x = Suc k\<close> show "k' < x" by simp
      next
        from C2 show "\<Lambda>,\<Gamma>,G \<turnstile>(Inl LHN, Normal ns2) -n\<rightarrow>^k' (m', s')" by simp
      next
        from C2 show "ns2 ''i'' = Some (IntV vc_i')" by simp
      next 
        from C2 show "ns2 ''k'' = Some (IntV vc_k)" by simp
      next
        from C2 show "ns2 ''n'' = Some (IntV vc_n)" by simp
      next
        from C2 show "ns2 ''j'' = Some (IntV vc_j')" by simp
      next
        from less.prems show \<open>vc_passive.vc_loopHeadNested vc_n vc_k\<close> by simp
      next
        from C2 show "\<Gamma> \<turnstile> \<langle>Var ''i'' \<guillemotleft>Gt\<guillemotright> Val (IntV 0),ns2\<rangle> \<Down> BoolV True" by simp
      next
        from C2 show "\<Gamma> \<turnstile> \<langle>Var ''j'' \<guillemotleft>Gt\<guillemotright> Val (IntV 0),ns2\<rangle> \<Down> BoolV True" by simp
      next
        fix k'' ns2'' vc_i''
        assume C2: "k'' \<le> k'"
                   "\<Lambda>,\<Gamma>,G \<turnstile>(Inl (Suc 0), Normal ns2'') -n\<rightarrow>^k'' (m', s')"
                   "ns2'' ''n'' = Some (IntV vc_n)"
                   "ns2'' ''k'' = Some (IntV vc_k)"
                   "ns2'' ''i'' = Some (IntV vc_i'')"
                   "\<Gamma> \<turnstile> \<langle>Var ''i'' \<guillemotleft>Gt\<guillemotright> Val (IntV 0),ns2''\<rangle> \<Down> BoolV True"
        show "s' \<noteq> Failure"
          apply (rule less.prems(9)[of k''])
          using \<open>k'' \<le> k'\<close> \<open>k' \<le> k\<close> \<open>x = Suc k\<close>
               apply simp
          using C2 
          by simp_all
      qed
    qed
    oops
lemma loopBodyStart_correct:
  assumes A1:"\<Lambda>, \<Gamma>, G \<turnstile> (Inl LB_1, Normal n_s) -n\<rightarrow>^j (m', s')" and
   A2:"((n_s ''i'') = (Some (IntV vc_i)))" and 
   A2:"((n_s ''k'') = (Some (IntV vc_k)))" and 
   A3:"((n_s ''n'') = (Some (IntV vc_n)))" and 
   "vc_passive.vc_loopBodyStart vc_i vc_k" and
   IH: "\<And>k' ns2 vc_i'. k' \<le> j \<Longrightarrow>
    \<Lambda>,\<Gamma>,G \<turnstile>(Inl LH, Normal ns2) -n\<rightarrow>^k' (m', s') \<Longrightarrow>
    ns2 ''n'' = Some (IntV vc_n) \<Longrightarrow> ((ns2 ''k'') = (Some (IntV vc_k))) \<Longrightarrow>
    ns2 ''i'' = Some (IntV vc_i') \<Longrightarrow>
    \<Gamma> \<turnstile> \<langle>Var ''i'' \<guillemotleft>Gt\<guillemotright> (Val (IntV 0)),ns2\<rangle> \<Down> BoolV True \<Longrightarrow> s' \<noteq> Failure"
 shows "s' \<noteq> Failure"
  oops

lemma loopHead_correct:
  assumes A1:"\<Lambda>, \<Gamma>, G \<turnstile> (Inl LH, Normal n_s) -n\<rightarrow>^j (m', s')" and
   A2:"((n_s ''i'') = (Some (IntV vc_i)))" and 
   A2:"((n_s ''k'') = (Some (IntV vc_k)))" and 
   A3:"((n_s ''n'') = (Some (IntV vc_n)))" and 
   "vc_passive.vc_loopHead vc_k" and
   "\<Gamma> \<turnstile> \<langle>(BinOp (Var ''i'') Gt (Val (IntV 0))), n_s\<rangle> \<Down> BoolV True"
 shows "s' \<noteq> Failure"
  using assms
  proof(induction j arbitrary: n_s vc_i rule: less_induct)
  case (less x ns')
  show ?case
  proof (cases x)
    case 0
    with less.prems(1) show ?thesis by auto
  next
    case (Suc k)
    with less.prems(1) obtain z where 
        "(\<Lambda>, \<Gamma>, G \<turnstile> (Inl LH, Normal ns') -n\<rightarrow> z)" and A2:"(\<Lambda>, \<Gamma>, G \<turnstile> z -n\<rightarrow>^k (m', s'))"
      by (meson relpowp_Suc_E2)
    from A2 have A3:"(\<Lambda>, \<Gamma>, G \<turnstile> z -n\<rightarrow>* (m', s'))" by (meson relpowp_imp_rtranclp)
    from \<open>x = Suc k\<close> and less.IH have
     IH2: "\<And>k' ns2 vc_i'. k' \<le> k \<Longrightarrow>
    \<Lambda>,\<Gamma>,G \<turnstile>(Inl LH, Normal ns2) -n\<rightarrow>^k' (m', s') \<Longrightarrow>
    ns2 ''n'' = Some (IntV vc_n) \<Longrightarrow> ((ns2 ''k'') = (Some (IntV vc_k))) \<Longrightarrow>
    ns2 ''i'' = Some (IntV vc_i') \<Longrightarrow>
    \<Gamma> \<turnstile> \<langle>Var ''i'' \<guillemotleft>Gt\<guillemotright> (Val (IntV 0)),ns2\<rangle> \<Down> BoolV True \<Longrightarrow> s' \<noteq> Failure"
      by (meson le_imp_less_Suc less.prems(5))
oops


end


end
