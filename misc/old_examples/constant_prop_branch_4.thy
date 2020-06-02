theory constant_prop_branch_4
imports Semantics Util
begin
locale vc
begin

definition vc_anon3_Then
  where
    "vc_anon3_Then  = (((0::int) + (0::int)) \<ge> (0::int))"
definition vc_anon3_Else
  where
    "vc_anon3_Else z = (z \<ge> (0::int))"
definition vc_anon0
  where
    "vc_anon0 z = ((z \<ge> (0::int)) \<longrightarrow> ((vc_anon3_Then ) \<and> (vc_anon3_Else z)))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry z = (vc_anon0 z)"
lemma vc_correct:

shows "(vc_PreconditionGeneratedEntry z)"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def vc_anon3_Else_def vc_anon3_Then_def)
oops


end

locale vc_passive
begin

definition vc_anon3_Then
  where
    "vc_anon3_Then  = (((0::int) + (0::int)) \<ge> (0::int))"
definition vc_anon3_Else
  where
    "vc_anon3_Else z = (z \<ge> (0::int))"
definition vc_anon0
  where
    "vc_anon0  = (\<forall> z. ((z \<ge> (0::int)) \<longrightarrow> ((vc_anon3_Then ) \<and> (vc_anon3_Else z))))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry  = (vc_anon0 )"
lemma vc_correct:

shows "(vc_PreconditionGeneratedEntry )"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def vc_anon3_Else_def vc_anon3_Then_def)
oops


end

locale beforePassive = 
fixes \<Lambda> :: "(var_context)" and \<Gamma> :: "(fun_context)"
assumes 
V0: "((\<Lambda> ''x'') = (Some TInt))" and 
V1: "((\<Lambda> ''z'') = (Some TInt))" and 
V2: "((\<Lambda> ''q'') = (Some TInt))"
begin

lemmas var_assms = V0 V1 V2
lemma block_GeneratedUnifiedExit:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')"
shows "(s' \<noteq> Failure)"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon3_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assign [(''z'', (Var ''x''))]), 
(Assign [(''q'', (Var ''z''))]), 
(Assert (BinOp (BinOp (Var ''x'') Add (Var ''z'')) Ge (Val (IntV 0))))] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV 0)))" and 
"(vc_passive.vc_anon3_Then )"
shows "(s' \<noteq> Failure)"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon3_Then_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon3_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assert (BinOp (Var ''z'') Ge (Val (IntV 0))))] (Normal n_s) s')" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"(vc_passive.vc_anon3_Else vc_z)"
shows "(s' \<noteq> Failure)"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon3_Else_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''z'') Ge (Val (IntV 0)))), 
(Assign [(''x'', (Val (IntV 0)))])] (Normal n_s) s')" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"(vc_passive.vc_anon0 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_z. ((((n_s' ''x'') = (Some (IntV 0))) \<and> ((n_s' ''z'') = (Some (IntV vc_z)))) \<and> ((vc_passive.vc_anon3_Then ) \<and> (vc_passive.vc_anon3_Else vc_z)))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon0_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"(vc_passive.vc_anon0 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_z. (((n_s' ''z'') = (Some (IntV vc_z))) \<and> (vc_passive.vc_anon0 ))))))"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"(vc_passive.vc_PreconditionGeneratedEntry )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_z. (((n_s' ''z'') = (Some (IntV vc_z))) \<and> (vc_passive.vc_anon0 ))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_PreconditionGeneratedEntry_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)


end

locale progLocale
begin

fun outEdges_constant_prop_branch_4
  where
    "outEdges_constant_prop_branch_4 (Suc(Suc(0))) = {}"
    |"outEdges_constant_prop_branch_4 (Suc(0)) = {}"
    |"outEdges_constant_prop_branch_4 (0) = {(Suc(Suc(0))), (Suc(0))}"
    |"outEdges_constant_prop_branch_4 _ = {}"
fun nodeToBlocks_constant_prop_branch_4
  where
    "nodeToBlocks_constant_prop_branch_4 (Suc(Suc(0))) = (Some [(Assign [(''z'', (Var ''x''))]), 
(Assign [(''q'', (Var ''z''))]), 
(Assert (BinOp (BinOp (Var ''x'') Add (Var ''z'')) Ge (Val (IntV 0))))])"
    |"nodeToBlocks_constant_prop_branch_4 (Suc(0)) = (Some [(Assert (BinOp (Var ''z'') Ge (Val (IntV 0))))])"
    |"nodeToBlocks_constant_prop_branch_4 (0) = (Some [(Assume (BinOp (Var ''z'') Ge (Val (IntV 0)))), 
(Assign [(''x'', (Val (IntV 0)))])])"
    |"nodeToBlocks_constant_prop_branch_4 _ = (None )"
fun funDecl_constant_prop_branch_4
  where
    "funDecl_constant_prop_branch_4 _ = (None )"
fun inParams_constant_prop_branch_4
  where
    "inParams_constant_prop_branch_4 _ = (None )"
fun localVars_constant_prop_branch_4
  where
    "localVars_constant_prop_branch_4 ''x'' = (Some TInt)"
    |"localVars_constant_prop_branch_4 ''z'' = (Some TInt)"
    |"localVars_constant_prop_branch_4 ''q'' = (Some TInt)"
    |"localVars_constant_prop_branch_4 _ = (None )"
definition ProgramM
  where
    "ProgramM  = (Program funDecl_constant_prop_branch_4 [(''constant_prop_branch_4'', inParams_constant_prop_branch_4, localVars_constant_prop_branch_4, (|entry = 0, nodes = {(Suc(Suc(0))), (Suc(0)), (0)}, out_edges = outEdges_constant_prop_branch_4, node_to_block = nodeToBlocks_constant_prop_branch_4|))])"

end


end
