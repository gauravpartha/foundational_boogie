theory infeasible_edge_3
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

locale vc_passive
begin

definition vc_anon4_Then
  where
    "vc_anon4_Then  = (\<forall> x. (((x > (0::int)) \<and> (x < (0::int))) \<longrightarrow> ((\<not> (x = (1::int))) \<and> (\<not> (\<not> (x = (1::int)))))))"
definition vc_anon4_Else
  where
    "vc_anon4_Else  = (\<forall> x y_0 z_0. (((0::int) \<ge> x) \<longrightarrow> (((y_0 = ((2::int) * x)) \<and> (z_0 = (y_0 + (1::int)))) \<longrightarrow> (z_0 = (((2::int) * x) + (1::int))))))"
definition vc_anon0
  where
    "vc_anon0  = ((vc_anon4_Then ) \<and> (vc_anon4_Else ))"
lemma vc_correct:

shows "(vc_anon0 )"
apply (simp only: vc_anon0_def vc_anon4_Else_def vc_anon4_Then_def)
oops


end

locale beforePassive = 
fixes \<Lambda> :: "(var_context)" and \<Gamma> :: "(fun_context)"
assumes 
V0: "((\<Lambda> ''y'') = (Some TInt))" and 
V1: "((\<Lambda> ''z'') = (Some TInt))" and 
V2: "((\<Lambda> ''x'') = (Some TInt))"
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

lemma block_anon4_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''x'') Gt (Val (IntV 0)))), 
(Assume (BinOp (Var ''x'') Lt (Val (IntV 0)))), 
(Assert (UnOp Not (BinOp (Var ''x'') Eq (Val (IntV 1))))), 
(Assert (Val (BoolV False)))] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_anon4_Then )"
shows "(s' = Magic)"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon4_Then_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon4_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Val (IntV 0)) Ge (Var ''x''))), 
(Assign [(''y'', (BinOp (Val (IntV 2)) Mul (Var ''x'')))]), 
(Assign [(''z'', (BinOp (Var ''y'') Add (Val (IntV 1))))]), 
(Assert (BinOp (Var ''z'') Eq (BinOp (BinOp (Val (IntV 2)) Mul (Var ''x'')) Add (Val (IntV 1)))))] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_anon4_Else )"
shows "(s' \<noteq> Failure)"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon4_Else_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((vc_passive.vc_anon4_Then ) \<and> (vc_passive.vc_anon4_Else ))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_x. (((n_s' ''x'') = (Some (IntV vc_x))) \<and> ((vc_passive.vc_anon4_Then ) \<and> (vc_passive.vc_anon4_Else )))))))"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((vc_passive.vc_anon4_Then ) \<and> (vc_passive.vc_anon4_Else ))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_x. (((n_s' ''x'') = (Some (IntV vc_x))) \<and> ((vc_passive.vc_anon4_Then ) \<and> (vc_passive.vc_anon4_Else )))))))"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_anon0 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_x. (((n_s' ''x'') = (Some (IntV vc_x))) \<and> ((vc_passive.vc_anon4_Then ) \<and> (vc_passive.vc_anon4_Else )))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon0_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)


end

locale progLocale
begin

fun outEdges_infeasible_edge_3
  where
    "outEdges_infeasible_edge_3 (Suc(Suc(0))) = {}"
    |"outEdges_infeasible_edge_3 (Suc(0)) = {}"
    |"outEdges_infeasible_edge_3 (0) = {(Suc(Suc(0))), (Suc(0))}"
    |"outEdges_infeasible_edge_3 _ = {}"
fun nodeToBlocks_infeasible_edge_3
  where
    "nodeToBlocks_infeasible_edge_3 (Suc(Suc(0))) = (Some [(Assume (BinOp (Var ''x'') Gt (Val (IntV 0)))), 
(Assume (BinOp (Var ''x'') Lt (Val (IntV 0)))), 
(Assert (UnOp Not (BinOp (Var ''x'') Eq (Val (IntV 1))))), 
(Assert (Val (BoolV False)))])"
    |"nodeToBlocks_infeasible_edge_3 (Suc(0)) = (Some [(Assume (BinOp (Val (IntV 0)) Ge (Var ''x''))), 
(Assign [(''y'', (BinOp (Val (IntV 2)) Mul (Var ''x'')))]), 
(Assign [(''z'', (BinOp (Var ''y'') Add (Val (IntV 1))))]), 
(Assert (BinOp (Var ''z'') Eq (BinOp (BinOp (Val (IntV 2)) Mul (Var ''x'')) Add (Val (IntV 1)))))])"
    |"nodeToBlocks_infeasible_edge_3 (0) = (Some [])"
    |"nodeToBlocks_infeasible_edge_3 _ = (None )"
fun funDecl_infeasible_edge_3
  where
    "funDecl_infeasible_edge_3 _ = (None )"
fun inParams_infeasible_edge_3
  where
    "inParams_infeasible_edge_3 ''x'' = (Some TInt)"
    |"inParams_infeasible_edge_3 _ = (None )"
fun localVars_infeasible_edge_3
  where
    "localVars_infeasible_edge_3 ''y'' = (Some TInt)"
    |"localVars_infeasible_edge_3 ''z'' = (Some TInt)"
    |"localVars_infeasible_edge_3 _ = (None )"
definition ProgramM
  where
    "ProgramM  = (Program funDecl_infeasible_edge_3 [(''infeasible_edge_3'', inParams_infeasible_edge_3, localVars_infeasible_edge_3, (|entry = 0, nodes = {(Suc(Suc(0))), (Suc(0)), (0)}, out_edges = outEdges_infeasible_edge_3, node_to_block = nodeToBlocks_infeasible_edge_3|))])"

end


end
