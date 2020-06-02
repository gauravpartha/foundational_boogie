theory m_branch_1
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

locale vc_passive = 
fixes f :: "(int => int)"
begin

definition vc_anon3
  where
    "vc_anon3 x y = (((1::int) \<le> x) \<longrightarrow> (((1::int) \<le> y) \<and> (((1::int) \<le> y) \<longrightarrow> ((x = (3::int)) \<longrightarrow> (y = (4::int))))))"
definition vc_anon4_Then
  where
    "vc_anon4_Then  = (\<forall> x y. ((((0::int) \<le> x) \<and> (y = (x + (1::int)))) \<longrightarrow> (vc_anon3 x y)))"
definition vc_anon4_Else
  where
    "vc_anon4_Else  = (\<forall> x y. (((x < (0::int)) \<and> (y \<le> (0::int))) \<longrightarrow> (vc_anon3 x y)))"
definition vc_anon0
  where
    "vc_anon0  = ((vc_anon4_Then ) \<and> (vc_anon4_Else ))"
lemma vc_correct:

shows "(vc_anon0 )"
apply (simp only: vc_anon0_def vc_anon4_Else_def vc_anon4_Then_def vc_anon3_def)
oops


end

locale beforePassive = 
fixes \<Lambda> :: "(var_context)" and \<Gamma> :: "(fun_context)" and f :: "(((val)list) => ((val)option))"
assumes 
V0: "((\<Lambda> ''y'') = (Some TInt))" and 
V1: "((\<Lambda> ''x'') = (Some TInt))" and 
F0: "(((snd \<Gamma>) ''f'') = (Some f))" and 
F1: "(\<forall> farg0. ((f [(IntV farg0)]) = (Some (IntV (vc_f farg0)))))"
begin

lemmas var_assms = V0 V1
lemmas fun_assms = F0 F1
lemma block_anon3:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Val (IntV 1)) Le (Var ''x''))), 
(Assert (BinOp (Val (IntV 1)) Le (Var ''y''))), 
(Assume (BinOp (Var ''x'') Eq (Val (IntV 3)))), 
(Assert (BinOp (Var ''y'') Eq (Val (IntV 4))))] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"(vc_passive.vc_anon3 vc_x vc_y)"
shows "(s' \<noteq> Failure)"
using assms fun_assms
apply cases
apply (simp only: vc_passive.vc_anon3_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon4_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Val (IntV 0)) Le (Var ''x''))), 
(Assume (BinOp (Var ''y'') Eq (BinOp (Var ''x'') Add (Val (IntV 1)))))] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_anon4_Then )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_x vc_y. ((((n_s' ''x'') = (Some (IntV vc_x))) \<and> ((n_s' ''y'') = (Some (IntV vc_y)))) \<and> (vc_passive.vc_anon3 vc_x vc_y))))))"
using assms fun_assms
apply cases
apply (simp only: vc_passive.vc_anon4_Then_def)
  apply (handle_cmd_list_full v_assms: var_assms)?
  
by (auto?)

lemma block_anon4_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''x'') Lt (Val (IntV 0)))), 
(Assume (BinOp (Var ''y'') Le (Val (IntV 0))))] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_anon4_Else )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_x vc_y. ((((n_s' ''x'') = (Some (IntV vc_x))) \<and> ((n_s' ''y'') = (Some (IntV vc_y)))) \<and> (vc_passive.vc_anon3 vc_x vc_y))))))"
using assms fun_assms
apply cases
apply (simp only: vc_passive.vc_anon4_Else_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((vc_passive.vc_anon4_Then ) \<and> (vc_passive.vc_anon4_Else ))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_y vc_x. ((((n_s' ''y'') = (Some (IntV vc_y))) \<and> ((n_s' ''x'') = (Some (IntV vc_x)))) \<and> ((vc_passive.vc_anon4_Then ) \<and> (vc_passive.vc_anon4_Else )))))))"
using assms fun_assms
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((vc_passive.vc_anon4_Then ) \<and> (vc_passive.vc_anon4_Else ))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_y vc_x. ((((n_s' ''y'') = (Some (IntV vc_y))) \<and> ((n_s' ''x'') = (Some (IntV vc_x)))) \<and> ((vc_passive.vc_anon4_Then ) \<and> (vc_passive.vc_anon4_Else )))))))"
using assms fun_assms
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_anon0 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_y vc_x. ((((n_s' ''y'') = (Some (IntV vc_y))) \<and> ((n_s' ''x'') = (Some (IntV vc_x)))) \<and> ((vc_passive.vc_anon4_Then ) \<and> (vc_passive.vc_anon4_Else )))))))"
using assms fun_assms
apply cases
apply (simp only: vc_passive.vc_anon0_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)


end

locale progLocale
begin

fun outEdges_m_branch_1
  where
    "outEdges_m_branch_1 (Suc(Suc(Suc(0)))) = {(Suc(Suc(0)))}"
    |"outEdges_m_branch_1 (Suc(Suc(0))) = {}"
    |"outEdges_m_branch_1 (Suc(0)) = {(Suc(Suc(0)))}"
    |"outEdges_m_branch_1 (0) = {(Suc(Suc(Suc(0)))), (Suc(0))}"
    |"outEdges_m_branch_1 _ = {}"
fun nodeToBlocks_m_branch_1
  where
    "nodeToBlocks_m_branch_1 (Suc(Suc(Suc(0)))) = (Some [(Assume (BinOp (Val (IntV 0)) Le (Var ''x''))), 
(Assume (BinOp (Var ''y'') Eq (BinOp (Var ''x'') Add (Val (IntV 1)))))])"
    |"nodeToBlocks_m_branch_1 (Suc(Suc(0))) = (Some [(Assume (BinOp (Val (IntV 1)) Le (Var ''x''))), 
(Assert (BinOp (Val (IntV 1)) Le (Var ''y''))), 
(Assume (BinOp (Var ''x'') Eq (Val (IntV 3)))), 
(Assert (BinOp (Var ''y'') Eq (Val (IntV 4))))])"
    |"nodeToBlocks_m_branch_1 (Suc(0)) = (Some [(Assume (BinOp (Var ''x'') Lt (Val (IntV 0)))), 
(Assume (BinOp (Var ''y'') Le (Val (IntV 0))))])"
    |"nodeToBlocks_m_branch_1 (0) = (Some [])"
    |"nodeToBlocks_m_branch_1 _ = (None )"
fun funDecl_m_branch_1
  where
    "funDecl_m_branch_1 _ = (None )"
fun inParams_m_branch_1
  where
    "inParams_m_branch_1 ''x'' = (Some TInt)"
    |"inParams_m_branch_1 _ = (None )"
fun localVars_m_branch_1
  where
    "localVars_m_branch_1 ''y'' = (Some TInt)"
    |"localVars_m_branch_1 _ = (None )"
definition ProgramM
  where
    "ProgramM  = (Program funDecl_m_branch_1 [(''m_branch_1'', inParams_m_branch_1, localVars_m_branch_1, (|entry = 0, nodes = {(Suc(Suc(Suc(0)))), (Suc(Suc(0))), (Suc(0)), (0)}, out_edges = outEdges_m_branch_1, node_to_block = nodeToBlocks_m_branch_1|))])"

end


end
