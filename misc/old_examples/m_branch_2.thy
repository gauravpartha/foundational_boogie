theory m_branch_2
imports Semantics Util
begin
locale vc = 
fixes f :: "(int => int)"
begin

definition vc_anon7_Then
  where
    "vc_anon7_Then y = (((f y) \<le> (0::int)) \<longrightarrow> ((f (y + (2::int))) < (2::int)))"
definition vc_anon7_Else
  where
    "vc_anon7_Else y x = ((((0::int) < (f y)) \<and> ((1::int) \<le> x)) \<longrightarrow> (((f (y + (2::int))) \<ge> (2::int)) \<and> (((f (y + (2::int))) \<ge> (2::int)) \<longrightarrow> (((x = (4::int)) \<and> (y = (3::int))) \<longrightarrow> ((f (8::int)) = (4::int))))))"
definition vc_anon6_Then
  where
    "vc_anon6_Then x y = (((((0::int) \<le> x) \<and> ((f y) > (0::int))) \<and> (((f (y + (2::int))) \<ge> (x + (1::int))) \<and> ((f (y + (5::int))) = x))) \<longrightarrow> ((vc_anon7_Then y) \<and> (vc_anon7_Else y x)))"
definition vc_anon6_Else
  where
    "vc_anon6_Else x y = ((x < (0::int)) \<longrightarrow> ((((f y) \<le> (0::int)) \<and> ((f (y + (2::int))) < (x + (1::int)))) \<longrightarrow> ((vc_anon7_Then y) \<and> (vc_anon7_Else y x))))"
definition vc_anon0
  where
    "vc_anon0 x y = ((vc_anon6_Then x y) \<and> (vc_anon6_Else x y))"
lemma vc_correct:

shows "(vc_anon0 x y)"
apply (simp only: vc_anon0_def vc_anon6_Else_def vc_anon6_Then_def vc_anon7_Else_def vc_anon7_Then_def)
oops


end

locale vc_passive = 
fixes f :: "(int => int)"
begin

definition vc_anon7_Then
  where
    "vc_anon7_Then y = (((f y) \<le> (0::int)) \<longrightarrow> ((f (y + (2::int))) < (2::int)))"
definition vc_anon7_Else
  where
    "vc_anon7_Else y x = ((((0::int) < (f y)) \<and> ((1::int) \<le> x)) \<longrightarrow> (((f (y + (2::int))) \<ge> (2::int)) \<and> (((f (y + (2::int))) \<ge> (2::int)) \<longrightarrow> (((x = (4::int)) \<and> (y = (3::int))) \<longrightarrow> ((f (8::int)) = (4::int))))))"
definition vc_anon6_Then
  where
    "vc_anon6_Then  = (\<forall> x y. (((((0::int) \<le> x) \<and> ((f y) > (0::int))) \<and> (((f (y + (2::int))) \<ge> (x + (1::int))) \<and> ((f (y + (5::int))) = x))) \<longrightarrow> ((vc_anon7_Then y) \<and> (vc_anon7_Else y x))))"
definition vc_anon6_Else
  where
    "vc_anon6_Else  = (\<forall> x y. ((x < (0::int)) \<longrightarrow> ((((f y) \<le> (0::int)) \<and> ((f (y + (2::int))) < (x + (1::int)))) \<longrightarrow> ((vc_anon7_Then y) \<and> (vc_anon7_Else y x)))))"
definition vc_anon0
  where
    "vc_anon0  = ((vc_anon6_Then ) \<and> (vc_anon6_Else ))"
lemma vc_correct:

shows "(vc_anon0 )"
apply (simp only: vc_anon0_def vc_anon6_Else_def vc_anon6_Then_def vc_anon7_Else_def vc_anon7_Then_def)
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
lemma block_GeneratedUnifiedExit:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')"
shows "(s' \<noteq> Failure)"
using assms fun_assms
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon7_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (FunExp ''f'' [(Var ''y'')]) Le (Val (IntV 0)))), 
(Assert (BinOp (FunExp ''f'' [(BinOp (Var ''y'') Add (Val (IntV 2)))]) Lt (Val (IntV 2))))] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"(vc_passive.vc_anon7_Then vc_f vc_y)"
shows "(s' \<noteq> Failure)"
using assms fun_assms
apply cases
apply (simp only: vc_passive.vc_anon7_Then_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon7_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Val (IntV 0)) Lt (FunExp ''f'' [(Var ''y'')]))), 
(Assume (BinOp (Val (IntV 1)) Le (Var ''x''))), 
(Assert (BinOp (FunExp ''f'' [(BinOp (Var ''y'') Add (Val (IntV 2)))]) Ge (Val (IntV 2)))), 
(Assume (BinOp (Var ''x'') Eq (Val (IntV 4)))), 
(Assume (BinOp (Var ''y'') Eq (Val (IntV 3)))), 
(Assert (BinOp (FunExp ''f'' [(Val (IntV 8))]) Eq (Val (IntV 4))))] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_anon7_Else vc_f vc_y vc_x)"
shows "(s' \<noteq> Failure)"
using assms fun_assms
apply cases
apply (simp only: vc_passive.vc_anon7_Else_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon3:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((vc_passive.vc_anon7_Then vc_f vc_y) \<and> (vc_passive.vc_anon7_Else vc_f vc_y vc_x))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_y vc_x. ((((n_s' ''y'') = (Some (IntV vc_y))) \<and> ((n_s' ''x'') = (Some (IntV vc_x)))) \<and> ((vc_passive.vc_anon7_Then vc_f vc_y) \<and> (vc_passive.vc_anon7_Else vc_f vc_y vc_x)))))))"
using assms fun_assms
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon6_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Val (IntV 0)) Le (Var ''x''))), 
(Assume (BinOp (FunExp ''f'' [(Var ''y'')]) Gt (Val (IntV 0)))), 
(Assume (BinOp (FunExp ''f'' [(BinOp (Var ''y'') Add (Val (IntV 2)))]) Ge (BinOp (Var ''x'') Add (Val (IntV 1))))), 
(Assume (BinOp (FunExp ''f'' [(BinOp (Var ''y'') Add (Val (IntV 5)))]) Eq (Var ''x'')))] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_anon6_Then vc_f)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_y vc_x. ((((n_s' ''y'') = (Some (IntV vc_y))) \<and> ((n_s' ''x'') = (Some (IntV vc_x)))) \<and> ((vc_passive.vc_anon7_Then vc_f vc_y) \<and> (vc_passive.vc_anon7_Else vc_f vc_y vc_x)))))))"
using assms fun_assms
apply cases
apply (simp only: vc_passive.vc_anon6_Then_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon6_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''x'') Lt (Val (IntV 0)))), 
(Assume (BinOp (FunExp ''f'' [(Var ''y'')]) Le (Val (IntV 0)))), 
(Assume (BinOp (FunExp ''f'' [(BinOp (Var ''y'') Add (Val (IntV 2)))]) Lt (BinOp (Var ''x'') Add (Val (IntV 1)))))] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_anon6_Else vc_f)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_y vc_x. ((((n_s' ''y'') = (Some (IntV vc_y))) \<and> ((n_s' ''x'') = (Some (IntV vc_x)))) \<and> ((vc_passive.vc_anon7_Then vc_f vc_y) \<and> (vc_passive.vc_anon7_Else vc_f vc_y vc_x)))))))"
using assms fun_assms
apply cases
apply (simp only: vc_passive.vc_anon6_Else_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((vc_passive.vc_anon6_Then vc_f) \<and> (vc_passive.vc_anon6_Else vc_f))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_y vc_x. ((((n_s' ''y'') = (Some (IntV vc_y))) \<and> ((n_s' ''x'') = (Some (IntV vc_x)))) \<and> ((vc_passive.vc_anon6_Then vc_f) \<and> (vc_passive.vc_anon6_Else vc_f)))))))"
using assms fun_assms
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((vc_passive.vc_anon6_Then vc_f) \<and> (vc_passive.vc_anon6_Else vc_f))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_y vc_x. ((((n_s' ''y'') = (Some (IntV vc_y))) \<and> ((n_s' ''x'') = (Some (IntV vc_x)))) \<and> ((vc_passive.vc_anon6_Then vc_f) \<and> (vc_passive.vc_anon6_Else vc_f)))))))"
using assms fun_assms
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_anon0 vc_f)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_y vc_x. ((((n_s' ''y'') = (Some (IntV vc_y))) \<and> ((n_s' ''x'') = (Some (IntV vc_x)))) \<and> ((vc_passive.vc_anon6_Then vc_f) \<and> (vc_passive.vc_anon6_Else vc_f)))))))"
using assms fun_assms
apply cases
apply (simp only: vc_passive.vc_anon0_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)


end


end
