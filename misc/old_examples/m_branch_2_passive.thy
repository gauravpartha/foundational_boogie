theory m_branch_2_passive
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

locale passification = 
fixes \<Lambda> :: "(var_context)" and \<Gamma> :: "(fun_context)" and n_s :: "((vname) => ((val)option))" and f :: "(((val)list) => ((val)option))" and vc_f :: "(int => int)" and vc_x :: "int" and vc_y :: "int"
assumes 
G0: "(((snd \<Gamma>) ''f'') = (Some f))" and 
G1: "(\<forall> farg0. ((f [(IntV farg0)]) = (Some (IntV (vc_f farg0)))))" and 
G2: "((n_s ''vc_x'') = (Some (IntV vc_x)))" and 
G3: "((n_s ''vc_y'') = (Some (IntV vc_y)))"
begin

lemmas global_assms = G0 G1 G2 G3
lemma block_anon7_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (FunExp ''f'' [(Var ''vc_y'')]) Le (Val (IntV 0)))), 
(Assert (BinOp (FunExp ''f'' [(BinOp (Var ''vc_y'') Add (Val (IntV 2)))]) Lt (Val (IntV 2))))] (Normal n_s) s')" and 
"(vc.vc_anon7_Then vc_f vc_y)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon7_Then_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon7_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Val (IntV 0)) Lt (FunExp ''f'' [(Var ''vc_y'')]))), 
(Assume (BinOp (Val (IntV 1)) Le (Var ''vc_x''))), 
(Assert (BinOp (FunExp ''f'' [(BinOp (Var ''vc_y'') Add (Val (IntV 2)))]) Ge (Val (IntV 2)))), 
(Assume (BinOp (Var ''vc_x'') Eq (Val (IntV 4)))), 
(Assume (BinOp (Var ''vc_y'') Eq (Val (IntV 3)))), 
(Assert (BinOp (FunExp ''f'' [(Val (IntV 8))]) Eq (Val (IntV 4))))] (Normal n_s) s')" and 
"(vc.vc_anon7_Else vc_f vc_y vc_x)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon7_Else_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon6_Then:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Val (IntV 0)) Le (Var ''vc_x''))), 
(Assume (BinOp (FunExp ''f'' [(Var ''vc_y'')]) Gt (Val (IntV 0)))), 
(Assume (BinOp (FunExp ''f'' [(BinOp (Var ''vc_y'') Add (Val (IntV 2)))]) Ge (BinOp (Var ''vc_x'') Add (Val (IntV 1))))), 
(Assume (BinOp (FunExp ''f'' [(BinOp (Var ''vc_y'') Add (Val (IntV 5)))]) Eq (Var ''vc_x'')))] (Normal n_s) s')" and 
"(vc.vc_anon6_Then vc_f vc_x vc_y)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon7_Then vc_f vc_y) \<and> (vc.vc_anon7_Else vc_f vc_y vc_x))))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon6_Then_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon6_Else:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''vc_x'') Lt (Val (IntV 0)))), 
(Assume (BinOp (FunExp ''f'' [(Var ''vc_y'')]) Le (Val (IntV 0)))), 
(Assume (BinOp (FunExp ''f'' [(BinOp (Var ''vc_y'') Add (Val (IntV 2)))]) Lt (BinOp (Var ''vc_x'') Add (Val (IntV 1)))))] (Normal n_s) s')" and 
"(vc.vc_anon6_Else vc_f vc_x vc_y)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon7_Then vc_f vc_y) \<and> (vc.vc_anon7_Else vc_f vc_y vc_x))))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon6_Else_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"(vc.vc_anon0 vc_f vc_x vc_y)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon6_Then vc_f vc_x vc_y) \<and> (vc.vc_anon6_Else vc_f vc_x vc_y))))))"
using assms global_assms
apply cases
apply (simp only: vc.vc_anon0_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma block_GeneratedUnifiedExit:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms
apply cases
by auto

lemma block_anon3:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((vc.vc_anon7_Then vc_f vc_y) \<and> (vc.vc_anon7_Else vc_f vc_y vc_x))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon7_Then vc_f vc_y) \<and> (vc.vc_anon7_Else vc_f vc_y vc_x))))))"
using assms
apply cases
by auto

lemma block_anon0_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((vc.vc_anon6_Then vc_f vc_x vc_y) \<and> (vc.vc_anon6_Else vc_f vc_x vc_y))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon6_Then vc_f vc_x vc_y) \<and> (vc.vc_anon6_Else vc_f vc_x vc_y))))))"
using assms
apply cases
by auto

lemma block_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((vc.vc_anon6_Then vc_f vc_x vc_y) \<and> (vc.vc_anon6_Else vc_f vc_x vc_y))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon6_Then vc_f vc_x vc_y) \<and> (vc.vc_anon6_Else vc_f vc_x vc_y))))))"
using assms
apply cases
by auto


end


end
