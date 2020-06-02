theory empty_join_blocks_1
imports Semantics Util
begin
locale vc
begin

definition vc_exit
  where
    "vc_exit x = (x \<ge> (0::int))"
definition vc_b4
  where
    "vc_b4 z y x = (((z > (0::int)) \<and> (y > ((4::int) * z))) \<longrightarrow> (vc_exit x))"
definition vc_b3
  where
    "vc_b3 y z x = (((y > (0::int)) \<and> (z > (y + (1::int)))) \<longrightarrow> (vc_exit x))"
definition vc_b1
  where
    "vc_b1 x y z = ((x \<ge> ((2::int) * y)) \<longrightarrow> ((vc_b4 z y x) \<and> (vc_b3 y z x)))"
definition vc_b2
  where
    "vc_b2 x z y = ((x \<ge> (z + (4::int))) \<longrightarrow> ((vc_b4 z y x) \<and> (vc_b3 y z x)))"
definition vc_anon0
  where
    "vc_anon0 x y z = ((vc_b1 x y z) \<and> (vc_b2 x z y))"
lemma vc_correct:

shows "(vc_anon0 x y z)"
apply (simp only: vc_anon0_def vc_b2_def vc_b1_def vc_b3_def vc_b4_def vc_exit_def)
oops


end

locale vc_passive
begin

definition vc_exit
  where
    "vc_exit x = (x \<ge> (0::int))"
definition vc_b4
  where
    "vc_b4 z y x = (((z > (0::int)) \<and> (y > ((4::int) * z))) \<longrightarrow> (vc_exit x))"
definition vc_b3
  where
    "vc_b3 y z x = (((y > (0::int)) \<and> (z > (y + (1::int)))) \<longrightarrow> (vc_exit x))"
definition vc_b1
  where
    "vc_b1 z = (\<forall> x y. ((x \<ge> ((2::int) * y)) \<longrightarrow> ((vc_b4 z y x) \<and> (vc_b3 y z x))))"
definition vc_b2
  where
    "vc_b2 y = (\<forall> x z. ((x \<ge> (z + (4::int))) \<longrightarrow> ((vc_b4 z y x) \<and> (vc_b3 y z x))))"
definition vc_anon0
  where
    "vc_anon0 z y = ((vc_b1 z) \<and> (vc_b2 y))"
lemma vc_correct:

shows "(vc_anon0 z y)"
apply (simp only: vc_anon0_def vc_b2_def vc_b1_def vc_b3_def vc_b4_def vc_exit_def)
oops


end

locale beforePassive = 
fixes \<Lambda> :: "(var_context)" and \<Gamma> :: "(fun_context)"
assumes 
V0: "((\<Lambda> ''z'') = (Some TInt))" and 
V1: "((\<Lambda> ''y'') = (Some TInt))" and 
V2: "((\<Lambda> ''x'') = (Some TInt))"
begin

lemmas var_assms = V0 V1 V2
lemma block_exit:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assert (BinOp (Var ''x'') Ge (Val (IntV 0))))] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_exit vc_x)"
shows "(s' \<noteq> Failure)"
using assms 
apply cases
apply (simp only: vc_passive.vc_exit_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_b4:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''z'') Gt (Val (IntV 0)))), 
(Assume (BinOp (Var ''y'') Gt (BinOp (Val (IntV 4)) Mul (Var ''z''))))] (Normal n_s) s')" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_b4 vc_z vc_y vc_x)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_x. (((n_s' ''x'') = (Some (IntV vc_x))) \<and> (vc_passive.vc_exit vc_x))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_b4_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_b2__2_b4:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_b4 vc_z vc_y vc_x)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_z vc_y vc_x. (((((n_s' ''z'') = (Some (IntV vc_z))) \<and> ((n_s' ''y'') = (Some (IntV vc_y)))) \<and> ((n_s' ''x'') = (Some (IntV vc_x)))) \<and> (vc_passive.vc_b4 vc_z vc_y vc_x))))))"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_b3:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''y'') Gt (Val (IntV 0)))), 
(Assume (BinOp (Var ''z'') Gt (BinOp (Var ''y'') Add (Val (IntV 1)))))] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_b3 vc_y vc_z vc_x)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_x. (((n_s' ''x'') = (Some (IntV vc_x))) \<and> (vc_passive.vc_exit vc_x))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_b3_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_b2__2_b3:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_b3 vc_y vc_z vc_x)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_y vc_z vc_x. (((((n_s' ''y'') = (Some (IntV vc_y))) \<and> ((n_s' ''z'') = (Some (IntV vc_z)))) \<and> ((n_s' ''x'') = (Some (IntV vc_x)))) \<and> (vc_passive.vc_b3 vc_y vc_z vc_x))))))"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_b2:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''x'') Ge (BinOp (Var ''z'') Add (Val (IntV 4)))))] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"(vc_passive.vc_b2 vc_y)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_z vc_y vc_x. (((((n_s' ''z'') = (Some (IntV vc_z))) \<and> ((n_s' ''y'') = (Some (IntV vc_y)))) \<and> ((n_s' ''x'') = (Some (IntV vc_x)))) \<and> ((vc_passive.vc_b4 vc_z vc_y vc_x) \<and> (vc_passive.vc_b3 vc_y vc_z vc_x)))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_b2_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_b1__2_b3:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_b3 vc_y vc_z vc_x)"
shows "(s' = (Normal n_s) \<and> (n_s ''y'') = (Some (IntV vc_y)) \<and> (n_s ''z'') = (Some (IntV vc_z)) \<and> (n_s ''x'') = (Some (IntV vc_x)) \<and> (vc_passive.vc_b3 vc_y vc_z vc_x))"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_b1__2_b4:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_b4 vc_z vc_y vc_x)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_z vc_y vc_x. (((((n_s' ''z'') = (Some (IntV vc_z))) \<and> ((n_s' ''y'') = (Some (IntV vc_y)))) \<and> ((n_s' ''x'') = (Some (IntV vc_x)))) \<and> (vc_passive.vc_b4 vc_z vc_y vc_x))))))"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_b1:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''x'') Ge (BinOp (Val (IntV 2)) Mul (Var ''y''))))] (Normal n_s) s')" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"(vc_passive.vc_b1 vc_z)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_z vc_y vc_x. (((((n_s' ''z'') = (Some (IntV vc_z))) \<and> ((n_s' ''y'') = (Some (IntV vc_y)))) \<and> ((n_s' ''x'') = (Some (IntV vc_x)))) \<and> ((vc_passive.vc_b4 vc_z vc_y vc_x) \<and> (vc_passive.vc_b3 vc_y vc_z vc_x)))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_b1_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((vc_passive.vc_b1 vc_z) \<and> (vc_passive.vc_b2 vc_y))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_z vc_y vc_x. (((((n_s' ''z'') = (Some (IntV vc_z))) \<and> ((n_s' ''y'') = (Some (IntV vc_y)))) \<and> ((n_s' ''x'') = (Some (IntV vc_x)))) \<and> ((vc_passive.vc_b1 vc_z) \<and> (vc_passive.vc_b2 vc_y)))))))"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((vc_passive.vc_b1 vc_z) \<and> (vc_passive.vc_b2 vc_y))"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_z vc_y vc_x. (((((n_s' ''z'') = (Some (IntV vc_z))) \<and> ((n_s' ''y'') = (Some (IntV vc_y)))) \<and> ((n_s' ''x'') = (Some (IntV vc_x)))) \<and> ((vc_passive.vc_b1 vc_z) \<and> (vc_passive.vc_b2 vc_y)))))))"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''z'') = (Some (IntV vc_z)))" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(vc_passive.vc_anon0 vc_z vc_y)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_z vc_y vc_x. (((((n_s' ''z'') = (Some (IntV vc_z))) \<and> ((n_s' ''y'') = (Some (IntV vc_y)))) \<and> ((n_s' ''x'') = (Some (IntV vc_x)))) \<and> ((vc_passive.vc_b1 vc_z) \<and> (vc_passive.vc_b2 vc_y)))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon0_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)


end


end
