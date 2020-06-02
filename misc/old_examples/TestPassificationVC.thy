theory TestPassificationVC
imports Main
begin
  

lemma "x1 = (x0::int)+x0 \<and> x2 = x1 + x1 \<and> x3 = (x2::int)+x2+0+1"
  apply clarsimp
  oops

locale vc = 
fixes n :: "int" and r_0 :: "int" and call0formal_n_0 :: "int" and call1formal_r_0 :: "int" and call1formal_r_0_0 :: "int" and r_1 :: "int"
begin

definition vc_GeneratedUnifiedExit
  where
    "vc_GeneratedUnifiedExit  = ((((100::int) < n) \<longrightarrow> (r_1 = (n - (10::int)))) \<and> ((((100::int) < n) \<longrightarrow> (r_1 = (n - (10::int)))) \<longrightarrow> ((n \<le> (100::int)) \<longrightarrow> (r_1 = (91::int)))))"
definition vc_anon3_Then
  where
    "vc_anon3_Then  = (((100::int) < n) \<longrightarrow> (((r_0 = (n - (10::int))) \<and> (r_1 = r_0)) \<longrightarrow> vc_GeneratedUnifiedExit))"
definition vc_anon3_Else
  where
    "vc_anon3_Else  = ((n \<le> (100::int)) \<longrightarrow> (((call0formal_n_0 = (n + (11::int))) \<and> (((100::int) < call0formal_n_0) \<longrightarrow> (call1formal_r_0 = (call0formal_n_0 - (10::int))))) \<longrightarrow> (((((call0formal_n_0 \<le> (100::int)) \<longrightarrow> (call1formal_r_0 = (91::int))) \<and> (((100::int) < call1formal_r_0) \<longrightarrow> (call1formal_r_0_0 = (call1formal_r_0 - (10::int))))) \<and> (((call1formal_r_0 \<le> (100::int)) \<longrightarrow> (call1formal_r_0_0 = (91::int))) \<and> (r_1 = call1formal_r_0_0))) \<longrightarrow> vc_GeneratedUnifiedExit)))"
definition vc_anon0
  where
    "vc_anon0  = (vc_anon3_Then \<and> vc_anon3_Else)"

lemma test:
  shows "let vc_anon0 = 4 in vc_anon0 > 4"
  oops

lemma vc_correct:
shows "vc_anon0"
apply (simp only: vc_anon0_def vc_anon3_Else_def vc_anon3_Then_def vc_GeneratedUnifiedExit_def)
  apply smt
  done

end

lemma vc_test: "(\<forall>x y. P x \<longrightarrow> (P y \<longrightarrow> Q x y)) \<Longrightarrow> \<forall>x. P x \<longrightarrow> (\<forall>y. P y \<longrightarrow> Q x y)"
  by simp

locale vc_passive
begin

definition vc_GeneratedUnifiedExit
  where
    "vc_GeneratedUnifiedExit n r_1  = ((((100::int) < n) \<longrightarrow> (r_1 = (n - (10::int)))) \<and> ((((100::int) < n) \<longrightarrow> (r_1 = (n - (10::int)))) \<longrightarrow> ((n \<le> (100::int)) \<longrightarrow> (r_1 = (91::int)))))"

definition vc_anon3_Then
  where
    "vc_anon3_Then = (\<forall> n r_1 r_0. (((100::int) < n) \<longrightarrow> (((r_0 = (n - (10::int))) \<and> (r_1 = r_0)) \<longrightarrow> vc_GeneratedUnifiedExit n r_1)))"

definition vc_anon3_Else
  where
    "vc_anon3_Else  = 
      (\<forall> n r_1 call0formal_n_0 call1formal_r_0 call1formal_r_0_0.
  ((n \<le> (100::int)) \<longrightarrow> (((call0formal_n_0 = (n + (11::int))) \<and> (((100::int) < call0formal_n_0) \<longrightarrow>
  (call1formal_r_0 = (call0formal_n_0 - (10::int))))) \<longrightarrow> (((((call0formal_n_0 \<le> (100::int)) \<longrightarrow>
 (call1formal_r_0 = (91::int))) \<and> (((100::int) < call1formal_r_0) \<longrightarrow>
 (call1formal_r_0_0 = (call1formal_r_0 - (10::int))))) \<and> (((call1formal_r_0 \<le> (100::int)) \<longrightarrow>
 (call1formal_r_0_0 = (91::int))) \<and> (r_1 = call1formal_r_0_0))) \<longrightarrow> vc_GeneratedUnifiedExit n r_1))))"
definition vc_anon0
  where
    "vc_anon0  = (vc_anon3_Then \<and> vc_anon3_Else)"

lemma test:
  shows "let vc_anon0 = 4 in vc_anon0 > 4"
  oops
(*
lemma vc_correct:
shows "vc_anon0"
apply (simp only: vc_anon0_def vc_anon3_Else_def vc_anon3_Then_def vc_GeneratedUnifiedExit_def)
  apply smt
  done
*)

end

lemma vc: "(\<forall> n r_0 call0formal_n_0 call1formal_r_0 call1formal_r_0_0 r_1. vc.vc_anon0 n r_0 call0formal_n_0 call1formal_r_0 call1formal_r_0_0 r_1)
   \<Longrightarrow> vc_passive.vc_anon0"
  oops


locale vc_sum = 
fixes n :: "int" and  i_0 :: "int" and res_0 :: "int" and res_1 :: "int" and i_1 :: "int"
begin

definition vc_anon7_Then
  where
    "vc_anon7_Then  = True"
definition vc_anon8_Then
  where
    "vc_anon8_Then  = True"
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
(*
lemma vc_correct:

shows "vc_PreconditionGeneratedEntry"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def vc_anon7_Else_def vc_anon9_Else_def vc_anon9_Then_def vc_anon8_Then_def vc_anon7_Then_def)
  by (smt mult.commute semiring_normalization_rules(3))
*)

end


locale vc_sum_passive = 
  fixes n :: int and i_0 :: int and res_0 :: int
begin

definition vc_anon7_Then
  where
    "vc_anon7_Then  = True"
definition vc_anon8_Then
  where
    "vc_anon8_Then  = True"
definition vc_anon9_Then
  where
    "vc_anon9_Then = (\<forall> i_1 res_1. ((i_0 \<le> (n + (1::int))) \<longrightarrow> (((((res_0 * (2::int)) = ((i_0 - (1::int)) * i_0)) \<and> (i_0 \<le> n)) \<and> ((res_1 = (res_0 + i_0)) \<and> (i_1 = (i_0 + (1::int))))) \<longrightarrow> ((i_1 \<le> (n + (1::int))) \<and> ((i_1 \<le> (n + (1::int))) \<longrightarrow> ((res_1 * (2::int)) = ((i_1 - (1::int)) * i_1)))))))"
definition vc_anon9_Else
  where
    "vc_anon9_Else  = ((\<not> (i_0 \<le> n)) \<longrightarrow> (((i_0 \<le> (n + (1::int))) \<and> ((res_0 * (2::int)) = ((i_0 - (1::int)) * i_0))) \<longrightarrow> ((res_0 * (2::int)) = (n * (n + (1::int))))))"
definition vc_anon7_Else
  where
    "vc_anon7_Else  = (((0::int) \<le> (n + (1::int))) \<and> (((0::int) \<le> (n + (1::int))) \<longrightarrow> ((((0::int) * (2::int)) = (((0::int) - (1::int)) * (0::int))) \<and> ((((0::int) * (2::int)) = (((0::int) - (1::int)) * (0::int))) \<longrightarrow> ((vc_anon8_Then \<and> vc_anon9_Then) \<and> vc_anon9_Else)))))"
definition vc_anon0
  where
    "vc_anon0  = (((0::int) \<le> n) \<longrightarrow> (vc_anon7_Then \<and> vc_anon7_Else ))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry  = vc_anon0"     
end

term vc_sum.vc_PreconditionGeneratedEntry

lemma vc_sum_relation: "\<lbrakk> \<forall> n i_0 res_0 res_1 i_1. vc_sum.vc_PreconditionGeneratedEntry n i_0 res_0 res_1 i_1 \<rbrakk> \<Longrightarrow>
                         \<forall> n i_0 res_0. vc_sum_passive.vc_PreconditionGeneratedEntry n i_0 res_0"
apply (simp only: vc_sum.vc_PreconditionGeneratedEntry_def vc_sum.vc_anon0_def vc_sum.vc_anon7_Else_def vc_sum.vc_anon9_Else_def vc_sum.vc_anon9_Then_def vc_sum.vc_anon8_Then_def vc_sum.vc_anon7_Then_def)
  apply (simp only: vc_sum_passive.vc_PreconditionGeneratedEntry_def vc_sum_passive.vc_anon0_def vc_sum_passive.vc_anon7_Else_def vc_sum_passive.vc_anon9_Else_def vc_sum_passive.vc_anon9_Then_def vc_sum_passive.vc_anon8_Then_def vc_sum_passive.vc_anon7_Then_def)  
  apply (unfold all-simps(6))
  using [[simp_trace_new mode=full]]


end