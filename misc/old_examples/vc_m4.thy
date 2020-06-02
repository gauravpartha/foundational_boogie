theory vc_m4
imports Semantics Util
begin
locale vc = 
fixes x :: "int" and y :: "int" and f :: "(int => int)"
begin

definition vc_anon0
  where
    "vc_anon0  = ((((5::int) \<le> (f x)) \<and> (y \<le> (4::int))) \<longrightarrow> (y \<le> (f x)))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry  = vc_anon0"
lemma vc_correct:

shows "vc_PreconditionGeneratedEntry"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def)
oops


end

lemma anon0_correct:
assumes 
"(red_cmd_list \<Gamma> [(Assume (BinOp (Val (IntV 5)) Le (FunExp ''f'' [(Var ''x'')]))), (Assume (BinOp (Var ''y'') Le (Val (IntV 4)))), (Assert (BinOp (Var ''y'') Le (FunExp ''f'' [(Var ''x'')])))] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"(((snd \<Gamma>) ''f'') = (Some isa_f))" and 
"(\<forall> farg0. ((isa_f [(IntV farg0)]) = (Some (IntV (vc_f farg0)))))" and 
"(vc.vc_anon0 vc_x vc_y vc_f)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms
apply cases
apply (simp only: vc.vc_anon0_def)
apply (handle_cmd_list_full?)
by (auto?)

lemma PreconditionGeneratedEntry_correct:
assumes 
"(red_cmd_list \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"(((snd \<Gamma>) ''f'') = (Some isa_f))" and 
"(\<forall> farg0. ((isa_f [(IntV farg0)]) = (Some (IntV (vc_f farg0)))))" and 
"(vc.vc_PreconditionGeneratedEntry vc_x vc_y vc_f)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 vc_x vc_y vc_f)))))"
using assms
apply cases
apply (simp only: vc.vc_PreconditionGeneratedEntry_def)
apply (handle_cmd_list_full?)
by (auto?)


end
