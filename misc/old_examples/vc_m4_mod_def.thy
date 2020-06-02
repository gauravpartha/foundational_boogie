theory vc_m4_mod_def
imports Semantics Util
begin
locale vc = 
fixes x :: "int" and y :: "int" and f :: "(int => int)"
begin

definition vc_anon0_assert1
  where
   "vc_anon0_assert1 \<equiv> y \<le> (f x)"

lemma vc_anon0_assert1_elim: "vc_anon0_assert1 \<Longrightarrow> (vc_anon0_assert1 \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

abbreviation vc_anon0
  where
    "vc_anon0  \<equiv> (((5 \<le> (f x)) \<and> (y \<le> 4)) \<longrightarrow> vc_anon0_assert1)"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry  \<equiv> vc_anon0"

end

lemma anon0_correct:
assumes 
A1:"(red_cmd_list \<Gamma> [(Assume (BinOp (Val (IntV 5)) Le (FunExp ''f'' [(Var ''x'')]))), (Assume (BinOp (Var ''y'') Le (Val (IntV 4)))), (Assert (BinOp (Var ''y'') Le (FunExp ''f'' [(Var ''x'')])))] (Normal n_s) s')" and 
A2:"((n_s ''x'') = (Some (IntV vc_x)))" and 
A3: "((n_s ''y'') = (Some (IntV vc_y)))" and 
A4: "(((snd \<Gamma>) ''f'') = (Some isa_f))" and 
A5: "(\<forall> farg0. ((isa_f [(IntV farg0)]) = (Some (IntV (vc_f farg0)))))" and 
A6: "(vc.vc_anon0 vc_x vc_y vc_f)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
  using assms
  apply cases
  apply handle_assume
  apply (erule RedCmdListCons_case)
  apply handle_assume
  apply (erule RedCmdListCons_case)
  apply (drule assert_correct)
  apply simp
  subgoal
    apply (simp? ; ( (simp add: assms | (rule+)), (simp add: assms)?)+)
    thm vc.vc_anon0_assert1_elim
    apply (rule vc.vc_anon0_assert1_elim)     
      using A6
      apply (rule impE)
        apply (metis A5 binop_lessOrEqual.elims list.collapse option.distinct(1) option.inject val.inject(1) val.inject(2))     
      apply simp
    subgoal
(*     using vc.vc_anon0_assert1_def by blast *)
      
      
  apply (handle_assert P: assms)
  (*
  apply (handle_cmd_list P: assms) 
  using assms 
  apply (smt binop_lessOrEqual.simps(1) list.exhaust_sel option.inject val.inject(1))
  by blast
  *)
  

(*apply (metis (no_types, lifting) binop_lessOrEqual.simps(1) list.exhaust_sel list.collapse option.inject val.inject(1))*)
using assms
 
 


lemma PreconditionGeneratedEntry_correct:
assumes 
"(red_cmd_list \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"((n_s ''y'') = (Some (IntV vc_y)))" and 
"(((snd \<Gamma>) ''f'') = (Some isa_f))" and 
"(\<forall> farg0. ((isa_f [(IntV farg0)]) = (Some (IntV (vc_f farg0)))))" and 
"(vc.vc_PreconditionGeneratedEntry vc_x vc_y vc_f)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_PreconditionGeneratedEntry vc_x vc_y vc_f)))))"
using assms
  apply cases
  apply simp
(*apply (metis (no_types, lifting) binop_lessOrEqual.simps(1) list.collapse option.inject val.inject(1))?*)
done


end
