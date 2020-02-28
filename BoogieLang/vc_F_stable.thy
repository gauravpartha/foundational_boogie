theory vc_F_stable
imports Semantics Util
begin
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
lemma vc_correct:

shows "vc_anon0"
apply (simp only: vc_anon0_def vc_anon3_Else_def vc_anon3_Then_def vc_GeneratedUnifiedExit_def)
  by linarith


end

lemma GeneratedUnifiedExit_correct:
assumes 
"(red_cmd_list \<Gamma> [(Assert (BinOp (BinOp (Val (IntV 100)) Lt (Var ''n'')) Imp (BinOp (Var ''r_1'') Eq (BinOp (Var ''n'') Sub (Val (IntV 10)))))), (Assert (BinOp (BinOp (Var ''n'') Le (Val (IntV 100))) Imp (BinOp (Var ''r_1'') Eq (Val (IntV 91)))))] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV n)))" and 
"((n_s ''vc_r_0'') = (Some (IntV vc_r_0)))" and 
"((n_s ''vc_call0formal_n_0'') = (Some (IntV vc_call0formal_n_0)))" and 
"((n_s ''vc_call1formal_r_0'') = (Some (IntV vc_call1formal_r_0)))" and 
"((n_s ''vc_call1formal_r_0_0'') = (Some (IntV vc_call1formal_r_0_0)))" and 
"((n_s ''r_1'') = (Some (IntV r_1)))" and 
"(vc.vc_GeneratedUnifiedExit n r_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms
apply cases
apply (simp only: vc.vc_GeneratedUnifiedExit_def)
  apply handle_cmd_list_full
by (auto?)

lemma anon3_Then_correct:
assumes 
"(red_cmd_list \<Gamma> [(Assume (BinOp (Val (IntV 100)) Lt (Var ''n''))), (Assume (BinOp (Var ''vc_r_0'') Eq (BinOp (Var ''n'') Sub (Val (IntV 10))))), (Assume (BinOp (Var ''r_1'') Eq (Var ''vc_r_0'')))] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV n)))" and 
"((n_s ''vc_r_0'') = (Some (IntV vc_r_0)))" and 
"((n_s ''vc_call0formal_n_0'') = (Some (IntV vc_call0formal_n_0)))" and 
"((n_s ''vc_call1formal_r_0'') = (Some (IntV vc_call1formal_r_0)))" and 
"((n_s ''vc_call1formal_r_0_0'') = (Some (IntV vc_call1formal_r_0_0)))" and 
"((n_s ''r_1'') = (Some (IntV r_1)))" and 
"(vc.vc_anon3_Then n vc_r_0 r_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_GeneratedUnifiedExit n r_1)))))"
using assms
apply cases
apply (simp only: vc.vc_anon3_Then_def)
apply (handle_cmd_list_full?)
  by (auto?)

method handle_assume_opaque uses P = 
 ( simp, (erule RedAssumeOk_case), (reduce_assm_expr),
        (auto simp add: P))

lemma anon3_Else_correct:
assumes 
"(red_cmd_list \<Gamma> [
(Assume (BinOp (Var ''n'') Le (Val (IntV 100)))),
 (Assume (BinOp (Var ''vc_call0formal_n_0'') Eq (BinOp (Var ''n'') Add (Val (IntV 11))))),
 (Assume (BinOp (BinOp (Val (IntV 100)) Lt (Var ''vc_call0formal_n_0'')) Imp 
           (BinOp (Var ''vc_call1formal_r_0'') Eq (BinOp (Var ''vc_call0formal_n_0'') Sub (Val (IntV 10)))))),
 (Assume (BinOp (BinOp (Var ''vc_call0formal_n_0'') Le (Val (IntV 100))) Imp
           (BinOp (Var ''vc_call1formal_r_0'') Eq (Val (IntV 91))))),
 (Assume (BinOp (BinOp (Val (IntV 100)) Lt (Var ''vc_call1formal_r_0'')) Imp 
           (BinOp (Var ''vc_call1formal_r_0_0'') Eq (BinOp (Var ''vc_call1formal_r_0'') Sub (Val (IntV 10)))))),
 (Assume (BinOp (BinOp (Var ''vc_call1formal_r_0'') Le (Val (IntV 100))) Imp 
           (BinOp (Var ''vc_call1formal_r_0_0'') Eq (Val (IntV 91))))),
 (Assume (BinOp (Var ''r_1'') Eq (Var ''vc_call1formal_r_0_0'')))]
 (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV n)))" and 
"((n_s ''vc_r_0'') = (Some (IntV vc_r_0)))" and 
"((n_s ''vc_call0formal_n_0'') = (Some (IntV vc_call0formal_n_0)))" and 
"((n_s ''vc_call1formal_r_0'') = (Some (IntV vc_call1formal_r_0)))" and 
"((n_s ''vc_call1formal_r_0_0'') = (Some (IntV vc_call1formal_r_0_0)))" and 
"((n_s ''r_1'') = (Some (IntV r_1)))" and 
"(vc.vc_anon3_Else n vc_call0formal_n_0 vc_call1formal_r_0 vc_call1formal_r_0_0 r_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_GeneratedUnifiedExit n r_1)))))"
  using assms
  apply cases
  apply (simp only: vc.vc_GeneratedUnifiedExit_def)
  apply handle_cmd_list_full
by (auto?)


(*
proof (cases)
  case (RedCmdListCons s')
  from local.RedCmdListCons(1)
  show ?thesis
  proof (rule assume_cases_2)
    assume "s' = Magic"
    show ?thesis using local.RedCmdListCons(2) \<open>s' = Magic\<close> by (blast dest: magic_stays_cmd_list)
  next
    assume "s' = Normal n_s"
    have A1: "n \<le> 100" using local.RedCmdListCons(1) \<open>s' = Normal n_s\<close>
      apply simp
      apply (erule RedAssumeOk_case)
      apply (reduce_assm_expr)
      using assms(1-6) 
      using option.inject val.inject(1) by auto
    from local.RedCmdListCons(2) \<open>s' = Normal n_s\<close> show ?thesis
    proof (simp, cases)
      case (RedCmdListCons s'')
      from local.RedCmdListCons(1) \<open>s' = Normal n_s\<close>
      show ?thesis
      proof (rule assume_cases_ext_2)
        assume "s'' = Magic"
        show ?thesis using local.RedCmdListCons(2) \<open>s'' = Magic\<close> by (blast dest: magic_stays_cmd_list)
      next
        assume "s'' = Normal n_s"
        have A2: "vc_call0formal_n_0 = n + 11"  using local.RedCmdListCons(1) \<open>s'' = Normal n_s\<close> \<open>s' = Normal n_s\<close>
        apply simp
        apply (erule RedAssumeOk_case, reduce_assm_expr)      
          by  (auto simp add: assms(1-6))
        from local.RedCmdListCons(2) \<open>s'' = Normal n_s\<close> show ?thesis
        proof (simp, cases)
              case (RedCmdListCons s')
      from local.RedCmdListCons(1) \<open>s'' = Normal n_s\<close>
      show ?thesis
      proof (rule assume_cases_ext_2)
        assume "s' = Magic"
        show ?thesis using local.RedCmdListCons(2) \<open>s' = Magic\<close> by (blast dest: magic_stays_cmd_list)
      next
        assume "s' = Normal n_s"         
        have A3: "100 < vc_call0formal_n_0 \<longrightarrow> (vc_call1formal_r_0 = vc_call0formal_n_0 - 10)"
          using local.RedCmdListCons(1) \<open>s'' = Normal n_s\<close>
        proof (rule assume_cases_ext_2)
          assume "s' = Magic"
          thus ?thesis using \<open>s' = Normal n_s\<close> by simp
        next
          assume B1: "\<Gamma> \<turnstile> \<langle>Val (IntV
               100) \<guillemotleft>Lt\<guillemotright> Var ''vc_call0formal_n_0'' \<guillemotleft>Imp\<guillemotright> (Var ''vc_call1formal_r_0'' \<guillemotleft>Eq\<guillemotright> (Var
                           ''vc_call0formal_n_0'' \<guillemotleft>Sub\<guillemotright> Val (IntV 10))),n_s\<rangle> \<Down> BoolV True"
          thus ?thesis
          proof (cases)
            case (RedBinOp v1 v2)
            from local.RedBinOp(1) have "v1 = BoolV (100 < vc_call0formal_n_0) " 
              apply (rule RedBinOp_case)
              apply reduce_assm_expr_full
              using assms(4)
              by auto
              
          
(*        
          apply simp 
          apply (erule RedAssumeOk_case, reduce_assm_expr)
          using option.inject val.inject(1) assms(1-6)
          apply subst*)
        

  oops
*)


lemma anon0_correct:
assumes 
"(red_cmd_list \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV n)))" and 
"((n_s ''vc_r_0'') = (Some (IntV vc_r_0)))" and 
"((n_s ''vc_call0formal_n_0'') = (Some (IntV vc_call0formal_n_0)))" and 
"((n_s ''vc_call1formal_r_0'') = (Some (IntV vc_call1formal_r_0)))" and 
"((n_s ''vc_call1formal_r_0_0'') = (Some (IntV vc_call1formal_r_0_0)))" and 
"((n_s ''r_1'') = (Some (IntV r_1)))" and 
"(vc.vc_anon0 n vc_r_0 vc_call0formal_n_0 vc_call1formal_r_0 vc_call1formal_r_0_0 r_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon3_Then n vc_r_0 r_1) \<and> (vc.vc_anon3_Else n vc_call0formal_n_0 vc_call1formal_r_0 vc_call1formal_r_0_0 r_1))))))"
using assms
apply cases
apply (simp only: vc.vc_anon0_def)
apply (handle_cmd_list_full?)
by (auto?)


end
