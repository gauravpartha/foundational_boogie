theory vc_m
imports Semantics Util
begin
locale vc = 
fixes x :: "int" and f :: "(int => int)" and g :: "(int => bool)"
begin

definition vc_anon0_assert1
  where
   "vc_anon0_assert1 = (((f x) + 4) \<le> 5)"

thm mp[of vc_anon0_assert1]


definition vc_anon0
  where
    "vc_anon0  = (((g x) \<and> ((f x) \<le> 0)) \<longrightarrow> ((((x \<le> 1) \<and> (x \<le> 2)) \<and> (x \<le> 3)) \<longrightarrow> ((((f x) + 4) \<le> 5) \<and> ((((f x) + 4) \<le> 5) \<longrightarrow> ((x \<le> 4) \<longrightarrow> (x \<le> 5))))))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry  = vc_anon0"

end

locale vc2 = 
fixes x :: "int" and f :: "(int => int)" and g :: "(int => bool)"
begin

definition vc_anon0_assert1
  where
   "vc_anon0_assert1 = (((f x) + 4) \<le> 5)"

definition vc_anon0_assert2
  where
    "vc_anon0_assert2 = (x \<le> 5)"

thm mp[of vc_anon0_assert1]

definition vc_anon0
  where
    "vc_anon0  = (((g x) \<and> ((f x) \<le> 0)) \<longrightarrow> ((((x \<le> 1) \<and> (x \<le> 2)) \<and> (x \<le> 3)) \<longrightarrow> (vc_anon0_assert1 \<and> (((x \<le> 4) \<longrightarrow> vc_anon0_assert2)))))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry  = vc_anon0"

lemma vc_correct: vc_PreconditionGeneratedEntry
  apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def vc_anon0_assert1_def vc_anon0_assert2_def)
  by smt

end
thm mp[of "vc2.vc_anon0_assert1 _ _"]


lemma anon0_correct_raw:
assumes 
"(red_cmd_list \<Gamma> [(Assume (BinOp (FunExp ''g'' [(Var ''x'')]) And (BinOp (FunExp ''f'' [(Var ''x'')]) Le (Val (IntV 0))))), (Assume (BinOp (BinOp (BinOp (Var ''x'') Le (Val (IntV 1))) And (BinOp (Var ''x'') Le (Val (IntV 2)))) And (BinOp (Var ''x'') Le (Val (IntV 3))))), (Assert (BinOp (BinOp (FunExp ''f'' [(Var ''x'')]) Add (Val (IntV 4))) Le (Val (IntV 5)))), (Assume (BinOp (Var ''x'') Le (Val (IntV 4)))), (Assert (BinOp (Var ''x'') Le (Val (IntV 5))))] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(((snd \<Gamma>) ''f'') = (Some isa_f))" and 
"(\<forall> farg0. ((isa_f [(IntV farg0)]) = (Some (IntV (vc_f farg0)))))" and 
"(((snd \<Gamma>) ''g'') = (Some isa_g))" and 
"(\<forall> farg0. ((isa_g [(IntV farg0)]) = (Some (BoolV (vc_g farg0)))))" and 
"(vc.vc_anon0 vc_x vc_f vc_g)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms
apply cases
  apply (handle_cmd_list P: assms)
  apply (simp only: vc.vc_anon0_def) (*not required*)
  apply (smt binop_and.simps(1) binop_lessOrEqual.simps(1) list.exhaust_sel option.inject val.inject(1))
  apply (erule RedCmdListCons_case)
  apply ( rule assume_cases_2)
  apply simp
  apply (
  (blast dest: magic_stays_cmd_list), simp)
  apply (rule RedCmdListCons_case)
  apply assumption
  apply (handle_assert)
  apply auto
  done
               
lemma anon0_correct_opaque:
assumes 
"(red_cmd_list \<Gamma> [(Assume (BinOp (FunExp ''g'' [(Var ''x'')]) And (BinOp (FunExp ''f'' [(Var ''x'')]) Le (Val (IntV 0))))), (Assume (BinOp (BinOp (BinOp (Var ''x'') Le (Val (IntV 1))) And (BinOp (Var ''x'') Le (Val (IntV 2)))) And (BinOp (Var ''x'') Le (Val (IntV 3))))), (Assert (BinOp (BinOp (FunExp ''f'' [(Var ''x'')]) Add (Val (IntV 4))) Le (Val (IntV 5)))), (Assume (BinOp (Var ''x'') Le (Val (IntV 4)))), (Assert (BinOp (Var ''x'') Le (Val (IntV 5))))] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(((snd \<Gamma>) ''f'') = (Some isa_f))" and 
"(\<forall> farg0. ((isa_f [(IntV farg0)]) = (Some (IntV (vc_f farg0)))))" and 
"(((snd \<Gamma>) ''g'') = (Some isa_g))" and 
"(\<forall> farg0. ((isa_g [(IntV farg0)]) = (Some (BoolV (vc_g farg0)))))" and 
A6:"(vc2.vc_anon0 vc_x vc_f vc_g)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms
  apply cases
  apply (handle_assume)
  apply (erule RedCmdListCons_case)
  apply (handle_assume)
  apply (erule RedCmdListCons_case)
  apply (handle_assert)
  apply (rule mp[of "(vc2.vc_anon0_assert1 vc_x vc_f)"])
(*apply (metis (no_types, lifting) binop_and.simps binop_lessOrEqual.simps list.exhaust_sel list.collapse option.inject val.inject) *)
  apply rule
  apply (simp only: vc2.vc_anon0_assert1_def)
  apply (simp only: vc2.vc_anon0_def)
  apply (smt binop_and.simps(1) binop_lessOrEqual.simps(1) list.exhaust_sel option.inject val.inject(1))
  apply (erule RedCmdListCons_case)
  apply simp
  apply (handle_assume)
  apply simp
  apply (erule RedCmdListCons_case)
  apply (handle_assert)
  by auto
  
  

lemma anon0_correct_assertions_opaque_isar:
assumes 
"(red_cmd_list \<Gamma> [(Assume (BinOp (FunExp ''g'' [(Var ''x'')]) And (BinOp (FunExp ''f'' [(Var ''x'')]) Le (Val (IntV 0))))), (Assume (BinOp (BinOp (BinOp (Var ''x'') Le (Val (IntV 1))) And (BinOp (Var ''x'') Le (Val (IntV 2)))) And (BinOp (Var ''x'') Le (Val (IntV 3))))), (Assert (BinOp (BinOp (FunExp ''f'' [(Var ''x'')]) Add (Val (IntV 4))) Le (Val (IntV 5)))), (Assume (BinOp (Var ''x'') Le (Val (IntV 4)))), (Assert (BinOp (Var ''x'') Le (Val (IntV 5))))] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(((snd \<Gamma>) ''f'') = (Some isa_f))" and 
"(\<forall> farg0. ((isa_f [(IntV farg0)]) = (Some (IntV (vc_f farg0)))))" and 
"(((snd \<Gamma>) ''g'') = (Some isa_g))" and 
"(\<forall> farg0. ((isa_g [(IntV farg0)]) = (Some (BoolV (vc_g farg0)))))" and 
VC:"(vc2.vc_anon0 vc_x vc_f vc_g)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
  using assms
proof  (cases)
  case (RedCmdListCons s')
  from local.RedCmdListCons(1)
  show ?thesis
  proof (rule assume_cases_2)
    assume "s' = Magic"
    show ?thesis using local.RedCmdListCons(2) \<open>s' = Magic\<close> by (blast dest: magic_stays_cmd_list)
  next
    assume "s' = Normal n_s"
    have A1:"vc_g vc_x \<and> vc_f vc_x \<le> 0" using local.RedCmdListCons(1) \<open>s' = Normal n_s\<close>
      apply simp
      apply (erule RedAssumeOk_case)
      apply (reduce_assm_expr)
      using assms(1-6)
      
      (*by (metis (no_types, lifting) binop_and.simps(1) binop_eval.simps(3) binop_eval.simps(4) binop_lessOrEqual.simps(1) list.collapse option.inject val.inject(1))    *)
    from local.RedCmdListCons(2) \<open>s' = Normal n_s\<close> show ?thesis    
    proof (simp,cases)
      case (RedCmdListCons s'')      
      show ?thesis using local.RedCmdListCons(1) \<open>s' = Normal n_s\<close>
        thm assume_cases_ext_2
      proof (rule assume_cases_ext_2)          
        assume "s'' = Magic"
        show ?thesis using local.RedCmdListCons(2) \<open>s'' = Magic\<close> by (blast dest: magic_stays_cmd_list)    
      next
        assume "s'' = Normal n_s"
        have A2:"vc_x \<le> 1 \<and> vc_x \<le> 2 \<and> vc_x \<le> 3" using local.RedCmdListCons(1) \<open>s' = Normal n_s\<close> \<open>s'' = Normal n_s\<close>
          apply simp
          apply (erule RedAssumeOk_case)
          apply (reduce_assm_expr)
          using assms(1-6) 
          using option.inject val.inject(1) by auto
        from local.RedCmdListCons(2) \<open>s'' = Normal n_s\<close> show ?thesis
        proof (simp, cases)
          case (RedCmdListCons s')          
          have "s' = Normal n_s" 
            apply (rule rev_mp[of "vc2.vc_anon0_assert1 vc_x vc_f"])
            using A1 A2 VC
             apply (simp only: vc2.vc_anon0_def)
            apply (rule impI)
            apply (rule assert_correct_2[OF local.RedCmdListCons(1) \<open>s'' = Normal n_s\<close>])
            apply (simp only: vc2.vc_anon0_assert1_def)
            apply (reduce_assert_expr P: assms(1-6))
            done
          from local.RedCmdListCons(2) \<open>s' = Normal n_s\<close> show ?thesis
          proof (simp, cases)
            case (RedCmdListCons s'')
            show ?thesis using local.RedCmdListCons(1) \<open>s' = Normal n_s\<close>
            proof (rule assume_cases_3)          
              assume "s'' = Magic"
              show ?thesis using local.RedCmdListCons(2) \<open>s'' = Magic\<close> by (blast dest: magic_stays_cmd_list)    
            next
              assume "s'' = Normal n_s"
              have A3:"vc_x \<le> 4" using local.RedCmdListCons(1) \<open>s' = Normal n_s\<close> \<open>s'' = Normal n_s\<close>
              apply simp
              apply (erule RedAssumeOk_case)
              apply (reduce_assm_expr)
              using assms(1-6)
              using option.inject val.inject(1) by auto
            show ?thesis using local.RedCmdListCons(2) \<open>s'' = Normal n_s\<close> 
            proof (simp, cases)
              case (RedCmdListCons s')
              have "s' = Normal n_s"
                apply (rule rev_mp[of "vc2.vc_anon0_assert2 vc_x"])
                using A1 A2 A3 VC
                 apply (simp only: vc2.vc_anon0_def)
                apply (rule impI)
                apply (rule assert_correct_2[OF local.RedCmdListCons(1) \<open>s'' = Normal n_s\<close>])
                apply (simp only: vc2.vc_anon0_assert2_def)
                apply (reduce_assert_expr P: assms(1-6))
                done
              from local.RedCmdListCons(2)  show ?thesis
                apply (rule nil_cmd_elim )
                using \<open>s' = Normal n_s\<close>
                by simp
            qed
          qed
        qed
      qed
    qed
  qed
qed
qed
  

lemma PreconditionGeneratedEntry_correct:
assumes 
"(red_cmd_list \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''x'') = (Some (IntV vc_x)))" and 
"(((snd \<Gamma>) ''f'') = (Some isa_f))" and 
"(\<forall> farg0. ((isa_f [(IntV farg0)]) = (Some (IntV (vc_f farg0)))))" and 
"(((snd \<Gamma>) ''g'') = (Some isa_g))" and 
"(\<forall> farg0. ((isa_g [(IntV farg0)]) = (Some (BoolV (vc_g farg0)))))" and 
"(vc.vc_PreconditionGeneratedEntry vc_x vc_f vc_g)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_PreconditionGeneratedEntry vc_x vc_f vc_g)))))"
using assms
  oops




end
