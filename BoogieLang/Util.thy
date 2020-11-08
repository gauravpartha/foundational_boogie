theory Util
imports Semantics "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
begin

lemma finterp_extract_1: "fun_interp_wf A fds \<Gamma> \<Longrightarrow> map_of fds fn = Some fd \<Longrightarrow> \<Gamma> fn = Some f \<Longrightarrow> 
  fun_interp_single_wf A fd f"
  by (metis fun_interp_wf_def option.sel)

lemma finterp_extract_2: "fun_interp_wf A fds \<Gamma> \<Longrightarrow> map_of fds fn = Some fd \<Longrightarrow> \<Gamma> fn = Some f \<Longrightarrow>
   fun_interp_single_wf_2 A fd f"
  by (metis fun_interp_wf_def option.sel)

lemma assert_correct:
  "\<lbrakk>A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>Assert e, Normal n_s\<rangle> \<rightarrow> s; A,\<Gamma>,\<Delta> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool True) \<rbrakk> \<Longrightarrow> s = Normal n_s"
  by (erule red_cmd.cases; simp; blast dest: expr_eval_determ(1))

(*TODO, rewrite this as an elimination rule to be consistent with other rules *)
lemma assert_correct_2:
  "\<lbrakk>A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>Assert e, s\<rangle> \<rightarrow> s'; s = Normal n_s; A,\<Gamma>,\<Delta> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool True)\<rbrakk> \<Longrightarrow> s' = Normal n_s"
  by (erule red_cmd.cases; simp; blast dest: expr_eval_determ(1))

lemma assert_ml: 
"\<lbrakk> A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>(Assert e) # cs, Normal ns\<rangle> [\<rightarrow>] s';
  A,\<Gamma>,\<Delta> \<turnstile> \<langle>e, ns\<rangle> \<Down> LitV (LBool True);
  A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>cs, Normal ns\<rangle> [\<rightarrow>] s' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (erule RedCmdListCons_case)
  by (blast dest: assert_correct)

lemma assert_true_cmds: 
"\<lbrakk> A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>(Assert (Lit (LBool True))) # cs, Normal ns\<rangle> [\<rightarrow>] s';
  A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>cs, Normal ns\<rangle> [\<rightarrow>] s' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto intro: RedLit elim: assert_ml)

lemma imp_conj_assoc: "(A \<and> B) \<and> C \<longrightarrow> D \<Longrightarrow> A \<and> (B \<and> C) \<longrightarrow> D"
  by simp

lemma imp_conj_imp: "(A \<and> B) \<longrightarrow> D \<Longrightarrow> A \<longrightarrow> (B \<longrightarrow> D)"
  by simp

lemma imp_conj_elim: "A \<and> B \<longrightarrow> D \<Longrightarrow> A \<Longrightarrow> ((B \<longrightarrow> D) \<Longrightarrow> R) \<Longrightarrow> R"
  by simp

lemma imp_not_elim: "\<not>A \<Longrightarrow> A \<Longrightarrow> (False \<Longrightarrow> R) \<Longrightarrow> R"
  by simp

lemma conj_elim_2: "A \<and> B \<Longrightarrow> (B \<Longrightarrow> R) \<Longrightarrow> R"
  by simp

lemma conj_imp_elim: "(A \<and> (A \<longrightarrow> B)) \<Longrightarrow> (B \<Longrightarrow> R) \<Longrightarrow> R"
  by simp

method tryRepeatConjI = ((rule conjI)+ | tactic \<open>all_tac\<close>)

(* use opaque composition to deal with lemmas such as "\<Gamma> ''f'' = Some ((the \<circ> \<Gamma>) ''f'')", which
lead to non-terminating tactics most likely due to \<Gamma> ''f'' appearing on both sides *)
definition opaque_comp 
  where "opaque_comp f g x = f (g x)"

lemma axioms_sat_mem: "a \<in> set(as) \<Longrightarrow> axioms_sat A \<Gamma> ns as \<Longrightarrow> A,\<Gamma>,[] \<turnstile> \<langle>a, ns\<rangle> \<Down> LitV (LBool (True))"
 by (simp add: axioms_sat_def axiom_sat_def list_all_iff)

lemma assume_cases_2: 
  "\<lbrakk>A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> s; 
    s = Magic \<Longrightarrow> P; 
    s = Normal n_s \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd.cases; simp)

lemma assume_cases_ext: 
  "\<lbrakk>A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> s; 
    s = Magic \<Longrightarrow> P; 
    s = Normal n_s \<Longrightarrow> A,\<Gamma>,\<Delta> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool True) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd.cases; simp)

lemma assume_cases_ext_2: 
  "\<lbrakk>A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>Assume e, s\<rangle> \<rightarrow> s'; 
    s = Normal n_s;
    s' = Magic \<Longrightarrow> P; 
    s' = Normal n_s \<Longrightarrow> A,\<Gamma>,\<Delta> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool True) \<Longrightarrow>  P \<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd.cases; simp)

lemma assume_ml: 
  "\<lbrakk>A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>(Assume e) # cs, Normal ns\<rangle> [\<rightarrow>] s';
       s' = Magic \<Longrightarrow> P;
        A,\<Gamma>,\<Delta> \<turnstile> \<langle>e, ns\<rangle> \<Down> LitV (LBool True) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>cs, Normal ns\<rangle> [\<rightarrow>] s' \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply (erule RedCmdListCons_case)
  by (metis assume_cases_ext magic_stays_cmd_list)

lemma assume_false_cmds:
  "\<lbrakk>A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>(Assume (Lit (LBool False))) # cs, Normal ns\<rangle> [\<rightarrow>] s';
       s' = Magic \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply (erule RedCmdListCons_case)
  by (metis RedAssertFail RedLit assert_correct assume_cases_ext magic_stays_cmd_list state.distinct(1))

  (*by (metis RedLit assume_cases_ext expr_eval_determ(1) magic_stays_cmd_list val.inject(1))*)

lemma assume_true_cmds: 
  "\<lbrakk>A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>(Assume e) # cs, Normal ns\<rangle> [\<rightarrow>] s';
       s' = Magic \<Longrightarrow> P;
       A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>cs, Normal ns\<rangle> [\<rightarrow>] s' \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (rule assume_ml)

lemma single_assign_cases:
  "\<lbrakk>A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>Assign [(x,e)], s\<rangle> \<rightarrow> s'; 
   s = Normal n_s;
   \<And>v. A,\<Gamma>,\<Delta> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v \<Longrightarrow> s' = Normal (n_s(x \<mapsto> v)) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (erule red_cmd.cases; simp)
  apply (erule red_exprs.cases; simp)
  by auto

lemma havoc_cases:
  "\<lbrakk>A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>Havoc x, s\<rangle> \<rightarrow> s';
    s = Normal n_s;
    \<Lambda> ! x = ty;
    \<And>v. type_of_val A v = ty \<Longrightarrow> s' = Normal (n_s(x \<mapsto> v)) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd.cases; simp) 

lemma type_of_val_int_elim:
  "\<lbrakk> type_of_val A v = TPrim TInt;
     \<And>i. v = LitV (LInt i) \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  apply (cases v)
   apply auto[2]
  by (metis lit.exhaust prim_ty.distinct(1) type_of_lit.simps(1))

lemma type_of_val_bool_elim:
  "\<lbrakk> type_of_val A v = TPrim TBool;
     \<And>b. v = LitV (LBool b) \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  apply (cases v)
   apply auto[2]
  by (metis lit.exhaust prim_ty.distinct(1) type_of_lit.simps(2))

 
lemma val_elim [elim!]:
 "\<lbrakk> A,\<Gamma>,\<Delta> \<turnstile> \<langle>Lit l, n_s\<rangle> \<Down> v'; (LitV l) = v' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (erule red_expr.cases; simp)

lemma cons_exp_elim :
 "A,\<Gamma>,\<Delta> \<turnstile> \<langle>e # es, n_s\<rangle> [\<Down>] vs \<Longrightarrow> (vs \<noteq> [] \<Longrightarrow> A,\<Gamma>,\<Delta> \<turnstile> \<langle>e, n_s\<rangle> \<Down> hd vs \<Longrightarrow> A,\<Gamma>,\<Delta> \<turnstile> \<langle>es, n_s\<rangle> [\<Down>] tl vs \<Longrightarrow> P) \<Longrightarrow> P"
  by (erule red_exprs.cases; simp_all)

lemma cons_exp_elim2:
  "\<lbrakk>A,\<Gamma>,\<Delta> \<turnstile> \<langle>e # es, n_s\<rangle> [\<Down>] vs;
   \<And>v vs'. vs = v # vs' \<Longrightarrow> A,\<Gamma>,\<Delta> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v \<Longrightarrow> A,\<Gamma>,\<Delta> \<turnstile> \<langle>es, n_s\<rangle> [\<Down>] vs' \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" 
  by (erule red_exprs.cases; simp_all)

lemma singleton_exp:
  "A,\<Gamma>,\<Delta> \<turnstile> \<langle>[e], n_s\<rangle> [\<Down>] vs \<Longrightarrow> A,\<Gamma>,\<Delta> \<turnstile> \<langle>e, n_s\<rangle> \<Down> hd vs"
  by (auto elim: cons_exp_elim)

lemma nil_exp_elim [elim!]:
 "\<lbrakk>A,\<Gamma>,\<Delta> \<turnstile> \<langle>[], n_s\<rangle> [\<Down>] vs; vs = [] \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
 by (erule red_exprs.cases; simp)


lemma nil_cmd_elim [elim!]:
 "\<lbrakk>A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>[], s\<rangle> [\<rightarrow>] s'; s' = s \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd_list.cases; simp)

lemma magic_stays_cmd_list_2:
  assumes "A,\<Lambda>,\<Gamma>,\<Delta> \<turnstile> \<langle>cs, s\<rangle> [\<rightarrow>] s'" and "s = Magic"
  shows   "s' = Magic"
  using assms
  by (simp add: magic_stays_cmd_list)

(* new version *)
method reduce_expr_full = 
        (( erule RedBinOp_case |
           erule RedFunOp_case |
           erule RedUnOp_case |
           erule val_elim |
           erule cons_exp_elim2 | 
           erule RedVar_case |
           erule nil_exp_elim))+

method assm_init_full = 
 ( erule assume_cases_ext_2,
   simp?,
  ((frule magic_stays_cmd_list_2), assumption, simp))

method handle_assume_full = ( assm_init_full, reduce_expr_full)

method reduce_assert_expr_full = 
  ((
          (rule RedVar |
          rule RedLit|
          rule RedBinOp |
          rule RedUnOp |
          rule RedFunOp |
          rule RedExpListNil |
          rule RedExpListCons)) |
  ((match conclusion in 
                       "?R = Some ?x" \<Rightarrow> \<open>fail?\<close>), (solves simp | solves fastforce) )
 (* Hack: 
    fastforce will only be executed,if match works, putting fastforce inside the match does not 
    seem to work: I guess the assumptions are not available *)
     )+

method handle_assert_full = (drule assert_correct_2, (assumption | simp)?, reduce_assert_expr_full)

(* simp is used in second subgoal if assertion is first command in list
   in that case, the goal is of the form "Normal n_s = Normal (?n_s3 s'a)", hence no assumption
   is used *)
method handle_assign_full = (erule single_assign_cases, (assumption | simp), reduce_expr_full)

method handle_havoc_full uses v_assms = 
(erule havoc_cases, (assumption | simp), (simp only: v_assms),
 (erule type_of_val_int_elim | erule type_of_val_bool_elim)
)

method handle_cmd_list_full uses v_assms = 
(
  (( ( handle_assume_full | handle_assert_full |
        handle_assign_full | (handle_havoc_full v_assms: v_assms)),
      (erule RedCmdListCons_case | erule nil_cmd_elim) )
   )+
)

lemmas relpowp_E2_2 =
  relpowp_E2[of _ _ "(n', s')" "(n'',s'')", split_rule]

lemma test: " Q \<longrightarrow> P \<Longrightarrow> Q \<Longrightarrow> P"
  by (match premises in I: "Q \<longrightarrow> P" and I': Q \<Rightarrow> \<open>insert mp [OF I I']\<close>)

method foo =
  (match conclusion in "?P \<and> ?Q" \<Rightarrow> \<open>fail\<close> \<bar> "?R" \<Rightarrow> \<open>fail\<close>)

method test1 =
  (match conclusion in "?P = Some ?x" \<Rightarrow> fastforce \<bar>
                       "?P = None" \<Rightarrow> \<open>fail\<close> )
 

end