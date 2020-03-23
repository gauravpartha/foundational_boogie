theory Util
imports Semantics "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
begin

lemma assert_correct:
  "\<lbrakk>\<Lambda>,\<Gamma> \<turnstile> \<langle>Assert e, Normal n_s\<rangle> \<rightarrow> s; \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> (BoolV True) \<rbrakk> \<Longrightarrow> s = Normal n_s"
  by (erule red_cmd.cases; simp; blast dest: expr_eval_determ(1))

(*TODO, rewrite this as an elimination rule to be consistent with other rules *)
lemma assert_correct_2:
  "\<lbrakk>\<Lambda>,\<Gamma> \<turnstile> \<langle>Assert e, s\<rangle> \<rightarrow> s'; s = Normal n_s; \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> (BoolV True)\<rbrakk> \<Longrightarrow> s' = Normal n_s"
  by (erule red_cmd.cases; simp; blast dest: expr_eval_determ(1))

lemma assume_cases_2: 
  "\<lbrakk>\<Lambda>,\<Gamma> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> s; 
    s = Magic \<Longrightarrow> P; 
    s = Normal n_s \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd.cases; simp)

lemma assume_cases_ext: 
  "\<lbrakk>\<Lambda>,\<Gamma> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> s; 
    s = Magic \<Longrightarrow> P; 
    s = Normal n_s \<Longrightarrow> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> (BoolV True) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd.cases; simp)

lemma assume_cases_ext_2: 
  "\<lbrakk>\<Lambda>,\<Gamma> \<turnstile> \<langle>Assume e, s\<rangle> \<rightarrow> s'; 
    s = Normal n_s;
    s' = Magic \<Longrightarrow> P; 
    s' = Normal n_s \<Longrightarrow> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> (BoolV True) \<Longrightarrow>  P \<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd.cases; simp)

lemma single_assign_cases:
  "\<lbrakk>\<Lambda>,\<Gamma> \<turnstile> \<langle>Assign [(x,e)], s\<rangle> \<rightarrow> s'; 
   s = Normal n_s;
   \<And>v. \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v \<Longrightarrow> s' = Normal (n_s(x \<mapsto> v)) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (erule red_cmd.cases; simp)
  apply (erule red_exprs.cases; simp)
  by auto

lemma havoc_cases:
  "\<lbrakk>\<Lambda>,\<Gamma> \<turnstile> \<langle>Havoc x, s\<rangle> \<rightarrow> s';
    s = Normal n_s;
    \<Lambda> x = Some ty;
    \<And>v. type_of_val v = ty \<Longrightarrow> s' = Normal (n_s(x \<mapsto> v)) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd.cases; simp)

lemma type_of_val_int_elim:
  "\<lbrakk> type_of_val v = TInt;
     \<And>i. v = IntV i \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  by (cases v; auto)

lemma type_of_val_bool_elim:
  "\<lbrakk> type_of_val v = TBool;
     \<And>b. v = BoolV b \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  by (cases v; auto)

lemma val_elim [elim!]:
 "\<lbrakk> \<Gamma> \<turnstile> \<langle>Val v, n_s\<rangle> \<Down> v'; v = v' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (erule red_expr.cases; simp)

lemma cons_exp_elim :
 "\<Gamma> \<turnstile> \<langle>e # es, n_s\<rangle> [\<Down>] vs \<Longrightarrow> (vs \<noteq> [] \<Longrightarrow> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> hd vs \<Longrightarrow> \<Gamma> \<turnstile> \<langle>es, n_s\<rangle> [\<Down>] tl vs \<Longrightarrow> P) \<Longrightarrow> P"
  by (erule red_exprs.cases; simp_all)

lemma cons_exp_elim2:
  "\<lbrakk>\<Gamma> \<turnstile> \<langle>e # es, n_s\<rangle> [\<Down>] vs;
   \<And>v vs'. vs = v # vs' \<Longrightarrow> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v \<Longrightarrow> \<Gamma> \<turnstile> \<langle>es, n_s\<rangle> [\<Down>] vs' \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" 
  by (erule red_exprs.cases; simp_all)

lemma singleton_exp:
  "\<Gamma> \<turnstile> \<langle>[e], n_s\<rangle> [\<Down>] vs \<Longrightarrow> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> hd vs"
  by (auto elim: cons_exp_elim)

lemma nil_exp_elim [elim!]:
 "\<lbrakk>\<Gamma> \<turnstile> \<langle>[], n_s\<rangle> [\<Down>] vs; vs = [] \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
 by (erule red_exprs.cases; simp)


lemma nil_cmd_elim [elim!]:
 "\<lbrakk>\<Lambda>,\<Gamma> \<turnstile> \<langle>[], s\<rangle> [\<rightarrow>] s'; s' = s \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd_list.cases; simp)

lemma magic_stays_cmd_list_2:
  assumes "\<Lambda>,\<Gamma> \<turnstile> \<langle>cs, s\<rangle> [\<rightarrow>] s'" and "s = Magic"
  shows   "s' = Magic"
  using assms
  by (simp add: magic_stays_cmd_list)

(* new version *)
method reduce_expr_full = 
        (( erule RedBinOp_case |
           erule RedFunOp_case |
           erule RedUnOp_case |
           erule val_elim |
           erule cons_exp_elim | 
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
          rule RedVal |
          rule RedBinOp |
          rule RedUnOp |
          rule RedFunOp |
          rule RedExpListNil |
          rule RedExpListCons)) |
  ((match conclusion in 
                       "?R = Some ?x" \<Rightarrow> \<open>fail?\<close>), (solves simp | fastforce) )
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
(erule havoc_cases, assumption, (simp only: v_assms),
 (erule type_of_val_int_elim | erule type_of_val_bool_elim)
)

method handle_cmd_list_full uses v_assms = 
(
  (( ( handle_assume_full | handle_assert_full |
        handle_assign_full | (handle_havoc_full v_assms: v_assms)),
      (erule RedCmdListCons_case | erule nil_cmd_elim) )
   )+
)

lemma test: " Q \<longrightarrow> P \<Longrightarrow> Q \<Longrightarrow> P"
  by (match premises in I: "Q \<longrightarrow> P" and I': Q \<Rightarrow> \<open>insert mp [OF I I']\<close>)

method foo =
  (match conclusion in "?P \<and> ?Q" \<Rightarrow> \<open>fail\<close> \<bar> "?R" \<Rightarrow> \<open>fail\<close>)

method test1 =
  (match conclusion in "?P = Some ?x" \<Rightarrow> fastforce \<bar>
                       "?P = None" \<Rightarrow> \<open>fail\<close> )
 

end