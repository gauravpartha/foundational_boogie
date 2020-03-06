theory Util
imports Semantics "HOL-Eisbach.Eisbach" "HOL-Eisbach.Eisbach_Tools"
begin

lemma assert_correct:
  "\<lbrakk>\<Gamma> \<turnstile> \<langle>Assert e, Normal n_s\<rangle> \<rightarrow> s; \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> (BoolV True) \<rbrakk> \<Longrightarrow> s = Normal n_s"
  by (erule red_cmd.cases; simp; blast dest: expr_eval_determ(1))

lemma assert_correct_2:
  "\<lbrakk>\<Gamma> \<turnstile> \<langle>Assert e, s\<rangle> \<rightarrow> s'; s = Normal n_s; \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> (BoolV True)\<rbrakk> \<Longrightarrow> s' = Normal n_s"
  by (erule red_cmd.cases; simp; blast dest: expr_eval_determ(1))

lemma assume_cases_2: 
  "\<lbrakk>\<Gamma> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> s; 
    s = Magic \<Longrightarrow> P; 
    s = Normal n_s \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd.cases; simp)

lemma assume_cases_ext: 
  "\<lbrakk>\<Gamma> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> s; 
    s = Magic \<Longrightarrow> P; 
    s = Normal n_s \<Longrightarrow> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> (BoolV True) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd.cases; simp)

lemma assume_cases_ext_2: 
  "\<lbrakk>\<Gamma> \<turnstile> \<langle>Assume e, s\<rangle> \<rightarrow> s'; 
    s = Normal n_s;
    s' = Magic \<Longrightarrow> P; 
    s' = Normal n_s \<Longrightarrow> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> (BoolV True) \<Longrightarrow>  P \<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd.cases; simp)

lemma assign_cases:
  "\<lbrakk>\<Gamma> \<turnstile> \<langle>x := e, s\<rangle> \<rightarrow> s'; 
   s = Normal n_s;
   \<And>v. \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v \<Longrightarrow> s' = Normal (n_s(x \<mapsto> v)) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd.cases; simp)
   
lemma havoc_cases:
  "\<lbrakk>\<Gamma> \<turnstile> \<langle>Havoc x, s\<rangle> \<rightarrow> s';
    s = Normal n_s;
    \<And>v. s' = Normal (n_s(x \<mapsto> v)) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd.cases; simp)

lemma val_elim [elim!]:
 "\<lbrakk> \<Gamma> \<turnstile> \<langle>Val v, n_s\<rangle> \<Down> v'; v = v' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (erule red_expr.cases; simp)

lemma cons_exp_elim [elim!]:
 "\<Gamma> \<turnstile> \<langle>e # es, n_s\<rangle> [\<Down>] vs \<Longrightarrow> (vs \<noteq> [] \<Longrightarrow> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> hd vs \<Longrightarrow> \<Gamma> \<turnstile> \<langle>es, n_s\<rangle> [\<Down>] tl vs \<Longrightarrow> P) \<Longrightarrow> P"
  by (erule red_exprs.cases; simp_all)

lemma nil_exp_elim [elim!]:
 "\<lbrakk>\<Gamma> \<turnstile> \<langle>[], n_s\<rangle> [\<Down>] vs; vs = [] \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
 by (erule red_exprs.cases; simp)


lemma nil_cmd_elim [elim!]:
 "\<lbrakk>\<Gamma> \<turnstile> \<langle>[], s\<rangle> [\<rightarrow>] s'; s' = s \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (erule red_cmd_list.cases; simp)

method reduce_assm_expr = 
        (( erule RedBinOp_case |
           erule RedFunOp_case |
           erule RedUnOp_case |
           erule val_elim |
           erule cons_exp_elim | 
           erule RedVar_case |
           erule nil_exp_elim))+

method assm_init = 
 ( rule assume_cases_2,
  assumption,
  (blast dest: magic_stays_cmd_list), simp, (erule RedAssumeOk_case))

method handle_assume = (assm_init, reduce_assm_expr)

method reduce_assert_expr uses P = 
        (simp? ; ( (simp add: P | (rule+)), (simp add: P)?)+)

method handle_assert uses P = (drule assert_correct, (reduce_assert_expr P: P))

method handle_cmd_list uses P = 
 (handle_assume | (handle_assert), fastforce? |
      erule RedCmdListCons_case | erule nil_cmd_elim)+

(* new version *)
method reduce_assm_expr_full = 
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
  (blast dest: magic_stays_cmd_list))

method handle_assume_full = ( assm_init_full, reduce_assm_expr_full)

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

method handle_assert_full = (drule assert_correct_2, simp?, (reduce_assert_expr_full))

method handle_cmd_list_full = 
(
  (( ( handle_assume_full | (handle_assert_full)),
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