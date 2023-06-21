theory DeadVarElimination
  imports Boogie_Lang.Semantics Boogie_Lang.Util
begin

subsection \<open>Definition of free variables\<close>

fun free_var_expr :: "expr \<Rightarrow> vname set"
where 
  "free_var_expr (Var n) = {n}"
| "free_var_expr (BVar n) = {}"
| "free_var_expr (Lit n) = {}"
| "free_var_expr (UnOp unop ex) = free_var_expr (ex)"
| "free_var_expr (BinOp ex1 binop ex2) = free_var_expr (ex1) \<union> free_var_expr (ex2)"
| "free_var_expr (FunExp fname ty_list ex_ls)  = \<Union> (Set.image free_var_expr (set ex_ls))" 
| "free_var_expr (Old ex) = free_var_expr (ex)"
| "free_var_expr (Forall ty ex) = free_var_expr (ex)"
| "free_var_expr (Exists ty ex) = free_var_expr (ex)"
| "free_var_expr (ForallT ex) = free_var_expr (ex)"
| "free_var_expr (ExistsT ex) = free_var_expr (ex)"

fun free_var_exprlist :: "expr list \<Rightarrow> vname set"
where
  "free_var_exprlist cs = \<Union> (Set.image free_var_expr (set cs))"


fun free_var_cmd :: "cmd \<Rightarrow> vname set"
where
  "free_var_cmd (Assert ex) = free_var_expr ex"
| "free_var_cmd (Assume ex) = free_var_expr ex"
| "free_var_cmd (Assign vname expr) = {vname} \<union> free_var_expr expr"
| "free_var_cmd (Havoc vname) = {vname}"
| "free_var_cmd (ProcCall pname ex_ls vname_ls) = set vname_ls \<union> (\<Union> (Set.image free_var_expr (set ex_ls)))" (* is this correct?" *)

fun free_var_cmdlist :: "cmd list \<Rightarrow> vname set"
where
  "free_var_cmdlist cs = \<Union> (Set.image free_var_cmd (set cs))"

subsection \<open>Helper Lemmas for the final dead variables elimination lemma\<close>

lemma validConf:
  assumes proc_cor: "proc_is_correct A fun_decls constants global_vars axioms proc Semantics.proc_body_satisfies_spec" and
                    "proc_body proc = Some (locals, mbody)" and
                    "(((\<forall>t. closed t \<longrightarrow> (\<exists>v. type_of_val A (v :: 'a val) = t)) \<and> (\<forall>v. closed ((type_of_val A) v))))" and
                    "fun_interp_wf A fun_decls \<Gamma>" and
                    "list_all closed \<Omega> \<and> length \<Omega> = proc_ty_args proc" and        
                    "state_typ_wf A \<Omega> gs (constants @ global_vars)" and
                    "state_typ_wf A \<Omega> ls ((proc_args proc)@ (locals @ proc_rets proc))" and
                    "axioms_sat A (constants, []) \<Gamma> (global_to_nstate (state_restriction gs constants)) axioms" and            
                    "expr_all_sat A (constants@global_vars, (proc_args proc)@(locals@(proc_rets proc))) \<Gamma> \<Omega> \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> (proc_all_pres proc)" and 
                    "A, [], (constants@global_vars, (proc_args proc)@(locals@(proc_rets proc))), \<Gamma>, \<Omega>, mbody \<turnstile> (Inl (entry(mbody)), Normal \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr>) -n\<rightarrow>* (m',s')"

  shows             "valid_configuration A (constants@global_vars, (proc_args proc)@(locals@(proc_rets proc))) \<Gamma> \<Omega> (proc_checked_posts proc) m' s'"
  using assms
  unfolding proc_body_satisfies_spec_def
  by fastforce

lemma map_le_append_pre:
  assumes "map_of xs \<subseteq>\<^sub>m map_of xs'"
  shows "map_of (ys@xs) \<subseteq>\<^sub>m map_of (ys@xs')" 
  using assms
  by (metis Map.map_of_append append_assoc map_add_subsumed2 map_le_map_add)
  
lemma map_le_append_post:
  assumes "map_of xs \<subseteq>\<^sub>m map_of xs'" and 
          \<comment>\<open>This second assumption is necessary, because otherwise \<^term>\<open>map_of (xs@ys) y\<close> may lookup
             a value in \<^term>\<open>ys\<close>, while \<^term>\<open>map_of (xs'@ys) y\<close> looks up the value in \<^term>\<open>xs'\<close>\<close>
          "dom (map_of xs') \<inter> dom (map_of ys) = {}"
  shows "map_of (xs@ys) \<subseteq>\<^sub>m map_of (xs'@ys)"
  using assms
  by (metis Map.map_of_append map_add_comm map_add_le_mapI map_le_map_add map_le_trans)

lemma map_le_append_pre_post:
  assumes "map_of xs \<subseteq>\<^sub>m map_of xs'" and 
          \<comment>\<open>This second assumption is necessary, because otherwise \<^term>\<open>map_of (xs@ys) y\<close> may lookup
             a value in \<^term>\<open>ys\<close>, while \<^term>\<open>map_of (xs'@ys) y\<close> looks up the value in \<^term>\<open>xs'\<close>\<close>
          "dom (map_of xs') \<inter> dom (map_of ys) = {}"
  shows "map_of (ws@xs@ys) \<subseteq>\<^sub>m map_of (ws@xs'@ys)"
  using assms map_le_append_pre map_le_append_post
  by blast 

lemma lookup_var_decl_map_le:
  assumes "map_of vs \<subseteq>\<^sub>m map_of vs'"          
  shows "lookup_vdecls_ty vs \<subseteq>\<^sub>m lookup_vdecls_ty vs'"
  unfolding lookup_vdecls_ty_def map_le_def
proof 
  fix a
  assume "a \<in> dom (\<lambda>x. map_option fst (map_of vs x))"

  thus "map_option fst (map_of vs a) = map_option fst (map_of vs' a)"
    using assms
    by (metis (full_types) domIff map_le_def option.map_disc_iff)
qed

text \<open>The following lemma should be helpful to prove that variables reduce to the same values in 
      in the program with and without dead variables.\<close>
lemma lookup_var_map_le_local:
  assumes MapLeLocal: "(map_of (snd \<Lambda>) \<subseteq>\<^sub>m map_of (snd \<Lambda>') \<and> x \<notin> (dom (map_of (snd \<Lambda>')) - (dom (map_of (snd \<Lambda>))))) 
                       \<or> (map_of (snd \<Lambda>') \<subseteq>\<^sub>m map_of (snd \<Lambda>) \<and> x \<notin> (dom (map_of (snd \<Lambda>)) - (dom (map_of (snd \<Lambda>'))))) "
  shows "lookup_var \<Lambda> ns x = lookup_var \<Lambda>' ns x"
proof (cases "(map_of (snd \<Lambda>) \<subseteq>\<^sub>m map_of (snd \<Lambda>') \<and> x \<notin> (dom (map_of (snd \<Lambda>')) - (dom (map_of (snd \<Lambda>)))))")
  case True
  then show ?thesis
  proof (cases "map_of (snd \<Lambda>) x = None")
    case True
    hence "map_of (snd \<Lambda>') x = None"
      by (metis (mono_tags, lifting) DiffI assms domIff map_le_def)
    with True show ?thesis 
      unfolding lookup_var_def
      by simp
  next
    case False
    then show ?thesis
      using MapLeLocal
      unfolding lookup_var_def
      by (metis (mono_tags, lifting) True domIff map_le_def)
  qed
next
  case False
  then show ?thesis
  proof (cases "map_of (snd \<Lambda>') x = None")
    case True
    hence "map_of (snd \<Lambda>) x = None"
      using False assms by blast
    with True show ?thesis 
      unfolding lookup_var_def
      by simp
  next
    case False
    then show ?thesis 
      using MapLeLocal
      unfolding lookup_var_def
      by (metis (mono_tags, lifting) DiffI domIff map_le_def)
  qed
qed


lemma binder_map_le_local:
  assumes MapLeLocal: "map_of (snd \<Lambda>) \<subseteq>\<^sub>m map_of (snd \<Lambda>')" and
          "x \<notin> (dom (map_of (snd \<Lambda>')) - (dom (map_of (snd \<Lambda>))))"
        shows "binder_state ns i = binder_state ns i"
  by simp



lemma state_typ_wf_map_le:
  assumes StateTypWf: "state_typ_wf A \<Omega> ls (proc_args proc @ locals' @ proc_rets proc)" (is "state_typ_wf A \<Omega> ls ?V'") and
         MapLe: "map_of locals \<subseteq>\<^sub>m map_of locals'" and
         DomLocalInterRetsEmpty:   "dom (map_of locals') \<inter> dom (map_of (proc_rets proc)) = {}"
        shows "state_typ_wf A \<Omega> ls (proc_args proc @ locals @ proc_rets proc)" (is "state_typ_wf A \<Omega> ls ?V")
  unfolding state_typ_wf_def
proof (rule allI | rule impI)+
  fix v t
  assume LookupV: "lookup_vdecls_ty (proc_args proc @ locals @ proc_rets proc) v = Some t"

  from MapLe have "map_of ?V \<subseteq>\<^sub>m map_of ?V'"
    using map_le_append_pre_post[OF MapLe DomLocalInterRetsEmpty]
    by blast        

  with LookupV
  have "lookup_vdecls_ty (proc_args proc @ locals' @ proc_rets proc) v = Some t"
    using lookup_var_decl_map_le
    by (metis (full_types) domI map_le_def)

  thus "map_option (type_of_val A) (ls v) = Some (instantiate \<Omega> t)"
    using StateTypWf
    unfolding state_typ_wf_def
    by blast
qed




lemma expr_eval_different_locals_same_value:
  assumes  "fst \<Lambda> = fst \<Lambda>'" and
           "map_of (snd \<Lambda>') \<subseteq>\<^sub>m map_of (snd \<Lambda>)  \<or> map_of (snd \<Lambda>) \<subseteq>\<^sub>m map_of (snd \<Lambda>')" 
  shows    "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, s\<rangle> \<Down> v \<Longrightarrow> 
              free_var_expr e \<inter> ((dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))) \<union> (dom (map_of (snd \<Lambda>)) - dom (map_of (snd \<Lambda>')))) = {} 
              \<Longrightarrow> A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>e, s\<rangle> \<Down> v" and
           "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es, s\<rangle> [\<Down>] vs \<Longrightarrow>
              \<Union> {free_var_expr e' | e'. e' \<in> set es} \<inter> ((dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))) \<union> (dom (map_of (snd \<Lambda>)) - dom (map_of (snd \<Lambda>')))) = {} 
              \<Longrightarrow> A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>es, s\<rangle> [\<Down>] vs"
  using assms
proof (induction rule: red_expr_red_exprs.inducts)
  case (RedVar n_s x v \<Omega>)
  then show ?case
  proof (cases "map_of (snd \<Lambda>') \<subseteq>\<^sub>m map_of (snd \<Lambda>)")
    case True
    have "free_var_expr (Var x) \<inter> (dom (map_of (snd \<Lambda>)) - (dom (map_of (snd \<Lambda>')))) = {}"
      using RedVar.prems(1)
      by blast

    hence notin: "x \<notin> (dom (map_of (snd \<Lambda>)) - (dom (map_of (snd \<Lambda>'))))"
      using Int_Un_eq(2) RedVar.prems(1) by auto

    have "lookup_var \<Lambda>' n_s x = lookup_var \<Lambda> n_s x"
      apply (rule lookup_var_map_le_local)
      using True notin by auto

    then show ?thesis
      by (simp add: RedVar.IH red_expr_red_exprs.RedVar)
  next
    case False

    have "free_var_expr (Var x) \<inter> (dom (map_of (snd \<Lambda>')) - (dom (map_of (snd \<Lambda>)))) = {}"
      using RedVar.prems(1)
      by blast

    hence notin: "x \<notin> (dom (map_of (snd \<Lambda>')) - (dom (map_of (snd \<Lambda>))))"
      by simp

    have "lookup_var \<Lambda>' n_s x = lookup_var \<Lambda> n_s x"
      apply (rule lookup_var_map_le_local)
      using False notin assms(2) by blast

    then show ?thesis
      by (simp add: RedVar.IH red_expr_red_exprs.RedVar)
  qed
next
  case (RedBVar n_s i v \<Omega>)
  then show ?case
    by (simp add: red_expr_red_exprs.RedBVar)
next
  case (RedLit \<Omega> v n_s)
  then show ?case
    by (simp add: red_expr_red_exprs.RedLit)
next
  case (RedBinOp \<Omega> e1 n_s v1 e2 v2 bop v)


  have v1: "A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>e1,n_s\<rangle> \<Down> v1"
    by (metis (no_types, lifting) Diff_Compl Int_Diff Int_empty_right RedBinOp.IH(2) RedBinOp.prems(1) RedBinOp.prems(3) Un_Int_eq(3) assms(1) free_var_expr.simps(5))

  have v2: "A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>e2,n_s\<rangle> \<Down> v2"
    using RedBinOp.IH(4) RedBinOp.prems(1) RedBinOp.prems(3) assms(1) free_var_expr.simps(5) by blast
  show ?case
    using v1 v2
    using RedBinOp.hyps red_expr_red_exprs.RedBinOp by blast
next
  case (RedUnOp \<Omega> e n_s v uop v')
  then show ?case
    by (simp add: red_expr_red_exprs.RedUnOp)
next
  case (RedFunOp f f_interp \<Omega> args n_s v_args ty_args v)


  have "\<Union> {free_var_expr e' |e'. e' \<in> set args} \<inter> ((dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))) \<union> (dom (map_of (snd \<Lambda>)) - dom (map_of (snd \<Lambda>')))) = {}"
    using RedFunOp.prems(1) free_var_expr.simps(6)
    by blast

  hence "A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>args, n_s\<rangle> [\<Down>] v_args"
    by (simp add: RedFunOp.IH(3) RedFunOp.prems(3) assms(1))

  then show ?case
    using RedFunOp
    by (simp add: red_expr_red_exprs.RedFunOp)
next
(*case (RedCondExpTrue \<Omega> cond n_s thn v els)
  then show ?case sorry
next
  case (RedCondExpFalse \<Omega> cond n_s els v thn)
  then show ?case sorry
next *)
  case (RedOld \<Omega> e n_s v)
  then show ?case
    by (simp add: red_expr_red_exprs.RedOld)
next
  case (RedExpListNil \<Omega> n_s)
  then show ?case
    by (meson red_expr_red_exprs.RedExpListNil)
next
  case (RedExpListCons \<Omega> e n_s v es vs)

  have free_var_e: "free_var_expr e \<inter> ((dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))) \<union> (dom (map_of (snd \<Lambda>)) - dom (map_of (snd \<Lambda>')))) = {}"
    using RedExpListCons.prems(1) by auto

  then have expr: "A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>e,n_s\<rangle> \<Down> v"
    by (simp add: RedExpListCons.IH(2) RedExpListCons.prems(3) assms(1))

  have "\<Union> {free_var_expr e' |e'. e' \<in> set es} \<subseteq> \<Union> {free_var_expr e' |e'. e' \<in> set (e # es)}"
    by auto

  then have "\<Union> {free_var_expr e' |e'. e' \<in> set es} \<inter> ((dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))) \<union> (dom (map_of (snd \<Lambda>)) - dom (map_of (snd \<Lambda>')))) = {}"
    using RedExpListCons.prems(1) boolean_algebra_cancel.inf1 inf.absorb_iff1 inf_bot_right by blast

  then have expr: "A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>es,n_s\<rangle> [\<Down>] vs"
    by (simp add: RedExpListCons.IH(4) RedExpListCons.prems(3) assms(1))
  then show ?case
    using expr
    by (simp add: RedExpListCons.IH(2) RedExpListCons.prems(3) assms(1) free_var_e red_expr_red_exprs.RedExpListCons)
next
  case (RedForAllTrue \<Omega> ty e n_s)
  then show ?case
    by (simp add: red_expr_red_exprs.RedForAllTrue)
next
  case (RedForAllFalse v \<Omega> ty e n_s)
  then show ?case
    using free_var_expr.simps(8) red_expr_red_exprs.RedForAllFalse by blast
next
  case (RedExistsTrue v \<Omega> ty e n_s)
  then show ?case
    using free_var_expr.simps(9) red_expr_red_exprs.RedExistsTrue by blast
next
  case (RedExistsFalse \<Omega> ty e n_s)
  then show ?case
    by (simp add: red_expr_red_exprs.RedExistsFalse)
next
  case (RedForallT_True \<Omega> e n_s)
  then show ?case
    by (simp add: inf_set_def red_expr_red_exprs.RedForallT_True)
next
  case (RedForallT_False \<tau> \<Omega> e n_s)
  then show ?case
    by (simp add: red_expr_red_exprs.RedForallT_False)
next
  case (RedExistsT_True \<tau> \<Omega> e n_s)
  then show ?case
    by (simp add: red_expr_red_exprs.RedExistsT_True)
next
  case (RedExistsT_False \<Omega> e n_s)
  then show ?case
    by (simp add: red_expr_red_exprs.RedExistsT_False)
qed



lemma expr_sat_locals_same_value:
  assumes ExprSat: "fst \<Lambda> = fst \<Lambda>'" and
                   "(map_of (snd \<Lambda>) \<subseteq>\<^sub>m map_of (snd \<Lambda>') \<and> free_var_expr e \<inter> ((dom (map_of (snd \<Lambda>'))) - (dom (map_of (snd \<Lambda>)))) = {}) 
                    \<or> (map_of (snd \<Lambda>') \<subseteq>\<^sub>m map_of (snd \<Lambda>) \<and> free_var_expr e \<inter> ((dom (map_of (snd \<Lambda>))) - (dom (map_of (snd \<Lambda>')))) = {})" 
                   "expr_sat A \<Lambda> \<Gamma> \<Omega> s e"
                 shows "expr_sat A \<Lambda>' \<Gamma> \<Omega> s e"
  unfolding expr_sat_def
  apply (rule expr_eval_different_locals_same_value[where ?\<Lambda> = "\<Lambda>"])
     apply (simp add: ExprSat)
  using assms(2) apply auto[1]
  using assms(3) expr_sat_def apply blast
  by (metis Diff_eq_empty_iff Int_Un_distrib Int_empty_right Un_empty_right assms(2) map_le_implies_dom_le)
  








lemma expr_sat_dead_variables:
  assumes ExprSat: "expr_sat A (constants @ global_vars, proc_args proc @ locals @ proc_rets proc) \<Gamma> \<Omega> 
                   ns expr" and
          NoDeadVariables: "(map_of (proc_args proc @ locals @ proc_rets proc) \<subseteq>\<^sub>m map_of (proc_args proc @ locals' @ proc_rets proc) \<and> free_var_expr expr \<inter> (dom (map_of (proc_args proc @ locals' @ proc_rets proc))) - (dom (map_of (proc_args proc @ locals @ proc_rets proc))) = {}) 
                           \<or> (map_of (proc_args proc @ locals' @ proc_rets proc) \<subseteq>\<^sub>m map_of (proc_args proc @ locals @ proc_rets proc) \<and> free_var_expr expr \<inter> (dom (map_of (proc_args proc @ locals @ proc_rets proc))) - (dom (map_of (proc_args proc @ locals' @ proc_rets proc))) = {})"

shows "expr_sat A (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega> ns expr"
  apply (rule expr_sat_locals_same_value[where ?\<Lambda> = "(constants @ global_vars, proc_args proc @ locals @ proc_rets proc)"])
    apply simp
  using NoDeadVariables
   apply simp
  using ExprSat by auto




  


lemma expr_list_sat_dead_variables:
  assumes ExprSat: "expr_all_sat A (constants @ global_vars, proc_args proc @ locals @ proc_rets proc) \<Gamma> \<Omega> ns expr_list" and
          MapLocal: "(map_of locals \<subseteq>\<^sub>m map_of locals' \<and> dom (map_of locals') \<inter> dom (map_of (proc_rets proc)) = {} \<and> free_var_exprlist expr_list \<inter> (dom (map_of (locals'))) - (dom (map_of (locals))) = {}) 
                     \<or> (map_of locals' \<subseteq>\<^sub>m map_of locals \<and> dom (map_of locals) \<inter> dom (map_of (proc_rets proc)) = {} \<and> free_var_exprlist expr_list \<inter> (dom (map_of (locals))) - (dom (map_of (locals'))) = {})"

shows "expr_all_sat A (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega> ns expr_list"
  unfolding expr_all_sat_def list_all_def Ball_def
proof (rule allI | rule impI)+
  fix x
  assume "x \<in> set (expr_list)"
  show "expr_sat A (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega>
          ns x"
  proof (cases "map_of locals \<subseteq>\<^sub>m map_of locals'")
    case True
    have "dom (map_of locals') \<inter> dom (map_of (proc_rets proc)) = {}"
      by (metis MapLocal True map_le_antisym)

    have freeVarList: "free_var_exprlist expr_list \<inter> (dom (map_of (locals'))) - (dom (map_of (locals))) = {}"
      by (metis MapLocal True map_le_antisym)

    hence "free_var_exprlist expr_list \<inter> (dom (map_of (proc_args proc @ locals' @ proc_rets proc))) - (dom (map_of (proc_args proc @ locals @ proc_rets proc))) = {}"
      by auto

    hence freeVar: "free_var_expr x \<inter> (dom (map_of (proc_args proc @ locals' @ proc_rets proc))) - (dom (map_of (proc_args proc @ locals @ proc_rets proc))) = {}"
      using \<open>x \<in> set expr_list\<close> free_var_exprlist.simps
      by (simp add: Int_Diff Sup_inf_eq_bot_iff) 


    have exprSat: "expr_sat A (constants @ global_vars, proc_args proc @ locals @ proc_rets proc) \<Gamma> \<Omega> ns x"
      using ExprSat
      unfolding expr_all_sat_def list_all_def Ball_def
      by (simp add: \<open>x \<in> set expr_list\<close>)

    have MapLe: "map_of (proc_args proc @ locals @ proc_rets proc) \<subseteq>\<^sub>m map_of (proc_args proc @ locals' @ proc_rets proc)"
      by (metis MapLocal True map_le_antisym map_le_append_pre_post)
    
    
    show ?thesis
      apply (rule expr_sat_dead_variables)
       apply (rule exprSat)
      using MapLe freeVar by blast
  next
    case False

    have exprSat: "expr_sat A (constants @ global_vars, proc_args proc @ locals @ proc_rets proc) \<Gamma> \<Omega> ns x"
       using ExprSat
       unfolding expr_all_sat_def list_all_def Ball_def
       by (simp add: \<open>x \<in> set expr_list\<close>)
    have map_of: "map_of (proc_args proc @ locals' @ proc_rets proc) \<subseteq>\<^sub>m map_of (proc_args proc @ locals @ proc_rets proc)"
      using False MapLocal map_le_append_pre_post by blast

    have domain: "dom (map_of locals) \<inter> dom (map_of (proc_rets proc)) = {}"
      using False MapLocal by auto

    have freeVarList: "free_var_exprlist expr_list \<inter> (dom (map_of (locals))) - (dom (map_of (locals'))) = {}"
      by (metis MapLocal False)

    hence "free_var_exprlist expr_list \<inter> (dom (map_of (proc_args proc @ locals @ proc_rets proc))) - (dom (map_of (proc_args proc @ locals' @ proc_rets proc))) = {}"
      by auto

    hence freeVar: "free_var_expr x \<inter> (dom (map_of (proc_args proc @ locals @ proc_rets proc))) - (dom (map_of (proc_args proc @ locals' @ proc_rets proc))) = {}"
      using \<open>x \<in> set expr_list\<close> free_var_exprlist.simps
      by (simp add: Int_Diff Union_disjoint)


    show ?thesis 
      apply (rule expr_sat_dead_variables[where ?locals = "locals"])
       apply (rule exprSat)
      using map_of freeVar by blast
  qed
qed

lemma dom_diff_empty: 
  assumes "A \<subseteq> B"
  shows "A - B = {}"
  by (simp add: assms)



lemma red_cfg_dead_variables_cmd:
  assumes "A,[],\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>c,s\<rangle> \<rightarrow> s'" and
          "fst \<Lambda> = fst \<Lambda>'" and
          MapLocal: "(map_of (snd \<Lambda>) \<subseteq>\<^sub>m map_of (snd \<Lambda>'))" and
          "free_var_cmd c \<inter> ((dom (map_of (snd \<Lambda>'))) - (dom (map_of (snd \<Lambda>)))) = {}" and
          WhereClausesFreeVars: "\<And>x d cond. lookup_var_decl \<Lambda>' x = Some d \<Longrightarrow> snd d = Some cond \<Longrightarrow> free_var_expr cond \<inter> ((dom (map_of (snd \<Lambda>'))) - (dom (map_of (snd \<Lambda>)))) = {} "
        shows "A,[],\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c,s\<rangle> \<rightarrow> s'"
  using assms
proof (induction rule: red_cmd.inducts)
  case (RedAssertOk e n_s)
  have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e,n_s\<rangle> \<Down> BoolV True"
    apply (rule expr_eval_different_locals_same_value[where ?\<Lambda>=\<Lambda>'])
    apply (simp add: assms(2))
    apply (simp add: RedAssertOk.prems(2))
    apply (simp add: RedAssertOk.hyps)
    by (metis Diff_mono RedAssertOk.prems(2) RedAssertOk.prems(3) Un_absorb1 free_var_cmd.simps(1) map_le_implies_dom_le)
  then show ?case
    by (meson red_cmd.RedAssertOk)
next
  case (RedAssertFail e n_s)
  have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e,n_s\<rangle> \<Down> BoolV False"
    apply (rule expr_eval_different_locals_same_value[where ?\<Lambda>=\<Lambda>'])
    apply (simp add: assms(2))
    apply (simp add: RedAssertFail.prems(2))
    apply (simp add: RedAssertFail.hyps)
    by (metis Diff_mono RedAssertFail.prems(2) RedAssertFail.prems(3) Un_absorb1 free_var_cmd.simps(1) map_le_implies_dom_le)
  then show ?case
    by (meson red_cmd.RedAssertFail)
next
  case (RedAssumeOk e n_s)
  have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e,n_s\<rangle> \<Down> BoolV True"
    apply (rule expr_eval_different_locals_same_value[where ?\<Lambda>=\<Lambda>'])
    apply (simp add: assms(2))
    apply (simp add: RedAssumeOk.prems(2))
    apply (simp add: RedAssumeOk.hyps)
    by (metis Diff_eq_empty_iff RedAssumeOk.prems(2) RedAssumeOk.prems(3) boolean_algebra.disj_zero_right free_var_cmd.simps(2) map_le_implies_dom_le sup_commute)
  then show ?case
    by (meson red_cmd.RedAssumeOk)
next
  case (RedAssumeMagic e n_s)
  have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e,n_s\<rangle> \<Down> BoolV False"
    apply (rule expr_eval_different_locals_same_value[where ?\<Lambda>=\<Lambda>'])
    apply (simp add: assms(2))
    apply (simp add: RedAssumeMagic.prems(2))
    apply (simp add: RedAssumeMagic.hyps)
    by (metis Diff_eq_empty_iff RedAssumeMagic.prems(2) RedAssumeMagic.prems(3) boolean_algebra.disj_zero_right free_var_cmd.simps(2) map_le_implies_dom_le sup_commute)
  then show ?case
    by (meson red_cmd.RedAssumeMagic)
next
  case (RedAssign x ty v e n_s)
  hence "x \<notin> (dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>)))"
    by simp

  hence "lookup_var_ty \<Lambda> x  = lookup_var_ty \<Lambda>' x"
    unfolding lookup_var_ty_def lookup_var_decl_def
    using assms
    by (metis (no_types, lifting) DiffI domIff map_le_def)

    
  then have lookupEq: "lookup_var_ty \<Lambda> x = Some ty"
    by (simp add: RedAssign.hyps(1))

  have otherDirEmpty: "(dom (map_of (snd \<Lambda>)) - dom (map_of (snd \<Lambda>'))) = {}"
    apply (rule dom_diff_empty)
    using assms
    by (simp add: map_le_implies_dom_le)

  have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v"
    apply (rule expr_eval_different_locals_same_value[where ?\<Lambda>=\<Lambda>'])
    apply (simp add: assms(2))
    apply (simp add: RedAssign.prems(2))
    apply (simp add: RedAssign.hyps)
    using RedAssign(6) MapLocal
    unfolding free_var_cmd.simps
    by (metis Int_Un_eq(2) Int_commute otherDirEmpty disjoint_insert(2) insert_is_Un)


  then have step: "A,[],\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assign x e,Normal n_s\<rangle> \<rightarrow> Normal (update_var \<Lambda> n_s x v)"
    using lookupEq RedAssign.hyps(2) RedAssign
    by (meson red_cmd.RedAssign)

  have "(update_var \<Lambda> n_s x v) = (update_var \<Lambda>' n_s x v)"
    unfolding update_var_def
    using assms RedAssign.prems(3) free_var_cmd.simps(3)
    by (metis (no_types, lifting) Diff_iff \<open>x \<notin> dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))\<close> domIff map_le_def)
  then show ?case
    using step by auto
next
  case (RedHavocNormal x ty w v n_s)

  hence "x \<notin> (dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>)))"
    by simp

  hence lookupVarEq: "lookup_var_decl \<Lambda> x = lookup_var_decl \<Lambda>' x"
    unfolding lookup_var_ty_def lookup_var_decl_def
    using assms
    by (metis (no_types, lifting) Diff_iff domIff map_le_def)

  have otherDirEmpty: "(dom (map_of (snd \<Lambda>)) - dom (map_of (snd \<Lambda>'))) = {}"
    apply (rule dom_diff_empty)
    using assms
    by (simp add: map_le_implies_dom_le)

  have updVarEq:"(update_var \<Lambda> n_s x v) = (update_var \<Lambda>' n_s x v)"
    unfolding update_var_def
    using assms RedHavocNormal.prems(3) free_var_cmd.simps(3)
    by (metis (no_types, lifting) Diff_iff \<open>x \<notin> dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))\<close> domIff map_le_def)

  have step: "\<And>cond. w = Some cond \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cond, (update_var \<Lambda> n_s x v)\<rangle> \<Down> BoolV True"
  proof -
    fix cond
    assume "w = Some cond"
    hence "free_var_expr cond \<inter> (dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))) = {}"
      using RedHavocNormal.hyps(1) WhereClausesFreeVars by auto
    show "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cond, (update_var \<Lambda> n_s x v)\<rangle> \<Down> BoolV True"
      apply (rule expr_eval_different_locals_same_value[where ?\<Lambda>=\<Lambda>'])
      apply (simp add: assms(2))
      apply (simp add: RedHavocNormal.prems(2))
      using RedHavocNormal.hyps(3)[OF \<open>w = Some cond\<close>]
      apply (simp add: updVarEq)
      by (simp add: \<open>free_var_expr cond \<inter> (dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))) = {}\<close> otherDirEmpty)
  qed


  then show ?case
    using updVarEq RedHavocNormal
    by (metis local.step lookupVarEq red_cmd.RedHavocNormal)
next
  case (RedHavocMagic x ty cond v n_s)
  hence "x \<notin> (dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>)))"
    by simp
  have lokupVarDecl: "lookup_var_decl \<Lambda> x = Some (ty,Some(cond))"
    unfolding lookup_var_ty_def lookup_var_decl_def
    using assms
    by (metis (no_types, lifting) Int_Diff Int_insert_left_if1 RedHavocMagic.hyps(1) RedHavocMagic.prems(3) domIff free_var_cmd.simps(4) insert_Diff_if insert_not_empty lookup_var_decl_def map_le_def)

  have updateEqual: "(update_var \<Lambda> n_s x v) = (update_var \<Lambda>' n_s x v)"
    unfolding update_var_def
    using assms RedHavocMagic.prems(3) free_var_cmd.simps(3)
    by (metis (no_types, lifting) Diff_iff \<open>x \<notin> dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))\<close> domIff map_le_def)

  have otherDirEmpty: "(dom (map_of (snd \<Lambda>)) - dom (map_of (snd \<Lambda>'))) = {}"
    apply (rule dom_diff_empty)
    using assms
    by (simp add: map_le_implies_dom_le)
  
  have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cond, (update_var \<Lambda> n_s x v)\<rangle> \<Down> BoolV False"
    apply (rule expr_eval_different_locals_same_value[where ?\<Lambda>=\<Lambda>'])
    apply (simp add: assms(2))
    apply (simp add: RedHavocMagic.prems(2))
    using updateEqual RedHavocMagic.hyps(3) apply simp
    using assms RedHavocMagic otherDirEmpty
    by (metis Int_Un_eq(2) snd_eqD)

    
  then show ?case 
    using RedHavocMagic.hyps(2) red_cmd.RedHavocMagic lokupVarDecl by blast
next
  case (RedProcCallOkAndMagic m msig args n_s v_args pre_ls new_ls ty_modifs vs_modifs vs_ret post_ls post_gs post_state post_success post_fail n_s' rets)
  then show ?case 
    by simp
next
  case (RedProcCallFail m msig args n_s v_args pre_ls new_ls rets)
  then show ?case 
    by simp
next
  case (RedPropagateMagic s)
  then show ?case
    by (simp add: red_cmd.RedPropagateMagic)
next
  case (RedPropagateFailure s)
  then show ?case
    by (simp add: red_cmd.RedPropagateFailure)
qed
  

lemma red_cfg_dead_variables_cmdlist:
assumes oneStep: "A,[],\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>cs,s\<rangle> [\<rightarrow>] s'" and
        "fst \<Lambda> = fst \<Lambda>'" and
        MapLocal: "(map_of (snd \<Lambda>) \<subseteq>\<^sub>m map_of (snd \<Lambda>'))" and 
        freeVarCmdList: "free_var_cmdlist cs \<inter> ((dom (map_of (snd \<Lambda>'))) - (dom (map_of (snd \<Lambda>)))) = {}" and 
        WhereClausesFreeVars: "\<And>x d cond. lookup_var_decl \<Lambda>' x = Some d \<Longrightarrow> snd d = Some cond \<Longrightarrow> free_var_expr cond \<inter> ((dom (map_of (snd \<Lambda>'))) - (dom (map_of (snd \<Lambda>)))) = {} "
      shows "A,[],\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,s\<rangle> [\<rightarrow>] s'"
  using oneStep freeVarCmdList
proof (induction rule: red_cmd_list.inducts)
  case (RedCmdListNil s)
  then show ?case
    by (meson red_cmd_list.RedCmdListNil)
next
  case (RedCmdListCons c s s'' cs' s')
  have freeVarSingleCmd: "free_var_cmd c \<inter> (dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))) = {}"
    using RedCmdListCons(4)
    unfolding free_var_cmdlist.simps
    by auto

  have oneStep: "A,[],\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c,s\<rangle> \<rightarrow> s''"
    apply (rule red_cfg_dead_variables_cmd[OF RedCmdListCons(1) assms(2) MapLocal freeVarSingleCmd])
    using WhereClausesFreeVars
    by simp

  have "free_var_cmdlist cs' \<inter> (dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))) = {}"
    using RedCmdListCons(4)
    unfolding free_var_cmdlist.simps
    by auto

  hence "A,[],\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs',s''\<rangle> [\<rightarrow>] s'"
    using RedCmdListCons.IH 
    sorry (*Why doesn't this hold trivially? Shouldn't it directly follow from the implication?*)

  
    
  then show ?case
    using oneStep red_cmd_list.RedCmdListCons by blast
qed

lemma red_cfg_dead_variables_cmdlist_onestep:
  assumes oneStep: "A,[],\<Lambda>',\<Gamma>,\<Omega>,body \<turnstile>(Inl m, Normal ns) -n\<rightarrow> (m', s')" and
          fstEq: "fst \<Lambda> = fst \<Lambda>'" and
          MapLocal: "(map_of (snd \<Lambda>) \<subseteq>\<^sub>m map_of (snd \<Lambda>'))" and
          NoDeadVariables: "free_var_cmdlist (node_to_block body ! m) \<inter> ((dom (map_of (snd \<Lambda>'))) - (dom (map_of (snd \<Lambda>)))) = {}" and
          WhereClausesFreeVars: "\<And>x d cond. lookup_var_decl \<Lambda>' x = Some d \<Longrightarrow> snd d = Some cond \<Longrightarrow> free_var_expr cond \<inter> ((dom (map_of (snd \<Lambda>'))) - (dom (map_of (snd \<Lambda>)))) = {} "
        shows   "A,[],\<Lambda>,\<Gamma>,\<Omega>,body \<turnstile>(Inl m, Normal ns) -n\<rightarrow> (m', s')"
  using assms
proof cases
  case (RedNormalSucc cs ns' n')
  have "A,[],\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns\<rangle> [\<rightarrow>] Normal ns'"
    apply (rule red_cfg_dead_variables_cmdlist[OF RedNormalSucc(4) fstEq MapLocal _ WhereClausesFreeVars])
    using NoDeadVariables local.RedNormalSucc(3) by auto

  then show ?thesis
    using local.RedNormalSucc(1) local.RedNormalSucc(2) local.RedNormalSucc(3) local.RedNormalSucc(5) red_cfg.RedNormalSucc by blast
next
  case (RedNormalReturn cs ns')
  have "A,[],\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns\<rangle> [\<rightarrow>] Normal ns'"
    apply (rule red_cfg_dead_variables_cmdlist[OF RedNormalReturn(4) fstEq MapLocal _ WhereClausesFreeVars])
    using NoDeadVariables local.RedNormalReturn(3) by auto

  then show ?thesis
    using local.RedNormalReturn(1) local.RedNormalReturn(2) local.RedNormalReturn(3) local.RedNormalReturn(5) red_cfg.RedNormalReturn by blast
next
  case (RedFailure cs)
  have "A,[],\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns\<rangle> [\<rightarrow>] Failure"
    apply (rule red_cfg_dead_variables_cmdlist[OF RedFailure(4) fstEq MapLocal _ WhereClausesFreeVars])
    using NoDeadVariables local.RedFailure(3) by auto
  then show ?thesis
    using local.RedFailure(1) local.RedFailure(2) local.RedFailure(3) red_cfg.RedFailure by blast
next
  case (RedMagic cs)
  have "A,[],\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns\<rangle> [\<rightarrow>] Magic"
    apply (rule red_cfg_dead_variables_cmdlist[OF RedMagic(4) fstEq MapLocal _ WhereClausesFreeVars])
    using NoDeadVariables local.RedMagic(3) by auto
  then show ?thesis
    using local.RedMagic(1) local.RedMagic(2) local.RedMagic(3) red_cfg.RedMagic by blast
qed


lemma list_member_proof: 
  assumes "ls ! i = ele" and
          "i < length ls"
  shows "List.member (ls) ele "
  using assms
proof -
  have "ele \<in> set ls"
    using assms(2) assms(1) nth_mem by blast
  then show "List.member ls ele"
    by (simp add: in_set_member)
qed

lemma red_cfg_multi_dead_variables:
  assumes RedCfg: "A,[],(constants @ global_vars, proc_args proc @ locals' @ proc_rets proc),\<Gamma>,\<Omega>,body \<turnstile>(Inl m, Normal ns) -n\<rightarrow>* (m', s')" and
          MapLocal: "map_of locals \<subseteq>\<^sub>m map_of locals'" and
          DomLocalInterRetsEmpty:   "dom (map_of locals') \<inter> dom (map_of (proc_rets proc)) = {}" and
          NoDeadVariables: "\<forall>b\<in>set(node_to_block body). free_var_cmdlist b \<inter> (dom (map_of locals') - (dom (map_of locals))) = {}" and
          WhereClausesFreeVars: "\<And>x d cond. lookup_var_decl (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) x = Some d \<Longrightarrow> snd d = Some cond \<Longrightarrow> free_var_expr cond \<inter> ((dom (map_of (snd (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc)))) - (dom (map_of (snd (constants @ global_vars, proc_args proc @ locals @ proc_rets proc))))) = {} "
        shows   "A,[],(constants @ global_vars, proc_args proc @ locals @ proc_rets proc),\<Gamma>,\<Omega>,body \<turnstile>(Inl m, Normal ns) -n\<rightarrow>* (m', s')"
  using RedCfg 
proof (induction rule: converse_rtranclp_induct2)
  case refl
  then show ?case 
    by simp
next
  case (step a b c d)
  have restSteps: "A,[],(constants @ global_vars, proc_args proc @ locals @ proc_rets proc),\<Gamma>,\<Omega>,body \<turnstile>(c, d) -n\<rightarrow>* (m', s')"
    using step.IH  by simp
  from step show ?case
  proof cases
    case (RedNormalSucc n cs ns ns' n')
    have oneStepLocals':"A,[],(constants @ global_vars, proc_args proc @ locals' @ proc_rets proc),\<Gamma>,\<Omega>,body \<turnstile> (Inl n, Normal ns) -n\<rightarrow> (c, d)"
      using local.RedNormalSucc(1) local.RedNormalSucc(2) step.hyps(1) by auto

    have nInBody: "cs \<in> set(node_to_block body)" (* This doesn't work because I dont know if n < length (node_to_block body) *)
      using RedNormalSucc(5)
      sorry


    have "A,[],(constants @ global_vars, proc_args proc @ locals @ proc_rets proc),\<Gamma>,\<Omega>,body \<turnstile> (Inl n, Normal ns) -n\<rightarrow> (c, d)"
      apply (rule red_cfg_dead_variables_cmdlist_onestep[OF oneStepLocals'])
      apply (simp)
      using MapLocal map_le_append_pre_post DomLocalInterRetsEmpty apply auto[1]
      using NoDeadVariables local.RedNormalSucc(5) nInBody apply auto[1]
      using WhereClausesFreeVars by simp

    then show ?thesis 
      by (simp add: converse_rtranclp_into_rtranclp local.RedNormalSucc(1) local.RedNormalSucc(2) restSteps)
  next
    case (RedNormalReturn n cs ns ns')
    have oneStepLocals':"A,[],(constants @ global_vars, proc_args proc @ locals' @ proc_rets proc),\<Gamma>,\<Omega>,body \<turnstile> (Inl n, Normal ns) -n\<rightarrow> (c, d)"
      using local.RedNormalReturn(1) local.RedNormalReturn(2) step.hyps(1) by auto

    have nInBody: "cs \<in> set(node_to_block body)"
      using RedNormalReturn(5)
      sorry


    have "A,[],(constants @ global_vars, proc_args proc @ locals @ proc_rets proc),\<Gamma>,\<Omega>,body \<turnstile> (Inl n, Normal ns) -n\<rightarrow> (c, d)"
      apply (rule red_cfg_dead_variables_cmdlist_onestep[OF oneStepLocals'])
      apply (simp)
      using MapLocal map_le_append_pre_post DomLocalInterRetsEmpty apply auto[1]
      using NoDeadVariables local.RedNormalReturn(5) nInBody apply auto[1]
      using WhereClausesFreeVars by simp

    then show ?thesis 
      by (simp add: converse_rtranclp_into_rtranclp local.RedNormalReturn(1) local.RedNormalReturn(2) restSteps)
  next
    case (RedFailure n cs ns)
    have oneStepLocals':"A,[],(constants @ global_vars, proc_args proc @ locals' @ proc_rets proc),\<Gamma>,\<Omega>,body \<turnstile> (Inl n, Normal ns) -n\<rightarrow> (c, d)"
      using local.RedFailure(1) local.RedFailure(2) step.hyps(1) by auto

    have nInBody: "cs \<in> set(node_to_block body)"
      using RedFailure(5)
      sorry


    have "A,[],(constants @ global_vars, proc_args proc @ locals @ proc_rets proc),\<Gamma>,\<Omega>,body \<turnstile> (Inl n, Normal ns) -n\<rightarrow> (c, d)"
      apply (rule red_cfg_dead_variables_cmdlist_onestep[OF oneStepLocals'])
      apply (simp)
      using MapLocal map_le_append_pre_post DomLocalInterRetsEmpty apply auto[1]
      using NoDeadVariables local.RedFailure(5) nInBody apply auto[1]
      using WhereClausesFreeVars by simp

    then show ?thesis 
      by (simp add: converse_rtranclp_into_rtranclp local.RedFailure(1) local.RedFailure(2) restSteps)
  next
    case (RedMagic n cs ns)
    have oneStepLocals':"A,[],(constants @ global_vars, proc_args proc @ locals' @ proc_rets proc),\<Gamma>,\<Omega>,body \<turnstile> (Inl n, Normal ns) -n\<rightarrow> (c, d)"
      using local.RedMagic(1) local.RedMagic(2) step.hyps(1) by auto

    have nInBody: "cs \<in> set(node_to_block body)"
      using RedMagic(5)
      sorry


    have "A,[],(constants @ global_vars, proc_args proc @ locals @ proc_rets proc),\<Gamma>,\<Omega>,body \<turnstile> (Inl n, Normal ns) -n\<rightarrow> (c, d)"
      apply (rule red_cfg_dead_variables_cmdlist_onestep[OF oneStepLocals'])
      apply (simp)
      using MapLocal map_le_append_pre_post DomLocalInterRetsEmpty apply auto[1]
      using NoDeadVariables local.RedMagic(5) nInBody apply auto[1]
      using WhereClausesFreeVars by simp

    then show ?thesis 
      by (simp add: converse_rtranclp_into_rtranclp local.RedMagic(1) local.RedMagic(2) restSteps)
  qed
qed


subsection \<open>Dead variables elimination lemma\<close>

lemma elimination:
  assumes proc_cor: "proc_is_correct A fun_decls constants global_vars axioms proc Semantics.proc_body_satisfies_spec" and
          Body1: "proc_body proc = Some (locals, body)" and
          Body2: "proc' = proc \<lparr>proc_body := Some (locals', body)\<rparr>" and
          LocalVariables: "map_of locals \<subseteq>\<^sub>m map_of locals'" and 
          FreeVarPres: "free_var_exprlist (proc_all_pres proc) \<inter> dom (map_of locals') - dom (map_of locals) = {}" and
          FreeVarPosts: "free_var_exprlist (proc_checked_posts proc) \<inter> dom (map_of locals') - dom (map_of locals) = {}" and
          DeadVariables: "\<forall>b\<in>set(node_to_block body). free_var_cmdlist b \<inter> (dom (map_of locals') - (dom (map_of locals))) = {}" and
                 \<comment>\<open>The following assumption is needed to lift \<^term>\<open>map_of locals \<subseteq>\<^sub>m map_of locals'\<close>
                    to the concatenation of all variables in the local state (arguments, locals, return variables)\<close>
          DomLocalInterRetsEmpty: "dom (map_of locals') \<inter> dom (map_of (proc_rets proc)) = {}" and
          WhereClausesFreeVars: "\<And>x d cond. lookup_var_decl (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) x = Some d \<Longrightarrow> snd d = Some cond \<Longrightarrow> free_var_expr cond \<inter> ((dom (map_of (snd (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc)))) - (dom (map_of (snd (constants @ global_vars, proc_args proc @ locals @ proc_rets proc))))) = {} "
        shows "proc_is_correct A fun_decls constants global_vars axioms proc' Semantics.proc_body_satisfies_spec"
proof (simp add: Body2 del: proc_checked_posts.simps, (rule impI | rule allI)+)
  fix \<Gamma> \<Omega> gs ls
  assume  Atyp: "(\<forall>t. closed t \<longrightarrow> (\<exists>v. type_of_val A v = t)) \<and> (\<forall>v. closed (type_of_val A v))" and
          FunWf:"fun_interp_wf A fun_decls \<Gamma>" and
          ARenv: "list_all closed \<Omega> \<and> length \<Omega> = proc_ty_args proc" and
          WfGlobal: "state_typ_wf A \<Omega> gs (constants @ global_vars)" and
          WfLocal: "state_typ_wf A \<Omega> ls (proc_args proc @ locals' @ proc_rets proc)" and 
          AxSat: "axioms_sat A (constants, []) \<Gamma>
                      \<lparr>old_global_state = Map.empty, global_state = state_restriction gs constants, local_state = Map.empty,
                      binder_state = Map.empty\<rparr> axioms"
  show  "proc_body_satisfies_spec A [] (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega>
        (map fst (proc_pres proc)) (proc_checked_posts (proc\<lparr>proc_body := Some (locals', body)\<rparr>)) body
        \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr>"
    unfolding proc_body_satisfies_spec_def
  proof ((rule impI | rule allI)+)
    fix m' s'
    assume ExprAllSat: "expr_all_sat A (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega>
        \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> (map fst (proc_pres proc))" and
           GoesTo: "A,[],(constants @ global_vars, proc_args proc @ locals' @ proc_rets proc),\<Gamma>,\<Omega>,body \<turnstile>(Inl (entry body),
                                Normal \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr>) -n\<rightarrow>* (m', s')"
    show "valid_configuration A (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega>
        (proc_checked_posts (proc\<lparr>proc_body := Some (locals', body)\<rparr>)) m' s'"
      unfolding valid_configuration_def
    proof -

      have valid_proc: "valid_configuration A (constants @ global_vars, proc_args proc @ locals @ proc_rets proc) \<Gamma> \<Omega> ((proc_checked_posts proc)) m' s'"
      proof (rule validConf [OF proc_cor Body1 Atyp FunWf ARenv WfGlobal])
        show "state_typ_wf A \<Omega> ls (proc_args proc @ locals @ proc_rets proc)"
          using state_typ_wf_map_le[OF WfLocal LocalVariables] DomLocalInterRetsEmpty
          by blast
      next
        show "axioms_sat A (constants, []) \<Gamma> (global_to_nstate (state_restriction gs constants)) axioms"
          using AxSat
          by simp
      next
        show "expr_all_sat A (constants @ global_vars, proc_args proc @ locals @ proc_rets proc) \<Gamma> \<Omega>
             \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> (proc_all_pres proc)"
        proof -
          have "expr_all_sat A (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega>
               \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> (proc_all_pres proc)"
            using ExprAllSat
            by simp

          thus "expr_all_sat A (constants @ global_vars, proc_args proc @ locals @ proc_rets proc) \<Gamma> \<Omega>
             \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> (proc_all_pres proc)"
            apply (rule expr_list_sat_dead_variables)
            using LocalVariables FreeVarPres DomLocalInterRetsEmpty by blast
        qed

      next
        show "A,[],(constants @ global_vars, proc_args proc @ locals @ proc_rets proc),\<Gamma>,\<Omega>,body \<turnstile>(Inl (entry body), Normal
              \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr>) -n\<rightarrow>* (m', s')"
          by (rule red_cfg_multi_dead_variables[OF GoesTo LocalVariables DomLocalInterRetsEmpty DeadVariables WhereClausesFreeVars])
      qed
       
       
      hence notFailure: "s' \<noteq> Failure"
        using valid_configuration_def by blast

      have FinalConfig: "(is_final_config (m', s') \<longrightarrow> (\<forall>ns'. s' = Normal ns' \<longrightarrow> 
                        expr_all_sat A (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega> ns' (proc_checked_posts (proc\<lparr>proc_body := Some (locals', body)\<rparr>))))" 
            (is "?isFinal \<longrightarrow> (\<forall>ns'. ?isNormal ns' \<longrightarrow> ?Goal ns')")
      proof ((rule impI | rule allI)+)
        fix ns'
        assume "?isFinal" and "?isNormal ns'" 
        show "?Goal ns'"
        proof -
          
          have EqPosts: "(proc_checked_posts proc) = (proc_checked_posts (proc\<lparr>proc_body := Some (locals', body)\<rparr>))"
            sorry

          have "expr_all_sat A (constants @ global_vars, proc_args proc @ locals @ proc_rets proc) \<Gamma> \<Omega> ns' (proc_checked_posts proc)"
            using valid_proc 
            unfolding valid_configuration_def
            using \<open>is_final_config (m', s')\<close> \<open>s' = Normal ns'\<close> by blast


          hence "expr_all_sat A (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega> ns' (proc_checked_posts proc)"
            apply (rule expr_list_sat_dead_variables)
            using LocalVariables FreeVarPosts DomLocalInterRetsEmpty by blast

            

          thus "expr_all_sat A (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega> ns' (proc_checked_posts (proc\<lparr>proc_body := Some (locals', body)\<rparr>))"
            using EqPosts
            by argo
        qed
      qed
      thus "s' \<noteq> Failure \<and> (is_final_config (m', s') \<longrightarrow> (\<forall>ns'. s' = Normal ns' \<longrightarrow>
            expr_all_sat A (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega> ns' (proc_checked_posts (proc\<lparr>proc_body := Some (locals', body)\<rparr>))))"
        using notFailure by blast
    qed
  qed
qed


end