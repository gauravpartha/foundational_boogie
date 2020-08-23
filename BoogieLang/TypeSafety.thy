theory TypeSafety
imports Semantics Typing Util
begin

fun expr_is_defined :: "'a nstate \<Rightarrow> expr \<Rightarrow> bool"
  where
     "expr_is_defined ns (Var i) = (ns(i) \<noteq> None)"
   | "expr_is_defined ns (Lit l) = True"
   | "expr_is_defined ns (UnOp uop e) = expr_is_defined ns e"
   | "expr_is_defined ns (e1 \<guillemotleft>bop\<guillemotright> e2) = ((expr_is_defined ns e1) \<and> (expr_is_defined ns e2))"
   | "expr_is_defined ns (FunExp f tys e) = ((list_all closed tys) \<and> (list_all (expr_is_defined ns) e))"
   | "expr_is_defined ns (Forall ty e) = ((closed ty) \<and> (\<forall>w. (expr_is_defined (ext_env ns w) e)))"
   | "expr_is_defined ns (Exists ty e) =  ((closed ty) \<and> (\<forall>w. (expr_is_defined (ext_env ns w) e)))"
   | "expr_is_defined ns (ForallT e) = expr_is_defined ns e"
   | "expr_is_defined ns (ExistsT e) = expr_is_defined ns e"

lemma unop_type_correct: "\<lbrakk> unop_type uop = (arg_ty, ret_ty); ty_val_rel A v' (TPrim arg_ty); 
                         (unop_eval_val uop v') = Some v  \<rbrakk> \<Longrightarrow>
                       ty_val_rel A v (TPrim ret_ty)"
  by (cases uop; rule lit_val_elim[where v=v']; auto)

lemma unop_progress: "\<lbrakk> unop_type uop = (arg_ty, ret_ty); ty_val_rel A v' (TPrim arg_ty) \<rbrakk> \<Longrightarrow>
                       \<exists>v. (unop_eval_val uop v') = Some v "
  by (cases uop; rule lit_val_elim[where v=v']; auto)

lemma binop_type_correct: 
 "\<lbrakk> binop_type bop = Some ((left_ty,right_ty), ret_ty); 
    ty_val_rel A v1 (TPrim left_ty); ty_val_rel A v2 (TPrim right_ty); 
    (binop_eval_val bop v1 v2) = Some v  \<rbrakk> \<Longrightarrow>
    ty_val_rel A v (TPrim ret_ty)"
  by (cases bop; rule lit_val_elim[where v=v1]; rule lit_val_elim[where v=v2]; auto)

lemma binop_progress:
 "\<lbrakk> binop_type bop = Some ((left_ty,right_ty), ret_ty); 
    ty_val_rel A v1 (TPrim left_ty); ty_val_rel A v2 (TPrim right_ty)\<rbrakk> \<Longrightarrow>
    \<exists>v. (binop_eval_val bop v1 v2) = Some v "
  by (cases bop; rule lit_val_elim[where v=v1]; rule lit_val_elim[where v=v2]; auto)

lemma binop_poly_type_correct:
 "\<lbrakk> binop_poly_type bop; binop_eval_val bop v1 v2 = Some v \<rbrakk> \<Longrightarrow> ty_val_rel A v (TPrim TBool)"
  by (cases bop; rule lit_val_elim[where v=v1]; rule lit_val_elim[where v=v2]; auto)

text\<open>check whether the free variables of a type are at smaller than some value\<close>
fun wf_ty :: "nat \<Rightarrow> ty \<Rightarrow> bool"
  where 
   "wf_ty n (TVar i) = (i < n)"
 | "wf_ty n (TPrim p) = True"
 | "wf_ty n (TCon tcon_id ty_args) = list_all (wf_ty n) ty_args"

primrec wf_expr :: "nat \<Rightarrow> expr \<Rightarrow> bool"
  where 
    "wf_expr k (Var i) = True"
  | "wf_expr k (Lit l) = True"
  | "wf_expr k (UnOp uop e) = wf_expr k e"
  | "wf_expr k (e1 \<guillemotleft>bop\<guillemotright> e2) = (wf_expr k e1 \<and> wf_expr k e2)"
  | "wf_expr k (FunExp f ty_args args) = ((list_all (wf_ty k) ty_args) \<and> (list_all (wf_expr k) args))"
  | "wf_expr k (Forall ty e) = ((wf_ty k ty) \<and> (wf_expr k e))"
  | "wf_expr k (Exists ty e) = ((wf_ty k ty) \<and> (wf_expr k e))"
  | "wf_expr k (ExistsT e) = (wf_expr (k+1) e)"
  | "wf_expr k (ForallT e) = (wf_expr (k+1) e)"

text \<open>a function declaration is well-formed, if the free variables in the specified types are captured
by the type parameters of the function\<close>

fun wf_fdecl :: "(nat \<times> ty list \<times> ty) \<Rightarrow> bool"
  where 
    "wf_fdecl (n, args_ty, ret_ty) = ((list_all (wf_ty n) args_ty) \<and> (wf_ty n ret_ty))"

(*
lemma wf_closed: "closed \<tau> \<Longrightarrow> (\<And>n. wf_ty n \<tau>)"
  oops

lemma wf_substT: "closed \<tau>' \<Longrightarrow> wf_ty n \<tau> \<Longrightarrow> wf_ty (n-1) (\<tau>[0 \<mapsto>\<^sub>\<tau> \<tau>']\<^sub>\<tau>)"
  apply (induction \<tau>)
    apply auto[1]
  apply (simp add: wf_closed)
   apply simp
  oops

lemma wf_zero_closed: "wf_ty 0 \<tau> \<Longrightarrow> closed \<tau>"
  sorry

lemma closed_msubstT_2: "closed t \<Longrightarrow> msubstT ts t = t"
  sorry

lemma closed_msubstT: "list_all closed ts \<Longrightarrow> wf_ty (length ts) \<tau> \<Longrightarrow> closed (msubstT ts \<tau>)"
  sorry
*)

lemma closed_instantiate: "list_all closed \<Omega> \<Longrightarrow> wf_ty (length \<Omega>) \<tau> \<Longrightarrow> closed (instantiate \<Omega> \<tau>)"
  by (induction \<tau>) (auto simp: list_all_iff)

lemma msubst_msubst: 
  assumes "wf_ty (length ts2) t" and 
          "list_all (wf_ty (length ts1)) ts2" and 
          "list_all closed ts1"
  shows "msubstT ts1 (msubstT ts2 t) = msubstT (map (msubstT ts1) ts2) t"
  using assms
  oops

lemma instantiate_msubst_opt:
  assumes "wf_ty (length ts) \<tau>"
  shows "instantiate \<Omega> (msubstT_opt ts \<tau>) = instantiate (map (instantiate \<Omega>) ts) \<tau>"
  using assms
proof (induction \<tau>)
  case (TVar x)
  hence "x < length ts" by simp
  hence "msubstT_opt ts (TVar x) = ts ! x" by (simp add: msubstT_opt_def)
  thus ?case using \<open>x < length ts\<close> by simp
next
  case (TPrim x)
  then show ?case by (simp add: msubstT_opt_def)
next
  case (TCon x1a x2a)
  thus ?case 
  apply (simp add: msubstT_opt_def)
  by (metis (no_types, lifting) in_set_conv_nth list_all_length)
qed

lemma map_of_list_all:
  assumes Map:"map_of xs k = Some x" and
          Pred:"list_all (P \<circ> snd) xs"
  shows "P x"
proof -
  from Map obtain i where "(i,x) \<in> set xs"
    by (meson map_of_SomeD) 
  with Pred show ?thesis
    by (metis comp_apply in_set_conv_nth list_all_length snd_conv) 
qed

lemma map_map:
  assumes "map f (map g xs) = ys"
  shows "map (f \<circ> g) xs = ys"
  using assms
  by auto

theorem preservation:
  assumes 
          "list_all closed \<Omega>"
          "\<forall> k \<tau>'. (\<Delta> k = Some \<tau>') \<longrightarrow> (\<exists>v. (n_s k = Some v) \<and> ty_val_rel A v (instantiate \<Omega> \<tau>'))" and
          Wf_\<Gamma>:"fun_interp_wf A F \<Gamma>" and
          Wf_F:"list_all (wf_fdecl \<circ> snd) F" 
  shows "F, \<Delta> \<turnstile> e : \<tau> \<Longrightarrow> wf_expr (length \<Omega>) e \<Longrightarrow> A,(F,\<Gamma>),\<Omega> \<turnstile> \<langle>e,n_s\<rangle> \<Down> v \<Longrightarrow> ty_val_rel A v (instantiate \<Omega> \<tau>)" and 
        "F, \<Delta> \<turnstile> es [:] ts \<Longrightarrow> list_all (wf_expr (length \<Omega>)) es \<Longrightarrow> A,(F,\<Gamma>),\<Omega> \<turnstile> \<langle>es,n_s\<rangle> [\<Down>] vs \<Longrightarrow> 
          list_all (\<lambda> v_\<tau>. ty_val_rel A (fst (v_\<tau>)) (snd (v_\<tau>))) (zip vs (map (instantiate \<Omega>) ts))"
  using assms
proof (induction arbitrary: v \<Omega> and vs \<Omega> rule: typing_typing_list.inducts)
  case (TypVar \<Delta> x ty)
then show ?case by fastforce
next
case (TypPrim l prim_ty \<Delta>)
  then show ?case by fastforce
next
  case (TypUnOp uop arg_ty ret_ty \<Delta> e)
  from this obtain v' where 
     "A,(F, \<Gamma>),\<Omega> \<turnstile> \<langle>e,n_s\<rangle> \<Down> v'" and "unop_eval_val uop v' = Some v" by auto
  moreover from this have "ty_val_rel A v' (TPrim arg_ty)" using TypUnOp by auto
  ultimately show ?case using \<open>unop_type uop = (arg_ty, ret_ty)\<close> unop_type_correct by fastforce 
next
  case (TypBinOpMono bop left_ty right_ty ret_ty \<Delta> e1 e2)
  from this obtain v1 v2 where 
     "A, (F, \<Gamma>),\<Omega> \<turnstile> \<langle>e1, n_s\<rangle> \<Down> v1" and "A, (F, \<Gamma>), \<Omega> \<turnstile> \<langle>e2, n_s\<rangle> \<Down> v2" and 
     E:"binop_eval_val bop v1 v2 = Some v"
    by auto
  moreover from this have T1:"ty_val_rel A v1 (TPrim left_ty)" and T2:"ty_val_rel A v2 (TPrim right_ty)" using TypBinOpMono by auto
  ultimately show ?case using \<open>binop_type bop = Some ((left_ty, right_ty), ret_ty)\<close> binop_type_correct by fastforce
next
  case (TypBinopPoly bop \<Delta> e1 ty1 e2 ty2 ty_inst)
  from this obtain v1 v2 where 
     E:"binop_eval_val bop v1 v2 = Some v" by auto
  thus ?case using  \<open>binop_poly_type bop\<close> binop_poly_type_correct by fastforce
next
  case (TypFunExp f n_ty_params args_ty ret_ty ty_params args \<Delta>)
  from this obtain vargs fi where
     RedArgs:"A,(F,\<Gamma>),\<Omega> \<turnstile> \<langle>args, n_s\<rangle> [\<Down>] vargs" and Mem\<Gamma>:"\<Gamma> f = Some fi" and     
    "fi (map (instantiate \<Omega>) ty_params) vargs = Some v"
    by auto
  with TypFunExp have FunSingleWf:"fun_interp_single_wf A (n_ty_params, args_ty, ret_ty) fi"
    using fun_interp_wf_def by (metis (mono_tags, lifting) option.inject)
  have A1:"length (map (instantiate \<Omega>) ty_params) = n_ty_params" using TypFunExp
    using length_map by simp 
  have Wf_args_ty:"list_all (wf_ty n_ty_params) args_ty" using Wf_F \<open>map_of F f = Some (n_ty_params, args_ty, ret_ty)\<close>
    by (meson map_of_list_all wf_fdecl.simps)   
  have Wf_ret_ty:"wf_ty n_ty_params ret_ty" using Wf_F \<open>map_of F f = Some (n_ty_params, args_ty, ret_ty)\<close>
    by (meson map_of_list_all wf_fdecl.simps)
  have A3:"length vargs = length args_ty"
    using RedArgs TypFunExp.hyps(2) red_exprs_length by fastforce
  have A4:"list_all closed (map (instantiate \<Omega>) ty_params)"
    using TypFunExp.prems(1) TypFunExp.prems(3) closed_instantiate wf_ty.simps(3) by fastforce
  (* have "list_all (wf_expr 0) (map (instantiate \<Omega>) args)" using \<open>wf_expr 0 (msubst_ty_expr \<sigma>_ts (FunExp f ty_params args))\<close> by simp *)
  have "list_all (wf_expr (length \<Omega>)) args" using TypFunExp by simp
  have InstMSubst:"(map (instantiate \<Omega>) (map (msubstT_opt ty_params) args_ty)) = map (instantiate (map (instantiate \<Omega>) ty_params)) args_ty"
    using Wf_args_ty \<open>length ty_params = n_ty_params\<close>
    apply simp
    apply rule
    apply (rule instantiate_msubst_opt)
    by (simp add: list.pred_set)   
  have
   AZip:"list_all (\<lambda>v_\<tau>. ty_val_rel A (fst v_\<tau>) (snd v_\<tau>)) (zip vargs (map (instantiate \<Omega>) (map (msubstT_opt ty_params) args_ty)))"
    using TypFunExp.IH RedArgs TypFunExp.prems(3) TypFunExp.prems(4) TypFunExp.prems(5) TypFunExp.prems(6) \<open>list_all (wf_expr (length \<Omega>)) args\<close> by blast
  hence "ty_val_rel A v (instantiate (map (instantiate \<Omega>) ty_params) ret_ty)"
    apply (simp only: InstMSubst)
    using FunSingleWf A1 A3 A4 
    apply auto
    by (metis (no_types, lifting) A1 \<open>fi (map (instantiate \<Omega>) ty_params) vargs = Some v\<close> option.inject) 
  thus ?case using TypFunExp.IH(1) 
    by (metis TypFunExp.IH(1) TypFunExp.hyps(1) TypFunExp.prems(6) instantiate_msubst_opt map_of_list_all wf_fdecl.simps)
next
  case (TypForall \<Delta> ty e)
  then show ?case by (auto dest: forall_red)    
next
case (TypExists \<Delta> ty e)
  then show ?case by (auto dest: exists_red)
next
  case (TypForallT \<Delta> e)
  then show ?case using msubst_ty_forallT by (auto dest: forallt_red_bool)
next
  case (TypExistsT \<Delta> e)
  then show ?case using msubst_ty_existsT by (auto dest: existst_red_bool)
next
  case (TypListNil \<Delta>)
  then show ?case by simp
next
  case (TypListCons \<Delta> e ty es tys)
    from \<open>A,(F, \<Gamma>),\<Omega> \<turnstile> \<langle>(e # es),n_s\<rangle> [\<Down>] vs\<close> have
  "A,(F, \<Gamma>),\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> hd vs" and "A,(F, \<Gamma>),\<Omega> \<turnstile> \<langle>es, n_s\<rangle> [\<Down>] tl vs" 
      using cons_exp_elim by auto
  with TypListCons have A1:"ty_val_rel A (hd vs) ((instantiate \<Omega>) ty)" and
                        A2:"list_all (\<lambda>v_\<tau>. ty_val_rel A (fst v_\<tau>) (snd v_\<tau>)) (zip (tl vs) (map (instantiate \<Omega>) tys))"
    by auto
  moreover have "(hd vs) # (tl vs) = vs" using \<open>A,(F, \<Gamma>),\<Omega> \<turnstile> \<langle>(e # es),n_s\<rangle> [\<Down>] vs\<close> 
      using cons_exp_elim list.collapse by blast
  ultimately show ?case
  proof -
    have "list_all (\<lambda>p. ty_val_rel A (fst p) (snd p)) ((hd vs, instantiate \<Omega> ty) # zip (tl vs) (map (instantiate \<Omega>) tys))"
      using A1 A2 by auto
    then show ?thesis
      by (metis (no_types) \<open>hd vs # tl vs = vs\<close> list.simps(9) zip_Cons_Cons)
  qed
qed

(*
lemma env_corres_extend:
  assumes AVal:"ty_val_rel A w (instantiate \<Omega> ty)" and
          Acorres:"\<forall>k \<tau>'. \<Delta> k = Some \<tau>' \<longrightarrow> (\<exists>v. n_s k = Some v \<and> ty_val_rel A v (instantiate \<Omega> \<tau>'))"
        shows "\<forall>k \<tau>'. (env_shift \<Delta>(0 \<mapsto> ty)) k = Some \<tau>' \<longrightarrow> (\<exists>v. (env_shift n_s(0 \<mapsto> w)) k = Some v \<and> ty_val_rel A v (instantiate \<Omega> \<tau>'))"
  using assms
  by simp  
*)

lemma
  assumes "\<forall>k \<tau>'.
           \<Delta> k = Some \<tau>' \<longrightarrow> (\<exists>v. n_s k = Some v \<and> ty_val_rel A v (instantiate \<Omega> \<tau>'))"
  shows "\<forall>k \<tau>'.
            shift_env 1 0 \<Delta> k = Some \<tau>' \<longrightarrow> (\<exists>v. n_s k = Some v \<and> ty_val_rel A v (instantiate (t # \<Omega>) \<tau>'))"
  oops

lemma instantiate_shift: "wf_ty (length \<Omega>) \<tau> \<Longrightarrow> instantiate (t#\<Omega>) (shiftT 1 0 \<tau>) = instantiate \<Omega> \<tau>"
  by (induction \<tau>) (auto simp add: list_all_iff)
  
lemma instantiate_shift_wf: "wf_ty (length \<Omega>) \<tau> \<Longrightarrow> wf_ty (Suc (length \<Omega>)) (shiftT 1 0 \<tau>)"
 by (induction \<tau>) (auto simp add: list_all_iff)

(* TODO: add instantiation *)
theorem progress:
  assumes
          Closed_\<Omega>:"list_all closed \<Omega>" and
          "\<forall> k \<tau>'. (\<Delta> k = Some \<tau>') \<longrightarrow> wf_ty (length \<Omega>) \<tau>'" and
          "\<forall> k \<tau>'. (\<Delta> k = Some \<tau>') \<longrightarrow> (\<exists>v. (n_s k = Some v) \<and> ty_val_rel A v (instantiate \<Omega> \<tau>'))" and
          Wf_\<Gamma>:"fun_interp_wf A F \<Gamma>" and
          Wf_F:"list_all (wf_fdecl \<circ> snd) F"
         (* NonEmptyT:"\<forall> t. closed t \<longrightarrow> (\<exists>w. ty_val_rel A w t)" *)
  shows "F, \<Delta> \<turnstile> e : \<tau> \<Longrightarrow> expr_is_defined n_s e \<Longrightarrow>  wf_expr (length \<Omega>) e \<Longrightarrow>  \<exists>v. A,(F,\<Gamma>),\<Omega> \<turnstile> \<langle>e,n_s\<rangle> \<Down> v" and
        "F, \<Delta> \<turnstile> es [:] ts \<Longrightarrow> list_all (expr_is_defined n_s) es \<Longrightarrow>  \<exists>vs. A,(F,\<Gamma>),\<Omega> \<turnstile> \<langle>es,n_s\<rangle> [\<Down>] vs"
  using assms
proof (induction arbitrary: n_s \<Omega> and n_s \<Omega> rule: typing_typing_list.inducts)
case (TypVar \<Delta> x ty)
  show ?case 
    apply (rule exI[where ?x="the (n_s x)"])
    using TypVar(2)
    by (simp add: RedVar)
next
  case (TypPrim l prim_ty \<Delta>)
  then show ?case by (auto intro: RedLit)
next
  case (TypUnOp uop arg_ty ret_ty \<Delta> e)
  from this obtain v' where RedE:"A,(F, \<Gamma>), \<Omega> \<turnstile> \<langle>e,n_s\<rangle> \<Down> v'" by fastforce
  hence "ty_val_rel A v' (TPrim arg_ty)" 
    using TypUnOp preservation(1)[OF \<open>list_all closed \<Omega>\<close> TypUnOp.prems(5) Wf_\<Gamma> Wf_F]
    by fastforce  
  thus ?case using \<open>unop_type uop = (arg_ty, ret_ty)\<close> unop_progress RedE RedUnOp
    by (metis (full_types)) 
next
  case (TypBinOpMono bop left_ty right_ty ret_ty \<Delta> e1 e2)
  then show ?case sorry
next
  case (TypBinopPoly bop \<Delta> e1 ty1 e2 ty2 ty_inst)
  then show ?case sorry
next
  case (TypFunExp f n_ty_params args_ty ret_ty ty_params \<Delta> args)
  then show ?case sorry
next
  case (TypForall \<Delta> ty e)
  have RedBody:"\<And>w. ty_val_rel A w (instantiate \<Omega> ty) \<Longrightarrow> \<exists>v'. A, (F, \<Gamma>), \<Omega> \<turnstile> \<langle>e, ext_env n_s w\<rangle> \<Down> v'"
    apply (rule TypForall.IH)
    using \<open>expr_is_defined n_s (Forall ty e)\<close> expr_is_defined.simps(6) apply blast
    using TypForall.prems by auto
  have EnvCorres:"\<And>w. ty_val_rel A w (instantiate \<Omega> ty) \<Longrightarrow> \<forall>k \<tau>'. (ext_env \<Delta> ty) k = Some \<tau>' \<longrightarrow> (\<exists>v. (ext_env n_s w) k = Some v \<and> ty_val_rel A v (instantiate \<Omega> \<tau>'))"
    using TypForall.prems(5)
    by simp
  
  have RedBodyTy:"\<And>w v'. ty_val_rel A w (instantiate \<Omega> ty) \<Longrightarrow> A, (F, \<Gamma>), \<Omega> \<turnstile> \<langle>e, ext_env n_s w\<rangle> \<Down> v' \<Longrightarrow>
        ty_val_rel A v' (TPrim TBool)"
    using preservation(1)[OF \<open>list_all closed \<Omega>\<close> EnvCorres Wf_\<Gamma> Wf_F]
          TypForall.IH(1) TypForall.prems(2) by fastforce
  show ?case
  proof (cases "\<forall> w. ty_val_rel A w (instantiate \<Omega> ty) \<longrightarrow> A, (F, \<Gamma>), \<Omega> \<turnstile> \<langle>e, ext_env n_s w\<rangle> \<Down> LitV (LBool True)")
    case True
    show ?thesis
      using RedForAllTrue True by blast   
  next
    case False
    from this obtain w where
       "ty_val_rel A w (instantiate \<Omega> ty)" and "\<not> (A,(F, \<Gamma>),\<Omega> \<turnstile> \<langle>e, ext_env n_s w\<rangle> \<Down> LitV (LBool True))"
      by auto
    moreover from this RedBody RedBodyTy obtain w' where "A,(F, \<Gamma>),\<Omega> \<turnstile> \<langle>e, ext_env n_s w\<rangle> \<Down> w'"
      and "ty_val_rel A w' (TPrim (TBool))"
    by fastforce
    ultimately show ?thesis
      by (metis (full_types) RedForAllFalse type_of_val_bool_elim) 
  qed
next
  case (TypExists \<Delta> ty e)
  (*  proof is almost identical to TypForall, TODO: re-use proof *)
  have RedBody:"\<And>w. ty_val_rel A w (instantiate \<Omega> ty) \<Longrightarrow> \<exists>v'. A, (F, \<Gamma>), \<Omega> \<turnstile> \<langle>e, ext_env n_s w\<rangle> \<Down> v'"
    apply (rule TypExists.IH)
    using \<open>expr_is_defined n_s (Exists ty e)\<close> expr_is_defined.simps(7) apply blast
    using TypExists.prems by auto
  have EnvCorres:"\<And>w. ty_val_rel A w (instantiate \<Omega> ty) \<Longrightarrow> \<forall>k \<tau>'. (ext_env \<Delta> ty) k = Some \<tau>' \<longrightarrow> (\<exists>v. (ext_env n_s w) k = Some v \<and> ty_val_rel A v (instantiate \<Omega> \<tau>'))"
    using TypExists.prems(5)
    by simp
  
  have RedBodyTy:"\<And>w v'. ty_val_rel A w (instantiate \<Omega> ty) \<Longrightarrow> A, (F, \<Gamma>), \<Omega> \<turnstile> \<langle>e, ext_env n_s w\<rangle> \<Down> v' \<Longrightarrow>
        ty_val_rel A v' (TPrim TBool)"
    using preservation(1)[OF \<open>list_all closed \<Omega>\<close> EnvCorres Wf_\<Gamma> Wf_F]
          TypExists.IH(1) TypExists.prems(2) by fastforce
  show ?case
  proof (cases "\<forall> w. ty_val_rel A w (instantiate \<Omega> ty) \<longrightarrow> A, (F, \<Gamma>), \<Omega> \<turnstile> \<langle>e, ext_env n_s w\<rangle> \<Down> LitV (LBool False)")
    case True
    show ?thesis
      using RedExistsFalse True by blast   
  next
    case False
    from this obtain w where
       "ty_val_rel A w (instantiate \<Omega> ty)" and "\<not> (A,(F, \<Gamma>),\<Omega> \<turnstile> \<langle>e, ext_env n_s w\<rangle> \<Down> LitV (LBool False))"
      by auto
    moreover from this RedBody RedBodyTy obtain w' where "A,(F, \<Gamma>),\<Omega> \<turnstile> \<langle>e, ext_env n_s w\<rangle> \<Down> w'"
      and "ty_val_rel A w' (TPrim (TBool))"
    by fastforce
    ultimately show ?thesis
      by (metis (full_types) RedExistsTrue type_of_val_bool_elim) 
  qed
next
  case (TypForallT \<Delta> e)
  have RedBody:"\<And>t. closed t \<Longrightarrow> (\<exists>v. A,(F, \<Gamma>), t#\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v)"    
    apply (rule TypForallT.IH)
    using \<open>expr_is_defined n_s (ForallT e)\<close> apply simp
    using TypForallT.prems
    apply simp_all
    using instantiate_shift_wf apply fastforce
    using instantiate_shift by auto

  have Closed\<Omega>Ext: "\<And>t. closed t \<Longrightarrow> list_all closed (t#\<Omega>)"
    using \<open>list_all closed \<Omega>\<close> by simp

  have RedBodyTy:"\<And>t v. closed t \<Longrightarrow> A,(F, \<Gamma>), t#\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v \<Longrightarrow> ty_val_rel A v (instantiate (t#\<Omega>) (TPrim TBool))"
    apply (rule preservation(1)[where ?\<Delta>="shift_env 1 0 \<Delta>" and ?n_s="n_s"])
          apply (simp add: \<open>list_all closed \<Omega>\<close>)
    using TypForallT.prems instantiate_shift
         apply fastforce
        apply (rule Wf_\<Gamma>)
       apply (rule Wf_F)
      apply (rule TypForallT.IH(1))
    using TypForallT.prems apply simp_all
   done
  show ?case 
  proof (cases "\<forall>t. closed t \<longrightarrow> A,(F, \<Gamma>),t#\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool True)")
    case True
    show ?thesis
      using RedForallT_True True by blast
  next
    case False
    from this obtain t where "closed t" and "\<not>(A,(F, \<Gamma>),t#\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool True))" by auto
    moreover from this RedBody RedBodyTy obtain w' where "A,(F, \<Gamma>),(t#\<Omega>) \<turnstile> \<langle>e, n_s\<rangle> \<Down> w'"
      and "ty_val_rel A w' (TPrim (TBool))" by fastforce
    ultimately show ?thesis
      by (metis (full_types) RedForallT_False type_of_val_bool_elim)
  qed
next
  case (TypExistsT \<Delta> e)
  (* proof is almost identical to TypForallT, TODO: re-use proof *)

  have RedBody:"\<And>t. closed t \<Longrightarrow> (\<exists>v. A,(F, \<Gamma>), t#\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v)"    
    apply (rule TypExistsT.IH)
    using \<open>expr_is_defined n_s (ExistsT e)\<close> apply simp
    using TypExistsT.prems
    apply simp_all
    using instantiate_shift_wf apply fastforce
    using instantiate_shift by auto

  have Closed\<Omega>Ext: "\<And>t. closed t \<Longrightarrow> list_all closed (t#\<Omega>)"
    using \<open>list_all closed \<Omega>\<close> by simp

  have RedBodyTy:"\<And>t v. closed t \<Longrightarrow> A,(F, \<Gamma>), t#\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v \<Longrightarrow> ty_val_rel A v (instantiate (t#\<Omega>) (TPrim TBool))"
    apply (rule preservation(1)[where ?\<Delta>="shift_env 1 0 \<Delta>" and ?n_s="n_s"])
          apply (simp add: \<open>list_all closed \<Omega>\<close>)
    using TypExistsT.prems instantiate_shift
         apply fastforce
        apply (rule Wf_\<Gamma>)
       apply (rule Wf_F)
      apply (rule TypExistsT.IH(1))
    using TypExistsT.prems apply simp_all
   done
  
  show ?case
  proof (cases "\<forall>t. closed t \<longrightarrow> A,(F, \<Gamma>),t#\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool False)")
    case True
    show ?thesis
      using RedExistsT_False True by blast
  next
    case False
    from this obtain t where "closed t" and "\<not>(A,(F, \<Gamma>),t#\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool False))" by auto
    moreover from this RedBody RedBodyTy obtain w' where "A,(F, \<Gamma>),(t#\<Omega>) \<turnstile> \<langle>e, n_s\<rangle> \<Down> w'"
      and "ty_val_rel A w' (TPrim (TBool))" by fastforce
    ultimately show ?thesis
     by (metis (full_types) RedExistsT_True type_of_val_bool_elim)
  qed
next
  case (TypListNil \<Delta>)
  then show ?case sorry
next
  case (TypListCons \<Delta> e ty es tys)
  then show ?case sorry
qed



end