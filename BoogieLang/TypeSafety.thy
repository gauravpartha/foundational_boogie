theory TypeSafety
imports Semantics Typing
begin

fun expr_is_defined :: "'a nstate \<Rightarrow> expr \<Rightarrow> bool"
  where
     "expr_is_defined ns (Var i) = (ns(i) \<noteq> None)"
   | "expr_is_defined ns (Lit l) = True"
   | "expr_is_defined ns (UnOp uop e) = expr_is_defined ns e"
   | "expr_is_defined ns (e1 \<guillemotleft>bop\<guillemotright> e2) = ((expr_is_defined ns e1) \<and> (expr_is_defined ns e2))"
   | "expr_is_defined ns (FunExp f tys e) = ((list_all closed tys) \<and> (list_all (expr_is_defined ns) e))"
   | "expr_is_defined ns (Forall ty e) = ((closed ty) \<and> (expr_is_defined ns e))"
   | "expr_is_defined ns (Exists ty e) =  ((closed ty) \<and> (expr_is_defined ns e))"
   | "expr_is_defined ns (ForallT e) = expr_is_defined ns e"
   | "expr_is_defined ns (ExistsT e) = expr_is_defined ns e"

lemma unop_type_correct: "\<lbrakk> unop_type uop = (arg_ty, ret_ty); ty_val_rel A v' (TPrim arg_ty); 
                         (unop_eval_val uop v') = Some v  \<rbrakk> \<Longrightarrow>
                       ty_val_rel A v (TPrim ret_ty)"
  by (cases uop; rule lit_val_elim[where v=v']; auto)

lemma binop_type_correct: 
 "\<lbrakk> binop_type bop = Some ((left_ty,right_ty), ret_ty); 
    ty_val_rel A v1 (TPrim left_ty); ty_val_rel A v2 (TPrim right_ty); 
    (binop_eval_val bop v1 v2) = Some v  \<rbrakk> \<Longrightarrow>
    ty_val_rel A v (TPrim ret_ty)"
  by (cases bop; rule lit_val_elim[where v=v1]; rule lit_val_elim[where v=v2]; auto)

lemma binop_poly_type_correct:
 "\<lbrakk> binop_poly_type bop; binop_eval_val bop v1 v2 = Some v \<rbrakk> \<Longrightarrow> ty_val_rel A v (TPrim TBool)"
  by (cases bop; rule lit_val_elim[where v=v1]; rule lit_val_elim[where v=v2]; auto)

(*lemma subst_closed_1: "*)

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

lemma wf_closed: "closed \<tau> \<Longrightarrow> (\<And>n. wf_ty n \<tau>)"
  sorry

lemma wf_substT: "closed \<tau>' \<Longrightarrow> wf_ty n \<tau> \<Longrightarrow> wf_ty (n-1) (\<tau>[0 \<mapsto>\<^sub>\<tau> \<tau>']\<^sub>\<tau>)"
  apply (induction \<tau>)
    apply auto[1]
  apply (simp add: wf_closed)
   apply simp
  sorry

lemma wf_zero_closed: "wf_ty 0 \<tau> \<Longrightarrow> closed \<tau>"
  sorry

lemma closed_msubstT: "list_all closed ts \<Longrightarrow> wf_ty (length ts) \<tau> \<Longrightarrow> closed (msubstT ts \<tau>)"
  sorry

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

(* desired theorems, probably well-formedness assumptions missing *)
theorem preservation:
  assumes "\<And>k \<tau>'. (\<Delta> k = Some \<tau>') \<Longrightarrow> \<exists>v. (n_s k = Some v) \<and> ty_val_rel A v (msubstT \<sigma>_ts \<tau>')" and
          "fun_interp_wf A F \<Gamma>" and
          Wf_F:"list_all (wf_fdecl \<circ> snd) F" and
          "list_all closed \<sigma>_ts"
  shows "F, \<Delta> \<turnstile> e : \<tau> \<Longrightarrow> wf_expr 0 (msubst_ty_expr \<sigma>_ts e) \<Longrightarrow> A,(F,\<Gamma>) \<turnstile> \<langle>msubst_ty_expr \<sigma>_ts e,n_s\<rangle> \<Down> v \<Longrightarrow> ty_val_rel A v (msubstT \<sigma>_ts \<tau>)" and 
        "F, \<Delta> \<turnstile> es [:] ts \<Longrightarrow> list_all (wf_expr 0) (map (msubst_ty_expr \<sigma>_ts) es) \<Longrightarrow> A,(F,\<Gamma>) \<turnstile> \<langle>map (msubst_ty_expr \<sigma>_ts) es,n_s\<rangle> [\<Down>] vs \<Longrightarrow> 
          list_all (\<lambda> v_\<tau>. ty_val_rel A (fst (v_\<tau>)) (snd (v_\<tau>))) (zip vs (map (msubstT \<sigma>_ts) ts))"
  using assms
proof (induction arbitrary: v \<sigma>_ts and vs \<sigma>_ts rule: typing_typing_list.inducts)
  case (TypVar \<Delta> x ty)
then show ?case by fastforce
next
case (TypPrim l prim_ty \<Delta>)
  then show ?case by fastforce
next
  case (TypUnOp uop arg_ty ret_ty \<Delta> e)
  from this obtain v' where 
     "A,(F, \<Gamma>) \<turnstile> \<langle>(msubst_ty_expr \<sigma>_ts e),n_s\<rangle> \<Down> v'" and "unop_eval_val uop v' = Some v" by auto
  moreover from this have "ty_val_rel A v' (TPrim arg_ty)" using TypUnOp by auto
  ultimately show ?case using \<open>unop_type uop = (arg_ty, ret_ty)\<close> unop_type_correct by fastforce 
next
  case (TypBinOpMono bop left_ty right_ty ret_ty \<Delta> e1 e2)
  from this obtain v1 v2 where 
     "A, (F, \<Gamma>) \<turnstile> \<langle>msubst_ty_expr \<sigma>_ts e1, n_s\<rangle> \<Down> v1" and "A, (F, \<Gamma>) \<turnstile> \<langle>msubst_ty_expr \<sigma>_ts e2, n_s\<rangle> \<Down> v2" and 
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
  case (TypFunExp f n_ty_params args_ty ret_ty ty_params \<Delta> args)
  from this obtain vargs fi where
     A1:"A,(F,\<Gamma>) \<turnstile> \<langle>map (msubst_ty_expr \<sigma>_ts) args, n_s\<rangle> [\<Down>] vargs" and A2:"\<Gamma> f = Some fi" and     
    "fi (map (msubstT \<sigma>_ts) ty_params) vargs = Some v"
    by auto
  with TypFunExp have "fun_interp_single_wf A (n_ty_params, args_ty, ret_ty) fi"
    using fun_interp_wf_def by (metis (mono_tags, lifting) option.inject) 
  from Wf_F \<open>map_of F f = Some (n_ty_params, args_ty, ret_ty)\<close> have "wf_fdecl (n_ty_params, args_ty, ret_ty)" using map_of_list_all
    by fastforce
  hence "(list_all (wf_ty n_ty_params) args_ty)" and "(wf_ty n_ty_params ret_ty)" by auto
  with \<open> length ty_params = n_ty_params\<close> have "list_all closed (map (msubstT \<sigma>_ts) args_ty)" 
    using closed_msubstT[OF \<open>list_all closed \<sigma>_ts\<close>] 
    
    
  
    
    
    
    
  then show ?case sorry
next
  case (TypForall \<Delta> ty e)
  then show ?case sorry
next
case (TypExists \<Delta> ty e)
  then show ?case sorry
next
  case (TypForallT \<Delta> e)
  then show ?case sorry
next
  case (TypExistsT \<Delta> e)
  then show ?case sorry
next
  case (TypListNil \<Delta>)
  then show ?case sorry
next
  case (TypListCons \<Delta> e ty es tys)
  then show ?case sorry
qed


(* TODO: add instantiation *)
theorem progress:
  assumes "F, \<Delta> \<turnstile> e : \<tau>" and
          "\<And>k \<tau>'. (\<Delta> k = Some \<tau>') \<Longrightarrow> \<exists>v. (n_s k = Some v) \<and> ty_val_rel A v \<tau>'"
          "expr_is_defined n_s e" and
          "fun_interp_wf A F \<Gamma>"
  shows "\<exists>v. A,(F,\<Gamma>) \<turnstile> \<langle>e,n_s\<rangle> \<Down> v"
  oops



end