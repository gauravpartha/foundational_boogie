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
   | "expr_is_defined ns (Forall ty e) = ((closed ty) \<and> (expr_is_defined ns e))"
   | "expr_is_defined ns (Exists ty e) =  ((closed ty) \<and> (expr_is_defined ns e))"
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
  assumes "\<forall> k \<tau>'. (\<Delta> k = Some \<tau>') \<longrightarrow> (\<exists>v. (n_s k = Some v) \<and> ty_val_rel A v (msubstT \<sigma>_ts \<tau>'))" and
          Wf_\<Gamma>:"fun_interp_wf A F \<Gamma>" and
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
     RedArgs:"A,(F,\<Gamma>) \<turnstile> \<langle>map (msubst_ty_expr \<sigma>_ts) args, n_s\<rangle> [\<Down>] vargs" and Mem\<Gamma>:"\<Gamma> f = Some fi" and     
    "fi (map (msubstT \<sigma>_ts) ty_params) vargs = Some v"
    by auto
  with TypFunExp have FunSingleWf:"fun_interp_single_wf A (n_ty_params, args_ty, ret_ty) fi"
    using fun_interp_wf_def by (metis (mono_tags, lifting) option.inject)
  (* well-formedness assumptions *)
  have A1:"length ty_params = n_ty_params" sorry
  (*have A2:"list_all closed ty_params" sorry*)
  have A3:"length vargs = length args_ty" sorry
  have A4:"list_all closed (map (msubstT \<sigma>_ts) ty_params)" sorry
  (* derive argument typing *)
  have "list_all (wf_expr 0) (map (msubst_ty_expr \<sigma>_ts) args)" using \<open>wf_expr 0 (msubst_ty_expr \<sigma>_ts (FunExp f ty_params args))\<close> by simp
  hence "list_all (\<lambda>v_\<tau>. ty_val_rel A (fst v_\<tau>) (snd v_\<tau>)) (zip vargs (map (msubstT \<sigma>_ts) (map (msubstT ty_params) args_ty)))"
    using TypFunExp.IH(3) RedArgs Wf_\<Gamma> Wf_F TypFunExp.prems(3) TypFunExp.prems(6) by blast  
  with FunSingleWf A1 A3 A4 show ?case 
    sorry
  (*
  from Wf_F \<open>map_of F f = Some (n_ty_params, args_ty, ret_ty)\<close> have "wf_fdecl (n_ty_params, args_ty, ret_ty)" using map_of_list_all
    by fastforce
  hence "(list_all (wf_ty n_ty_params) args_ty)" and "(wf_ty n_ty_params ret_ty)" by auto
  *)
  (*
  with \<open> length ty_params = n_ty_params\<close> have "list_all closed (map (msubstT \<sigma>_ts) args_ty)"
    using closed_msubstT[OF \<open>list_all closed \<sigma>_ts\<close>]
  *)
next
  case (TypForall \<Delta> ty e)
  then show ?case by auto
next
case (TypExists \<Delta> ty e)
  then show ?case by auto
next
  case (TypForallT \<Delta> e)
  then show ?case using msubst_ty_forallT by auto
next
  case (TypExistsT \<Delta> e)
  then show ?case using msubst_ty_existsT by auto
next
  case (TypListNil \<Delta>)
  then show ?case by simp
next
  case (TypListCons \<Delta> e ty es tys)
  from \<open>A,(F, \<Gamma>) \<turnstile> \<langle>map (msubst_ty_expr \<sigma>_ts) (e # es),n_s\<rangle> [\<Down>] vs\<close> have
  "A,(F, \<Gamma>) \<turnstile> \<langle>msubst_ty_expr \<sigma>_ts e, n_s\<rangle> \<Down> hd vs" and "A,(F, \<Gamma>) \<turnstile> \<langle>map (msubst_ty_expr \<sigma>_ts) es, n_s\<rangle> [\<Down>] tl vs"
    using cons_exp_elim red_exprs_length by auto
  with TypListCons have A1:"ty_val_rel A (hd vs) (msubstT \<sigma>_ts ty)" and
                        A2:"list_all (\<lambda>v_\<tau>. ty_val_rel A (fst v_\<tau>) (snd v_\<tau>)) (zip (tl vs) (map (msubstT \<sigma>_ts) tys))"
    by auto
  from \<open>A,(F, \<Gamma>) \<turnstile> \<langle>map (msubst_ty_expr \<sigma>_ts) (e # es),n_s\<rangle> [\<Down>] vs\<close> have
      "length (map (msubst_ty_expr \<sigma>_ts) (e # es)) = length vs" using red_exprs_length by fastforce
  hence "vs = (hd vs)#(tl vs)"
    by (metis length_0_conv length_map list.distinct(1) list.exhaust_sel) 
  then show ?case using A1 A2 sorry  
qed


(* TODO: add instantiation *)
theorem progress:
  assumes 
       "\<forall> k \<tau>'. (\<Delta> k = Some \<tau>') \<longrightarrow> (\<exists>v. (n_s k = Some v) \<and> ty_val_rel A v (msubstT \<sigma>_ts \<tau>'))" and
          Wf_\<Gamma>:"fun_interp_wf A F \<Gamma>" and
          Wf_F:"list_all (wf_fdecl \<circ> snd) F" and
          "list_all closed \<sigma>_ts"
  shows "F, \<Delta> \<turnstile> e : \<tau> \<Longrightarrow> expr_is_defined n_s e \<Longrightarrow>  wf_expr 0 (msubst_ty_expr \<sigma>_ts e) \<Longrightarrow>  \<exists>v. A,(F,\<Gamma>) \<turnstile> \<langle>msubst_ty_expr \<sigma>_ts e,n_s\<rangle> \<Down> v" and
        "F, \<Delta> \<turnstile> es [:] ts \<Longrightarrow> list_all (expr_is_defined n_s) es \<Longrightarrow>  \<exists>vs. A,(F,\<Gamma>) \<turnstile> \<langle>map (msubst_ty_expr \<sigma>_ts) es,n_s\<rangle> [\<Down>] vs"
  using assms
proof (induction arbitrary: \<sigma>_ts and \<sigma>_ts rule: typing_typing_list.inducts)
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
  from this obtain v' where RedE:"A,(F, \<Gamma>) \<turnstile> \<langle>msubst_ty_expr \<sigma>_ts e,n_s\<rangle> \<Down> v'" by fastforce
  hence "ty_val_rel A v' (TPrim arg_ty)" using TypUnOp preservation(1)[OF TypUnOp(6) Wf_\<Gamma> Wf_F TypUnOp(9) TypUnOp(2)]
    by simp 
  thus ?case using \<open>unop_type uop = (arg_ty, ret_ty)\<close> unop_progress RedE RedUnOp
    by (metis msubst_ty_unop)
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



end