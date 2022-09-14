theory BoogieDeBruijn
imports Lang
begin
 
text \<open>We define the machinery required to define substitution functions to substitute
arbitrary, potentially open, types. This is inspired by inspired by Vouillon's and Berghofer's 
POPLMark solutions\<close>
fun ext_env :: "(nat \<Rightarrow> 'a option) \<Rightarrow> 'a \<Rightarrow> (nat \<Rightarrow> 'a option)"
  where "ext_env f x = (\<lambda>m. f (m-1))(0 \<mapsto> x)"

primrec shiftT :: "nat \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> ty" 
where
  "shiftT n k (TVar i) = (if i < k then TVar i else TVar (i + n))"
| "shiftT n k (TPrim tp) = (TPrim tp)"
| "shiftT n k (TCon tcon_id ty_args) = (TCon tcon_id (map (shiftT n k) ty_args))"

primrec shift :: "nat \<Rightarrow> nat \<Rightarrow> expr \<Rightarrow> expr" ("\<up>")
where
  "\<up> n k (Var i) = Var i"
| "\<up> n k (BVar i) = (if i < k then BVar i else BVar (i + n))"
| "\<up> n k (Lit l) = (Lit l)"
| "\<up> n k (UnOp uop e) = UnOp uop (\<up> n k e)"
| "\<up> n k (e1 \<guillemotleft>bop\<guillemotright> e2) = (\<up> n k e1) \<guillemotleft>bop\<guillemotright> (\<up> n k e2)"
| "\<up> n k (FunExp f ty_args args) = FunExp f ty_args (map (\<up> n k) args)"
| "\<up> n k (CondExp cond els thn) = CondExp (\<up> n k cond) (\<up> n k els) (\<up> n k thn)"
| "\<up> n k (Old e) = Old (\<up> n k e)"
| "\<up> n k (Forall ty e) = (Forall ty (\<up> n (k+1) e))"
| "\<up> n k (Exists ty e) = (Exists ty (\<up> n (k+1) e))"
| "\<up> n k (ForallT e) = (ForallT (\<up> n k e))"
| "\<up> n k (ExistsT e) = (ExistsT (\<up> n k e))"

fun shift_env :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<rightharpoonup> ty) \<Rightarrow> (nat \<rightharpoonup> ty)"
  where "shift_env n k \<Delta> m = map_option (shiftT n k) (\<Delta> m)"

primrec shift_ty_term :: "nat \<Rightarrow> nat \<Rightarrow> expr \<Rightarrow> expr" ("\<up>\<^sub>\<tau>")
  where
  "\<up>\<^sub>\<tau> n k (Var i) = Var i"
| "\<up>\<^sub>\<tau> n k (BVar i) = BVar i"
| "\<up>\<^sub>\<tau> n k (Lit l) = (Lit l)"
| "\<up>\<^sub>\<tau> n k (UnOp uop e) = UnOp uop (\<up>\<^sub>\<tau> n k e)"
| "\<up>\<^sub>\<tau> n k (e1 \<guillemotleft>bop\<guillemotright> e2) = (\<up>\<^sub>\<tau> n k e1) \<guillemotleft>bop\<guillemotright> (\<up>\<^sub>\<tau> n k e2)"
| "\<up>\<^sub>\<tau> n k (FunExp f ty_args args) = FunExp f (map (shiftT n k) ty_args) (map (\<up>\<^sub>\<tau> n k) args)"
| "\<up>\<^sub>\<tau> n k (CondExp cond thn els) = CondExp (\<up>\<^sub>\<tau> n k cond) (\<up>\<^sub>\<tau> n k thn) (\<up>\<^sub>\<tau> n k els)"
| "\<up>\<^sub>\<tau> n k (Old e) = Old (\<up>\<^sub>\<tau> n k e)"
| "\<up>\<^sub>\<tau> n k (Forall ty e) = (Forall (shiftT n k ty) (\<up>\<^sub>\<tau> n k e))"
| "\<up>\<^sub>\<tau> n k (Exists ty e) = (Exists (shiftT n k ty) (\<up>\<^sub>\<tau> n k e))"
| "\<up>\<^sub>\<tau> n k (ForallT e) = (ForallT (\<up>\<^sub>\<tau> n (k+1) e))"
| "\<up>\<^sub>\<tau> n k (ExistsT e) = (ExistsT (\<up>\<^sub>\<tau> n (k+1) e))"


primrec substT :: "ty \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> ty"  ("_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>\<tau>" [300, 0, 0] 300)
  where
  "(TVar i)[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> = (if k < i then TVar (i - 1) else if i = k then shiftT k 0 S else TVar i)"
| "(TPrim p)[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> = TPrim p"
| "(TCon tcon_id ty_args)[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> = TCon tcon_id (map (\<lambda>t. t[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>) ty_args)"

text\<open>At the top-level, e[k \<mapsto>_\<tau> S] must only be used for k = 0, since the function assumes that
S must be shifted by j if variable j must be substituted.\<close>

primrec subst_ty_expr :: "expr \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> expr" ("_[_ \<mapsto>\<^sub>\<tau> _]" [300, 0, 0] 300)
  where
    "(Var i)[k \<mapsto>\<^sub>\<tau> S] = Var i"
  | "(BVar i)[k \<mapsto>\<^sub>\<tau> S] = BVar i"
  | "(Lit l)[k \<mapsto>\<^sub>\<tau> S] = (Lit l)"
  | "(UnOp uop e)[k \<mapsto>\<^sub>\<tau> S] = UnOp uop (e[k \<mapsto>\<^sub>\<tau> S])"
  | "(e1 \<guillemotleft>bop\<guillemotright> e2)[k \<mapsto>\<^sub>\<tau> S] = (e1[k \<mapsto>\<^sub>\<tau> S]) \<guillemotleft>bop\<guillemotright> (e2[k \<mapsto>\<^sub>\<tau> S])"
  | "(FunExp f ty_args args)[k \<mapsto>\<^sub>\<tau> S] = FunExp f (map (\<lambda>t. t[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>) ty_args) (map (\<lambda>e. e[k \<mapsto>\<^sub>\<tau> S]) args)"
  | "(CondExp cond thn els)[k \<mapsto>\<^sub>\<tau> S] = CondExp (cond[k \<mapsto>\<^sub>\<tau> S]) (thn[k \<mapsto>\<^sub>\<tau> S]) (els[k \<mapsto>\<^sub>\<tau> S])"
  | "(Old e)[k \<mapsto>\<^sub>\<tau> S] = Old (e[k \<mapsto>\<^sub>\<tau> S])"
  | "(Forall ty e)[k \<mapsto>\<^sub>\<tau> S] = (Forall (ty[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>) (e[k \<mapsto>\<^sub>\<tau> S]))"
  | "(Exists ty e)[k \<mapsto>\<^sub>\<tau> S] = (Exists (ty[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>) (e[k \<mapsto>\<^sub>\<tau> S]))"
  | "(ForallT e)[k \<mapsto>\<^sub>\<tau> S] = (ForallT (e[k+1 \<mapsto>\<^sub>\<tau> S]))"
  | "(ExistsT e)[k \<mapsto>\<^sub>\<tau> S] = (ExistsT (e[k+1 \<mapsto>\<^sub>\<tau> S]))"


text\<open>Most of the following were adapted from Berhofer's POPLMark solution\<close>

lemma shiftT_shiftT [simp]:
  "i \<le> j \<Longrightarrow> j \<le> i + m \<Longrightarrow> shiftT n j (shiftT m i T) = shiftT (m + n) i T"
  by (induct T arbitrary: i j m n) simp_all

lemma shiftT_shiftT' [simp]:
  "i + m \<le> j \<Longrightarrow> shiftT n j (shiftT m i T) = shiftT m i (shiftT n (j - m) T)"
  apply (induct T arbitrary: i j m n)
  apply simp_all
  apply arith
(* from Berghofer, not required here
  apply (subgoal_tac "Suc j - m = Suc (j - m)")
  apply simp
  apply arith
*)
  done

lemma shiftT_size [simp]: "size (shiftT n k T) = size T"
  apply (induct T arbitrary: k; simp) 
  by (simp add: eq_iff size_list_pointwise)

lemma shiftT0 [simp]: "shiftT 0 i T = T"
  apply (induct T arbitrary: i) by (auto simp add: map_idI)

lemma shift0 [simp]: "\<up> 0 i t = t"
  by (induct t arbitrary: i) (auto simp add: map_idI)

theorem substT_shiftT [simp]:
  "k \<le> k' \<Longrightarrow> k' < k + n \<Longrightarrow> (shiftT n k T)[k' \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau> = shiftT (n - 1) k T"
  by (induct T arbitrary: k k'; simp)

theorem shiftT_substT [simp]:
  "k \<le> k' \<Longrightarrow> shiftT n k (T[k' \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>) = shiftT n k T[k' + n \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>"
  apply (induct T arbitrary: k k')
  apply simp_all
  done

theorem shiftT_substT' [simp]: "k' < k \<Longrightarrow>
  shiftT n k (T[k' \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>) = shiftT n (k + 1) T[k' \<mapsto>\<^sub>\<tau> shiftT n (k - k') U]\<^sub>\<tau>"
  apply (induct T arbitrary: k k')
  apply simp_all
  apply arith
  done

(* no equivalent 
lemma shiftT_substT_Top [simp]:
  "k \<le> k' \<Longrightarrow> shiftT n k' (T[k \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>) = shiftT n (Suc k') T[k \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>"
*)

lemma liftT_substT_strange:
  "shiftT n k T[n + k \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau> = shiftT n (Suc k) T[k \<mapsto>\<^sub>\<tau> shiftT n 0 U]\<^sub>\<tau>"
  apply (induct T arbitrary: n k)
    apply simp_all
  done 
(* required in Berhofer's proof, not here
  apply (thin_tac "\<And>x. PROP P x" for P :: "_ \<Rightarrow> prop")
  apply (drule_tac x=n in meta_spec)
  apply (drule_tac x="Suc k" in meta_spec)
  apply simp
  done
*)

lemma lift_lift [simp]:
  "k \<le> k' \<Longrightarrow> k' \<le> k + n \<Longrightarrow> \<up> n' k' (\<up> n k t) = \<up> (n + n') k t"
  by (induct t arbitrary: k k') simp_all

lemma substT_substT:
  "i \<le> j \<Longrightarrow> T[Suc j \<mapsto>\<^sub>\<tau> V]\<^sub>\<tau>[i \<mapsto>\<^sub>\<tau> U[j - i \<mapsto>\<^sub>\<tau> V]\<^sub>\<tau>]\<^sub>\<tau> = T[i \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>[j \<mapsto>\<^sub>\<tau> V]\<^sub>\<tau>"
  apply (induct T arbitrary: i j U V)
    apply (simp_all add: diff_Suc split: nat.split)
  done 
(* required in Berghofer's proof, not here 
  apply (thin_tac "\<And>x. PROP P x" for P :: "_ \<Rightarrow> prop")
  apply (drule_tac x="Suc i" in meta_spec)
  apply (drule_tac x="Suc j" in meta_spec)
  apply simp
  done
*)

(* slow implementation of multi-substitution  *)
primrec msubstT :: "ty list \<Rightarrow> ty \<Rightarrow> ty" 
  where
   "msubstT [] e = e"
 | "msubstT (t#ts) e = msubstT ts (e[0 \<mapsto>\<^sub>\<tau> t]\<^sub>\<tau>)"

(* substitution where free variable indices are not decremented *) 
primrec msubstT_opt_aux :: "(nat \<Rightarrow> ty option) \<Rightarrow> ty \<Rightarrow> nat \<Rightarrow> ty"
  where
  "msubstT_opt_aux \<sigma> (TVar i) n = (if \<sigma> i \<noteq> None then shiftT n 0 (the (\<sigma> i)) else TVar i)"
| "msubstT_opt_aux \<sigma> (TPrim p) n = TPrim p"
| "msubstT_opt_aux \<sigma> (TCon tcon_id ty_args) n = TCon tcon_id (map (\<lambda>t. msubstT_opt_aux \<sigma> t n) ty_args)"

definition msubstT_opt :: "ty list \<Rightarrow> ty \<Rightarrow> ty"
  where
  "msubstT_opt ts \<tau> = msubstT_opt_aux (\<lambda>i. if i < length ts then Some (ts ! i) else None) \<tau> 0"

lemma msubstT_opt_empty: "msubstT_opt_aux Map.empty \<tau> n = \<tau>"
  by (induction \<tau>; simp add: map_idI)

lemma msubstT_opt_nil: "msubstT_opt [] \<tau> = \<tau>"
  by (simp add: msubstT_opt_def msubstT_opt_empty)
(*
lemma msubstT_msubstT_opt : "msubstT (map (shiftT (length ts) 0) ts) \<tau> =
       msubstT_opt \<tau> (\<lambda>i. if (i < length ts) then Some (ts ! i) else None) 0" 
  apply (induction ts)
   apply (simp add: msubstT_opt_nil)
  oops
*)

primrec msubst_ty_expr :: "ty list \<Rightarrow> expr \<Rightarrow> expr" 
  where
   "msubst_ty_expr [] e = e"
 | "msubst_ty_expr (t#ts) e = msubst_ty_expr ts (e[0 \<mapsto>\<^sub>\<tau> t])"


(*
lemma msubstT_msubstT: "msubstT ts2 (msubstT ts1 t) = msubstT (ts1@ts2) t"
  oops
*)

lemma msubstT_map_empty [simp]: "map (msubstT []) ts = ts"
  by (induction ts; auto)

lemma msubstT_tprim [simp]: "msubstT ts (TPrim p) = (TPrim p)"
  by (induction ts; auto)

lemma msubst_ty_map_empty [simp]: "map (msubst_ty_expr []) es = es"
  by (induction es; auto)

lemma msubst_ty_var [simp]: "msubst_ty_expr ts (Var i) = (Var i)"
  by (induction ts; auto)

lemma msubst_ty_lit [simp]: "msubst_ty_expr ts (Lit l) = (Lit l)"
  by (induction ts; auto)

lemma msubst_ty_unop [simp]: "msubst_ty_expr ts (UnOp uop e) = UnOp uop (msubst_ty_expr ts e)"
  by (induction ts arbitrary: e; auto)

lemma msubst_ty_binop [simp]: "msubst_ty_expr ts (e1 \<guillemotleft>bop\<guillemotright> e2) = (msubst_ty_expr ts e1) \<guillemotleft>bop\<guillemotright> (msubst_ty_expr ts e2)"
  by (induction ts arbitrary: e1 e2; auto)

lemma msubst_ty_funexp [simp]: 
"msubst_ty_expr ts (FunExp f ty_args args) = (FunExp f (map (msubstT ts) ty_args) (map (msubst_ty_expr ts) args))"
  by (induction ts arbitrary: ty_args args; auto)

lemma msubst_ty_forall [simp]:
"msubst_ty_expr ts (Forall ty e) = Forall (msubstT ts ty) (msubst_ty_expr ts e)"
  by (induction ts arbitrary:e ty; auto)

lemma msubst_ty_exists [simp]:
"msubst_ty_expr ts (Exists ty e) = Exists (msubstT ts ty) (msubst_ty_expr ts e)"
  by (induction ts arbitrary:e ty; auto)

lemma msubst_ty_forallT:
"msubst_ty_expr ts (ForallT e) = ForallT (fold (\<lambda> \<tau> e'. (e'[1 \<mapsto>\<^sub>\<tau> \<tau>])) ts e)"
  by (induction ts arbitrary: e; auto)

lemma msubst_ty_existsT:
"msubst_ty_expr ts (ExistsT e) = ExistsT (fold (\<lambda> \<tau> e'. (e'[1 \<mapsto>\<^sub>\<tau> \<tau>])) ts e)"
  by (induction ts arbitrary: e; auto)

end