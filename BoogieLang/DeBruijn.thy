theory DeBruijn
imports Lang
begin

(* inspired by Vouillon's and Berghofer's POPLMark solutions *)

fun env_shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)"
  where "env_shift f = (\<lambda>m. f (m-1))"

primrec shiftT :: "nat \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> ty" 
where
  "shiftT n k (TVar i) = (if i < k then TVar i else TVar (i + n))"
| "shiftT n k (TPrim tp) = (TPrim tp)"
| "shiftT n k (TCon tcon_id ty_args) = (TCon tcon_id (map (shiftT n k) ty_args))"

primrec shift :: "nat \<Rightarrow> nat \<Rightarrow> expr \<Rightarrow> expr" ("\<up>")
where
  "\<up> n k (Var i) = (if i < k then Var i else Var (i + n))"
| "\<up> n k (Lit l) = (Lit l)"
| "\<up> n k (UnOp uop e) = UnOp uop (\<up> n k e)"
| "\<up> n k (e1 \<guillemotleft>bop\<guillemotright> e2) = (\<up> n k e1) \<guillemotleft>bop\<guillemotright> (\<up> n k e2)"
| "\<up> n k (FunExp f ty_args args) = FunExp f ty_args (map (\<up> n k) args)"
| "\<up> n k (Forall ty e) = (Forall ty (\<up> n (k+1) e))"
| "\<up> n k (Exists ty e) = (Exists ty (\<up> n (k+1) e))"
| "\<up> n k (ForallT e) = (ForallT (\<up> n k e))"
| "\<up> n k (ExistsT e) = (ExistsT (\<up> n k e))"

fun shiftEnv :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<rightharpoonup> ty) \<Rightarrow> (nat \<rightharpoonup> ty)"
  where "shiftEnv n k \<Delta> m = map_option (shiftT n k) (\<Delta> m)"

primrec shift_ty_term :: "nat \<Rightarrow> nat \<Rightarrow> expr \<Rightarrow> expr" ("\<up>\<^sub>\<tau>")
  where
  "\<up>\<^sub>\<tau> n k (Var i) = Var i"
| "\<up>\<^sub>\<tau> n k (Lit l) = (Lit l)"
| "\<up>\<^sub>\<tau> n k (UnOp uop e) = UnOp uop (\<up>\<^sub>\<tau> n k e)"
| "\<up>\<^sub>\<tau> n k (e1 \<guillemotleft>bop\<guillemotright> e2) = (\<up>\<^sub>\<tau> n k e1) \<guillemotleft>bop\<guillemotright> (\<up>\<^sub>\<tau> n k e2)"
| "\<up>\<^sub>\<tau> n k (FunExp f ty_args args) = FunExp f (map (shiftT n k) ty_args) (map (\<up>\<^sub>\<tau> n k) args)"
| "\<up>\<^sub>\<tau> n k (Forall ty e) = (Forall (shiftT n k ty) (\<up>\<^sub>\<tau> n k e))"
| "\<up>\<^sub>\<tau> n k (Exists ty e) = (Exists (shiftT n k ty) (\<up>\<^sub>\<tau> n k e))"
| "\<up>\<^sub>\<tau> n k (ForallT e) = (ForallT (\<up>\<^sub>\<tau> n (k+1) e))"
| "\<up>\<^sub>\<tau> n k (ExistsT e) = (ExistsT (\<up>\<^sub>\<tau> n (k+1) e))"

primrec substT :: "ty \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> ty"  ("_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>\<tau>" [300, 0, 0] 300)
  where
  "(TVar i)[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> = (if k < i then TVar (i - 1) else if i = k then shiftT k 0 S else TVar i)"
| "(TPrim p)[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> = TPrim p"
| "(TCon tcon_id ty_args)[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> = TCon tcon_id (map (\<lambda>t. t[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>) ty_args)"

(* can only use e[k \<mapsto>\<^sub>\<tau> S] if start by substituting bound variable 0, since it assumes that 
S must be shifted by k for e = (Var k) *)
primrec subst_ty_expr :: "expr \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> expr" ("_[_ \<mapsto>\<^sub>\<tau> _]" [300, 0, 0] 300)
  where
    "(Var i)[k \<mapsto>\<^sub>\<tau> S] = Var i"
  | "(Lit l)[k \<mapsto>\<^sub>\<tau> S] = (Lit l)"
  | "(UnOp uop e)[k \<mapsto>\<^sub>\<tau> S] = UnOp uop (e[k \<mapsto>\<^sub>\<tau> S])"
  | "(e1 \<guillemotleft>bop\<guillemotright> e2)[k \<mapsto>\<^sub>\<tau> S] = (e1[k \<mapsto>\<^sub>\<tau> S]) \<guillemotleft>bop\<guillemotright> (e2[k \<mapsto>\<^sub>\<tau> S])"
  | "(FunExp f ty_args args)[k \<mapsto>\<^sub>\<tau> S] = FunExp f (map (\<lambda>t. t[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>) ty_args) (map (\<lambda>e. e[k \<mapsto>\<^sub>\<tau> S]) args)"
  | "(Forall ty e)[k \<mapsto>\<^sub>\<tau> S] = (Forall (ty[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>) (e[k \<mapsto>\<^sub>\<tau> S]))"
  | "(Exists ty e)[k \<mapsto>\<^sub>\<tau> S] = (Exists (ty[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>) (e[k \<mapsto>\<^sub>\<tau> S]))"
  | "(ForallT e)[k \<mapsto>\<^sub>\<tau> S] = (ForallT (e[k+1 \<mapsto>\<^sub>\<tau> S]))"
  | "(ExistsT e)[k \<mapsto>\<^sub>\<tau> S] = (ExistsT (e[k+1 \<mapsto>\<^sub>\<tau> S]))"

(* slow implementation of multi-substitution  *)
primrec msubstT :: "ty list \<Rightarrow> ty \<Rightarrow> ty" 
  where
   "msubstT [] e = e"
 | "msubstT (t#ts) e = msubstT ts (e[0 \<mapsto>\<^sub>\<tau> t]\<^sub>\<tau>)"

primrec msubst_ty_expr :: "ty list \<Rightarrow> expr \<Rightarrow> expr" 
  where
   "msubst_ty_expr [] e = e"
 | "msubst_ty_expr (t#ts) e = msubst_ty_expr ts (e[0 \<mapsto>\<^sub>\<tau> t])"


(*
primrec subst :: "expr \<Rightarrow> nat \<Rightarrow> expr \<Rightarrow> expr" ("_[_ \<mapsto> _]" [300, 0, 0] 300)
  where
    "(Var i)[k \<mapsto> e] = (if k < i then Var (i-1) else if i = k then \<up> k 0 e else Var i)"
*)
end