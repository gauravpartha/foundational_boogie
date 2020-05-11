theory Binders
imports Lang
begin

fun vopen :: "nat \<Rightarrow> vname \<Rightarrow> expr \<Rightarrow> expr"
  where 
    "vopen k x (BVar i) = (if (i = k) then (Var x) else (BVar i))"
  | "vopen k x (Var y) = Var x"
  | "vopen k x (Val v) = Val v"
  | "vopen k x (UnOp uop e) = (UnOp uop (vopen k x e))"
  | "vopen k x (e1 \<guillemotleft>bop\<guillemotright> e2) = (vopen k x e1) \<guillemotleft>bop\<guillemotright> (vopen k x e2)"
  | "vopen k x (FunExp f es) = (FunExp f (map (vopen k x) es))"
  | "vopen k x (Forall ty e) = (Forall ty (vopen (k+1) x e))"

fun eopen :: "nat \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"
  where 
    "eopen k e' (BVar i) = (if (i = k) then e' else (BVar i))"
  | "eopen k e' (Var y) = Var y"
  | "eopen k e' (Val v) = Val v"
  | "eopen k e' (UnOp uop e) = (UnOp uop (eopen k e' e))"
  | "eopen k e' (e1 \<guillemotleft>bop\<guillemotright> e2) = (eopen k e' e1) \<guillemotleft>bop\<guillemotright> (eopen k e' e2)"
  | "eopen k e' (FunExp f es) = (FunExp f (map (eopen k e') es))"
  | "eopen k e' (Forall ty e) = (Forall ty (eopen (k+1) e' e))"

inductive lc :: "expr \<Rightarrow> bool" and
   lc_list :: "expr list \<Rightarrow> bool"
  where 
   "lc (Var y)"
 | "lc (Val v)"
 | "lc e \<Longrightarrow> lc (UnOp uop e)"
 | "\<lbrakk>lc e1; lc e2\<rbrakk> \<Longrightarrow> lc (e1 \<guillemotleft>bop\<guillemotright> e2)"
 | "lc_list es \<Longrightarrow> lc (FunExp f es)"
 | "\<lbrakk>\<And>x. x \<notin> L \<Longrightarrow>  lc (vopen 0 x e)\<rbrakk> \<Longrightarrow> lc (Forall ty e)"
 | "lc_list []"
 | "\<lbrakk>lc e; lc_list es\<rbrakk> \<Longrightarrow> lc_list (e#es)"

fun lc_at :: "nat \<Rightarrow> expr \<Rightarrow> bool" 
  where
   "lc_at k (Var y) = True"
 | "lc_at k (BVar i) = (i < k)"
 | "lc_at k (Val v) = True"
 | "lc_at k (UnOp uop e) = lc_at k e"
 | "lc_at k (e1 \<guillemotleft>bop\<guillemotright> e2) = (lc_at k e1 \<and> lc_at k e2)"
 | "lc_at k (FunExp f es) = list_all (lc_at k) es"
 | "lc_at k (Forall ty e) = lc_at (k+1) e"

fun fv :: "expr \<Rightarrow> vname set"
  where
    "fv (BVar i) = {}"
  | "fv (Var y) = {y}"
  | "fv (Val v) = {}"
  | "fv (UnOp up e) = fv e"
  | "fv (e1 \<guillemotleft>bop\<guillemotright> e2) = (fv e1) \<union> (fv e2)"
  | "fv (FunExp f es) = fold (union \<circ> fv) es {}"
  | "fv (Forall ty e) = fv e"

end