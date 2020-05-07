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

(*
fun fv :: "expr \<Rightarrow> vname set"
  where
    "fv (BVar i) = {}"
  | "fv (Var y) = {y}"
  | "fv (Val v) = {}"
  | "fv (UnOp up e) = fv e"
  | "fv (e1 \<guillemotleft>bop\<guillemotright> e2) = (fv e1) \<union> (fv e2)"
  | "fv (FunExp f es) = fold (union) {} es"
*)

end