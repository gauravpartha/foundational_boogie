theory Lang
  imports Main
begin

type_synonym fname = string (* function name *)
type_synonym vname = nat (* variable name, de-bruijn index *)
type_synonym mname = string (* method name *)

datatype lit =  LBool bool  | LInt int

datatype binop = Eq | Neq | Add | Sub | Mul | Lt | Le | Gt | Ge | And | Or | Imp | Iff
datatype unop = Not | UMinus

datatype prim_ty 
 = TBool | TInt

type_synonym tcon_id = string (* type constructor id *)

datatype ty
  = TVar nat | (* type variables as de-bruijn indices *)
    TPrim prim_ty | (* primitive types *)
    TCon tcon_id "ty list" (* type constructor *)

primrec type_of_lit :: "lit \<Rightarrow> prim_ty"
  where 
    "type_of_lit (LBool _) = TBool"
  | "type_of_lit (LInt _)  = TInt"

datatype expr
  =
    Var vname
  | BVar nat (* de-bruijn index *)
  | Lit lit
  | UnOp unop "expr"
  | BinOp "(expr)" binop "(expr)" ("_ \<guillemotleft>_\<guillemotright> _" [80,0,81] 80) 
  | FunExp fname "ty list" "(expr list)" (* second argument: type instantiation *)
  | Old expr
(* value quantification *)
  | Forall ty expr
  | Exists ty expr
(* type quantification *)
  | ForallT expr 
  | ExistsT expr

datatype cmd
 = Assert expr
 | Assume expr
 | Assign vname expr
 | Havoc vname
 | MethodCall mname "expr list" "vname list"

(* function declarations: number of type parameters, argument types and return type *)
type_synonym fdecls = "(fname \<times> nat \<times> ty list \<times> ty) list"
(* variable declarations *)
(* type_synonym vdecls = "(vname \<times> ty) list" *)
type_synonym vdecls = "(vname \<times> ty) list"
(* type constructor declarations: number of arguments for each constructor *)
type_synonym tdecls = "(tcon_id \<times> nat) list"

(* basic blocks as a list of commands *)
type_synonym block = "cmd list"

(* identify nodes in the CFG by natural numbers *)
type_synonym node = "nat"

record mbodyCFG =
  entry :: "node"
  out_edges :: "(node list) list"
  node_to_block :: "block list"
 
(*for now just support method without return type and some body *)

(* number of type arguments, arguments, return values, modified global vars, pre- and postconditions, variable declarations,optional local vars + body *)
type_synonym msig = "nat \<times> vdecls \<times> vdecls \<times> vname list \<times> (expr list \<times> expr list) \<times> (vdecls \<times> mbodyCFG) option"
type_synonym mdecl = "mname \<times> msig"

fun get_pres :: "msig \<Rightarrow> expr list"
  where "get_pres (n_ty_params, var_params, var_rets, modifs, (pres,posts), body) = pres"

fun get_posts :: "msig \<Rightarrow> expr list"
  where "get_posts (n_ty_params, var_params, var_rets, modifs, (pres,posts), body) = posts"

fun get_params :: "msig \<Rightarrow> vdecls"
  where "get_params (n_ty_params, var_params, var_rets, modifs, spec, body) = var_params"

fun get_rets :: "msig \<Rightarrow> vdecls"
  where "get_rets (n_ty_params, var_params, var_rets, modifs, spec, body) = var_rets"

fun get_modifs :: "msig \<Rightarrow> vname list"
  where "get_modifs (n_ty_params, var_params, var_rets, modifs, (pres,posts), body) = modifs"

(* an axiom is a boolean expression that can refer to constants *)
type_synonym axiom = expr

(* type constructors, funtions, constants, global variables, axioms, methods *) 
datatype prog = Program "tdecls" "fdecls" "vdecls" "vdecls" "axiom list" "mdecl list"


primrec closed :: "ty \<Rightarrow> bool"
  where
    "closed (TVar i) = False"
  | "closed (TPrim prim_ty) = True"
  | "closed (TCon tcon_id ty_args) = list_all closed ty_args"

end