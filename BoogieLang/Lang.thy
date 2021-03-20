section \<open>Syntax of the Boogie language\<close>

theory Lang
  imports Main
begin

type_synonym fname = string (* function name *)
type_synonym vname = nat (* variable name, de-bruijn index *)
type_synonym pname = string (* procedure name *)

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

(* multi-assign and multi-havoc not supported for now *)
datatype cmd
 = Assert expr
 | Assume expr
 | Assign vname expr
 | Havoc vname
 | ProcCall pname "expr list" "vname list"

text \<open>Function declarations: number of type parameters, argument types and return type\<close>
type_synonym fdecl = "(fname \<times> nat \<times> ty list \<times> ty)"
type_synonym fdecls = "fdecl list"

text \<open>Variable declarations: the optional expression represents the where-clause\<close>
type_synonym vdecl = "vname \<times> ty \<times> (expr option)"
type_synonym vdecls = "vdecl list"

text \<open>Type constructor declarations: number of arguments for each constructor\<close>
type_synonym tdecls = "(tcon_id \<times> nat) list"

text \<open>Basic blocks as a list of commands\<close>
type_synonym block = "cmd list"

(* identify nodes in the CFG by natural numbers *)
type_synonym node = "nat"

record mbodyCFG =
  entry :: "node"
  out_edges :: "(node list) list"
  node_to_block :: "block list"
 

text \<open>Procedure pre- and postconditions contain a boolean to indicate whether they are free (true) or checked (false).\<close>
record procedure =
  proc_ty_args :: nat
  proc_args :: vdecls
  proc_rets :: vdecls
  proc_modifs :: "vname list"
  proc_pres :: "(expr \<times> bool) list" 
  proc_posts :: "(expr \<times> bool) list"
  proc_body :: "(vdecls \<times> mbodyCFG) option"

fun proc_checked_pres :: "procedure \<Rightarrow> expr list"
  where "proc_checked_pres p = map fst (filter (\<lambda>x. \<not> snd(x)) (proc_pres p))"

fun proc_free_pres :: "procedure \<Rightarrow> expr list"
  where "proc_free_pres p = map fst (filter (\<lambda>x. snd(x)) (proc_pres p))"

fun proc_all_pres :: "procedure \<Rightarrow> expr list"
  where "proc_all_pres p = map fst (proc_pres p)"

fun proc_checked_posts :: "procedure \<Rightarrow> expr list"
  where "proc_checked_posts p = map fst (filter (\<lambda>x. \<not> snd(x)) (proc_posts p))"

fun proc_all_posts :: "procedure \<Rightarrow> expr list"
  where "proc_all_posts p = map fst (proc_posts p)"

fun proc_free_posts :: "procedure \<Rightarrow> expr list"
  where "proc_free_posts p = map fst (filter (\<lambda>x. snd(x)) (proc_posts p))"

type_synonym pdecl = "pname \<times> procedure"

(* an axiom is a boolean expression that can refer to constants *)
type_synonym axiom = expr

record prog =
  prog_ty_constr :: tdecls 
  prog_funcs :: fdecls
  prog_consts :: vdecls
  prog_globals :: vdecls
  prog_axioms :: "axiom list"
  prog_procs :: "pdecl list"

primrec closed :: "ty \<Rightarrow> bool"
  where
    "closed (TVar i) = False"
  | "closed (TPrim prim_ty) = True"
  | "closed (TCon tcon_id ty_args) = list_all closed ty_args"

end