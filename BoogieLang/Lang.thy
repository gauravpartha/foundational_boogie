theory Lang
  imports Main
begin

type_synonym fname = string (* function name *)
type_synonym vname = nat (* variable name, de-bruijn index *)
type_synonym mname = string (* method name *)

datatype lit =  LBool bool  | LInt int

datatype binop = Eq | Neq | Add | Sub | Mul | Lt | Le | Gt | Ge | And | Or | Imp
datatype unop = Not | UMinus

datatype prim_ty 
 = TBool | TInt

type_synonym tcon_id = string (* type constructor id *)

datatype ty
  = TPrim prim_ty | TCon tcon_id "ty list"

primrec type_of_lit :: "lit \<Rightarrow> prim_ty"
  where 
    "type_of_lit (LBool _) = TBool"
  | "type_of_lit (LInt _)  = TInt"

datatype expr
  = Var vname
  | Lit lit
  | UnOp unop "expr"
  | BinOp "(expr)" binop "(expr)" ("_ \<guillemotleft>_\<guillemotright> _" [80,0,81] 80) 
  | FunExp fname "(expr list)"
  | Forall ty expr
  | Exists ty expr

datatype cmd
 = Assert expr
 | Assume expr
 | Assign "(vname \<times> expr) list" 
 | Havoc vname

(* function declarations: argument types and return type *)
type_synonym fdecls = "(fname \<times> ty list \<times> ty) list"
(* variable declarations *)
type_synonym vdecls = "(vname \<times> ty) list"
(* type constructor declarations: number of arguments for each constructor *)
type_synonym tdecls = "(tcon_id \<times> nat) list"

(* basic blocks as a list of commands *)
type_synonym block = "cmd list"

(* identify nodes in the CFG by natural numbers *)
type_synonym node = "nat"

record mbodyCFG = 
  entry :: "node"
  nodes :: "node set"
  out_edges :: "node \<Rightarrow> node set"
  node_to_block :: "node \<rightharpoonup> block"
 
(*for now just support method without return type and some body *)

(* method name, arguments, variable declarations, body *)
type_synonym mdecl = "mname \<times> vdecls \<times> vdecls \<times> mbodyCFG"

(* an axiom is a boolean expression that can refer to constants *)
type_synonym axiom = expr

(* type constructors, funtions, constants, global variables, axioms, methods *) 
datatype prog = Program "tdecls" "fdecls" "vdecls" "vdecls" "axiom list" "mdecl list"

end