theory Lang
  imports Main
begin

type_synonym fname = string (* function name *)
type_synonym vname = string (* variable name *)
type_synonym mname = string (* method name *)

datatype val =  BoolV bool  | IntV int

datatype binop = Eq | Add | Sub | Mul | Lt | Le | Gt | Ge | And | Or | Imp
datatype unop = Not

datatype ty
  = TBool |
    TInt

primrec type_of_val :: "val \<Rightarrow> ty"
  where 
    "type_of_val (BoolV _) = TBool"
  | "type_of_val (IntV _)  = TInt"

datatype expr
  = Var vname
  | BVar nat
  | Val val
  | UnOp unop "expr"
  | BinOp "(expr)" binop "(expr)" ("_ \<guillemotleft>_\<guillemotright> _" [80,0,81] 80) 
  | FunExp fname "(expr list)"
  | Forall ty expr

datatype cmd
 = Assert expr
 | Assume expr
 | Assign "(vname \<times> expr) list" 
 | Havoc vname

type_synonym fdecls = "fname \<rightharpoonup> ty list \<times> ty"
type_synonym vdecls = "vname \<rightharpoonup> ty"

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

(*for now just support a single method and no axioms*)
datatype prog = Program "fdecls" "mdecl list"

end