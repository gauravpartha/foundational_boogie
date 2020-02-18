theory Lang
  imports Main
begin

type_synonym fname = string (* function name *)
type_synonym vname = string (* variable name *)
type_synonym mname = string (* method name *)

datatype val =  BoolV bool  | IntV int

datatype binop = Eq | Add | Sub | Mul | Lt | Le | Gt | Ge | And 
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
  | Val val
  | UnOp unop "expr"
  | BinOp "(expr)" binop "(expr)" ("_ \<guillemotleft>_\<guillemotright> _" [80,0,81] 80) 
  | FunExp fname "(expr list)"

datatype cmd
 = Assert expr
 | Assume expr

type_synonym fdecl = "fname \<times> ty list \<times> ty"
type_synonym vdecl = "vname \<times> ty"

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
type_synonym mdecl = "mname \<times> vdecl list \<times> vdecl list \<times> mbodyCFG"

(*for now just support a single method and no axioms*)
datatype prog = Program "fdecl list" "mdecl list"

end