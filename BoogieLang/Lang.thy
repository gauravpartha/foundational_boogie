theory Lang
  imports Main CFG
begin

type_synonym fname = string (* function name *)
type_synonym vname = string (* variable name *)
type_synonym mname = string (* method name *)

datatype val =  BoolV bool  | IntV int

datatype binop = Eq | Add | Le | And
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
  | BinOp "(expr)" binop "(expr)" ("_ \<guillemotleft>_\<guillemotright> _" [80,0,81] 80) 
  | FunExp fname "(expr list)"

datatype cmd
 = Assert expr
 | Assume expr
 (* 
   More simple to work with lists of commands than Seq, since need not deal with nesting.
   | Seq expr expr ("_;;/ _"             [61,60]60) *)

type_synonym fdecl = "fname \<times> ty list \<times> ty"
type_synonym vdecl = "vname \<times> ty"

(*for now just support method without return type and some body *)
(* method name, argument types, variable declarations, body *)
type_synonym 'm mdecl = "mname \<times> ty list \<times> vname list \<times> 'm" 


(*for now just support a single method and no axioms*)
datatype 'm prog = Program "fdecl list" "'m mdecl"

(* basic blocks as a list of commands *)
type_synonym block = "cmd list"

(* identify nodes in the CFG by natural numbers *)
type_synonym node = "nat"
(* every edge is the same *)
type_synonym edge_kind = "unit"

(*
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry :: "'g \<Rightarrow> 'node"
  nodeToBlock" :: "'g \<Rightarrow> 'node \<rightharpoonup> 'block
*)
(*
  gen_\<alpha>e :: "('node, 'edge) edge set"
  gen_\<alpha>n :: "'node list"
  gen_inEdges :: "'node \<Rightarrow> ('node, 'edge) edge list"
  gen_Entry :: "'node"
*)

(* args :: "(vname \<times> ty) list" *)
record gen_methodCFG = 
  gen_nodes :: "node list"
  gen_edges :: "(node, edge_kind) edge set"
  gen_inEdges :: "node \<Rightarrow> (node, edge_kind) edge list"
  get_outEdges :: "node \<Rightarrow> (node
  gen_entry :: "node"
  gen_nodeToBlock :: "node \<rightharpoonup> block"
  
  

end