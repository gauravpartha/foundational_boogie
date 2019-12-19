theory Lang
  imports Main
begin

type_synonym fname = string (* function name *)
type_synonym vname = string (* variable name *)
type_synonym mname = string (* method name *)

datatype val =  Bool bool  | Intg int

datatype binop = Eq | Add | Le | And
datatype unop = Not

datatype ty
  = Boolean |
    Integer

type_synonym fdecl = "fname \<times> ty list \<times> ty"
(*for now just support method without return type and some body *)
type_synonym 'm mdecl = "mname \<times> ty list \<times> 'm" 

(*for now just support a single method and no axioms*)
datatype 'm prog = Program "fdecl list" "'m mdecl" 

datatype expr
  = Var vname
  | Val val
  | BinOp "(expr)" binop "(expr)" ("_ \<guillemotleft>_\<guillemotright> _" [80,0,81] 80) 
  | FunExp fname "(expr list)"

datatype cmd
 = Assert expr
 | Assume expr
 | Seq expr expr ("_;;/ _"             [61,60]60) 

end