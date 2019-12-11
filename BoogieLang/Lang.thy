theory Lang
  imports Main
begin

type_synonym fname = string (* function name *)
type_synonym vname = string (*variable name *)

datatype val =  Bool bool  | Int int

datatype bop = Eq | Add | Le 
datatype unop = Not

datatype ty
  = Boolean |
    Integer

datatype expr
  = Var vname
  | Val val
  | BinOp "( expr)" bop "(expr)" ("_ \<guillemotleft>_\<guillemotright> _" [80,0,81] 80) 
  | FunExp fname "(expr list)"

datatype cmd
 = Assert expr
 | Assume expr
 | Seq expr expr ("_;;/ _"             [61,60]60)

end