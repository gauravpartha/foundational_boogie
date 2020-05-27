theory VCHints
imports Main
begin

ML \<open>

datatype VcHint = 
  AssumeImplies | 
  AssumeConjR of int | 
  AssumeConj | 
  AssertConj | 
  AssertNoConj | 
  AssertSub
\<close>


end
