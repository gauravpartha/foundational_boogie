theory VCHints
imports Main
begin

ML \<open>

datatype VcHint = 
  AssumeConjR of int |
  AssumeTrue |
  AssumeFalse |
  AssumeNot | 
  AssertConj | 
  AssertNoConj | 
  AssertSub |
  AssertTrue |
  AssertFalse
\<close>


end
