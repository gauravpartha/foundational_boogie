theory wp_test
imports Semantics
begin

value "\<not>False"
value "False \<le> True"

fun wp_test:: "cmd  \<Rightarrow> (nstate \<Rightarrow> bool) \<Rightarrow> (nstate \<Rightarrow> bool)"
  where "wp_test (Assert e) P = P"


end