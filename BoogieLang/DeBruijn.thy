theory DeBruijn
imports Main
begin

fun shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)"
  where "shift f = (\<lambda>m. f (m-1))" 

end