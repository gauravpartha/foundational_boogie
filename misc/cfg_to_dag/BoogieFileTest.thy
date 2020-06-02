theory BoogieFileTest
  imports Lang
begin

fun out_edges_1 
  where
   "out_edges_1 0 = {1,2}"
 | "out_edges_1 (Suc 0) = {3,4}"
 | "out_edges_1 _ = {}"

fun outEdges_m
  where
   "outEdges_m 0 = {Suc(0)}"
 | "outEdges_m (Suc(0)) = {}"
 | "outEdges_m _ = {}"

(*
fun outEdges_m
  where
    "outEdges_m 0 = {Suc(0)}"
    |"outEdges_m Suc(0) = {}"
    |"outEdges_m _ = {}"
*)

fun node_to_block_1 
  where
    "node_to_block_1 0 = Some [Assert (Val (BoolV True))]"
  | "node_to_block_1 (Suc 0) = Some [Assume (Val (BoolV True))]"
  | "node_to_block_1 _ = None"

lemma "1 \<in> out_edges_1 0"
  by simp

definition test :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "test x y = y"

locale smttest =
  fixes x :: int and y :: int and f :: "int \<Rightarrow> int"

context smttest
begin

definition block1
  where "block1 = (10 \<le> y \<and> f x \<le> 5 \<longrightarrow> f x + 4 \<le> y)"

definition block0
  where "block0 = (True \<longrightarrow> block1)"

lemma h: block0
  apply (simp only: block0_def)
  apply (rule)
  apply (simp only: block1_def)
  apply (rule)
  apply auto

end
  

lemma testlemma: "let x = 4 in x > 4"

(*
record mbodyCFG = 
  entry :: "node"
  nodes :: "node set"
  out_edges :: "node \<Rightarrow> node set"
  node_to_block :: "node \<rightharpoonup> block"
*)

definition someMethodCFG :: mbodyCFG 
  where "someMethodCFG = (| entry = 1, nodes = {1,2,3,4}, out_edges = out_edges_1, node_to_block = node_to_block_1 |)"

typ mdecl

definition someMethod :: mdecl 
  where "someMethod = (''m'', [], [], someMethodCFG)"

definition someBinOp :: expr
  where "someBinOp = ((BinOp (Val (IntV 0))) Eq) (Val (IntV 0))"

end
