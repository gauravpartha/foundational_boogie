theory CFG
imports Formal_SSA.Graph_path

begin

subsection \<open>CFG formalization\<close>

text \<open>We use the graph path library by Ullrich and Lohner (Verified Construction of 
      Static Single Assignment Form). 
      We re-define graph_Entry_base. Our CFGs do not require to record defs and uses.
      Instead, we require a mapping from nodes to basic blocks.
\<close>
  
locale CFG_base = graph_Entry_base \<alpha>e \<alpha>n invar inEdges' Entry
for
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry :: "'g \<Rightarrow> 'node" +
fixes "nodeToBlock" :: "'g \<Rightarrow> 'node \<rightharpoonup> 'block"

locale CFG = CFG_base \<alpha>e \<alpha>n invar inEdges' Entry "nodeToBlock"
+ graph_Entry \<alpha>e \<alpha>n invar inEdges' Entry
for
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry :: "'g \<Rightarrow> 'node" and
  "nodeToBlock" :: "'g \<Rightarrow> 'node \<rightharpoonup> 'block" +
assumes invar[intro!]: "invar g"
begin
  lemma Entry_no_predecessor[simp]: "predecessors g (Entry g) = []"
  using Entry_unreachable
  by (auto simp:predecessors_def)
end

end