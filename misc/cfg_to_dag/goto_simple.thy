theory goto_simple
imports Semantics Util
begin
locale vc
begin

definition vc_loopBody
  where
    "vc_loopBody i_1 n i_2 = (((i_1 < n) \<and> (i_2 = (i_1 + (1::int)))) \<longrightarrow> (i_2 > (0::int)))"
definition vc_afterLoop
  where
    "vc_afterLoop i_1 n = ((i_1 \<ge> n) \<longrightarrow> ((i_1 + (1::int)) > (1::int)))"
definition vc_loopHead
  where
    "vc_loopHead i_1 n i_2 = ((((1::int) \<le> i_1) \<and> (i_1 > (0::int))) \<longrightarrow> ((vc_loopBody i_1 n i_2) \<and> (vc_afterLoop i_1 n)))"
definition vc_anon0
  where
    "vc_anon0 k i_0 i_1 n i_2 = (((k \<ge> (0::int)) \<and> (i_0 = (k + (1::int)))) \<longrightarrow> ((i_0 > (0::int)) \<and> ((i_0 > (0::int)) \<longrightarrow> (vc_loopHead i_1 n i_2))))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry k i_0 i_1 n i_2 = (vc_anon0 k i_0 i_1 n i_2)"
lemma vc_correct:

shows "(vc_PreconditionGeneratedEntry k i_0 i_1 n i_2)"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def vc_loopHead_def vc_afterLoop_def vc_loopBody_def)
oops


end

locale vc_passive
begin

definition vc_loopBody
  where
    "vc_loopBody i_1 = (\<forall> n i_2. (((i_1 < n) \<and> (i_2 = (i_1 + (1::int)))) \<longrightarrow> (i_2 > (0::int))))"
definition vc_afterLoop
  where
    "vc_afterLoop i_1 = (\<forall> n. ((i_1 \<ge> n) \<longrightarrow> ((i_1 + (1::int)) > (1::int))))"
definition vc_loopHead
  where
    "vc_loopHead  = (\<forall> i_1. ((((1::int) \<le> i_1) \<and> (i_1 > (0::int))) \<longrightarrow> ((vc_loopBody i_1) \<and> (vc_afterLoop i_1))))"
definition vc_anon0
  where
    "vc_anon0  = (\<forall> k i_0. (((k \<ge> (0::int)) \<and> (i_0 = (k + (1::int)))) \<longrightarrow> ((i_0 > (0::int)) \<and> ((i_0 > (0::int)) \<longrightarrow> (vc_loopHead )))))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry  = (vc_anon0 )"
lemma vc_correct:

shows "(vc_PreconditionGeneratedEntry )"
apply (simp only: vc_PreconditionGeneratedEntry_def vc_anon0_def vc_loopHead_def vc_afterLoop_def vc_loopBody_def)
oops


end

locale beforePassive = 
fixes \<Lambda> :: "(var_context)" and \<Gamma> :: "(fun_context)"
assumes 
V0: "((\<Lambda> ''i'') = (Some TInt))" and 
V1: "((\<Lambda> ''n'') = (Some TInt))" and 
V2: "((\<Lambda> ''k'') = (Some TInt))"
begin

lemmas var_assms = V0 V1 V2
lemma block_GeneratedUnifiedExit:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')"
shows "(s' \<noteq> Failure)"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_loopBody:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''i'') Lt (Var ''n''))), 
(Assign [(''i'', (BinOp (Var ''i'') Add (Val (IntV 1))))]), 
(Assert (BinOp (Var ''i'') Gt (Val (IntV 0)))), 
(Assume (Val (BoolV False)))] (Normal n_s) s')" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"(vc_passive.vc_loopBody vc_i)"
shows "(s' = Magic)"
using assms 
apply cases
apply (simp only: vc_passive.vc_loopBody_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_afterLoop:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''i'') Ge (Var ''n''))), 
(Assert (BinOp (BinOp (Var ''i'') Add (Val (IntV 1))) Gt (Val (IntV 1))))] (Normal n_s) s')" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"(vc_passive.vc_afterLoop vc_i)"
shows "(s' \<noteq> Failure)"
using assms 
apply cases
apply (simp only: vc_passive.vc_afterLoop_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_loopHead:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Havoc ''i''), 
(Assume (BinOp (Val (IntV 1)) Le (Var ''i''))), 
(Assume (BinOp (Var ''i'') Gt (Val (IntV 0))))] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"(vc_passive.vc_loopHead )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_i vc_n. ((((n_s' ''i'') = (Some (IntV vc_i))) \<and> ((n_s' ''n'') = (Some (IntV vc_n)))) \<and> ((vc_passive.vc_loopBody vc_i) \<and> (vc_passive.vc_afterLoop vc_i)))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_loopHead_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_anon0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [(Assume (BinOp (Var ''k'') Ge (Val (IntV 0)))), 
(Assign [(''i'', (BinOp (Var ''k'') Add (Val (IntV 1))))]), 
(Assert (BinOp (Var ''i'') Gt (Val (IntV 0))))] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''k'') = (Some (IntV vc_k)))" and 
"(vc_passive.vc_anon0 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_n. (((n_s' ''n'') = (Some (IntV vc_n))) \<and> (vc_passive.vc_loopHead ))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon0_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''k'') = (Some (IntV vc_k)))" and 
"(vc_passive.vc_anon0 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_n vc_k. ((((n_s' ''n'') = (Some (IntV vc_n))) \<and> ((n_s' ''k'') = (Some (IntV vc_k)))) \<and> (vc_passive.vc_anon0 ))))))"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"((n_s ''k'') = (Some (IntV vc_k)))" and 
"(vc_passive.vc_PreconditionGeneratedEntry )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_n vc_k. ((((n_s' ''n'') = (Some (IntV vc_n))) \<and> ((n_s' ''k'') = (Some (IntV vc_k)))) \<and> (vc_passive.vc_anon0 ))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_PreconditionGeneratedEntry_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)


fun outEdges_goto_simple
  where
    "outEdges_goto_simple (Suc(Suc(Suc(0)))) = {(Suc(0))}"
    |"outEdges_goto_simple (Suc(Suc(0))) = {}"
    |"outEdges_goto_simple (Suc(0)) = {(Suc(Suc(Suc(0)))), (Suc(Suc(0)))}"
    |"outEdges_goto_simple (0) = {(Suc(0))}"
    |"outEdges_goto_simple _ = {}"
fun nodeToBlocks_goto_simple
  where
    "nodeToBlocks_goto_simple (Suc(Suc(Suc(0)))) = (Some [(Assume (BinOp (Var ''i'') Lt (Var ''n''))), 
(Assign [(''i'', (BinOp (Var ''i'') Add (Val (IntV 1))))]), 
(Assert (BinOp (Var ''i'') Gt (Val (IntV 0)))), 
(Assume (Val (BoolV False)))])"
    |"nodeToBlocks_goto_simple (Suc(Suc(0))) = (Some [(Assume (BinOp (Var ''i'') Ge (Var ''n''))), 
(Assert (BinOp (BinOp (Var ''i'') Add (Val (IntV 1))) Gt (Val (IntV 1))))])"
    |"nodeToBlocks_goto_simple (Suc(0)) = (Some [(Assume (BinOp (Val (IntV 1)) Le (Var ''i''))), 
(Assume (BinOp (Var ''i'') Gt (Val (IntV 0))))])"
    |"nodeToBlocks_goto_simple (0) = (Some [(Assume (BinOp (Var ''k'') Ge (Val (IntV 0)))), 
(Assign [(''i'', (BinOp (Var ''k'') Add (Val (IntV 1))))]), 
(Assert (BinOp (Var ''i'') Gt (Val (IntV 0))))])"
    |"nodeToBlocks_goto_simple _ = (None )"
fun funDecl_goto_simple
  where
    "funDecl_goto_simple _ = (None )"
fun inParams_goto_simple
  where
    "inParams_goto_simple ''n'' = (Some TInt)"
    |"inParams_goto_simple ''k'' = (Some TInt)"
    |"inParams_goto_simple _ = (None )"
fun localVars_goto_simple
  where
    "localVars_goto_simple ''i'' = (Some TInt)"
  |"localVars_goto_simple _ = (None )"

definition G 
  where "G \<equiv>
(|entry = 0, nodes = {(Suc(Suc(Suc(0)))), (Suc(Suc(0))), (Suc(0)), (0)},
 out_edges = outEdges_goto_simple, node_to_block = nodeToBlocks_goto_simple|)"

definition ProgramM
  where
    "ProgramM  = (Program funDecl_goto_simple [(''goto_simple'', inParams_goto_simple, localVars_goto_simple, G)])"

(* loop head *)
abbreviation LH where "LH \<equiv> Suc 0"
(* loop body *)
abbreviation LB where "LB \<equiv> Suc(Suc(Suc(0)))"
(* after loop *)
abbreviation AL where "AL \<equiv> Suc(Suc(0))"

lemma afterLoop_correct: 
  assumes A1:"\<Lambda>, \<Gamma>, G \<turnstile> (Inl AL, Normal n_s) -n\<rightarrow>* (m, s')" and
   A2:"((n_s ''i'') = (Some (IntV vc_i)))" and 
   A3:"((n_s ''n'') = (Some (IntV vc_n)))" and 
   A4: "(vc_passive.vc_afterLoop vc_i)"
  shows "s' \<noteq> Failure"
  using A1
proof (cases rule: converse_rtranclpE)
  case base
  then show ?thesis by auto
next
  case (step y)
  assume "\<Lambda>,\<Gamma>,G \<turnstile> y -n\<rightarrow>* (m, s')"
  assume "\<Lambda>,\<Gamma>,G \<turnstile> (Inl AL, Normal n_s) -n\<rightarrow> y"
  then show ?thesis
  proof (cases)
    case (RedNode cs s' n')
    assume "n' \<in> out_edges G AL"
    thus ?thesis by (auto simp add: G_def)
  next
    case (RedReturn cs s'')
    assume "node_to_block G AL = Some cs"
    moreover assume "\<Lambda>,\<Gamma> \<turnstile> \<langle>cs,Normal n_s\<rangle> [\<rightarrow>] s''"
    ultimately have B1:"\<Lambda>,\<Gamma> \<turnstile> \<langle>[(Assume (BinOp (Var ''i'') Ge (Var ''n''))), 
(Assert (BinOp (BinOp (Var ''i'') Add (Val (IntV 1))) Gt (Val (IntV 1))))],Normal n_s\<rangle> [\<rightarrow>] s''"
      by (simp add: G_def)
    then have "s'' \<noteq> Failure" using A2 A3 A4
      by (rule block_afterLoop)
    with \<open>y = (Inr (), s'')\<close> \<open>\<Lambda>,\<Gamma>,G \<turnstile> y -n\<rightarrow>* (m, s')\<close> show ?thesis using finished_remains
      by blast
  qed
qed


(*Goal*)
lemma loopHead_correct:
  assumes 
   "\<Lambda>, \<Gamma>, G \<turnstile> (Inl LH, Normal n_s) -n\<rightarrow>* (m, s')" and 
   "((n_s ''i'') = (Some (IntV vc_i)))" and 
   "((n_s ''n'') = (Some (IntV vc_n)))" and
   "((n_s ''k'') = (Some (IntV vc_k)))" and
   "vc_passive.vc_loopHead"
 shows "s' \<noteq> Failure"
  oops


lemma cfg_ind: 
  assumes A1:"\<Lambda>, \<Gamma>, G \<turnstile> (m, s) -n\<rightarrow>* (m', s')" and "vc"
  shows "\<And> ns' ns''. \<lbrakk>(\<Lambda>, \<Gamma>, G \<turnstile> (m, s) -n\<rightarrow>* (Inl h, Normal ns'')); s = (Normal ns');
                       ns' ''x'' = Some (IntV vc_x);
                       \<Gamma> \<turnstile> \<langle>e_inv, ns'\<rangle> \<Down> BoolV True; 
                           (\<Lambda>, \<Gamma>, G \<turnstile> (Inl h, Normal ns'') -n\<rightarrow>* (m',s'))\<rbrakk> \<Longrightarrow>
                       s' \<noteq> Failure"
  oops

(* Prover stronger lemma *)
lemma loopHead_aux:
  assumes 
   Ared:"\<Lambda>, \<Gamma>, G \<turnstile> (m, s) -n\<rightarrow>* (m', s')" and 
   An:"((n_s ''n'') = (Some (IntV vc_n)))" and
   Ak:"((n_s ''k'') = (Some (IntV vc_k)))" and
   "vc_passive.vc_loopHead" and
   Inv_holds:"\<Gamma> \<turnstile> \<langle>BinOp (Val (IntV 1)) Le (Var ''i''), n_s\<rangle> \<Down> BoolV (True)"
  shows "\<And> ns' ns''. \<lbrakk>(\<Lambda>, \<Gamma>, G \<turnstile> (m, s) -n\<rightarrow>* (Inl 1, Normal ns'')); s = (Normal ns');
                       ns' ''x'' = Some (IntV vc_x);
                       \<Gamma> \<turnstile> \<langle>e_inv, ns'\<rangle> \<Down> BoolV True; 
                           (\<Lambda>, \<Gamma>, G \<turnstile> (Inl h, Normal ns'') -n\<rightarrow>* (m',s'))\<rbrakk> \<Longrightarrow>
                       s' \<noteq> Failure"
  using Ared                 

(* Prove stronger lemma *)
lemma loopHead_aux:
  assumes 
   Ared:"\<Lambda>, \<Gamma>, G \<turnstile> (m, s) -n\<rightarrow>* (m', s')" and 
   An:"((n_s ''n'') = (Some (IntV vc_n)))" and
   Ak:"((n_s ''k'') = (Some (IntV vc_k)))" and
   "vc_passive.vc_loopHead" and
   Inv_holds:"\<Gamma> \<turnstile> \<langle>BinOp (Val (IntV 1)) Le (Var ''i''), n_s\<rangle> \<Down> BoolV (True)"
  shows "\<And> ns' ns''. \<lbrakk>(\<Lambda>, \<Gamma>, G \<turnstile> (m, s) -n\<rightarrow>* (Inl 1, Normal ns'')); s = (Normal ns');
                       ns' ''x'' = Some (IntV vc_x);
                       \<Gamma> \<turnstile> \<langle>e_inv, ns'\<rangle> \<Down> BoolV True; 
                           (\<Lambda>, \<Gamma>, G \<turnstile> (Inl h, Normal ns'') -n\<rightarrow>* (m',s'))\<rbrakk> \<Longrightarrow>
                       s' \<noteq> Failure"
  using Ared                 



lemma loopBody_aux:
  assumes 
  "\<Lambda>, \<Gamma>, G \<turnstile> (Inl 3, Normal n_s) -n\<rightarrow> (m'', s'')" and
  "\<Lambda>, \<Gamma>, G \<turnstile> (m'', s'') -n\<rightarrow>* (m', s')" and 
  "((n_s ''n'') = (Some (IntV vc_n)))" and
  "((n_s ''k'') = (Some (IntV vc_k)))" and
  IH:"
  \<And>n_s'. m'' = Inl 1 \<Longrightarrow> 
   \<Gamma> \<turnstile> \<langle>BinOp (Val (IntV 1)) Le (Var ''i''), n_s'\<rangle> \<Down> BoolV (True) \<Longrightarrow>
   ((n_s' ''n'') = (Some (IntV vc_n))) \<Longrightarrow>
   ((n_s' ''k'') = (Some (IntV vc_k))) \<Longrightarrow> 
   s' \<noteq> Failure"
shows "s' \<noteq> Failure"
  oops

end


end
