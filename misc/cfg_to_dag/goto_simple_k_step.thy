theory goto_simple_k_step
imports Semantics Util
begin
locale vc
begin

definition vc_loopBody
  where
    "vc_loopBody i_1 n i_2 k = (((i_1 < n) \<and> (i_2 = (i_1 + k))) \<longrightarrow> (i_2 > (0::int)))"
definition vc_afterLoop
  where
    "vc_afterLoop i_1 n = ((i_1 \<ge> n) \<longrightarrow> ((i_1 + (1::int)) > (1::int)))"
definition vc_loopHead
  where
    "vc_loopHead i_1 n i_2 k = ((i_1 > (0::int)) \<longrightarrow> ((vc_loopBody i_1 n i_2 k) \<and> (vc_afterLoop i_1 n)))"
definition vc_anon0
  where
    "vc_anon0 k i_0 i_1 n i_2 = (((k \<ge> (0::int)) \<and> (i_0 = (k + (1::int)))) \<longrightarrow> ((i_0 > (0::int)) \<and> ((i_0 > (0::int)) \<longrightarrow> (vc_loopHead i_1 n i_2 k))))"
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
    "vc_loopBody i_1 k = (\<forall> n i_2. (((i_1 < n) \<and> (i_2 = (i_1 + k))) \<longrightarrow> (i_2 > (0::int))))"
definition vc_afterLoop
  where
    "vc_afterLoop i_1 = (\<forall> n. ((i_1 \<ge> n) \<longrightarrow> ((i_1 + (1::int)) > (1::int))))"
definition vc_loopHead
  where
    "vc_loopHead k = (\<forall> i_1. ((i_1 > (0::int)) \<longrightarrow> ((vc_loopBody i_1 k) \<and> (vc_afterLoop i_1))))"
definition vc_anon0
  where
    "vc_anon0  = (\<forall> k i_0. (((k \<ge> (0::int)) \<and> (i_0 = (k + (1::int)))) \<longrightarrow> ((i_0 > (0::int)) \<and> ((i_0 > (0::int)) \<longrightarrow> (vc_loopHead k)))))"
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
(Assign [(''i'', (BinOp (Var ''i'') Add (Var ''k'')))]), 
(Assert (BinOp (Var ''i'') Gt (Val (IntV 0)))), 
(Assume (Val (BoolV False)))] (Normal n_s) s')" and 
"((n_s ''i'') = (Some (IntV vc_i)))" and 
"((n_s ''k'') = (Some (IntV vc_k)))" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"(vc_passive.vc_loopBody vc_i vc_k)"
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
(Assume (BinOp (Var ''i'') Gt (Val (IntV 0))))] (Normal n_s) s')" and 
"((n_s ''k'') = (Some (IntV vc_k)))" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"(vc_passive.vc_loopHead vc_k)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_i vc_k vc_n. (((((n_s' ''i'') = (Some (IntV vc_i))) \<and> ((n_s' ''k'') = (Some (IntV vc_k)))) \<and> ((n_s' ''n'') = (Some (IntV vc_n)))) \<and> ((vc_passive.vc_loopBody vc_i vc_k) \<and> (vc_passive.vc_afterLoop vc_i)))))))"
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
"((n_s ''k'') = (Some (IntV vc_k)))" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"(vc_passive.vc_anon0 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_k vc_n. ((((n_s' ''k'') = (Some (IntV vc_k))) \<and> ((n_s' ''n'') = (Some (IntV vc_n)))) \<and> (vc_passive.vc_loopHead vc_k))))))"
using assms 
apply cases
apply (simp only: vc_passive.vc_anon0_def)
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_0:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''k'') = (Some (IntV vc_k)))" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"(vc_passive.vc_anon0 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_k vc_n. ((((n_s' ''k'') = (Some (IntV vc_k))) \<and> ((n_s' ''n'') = (Some (IntV vc_n)))) \<and> (vc_passive.vc_anon0 ))))))"
using assms 
apply cases
apply (handle_cmd_list_full v_assms: var_assms)?
by (auto?)

lemma block_PreconditionGeneratedEntry:
assumes 
"(red_cmd_list \<Lambda> \<Gamma> [] (Normal n_s) s')" and 
"((n_s ''k'') = (Some (IntV vc_k)))" and 
"((n_s ''n'') = (Some (IntV vc_n)))" and 
"(vc_passive.vc_PreconditionGeneratedEntry )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (\<exists> vc_k vc_n. ((((n_s' ''k'') = (Some (IntV vc_k))) \<and> ((n_s' ''n'') = (Some (IntV vc_n)))) \<and> (vc_passive.vc_anon0 ))))))"
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
(Assign [(''i'', (BinOp (Var ''i'') Add (Var ''k'')))])])"
    |"nodeToBlocks_goto_simple (Suc(Suc(0))) = (Some [(Assume (BinOp (Var ''i'') Ge (Var ''n''))), 
(Assert (BinOp (BinOp (Var ''i'') Add (Val (IntV 1))) Gt (Val (IntV 1))))])"
    |"nodeToBlocks_goto_simple (Suc(0)) = (Some [(Assert (BinOp (Var ''i'') Gt (Val (IntV 0))))])"
    |"nodeToBlocks_goto_simple (0) = (Some [(Assume (BinOp (Var ''k'') Ge (Val (IntV 0)))), 
(Assign [(''i'', (BinOp (Var ''k'') Add (Val (IntV 1))))])])"
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

definition G where "G \<equiv> (|entry = 0, nodes = {(Suc(Suc(Suc(0)))), (Suc(Suc(0))), (Suc(0)), (0)}, out_edges = outEdges_goto_simple, node_to_block = nodeToBlocks_goto_simple|)"

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
 
lemma loopBody_correct:
  assumes 
  "\<Lambda>, \<Gamma>, G \<turnstile> (Inl LB, Normal n_s) -n\<rightarrow>^j (m', s')" and
  "((n_s ''n'') = (Some (IntV vc_n)))" and
  "((n_s ''k'') = (Some (IntV vc_k)))" and
  "((n_s ''i'') = Some (IntV vc_i))" and
  "vc_passive.vc_loopBody vc_i vc_k" and
  IH:"\<And>k' ns2 vc_i'. k' \<le> j \<Longrightarrow>
    \<Lambda>,\<Gamma>,G \<turnstile>(Inl LH, Normal ns2) -n\<rightarrow>^k' (m', s') \<Longrightarrow>
    ns2 ''n'' = Some (IntV vc_n) \<Longrightarrow> 
    ((ns2 ''k'') = (Some (IntV vc_k))) \<Longrightarrow>
    ns2 ''i'' = Some (IntV vc_i') \<Longrightarrow>
    \<Gamma> \<turnstile> \<langle>Var ''i'' \<guillemotleft>Gt\<guillemotright> (Val (IntV 0)), ns2\<rangle> \<Down> BoolV True \<Longrightarrow> s' \<noteq> Failure"
shows "s' \<noteq> Failure"
  using assms
proof (cases rule: relpowp_E2_2, simp)
  assume "(Inl LB, Normal n_s) = (m', s')"
  thus ?thesis by auto
next
  fix m'' s'' j2 jpred
  assume "j = Suc jpred"
  assume Apred:"\<Lambda>,\<Gamma>,G \<turnstile> (m'', s'') -n\<rightarrow>^jpred (m', s')"
  assume "\<Lambda>,\<Gamma>,G \<turnstile> (Inl LB, Normal n_s) -n\<rightarrow> (m'', s'')"
  thus ?thesis
  proof (cases)
    case (RedNode cs n')
    from local.RedNode have "\<Lambda>,\<Gamma> \<turnstile> \<langle>[(Assume (BinOp (Var ''i'') Lt (Var ''n''))), 
(Assign [(''i'', (BinOp (Var ''i'') Add (Var ''k'')))])], Normal n_s\<rangle> [\<rightarrow>]  s''" using G_def
      by (metis nodeToBlocks_goto_simple.simps(1) option.inject select_convs(4))
    then have
    "s'' \<noteq> Failure \<and> (\<forall>n_s''. s'' = Normal n_s'' \<longrightarrow> 
                                     n_s'' ''n'' = Some (IntV vc_n) \<and> n_s'' ''k'' = Some (IntV vc_k) \<and>
                                     (\<exists> vc_i'. n_s'' ''i'' = Some (IntV vc_i')) \<and>
                                     \<Gamma> \<turnstile> \<langle>Var ''i'' \<guillemotleft>Gt\<guillemotright> (Val (IntV 0)), n_s''\<rangle> \<Down> BoolV True)"
      using assms(2,3,4,5)
      apply (cases)
      apply (simp only: vc_passive.vc_loopBody_def)
      apply (handle_cmd_list_full)
      apply auto
      apply (rule+, simp)+
      done
    hence "s'' \<noteq> Failure" and As'':"(\<forall>n_s''. s'' = Normal n_s'' \<longrightarrow> 
                                     n_s'' ''n'' = Some (IntV vc_n) \<and> n_s'' ''k'' = Some (IntV vc_k) \<and>
                                     (\<exists> vc_i'. n_s'' ''i'' = Some (IntV vc_i')) \<and>
                                     \<Gamma> \<turnstile> \<langle>Var ''i'' \<guillemotleft>Gt\<guillemotright> (Val (IntV 0)), n_s''\<rangle> \<Down> BoolV True)"
    by simp_all
    moreover from local.RedNode have "n' = LH" using G_def
      by (metis outEdges_goto_simple.simps(1) select_convs(3) singleton_iff)
    show ?thesis
    proof (cases s'')
      case (Normal n_s'')
      with  As'' obtain vc_i' where "n_s'' ''i'' = Some (IntV vc_i')" by auto
      show ?thesis 
      proof (rule IH[of jpred n_s''])
        show "jpred \<le> j" using \<open>j = Suc jpred\<close> by simp
      next
        show "\<Lambda>,\<Gamma>,G \<turnstile>(Inl (Suc 0), Normal n_s'') -n\<rightarrow>^jpred (m', s')" 
          using Apred local.Normal \<open>m'' = Inl n'\<close> \<open>n' = LH\<close> by simp
      next 
        show "n_s'' ''n'' = Some (IntV vc_n)" using As'' local.Normal by simp
      next
        show "n_s'' ''k'' = Some (IntV vc_k)" using As'' local.Normal by simp
      next 
        show "n_s'' ''i'' = Some (IntV vc_i')" using \<open>n_s'' ''i'' = Some (IntV vc_i')\<close> by assumption
        show "\<Gamma> \<turnstile> \<langle>Var ''i'' \<guillemotleft>Gt\<guillemotright> Val (IntV 0),n_s''\<rangle> \<Down> BoolV True" using As'' local.Normal  by simp
      qed
    next
      case Failure
      then show ?thesis using \<open>s'' \<noteq> Failure\<close> by simp
    next
      case Magic
      then show ?thesis using Apred magic_stays_cfg_k_step by blast
    qed
  next
    case (RedReturn cs)
    then show ?thesis using G_def 
    by (metis insert_not_empty outEdges_goto_simple.simps(1) select_convs(3))
  qed
qed

lemma loopHead_correct:
  assumes 
   "\<Lambda>, \<Gamma>, G \<turnstile> (Inl LH, Normal n_s) -n\<rightarrow>^j (m', s')" and 
   "((n_s ''n'') = (Some (IntV vc_n)))" and
   "((n_s ''k'') = (Some (IntV vc_k)))" and
   "((n_s ''i'') = (Some (IntV vc_i)))"
   "vc_passive.vc_loopHead vc_k" and
   Inv_holds:"\<Gamma> \<turnstile> \<langle>Var ''i'' \<guillemotleft>Gt\<guillemotright> (Val (IntV 0)), n_s\<rangle> \<Down> BoolV (True)"
  shows "s' \<noteq> Failure"
  using assms                 
proof(induction j arbitrary: n_s vc_i rule: less_induct)
  case (less x ns')
  show ?case
  proof (cases x)
    case 0
    with less.prems(1) show ?thesis by auto
  next
    case (Suc k)
    with less.prems(1) obtain z where 
        "(\<Lambda>, \<Gamma>, G \<turnstile> (Inl LH, Normal ns') -n\<rightarrow> z)" and A2:"(\<Lambda>, \<Gamma>, G \<turnstile> z -n\<rightarrow>^k (m', s'))"
      by (meson relpowp_Suc_E2)
    from A2 have A3:"(\<Lambda>, \<Gamma>, G \<turnstile> z -n\<rightarrow>* (m', s'))" by (meson relpowp_imp_rtranclp)
    from \<open>x = Suc k\<close> and less.IH have
     IH2: "\<And>k' ns2 vc_i'. k' \<le> k \<Longrightarrow>
    \<Lambda>,\<Gamma>,G \<turnstile>(Inl LH, Normal ns2) -n\<rightarrow>^k' (m', s') \<Longrightarrow>
    ns2 ''n'' = Some (IntV vc_n) \<Longrightarrow> ((ns2 ''k'') = (Some (IntV vc_k))) \<Longrightarrow>
    ns2 ''i'' = Some (IntV vc_i') \<Longrightarrow>
    \<Gamma> \<turnstile> \<langle>Var ''i'' \<guillemotleft>Gt\<guillemotright> (Val (IntV 0)),ns2\<rangle> \<Down> BoolV True \<Longrightarrow> s' \<noteq> Failure"
          using le_imp_less_Suc less.prems(4) less.prems(5) by meson
        from \<open>(\<Lambda>, \<Gamma>, G \<turnstile> (Inl LH, Normal ns') -n\<rightarrow> z)\<close> show ?thesis
        proof (cases)
          case (RedNode cs s'' n'')
          hence "\<Lambda>, \<Gamma> \<turnstile> \<langle>[(Assert (BinOp (Var ''i'') Gt (Val (IntV 0))))], Normal ns'\<rangle> [\<rightarrow>] s''"
            by (simp add: G_def)
          hence "s'' = Normal ns' \<and> vc_passive.vc_loopBody vc_i vc_k \<and> vc_passive.vc_afterLoop vc_i" using less.prems(4) less.prems(6) \<open>vc_passive.vc_loopHead vc_k\<close>
            apply (cases)
            apply (reduce_expr_full)
            apply (handle_cmd_list_full)
            apply (simp only: vc_passive.vc_loopHead_def)
            by auto
          hence "s'' = Normal ns'" and "vc_passive.vc_loopBody vc_i vc_k" and "vc_passive.vc_afterLoop vc_i" by simp_all
          from \<open>n'' \<in> out_edges G (Suc 0)\<close> have "n'' = LB \<or> n'' = AL" using G_def
            by (metis insertE outEdges_goto_simple.simps(3) select_convs(3) singleton_iff)
          thus ?thesis
          proof rule
            assume "n'' = AL"
            show ?thesis 
              apply (rule afterLoop_correct[of ns' m'])
              using \<open>n'' = AL\<close> A3 \<open>z = (Inl n'', s'')\<close> \<open>s'' = Normal ns'\<close> less.prems \<open>vc_passive.vc_afterLoop vc_i\<close>
              by simp_all
          next  
            assume "n'' = LB"
            show ?thesis
              apply (rule loopBody_correct[of k ns'])
              using A2 \<open>n'' = LB\<close> \<open>z = (Inl n'', s'')\<close> \<open>s'' = Normal ns'\<close> apply simp
              using \<open>ns' ''n'' = Some (IntV vc_n)\<close> apply simp
              using \<open>ns' ''k'' = Some (IntV vc_k)\<close> apply simp
              using \<open>ns' ''i'' = Some (IntV vc_i)\<close> apply simp
              using \<open>vc_passive.vc_loopBody vc_i vc_k\<close> apply simp
              using IH2 apply simp
              done
           qed
        next
          case (RedReturn cs s')
          then show ?thesis using G_def
            by (metis insert_not_empty outEdges_goto_simple.simps(3) select_convs(3)) 
        qed
      qed
qed
end

end
