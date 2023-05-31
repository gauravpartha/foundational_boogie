theory CfgOptimizations
  imports Boogie_Lang.Semantics Boogie_Lang.Util
begin


subsection \<open>Global block and hybrid global block lemma definition\<close>

definition hybrid_block_lemma_target_succ_verifies
  where "hybrid_block_lemma_target_succ_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block s1' \<equiv>
         (\<forall>ns1'. s1' = Normal ns1' \<longrightarrow>
                     (\<forall>target_succ. List.member (out_edges(G') ! tgt_block) target_succ \<longrightarrow>
                          (\<forall>m2' s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile> (Inl target_succ, (Normal  ns1')) -n\<rightarrow>* (m2', s2')) \<longrightarrow>
                                  s2' \<noteq> Failure)
                     )
                   )"

definition hybrid_block_lemma_target_verifies
  where "hybrid_block_lemma_target_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block tgt_cmds ns \<equiv>              
            (\<forall>s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>tgt_cmds, Normal ns\<rangle> [\<rightarrow>] s1') \<longrightarrow>  \<comment>\<open>First reduce the coalesced commands\<close>
                   s1' \<noteq> Failure \<and> 
                   \<comment>\<open>All successors blocks of \<^term>\<open>tgt_block\<close> must verify\<close>
                   hybrid_block_lemma_target_succ_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block s1'
              )"

definition hybrid_block_lemma
  where "hybrid_block_lemma A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block tgt_cmds \<equiv> 
          \<forall>m' ns s'.  
             (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, (Normal ns)) -n\<rightarrow>* (m', s')) \<longrightarrow>
             hybrid_block_lemma_target_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block tgt_cmds ns \<longrightarrow>
             s' \<noteq> Failure"

text \<open>\<^prop>\<open>hybrid_block_lemma A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block tgt_cmds\<close> formalizes the ``hybrid''
global block lemma that we discussed on 22.03. with which one can deal with the case where blocks
are coalesced. \<^term>\<open>src_block\<close> expresses the source block id that we are currently considering
(i.e., one of the blocks that will be coalesced). \<^term>\<open>tgt_block\<close> expresses the target block id
that of the coalesced block. \<^term>\<open>tgt_cmds\<close> expresses the currently considered 
coalesced commands in the target CFG (this corresponds to \<open>cs_i@cs_(i+1)@...@cs_n\<close> in our discussion).
\<close>

text \<open>We now define the standard global block lemma that we want to use for the cases where no blocks
are coalesced.\<close>

definition global_block_lemma
  where "global_block_lemma A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block \<equiv> 
          \<forall>m' ns s'.  
             (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, (Normal ns)) -n\<rightarrow>* (m', s')) \<longrightarrow>
             (\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile> (Inl tgt_block, (Normal ns)) -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure) \<longrightarrow>
             s' \<noteq> Failure"

subsection \<open>Helper lemmas\<close>

lemma hybrid_block_lemma_target_succ_verifies_intro:
  assumes 
   "\<And>ns1' target_succ m2' s2'. s1' = Normal ns1' \<Longrightarrow>
           List.member (out_edges(G') ! tgt_block) target_succ \<Longrightarrow>
           (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile> (Inl target_succ, (Normal  ns1')) -n\<rightarrow>* (m2', s2')) \<Longrightarrow>
            s2' \<noteq> Failure"
 shows "hybrid_block_lemma_target_succ_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block s1'"
  using assms
  unfolding hybrid_block_lemma_target_succ_verifies_def
  by blast

lemma hybrid_block_lemma_elim:
  assumes "hybrid_block_lemma A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block tgt_cmds" and
          "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, (Normal ns)) -n\<rightarrow>* (m', s')" and
          "hybrid_block_lemma_target_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block tgt_cmds ns"
  shows "s' \<noteq> Failure"
  using assms
  unfolding hybrid_block_lemma_def
  by blast




text \<open>The lemmas above are just for convenience. They make it more pleasant to prove (..._intro) 
and use (..._elim) the hybrid global block lemma definitions\<close>


text \<open>We discussed the following useful lemma (that is used below in the main proofs)\<close>

lemma red_cmd_append_failure_preserved:
  assumes "(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns\<rangle> [\<rightarrow>] s)" and 
          "s = Failure" 
     \<comment>\<open>Theoretically, it would be fine to directly write
       \<^term>\<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns\<rangle> [\<rightarrow>] Failure\<close>, but then the standard induction tactic
       does not carry over that the resulting state is a failure state\<close>
  shows "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs@cs',Normal ns\<rangle> [\<rightarrow>] Failure"
  using assms
  apply induction
   apply (simp add: failure_red_cmd_list)
  by (simp add: RedCmdListCons)




lemma red_cfg_magic_preserved:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(b, s0) -n\<rightarrow>* (m', s')" and "s0 = Magic"
  shows "s' = Magic"
  using assms
proof (induction rule: rtranclp_induct2)
  case refl
  then show ?case by simp
next
  case (step a b a b)
  then show ?case 
    using red_cfg.cases by blast
qed



lemma magic_lemma_assume_false:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, s\<rangle> [\<rightarrow>] s'" and
          "s'\<noteq>Failure" and
          "s = Normal ns"
          "(Assume (Lit (LBool False))) \<in> set (cs)"
        shows "s' = Magic"
  using assms
proof (induction arbitrary: ns)
  case (RedCmdListNil s)
  then show ?case
    by simp
next
  case (RedCmdListCons c s s'' cs s')
  then show ?case
proof (cases "c = (Assume (Lit (LBool False)))")
  case True
  hence "s'' = Magic" using RedCmdListCons
    by (meson RedLit assume_red_false)
  then show ?thesis using RedCmdListCons
    by (simp add: magic_stays_cmd_list_2)
next
  case False
  then show ?thesis
  proof (cases "s''")
    case (Normal x1)
    then show ?thesis
      by (metis False RedCmdListCons.IH RedCmdListCons.prems(1) RedCmdListCons.prems(3) set_ConsD)
  next
    case Failure
    then show ?thesis
      using RedCmdListCons.hyps(2) RedCmdListCons.prems(1) failure_stays_cmd_list by blast
  next
    case Magic
    then show ?thesis
      using RedCmdListCons.hyps(2) magic_stays_cmd_list_2 by blast
  qed
qed
qed

lemma assert_false_failure:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assert (Lit (LBool False)), Normal ns\<rangle> \<rightarrow> s"
  shows "s = Failure"
  using assms
  by (cases) auto


lemma magic_lemma_assert_false:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, s\<rangle> [\<rightarrow>] s'" and
          "s = Normal ns"
          "(Assert (Lit (LBool False))) \<in> set (cs)"
        shows "s' = Magic \<or> s' = Failure"
  using assms
proof (induction arbitrary: ns)
  case (RedCmdListNil s)
  then show ?case
    by simp
next
  case (RedCmdListCons c s s'' cs s')
  then show ?case
proof (cases "c = (Assert (Lit (LBool False)))")
  case True

  hence "s'' = Failure" using RedCmdListCons
    by (metis True assert_false_failure)
  
  then show ?thesis
    using RedCmdListCons.hyps(2) failure_stays_cmd_list_aux by blast
next
  case False
  then show ?thesis
  proof (cases "s''")
    case (Normal x1)
    then show ?thesis
      using False RedCmdListCons.IH RedCmdListCons.prems(2) by auto
  next
    case Failure
    then show ?thesis
      using RedCmdListCons.hyps(2) RedCmdListCons.prems(1) failure_stays_cmd_list by blast
  next
    case Magic
    then show ?thesis
      using RedCmdListCons.hyps(2) magic_stays_cmd_list_2 by blast
  qed
qed
qed


subsection \<open>Main lemmas for block coalescing and pruning of unreachable blocks\<close>

text \<open>In the following subsection, we show the two main lemmas that are interested in:
    \<^item> Given the hybrid global lemma for block i, we can construct the hybrid block lemma for block i-1 
    \<^item> Given the hybrid global lemma for block 1 (the first one of a sequence of blocks that is coalesced),
     we can construct the global block lemma (i.e., not hybrid global block lemma) for block 1.
\<close>

subsubsection \<open>Main lemma 1 (extending hybrid global block lemmas)\<close>

text \<open>The following lemma shows that given the hybrid global block lemma for block i, we can construct
the hybrid block lemma for block i-1. Below the suffix 1 is used for i and 0 is used for i-1.\<close>

lemma extend_hybrid_global_block_lemma:
 assumes 
      NextGlobal: "hybrid_block_lemma A M \<Lambda> \<Gamma> \<Omega> G G' src_block_1 tgt_block tgt_cmds_1" and      
      SourceBlock: "node_to_block G ! src_block_0 = cs" and
      SourceSucc: "out_edges G ! src_block_0 = [src_block_1]" and
                  "tgt_cmds_0 = cs@tgt_cmds_1"
 shows 
      "hybrid_block_lemma A M \<Lambda> \<Gamma> \<Omega> G G' src_block_0 tgt_block tgt_cmds_0"
  unfolding hybrid_block_lemma_def
proof (rule allI | rule impI)+ \<comment>\<open>Here, we are applying initial proof rule to get rid of universal quantifiers and implications\<close>
  fix m' ns s'
  assume RedSource: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block_0, Normal ns) -n\<rightarrow>* (m', s')" and
         TargetVerifies: "hybrid_block_lemma_target_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block tgt_cmds_0 ns"

  show "s' \<noteq> Failure"
  proof (cases rule: converse_rtranclpE2[OF RedSource]) 
    \<comment>\<open>converse_tranclpE2 shows that if (a,b) are in the transitive closure of R, then this means that either
       a = b or there is some y s.t. (a,y) is in R and (y,b) is in the transitive closure of R (the standard
       case  distinction has the dual second case where (a,y) is in the transitive closure of R and
       (y,b) is in R\<close>
    case 1
    \<comment>\<open>Source takes 0 steps \<longrightarrow> trivial\<close>
    then show ?thesis 
      by fast
  next
    case (2 b s0)
    \<comment>\<open>Source takes 1 step to \<^term>\<open>(b,s0)\<close> and then 0 more steps to \<^term>\<open>(m',s')\<close>\<close>

    \<comment>\<open>We now first show that b must be \<^term>\<open>src_block_1\<close>, \<^term>\<open>s0\<close> cannot be a failure, and that if \<^term>\<open>s0\<close> is
      a normal state, then we can reduce the commands of \<^term>\<open>src_block_0\<close> (i.e., \<^term>\<open>cs\<close>) to \<^term>\<open>s0\<close>.\<close>

    from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block_0, Normal ns) -n\<rightarrow> (b, s0)\<close>
    have OneStepResult: "s0 \<noteq> Failure \<and> (\<forall>ns0. (s0 = Normal ns0 \<longrightarrow> b = Inl src_block_1 \<and> 
                                                A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns\<rangle> [\<rightarrow>] Normal ns0))"
    proof cases \<comment>\<open>Because we used "from \<open>fact\<close>" where \<open>fact\<close> is defined inductively, \<open>cases\<close> 
                   does a case distinction over all rules that could have been used to derive 
                   \<open>fact\<close>\<close>
      case (RedNormalSucc cs ns' n')
      then show ?thesis 
        using SourceSucc SourceBlock
        by (simp add: member_rec(1) member_rec(2))
    next
      case (RedNormalReturn cs ns')
      then show ?thesis 
        using SourceSucc
        by simp
    next
      case (RedFailure cs)
      hence "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs@tgt_cmds_1,Normal ns\<rangle> [\<rightarrow>] Failure"
        using red_cmd_append_failure_preserved
        by fast
      hence False 
        using TargetVerifies \<open> node_to_block G ! src_block_0 = cs\<close> \<open>tgt_cmds_0 = _\<close> SourceBlock
        unfolding hybrid_block_lemma_target_verifies_def
        by blast
      thus ?thesis
        by simp        
    next
      case (RedMagic cs)
      then show ?thesis by auto
    qed

    \<comment>\<open>Using this result we now prove the goal by doing a case distinction on whether \<^term>\<open>s0\<close> is
       a magic state (if it is, we are trivially done; if not we know we are in a normal state and must
       continue the proof) \<close>
    
    show ?thesis
    proof (cases "s0 = Magic")
      case True
      \<comment>\<open>Once we are in the Magic state, we will always remain in the Magic state.\<close>
      thus "s' \<noteq> Failure"
        using red_cfg_magic_preserved[OF \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(b, s0) -n\<rightarrow>* (m', s')\<close>]
        by simp        
    next
      case False
      \<comment>\<open>In this case, we know that there must be a normal execution from \<^term>\<open>src_block_1\<close> to \<^term>\<open>(m', s')\<close>.
         Using this execution we can then get that \<^term>\<open>s'\<close> does not fail using the successor global block lemma
         that we are given as an assumption.\<close>

      from this obtain ns0 where "s0 = Normal ns0" 
        using OneStepResult state.exhaust by auto

      hence RedBlock0:  "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns\<rangle> [\<rightarrow>] Normal ns0" and
          RedSuccBlock: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block_1, Normal ns0) -n\<rightarrow>* (m', s')"
        using OneStepResult \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(b, s0) -n\<rightarrow>* (m', s')\<close>
        by auto
        
      \<comment>\<open>We now want to obtain the conclusion of the successor global lemma lemma (which shows our goal). 
         To do so, we will have to prove the corresponding assumptions.\<close>
      show ?thesis
      proof (rule hybrid_block_lemma_elim[OF NextGlobal RedSuccBlock]) 
        \<comment>\<open>\<open>thm\<close>[OF \<open>fact\<close>] works if \<open>fact1\<close> proves the first assumption of \<open>thm\<close> and renders the same
           as \<open>thm\<close> without the first assumption (one can discharge multiple assumptions using OF)\<close>

        \<comment>\<open>We now just need to show that the target assumption of the successor global block lemma
          holds\<close>
        show "hybrid_block_lemma_target_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block tgt_cmds_1 ns0"
          unfolding hybrid_block_lemma_target_verifies_def
        proof (rule allI, rule impI, rule conjI)
           \<comment>\<open>We first need to show that executing \<^emph>\<open>just\<close> the coalesced blocks associated with the 
             successor block cannot fail\<close>
          fix s1'
          assume "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>tgt_cmds_1,Normal ns0\<rangle> [\<rightarrow>] s1'"
          with RedBlock0 have "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs@tgt_cmds_1,Normal ns\<rangle> [\<rightarrow>] s1'"
            by (simp add: red_cmd_list_append)
          thus "s1' \<noteq> Failure"
            using TargetVerifies \<open>tgt_cmds_0 = cs @ tgt_cmds_1\<close>
            unfolding hybrid_block_lemma_target_verifies_def
            by simp
        next
          \<comment>\<open>We next need to show that for any execution E of the successor coalesced blocks that continues
            in the CFG will not fail. We show this by first show that execution E can be extended
            to an execution of the extended coalesced blocks (i.e., \<^prop>\<open>tgt_cmds_0 = cs @ tgt_cmds_1\<close>).
            Using this assumption we automatically get from our own assumptions (TargetVerifies) that
            if E continues through the CFG (through \<open>tgt_block\<close>) there won't be any issues\<close>
          fix s1'
          assume "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>tgt_cmds_1,Normal ns0\<rangle> [\<rightarrow>] s1'"
          with RedBlock0 have RedTgtCmds0:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>tgt_cmds_0 ,Normal ns\<rangle> [\<rightarrow>] s1'"
            using \<open>tgt_cmds_0 = _\<close>
            by (simp add: red_cmd_list_append)

          
          thus "hybrid_block_lemma_target_succ_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block s1'"
            using TargetVerifies
            unfolding hybrid_block_lemma_target_verifies_def
            by fast
        qed
      qed    
    qed
  qed
qed

subsubsection \<open>Main lemma 2 (converting hybrid global block lemma to normal global block lemma)\<close>  

lemma convert_hybrid_global_block_lemma:
 assumes 
      HybridGlobal: "hybrid_block_lemma A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block tgt_cmds" and      
      \<comment>\<open>The coalesced block id has commands \<^term>\<open>tgt_cmds\<close>\<close> 
      TargetBlock: "node_to_block G' ! tgt_block = tgt_cmds"
 shows 
      "global_block_lemma A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block"  
  unfolding global_block_lemma_def
proof (rule allI | rule impI)+
  fix m' ns s'
  assume RedSource: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block, Normal ns) -n\<rightarrow>* (m', s')" and
     TargetVerifies: "\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl tgt_block, Normal ns) -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure"         

  \<comment>\<open>We prove the conclusion by proving the assumptions of the hybrid global block lemma and then 
     using its conclusion, which solves the goal\<close>
  show "s' \<noteq> Failure"
  proof (rule hybrid_block_lemma_elim[OF HybridGlobal RedSource]) \<comment>\<open>We discharge the first assumption via OF\<close> 
    show "hybrid_block_lemma_target_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block tgt_cmds ns"
      unfolding hybrid_block_lemma_target_verifies_def
    proof (rule allI, rule impI)
      fix s1'
      assume RedTgtCmds: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>tgt_cmds,Normal ns\<rangle> [\<rightarrow>] s1'"
      text \<open>We need to show that \<^term>\<open>s1'\<close> does not fail. Since we know \<^term>\<open>tgt_cmds\<close> denotes exactly
            the commands of \<^term>\<open>tgt_block\<close>, we get automatically that there is a one step execution
            from \<^term>\<open>tgt_block\<close> to state \<^term>\<open>s1'\<close> and according to our TargetVerifies assumption
            we thus get that  \<^term>\<open>s1'\<close> is not a failing state\<close>

      have "s1' \<noteq> Failure"
      proof (rule ccontr) \<comment>\<open>proof by contradiction\<close>
        assume "\<not> s1' \<noteq> Failure" 
        hence "s1' = Failure" by simp
        have "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl tgt_block, Normal ns) -n\<rightarrow>* (Inr (), Failure))"
          apply (rule converse_rtranclp_into_rtranclp)
           apply (rule RedFailure)
            apply (rule TargetBlock)
          using  RedTgtCmds \<open>s1' = Failure\<close>
           apply blast
          by simp
        thus False
          using TargetVerifies
          by blast        
      qed
    
        
      text \<open>Next, we show the second assumption: If the execution continues through the CFG, then the
            execution won't fail. \<close>
  
      moreover have "hybrid_block_lemma_target_succ_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block s1'"
      proof (rule hybrid_block_lemma_target_succ_verifies_intro)
        fix ns1' tgt_succ m2' s2'
        assume "s1' = Normal ns1'" and 
               TargetSucc: "List.member (out_edges G' ! tgt_block) tgt_succ" and
               RedTargetSucc: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl tgt_succ, Normal ns1') -n\<rightarrow>* (m2', s2')"

        text \<open>We can construct an execution beginning from \<^term>\<open>tgt_block\<close>\<close>
        have "A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl tgt_block, Normal ns) -n\<rightarrow>* (m2', s2')"
          apply (rule converse_rtranclp_into_rtranclp)
           apply (rule RedNormalSucc) 
             apply (rule TargetBlock)
          using RedTgtCmds \<open>s1' = Normal ns1'\<close>
            apply blast
           apply (rule TargetSucc)
          apply (rule RedTargetSucc)
          done

        thus "s2' \<noteq> Failure"
          using TargetVerifies
          by blast
      qed

      ultimately show 
       "s1' \<noteq> Failure \<and> hybrid_block_lemma_target_succ_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block s1'"
        by simp
    qed
  qed
qed

subsubsection \<open>Main Lemma 3 (The following lemma shows that if in a block the global block lemma holds for all successors and the block was not coalesced, then the global block lemma holds)\<close>

lemma global_block_succ:
  assumes SuccBlocks: "out_edges G ! src_block = ls" and
          GlobalBlockSucc: "\<forall>x\<in>set(ls). global_block_lemma A M \<Lambda> \<Gamma> \<Omega> G G' x (f(x))" and
          FunctionCorr: "\<forall>x\<in>set(ls). f(x)\<in>set(out_edges G' ! tgt_block)" and
          TargetBlock: "node_to_block G' ! tgt_block = tgt_cmds" and
          SourceBlock: "node_to_block G ! src_block = src_cmds" and
          NotCoalesced: "tgt_cmds = src_cmds"
        shows "global_block_lemma A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block"
  unfolding global_block_lemma_def
proof (rule allI | rule impI)+
  fix m' ns s'
  assume RedSource: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block, Normal ns) -n\<rightarrow>* (m', s')" and
         TargetVerifies: "\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl tgt_block, Normal ns) -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure"
  show "s'\<noteq>Failure"

  proof (cases rule: converse_rtranclpE2[OF RedSource])
    case 1
    then show ?thesis
      by blast
  next
    case (2 a b)
    from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, Normal ns) -n\<rightarrow> (a, b)\<close> have OneStepResult: "b \<noteq> Failure"
    proof cases
      case (RedNormalSucc cs ns' n')
      then show ?thesis
        by auto
    next
      case (RedNormalReturn cs ns')
      then show ?thesis
        by simp
    next
      case (RedFailure cs)
      then show ?thesis
        by (metis NotCoalesced SourceBlock TargetBlock TargetVerifies r_into_rtranclp red_cfg.RedFailure)
    next
      case (RedMagic cs)
      then show ?thesis
        by simp
    qed

    show ?thesis
    proof (cases "b = Magic")
      case True
      thus "s' \<noteq> Failure"
        using "2"(2) red_cfg_magic_preserved by blast
    next
      case False

      from this obtain ns0 where "b = Normal ns0"
        using OneStepResult state.exhaust by blast

      from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block, Normal ns) -n\<rightarrow> (a, b)\<close> show ?thesis
      proof cases
        case (RedNormalSucc cs ns' succ)
        have cond_global_block: "\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile> (Inl (f(succ)), (Normal ns0)) -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure"
        proof (rule allI | rule impI)+
          fix m1' s1'
          assume "A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl (f succ), Normal ns0) -n\<rightarrow>* (m1', s1')"
          show "s1' \<noteq> Failure"
          proof (cases "((m1', s1') = (Inl (f succ), Normal ns0))")
            case True
            then show ?thesis 
              by auto
          next
            case False
            hence "A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl tgt_block, Normal ns) -n\<rightarrow> (Inl (f succ), Normal ns0)"
              by (metis FunctionCorr NotCoalesced SourceBlock SuccBlocks TargetBlock \<open>b = Normal ns0\<close> in_set_member local.RedNormalSucc(2) local.RedNormalSucc(3) local.RedNormalSucc(4) local.RedNormalSucc(5) red_cfg.RedNormalSucc)
            hence "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl tgt_block, Normal ns) -n\<rightarrow>* (m1', s1'))"
              by (simp add: \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl (f succ), Normal ns0) -n\<rightarrow>* (m1', s1')\<close> converse_rtranclp_into_rtranclp)
            then show ?thesis
              by (simp add: TargetVerifies)
          qed
        qed
        hence "global_block_lemma A M \<Lambda> \<Gamma> \<Omega> G G' succ (f(succ))"
          by (metis GlobalBlockSucc SuccBlocks in_set_member local.RedNormalSucc(5))
        then show ?thesis 
          using cond_global_block
          unfolding global_block_lemma_def
          using "2"(2) \<open>b = Normal ns0\<close> local.RedNormalSucc(1) by blast
      next
        case (RedNormalReturn cs ns')
        then show ?thesis 
          using "2"(2) finished_remains by blast
      next
        case (RedFailure cs)
        then show ?thesis 
          by (simp add: OneStepResult)
      next
        case (RedMagic cs)
        then show ?thesis 
          by (simp add: False)
      qed
    qed
  qed
qed

subsubsection \<open>Main Lemma 4: The following lemma shows that if in a block the global block lemma holds for all successors and the block was coalesced, then the hybrid block lemma holds\<close>

lemma hybrid_block_succ:
  assumes SuccBlocks: "out_edges G ! src_block = ls" and
          GlobalBlockSucc: "\<forall>x\<in>set(ls). global_block_lemma A M \<Lambda> \<Gamma> \<Omega> G G' x (f(x))" and
          FunctionCorr: "\<forall>x\<in>set(ls). f(x)\<in>set(out_edges G' ! tgt_block)" and
          SourceBlock: "node_to_block G ! src_block = src_cmds"
        shows "hybrid_block_lemma A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block src_cmds"
  unfolding hybrid_block_lemma_def
proof (rule allI | rule impI)+
  fix m' ns s'
  assume RedSource: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block, Normal ns) -n\<rightarrow>* (m', s')" and
         TargetVerifies: "hybrid_block_lemma_target_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block src_cmds ns"
  show "s' \<noteq> Failure"
  proof (cases rule: converse_rtranclpE2[OF RedSource])
    case 1
    then show ?thesis by blast
  next
    case (2 a b)
    from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, Normal ns) -n\<rightarrow> (a, b)\<close> have OneStepResult: "b \<noteq> Failure"
    proof cases
      case (RedNormalSucc cs ns' n')
      then show ?thesis
        by simp
    next
      case (RedNormalReturn cs ns')
      then show ?thesis
        by simp
    next
      case (RedFailure cs)
      then show ?thesis
        using SourceBlock TargetVerifies hybrid_block_lemma_target_verifies_def by blast
    next
      case (RedMagic cs)
      then show ?thesis
        by blast
    qed

    show ?thesis
    proof (cases "b = Magic")
      case True
      then show ?thesis
        using "2"(2) red_cfg_magic_preserved by blast
    next
      case False
      from this obtain ns0 where "b = Normal ns0"
        using OneStepResult state.exhaust by blast
      from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, Normal ns) -n\<rightarrow> (a, b)\<close> show ?thesis
      proof cases
        case (RedNormalSucc cs ns' succ)
        hence "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>src_cmds,Normal ns\<rangle> [\<rightarrow>] Normal ns0"
          using SourceBlock \<open>b = Normal ns0\<close> by force

        have cond_global_block: "\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile> (Inl (f(succ)), (Normal ns0)) -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure"
          using GlobalBlockSucc TargetVerifies
          unfolding hybrid_block_lemma_target_verifies_def global_block_lemma_def hybrid_block_lemma_target_succ_verifies_def
          by (metis FunctionCorr SuccBlocks \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>src_cmds,Normal ns\<rangle> [\<rightarrow>] Normal ns0\<close> in_set_member local.RedNormalSucc(5))

        hence "global_block_lemma A M \<Lambda> \<Gamma> \<Omega> G G' succ (f(succ))"
          by (metis GlobalBlockSucc SuccBlocks in_set_member local.RedNormalSucc(5))
        then show ?thesis
          unfolding global_block_lemma_def
          using "2"(2) \<open>b = Normal ns0\<close> cond_global_block local.RedNormalSucc(1) by blast
      next
        case (RedNormalReturn cs ns')
        then show ?thesis
          using "2"(2) finished_remains by blast
      next
        case (RedFailure cs)
        then show ?thesis 
          using OneStepResult by blast
      next
        case (RedMagic cs)
        then show ?thesis 
          by (simp add: False)
      qed
    qed
  qed
qed


subsubsection \<open>Main Lemma 5: Following Lemma shows correctness of pruning of unreachable blocks if the block was not coalesced\<close>

lemma pruning_not_coalesced:
  assumes SuccBlocks: "out_edges G ! src_block = ls" and
          TargetBlock: "node_to_block G' ! tgt_block = tgt_cmds" and
          SourceBlock: "node_to_block G ! src_block = src_cmds" and
          Pruning: "(Assume (Lit (LBool False))) \<in> set (src_cmds) \<or> (Assert (Lit (LBool False))) \<in> set (src_cmds)" and
          NotCoalesced: "tgt_cmds = src_cmds"
        shows "global_block_lemma A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block"
  unfolding global_block_lemma_def

proof (rule allI | rule impI)+
  fix m' ns s'
  assume RedSource: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block, Normal ns) -n\<rightarrow>* (m', s')" and
         TargetVerifies: "\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl tgt_block, Normal ns) -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure"
  show "s'\<noteq>Failure"
  proof (cases rule: converse_rtranclpE2[OF RedSource])
    case 1
    then show ?thesis
      by blast
  next
    case (2 a b)
    from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, Normal ns) -n\<rightarrow> (a, b)\<close>  show ?thesis
    proof cases
      case (RedNormalSucc cs ns' n')
      have "(Assume (Lit (LBool False))) \<in> set (cs) \<or> (Assert (Lit (LBool False))) \<in> set (cs)"
        using Pruning SourceBlock local.RedNormalSucc(3) by blast
      then show ?thesis
      proof (cases "(Assume (Lit (LBool False))) \<in> set (cs)")
        case True
        hence "b = Magic"
          using local.RedNormalSucc(4) magic_lemma_assume_false by blast
        then show ?thesis
          by (simp add: local.RedNormalSucc(2))
      next
        case False
        hence "b = Magic \<or> b = Failure"
          using \<open>Assume (Lit (LBool False)) \<in> set cs \<or> Assert (Lit (LBool False)) \<in> set cs\<close> local.RedNormalSucc(4) magic_lemma_assert_false by blast
        then show ?thesis
          by (simp add: local.RedNormalSucc(2))
      qed

    next
      case (RedNormalReturn cs ns')
      then show ?thesis 
        by (metis "2"(2) Pair_inject finished_remains state.distinct(1))
    next
      case (RedFailure cs)
      then show ?thesis
        by (metis NotCoalesced SourceBlock TargetBlock TargetVerifies r_into_rtranclp red_cfg.RedFailure)
    next
      case (RedMagic cs)
      then show ?thesis
        using "2"(2) red_cfg_magic_preserved by blast
    qed
  qed
qed

subsubsection \<open>Main Lemma 6: Following Lemma shows correctness of pruning of unreachable blocks if the block was coalesced\<close>

lemma pruning_coalesced:
  assumes TargetBlock: "node_to_block G' ! tgt_block = tgt_cmds" and
          SourceBlock: "node_to_block G ! src_block = src_cmds" and
          Pruning: "(Assert (Lit (LBool False))) \<in> set (src_cmds) \<or> (Assume (Lit (LBool False))) \<in> set (src_cmds)" and
          Coalesced: "tgt_cmds = cs@src_cmds"
        shows "hybrid_block_lemma A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block src_cmds"
  unfolding hybrid_block_lemma_def

proof (rule allI | rule impI)+
  fix m' ns s'
  assume RedSource: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block, Normal ns) -n\<rightarrow>* (m', s')" and
         TargetVerifies: "hybrid_block_lemma_target_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block src_cmds ns"
  show "s' \<noteq> Failure"
  proof (cases rule: converse_rtranclpE2[OF RedSource])
    case 1
    then show ?thesis
      by blast
  next
    case (2 a b)
    from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, Normal ns) -n\<rightarrow> (a, b)\<close>  show ?thesis
    proof cases
      case (RedNormalSucc cs ns' n')
      have "(Assume (Lit (LBool False))) \<in> set (cs) \<or> (Assert (Lit (LBool False))) \<in> set (cs)"
        using Pruning SourceBlock local.RedNormalSucc(3) by blast
      then show ?thesis
      proof (cases "(Assume (Lit (LBool False))) \<in> set (cs)")
        case True
        hence "b = Magic"
          using local.RedNormalSucc(4) magic_lemma_assume_false by blast
        then show ?thesis
          by (simp add: local.RedNormalSucc(2))
      next
        case False
        hence "b = Magic \<or> b = Failure"
          using \<open>Assume (Lit (LBool False)) \<in> set cs \<or> Assert (Lit (LBool False)) \<in> set cs\<close> local.RedNormalSucc(4) magic_lemma_assert_false by blast
        then show ?thesis
          by (simp add: local.RedNormalSucc(2))
      qed
    next
      case (RedNormalReturn cs ns')
      then show ?thesis
        by (metis "2"(2) Pair_inject finished_remains state.distinct(1))
    next
      case (RedFailure cs)
      then show ?thesis 
        using SourceBlock TargetVerifies hybrid_block_lemma_target_verifies_def by blast
    next
      case (RedMagic cs)
      then show ?thesis 
        using "2"(2) red_cfg_magic_preserved by blast
    qed
   
  qed
qed

subsection \<open>Definition of free variables\<close>

fun free_var_expr :: "expr \<Rightarrow> vname set"
where 
  "free_var_expr (Var n) = {n}"
| "free_var_expr (BVar n) = {}"
| "free_var_expr (Lit n) = {}"
| "free_var_expr (UnOp unop ex) = free_var_expr (ex)"
| "free_var_expr (BinOp ex1 binop ex2) = free_var_expr (ex1) \<union> free_var_expr (ex2)"
| "free_var_expr (FunExp fname ty_list ex_ls)  = \<Union> (Set.image free_var_expr (set ex_ls))" 
| "free_var_expr (Old ex) = free_var_expr (ex)"
| "free_var_expr (Forall ty ex) = free_var_expr (ex)"
| "free_var_expr (Exists ty ex) = free_var_expr (ex)"
| "free_var_expr (ForallT ex) = free_var_expr (ex)"
| "free_var_expr (ExistsT ex) = free_var_expr (ex)"

fun free_var_exprlist :: "expr list \<Rightarrow> vname set"
where
  "free_var_exprlist cs = \<Union> (Set.image free_var_expr (set cs))"


fun free_var_cmd :: "cmd \<Rightarrow> vname set"
where
  "free_var_cmd (Assert ex) = free_var_expr ex"
| "free_var_cmd (Assume ex) = free_var_expr ex"
| "free_var_cmd (Assign vname expr) = {vname} \<union> free_var_expr expr"
| "free_var_cmd (Havoc vname) = {vname}"
| "free_var_cmd (ProcCall pname ex_ls vname_ls) = set vname_ls \<union> (\<Union> (Set.image free_var_expr (set ex_ls)))" (* is this correct?" *)

fun free_var_cmdlist :: "cmd list \<Rightarrow> vname set"
where
  "free_var_cmdlist cs = \<Union> (Set.image free_var_cmd (set cs))"

subsection \<open>Helper Lemmas for the final dead variables elimination lemma\<close>

lemma validConf:
  assumes proc_cor: "proc_is_correct A fun_decls constants global_vars axioms proc Semantics.proc_body_satisfies_spec" and
                    "proc_body proc = Some (locals, mbody)" and
                    "(((\<forall>t. closed t \<longrightarrow> (\<exists>v. type_of_val A (v :: 'a val) = t)) \<and> (\<forall>v. closed ((type_of_val A) v))))" and
                    "fun_interp_wf A fun_decls \<Gamma>" and
                    "list_all closed \<Omega> \<and> length \<Omega> = proc_ty_args proc" and        
                    "state_typ_wf A \<Omega> gs (constants @ global_vars)" and
                    "state_typ_wf A \<Omega> ls ((proc_args proc)@ (locals @ proc_rets proc))" and
                    "axioms_sat A (constants, []) \<Gamma> (global_to_nstate (state_restriction gs constants)) axioms" and            
                    "expr_all_sat A (constants@global_vars, (proc_args proc)@(locals@(proc_rets proc))) \<Gamma> \<Omega> \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> (proc_all_pres proc)" and 
                    "A, [], (constants@global_vars, (proc_args proc)@(locals@(proc_rets proc))), \<Gamma>, \<Omega>, mbody \<turnstile> (Inl (entry(mbody)), Normal \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr>) -n\<rightarrow>* (m',s')"

  shows             "valid_configuration A (constants@global_vars, (proc_args proc)@(locals@(proc_rets proc))) \<Gamma> \<Omega> (proc_checked_posts proc) m' s'"
  using assms
  unfolding proc_body_satisfies_spec_def
  by fastforce

lemma map_le_append_pre:
  assumes "map_of xs \<subseteq>\<^sub>m map_of xs'"
  shows "map_of (ys@xs) \<subseteq>\<^sub>m map_of (ys@xs')" 
  using assms
  by (metis Map.map_of_append append_assoc map_add_subsumed2 map_le_map_add)
  
lemma map_le_append_post:
  assumes "map_of xs \<subseteq>\<^sub>m map_of xs'" and 
          \<comment>\<open>This second assumption is necessary, because otherwise \<^term>\<open>map_of (xs@ys) y\<close> may lookup
             a value in \<^term>\<open>ys\<close>, while \<^term>\<open>map_of (xs'@ys) y\<close> looks up the value in \<^term>\<open>xs'\<close>\<close>
          "dom (map_of xs') \<inter> dom (map_of ys) = {}"
  shows "map_of (xs@ys) \<subseteq>\<^sub>m map_of (xs'@ys)"
  using assms
  by (metis Map.map_of_append map_add_comm map_add_le_mapI map_le_map_add map_le_trans)

lemma map_le_append_pre_post:
  assumes "map_of xs \<subseteq>\<^sub>m map_of xs'" and 
          \<comment>\<open>This second assumption is necessary, because otherwise \<^term>\<open>map_of (xs@ys) y\<close> may lookup
             a value in \<^term>\<open>ys\<close>, while \<^term>\<open>map_of (xs'@ys) y\<close> looks up the value in \<^term>\<open>xs'\<close>\<close>
          "dom (map_of xs') \<inter> dom (map_of ys) = {}"
  shows "map_of (ws@xs@ys) \<subseteq>\<^sub>m map_of (ws@xs'@ys)"
  using assms map_le_append_pre map_le_append_post
  by blast 

lemma lookup_var_decl_map_le:
  assumes "map_of vs \<subseteq>\<^sub>m map_of vs'"          
  shows "lookup_vdecls_ty vs \<subseteq>\<^sub>m lookup_vdecls_ty vs'"
  unfolding lookup_vdecls_ty_def map_le_def
proof 
  fix a
  assume "a \<in> dom (\<lambda>x. map_option fst (map_of vs x))"

  thus "map_option fst (map_of vs a) = map_option fst (map_of vs' a)"
    using assms
    by (metis (full_types) domIff map_le_def option.map_disc_iff)
qed

text \<open>The following lemma should be helpful to prove that variables reduce to the same values in 
      in the program with and without dead variables.\<close>
lemma lookup_var_map_le_local:
  assumes MapLeLocal: "(map_of (snd \<Lambda>) \<subseteq>\<^sub>m map_of (snd \<Lambda>') \<and> x \<notin> (dom (map_of (snd \<Lambda>')) - (dom (map_of (snd \<Lambda>))))) 
                       \<or> (map_of (snd \<Lambda>') \<subseteq>\<^sub>m map_of (snd \<Lambda>) \<and> x \<notin> (dom (map_of (snd \<Lambda>)) - (dom (map_of (snd \<Lambda>'))))) "
  shows "lookup_var \<Lambda> ns x = lookup_var \<Lambda>' ns x"
proof (cases "(map_of (snd \<Lambda>) \<subseteq>\<^sub>m map_of (snd \<Lambda>') \<and> x \<notin> (dom (map_of (snd \<Lambda>')) - (dom (map_of (snd \<Lambda>)))))")
  case True
  then show ?thesis
  proof (cases "map_of (snd \<Lambda>) x = None")
    case True
    hence "map_of (snd \<Lambda>') x = None"
      by (metis (mono_tags, lifting) DiffI assms domIff map_le_def)
    with True show ?thesis 
      unfolding lookup_var_def
      by simp
  next
    case False
    then show ?thesis
      using MapLeLocal
      unfolding lookup_var_def
      by (metis (mono_tags, lifting) True domIff map_le_def)
  qed
next
  case False
  then show ?thesis
  proof (cases "map_of (snd \<Lambda>') x = None")
    case True
    hence "map_of (snd \<Lambda>) x = None"
      using False assms by blast
    with True show ?thesis 
      unfolding lookup_var_def
      by simp
  next
    case False
    then show ?thesis 
      using MapLeLocal
      unfolding lookup_var_def
      by (metis (mono_tags, lifting) DiffI domIff map_le_def)
  qed
qed


lemma binder_map_le_local:
  assumes MapLeLocal: "map_of (snd \<Lambda>) \<subseteq>\<^sub>m map_of (snd \<Lambda>')" and
          "x \<notin> (dom (map_of (snd \<Lambda>')) - (dom (map_of (snd \<Lambda>))))"
        shows "binder_state ns i = binder_state ns i"
  by simp



lemma state_typ_wf_map_le:
  assumes StateTypWf: "state_typ_wf A \<Omega> ls (proc_args proc @ locals' @ proc_rets proc)" (is "state_typ_wf A \<Omega> ls ?V'") and
         MapLe: "map_of locals \<subseteq>\<^sub>m map_of locals'" and
         DomLocalInterRetsEmpty:   "dom (map_of locals') \<inter> dom (map_of (proc_rets proc)) = {}"
        shows "state_typ_wf A \<Omega> ls (proc_args proc @ locals @ proc_rets proc)" (is "state_typ_wf A \<Omega> ls ?V")
  unfolding state_typ_wf_def
proof (rule allI | rule impI)+
  fix v t
  assume LookupV: "lookup_vdecls_ty (proc_args proc @ locals @ proc_rets proc) v = Some t"

  from MapLe have "map_of ?V \<subseteq>\<^sub>m map_of ?V'"
    using map_le_append_pre_post[OF MapLe DomLocalInterRetsEmpty]
    by blast        

  with LookupV
  have "lookup_vdecls_ty (proc_args proc @ locals' @ proc_rets proc) v = Some t"
    using lookup_var_decl_map_le
    by (metis (full_types) domI map_le_def)

  thus "map_option (type_of_val A) (ls v) = Some (instantiate \<Omega> t)"
    using StateTypWf
    unfolding state_typ_wf_def
    by blast
qed




lemma expr_eval_different_locals_same_value:
  assumes  "fst \<Lambda> = fst \<Lambda>'" and
           "map_of (snd \<Lambda>') \<subseteq>\<^sub>m map_of (snd \<Lambda>)  \<or> map_of (snd \<Lambda>) \<subseteq>\<^sub>m map_of (snd \<Lambda>')" 
  shows    "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, s\<rangle> \<Down> v \<Longrightarrow> 
              free_var_expr e \<inter> ((dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))) \<union> (dom (map_of (snd \<Lambda>)) - dom (map_of (snd \<Lambda>')))) = {} 
              \<Longrightarrow> A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>e, s\<rangle> \<Down> v" and
           "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es, s\<rangle> [\<Down>] vs \<Longrightarrow>
              \<Union> {free_var_expr e' | e'. e' \<in> set es} \<inter> ((dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))) \<union> (dom (map_of (snd \<Lambda>)) - dom (map_of (snd \<Lambda>')))) = {} 
              \<Longrightarrow> A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>es, s\<rangle> [\<Down>] vs"
  using assms
proof (induction rule: red_expr_red_exprs.inducts)
  case (RedVar n_s x v \<Omega>)
  then show ?case
  proof (cases "map_of (snd \<Lambda>') \<subseteq>\<^sub>m map_of (snd \<Lambda>)")
    case True
    have "free_var_expr (Var x) \<inter> (dom (map_of (snd \<Lambda>)) - (dom (map_of (snd \<Lambda>')))) = {}"
      using RedVar.prems(1)
      by blast

    hence notin: "x \<notin> (dom (map_of (snd \<Lambda>)) - (dom (map_of (snd \<Lambda>'))))"
      using Int_Un_eq(2) RedVar.prems(1) by auto

    have "lookup_var \<Lambda>' n_s x = lookup_var \<Lambda> n_s x"
      apply (rule lookup_var_map_le_local)
      using True notin by auto

    then show ?thesis
      by (simp add: RedVar.IH red_expr_red_exprs.RedVar)
  next
    case False

    have "free_var_expr (Var x) \<inter> (dom (map_of (snd \<Lambda>')) - (dom (map_of (snd \<Lambda>)))) = {}"
      using RedVar.prems(1)
      by blast

    hence notin: "x \<notin> (dom (map_of (snd \<Lambda>')) - (dom (map_of (snd \<Lambda>))))"
      by simp

    have "lookup_var \<Lambda>' n_s x = lookup_var \<Lambda> n_s x"
      apply (rule lookup_var_map_le_local)
      using False notin assms(2) by blast

    then show ?thesis
      by (simp add: RedVar.IH red_expr_red_exprs.RedVar)
  qed
next
  case (RedBVar n_s i v \<Omega>)
  then show ?case
    by (simp add: red_expr_red_exprs.RedBVar)
next
  case (RedLit \<Omega> v n_s)
  then show ?case
    by (simp add: red_expr_red_exprs.RedLit)
next
  case (RedBinOp \<Omega> e1 n_s v1 e2 v2 bop v)


  have v1: "A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>e1,n_s\<rangle> \<Down> v1"
    by (metis (no_types, lifting) Diff_Compl Int_Diff Int_empty_right RedBinOp.IH(2) RedBinOp.prems(1) RedBinOp.prems(3) Un_Int_eq(3) assms(1) free_var_expr.simps(5))

  have v2: "A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>e2,n_s\<rangle> \<Down> v2"
    using RedBinOp.IH(4) RedBinOp.prems(1) RedBinOp.prems(3) assms(1) free_var_expr.simps(5) by blast
  show ?case
    using v1 v2
    using RedBinOp.hyps red_expr_red_exprs.RedBinOp by blast
next
  case (RedUnOp \<Omega> e n_s v uop v')
  then show ?case
    by (simp add: red_expr_red_exprs.RedUnOp)
next
  case (RedFunOp f f_interp \<Omega> args n_s v_args ty_args v)


  have "\<Union> {free_var_expr e' |e'. e' \<in> set args} \<inter> ((dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))) \<union> (dom (map_of (snd \<Lambda>)) - dom (map_of (snd \<Lambda>')))) = {}"
    using RedFunOp.prems(1) free_var_expr.simps(6)
    by blast

  hence "A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>args, n_s\<rangle> [\<Down>] v_args"
    by (simp add: RedFunOp.IH(3) RedFunOp.prems(3) assms(1))

  then show ?case
    using RedFunOp
    by (simp add: red_expr_red_exprs.RedFunOp)
next
(*case (RedCondExpTrue \<Omega> cond n_s thn v els)
  then show ?case sorry
next
  case (RedCondExpFalse \<Omega> cond n_s els v thn)
  then show ?case sorry
next *)
  case (RedOld \<Omega> e n_s v)
  then show ?case
    by (simp add: red_expr_red_exprs.RedOld)
next
  case (RedExpListNil \<Omega> n_s)
  then show ?case
    by (meson red_expr_red_exprs.RedExpListNil)
next
  case (RedExpListCons \<Omega> e n_s v es vs)

  have free_var_e: "free_var_expr e \<inter> ((dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))) \<union> (dom (map_of (snd \<Lambda>)) - dom (map_of (snd \<Lambda>')))) = {}"
    using RedExpListCons.prems(1) by auto

  then have expr: "A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>e,n_s\<rangle> \<Down> v"
    by (simp add: RedExpListCons.IH(2) RedExpListCons.prems(3) assms(1))

  have "\<Union> {free_var_expr e' |e'. e' \<in> set es} \<subseteq> \<Union> {free_var_expr e' |e'. e' \<in> set (e # es)}"
    by auto

  then have "\<Union> {free_var_expr e' |e'. e' \<in> set es} \<inter> ((dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))) \<union> (dom (map_of (snd \<Lambda>)) - dom (map_of (snd \<Lambda>')))) = {}"
    using RedExpListCons.prems(1) boolean_algebra_cancel.inf1 inf.absorb_iff1 inf_bot_right by blast

  then have expr: "A,\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>es,n_s\<rangle> [\<Down>] vs"
    by (simp add: RedExpListCons.IH(4) RedExpListCons.prems(3) assms(1))
  then show ?case
    using expr
    by (simp add: RedExpListCons.IH(2) RedExpListCons.prems(3) assms(1) free_var_e red_expr_red_exprs.RedExpListCons)
next
  case (RedForAllTrue \<Omega> ty e n_s)
  then show ?case
    by (simp add: red_expr_red_exprs.RedForAllTrue)
next
  case (RedForAllFalse v \<Omega> ty e n_s)
  then show ?case
    using free_var_expr.simps(8) red_expr_red_exprs.RedForAllFalse by blast
next
  case (RedExistsTrue v \<Omega> ty e n_s)
  then show ?case
    using free_var_expr.simps(9) red_expr_red_exprs.RedExistsTrue by blast
next
  case (RedExistsFalse \<Omega> ty e n_s)
  then show ?case
    by (simp add: red_expr_red_exprs.RedExistsFalse)
next
  case (RedForallT_True \<Omega> e n_s)
  then show ?case
    by (simp add: inf_set_def red_expr_red_exprs.RedForallT_True)
next
  case (RedForallT_False \<tau> \<Omega> e n_s)
  then show ?case
    by (simp add: red_expr_red_exprs.RedForallT_False)
next
  case (RedExistsT_True \<tau> \<Omega> e n_s)
  then show ?case
    by (simp add: red_expr_red_exprs.RedExistsT_True)
next
  case (RedExistsT_False \<Omega> e n_s)
  then show ?case
    by (simp add: red_expr_red_exprs.RedExistsT_False)
qed



lemma expr_sat_locals_same_value:
  assumes ExprSat: "fst \<Lambda> = fst \<Lambda>'" and
                   "(map_of (snd \<Lambda>) \<subseteq>\<^sub>m map_of (snd \<Lambda>') \<and> free_var_expr e \<inter> ((dom (map_of (snd \<Lambda>'))) - (dom (map_of (snd \<Lambda>)))) = {}) 
                    \<or> (map_of (snd \<Lambda>') \<subseteq>\<^sub>m map_of (snd \<Lambda>) \<and> free_var_expr e \<inter> ((dom (map_of (snd \<Lambda>))) - (dom (map_of (snd \<Lambda>')))) = {})" 
                   "expr_sat A \<Lambda> \<Gamma> \<Omega> s e"
                 shows "expr_sat A \<Lambda>' \<Gamma> \<Omega> s e"
  unfolding expr_sat_def
  apply (rule expr_eval_different_locals_same_value[where ?\<Lambda> = "\<Lambda>"])
     apply (simp add: ExprSat)
  using assms(2) apply auto[1]
  using assms(3) expr_sat_def apply blast
  by (metis Diff_eq_empty_iff Int_Un_distrib Int_empty_right Un_empty_right assms(2) map_le_implies_dom_le)
  








lemma expr_sat_dead_variables:
  assumes ExprSat: "expr_sat A (constants @ global_vars, proc_args proc @ locals @ proc_rets proc) \<Gamma> \<Omega> 
                   ns expr" and
          NoDeadVariables: "(map_of (proc_args proc @ locals @ proc_rets proc) \<subseteq>\<^sub>m map_of (proc_args proc @ locals' @ proc_rets proc) \<and> free_var_expr expr \<inter> (dom (map_of (proc_args proc @ locals' @ proc_rets proc))) - (dom (map_of (proc_args proc @ locals @ proc_rets proc))) = {}) 
                           \<or> (map_of (proc_args proc @ locals' @ proc_rets proc) \<subseteq>\<^sub>m map_of (proc_args proc @ locals @ proc_rets proc) \<and> free_var_expr expr \<inter> (dom (map_of (proc_args proc @ locals @ proc_rets proc))) - (dom (map_of (proc_args proc @ locals' @ proc_rets proc))) = {})"

shows "expr_sat A (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega> ns expr"
  apply (rule expr_sat_locals_same_value[where ?\<Lambda> = "(constants @ global_vars, proc_args proc @ locals @ proc_rets proc)"])
    apply simp
  using NoDeadVariables
   apply simp
  using ExprSat by auto




  


lemma expr_list_sat_dead_variables:
  assumes ExprSat: "expr_all_sat A (constants @ global_vars, proc_args proc @ locals @ proc_rets proc) \<Gamma> \<Omega> ns expr_list" and
          MapLocal: "(map_of locals \<subseteq>\<^sub>m map_of locals' \<and> dom (map_of locals') \<inter> dom (map_of (proc_rets proc)) = {} \<and> free_var_exprlist expr_list \<inter> (dom (map_of (locals'))) - (dom (map_of (locals))) = {}) 
                     \<or> (map_of locals' \<subseteq>\<^sub>m map_of locals \<and> dom (map_of locals) \<inter> dom (map_of (proc_rets proc)) = {} \<and> free_var_exprlist expr_list \<inter> (dom (map_of (locals))) - (dom (map_of (locals'))) = {})"

shows "expr_all_sat A (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega> ns expr_list"
  unfolding expr_all_sat_def list_all_def Ball_def
proof (rule allI | rule impI)+
  fix x
  assume "x \<in> set (expr_list)"
  show "expr_sat A (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega>
          ns x"
  proof (cases "map_of locals \<subseteq>\<^sub>m map_of locals'")
    case True
    have "dom (map_of locals') \<inter> dom (map_of (proc_rets proc)) = {}"
      by (metis MapLocal True map_le_antisym)

    have freeVarList: "free_var_exprlist expr_list \<inter> (dom (map_of (locals'))) - (dom (map_of (locals))) = {}"
      by (metis MapLocal True map_le_antisym)

    hence "free_var_exprlist expr_list \<inter> (dom (map_of (proc_args proc @ locals' @ proc_rets proc))) - (dom (map_of (proc_args proc @ locals @ proc_rets proc))) = {}"
      by auto

    hence freeVar: "free_var_expr x \<inter> (dom (map_of (proc_args proc @ locals' @ proc_rets proc))) - (dom (map_of (proc_args proc @ locals @ proc_rets proc))) = {}"
      using \<open>x \<in> set expr_list\<close> free_var_exprlist.simps
      by (simp add: Int_Diff Sup_inf_eq_bot_iff) 


    have exprSat: "expr_sat A (constants @ global_vars, proc_args proc @ locals @ proc_rets proc) \<Gamma> \<Omega> ns x"
      using ExprSat
      unfolding expr_all_sat_def list_all_def Ball_def
      by (simp add: \<open>x \<in> set expr_list\<close>)

    have MapLe: "map_of (proc_args proc @ locals @ proc_rets proc) \<subseteq>\<^sub>m map_of (proc_args proc @ locals' @ proc_rets proc)"
      by (metis MapLocal True map_le_antisym map_le_append_pre_post)
    
    
    show ?thesis
      apply (rule expr_sat_dead_variables)
       apply (rule exprSat)
      using MapLe freeVar by blast
  next
    case False

    have exprSat: "expr_sat A (constants @ global_vars, proc_args proc @ locals @ proc_rets proc) \<Gamma> \<Omega> ns x"
       using ExprSat
       unfolding expr_all_sat_def list_all_def Ball_def
       by (simp add: \<open>x \<in> set expr_list\<close>)
    have map_of: "map_of (proc_args proc @ locals' @ proc_rets proc) \<subseteq>\<^sub>m map_of (proc_args proc @ locals @ proc_rets proc)"
      using False MapLocal map_le_append_pre_post by blast

    have domain: "dom (map_of locals) \<inter> dom (map_of (proc_rets proc)) = {}"
      using False MapLocal by auto

    have freeVarList: "free_var_exprlist expr_list \<inter> (dom (map_of (locals))) - (dom (map_of (locals'))) = {}"
      by (metis MapLocal False)

    hence "free_var_exprlist expr_list \<inter> (dom (map_of (proc_args proc @ locals @ proc_rets proc))) - (dom (map_of (proc_args proc @ locals' @ proc_rets proc))) = {}"
      by auto

    hence freeVar: "free_var_expr x \<inter> (dom (map_of (proc_args proc @ locals @ proc_rets proc))) - (dom (map_of (proc_args proc @ locals' @ proc_rets proc))) = {}"
      using \<open>x \<in> set expr_list\<close> free_var_exprlist.simps
      by (simp add: Int_Diff Union_disjoint)


    show ?thesis 
      apply (rule expr_sat_dead_variables[where ?locals = "locals"])
       apply (rule exprSat)
      using map_of freeVar by blast
  qed
qed

lemma dom_diff_empty: 
  assumes "A \<subseteq> B"
  shows "A - B = {}"
  by (simp add: assms)



lemma red_cfg_dead_variables_cmd:
  assumes "A,[],\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>c,s\<rangle> \<rightarrow> s'" and
          "fst \<Lambda> = fst \<Lambda>'" and
          MapLocal: "(map_of (snd \<Lambda>) \<subseteq>\<^sub>m map_of (snd \<Lambda>'))" and
          "free_var_cmd c \<inter> ((dom (map_of (snd \<Lambda>'))) - (dom (map_of (snd \<Lambda>)))) = {}" and
          WhereClausesFreeVars: "\<And>x d cond. lookup_var_decl \<Lambda>' x = Some d \<Longrightarrow> snd d = Some cond \<Longrightarrow> free_var_expr cond \<inter> ((dom (map_of (snd \<Lambda>'))) - (dom (map_of (snd \<Lambda>)))) = {} "
        shows "A,[],\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c,s\<rangle> \<rightarrow> s'"
  using assms
proof (induction rule: red_cmd.inducts)
  case (RedAssertOk e n_s)
  have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e,n_s\<rangle> \<Down> BoolV True"
    apply (rule expr_eval_different_locals_same_value[where ?\<Lambda>=\<Lambda>'])
    apply (simp add: assms(2))
    apply (simp add: RedAssertOk.prems(2))
    apply (simp add: RedAssertOk.hyps)
    by (metis Diff_mono RedAssertOk.prems(2) RedAssertOk.prems(3) Un_absorb1 free_var_cmd.simps(1) map_le_implies_dom_le)
  then show ?case
    by (meson red_cmd.RedAssertOk)
next
  case (RedAssertFail e n_s)
  have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e,n_s\<rangle> \<Down> BoolV False"
    apply (rule expr_eval_different_locals_same_value[where ?\<Lambda>=\<Lambda>'])
    apply (simp add: assms(2))
    apply (simp add: RedAssertFail.prems(2))
    apply (simp add: RedAssertFail.hyps)
    by (metis Diff_mono RedAssertFail.prems(2) RedAssertFail.prems(3) Un_absorb1 free_var_cmd.simps(1) map_le_implies_dom_le)
  then show ?case
    by (meson red_cmd.RedAssertFail)
next
  case (RedAssumeOk e n_s)
  have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e,n_s\<rangle> \<Down> BoolV True"
    apply (rule expr_eval_different_locals_same_value[where ?\<Lambda>=\<Lambda>'])
    apply (simp add: assms(2))
    apply (simp add: RedAssumeOk.prems(2))
    apply (simp add: RedAssumeOk.hyps)
    by (metis Diff_eq_empty_iff RedAssumeOk.prems(2) RedAssumeOk.prems(3) boolean_algebra.disj_zero_right free_var_cmd.simps(2) map_le_implies_dom_le sup_commute)
  then show ?case
    by (meson red_cmd.RedAssumeOk)
next
  case (RedAssumeMagic e n_s)
  have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e,n_s\<rangle> \<Down> BoolV False"
    apply (rule expr_eval_different_locals_same_value[where ?\<Lambda>=\<Lambda>'])
    apply (simp add: assms(2))
    apply (simp add: RedAssumeMagic.prems(2))
    apply (simp add: RedAssumeMagic.hyps)
    by (metis Diff_eq_empty_iff RedAssumeMagic.prems(2) RedAssumeMagic.prems(3) boolean_algebra.disj_zero_right free_var_cmd.simps(2) map_le_implies_dom_le sup_commute)
  then show ?case
    by (meson red_cmd.RedAssumeMagic)
next
  case (RedAssign x ty v e n_s)
  hence "x \<notin> (dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>)))"
    by simp

  hence "lookup_var_ty \<Lambda> x  = lookup_var_ty \<Lambda>' x"
    unfolding lookup_var_ty_def lookup_var_decl_def
    using assms
    by (metis (no_types, lifting) DiffI domIff map_le_def)

    
  then have lookupEq: "lookup_var_ty \<Lambda> x = Some ty"
    by (simp add: RedAssign.hyps(1))

  have otherDirEmpty: "(dom (map_of (snd \<Lambda>)) - dom (map_of (snd \<Lambda>'))) = {}"
    apply (rule dom_diff_empty)
    using assms
    by (simp add: map_le_implies_dom_le)

  have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v"
    apply (rule expr_eval_different_locals_same_value[where ?\<Lambda>=\<Lambda>'])
    apply (simp add: assms(2))
    apply (simp add: RedAssign.prems(2))
    apply (simp add: RedAssign.hyps)
    using RedAssign(6) MapLocal
    unfolding free_var_cmd.simps
    by (metis Int_Un_eq(2) Int_commute otherDirEmpty disjoint_insert(2) insert_is_Un)


  then have step: "A,[],\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assign x e,Normal n_s\<rangle> \<rightarrow> Normal (update_var \<Lambda> n_s x v)"
    using lookupEq RedAssign.hyps(2) RedAssign
    by (meson red_cmd.RedAssign)

  have "(update_var \<Lambda> n_s x v) = (update_var \<Lambda>' n_s x v)"
    unfolding update_var_def
    using assms RedAssign.prems(3) free_var_cmd.simps(3)
    by (metis (no_types, lifting) Diff_iff \<open>x \<notin> dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))\<close> domIff map_le_def)
  then show ?case
    using step by auto
next
  case (RedHavocNormal x ty w v n_s)

  hence "x \<notin> (dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>)))"
    by simp

  hence lookupVarEq: "lookup_var_decl \<Lambda> x = lookup_var_decl \<Lambda>' x"
    unfolding lookup_var_ty_def lookup_var_decl_def
    using assms
    by (metis (no_types, lifting) Diff_iff domIff map_le_def)

  have otherDirEmpty: "(dom (map_of (snd \<Lambda>)) - dom (map_of (snd \<Lambda>'))) = {}"
    apply (rule dom_diff_empty)
    using assms
    by (simp add: map_le_implies_dom_le)

  have updVarEq:"(update_var \<Lambda> n_s x v) = (update_var \<Lambda>' n_s x v)"
    unfolding update_var_def
    using assms RedHavocNormal.prems(3) free_var_cmd.simps(3)
    by (metis (no_types, lifting) Diff_iff \<open>x \<notin> dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))\<close> domIff map_le_def)

  have step: "\<And>cond. w = Some cond \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cond, (update_var \<Lambda> n_s x v)\<rangle> \<Down> BoolV True"
  proof -
    fix cond
    assume "w = Some cond"
    hence "free_var_expr cond \<inter> (dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))) = {}"
      using RedHavocNormal.hyps(1) WhereClausesFreeVars by auto
    show "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cond, (update_var \<Lambda> n_s x v)\<rangle> \<Down> BoolV True"
      apply (rule expr_eval_different_locals_same_value[where ?\<Lambda>=\<Lambda>'])
      apply (simp add: assms(2))
      apply (simp add: RedHavocNormal.prems(2))
      using RedHavocNormal.hyps(3)[OF \<open>w = Some cond\<close>]
      apply (simp add: updVarEq)
      by (simp add: \<open>free_var_expr cond \<inter> (dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))) = {}\<close> otherDirEmpty)
  qed


  then show ?case
    using updVarEq RedHavocNormal
    by (metis local.step lookupVarEq red_cmd.RedHavocNormal)
next
  case (RedHavocMagic x ty cond v n_s)
  hence "x \<notin> (dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>)))"
    by simp
  have lokupVarDecl: "lookup_var_decl \<Lambda> x = Some (ty,Some(cond))"
    unfolding lookup_var_ty_def lookup_var_decl_def
    using assms
    by (metis (no_types, lifting) Int_Diff Int_insert_left_if1 RedHavocMagic.hyps(1) RedHavocMagic.prems(3) domIff free_var_cmd.simps(4) insert_Diff_if insert_not_empty lookup_var_decl_def map_le_def)

  have updateEqual: "(update_var \<Lambda> n_s x v) = (update_var \<Lambda>' n_s x v)"
    unfolding update_var_def
    using assms RedHavocMagic.prems(3) free_var_cmd.simps(3)
    by (metis (no_types, lifting) Diff_iff \<open>x \<notin> dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))\<close> domIff map_le_def)

  have otherDirEmpty: "(dom (map_of (snd \<Lambda>)) - dom (map_of (snd \<Lambda>'))) = {}"
    apply (rule dom_diff_empty)
    using assms
    by (simp add: map_le_implies_dom_le)
  
  have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cond, (update_var \<Lambda> n_s x v)\<rangle> \<Down> BoolV False"
    apply (rule expr_eval_different_locals_same_value[where ?\<Lambda>=\<Lambda>'])
    apply (simp add: assms(2))
    apply (simp add: RedHavocMagic.prems(2))
    using updateEqual RedHavocMagic.hyps(3) apply simp
    using assms RedHavocMagic otherDirEmpty
    by (metis Int_Un_eq(2) snd_eqD)

    
  then show ?case 
    using RedHavocMagic.hyps(2) red_cmd.RedHavocMagic lokupVarDecl by blast
next
  case (RedProcCallOkAndMagic m msig args n_s v_args pre_ls new_ls ty_modifs vs_modifs vs_ret post_ls post_gs post_state post_success post_fail n_s' rets)
  then show ?case 
    by simp
next
  case (RedProcCallFail m msig args n_s v_args pre_ls new_ls rets)
  then show ?case 
    by simp
next
  case (RedPropagateMagic s)
  then show ?case
    by (simp add: red_cmd.RedPropagateMagic)
next
  case (RedPropagateFailure s)
  then show ?case
    by (simp add: red_cmd.RedPropagateFailure)
qed
  

lemma red_cfg_dead_variables_cmdlist:
assumes oneStep: "A,[],\<Lambda>',\<Gamma>,\<Omega> \<turnstile> \<langle>cs,s\<rangle> [\<rightarrow>] s'" and
        "fst \<Lambda> = fst \<Lambda>'" and
        MapLocal: "(map_of (snd \<Lambda>) \<subseteq>\<^sub>m map_of (snd \<Lambda>'))" and 
        freeVarCmdList: "free_var_cmdlist cs \<inter> ((dom (map_of (snd \<Lambda>'))) - (dom (map_of (snd \<Lambda>)))) = {}" and 
        WhereClausesFreeVars: "\<And>x d cond. lookup_var_decl \<Lambda>' x = Some d \<Longrightarrow> snd d = Some cond \<Longrightarrow> free_var_expr cond \<inter> ((dom (map_of (snd \<Lambda>'))) - (dom (map_of (snd \<Lambda>)))) = {} "
      shows "A,[],\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,s\<rangle> [\<rightarrow>] s'"
  using oneStep freeVarCmdList
proof (induction rule: red_cmd_list.inducts)
  case (RedCmdListNil s)
  then show ?case
    by (meson red_cmd_list.RedCmdListNil)
next
  case (RedCmdListCons c s s'' cs' s')
  have freeVarSingleCmd: "free_var_cmd c \<inter> (dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))) = {}"
    using RedCmdListCons(4)
    unfolding free_var_cmdlist.simps
    by auto

  have oneStep: "A,[],\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c,s\<rangle> \<rightarrow> s''"
    apply (rule red_cfg_dead_variables_cmd[OF RedCmdListCons(1) assms(2) MapLocal freeVarSingleCmd])
    using WhereClausesFreeVars
    by simp

  have "free_var_cmdlist cs' \<inter> (dom (map_of (snd \<Lambda>')) - dom (map_of (snd \<Lambda>))) = {}"
    using RedCmdListCons(4)
    unfolding free_var_cmdlist.simps
    by auto

  have "A,[],\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs',s''\<rangle> [\<rightarrow>] s'"
    using RedCmdListCons.IH 
    sorry (*Why doesn't this hold trivially? Shouldn't it directly follow from the implication?*)

  
    
  then show ?case
    using oneStep red_cmd_list.RedCmdListCons by blast
qed

lemma red_cfg_dead_variables_cmdlist_onestep:
  assumes oneStep: "A,[],\<Lambda>',\<Gamma>,\<Omega>,body \<turnstile>(Inl m, Normal ns) -n\<rightarrow> (m', s')" and
          fstEq: "fst \<Lambda> = fst \<Lambda>'" and
          MapLocal: "(map_of (snd \<Lambda>) \<subseteq>\<^sub>m map_of (snd \<Lambda>'))" and
          NoDeadVariables: "free_var_cmdlist (node_to_block body ! m) \<inter> ((dom (map_of (snd \<Lambda>'))) - (dom (map_of (snd \<Lambda>)))) = {}" and
          WhereClausesFreeVars: "\<And>x d cond. lookup_var_decl \<Lambda>' x = Some d \<Longrightarrow> snd d = Some cond \<Longrightarrow> free_var_expr cond \<inter> ((dom (map_of (snd \<Lambda>'))) - (dom (map_of (snd \<Lambda>)))) = {} "
        shows   "A,[],\<Lambda>,\<Gamma>,\<Omega>,body \<turnstile>(Inl m, Normal ns) -n\<rightarrow> (m', s')"
  using assms
proof cases
  case (RedNormalSucc cs ns' n')
  have "A,[],\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns\<rangle> [\<rightarrow>] Normal ns'"
    apply (rule red_cfg_dead_variables_cmdlist[OF RedNormalSucc(4) fstEq MapLocal _ WhereClausesFreeVars])
    using NoDeadVariables local.RedNormalSucc(3) by auto

  then show ?thesis
    using local.RedNormalSucc(1) local.RedNormalSucc(2) local.RedNormalSucc(3) local.RedNormalSucc(5) red_cfg.RedNormalSucc by blast
next
  case (RedNormalReturn cs ns')
  have "A,[],\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns\<rangle> [\<rightarrow>] Normal ns'"
    apply (rule red_cfg_dead_variables_cmdlist[OF RedNormalReturn(4) fstEq MapLocal _ WhereClausesFreeVars])
    using NoDeadVariables local.RedNormalReturn(3) by auto

  then show ?thesis
    using local.RedNormalReturn(1) local.RedNormalReturn(2) local.RedNormalReturn(3) local.RedNormalReturn(5) red_cfg.RedNormalReturn by blast
next
  case (RedFailure cs)
  have "A,[],\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns\<rangle> [\<rightarrow>] Failure"
    apply (rule red_cfg_dead_variables_cmdlist[OF RedFailure(4) fstEq MapLocal _ WhereClausesFreeVars])
    using NoDeadVariables local.RedFailure(3) by auto
  then show ?thesis
    using local.RedFailure(1) local.RedFailure(2) local.RedFailure(3) red_cfg.RedFailure by blast
next
  case (RedMagic cs)
  have "A,[],\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns\<rangle> [\<rightarrow>] Magic"
    apply (rule red_cfg_dead_variables_cmdlist[OF RedMagic(4) fstEq MapLocal _ WhereClausesFreeVars])
    using NoDeadVariables local.RedMagic(3) by auto
  then show ?thesis
    using local.RedMagic(1) local.RedMagic(2) local.RedMagic(3) red_cfg.RedMagic by blast
qed


lemma list_member_proof: 
  assumes "ls ! i = ele" and
          "i < length ls"
  shows "List.member (ls) ele "
  using assms
proof -
  have "ele \<in> set ls"
    using assms(2) assms(1) nth_mem by blast
  then show "List.member ls ele"
    by (simp add: in_set_member)
qed

lemma red_cfg_multi_dead_variables:
  assumes RedCfg: "A,[],(constants @ global_vars, proc_args proc @ locals' @ proc_rets proc),\<Gamma>,\<Omega>,body \<turnstile>(Inl m, Normal ns) -n\<rightarrow>* (m', s')" and
          MapLocal: "map_of locals \<subseteq>\<^sub>m map_of locals'" and
          DomLocalInterRetsEmpty:   "dom (map_of locals') \<inter> dom (map_of (proc_rets proc)) = {}" and
          NoDeadVariables: "\<forall>b\<in>set(node_to_block body). free_var_cmdlist b \<inter> (dom (map_of locals') - (dom (map_of locals))) = {}" and
          WhereClausesFreeVars: "\<And>x d cond. lookup_var_decl (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) x = Some d \<Longrightarrow> snd d = Some cond \<Longrightarrow> free_var_expr cond \<inter> ((dom (map_of (snd (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc)))) - (dom (map_of (snd (constants @ global_vars, proc_args proc @ locals @ proc_rets proc))))) = {} "
        shows   "A,[],(constants @ global_vars, proc_args proc @ locals @ proc_rets proc),\<Gamma>,\<Omega>,body \<turnstile>(Inl m, Normal ns) -n\<rightarrow>* (m', s')"
  using RedCfg 
proof (induction rule: converse_rtranclp_induct2)
  case refl
  then show ?case 
    by simp
next
  case (step a b c d)
  have restSteps: "A,[],(constants @ global_vars, proc_args proc @ locals @ proc_rets proc),\<Gamma>,\<Omega>,body \<turnstile>(c, d) -n\<rightarrow>* (m', s')"
    using step.IH  by simp
  from step show ?case
  proof cases
    case (RedNormalSucc n cs ns ns' n')
    have oneStepLocals':"A,[],(constants @ global_vars, proc_args proc @ locals' @ proc_rets proc),\<Gamma>,\<Omega>,body \<turnstile> (Inl n, Normal ns) -n\<rightarrow> (c, d)"
      using local.RedNormalSucc(1) local.RedNormalSucc(2) step.hyps(1) by auto

    have nInBody: "cs \<in> set(node_to_block body)"
      sorry
    

    have temp: "dom (map_of (proc_args proc @ locals' @ proc_rets proc)) - dom (map_of (proc_args proc @ locals @ proc_rets proc)) = dom (map_of locals') - (dom (map_of locals))"
      using DomLocalInterRetsEmpty
      sorry


    have "A,[],(constants @ global_vars, proc_args proc @ locals @ proc_rets proc),\<Gamma>,\<Omega>,body \<turnstile> (Inl n, Normal ns) -n\<rightarrow> (c, d)"
      apply (rule red_cfg_dead_variables_cmdlist_onestep[OF oneStepLocals'])
      apply (simp)
      using MapLocal map_le_append_pre_post DomLocalInterRetsEmpty apply auto[1]
      using NoDeadVariables local.RedNormalSucc(5) nInBody apply auto[1]
      using WhereClausesFreeVars by simp

    then show ?thesis 
      by (simp add: converse_rtranclp_into_rtranclp local.RedNormalSucc(1) local.RedNormalSucc(2) restSteps)
  next
    case (RedNormalReturn n cs ns ns')
    then show ?thesis sorry
  next
    case (RedFailure n cs ns)
    then show ?thesis sorry
  next
    case (RedMagic n cs ns)
    then show ?thesis sorry
  qed
qed


subsection \<open>Dead variables elimination lemma\<close>

lemma elimination:
  assumes proc_cor: "proc_is_correct A fun_decls constants global_vars axioms proc Semantics.proc_body_satisfies_spec" and
          Body1: "proc_body proc = Some (locals, body)" and
          Body2: "proc' = proc \<lparr>proc_body := Some (locals', body)\<rparr>" and
          LocalVariables: "map_of locals \<subseteq>\<^sub>m map_of locals'" and 
          FreeVarPres: "free_var_exprlist (proc_all_pres proc) \<inter> dom (map_of locals') - dom (map_of locals) = {}" and
          FreeVarPosts: "free_var_exprlist (proc_checked_posts proc) \<inter> dom (map_of locals') - dom (map_of locals) = {}" and
          DeadVariables: "\<forall>b\<in>set(node_to_block body). free_var_cmdlist b \<inter> (dom (map_of locals') - (dom (map_of locals))) = {}" and
                 \<comment>\<open>The following assumption is needed to lift \<^term>\<open>map_of locals \<subseteq>\<^sub>m map_of locals'\<close>
                    to the concatenation of all variables in the local state (arguments, locals, return variables)\<close>
          DomLocalInterRetsEmpty: "dom (map_of locals') \<inter> dom (map_of (proc_rets proc)) = {}" and
          WhereClausesFreeVars: "\<And>x d cond. lookup_var_decl (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) x = Some d \<Longrightarrow> snd d = Some cond \<Longrightarrow> free_var_expr cond \<inter> ((dom (map_of (snd (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc)))) - (dom (map_of (snd (constants @ global_vars, proc_args proc @ locals @ proc_rets proc))))) = {} "
        shows "proc_is_correct A fun_decls constants global_vars axioms proc' Semantics.proc_body_satisfies_spec"
proof (simp add: Body2 del: proc_checked_posts.simps, (rule impI | rule allI)+)
  fix \<Gamma> \<Omega> gs ls
  assume  Atyp: "(\<forall>t. closed t \<longrightarrow> (\<exists>v. type_of_val A v = t)) \<and> (\<forall>v. closed (type_of_val A v))" and
          FunWf:"fun_interp_wf A fun_decls \<Gamma>" and
          ARenv: "list_all closed \<Omega> \<and> length \<Omega> = proc_ty_args proc" and
          WfGlobal: "state_typ_wf A \<Omega> gs (constants @ global_vars)" and
          WfLocal: "state_typ_wf A \<Omega> ls (proc_args proc @ locals' @ proc_rets proc)" and 
          AxSat: "axioms_sat A (constants, []) \<Gamma>
                      \<lparr>old_global_state = Map.empty, global_state = state_restriction gs constants, local_state = Map.empty,
                      binder_state = Map.empty\<rparr> axioms"
  show  "proc_body_satisfies_spec A [] (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega>
        (map fst (proc_pres proc)) (proc_checked_posts (proc\<lparr>proc_body := Some (locals', body)\<rparr>)) body
        \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr>"
    unfolding proc_body_satisfies_spec_def
  proof ((rule impI | rule allI)+)
    fix m' s'
    assume ExprAllSat: "expr_all_sat A (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega>
        \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> (map fst (proc_pres proc))" and
           GoesTo: "A,[],(constants @ global_vars, proc_args proc @ locals' @ proc_rets proc),\<Gamma>,\<Omega>,body \<turnstile>(Inl (entry body),
                                Normal \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr>) -n\<rightarrow>* (m', s')"
    show "valid_configuration A (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega>
        (proc_checked_posts (proc\<lparr>proc_body := Some (locals', body)\<rparr>)) m' s'"
      unfolding valid_configuration_def
    proof -

      have valid_proc: "valid_configuration A (constants @ global_vars, proc_args proc @ locals @ proc_rets proc) \<Gamma> \<Omega> ((proc_checked_posts proc)) m' s'"
      proof (rule validConf [OF proc_cor Body1 Atyp FunWf ARenv WfGlobal])
        show "state_typ_wf A \<Omega> ls (proc_args proc @ locals @ proc_rets proc)"
          using state_typ_wf_map_le[OF WfLocal LocalVariables] DomLocalInterRetsEmpty
          by blast
      next
        show "axioms_sat A (constants, []) \<Gamma> (global_to_nstate (state_restriction gs constants)) axioms"
          using AxSat
          by simp
      next
        show "expr_all_sat A (constants @ global_vars, proc_args proc @ locals @ proc_rets proc) \<Gamma> \<Omega>
             \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> (proc_all_pres proc)"
        proof -
          have "expr_all_sat A (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega>
               \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> (proc_all_pres proc)"
            using ExprAllSat
            by simp

          thus "expr_all_sat A (constants @ global_vars, proc_args proc @ locals @ proc_rets proc) \<Gamma> \<Omega>
             \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> (proc_all_pres proc)"
            apply (rule expr_list_sat_dead_variables)
            using LocalVariables FreeVarPres DomLocalInterRetsEmpty by blast
        qed

      next
        show "A,[],(constants @ global_vars, proc_args proc @ locals @ proc_rets proc),\<Gamma>,\<Omega>,body \<turnstile>(Inl (entry body), Normal
              \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr>) -n\<rightarrow>* (m', s')"
          by (rule red_cfg_multi_dead_variables[OF GoesTo LocalVariables DomLocalInterRetsEmpty DeadVariables WhereClausesFreeVars])
      qed
       
       
      hence notFailure: "s' \<noteq> Failure"
        using valid_configuration_def by blast

      have FinalConfig: "(is_final_config (m', s') \<longrightarrow> (\<forall>ns'. s' = Normal ns' \<longrightarrow> 
                        expr_all_sat A (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega> ns' (proc_checked_posts (proc\<lparr>proc_body := Some (locals', body)\<rparr>))))" 
            (is "?isFinal \<longrightarrow> (\<forall>ns'. ?isNormal ns' \<longrightarrow> ?Goal ns')")
      proof ((rule impI | rule allI)+)
        fix ns'
        assume "?isFinal" and "?isNormal ns'" 
        show "?Goal ns'"
        proof -
          
          have EqPosts: "(proc_checked_posts proc) = (proc_checked_posts (proc\<lparr>proc_body := Some (locals', body)\<rparr>))"
            sorry

          have "expr_all_sat A (constants @ global_vars, proc_args proc @ locals @ proc_rets proc) \<Gamma> \<Omega> ns' (proc_checked_posts proc)"
            using valid_proc 
            unfolding valid_configuration_def
            using \<open>is_final_config (m', s')\<close> \<open>s' = Normal ns'\<close> by blast


          hence "expr_all_sat A (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega> ns' (proc_checked_posts proc)"
            apply (rule expr_list_sat_dead_variables)
            using LocalVariables FreeVarPosts DomLocalInterRetsEmpty by blast

            

          thus "expr_all_sat A (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega> ns' (proc_checked_posts (proc\<lparr>proc_body := Some (locals', body)\<rparr>))"
            using EqPosts
            by argo
        qed
      qed
      thus "s' \<noteq> Failure \<and> (is_final_config (m', s') \<longrightarrow> (\<forall>ns'. s' = Normal ns' \<longrightarrow>
            expr_all_sat A (constants @ global_vars, proc_args proc @ locals' @ proc_rets proc) \<Gamma> \<Omega> ns' (proc_checked_posts (proc\<lparr>proc_body := Some (locals', body)\<rparr>))))"
        using notFailure by blast
    qed
  qed
qed

end