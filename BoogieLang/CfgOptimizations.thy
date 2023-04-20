theory CfgOptimizations
  imports Boogie_Lang.Semantics Boogie_Lang.Util "../global_data"
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


subsection \<open>Main lemmas\<close>

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

text \<open>The following lemma shows that if in a block the global block lemma holds for all successors and the block was not coalesced, then the global block lemma holds\<close>

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
    case (2 b s0)
    from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, Normal ns) -n\<rightarrow> (b, s0)\<close> have OneStepResult: "s0 \<noteq> Failure"
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
    proof (cases "s0 = Magic")
      case True
      thus "s' \<noteq> Failure"
        using "2"(2) red_cfg_magic_preserved by blast
    next
      case False

      from this obtain ns0 where "s0 = Normal ns0"
        using OneStepResult state.exhaust by blast

      show ?thesis
      proof (cases "ls = []")
        case True
        hence "(m', s') = (Inl src_block, Normal ns) \<or> m' = Inr()"
          by (smt (verit) "2"(1) "2"(2) SuccBlocks finished_remains no_out_edges_return old.unit.exhaust sumE)
        then show ?thesis
          by (smt (verit) "2"(1) "2"(2) OneStepResult Pair_inject SuccBlocks True finished_remains no_out_edges_return red_cfg.simps)
      next
        case False

        from this obtain succ where cond: "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, Normal ns) -n\<rightarrow> (Inl succ, Normal ns0)) \<and> (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl succ, Normal ns0) -n\<rightarrow>* (m',s'))" 
          by (smt (verit) "2"(1) "2"(2) Inl_inject OneStepResult Pair_inject SuccBlocks \<open>s0 = Normal ns0\<close> red_cfg.cases state.distinct(3))


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
              by (metis FunctionCorr NotCoalesced RedNormalSucc RedNormalSucc_case SourceBlock SuccBlocks TargetBlock cond in_set_member)
            hence "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl tgt_block, Normal ns) -n\<rightarrow>* (m1', s1'))"
              by (simp add: \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl (f succ), Normal ns0) -n\<rightarrow>* (m1', s1')\<close> converse_rtranclp_into_rtranclp)
            then show ?thesis
              by (simp add: TargetVerifies)
          qed
        qed

        hence "global_block_lemma A M \<Lambda> \<Gamma> \<Omega> G G' succ (f(succ))"
          by (metis GlobalBlockSucc RedNormalSucc_case SuccBlocks cond in_set_member)

        thus "s'\<noteq>Failure"
          using cond_global_block cond
          unfolding global_block_lemma_def
          by blast
      qed
    qed
  qed
qed

text \<open>The following lemma shows that if in a block the global block lemma holds for all successors and the block was coalesced, then the hybrid block lemma holds\<close>

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
    case (2 b s0)
    from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, Normal ns) -n\<rightarrow> (b, s0)\<close> have OneStepResult: "s0 \<noteq> Failure"
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
    proof (cases "s0 = Magic")
      case True
      then show ?thesis
        using "2"(2) red_cfg_magic_preserved by blast
    next
      case False
      from this obtain ns0 where "s0 = Normal ns0"
        using OneStepResult state.exhaust by blast
      show ?thesis
      proof (cases "ls = []")
        case True
        hence "(m', s') = (Inl src_block, Normal ns) \<or> m' = Inr()"
          by (smt (verit) "2"(1) "2"(2) SuccBlocks finished_remains no_out_edges_return prod.inject red_cfg.cases)
        then show ?thesis
          by (smt (verit) "2"(1) "2"(2) OneStepResult Pair_inject SuccBlocks True finished_remains no_out_edges_return red_cfg.cases)
      next
        case False

        from this obtain succ where cond: "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, Normal ns) -n\<rightarrow> (Inl succ, Normal ns0)) \<and> (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl succ, Normal ns0) -n\<rightarrow>* (m',s'))"
          by (smt (verit) "2"(1) "2"(2) Inl_inject Pair_inject SourceBlock SuccBlocks TargetVerifies \<open>s0 = Normal ns0\<close> hybrid_block_lemma_target_verifies_def red_cfg.simps state.distinct(3))

        hence "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>src_cmds,Normal ns\<rangle> [\<rightarrow>] Normal ns0"
          using RedNormalSucc_case SourceBlock by blast

        have cond_global_block: "\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile> (Inl (f(succ)), (Normal ns0)) -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure"
          using GlobalBlockSucc TargetVerifies
          unfolding hybrid_block_lemma_target_verifies_def global_block_lemma_def hybrid_block_lemma_target_succ_verifies_def
          by (metis FunctionCorr RedNormalSucc_case SuccBlocks \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>src_cmds,Normal ns\<rangle> [\<rightarrow>] Normal ns0\<close> cond in_set_member)

        hence "global_block_lemma A M \<Lambda> \<Gamma> \<Omega> G G' succ (f(succ))"
          by (metis GlobalBlockSucc RedNormalSucc_case SuccBlocks cond in_set_member)
        then show ?thesis
          using cond global_block_lemma_def cond_global_block by blast
      qed

    qed
  qed

qed



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
    then show ?thesis
    proof (cases "(Assume (Lit (LBool False))) \<in> set (src_cmds)")
      case True
      hence  "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>src_cmds,Normal ns\<rangle> [\<rightarrow>] s'"
        by (smt (verit) "2"(1) "2"(2) Inl_inject Pair_inject SourceBlock converse_rtranclpE magic_lemma_assume_false red_cfg.simps state.distinct(1) state.distinct(3))
      hence "s' = Magic"
        using magic_lemma_assume_false
        by (metis NotCoalesced RedFailure TargetBlock TargetVerifies True r_into_rtranclp)
      then show ?thesis 
        by simp
    next
      case False
      hence "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>src_cmds,Normal ns\<rangle> [\<rightarrow>] s'"
        by (smt (verit) "2"(1) "2"(2) Inl_inject Pair_inject Pruning SourceBlock converse_rtranclpE magic_lemma_assert_false red_cfg.simps state.distinct(1) state.distinct(3))
      hence "s' = Magic \<or> s' = Failure" using magic_lemma_assert_false False Pruning 
        by blast
      then show ?thesis
        using NotCoalesced RedFailure TargetBlock TargetVerifies \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>src_cmds,Normal ns\<rangle> [\<rightarrow>] s'\<close> by blast
    qed
  qed
qed

lemma pruning_coalesced:
  assumes SuccBlocks: "out_edges G ! src_block = ls" and
          TargetBlock: "node_to_block G' ! tgt_block = tgt_cmds" and
          SourceBlock: "node_to_block G ! src_block = src_cmds" and
          Pruning: "(Assert (Lit (LBool False))) \<in> set (src_cmds)" and
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
    then show ?thesis
    proof (cases "(Assume (Lit (LBool False))) \<in> set (src_cmds)")
      case True
      have "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>src_cmds,Normal ns\<rangle> [\<rightarrow>] s'"
        by (smt (verit) "2"(1) "2"(2) Inl_inject Pair_inject Pruning SourceBlock converse_rtranclpE magic_lemma_assert_false red_cfg.simps state.distinct(1) state.distinct(3))
      hence "s' = Magic"
        using TargetVerifies True hybrid_block_lemma_target_verifies_def magic_lemma_assume_false by blast
      then show ?thesis
        by simp
    next
      case False
      have "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>src_cmds,Normal ns\<rangle> [\<rightarrow>] s'"
        by (smt (verit) "2"(1) "2"(2) Inl_inject Pair_inject Pruning SourceBlock converse_rtranclpE magic_lemma_assert_false red_cfg.simps state.distinct(1) state.distinct(3))
      hence "s' = Magic \<or> s' = Failure" using magic_lemma_assert_false Pruning 
        by blast
      then show ?thesis using Coalesced RedFailure TargetBlock TargetVerifies \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>src_cmds,Normal ns\<rangle> [\<rightarrow>] s'\<close>
        by (simp add: hybrid_block_lemma_target_verifies_def)
    qed
  qed
qed


term "global_data.fdecls"

end