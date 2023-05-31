theory CfgOptimizationsLoop
  imports Boogie_Lang.Semantics Boogie_Lang.Util CfgOptimizations
begin



subsection \<open>Definition loop induction hypothesis and global block Lemma for blocks in a loop\<close>

definition loop_ih_optimizations
  where "loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHeader LoopHeader'  m' s' j \<equiv> 
          \<forall>j' ns1'. ((j' \<le> j) \<longrightarrow> 
                     (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl LoopHeader, Normal ns1') -n\<rightarrow>^j' (m', s')) \<longrightarrow>
         (\<forall>m1' s1'.( A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl LoopHeader', Normal ns1') -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure) \<longrightarrow>
                     s' \<noteq> Failure)"



definition global_block_lemma_loop
  where "global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block lsLoopHead \<equiv> 
          \<forall>m' ns s' j.  
             (red_cfg_k_step A M \<Lambda> \<Gamma> \<Omega> G ((Inl src_block),(Normal ns)) j (m',s')) \<longrightarrow>
             (\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile> (Inl tgt_block, (Normal ns)) -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure) \<longrightarrow>
             (\<forall>(LoopHead,LoopHead')\<in>lsLoopHead. loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead'  m' s' j) \<longrightarrow>
             s' \<noteq> Failure"

definition hybrid_block_lemma_loop
  where "hybrid_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block tgt_cmds lsLoopHead\<equiv> 
          \<forall>m' ns s' j.  
             (red_cfg_k_step A M \<Lambda> \<Gamma> \<Omega> G ((Inl src_block),(Normal ns)) j (m',s')) \<longrightarrow>
             hybrid_block_lemma_target_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block tgt_cmds ns \<longrightarrow>
             (\<forall>(LoopHead,LoopHead')\<in>lsLoopHead. loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead'  m' s' j) \<longrightarrow>
             s' \<noteq> Failure"


subsection \<open>Helper Lemmas\<close>

lemma target_verifies: 
  assumes oneStep: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl a, Normal ns) -n\<rightarrow> (Inl b, Normal ns')" and
          cmd: "node_to_block(G) ! a = node_to_block(G') ! c" and
          targetVerifies: "(\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl c, Normal ns) -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure)" and
          member: "List.member (out_edges(G') ! c) d"
        shows "\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G'\<turnstile>(Inl d, Normal ns') -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure"
proof -
  have "A,M,\<Lambda>,\<Gamma>,\<Omega>,G'  \<turnstile> (Inl c, Normal ns) -n\<rightarrow> (Inl d, Normal ns')"
    using oneStep cmd
    apply (cases)
    by (simp add: RedNormalSucc cmd member)

  then show ?thesis 
    by (meson targetVerifies converse_rtranclp_into_rtranclp)
qed

lemma one_step_not_failure:
  assumes "(\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl a, Normal ns) -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure)" and
          "node_to_block G ! b = node_to_block G' ! a" and
          "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl b, Normal ns) -n\<rightarrow> (c, d)"
        shows "d \<noteq> Failure"
  using assms(3)
proof cases
  case (RedNormalSucc cs ns' n')
  then show ?thesis by auto
next
  case (RedNormalReturn cs ns')
  then show ?thesis by auto
next
  case (RedFailure cs)
  then show ?thesis
    by (metis assms(1) assms(2) r_into_rtranclp red_cfg.RedFailure)
next
  case (RedMagic cs)
  then show ?thesis by auto
qed

lemma hybrid_block_lemma_loop_elim:
  assumes "hybrid_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block tgt_cmds lsLoopHead" and
          "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, (Normal ns)) -n\<rightarrow>^j (m', s')" and
          "hybrid_block_lemma_target_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block tgt_cmds ns" and 
          "\<forall>(LoopHead, LoopHead')\<in>lsLoopHead. loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead' m' s' j"
  shows "s' \<noteq> Failure"
  using assms
  unfolding hybrid_block_lemma_loop_def
  by blast

lemma loop_ih_optimizations_one_less:
  assumes "loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead' m' s' j"
  shows "loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead' m' s' (j-1)"
  using assms
  unfolding loop_ih_optimizations_def
  by (meson diff_le_self le_trans)

lemma loop_ih_optimizations_more_less:
  assumes "loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead' m' s' j" and
          "j' \<le> j"
  shows "loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead' m' s' j'"
  using assms
  unfolding loop_ih_optimizations_def
  by (meson diff_le_self le_trans)


lemma loop_global_block_subset: 
  assumes "global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block lsSubset" and
          "(lsSubset) \<subseteq> (lsLoopHead)"
     shows "global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block lsLoopHead"
  using assms
  unfolding global_block_lemma_loop_def
  by blast

lemma normal_target_verfies_show_hybrid_verifies:
  assumes TargetVerifies: "\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl tgt_block, Normal ns) -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure" and
          TgtCmds: "node_to_block G' ! tgt_block = tgt_cmds"
        shows "hybrid_block_lemma_target_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block tgt_cmds ns"
  unfolding hybrid_block_lemma_target_verifies_def hybrid_block_lemma_target_succ_verifies_def
proof (rule allI | rule impI)+
  fix s1'
  assume oneStep: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>tgt_cmds,Normal ns\<rangle> [\<rightarrow>] s1'"
  show "(s1' \<noteq> Failure) \<and> (\<forall>ns1'. s1' = Normal ns1' \<longrightarrow> (\<forall>target_succ. List.member (out_edges(G') ! tgt_block) target_succ \<longrightarrow> (\<forall>m2' s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile> (Inl target_succ, (Normal  ns1')) -n\<rightarrow>* (m2', s2')) \<longrightarrow> s2' \<noteq> Failure)))"
  proof -
    have "s1' \<noteq> Failure"
      using TargetVerifies
      using RedFailure TgtCmds oneStep by blast
    have "(\<forall>ns1'. s1' = Normal ns1' \<longrightarrow> (\<forall>target_succ. List.member (out_edges(G') ! tgt_block) target_succ \<longrightarrow> (\<forall>m2' s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile> (Inl target_succ, (Normal  ns1')) -n\<rightarrow>* (m2', s2')) \<longrightarrow> s2' \<noteq> Failure)))"
      by (metis (no_types, lifting) RedNormalSucc TargetVerifies TgtCmds converse_rtranclp_into_rtranclp oneStep)
    then show ?thesis
      using \<open>s1' \<noteq> Failure\<close> by blast
  qed
qed




subsection \<open>Main Lemmas for Loops\<close>

subsubsection \<open>Main Lemma 1: Shows that the Loop Global Block Lemma holds if for all successors either the global 
              block lemma holds or there exists a pair of Loop Headers such that the Loop global block 
              lemma holds or the successor is equal to one of the Loop Heads\<close>

lemma loopBlock_global_block:
  assumes   SuccBlocks: "out_edges G ! src_block = ls" and
          GlobalBlockSucc: "\<forall>x\<in>set(ls).(\<exists>lsSubsetList. lsSubsetList\<subseteq>lsLoopHead \<and> global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' x (f(x)) lsSubsetList) \<or> (\<exists>(LoopHead, LoopHead')\<in>lsLoopHead. (x = LoopHead \<and> f(x) = LoopHead'))" and
          FunctionCorr: "\<forall>x\<in>set(ls). f(x)\<in>set(out_edges G' ! tgt_block)" and
          TargetBlock: "node_to_block G' ! tgt_block = tgt_cmds" and
          SourceBlock: "node_to_block G ! src_block = src_cmds" and
          NotCoalesced: "tgt_cmds = src_cmds"
        shows     "global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block lsLoopHead"
  unfolding global_block_lemma_loop_def
proof (rule allI | rule impI)+
  fix m' ns s' j
  assume k_step: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block, Normal ns) -n\<rightarrow>^j (m', s')" and
         IH: "\<forall>(LoopHead, LoopHead')\<in>lsLoopHead. loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead' m' s' j" and
         TargetVerifies: "(\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl tgt_block, Normal ns) -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure)"
  show   "s' \<noteq> Failure "
  proof (cases rule: relpowp_E2_2[OF k_step])
    case 1
    then show ?thesis 
      by blast
  next
    case (2 a b m)
    have OneStepResult: "b \<noteq> Failure"
      apply (rule one_step_not_failure[where ?G = G and ?b = src_block and ?c = a])
      apply (rule TargetVerifies)
      apply (simp add: NotCoalesced SourceBlock TargetBlock)
      by (simp add: "2"(2))
    then show ?thesis 
    proof (cases "b = Magic")
      case True
      have "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(a, b) -n\<rightarrow>* (m', s')"
        by (meson "2"(3) rtranclp_power)
      then show ?thesis
        using True red_cfg_magic_preserved by blast
    next
      case False
      from this obtain ns1 where "b = Normal ns1"
        using OneStepResult state.exhaust by blast
      from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, Normal ns) -n\<rightarrow> (a, b)\<close> show ?thesis
      proof cases
        case (RedNormalSucc cs ns' succ)
        have succInList: "succ \<in> set(ls)"
          using SuccBlocks in_set_member local.RedNormalSucc(5) by force
        have oneStepG: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, Normal ns) -n\<rightarrow> (Inl succ, Normal ns')"
          using "2"(2) local.RedNormalSucc(1) local.RedNormalSucc(2) by auto
        then show ?thesis
        proof (cases "\<exists>lsSubsetList. lsSubsetList\<subseteq>lsLoopHead \<and> global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' succ (f(succ)) lsSubsetList")
          case True
          from this obtain lsSubset where subset: "lsSubset\<subseteq>lsLoopHead" and globalBlockLoop: "global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' succ (f(succ)) lsSubset"
            by auto
          have steps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl succ, Normal ns') -n\<rightarrow>^(j - 1) (m', s')"
            using "2"(1) "2"(3) local.RedNormalSucc(1) local.RedNormalSucc(2) by auto
          have "\<forall>(LoopHeadG,LoopHeadG')\<in>lsSubset. loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHeadG LoopHeadG' m' s' j"
            using IH subset by auto
          hence loopIH: "\<forall>(LoopHeadG,LoopHeadG')\<in>lsSubset. loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHeadG LoopHeadG' m' s' (j - 1)"
            using loop_ih_optimizations_one_less
            using case_prodI2 by blast
          have "\<forall>m1' s1'.( A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl (f(succ)), Normal ns') -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure"
            apply (rule target_verifies[where ?c = tgt_block])
            apply (rule oneStepG)
            apply (simp add: NotCoalesced SourceBlock TargetBlock)
            apply (rule TargetVerifies)
            using succInList FunctionCorr in_set_member by fastforce
          then show ?thesis 
            using globalBlockLoop loopIH steps
            unfolding global_block_lemma_loop_def
            by simp
        next
          case False
          from this obtain LoopHeadG LoopHeadG' where "succ = LoopHeadG \<and> f(succ) = LoopHeadG'" and "(LoopHeadG, LoopHeadG')\<in>lsLoopHead"
            using GlobalBlockSucc succInList by force
          hence SuccEqLoopHead: "succ = LoopHeadG \<and> f(succ) = LoopHeadG'"
            using GlobalBlockSucc global_block_lemma_def succInList
            by force

          have verifies: "\<forall>m1' s1'.( A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl (f(succ)), Normal ns') -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure"
            apply (rule target_verifies[where ?c = tgt_block])
            apply (rule oneStepG)
            apply (simp add: NotCoalesced SourceBlock TargetBlock)
            apply (rule TargetVerifies)
            using succInList FunctionCorr in_set_member by fastforce

          have "loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHeadG LoopHeadG' m' s' j"
            using IH SuccEqLoopHead False \<open>(LoopHeadG, LoopHeadG') \<in> lsLoopHead\<close> 
            by fastforce

          then show ?thesis
            using SuccEqLoopHead verifies
            unfolding loop_ih_optimizations_def
            by (metis "2"(1) "2"(3) diff_Suc_1 diff_le_self local.RedNormalSucc(1) local.RedNormalSucc(2))
        qed
      next
        case (RedNormalReturn cs ns')
        then show ?thesis
          by (metis "2"(3) OneStepResult Pair_inject finished_remains relpowp_imp_rtranclp)
      next
        case (RedFailure cs)
        then show ?thesis
          using OneStepResult by auto
      next
        case (RedMagic cs)
        then show ?thesis
          by (simp add: False)
      qed
    qed
  qed
qed

subsubsection \<open>Main Lemma 2: Shows that the Loop Global Block Lemma holds for a loop Head. 
              Note that src_block and tgt_block are both Loop Heads in this case.\<close>


lemma loopHead_global_block:
  assumes SuccBlocks: "out_edges G ! src_block = ls" and
          GlobalBlockSucc: "\<forall>x\<in>set(ls). (\<exists>lsSubsetList. lsSubsetList\<subseteq>(lsLoopHead \<union> {(src_block,tgt_block)}) \<and> global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' x (f(x)) lsSubsetList) \<or> (\<exists>(LoopHead, LoopHead')\<in>(lsLoopHead\<union>{(src_block,tgt_block)}). (x = LoopHead \<and> f(x) = LoopHead'))"  and
          FunctionCorr: "\<forall>x\<in>set(ls). f(x)\<in>set(out_edges G' ! tgt_block)" and
          TargetBlock: "node_to_block G' ! tgt_block = tgt_cmds" and
          SourceBlock: "node_to_block G ! src_block = src_cmds" and
          NotCoalesced: "tgt_cmds = src_cmds"
        shows "global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block lsLoopHead" 
unfolding global_block_lemma_loop_def
proof (rule allI | rule impI)+
  fix m' ns s' j
  assume k_step: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block, Normal ns) -n\<rightarrow>^j (m', s')" and
         TargetVerifies: "\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl tgt_block, Normal ns) -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure" and
         IH: "\<forall>(LoopHead, LoopHead')\<in>lsLoopHead. loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead' m' s' j"
  show "s' \<noteq> Failure" using TargetVerifies k_step GlobalBlockSucc IH
  proof (induction j arbitrary: ns rule: less_induct)
    case (less j)
    then show ?case
    proof (cases rule: relpowp_E2_2[OF less(3)])
      case 1
      then show ?thesis
        by auto
    next
      case (2 a b m)
      have OneStepResult: "b \<noteq> Failure"
        apply (rule one_step_not_failure[where ?G = G and ?b = src_block and ?c = a])
        apply (rule less.prems(1))
        apply (simp add: NotCoalesced SourceBlock TargetBlock)
        by (simp add: "2"(2))
      then show ?thesis 
      proof (cases "b = Magic")
        case True
        have "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(a, b) -n\<rightarrow>* (m', s')"
          by (meson "2"(3) relpowp_imp_rtranclp)
        then show ?thesis
          using True red_cfg_magic_preserved by blast
      next
        case False
        from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, Normal ns) -n\<rightarrow> (a, b)\<close> show ?thesis
        proof (cases)
          case (RedNormalSucc cs ns' succ)
          have succInList: "succ \<in> set(ls)"
            using SuccBlocks in_set_member local.RedNormalSucc(5) by fastforce

          obtain LoopHeadG LoopHeadG' lsSubsetList where cond: "global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' succ (f(succ)) lsSubsetList \<or> (succ = LoopHeadG \<and> f(succ) = LoopHeadG')" and elem: "(LoopHeadG, LoopHeadG')\<in>(lsLoopHead\<union>{(src_block, tgt_block)}) \<and> lsSubsetList \<subseteq> lsLoopHead\<union>{(src_block, tgt_block)}"
            using succInList less.prems(3)
            by blast
          have oneStepG: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, Normal ns) -n\<rightarrow> (Inl succ, Normal ns')"
            using "2"(2) local.RedNormalSucc(1) local.RedNormalSucc(2)
            by simp
         
          then show ?thesis
          proof (cases "global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' succ (f(succ)) lsSubsetList")
            case True
            have loopIHSrcTgt: "loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block m' s' (j-1)"
              unfolding loop_ih_optimizations_def
              proof (rule allI | rule impI)+
                fix j' ns1'
                assume "j' \<le> j-1" and
                       j'Step: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block, Normal ns1') -n\<rightarrow>^j' (m', s')" and 
                       TargetVer: "\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl tgt_block, Normal ns1') -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure"
                show "s' \<noteq> Failure"
                  using less.IH
                proof -
                  have strictlySmaller: "j' < j" 
                    using "2"(1) \<open>j' \<le> j - 1\<close> verit_comp_simplify1(3) by linarith
                  have loopIHHolds: "\<forall>(LoopHead, LoopHead')\<in>lsLoopHead. loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead' m' s' j'"
                    using less.prems(4) loop_ih_optimizations_more_less
                    by (metis (no_types, lifting) \<open>j' \<le> j - 1\<close> case_prodD case_prodI2 loop_ih_optimizations_one_less)
                  thus "s'\<noteq>Failure"
                    using j'Step TargetVer less.IH strictlySmaller GlobalBlockSucc loopIHHolds
                    by blast
                qed
              qed
            have  globalBlockLoopHolds: "global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' succ (f(succ)) lsSubsetList"
              using True by simp
            have steps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl succ, Normal ns') -n\<rightarrow>^(j - 1) (m', s')"
              using "2"(1) "2"(3) local.RedNormalSucc(1) local.RedNormalSucc(2) by force
            have succVerifies: "\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl (f succ), Normal ns') -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure"
              apply (rule target_verifies[where ?c = tgt_block])
              apply (rule oneStepG)
              apply (simp add: NotCoalesced SourceBlock TargetBlock)
              apply (simp add: less.prems(1))
              using succInList FunctionCorr in_set_member by fastforce
            have "\<forall>(LoopHead, LoopHead')\<in>lsLoopHead \<union> {(src_block, tgt_block)}. loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead' m' s' (j - 1)"
              using IH loop_ih_optimizations_one_less loopIHSrcTgt less.prems(4) Un_iff 
              by blast
            hence "\<forall>(LoopHead, LoopHead')\<in>lsSubsetList. loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead' m' s' (j - 1)"
              using elem by auto
            then show ?thesis
              using globalBlockLoopHolds steps succVerifies
              unfolding global_block_lemma_loop_def
              by blast
          next
            case False
            hence SuccEqLoopHead: "succ = LoopHeadG \<and> f(succ) = LoopHeadG'"
                using cond by auto
            then show ?thesis 
            proof (cases "(LoopHeadG, LoopHeadG') = (src_block, tgt_block)")
              case True
              have srcAgain: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block, Normal ns') -n\<rightarrow>^(j-1) (m', s')"
                using "2"(1) "2"(3) SuccEqLoopHead True local.RedNormalSucc(1) local.RedNormalSucc(2) by auto
              have TargetVerifiesAgain: "\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl tgt_block, Normal ns') -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure"
                using TargetVerifies
                by (metis FunctionCorr NotCoalesced Pair_inject SourceBlock SuccEqLoopHead TargetBlock True converse_rtranclp_into_rtranclp in_set_member less.prems(1) local.RedNormalSucc(3) local.RedNormalSucc(4) red_cfg.RedNormalSucc succInList)
              have strictlySmaller: "j-1<j"
                by (simp add: "2"(1))
              have "\<forall>(LoopHead,LoopHead')\<in>lsLoopHead. loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead' m' s' (j-1)"
                using less(5) loop_ih_optimizations_one_less
                by blast
              then show ?thesis
                using less.IH srcAgain TargetVerifiesAgain less(4) strictlySmaller
                by presburger
            next 
              case False
              hence "(LoopHeadG, LoopHeadG') \<in> (lsLoopHead)"
                using elem by auto
              hence loopIH: "loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHeadG LoopHeadG' m' s' j"
                using less.prems(4)
                by fastforce
              have "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl succ, Normal ns') -n\<rightarrow>^m (m', s')"
                using "2"(3) local.RedNormalSucc(1) local.RedNormalSucc(2) by auto
              hence stepsFromSucc: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl succ, Normal ns') -n\<rightarrow>^(j-1) (m', s')"
                using \<open>j = Suc m\<close>
                by simp
              have "\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl (f succ), Normal ns') -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure"
                apply (rule target_verifies[where ?c = tgt_block])
                apply (rule oneStepG)
                apply (simp add: NotCoalesced SourceBlock TargetBlock)
                apply (simp add: less.prems(1))
                using succInList FunctionCorr in_set_member by fastforce
              then show ?thesis
                using stepsFromSucc loopIH SuccEqLoopHead
                unfolding loop_ih_optimizations_def
                by (meson diff_le_self)
            qed
          qed
        next
          case (RedNormalReturn cs ns')
          then show ?thesis
            by (metis "2"(3) OneStepResult finished_remains old.prod.inject relpowp_imp_rtranclp)
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
qed


subsubsection \<open>Main Lemma 3: Reduce the set of loop heads when we know that the loop global block lemma holds\<close>

text \<open>The use case for this lemma is when a loop head gets coalesced\<close>



lemma loopHead_global_block_hybrid_new:
  assumes OneSucc:"out_edges G ! src_block = [succ]" and 
          HybridHoldsSucc: "hybrid_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G  G' succ tgt_block tgt_cmds_0 (lsLoopHead\<union>{(src_block, tgt_block)})" and  
          SrcCmds: "node_to_block G ! src_block = src_cmds" and
          TgtCmds: "node_to_block G' ! tgt_block = tgt_cmds" and
          CoalescedBlock: "tgt_cmds = src_cmds@tgt_cmds_0"
        shows "global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G  G' src_block tgt_block lsLoopHead"
  unfolding global_block_lemma_loop_def
proof (rule allI | rule impI)+
  fix m' ns s' j
  assume k_step: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block, Normal ns) -n\<rightarrow>^j (m', s')" and
         TargetVerifies: "\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl tgt_block, Normal ns) -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure" and
         IH: "\<forall>(LoopHead, LoopHead')\<in>lsLoopHead. loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead' m' s' j"
  show "s' \<noteq> Failure" using TargetVerifies k_step IH
  proof (induction j arbitrary: ns rule: less_induct)
    case (less j)
    then show ?case
    proof (cases rule: relpowp_E2_2[OF less(3)])
      case 1
      then show ?thesis
        by auto
    next
      case (2 a b m)
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
            by (metis assms(3) assms(4) assms(5) less.prems(1) r_into_rtranclp red_cfg.RedFailure red_cmd_append_failure_preserved)
        next
          case (RedMagic cs)
          then show ?thesis 
            by simp
        qed
      then show ?thesis
      proof (cases "b = Magic")
        case True
        have "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(a, b) -n\<rightarrow>* (m', s')"
          by (meson "2"(3) relpowp_imp_rtranclp)
        then show ?thesis
          using True red_cfg_magic_preserved by blast
      next
        case False
        from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, Normal ns) -n\<rightarrow> (a, b)\<close> show ?thesis
        proof cases
          case (RedNormalSucc cs ns' n')
          have "n' = succ"
            by (metis OneSucc local.RedNormalSucc(5) member_rec(1) member_rec(2))
          hence mSteps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl succ, Normal ns') -n\<rightarrow>^m (m', s')"
            using "2"(3) local.RedNormalSucc(1) local.RedNormalSucc(2) by blast
          have "hybrid_block_lemma_target_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block tgt_cmds ns"
            apply (rule normal_target_verfies_show_hybrid_verifies)
            using less.prems(1) apply blast
            by (simp add: TgtCmds)

          hence hybridTargetVerifies: "hybrid_block_lemma_target_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block tgt_cmds_0 ns'"
            using less(2)
            unfolding hybrid_block_lemma_target_verifies_def
            using SrcCmds CoalescedBlock local.RedNormalSucc(3) local.RedNormalSucc(4) red_cmd_list_append by blast
          have loopIH: "loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block m' s' m"
            unfolding loop_ih_optimizations_def
          proof (rule allI | rule impI)+
            fix j' ns1'
            assume "j'\<le>m" and
                   steps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block, Normal ns1') -n\<rightarrow>^j' (m', s')" and
                   TarVer: "\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl tgt_block, Normal ns1') -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure"
            show "s' \<noteq> Failure"
              using less.IH
            proof -
              have strictlySmaller:"j'<j"
                using "2"(1) \<open>j' \<le> m\<close> by auto
              have "\<forall>(LoopHead, LoopHead')\<in>lsLoopHead. loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead' m' s' j'"
                using loop_ih_optimizations_more_less less(4)
                by (metis (no_types, lifting) \<open>j' < j\<close> case_prodD case_prodI2 order_less_imp_le)
              thus "s' \<noteq> Failure"
                using strictlySmaller TarVer steps less.IH
                by blast
            qed
          qed
          have "m\<le>j"
            by (simp add: "2"(1))
          hence "\<forall>(LoopHead, LoopHead')\<in>lsLoopHead \<union> {(src_block, tgt_block)}.loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead' m' s' m"
            using loop_ih_optimizations_more_less less(4) loopIH
            by blast
          then show ?thesis 
            using HybridHoldsSucc mSteps hybridTargetVerifies
            unfolding hybrid_block_lemma_loop_def
            by blast
        next
          case (RedNormalReturn cs ns')
          then show ?thesis 
            by (simp add: OneSucc)
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
qed




subsubsection \<open>Main Lemma 4: Shows that the Loop Hybrid Block Lemma holds if a block in a loop was coalesced\<close>

lemma loopBlock_global_block_hybrid:
assumes   SuccBlocks: "out_edges G ! src_block = ls" and
          GlobalBlockSucc: "\<forall>x\<in>set(ls). ((global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' x (f(x)) {}) \<or>  (\<exists>(LoopHead, LoopHead')\<in>lsLoopHead.(global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' x (f(x)) lsLoopHead) \<or> (x = LoopHead \<and> f(x) = LoopHead')))" and
          FunctionCorr: "\<forall>x\<in>set(ls). f(x)\<in>set(out_edges G' ! tgt_block)" and
          SourceBlock: "node_to_block G ! src_block = src_cmds" 
shows     "hybrid_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block src_cmds lsLoopHead"
unfolding hybrid_block_lemma_loop_def
proof (rule allI | rule impI)+
fix m' ns s' j
assume k_step: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block, Normal ns) -n\<rightarrow>^j (m', s')" and
IH: "\<forall>(LoopHead, LoopHead')\<in>lsLoopHead. loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead' m' s' j" and
TargetVerifies: "hybrid_block_lemma_target_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block src_cmds ns"
show   "s' \<noteq> Failure "
proof (cases rule: relpowp_E2_2[OF k_step])
  case 1
  then show ?thesis
    by blast
next
  case (2 a b m)
  from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, Normal ns) -n\<rightarrow> (a, b)\<close> have OneStepResult: "b \<noteq> Failure"
  proof cases
    case (RedNormalSucc cs ns' n')
    then show ?thesis by blast
  next
    case (RedNormalReturn cs ns')
    then show ?thesis by blast
  next
    case (RedFailure cs)
    then show ?thesis
      using SourceBlock TargetVerifies hybrid_block_lemma_target_verifies_def by blast
  next
    case (RedMagic cs)
    then show ?thesis by blast
  qed
  then show ?thesis 
  proof (cases "b = Magic")
    case True
    have "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(a, b) -n\<rightarrow>* (m', s')"
      by (meson "2"(3) rtranclp_power)
    then show ?thesis
      using True red_cfg_magic_preserved by blast
  next
    case False
    from this obtain ns1 where "b = Normal ns1"
      using OneStepResult state.exhaust by blast
    from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, Normal ns) -n\<rightarrow> (a, b)\<close> show ?thesis
    proof cases
      case (RedNormalSucc cs ns' succ)
      have succInList: "succ \<in> set(ls)"
        using SuccBlocks in_set_member local.RedNormalSucc(5) by force
      have oneStepG: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block, Normal ns) -n\<rightarrow> (Inl succ, Normal ns')"
        using "2"(2) local.RedNormalSucc(1) local.RedNormalSucc(2) by auto
      then show ?thesis 
      proof (cases "global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' succ (f(succ)) {}")
        case True
        have transCl: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl succ, Normal ns') -n\<rightarrow>* (m', s')"
          by (metis "2"(3) local.RedNormalSucc(1) local.RedNormalSucc(2) relpowp_imp_rtranclp)

        have "\<forall>m1' s1'.( A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl (f(succ)), Normal ns') -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure"
          using GlobalBlockSucc TargetVerifies
          unfolding hybrid_block_lemma_target_verifies_def global_block_lemma_def hybrid_block_lemma_target_succ_verifies_def
          by (metis (mono_tags, lifting) FunctionCorr SourceBlock in_set_member local.RedNormalSucc(3) local.RedNormalSucc(4) succInList)

        then show ?thesis
          using True transCl
          unfolding global_block_lemma_loop_def
          using "2"(3) local.RedNormalSucc(1) local.RedNormalSucc(2) by blast
      next
        case False
        from this obtain LoopHeadG LoopHeadG' where cond: "global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' succ (f(succ)) lsLoopHead \<or> (succ = LoopHeadG \<and> f(succ) = LoopHeadG')" and inList: "(LoopHeadG, LoopHeadG')\<in>lsLoopHead"
          using GlobalBlockSucc case_prodE succInList by fastforce
        then show ?thesis
        proof (cases "global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' succ (f(succ)) lsLoopHead")
          case True
          have "loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHeadG LoopHeadG' m' s' j"
            using IH inList
            by blast 
          hence "loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHeadG LoopHeadG' m' s' (j - 1)"
            using IH
            unfolding loop_ih_optimizations_def
            by (meson less_imp_diff_less linorder_not_less)

          have loopIH: "\<forall>(LoopHead, LoopHead')\<in>lsLoopHead. loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead' m' s' (j - 1)"
            using IH loop_ih_optimizations_one_less
            by blast

          have steps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl succ, Normal ns') -n\<rightarrow>^(j - 1) (m', s')"
            using "2"(1) "2"(3) local.RedNormalSucc(1) local.RedNormalSucc(2) by auto

          have "\<forall>m1' s1'.( A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl (f(succ)), Normal ns') -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure"
            using GlobalBlockSucc TargetVerifies
            unfolding hybrid_block_lemma_target_verifies_def global_block_lemma_def hybrid_block_lemma_target_succ_verifies_def
            by (metis (no_types, opaque_lifting) FunctionCorr SourceBlock in_set_member local.RedNormalSucc(3) local.RedNormalSucc(4) succInList)
          then show ?thesis
            using True loopIH steps
            unfolding global_block_lemma_loop_def
            by presburger
        next
          case False
          hence SuccEqLoopHead: "succ = LoopHeadG \<and> f(succ) = LoopHeadG'"
            using GlobalBlockSucc global_block_lemma_def succInList cond 
            by force

          have verifies: "\<forall>m1' s1'.( A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl (f(succ)), Normal ns') -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure"
            using GlobalBlockSucc TargetVerifies
            unfolding hybrid_block_lemma_target_verifies_def global_block_lemma_def hybrid_block_lemma_target_succ_verifies_def
            by (metis (mono_tags, lifting) FunctionCorr SourceBlock in_set_member local.RedNormalSucc(3) local.RedNormalSucc(4) succInList)

         have "loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHeadG LoopHeadG' m' s' j"
            using IH inList
            by fastforce

          then show ?thesis
            using SuccEqLoopHead verifies
            unfolding loop_ih_optimizations_def
            by (metis "2"(1) "2"(3) diff_Suc_1 diff_le_self local.RedNormalSucc(1) local.RedNormalSucc(2))
        qed
      qed
    next
      case (RedNormalReturn cs ns')
      then show ?thesis
        by (metis "2"(3) OneStepResult Pair_inject finished_remains relpowp_imp_rtranclp)
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



subsubsection \<open>Main lemma 5 (extending hybrid global block lemmas for loops)\<close>

text \<open>The following lemma shows that given the loop hybrid global block lemma for block i, we can construct
the loop hybrid block lemma for block i-1. Below the suffix 1 is used for i and 0 is used for i-1.\<close>

lemma extend_hybrid_global_block_lemma_loop:
 assumes 
      NextGlobal: "hybrid_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' src_block_1 tgt_block tgt_cmds_1 lsLoopHead" and      
      SourceBlock: "node_to_block G ! src_block_0 = cs" and
      SourceSucc: "out_edges G ! src_block_0 = [src_block_1]" and
                  "tgt_cmds_0 = cs@tgt_cmds_1"
 shows                    
      "hybrid_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' src_block_0 tgt_block tgt_cmds_0 lsLoopHead"
  unfolding hybrid_block_lemma_loop_def
proof (rule allI | rule impI)+ \<comment>\<open>Here, we are applying initial proof rule to get rid of universal quantifiers and implications\<close>
  fix m' ns s' j
  assume k_step: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block_0, Normal ns) -n\<rightarrow>^j (m', s')" and
         TargetVerifies: "hybrid_block_lemma_target_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block tgt_cmds_0 ns" and 
         IH: "\<forall>(LoopHead, LoopHead')\<in>lsLoopHead. loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead' m' s' j"

  show "s' \<noteq> Failure"
  proof (cases rule: relpowp_E2_2[OF k_step])
    case 1
    then show ?thesis 
      by fast
  next
    case (2 b s0)
    from \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl src_block_0, Normal ns) -n\<rightarrow> (b, s0)\<close>
    have OneStepResult: "s0 \<noteq> Failure \<and> (\<forall>ns0. (s0 = Normal ns0 \<longrightarrow> b = Inl src_block_1 \<and> 
                                                A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns\<rangle> [\<rightarrow>] Normal ns0))"
    proof cases 
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

    
    show ?thesis
    proof (cases "s0 = Magic")
      case True
      have "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(b, s0) -n\<rightarrow>* (m', s')"
        by (meson "2"(3) relpowp_imp_rtranclp)
      thus "s' \<noteq> Failure"
        using red_cfg_magic_preserved[OF \<open>A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(b, s0) -n\<rightarrow>* (m', s')\<close>] True 
        by blast     
    next
      case False
      from this obtain ns0 where "s0 = Normal ns0" 
        using OneStepResult state.exhaust by auto

      hence RedBlock0:  "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs,Normal ns\<rangle> [\<rightarrow>] Normal ns0" and RedSuccBlock: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block_1, Normal ns0) -n\<rightarrow>^(j-1) (m', s')"
        using OneStepResult apply auto[1]
        using "2"(1) "2"(3) OneStepResult \<open>s0 = Normal ns0\<close> by auto
      show ?thesis
      proof (rule hybrid_block_lemma_loop_elim[OF NextGlobal RedSuccBlock]) 
        show "hybrid_block_lemma_target_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block tgt_cmds_1 ns0"
          unfolding hybrid_block_lemma_target_verifies_def
        proof (rule allI, rule impI, rule conjI)
          fix s1'
          assume "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>tgt_cmds_1,Normal ns0\<rangle> [\<rightarrow>] s1'"
          with RedBlock0 have "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs@tgt_cmds_1,Normal ns\<rangle> [\<rightarrow>] s1'"
            by (simp add: red_cmd_list_append)
          thus "s1' \<noteq> Failure"
            using TargetVerifies \<open>tgt_cmds_0 = cs @ tgt_cmds_1\<close>
            unfolding hybrid_block_lemma_target_verifies_def
            by simp
        next
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
        
        show "\<forall>(LoopHead, LoopHead')\<in>lsLoopHead. loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead' m' s' (j-1)"
          using IH  loop_ih_optimizations_one_less 
          by blast

      qed    
    qed
  qed
qed


subsubsection \<open>Main lemma 6 (converting loop hybrid global block lemma to normal loop global block lemma)\<close>  

lemma convert_hybrid_global_block_lemma_loop:
 assumes 
      HybridGlobal: "hybrid_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block tgt_cmds lsLoopHead" and
      TargetBlock: "node_to_block G' ! tgt_block = tgt_cmds"
 shows 
      "global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block lsLoopHead"  
  unfolding global_block_lemma_loop_def
proof (rule allI | rule impI)+
  fix m' ns s' j
  assume RedSource: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block, Normal ns) -n\<rightarrow>^j (m', s')" and
     TargetVerifies: "\<forall>m1' s1'. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl tgt_block, Normal ns) -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure" and
     IH: "\<forall>(LoopHead, LoopHead')\<in>lsLoopHead. loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead' m' s' j"
  show "s' \<noteq> Failure"
  proof (rule hybrid_block_lemma_loop_elim[OF HybridGlobal RedSource])  
    show "hybrid_block_lemma_target_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block tgt_cmds ns"
      unfolding hybrid_block_lemma_target_verifies_def
    proof (rule allI, rule impI)
      fix s1'
      assume RedTgtCmds: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>tgt_cmds,Normal ns\<rangle> [\<rightarrow>] s1'"

      have "s1' \<noteq> Failure"
      proof (rule ccontr)
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

    show "\<forall>(LoopHead, LoopHead')\<in>lsLoopHead. loop_ih_optimizations A M \<Lambda> \<Gamma> \<Omega> G G' LoopHead LoopHead' m' s' j"
      using IH by auto
  qed
qed

subsubsection \<open>Main Lemma 7: Following Lemma shows correctness of pruning of unreachable blocks if the block was not coalesced\<close>

lemma pruning_not_coalesced_loop:
  assumes SuccBlocks: "out_edges G ! src_block = ls" and
          TargetBlock: "node_to_block G' ! tgt_block = tgt_cmds" and
          SourceBlock: "node_to_block G ! src_block = src_cmds" and
          Pruning: "(Assume (Lit (LBool False))) \<in> set (src_cmds) \<or> (Assert (Lit (LBool False))) \<in> set (src_cmds)" and
          NotCoalesced: "tgt_cmds = src_cmds"
        shows "global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block {}"
  unfolding global_block_lemma_loop_def
proof (rule allI | rule impI)+
  fix m' ns s' j
  assume k_step: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block, Normal ns) -n\<rightarrow>^j (m', s')" and
         TargetVerifies: "\<forall>m1' s1'.( A,M,\<Lambda>,\<Gamma>,\<Omega>,G' \<turnstile>(Inl tgt_block, Normal ns) -n\<rightarrow>* (m1', s1')) \<longrightarrow> s1' \<noteq> Failure"
  show "s' \<noteq> Failure"
  proof -
    from k_step have RedSource: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block, Normal ns) -n\<rightarrow>* (m', s')"
      by (simp add: relpowp_imp_rtranclp)
    show ?thesis
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
qed

subsubsection \<open>Main Lemma 8: Following Lemma shows correctness of pruning of unreachable blocks if the block was coalesced\<close>

lemma pruning_coalesced_loop:
  assumes TargetBlock: "node_to_block G' ! tgt_block = tgt_cmds" and
          SourceBlock: "node_to_block G ! src_block = src_cmds" and
          Pruning: "(Assert (Lit (LBool False))) \<in> set (src_cmds) \<or> (Assume (Lit (LBool False))) \<in> set (src_cmds)" and
          Coalesced: "tgt_cmds = cs@src_cmds"
        shows "hybrid_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block src_cmds {}"
  unfolding hybrid_block_lemma_loop_def

proof (rule allI | rule impI)+
  fix m' ns s' j
  assume k_step: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block, Normal ns) -n\<rightarrow>^j (m', s')" and
         TargetVerifies: "hybrid_block_lemma_target_verifies A M \<Lambda> \<Gamma> \<Omega> G' tgt_block src_cmds ns"
  show "s' \<noteq> Failure"
  proof -
    have RedSource: "A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl src_block, Normal ns) -n\<rightarrow>* (m', s')"
      by (meson k_step rtranclp_power)
    show ?thesis
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
qed


subsubsection \<open>Main Lemma 9: Loop Global Block with empty set is equal to normal global block lemma \<close>

lemma empty_loop_global_block_eq_global_block: 
  assumes "global_block_lemma_loop A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block {}"
  shows "global_block_lemma A M \<Lambda> \<Gamma> \<Omega> G G' src_block tgt_block"
  using assms 
  unfolding global_block_lemma_loop_def global_block_lemma_def
  by (metis (no_types, lifting) ball_empty rtranclp_imp_relpowp)


end