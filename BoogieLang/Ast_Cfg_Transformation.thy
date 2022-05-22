theory Ast_Cfg_Transformation 
   imports Main
          "Boogie_Lang.Ast"
          "Boogie_Lang.Semantics"
          "Boogie_Lang.BackedgeElim"
begin 

text \<open>The following are various miscellaneous helper lemmas used later in the proofs of the local and global relation lemmas.\<close>

lemmas converse_rtranclp_induct3 =
  converse_rtranclp_induct [of _ "(ax, ay, az)" "(bx, by, bz)", split_rule, consumes 1, case_names refl step]

lemmas converse_rtranclpE3 = converse_rtranclpE [of _ "(xa,xb,xc)" "(za,zb,zc)", split_rule]

lemma final_is_static: 
  assumes "is_final ((BigBlock name [] None None), start_cont, start_state)"
  shows "\<And>A M \<Lambda> \<Gamma> \<Omega> T end_bb end_cont end_state. 
         (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name [] None None), start_cont, start_state) (end_bb, end_cont, end_state)) \<Longrightarrow> 
         ((end_bb, end_cont, end_state) = ((BigBlock name [] None None), start_cont, start_state))" 
  using assms 
proof -
  fix A M \<Lambda> \<Gamma> \<Omega> T end_bb  end_cont end_state
  have cont_eq: "start_cont = KStop" using assms is_final.elims(1) by blast  

  assume prem1: "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name [] None None), start_cont, start_state) (end_bb, end_cont, end_state))"
  from prem1 show "((end_bb, end_cont, end_state) = ((BigBlock name [] None None), start_cont, start_state))" using cont_eq
  proof cases 
    case RedFailure_or_Magic thus ?thesis using cont_eq by blast
  qed auto
qed

lemma final_is_static_propagate:
  assumes "rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T) start_config  end_config" 
  and "is_final start_config"
  and "start_config = ((BigBlock name [] None None), start_cont, start_state)"
  shows "end_config = ((BigBlock name [] None None), start_cont, start_state)"
  using assms
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case using assms by simp
next
  case (rtrancl_into_rtrancl a b c)
  then have inter_is_same: "b = (BigBlock name [] None None, start_cont, start_state)" and inter_is_final: "is_final b" by auto
  have "start_cont = KStop" using rtrancl_into_rtrancl(4) is_final.elims(1) rtrancl_into_rtrancl.prems(2) by blast

  from rtrancl_into_rtrancl(2) show ?case
    using inter_is_same inter_is_final \<open>start_cont = KStop\<close>
  proof cases
    case RedFailure_or_Magic thus ?thesis using inter_is_same inter_is_final \<open>start_cont = KStop\<close> by (auto simp add: RedFailure_or_Magic)
  qed auto
qed


lemma magic_propagates: 
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, cont, Magic) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
    shows "reached_state = Magic"
  using assms
proof (cases j)
  case 0 
  hence "(reached_bb, reached_cont, reached_state) = (bb, cont, Magic)" using assms by fastforce
  thus ?thesis by simp
next
  case (Suc j')
  from this obtain first_inter where 
    red1: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>(bb, cont, Magic)\<rangle> \<longrightarrow> first_inter" and red_rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> first_inter -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)"
    by (metis assms relpowp_Suc_E2)
  hence reached_conj: "((get_state first_inter) = Magic) \<and> ((is_final first_inter) = True)" 
  proof cases
    case RedFailure_or_Magic thus ?thesis by simp
  qed
  hence magic_reached: "(get_state first_inter) = Magic" by simp
  have final_config: "is_final first_inter" using reached_conj by simp
  hence "\<exists> name. first_inter = ((BigBlock name [] None None), KStop, Magic)" using magic_reached
    by (metis get_state.simps is_final.elims(2))
  from this obtain name1 where concrete: "first_inter = ((BigBlock name1 [] None None), KStop, Magic)" 
    by blast 

  from red_rest show ?thesis using final_config magic_reached concrete final_is_static_propagate by (metis prod.inject relpowp_imp_rtranclp)
qed 


lemma strictly_smaller_helper2: "j'' < j' \<Longrightarrow> j = Suc j' \<Longrightarrow> j'' < j"
  by simp

lemma strictly_smaller_helper3: "j'' < j' \<Longrightarrow> j''' < j'' \<Longrightarrow> j = Suc j' \<Longrightarrow> j''' < j"
  by simp

lemma strictly_smaller_helper4: "j' = Suc (Suc j'') \<Longrightarrow> k < j'' \<Longrightarrow> j = Suc j' \<Longrightarrow> k < j"
  by simp

lemma steps_trans_helper:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb0, cont0, Normal ns1'') -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)"
  shows "rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T) (bb0, cont0, Normal ns1'') (reached_bb, reached_cont, reached_state)"
  using assms
proof -
  from assms(1) show ?thesis by (simp add: relpowp_imp_rtranclp)
qed

lemma seq_skip:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb0, (KSeq bb_next cont0), Normal ns3) -n\<longrightarrow>^l (reached_bb, reached_cont, reached_state)"
      and "bb0 = BigBlock None [] None None"
  shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state) \<or> 
            (\<exists> l1. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb_next, cont0, Normal ns3) -n\<longrightarrow>^l1 (reached_bb, reached_cont, reached_state)) \<and> (l = Suc l1) )"
  using assms
proof (cases l)
  case 0
  then show ?thesis by (metis Ast.valid_configuration_def assms(1) get_state.simps is_final.simps(5) relpowp_0_E state.distinct(1))
next
  case 1: (Suc l1)
  then show ?thesis 
  proof -
    from 1 assms obtain inter_bb inter_cont inter_state where
      step1: "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (BigBlock None [] None None, (KSeq bb_next cont0), Normal ns3) (inter_bb, inter_cont, inter_state))" and 
      rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(inter_bb, inter_cont, inter_state) -n\<longrightarrow>^l1 (reached_bb, reached_cont, reached_state)" 
      by (metis (no_types, opaque_lifting) prod_cases3 relpowp_Suc_D2)
    from this have "(inter_bb, inter_cont, inter_state) = (bb_next, (cont0), Normal ns3)"
    proof cases
      case RedSkip thus ?thesis by auto
    qed auto
    hence "(A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb_next, cont0, Normal ns3) -n\<longrightarrow>^l1 (reached_bb, reached_cont, reached_state)) \<and> (l = Suc l1)" using rest \<open>l = Suc l1\<close> by simp
    then show ?thesis by blast
  qed
qed

lemma endblock_skip:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb0, KEndBlock (KSeq bb_next cont0), Normal ns3) -n\<longrightarrow>^l (reached_bb, reached_cont, reached_state)"
      and "bb0 = BigBlock None [] None None" 
  shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state) \<or> 
            (\<exists> l2. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb_next, cont0, Normal ns3) -n\<longrightarrow>^l2 (reached_bb, reached_cont, reached_state)) \<and> (l = Suc (Suc l2)) )"
  using assms
proof (cases l)
  case 0
  then show ?thesis by (metis Ast.valid_configuration_def assms(1) get_state.simps is_final.simps(6) relpowp_fun_conv state.simps(3))
next
  case 1: (Suc l1)
  then show ?thesis 
  proof (cases l1)
    case 0
    from 1 assms this have "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (BigBlock None [] None None, KEndBlock (KSeq bb_next cont0), Normal ns3) (reached_bb, reached_cont, reached_state))"
      by fastforce
    then show ?thesis
    proof cases
      case RedSkipEndBlock thus ?thesis by (simp add: Ast.valid_configuration_def)
    qed auto
  next
    case 2: (Suc l2)
    from 2 1 have "l = Suc (Suc l2)" by auto
    from 2 1 assms obtain inter_bb inter_cont inter_state inter_bb2 inter_cont2 inter_state2 where
      step1: "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (BigBlock None [] None None, KEndBlock (KSeq bb_next cont0), Normal ns3) (inter_bb, inter_cont, inter_state))" and 
      step2: "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (inter_bb, inter_cont, inter_state) (inter_bb2, inter_cont2, inter_state2))" and
      rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(inter_bb2, inter_cont2, inter_state2) -n\<longrightarrow>^l2 (reached_bb, reached_cont, reached_state)" 
      by (metis (no_types, opaque_lifting) prod_cases3 relpowp_Suc_D2)
    from this step1 have "(inter_bb, inter_cont, inter_state) = (BigBlock None [] None None, (KSeq bb_next cont0), Normal ns3)"
    proof cases
      case RedSkipEndBlock thus ?thesis 
        by blast
    qed auto
    from step2 this have "(inter_bb2, inter_cont2, inter_state2) = (bb_next, cont0, Normal ns3)" 
    proof cases 
      case RedSkip thus ?thesis  using \<open>(inter_bb, inter_cont, inter_state) = (BigBlock None [] None None, KSeq bb_next cont0, Normal ns3)\<close> by fastforce
    qed auto
    hence "(A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb_next, cont0, Normal ns3) -n\<longrightarrow>^l2 (reached_bb, reached_cont, reached_state)) \<and> (l = Suc (Suc l2))" using rest \<open>l = Suc (Suc l2)\<close> by simp
    then show ?thesis by blast
  qed
qed

lemma correctness_propagates_through_empty:
  assumes "\<forall>m s. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n0, Normal ns1) -n\<rightarrow>* (m, s)) \<longrightarrow> s \<noteq> Failure"
      and "node_to_block G ! n0 = []"
      and "List.member (out_edges G ! n0) n1"
    shows "\<And> m s. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m, s)) \<Longrightarrow> s \<noteq> Failure"
proof -
  fix m1 s1
  have a1: "(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>[], Normal ns1\<rangle> [\<rightarrow>] (Normal ns1))" by (rule RedCmdListNil)
  show "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m1, s1)) \<Longrightarrow> s1 \<noteq> Failure" 
  proof -
    assume "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m1, s1))"
    thus "s1 \<noteq> Failure" by (metis a1 assms(1-3) dag_verifies_propagate)
  qed
qed

lemma wrapper_to_endblock:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb0, cont0, Normal ns) -n\<longrightarrow>^l (reached_bb, reached_cont, reached_state)"
      and "bb0 = BigBlock name [] (Some (WhileWrapper loop)) None"
  shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state) \<or> 
         (\<exists> l1. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>((BigBlock name [] (Some loop) None), KEndBlock cont0, Normal ns) -n\<longrightarrow>^l1 (reached_bb, reached_cont, reached_state)) \<and> (l = Suc l1))"
  using assms
proof (cases l)
  case 0
  hence "(reached_bb, reached_cont, reached_state) = (bb0, cont0, Normal ns)" using assms(1) by simp
  then show ?thesis by (simp add: Ast.valid_configuration_def assms(2))
next
  case 1: (Suc l1)
  then show ?thesis 
  proof -
    from 1 assms obtain inter_bb inter_cont inter_state where
      step1: "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb0, cont0, Normal ns) (inter_bb, inter_cont, inter_state))" and 
      rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(inter_bb, inter_cont, inter_state) -n\<longrightarrow>^l1 (reached_bb, reached_cont, reached_state)" 
      by (metis (no_types, opaque_lifting) prod_cases3 relpowp_Suc_D2)
    from this have "(inter_bb, inter_cont, inter_state) = (BigBlock name [] (Some loop) None, KEndBlock cont0, Normal ns)"
    proof cases
      case RedParsedWhileWrapper thus ?thesis using assms(2) by auto
    qed (auto simp add: assms(2))
    hence "(A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(BigBlock name [] (Some loop) None, KEndBlock cont0, Normal ns) -n\<longrightarrow>^l1 (reached_bb, reached_cont, reached_state)) \<and> (l = Suc l1)" 
      using rest \<open>l = Suc l1\<close> assms(2) by simp
    then show ?thesis by blast
  qed
qed

lemma ending3:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb, cont0, Normal ns1'') -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)" 
      and "bb = BigBlock name [] (Some (WhileWrapper loop)) None"
      and "\<And>m3 s3. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m3, s3)) \<Longrightarrow> s3 \<noteq> Failure"
      and "\<And> j''. 
            j = Suc j'' \<Longrightarrow>
            A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(BigBlock name [] (Some loop) None, KEndBlock cont0, Normal ns1'') -n\<longrightarrow>^j'' (reached_bb, reached_cont, reached_state) \<Longrightarrow>
           (\<And>m' s'. A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m', s') \<Longrightarrow> s' \<noteq> Failure) \<Longrightarrow>
           (valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
    shows "valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state"
proof -
  from assms(1-2) have disj_a:
    "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state) \<or> 
       (\<exists> l1. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(BigBlock name [] (Some loop) None, KEndBlock cont0, Normal ns1'') -n\<longrightarrow>^l1 (reached_bb, reached_cont, reached_state)) \<and> (j = Suc l1) )" 
    by (simp add: wrapper_to_endblock)
  thus ?thesis
  proof cases
    assume "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)" thus ?thesis by simp
  next 
    assume "\<not> ((valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state))"
    hence "(\<exists> l2. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(BigBlock name [] (Some loop) None, KEndBlock cont0, Normal ns1'') -n\<longrightarrow>^l2 (reached_bb, reached_cont, reached_state)) \<and> (j = Suc l2) )" 
      using disj_a by blast
    thus ?thesis
    proof -
      obtain l2_conc where conc_trace: "(A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(BigBlock name [] (Some loop) None, KEndBlock cont0, Normal ns1'') -n\<longrightarrow>^l2_conc (reached_bb, reached_cont, reached_state))" and 
                           succ_rel: "(j = Suc l2_conc)"
        using \<open>\<exists>l2. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(BigBlock name [] (Some loop) None, KEndBlock cont0, Normal ns1'') -n\<longrightarrow>^l2 (reached_bb, reached_cont, reached_state)) \<and> j = Suc l2\<close> by blast
      show ?thesis
        apply (rule assms(4))
          apply (rule succ_rel)
         apply (rule conc_trace)
        apply (rule assms(3))
        apply (simp)
        done
    qed
  qed
qed


lemma endblock_skip_wrapper:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb0, KEndBlock (KSeq (BigBlock name [] (Some (WhileWrapper str)) tr) cont0), Normal ns3) -n\<longrightarrow>^l (reached_bb, reached_cont, reached_state)"
      and "bb0 = BigBlock None [] None None"
  shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state) \<or> 
         (\<exists> l3. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>((BigBlock name [] (Some str) tr), KEndBlock cont0, Normal ns3) -n\<longrightarrow>^l3 (reached_bb, reached_cont, reached_state)) \<and> (l = Suc (Suc (Suc l3))) )"
  using assms
proof (cases l)
  case 0
  then show ?thesis by (metis Ast.valid_configuration_def assms(1) get_state.simps is_final.simps(6) relpowp_fun_conv state.simps(3))
next
  case 1: (Suc l1)
  then show ?thesis 
    proof (cases l1)
      case 0
      from 1 assms this have 
        "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (BigBlock None [] None None, KEndBlock (KSeq (BigBlock name [] (Some (WhileWrapper str)) tr) cont0), Normal ns3) (reached_bb, reached_cont, reached_state))"
        by fastforce
      then show ?thesis
      proof cases
        case RedSkipEndBlock thus ?thesis by (simp add: Ast.valid_configuration_def)
      qed auto
    next
      case 2: (Suc l2)
      then show ?thesis
      proof (cases l2)
        case 0 
        from 2 1 have "l = Suc (Suc l2)" by auto
        from 2 1 assms obtain inter_bb inter_cont inter_state  where
          step1: "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (BigBlock None [] None None, KEndBlock (KSeq (BigBlock name [] (Some (WhileWrapper str)) tr) cont0), Normal ns3) (inter_bb, inter_cont, inter_state))" and 
          step2: "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (inter_bb, inter_cont, inter_state) (reached_bb, reached_cont, reached_state))" 
          using "0" by auto
        from this step1 have "(inter_bb, inter_cont, inter_state) = (BigBlock None [] None None, (KSeq (BigBlock name [] (Some (WhileWrapper str)) tr) cont0), Normal ns3)"
        proof cases
          case RedSkipEndBlock thus ?thesis 
            by blast
        qed auto
        from step2 this have "(reached_bb, reached_cont, reached_state) = ((BigBlock name [] (Some (WhileWrapper str)) tr), cont0, Normal ns3)" 
        proof cases 
          case RedSkip thus ?thesis  using \<open>(inter_bb, inter_cont, inter_state) = (BigBlock None [] None None, (KSeq (BigBlock name [] (Some (WhileWrapper str)) tr) cont0), Normal ns3)\<close> by fastforce
        qed auto
        then show ?thesis by (simp add: Ast.valid_configuration_def)
      next
        case 3: (Suc l3)
        from 3 2 1 have "l = Suc (Suc (Suc l3))" by auto
        from 3 2 1 assms obtain inter_bb inter_cont inter_state inter_bb2 inter_cont2 inter_state2 inter_bb3 inter_cont3 inter_state3 where
          step1: "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (BigBlock None [] None None, KEndBlock (KSeq (BigBlock name [] (Some (WhileWrapper str)) tr) cont0), Normal ns3) (inter_bb, inter_cont, inter_state))" and 
          step2: "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (inter_bb, inter_cont, inter_state) (inter_bb2, inter_cont2, inter_state2))" and 
          step3: "(red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (inter_bb2, inter_cont2, inter_state2) (inter_bb3, inter_cont3, inter_state3))" and
          rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb3, inter_cont3, inter_state3) -n\<longrightarrow>^l3 (reached_bb, reached_cont, reached_state)" 
          by (metis (no_types, opaque_lifting) get_state.cases relpowp_Suc_D2)
  
        from this step1 have "(inter_bb, inter_cont, inter_state) = (BigBlock None [] None None, (KSeq (BigBlock name [] (Some (WhileWrapper str)) tr) cont0), Normal ns3)"
        proof cases
          case RedSkipEndBlock thus ?thesis 
            by blast
        qed auto
        from step2 this have "(inter_bb2, inter_cont2, inter_state2) = ((BigBlock name [] (Some (WhileWrapper str)) tr), cont0, Normal ns3)" 
        proof cases 
          case RedSkip thus ?thesis  using \<open>(inter_bb, inter_cont, inter_state) = (BigBlock None [] None None, (KSeq (BigBlock name [] (Some (WhileWrapper str)) tr) cont0), Normal ns3)\<close> by fastforce
        qed auto
        from step3 this have "(inter_bb3, inter_cont3, inter_state3) = ((BigBlock name [] (Some str) tr), KEndBlock cont0, Normal ns3)"
        proof cases
          case RedParsedWhileWrapper thus ?thesis using \<open>(inter_bb2, inter_cont2, inter_state2) = (BigBlock name [] (Some (WhileWrapper str)) tr, cont0, Normal ns3)\<close> by fastforce 
        qed auto
        hence "(A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>((BigBlock name [] (Some str) tr), KEndBlock cont0, Normal ns3) -n\<longrightarrow>^l3 (reached_bb, reached_cont, reached_state)) \<and> (l = Suc (Suc (Suc l3)))" 
          using \<open>l = Suc (Suc (Suc l3))\<close> rest by blast
        thus ?thesis by blast
    qed
  qed
qed


text \<open>Local lemmas: The following are lemmas proving local relations between various kinds of ast-bigblocks and cfg-blocks\<close>

text \<open>Local relation between an ast-bigblock starting with a non-empty set of simple commands and a cfg-block containing the same simple commands\<close>
lemma block_local_rel_generic:
  assumes block_rel: "ast_cfg_rel guard invs bb cs2"
  and "guard = None"
  and "invs = []"
  and Red_bb_to: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb, cont0, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cs2 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))"
  and "bb = (BigBlock name cs1 any_str any_tr)"
  and "cs1 \<noteq> Nil"
  and "cs2 \<noteq> Nil"
  shows "reached_state \<noteq> Failure  \<and>
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
  using assms
proof (induction arbitrary: ns1)
  case (Rel_Main_test bb name cs1 any_str any_tr)
  thus ?case
  proof (cases cs1)
    case Nil
    then show ?thesis using \<open>cs1 \<noteq> Nil\<close> by simp
  next
    case (Cons a list)
    then have "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name (a#list) any_str any_tr), cont0, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
      using Rel_Main_test by blast
    then have "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(a#list), Normal ns1\<rangle> [\<rightarrow>] reached_state" using Rel_Main_test(5) 
    proof cases
      case RedSimpleCmds thus ?thesis by (simp add: RedSimpleCmds)
    qed
    then have "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] reached_state" using Cons by simp
    
    then show ?thesis using Rel_Main_test by auto
  qed 
qed auto

text \<open>Local relation between (an ast-bigblock starting with a non-empty set of simple commands 
               and (is the first ast-bigblock in the then-branch of an if-statement or is the first ast-bigblock in the body of a while-loop)) 
       and a cfg-block containing the same simple commands\<close>
lemma block_local_rel_guard_true:
  assumes block_rel: "ast_cfg_rel None [] bb cs2"
  and "c = Assume block_guard"
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>block_guard, ns1\<rangle> \<Down> LitV (LBool True)"
  and Red_bb_to: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb, cont0, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (cs3) (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" 
  and "bb = (BigBlock name cs1 any_str any_tr)"
  and "cs1 \<noteq> Nil"
  and "cs2 \<noteq> Nil"
  and "cs3 = (c#cs2)"
  shows "reached_state \<noteq> Failure  \<and>
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs3, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
  using assms 
proof cases
  case Rel_Main_test
  have Red_impl_extended: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cs2 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" 
    using trace_is_possible \<open>c = Assume block_guard\<close> Red_impl RedAssumeOk RedCmdListCons \<open>cs3 = c#cs2\<close> by blast
  hence snd_step_to_end: "reached_state \<noteq> Failure  \<and> (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))"
    using Red_bb_to assms(6-8) block_local_rel_generic block_rel by metis
  have push_one_cmd: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, Normal ns1\<rangle> \<rightarrow> Normal ns1" 
    using \<open>c = Assume block_guard\<close> trace_is_possible 
    by (simp only: RedAssumeOk)
  then show ?thesis using snd_step_to_end by (simp add: RedCmdListCons \<open>cs3 = c#cs2\<close>)
qed auto

text \<open>Local relation between (an ast-bigblock starting with a non-empty set of simple commands 
               and (is the first ast-bigblock in the else-branch of an if-statement or is the first ast-bigblock after a while-loop)) 
       and a cfg-block containing the same simple commands\<close>
lemma block_local_rel_guard_false:
  assumes block_rel: "ast_cfg_rel None [] bb cs2"
  and "(UnOp Not block_guard) \<sim> b "
  and "c = Assume b"
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(UnOp Not block_guard), ns1\<rangle> \<Down> LitV (LBool True)"
  and Red_bb_to: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb, cont0, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (c#cs2) (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" 
  and "bb = (BigBlock name cs1 any_str any_tr)"
  and "cs1 \<noteq> Nil"
  and "cs2 \<noteq> Nil"
  shows "reached_state \<noteq> Failure  \<and>
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(c#cs2), Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
  using assms 
proof cases
  case Rel_Main_test
  have Red_impl_extended: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cs2 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" 
    using trace_is_possible \<open>c = Assume b\<close> \<open>(UnOp Not block_guard) \<sim> b\<close> equiv_preserves_value  Red_impl RedAssumeOk RedCmdListCons by metis
  hence snd_step_to_end: "reached_state \<noteq> Failure  \<and> (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))"
    using Red_bb_to assms(7-9) block_local_rel_generic block_rel by metis
  have equiv: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, ns1\<rangle> \<Down> BoolV True" 
    using trace_is_possible equiv_preserves_value \<open>(UnOp Not block_guard) \<sim> b\<close>
    by metis
  hence push_one_cmd: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, Normal ns1\<rangle> \<rightarrow> Normal ns1" 
    using \<open>c = Assume b\<close> trace_is_possible equiv_preserves_value
    by (auto simp add: RedAssumeOk)
  then show ?thesis using snd_step_to_end  by (simp add: RedCmdListCons)
qed auto

text \<open>Local relation between a loop-only(no simple commands) ast-bigblock and a corresponding cfg-block containing assertions of the loop invariants\<close>
lemma block_local_rel_loop_head:
  assumes block_rel: "ast_cfg_rel None assert_invs bb assertions"
  and "bb =  (BigBlock name [] (Some (ParsedWhile loop_guard invs (bb0#body_bbs))) any_tr)"
  and "assert_invs = map inv_into_assertion invs"
  and Red_bb: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb, cont0, (Normal ns1)) (reached_bb, reached_cont, reached_state)" 
  and Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> assertions (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))"
  shows "reached_state \<noteq> Failure  \<and>
         (\<forall>ns1'. reached_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>assertions, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
  using assms
proof cases
  case Rel_Invs
  hence "assertions = map inv_into_assertion invs" using assms(3) by simp
  from Red_bb show ?thesis
  proof cases
    case RedParsedWhileTrue thus ?thesis using \<open>assertions = (map inv_into_assertion invs)\<close>  by (simp add: asserts_hold_if_invs_hold assms(2))
  next
    case RedParsedWhileFalse thus ?thesis using \<open>assertions = (map inv_into_assertion invs)\<close>  by (simp add: asserts_hold_if_invs_hold assms(2))
  next
    case RedParsedWhile_InvFail thus ?thesis using Red_impl \<open>assertions = map inv_into_assertion invs\<close> one_inv_fails_assertions assms(2) by blast
  qed (auto simp add: assms(2))
next
  case Rel_Main_test
  hence "assertions = map inv_into_assertion invs" using assms(2-3) by simp
  from Red_bb show ?thesis
  proof cases
    case RedParsedWhileTrue thus ?thesis using \<open>assertions = (map inv_into_assertion invs)\<close>  by (simp add: asserts_hold_if_invs_hold assms(2))
  next
    case RedParsedWhileFalse thus ?thesis using \<open>assertions = (map inv_into_assertion invs)\<close>  by (simp add: asserts_hold_if_invs_hold assms(2))
  next
    case RedParsedWhile_InvFail thus ?thesis using Red_impl \<open>assertions = map inv_into_assertion invs\<close> one_inv_fails_assertions assms(2) by blast
  qed (auto simp add: assms(2))
qed

text \<open>Global lemmas: The following are lemmas proving global relations between various kinds of ast-bigblocks and cfg-blocks\<close>

text \<open>'ending', 'ending2' and 'correctness_propagates_through_assumption' are helper lemmas 
       used to complete the proofs of the global lemmas for ast-bigblocks, which are heads of loops. 
       'ending2' and 'correctness_propagates_through_assumption' are used in the case where 
       we're proving a global lemma for the head of a loop that is followed by another loop (not nested).\<close>
lemma ending:
  assumes "j = Suc j'" 
      and "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb, KEndBlock (KSeq bigblock_next cont0), Normal ns1'') -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)" 
      and "bb = BigBlock None [] None None"
      and "\<And>m3 s3. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m3, s3)) \<Longrightarrow> s3 \<noteq> Failure"
      and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard,ns1''\<rangle> \<Down> BoolV False" 
      and "\<And> j''. 
            j' = Suc (Suc j'') \<Longrightarrow>
            A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bigblock_next, cont0, Normal ns1'') -n\<longrightarrow>^j'' (reached_bb, reached_cont, reached_state) \<Longrightarrow>
           (\<And>m' s'. A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m', s') \<Longrightarrow> s' \<noteq> Failure) \<Longrightarrow>
           (A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp Not guard,ns1''\<rangle> \<Down> BoolV True) \<Longrightarrow> (valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
    shows "valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state"
proof -
  from assms(2-3) have disj_a:
    "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state) \<or> 
       (\<exists> l2. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bigblock_next, cont0, Normal ns1'') -n\<longrightarrow>^l2 (reached_bb, reached_cont, reached_state)) \<and> (j' = Suc (Suc l2)) )" 
    by (simp add: endblock_skip)
  thus ?thesis
  proof cases
    assume "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)" thus ?thesis by simp
  next 
    assume "\<not> ((valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state))"
    hence "(\<exists> l2. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bigblock_next, cont0, Normal ns1'') -n\<longrightarrow>^l2 (reached_bb, reached_cont, reached_state)) \<and> (j' = Suc (Suc l2)) )" 
      using disj_a by blast
    thus ?thesis
    proof -
      obtain l2_conc where conc_trace: "(A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bigblock_next, cont0, Normal ns1'') -n\<longrightarrow>^l2_conc (reached_bb, reached_cont, reached_state))" and 
                           succ_rel: "(j' = Suc (Suc l2_conc))"
        using \<open>\<exists>l2. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bigblock_next, cont0, Normal ns1'') -n\<longrightarrow>^l2 (reached_bb, reached_cont, reached_state)) \<and> j' = Suc (Suc l2)\<close> by blast
      show ?thesis
        apply (rule assms(6))
           apply (rule succ_rel)
          apply (rule conc_trace)
         apply (rule assms(4))
         apply (simp)
        using assms(5) false_equals_not_true 
        by blast
    qed
  qed
qed

lemma correctness_propagates_through_assumption:
  assumes "\<forall>m s. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n0, Normal ns1) -n\<rightarrow>* (m, s)) \<longrightarrow> s \<noteq> Failure"
      and "node_to_block G ! n0 = [Assume c]"
      and "UnOp Not guard \<sim> c"
      and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard, ns1\<rangle> \<Down> BoolV False"
      and "List.member (out_edges G ! n0) n1"
    shows "\<And> m s. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m, s)) \<Longrightarrow> s \<noteq> Failure"
proof -
  fix m1 s1
  have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, ns1\<rangle> \<Down> BoolV True" using assms(3-4) equiv_preserves_value false_equals_not_true by blast
  then have a1: "(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>[Assume c], Normal ns1\<rangle> [\<rightarrow>] (Normal ns1))" by (meson RedAssumeOk RedCmdListCons RedCmdListNil)
  show "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m1, s1)) \<Longrightarrow> s1 \<noteq> Failure" 
  proof -
    assume "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m1, s1))"
    thus "s1 \<noteq> Failure" using a1 assms(1-2) assms(5) dag_verifies_propagate by blast 
  qed
qed

lemma correctness_propagates_through_assumption2:
  assumes "\<forall>m s. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n0, Normal ns1) -n\<rightarrow>* (m, s)) \<longrightarrow> s \<noteq> Failure"
      and "node_to_block G ! n0 = [Assume guard]"
      and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard, ns1\<rangle> \<Down> BoolV True"
      and "List.member (out_edges G ! n0) n1"
    shows "\<And> m s. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m, s)) \<Longrightarrow> s \<noteq> Failure"
proof -
  fix m1 s1
  have a1: "(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>[Assume guard], Normal ns1\<rangle> [\<rightarrow>] (Normal ns1))" by (meson RedAssumeOk assms(3) red_cmd_list.simps)
  show "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m1, s1)) \<Longrightarrow> s1 \<noteq> Failure" 
  proof -
    assume "(A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1) -n\<rightarrow>* (m1, s1))"
    thus "s1 \<noteq> Failure" using a1 assms(1-2) assms(4) dag_verifies_propagate by blast 
  qed
qed

lemma ending2:
  assumes "j = Suc j'"
      and "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb,
                      KEndBlock (KSeq (BigBlock None [] (Some (WhileWrapper (ParsedWhile next_guard next_invs (next_body_bb#body_bbs)))) None) cont1),
                      Normal ns1'') -n\<longrightarrow>^j'
           (reached_bb, reached_cont, reached_state)"
      and "bb = BigBlock None [] None None"
      and corr: "\<forall>m3 s3. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure"
      and guard_false: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard, ns1''\<rangle> \<Down> BoolV False" 
      and "node_to_block G ! n = [Assume c]" 
      and "(UnOp Not guard) \<sim> c"
      and "List.member (out_edges(G) ! n) n1"
      and "\<And> j'''.
          j' = Suc (Suc (Suc j''')) \<Longrightarrow>
          node_to_block G ! n = [Assume c] \<Longrightarrow>
          (UnOp Not guard) \<sim> c \<Longrightarrow>
          List.member (out_edges(G) ! n) n1 \<Longrightarrow>
          A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>((BigBlock None [] (Some (ParsedWhile next_guard next_invs (next_body_bb#body_bbs))) None), KEndBlock cont1, Normal ns1'') -n\<longrightarrow>^j''' 
              (reached_bb, reached_cont, reached_state) \<Longrightarrow>
          (\<And>m' s'. A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1'') -n\<rightarrow>* (m', s') \<Longrightarrow> s' \<noteq> Failure) \<Longrightarrow> 
          (Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
    shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
  using assms
proof -
  from assms(2-3) have disj_a:
    "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state) \<or> 
       (\<exists> l3. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> ((BigBlock None [] (Some (ParsedWhile next_guard next_invs (next_body_bb#body_bbs))) None), KEndBlock cont1, Normal ns1'') 
              -n\<longrightarrow>^l3 (reached_bb, reached_cont, reached_state)) \<and> (j' = Suc (Suc (Suc l3))) )"
    by (simp add: endblock_skip_wrapper)
  thus ?thesis
  proof cases
    assume "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)" thus ?thesis by simp
  next 
    assume "\<not> ((valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state))"
    hence skipped_endblock: 
                  "(\<exists> l3. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>((BigBlock None [] (Some (ParsedWhile next_guard next_invs (next_body_bb#body_bbs))) None), KEndBlock cont1, Normal ns1'') 
                   -n\<longrightarrow>^l3 (reached_bb, reached_cont, reached_state)) \<and> (j' = Suc (Suc (Suc l3))) )" 
      using disj_a by blast
    thus ?thesis
    proof -
      obtain l3_conc where 
           conc_trace: "(A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>((BigBlock None [] (Some (ParsedWhile next_guard next_invs (next_body_bb#body_bbs))) None), KEndBlock cont1, Normal ns1'') 
                        -n\<longrightarrow>^l3_conc (reached_bb, reached_cont, reached_state))" and 
           succ_rel: "(j' = Suc (Suc (Suc l3_conc))) " 
        using skipped_endblock by blast
      show ?thesis
        apply (rule assms(9))
             apply (rule succ_rel)
            apply (simp add: assms)
           apply (rule assms(7))
          apply (rule assms(8))
         apply (rule conc_trace)
        apply (rule correctness_propagates_through_assumption)
             apply (rule corr)
            apply (rule assms(6))
           apply (rule assms(7))
          apply (rule guard_false)
         apply (rule assms(8))
        apply simp
        done
    qed
  qed
qed

lemma ending_then:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb, KSeq bb_next cont1, Normal ns1'') -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
      and "bb = BigBlock None [] None None"
      and guard_true: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard, ns1''\<rangle> \<Down> BoolV True" 
      and "node_to_block G ! n = cs2"
      and "cs2 = [Assume guard]"
      and "List.member (out_edges(G) ! n) n1"
      and corr: "\<forall>m3 s3. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure"
      and "\<And> j''.
          j = (Suc j'') \<Longrightarrow>
          node_to_block G ! n = cs2 \<Longrightarrow>
          List.member (out_edges(G) ! n) n1 \<Longrightarrow>
          A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb_next, cont1, Normal ns1'') -n\<longrightarrow>^j'' (reached_bb, reached_cont, reached_state) \<Longrightarrow>
          (\<And>m' s'. A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1'') -n\<rightarrow>* (m', s') \<Longrightarrow> s' \<noteq> Failure) \<Longrightarrow> 
          (Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
    shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
  using assms
proof -
  from assms(1-2) have disj_a:
    "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state) \<or> 
       (\<exists> l1. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb_next, cont1, Normal ns1'') -n\<longrightarrow>^l1 (reached_bb, reached_cont, reached_state)) \<and> (j = Suc l1) )"
    by (simp add: seq_skip)
  thus ?thesis
  proof cases
    assume "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)" thus ?thesis by simp
  next 
    assume "\<not> ((valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state))"
    hence skipped_endblock: 
                  "(\<exists> l1. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb_next, cont1, Normal ns1'') 
                   -n\<longrightarrow>^l1 (reached_bb, reached_cont, reached_state)) \<and> (j = Suc l1) )" 
      using disj_a by blast
    thus ?thesis
    proof -
      obtain l1_conc where 
           conc_trace: "(A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb_next, cont1, Normal ns1'') -n\<longrightarrow>^l1_conc (reached_bb, reached_cont, reached_state))" and 
           succ_rel: "(j = Suc l1_conc) " 
        using skipped_endblock by blast
      show ?thesis
        apply (rule assms(8))
             apply (rule succ_rel)
            apply (simp add: assms)
           apply (rule assms(6))
         apply (rule conc_trace)
        apply (rule correctness_propagates_through_assumption2)
            apply (rule corr)
           apply (simp add: assms(4))
           apply (rule assms(5))
          apply (rule guard_true)
         apply (rule assms(6))
        apply simp
        done
    qed
  qed
qed

lemma ending_else:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb, KSeq bb_next cont1, Normal ns1'') -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
      and "bb = BigBlock None [] None None"
      and corr: "\<forall>m3 s3. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n, Normal ns1'') -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure"
      and guard_false: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>guard, ns1''\<rangle> \<Down> BoolV False" 
      and "node_to_block G ! n = [Assume c]" 
      and "(UnOp Not guard) \<sim> c"
      and "List.member (out_edges(G) ! n) n1"
      and "\<And> j''.
          j = (Suc j'') \<Longrightarrow>
          node_to_block G ! n = [Assume c] \<Longrightarrow>
          (UnOp Not guard) \<sim> c \<Longrightarrow>
          List.member (out_edges(G) ! n) n1 \<Longrightarrow>
          A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb_next, cont1, Normal ns1'') -n\<longrightarrow>^j'' (reached_bb, reached_cont, reached_state) \<Longrightarrow>
          (\<And>m' s'. A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile>(Inl n1, Normal ns1'') -n\<rightarrow>* (m', s') \<Longrightarrow> s' \<noteq> Failure) \<Longrightarrow> 
          (Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
    shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
  using assms
proof -
  from assms(1-2) have disj_a:
    "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state) \<or> 
       (\<exists> l1. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb_next, cont1, Normal ns1'') -n\<longrightarrow>^l1 (reached_bb, reached_cont, reached_state)) \<and> (j = Suc l1) )"
    by (simp add: seq_skip)
  thus ?thesis
  proof cases
    assume "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)" thus ?thesis by simp
  next 
    assume "\<not> ((valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state))"
    hence skipped_endblock: 
                  "(\<exists> l1. (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb_next, cont1, Normal ns1'') 
                   -n\<longrightarrow>^l1 (reached_bb, reached_cont, reached_state)) \<and> (j = Suc l1) )" 
      using disj_a by blast
    thus ?thesis
    proof -
      obtain l1_conc where 
           conc_trace: "(A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile>(bb_next, cont1, Normal ns1'') -n\<longrightarrow>^l1_conc (reached_bb, reached_cont, reached_state))" and 
           succ_rel: "(j = Suc l1_conc) " 
        using skipped_endblock by blast
      show ?thesis
        apply (rule assms(8))
             apply (rule succ_rel)
            apply (simp add: assms)
           apply (rule assms(6))
          apply (rule assms(7))
         apply (rule conc_trace)
        apply (rule correctness_propagates_through_assumption)
             apply (rule corr)
            apply (rule assms(5))
           apply (rule assms(6))
          apply (rule guard_false)
         apply (rule assms(7))
        apply simp
        done
    qed
  qed
qed


text \<open>Global lemma for an ast-bigblock with a non-empty set of simple commands which concludes the program and is immediately after a loop.\<close>
lemma generic_ending_block_after_loop_global_rel:
  assumes syn_rel: "ast_cfg_rel None [] bb cs2"
  and "bb = (BigBlock name cs1 None any_tr)"
  and "(any_tr = None) \<or> (any_tr = (Some (Return val1)))"
  and "node_to_block G ! n = (cs3)"
  and "cs3 = c#cs2"
  and "c = Assume b"
  and "(UnOp Not guard) \<sim> b"
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp Not guard, ns1\<rangle> \<Down> BoolV True"
  and j_step_ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G ((Inl n),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)" 
  using assms
proof (cases cs2)
  case Nil
  hence "cs1 = []" using ast_cfg_rel.cases syn_rel assms(2) by blast 
  thus ?thesis
    proof (cases any_tr)
      case None
      then have "is_final ((BigBlock name cs1 None any_tr), KStop, (Normal ns1))" using \<open>cs1 = []\<close> by auto 
      moreover have "(valid_configuration A \<Lambda> \<Gamma> \<Omega> [] (BigBlock name cs1 None any_tr) KStop (Normal ns1))" by (simp add: Ast.valid_configuration_def expr_all_sat_def)
      ultimately show ?thesis by (metis None \<open>cs1 = []\<close> final_is_static_propagate j_step_ast_trace prod.sel(1) prod.sel(2) relpowp_imp_rtranclp assms(2))
    next
      case (Some a)
      then show ?thesis
      proof (cases j)
        case 0
        from this j_step_ast_trace assms(2) have "(reached_bb, reached_cont, reached_state) = ((BigBlock name cs1 None any_tr), KStop, (Normal ns1))" by simp
        then show ?thesis by (simp add: valid_configuration_def expr_all_sat_def)
      next
        case (Suc j')
        thus ?thesis 
        proof (cases a)
          case (Return x2) 
          from Suc j_step_ast_trace assms(2) obtain inter_bb inter_cont inter_state where
            step0: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock name cs1 None any_tr), KStop, (Normal ns1))\<rangle> \<longrightarrow> (inter_bb, inter_cont, inter_state)" and
            rest0: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb, inter_cont, inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)"
            by (metis prod_cases3 relpowp_Suc_D2) 
          then have inter_conc: "(inter_bb, inter_cont, inter_state) = ((BigBlock name [] None None), KStop, Normal ns1)" 
            using \<open>cs1 = []\<close> Return Some
          proof cases
            case RedReturn thus ?thesis by blast
          qed auto
          then have "is_final (inter_bb, inter_cont, inter_state)" by simp
          then have "(valid_configuration A \<Lambda> \<Gamma> \<Omega> [] inter_bb inter_cont inter_state)" using inter_conc valid_configuration_def
            by (metis expr_all_sat_def get_state.simps list.pred_inject(1) state.simps(3))
          then show ?thesis
            by (metis \<open>is_final (inter_bb, inter_cont, inter_state)\<close> final_is_static_propagate inter_conc prod.sel(1) prod.sel(2) relpowp_imp_rtranclp rest0)
        next
          case (Goto x3)
          thus ?thesis using assms(3) Some by blast
      qed
    qed
  qed
next
  case (Cons)
  hence "cs1 \<noteq> []" using syn_rel assms(2) ast_cfg_rel.simps by blast
  thus ?thesis 
  proof (cases j)
    case 0
    from this j_step_ast_trace assms(2) have "(reached_bb, reached_cont, reached_state) = ((BigBlock name cs1 None any_tr), KStop, (Normal ns1))" by simp
    then show ?thesis by (simp add: valid_configuration_def expr_all_sat_def)
  next
    case (Suc j')
    from this j_step_ast_trace assms(2) obtain inter_bb inter_cont inter_state where
      step: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock name cs1 None any_tr), KStop, (Normal ns1))\<rangle> \<longrightarrow> (inter_bb, inter_cont, inter_state)" and
      rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb, inter_cont, inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)"
      by (metis prod_cases3 relpowp_Suc_D2) 
    then show ?thesis 
    proof (cases any_tr)
      case None
      from step this have concrete_inter: "(inter_bb, inter_cont, inter_state) = (BigBlock name [] None None, KStop, inter_state)"
      proof cases
        case RedSimpleCmds thus ?thesis using None by (auto simp add: RedSimpleCmds)
      qed auto
  
      have Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (c#cs2) (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" 
        using dag_verifies_propagate_2 assms cfg_is_correct by blast 
  
      from step have "inter_state \<noteq> Failure"
      proof cases
        case RedSimpleCmds thus ?thesis using Red_impl trace_is_possible
          by (metis assms(5-7) assms(2) block_local_rel_guard_false local.Cons local.step neq_Nil_conv syn_rel)
      qed auto
  
      hence valid_inter: "(valid_configuration A \<Lambda> \<Gamma> \<Omega> [] inter_bb inter_cont inter_state)" 
        unfolding valid_configuration_def expr_all_sat_def
        using concrete_inter get_state.simps is_final.simps by simp
  
      have "is_final (inter_bb, inter_cont, inter_state)" using concrete_inter by simp 
      then show ?thesis by (metis Pair_inject concrete_inter final_is_static_propagate relpowp_imp_rtranclp rest valid_inter)
    next
      case (Some transfer)
      then show ?thesis
      proof (cases transfer)
        case (Goto x1)
        then show ?thesis using Some assms(3) by blast
      next
        case (Return ret)
        from step this Some have concrete_inter: "(inter_bb, inter_cont, inter_state) = (BigBlock name [] None (Some (Return ret)), KStop, inter_state)"
        proof cases
          case RedSimpleCmds thus ?thesis using Return Some by blast
        qed (auto simp add: Cons \<open>cs1 \<noteq> []\<close>)
    
        have Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (c#cs2) (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" 
          using dag_verifies_propagate_2 assms cfg_is_correct by blast 
    
        from step have "inter_state \<noteq> Failure"
        proof cases
          case RedSimpleCmds thus ?thesis using Red_impl trace_is_possible
            by (metis assms(1-2) assms(5-8) block_local_rel_guard_false local.Cons local.step neq_Nil_conv syn_rel)
        qed auto
        then show ?thesis 
        proof (cases inter_state)
          case (Normal x1)
          then show ?thesis
          proof (cases j')
            case 0
            then show ?thesis using concrete_inter by (metis Ast.valid_configuration_def \<open>inter_state \<noteq> Failure\<close> get_state.simps is_final.simps(4) relpowp_0_E rest)
          next
            case (Suc j'')
            from this rest obtain inter_bb2 inter_cont2 inter_state2 where
              snd_step: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>(inter_bb, inter_cont, inter_state)\<rangle> \<longrightarrow> (inter_bb2, inter_cont2, inter_state2)" and
              snd_rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb2, inter_cont2, inter_state2) -n\<longrightarrow>^j'' (reached_bb, reached_cont, reached_state)"
              by (metis get_state.cases relpowp_Suc_E2)
            then have inter2_conc: "(inter_bb2, inter_cont2, inter_state2) = ((BigBlock name [] None None), KStop, inter_state)" 
              using concrete_inter \<open>inter_state \<noteq> Failure\<close> Normal
            proof cases
              case RedReturn thus ?thesis using concrete_inter \<open>inter_state \<noteq> Failure\<close> Normal by blast
            qed auto
            hence "is_final (inter_bb2, inter_cont2, inter_state2)" by simp
            then show ?thesis
              by (metis Ast.valid_configuration_def inter2_conc \<open>inter_state \<noteq> Failure\<close> expr_all_sat_def final_is_static_propagate get_state.simps list.pred_inject(1) rtranclp_power snd_rest)
          qed
        next
          case Failure
          then show ?thesis using \<open>inter_state \<noteq> Failure\<close> by simp
        next
          case Magic
          then show ?thesis by (metis Ast.valid_configuration_def \<open>inter_state \<noteq> Failure\<close> get_state.simps magic_propagates rest state.simps(5))
        qed
      qed
    qed
  qed
qed


text \<open>Global lemma for an ast-bigblock with a non-empty set of simple commands which concludes the program.\<close>
lemma generic_ending_block_global_rel:
  assumes syn_rel: "ast_cfg_rel None [] bb cs2"
  and j_step_ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, KStop, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and "bb = (BigBlock name cs1 None any_tr)"
  and "(any_tr = None) \<or> (any_tr = (Some (Return val1)))"
  and "node_to_block G ! n = cs2"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G ((Inl n),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)" 
shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)"
  using assms
proof (cases cs2)
  case Nil 
  hence "cs1 = []" using ast_cfg_rel.cases syn_rel assms(3) by blast 
  thus ?thesis
    proof (cases any_tr)
      case None
      then have "is_final ((BigBlock name cs1 None any_tr), KStop, (Normal ns1))" using \<open>cs1 = []\<close> by auto 
      moreover have "(valid_configuration A \<Lambda> \<Gamma> \<Omega> [] (BigBlock name cs1 None any_tr) KStop (Normal ns1))" by (simp add: Ast.valid_configuration_def expr_all_sat_def)
      ultimately show ?thesis by (metis assms(3) None \<open>cs1 = []\<close> final_is_static_propagate j_step_ast_trace prod.sel(1) prod.sel(2) relpowp_imp_rtranclp)
    next
      case (Some a)
      then show ?thesis
      proof (cases j)
        case 0
        from this j_step_ast_trace assms(3) have "(reached_bb, reached_cont, reached_state) = ((BigBlock name cs1 None any_tr), KStop, (Normal ns1))" by simp
        then show ?thesis by (simp add: valid_configuration_def expr_all_sat_def)
      next
        case (Suc j')
        thus ?thesis 
        proof (cases a)
          case (Return x2) 
          from Suc j_step_ast_trace assms(3) obtain inter_bb inter_cont inter_state where
            step0: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock name cs1 None any_tr), KStop, (Normal ns1))\<rangle> \<longrightarrow> (inter_bb, inter_cont, inter_state)" and
            rest0: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb, inter_cont, inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)"
            by (metis prod_cases3 relpowp_Suc_D2) 
          then have inter_conc: "(inter_bb, inter_cont, inter_state) = ((BigBlock name [] None None), KStop, Normal ns1)" 
            using \<open>cs1 = []\<close> Return Some
          proof cases
            case RedReturn thus ?thesis by blast
          qed auto
          then have "is_final (inter_bb, inter_cont, inter_state)" by simp
          then have "(valid_configuration A \<Lambda> \<Gamma> \<Omega> [] inter_bb inter_cont inter_state)" using inter_conc valid_configuration_def
            by (metis expr_all_sat_def get_state.simps list.pred_inject(1) state.simps(3))
          then show ?thesis
            by (metis \<open>is_final (inter_bb, inter_cont, inter_state)\<close> final_is_static_propagate inter_conc prod.sel(1) prod.sel(2) relpowp_imp_rtranclp rest0)
        next
          case (Goto x3)
          thus ?thesis using assms(4) Some by blast
      qed
    qed
  qed
next
  case (Cons) 
  hence "cs1 \<noteq> []" using ast_cfg_rel.simps syn_rel assms(3) by blast
  thus ?thesis
  proof (cases j)
    case 0
    from this j_step_ast_trace assms(3) have "(reached_bb, reached_cont, reached_state) = ((BigBlock name cs1 None any_tr), KStop, (Normal ns1))" by simp
    then show ?thesis by (simp add: valid_configuration_def expr_all_sat_def)
  next
    case (Suc j')
    from this j_step_ast_trace assms(3) obtain inter_bb inter_cont inter_state where
      step: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock name cs1 None any_tr), KStop, (Normal ns1))\<rangle> \<longrightarrow> (inter_bb, inter_cont, inter_state)" and
      rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb, inter_cont, inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)"
      by (metis prod_cases3 relpowp_Suc_D2) 
    then show ?thesis 
    proof (cases any_tr)
      case None
      from step this have concrete_inter: "(inter_bb, inter_cont, inter_state) = (BigBlock name [] None None, KStop, inter_state)"
      proof cases
        case RedSimpleCmds thus ?thesis using None by (auto simp add: RedSimpleCmds)
      qed auto
  
      have Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cs2 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))"
        using assms(5) cfg_is_correct dag_verifies_propagate_2 by blast
  
      from step have "inter_state \<noteq> Failure"
      proof cases
        case RedSimpleCmds thus ?thesis using Red_impl block_local_rel_generic local.Cons local.step syn_rel assms(3) by blast
      qed auto
  
      hence valid_inter: "(valid_configuration A \<Lambda> \<Gamma> \<Omega> [] inter_bb inter_cont inter_state)" 
        unfolding valid_configuration_def expr_all_sat_def
        using concrete_inter get_state.simps is_final.simps by simp
  
      have "is_final (inter_bb, inter_cont, inter_state)" using concrete_inter by simp 
      then show ?thesis by (metis Pair_inject concrete_inter final_is_static_propagate relpowp_imp_rtranclp rest valid_inter)
    next
      case (Some transfer)
      then show ?thesis
      proof (cases transfer)
        case (Goto x1)
        then show ?thesis using Some assms(4) by blast
      next
        case (Return ret)
        from step this Some have concrete_inter: "(inter_bb, inter_cont, inter_state) = (BigBlock name [] None (Some (Return ret)), KStop, inter_state)"
        proof cases
          case RedSimpleCmds thus ?thesis using Return Some by blast
        qed (auto simp add: \<open>cs1 \<noteq> []\<close>)
    
        have Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cs2 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" 
          using dag_verifies_propagate_2  assms(5) cfg_is_correct by blast 
    
        from step have "inter_state \<noteq> Failure"
        proof cases
          case RedSimpleCmds thus ?thesis using Red_impl block_local_rel_generic local.Cons local.step syn_rel assms(3) by blast
        qed auto
  
        then show ?thesis
        proof (cases inter_state)
          case (Normal x1)
          then show ?thesis
          proof (cases j')
            case 0
            then show ?thesis using concrete_inter by (metis Ast.valid_configuration_def \<open>inter_state \<noteq> Failure\<close> get_state.simps is_final.simps(4) relpowp_0_E rest)
          next
            case (Suc j'')
            from this rest obtain inter_bb2 inter_cont2 inter_state2 where
              snd_step: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>(inter_bb, inter_cont, inter_state)\<rangle> \<longrightarrow> (inter_bb2, inter_cont2, inter_state2)" and
              snd_rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb2, inter_cont2, inter_state2) -n\<longrightarrow>^j'' (reached_bb, reached_cont, reached_state)"
              by (metis get_state.cases relpowp_Suc_E2)
            then have inter2_conc: "(inter_bb2, inter_cont2, inter_state2) = ((BigBlock name [] None None), KStop, inter_state)" 
              using concrete_inter \<open>inter_state \<noteq> Failure\<close> Normal
            proof cases
              case RedReturn thus ?thesis using concrete_inter \<open>inter_state \<noteq> Failure\<close> Normal by blast
            qed auto
            hence "is_final (inter_bb2, inter_cont2, inter_state2)" by simp
            then show ?thesis
              by (metis Ast.valid_configuration_def inter2_conc \<open>inter_state \<noteq> Failure\<close> expr_all_sat_def final_is_static_propagate get_state.simps list.pred_inject(1) rtranclp_power snd_rest)
          qed
        next
          case Failure
          then show ?thesis using \<open>inter_state \<noteq> Failure\<close> by simp
        next
          case Magic
          then show ?thesis by (metis valid_configuration_def \<open>inter_state \<noteq> Failure\<close> get_state.simps magic_propagates rest state.simps(5))
        qed
      qed
    qed
  qed
qed


text \<open>Global lemma for an ast-bigblock with a non-empty set of simple commands that enters a loop after it executes its simple cmds.\<close>

(*
lemma inner_loop_head_global_rel_wrapped:
  assumes j_step_ast_trace: 
          "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (BigBlock None [] (Some (WhileWrapper loop)) None, cont0, Normal ns1) -n\<longrightarrow>^j 
                                 (reached_bb, reached_cont, reached_state)"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> G ((Inl n),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and loop_ih:
        "\<And>k ns1'. k < j \<Longrightarrow>
        (A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile>(bb0_unwrapped, KEndBlock KStop, Normal ns1') -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state)) \<Longrightarrow>
        (\<And> m' s'. (red_cfg_multi A M \<Lambda>1_local \<Gamma> \<Omega> nested_loop_before_cfg_to_dag_prog.proc_body ((Inl 1),(Normal ns1')) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)) \<Longrightarrow>
        (Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)" 
  shows "(Ast.valid_configuration A \<Lambda>1_local \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)"
  using assms
proof (cases j)
  case 0
  from this j_step_ast_trace have 
    "(reached_bb, reached_cont, reached_state) = (outer_body_bb1, (KSeq outer_body_bb2 (KSeq bb0_unwrapped (KEndBlock KStop))), Normal ns1)" by auto
  then show ?thesis by (simp add: Ast.valid_configuration_def)
next
  case (Suc j')
  from assms this obtain inter_bb inter_cont inter_state where
    step: "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> \<langle>(outer_body_bb1, (KSeq outer_body_bb2 (KSeq bb0_unwrapped (KEndBlock KStop))), Normal ns1)\<rangle> \<longrightarrow> (inter_bb, inter_cont, inter_state)" and
    rest: "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile>(inter_bb, inter_cont, inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)" 
    by (metis (no_types, opaque_lifting) get_state.cases relpowp_Suc_D2)
  hence "(inter_bb, inter_cont, inter_state) = (outer_body_bb1_unwrapped, KEndBlock (KSeq outer_body_bb2 (KSeq bb0_unwrapped (KEndBlock KStop))), Normal ns1)"
    unfolding outer_body_bb1_unwrapped_def outer_body_bb1_def
    by (cases) auto
  hence rest_conc: "A,M,\<Lambda>1_local,\<Gamma>,\<Omega>,T \<turnstile> (outer_body_bb1_unwrapped, KEndBlock (KSeq outer_body_bb2 (KSeq bb0_unwrapped (KEndBlock KStop))), Normal ns1) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)" 
    using rest by simp
  show ?thesis 
    apply (rule inner_loop_head_global_rel)
      apply (rule rest_conc)
     apply (rule cfg_is_correct)
     apply simp
    using Suc less_SucI loop_ih by blast
qed
*)

lemma block_global_rel_while_successor:
  assumes j_step_ast_trace: 
      "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, cont1, Normal ns1) -n\<longrightarrow>^j 
                      (reached_bb, reached_cont, reached_state)"
  and syn_rel: "ast_cfg_rel None [] bb cmds"
  and "bb = (BigBlock name cmds (Some (WhileWrapper (ParsedWhile guard invs (body_bb0#body_bbs)))) None)"
  and "cmds \<noteq> []"
  and "node_to_block G ! n = cmds"
  and cfg_is_correct: "\<And> m' s'. (red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G ((Inl n),(Normal ns1)) (m',s')) \<Longrightarrow> (s' \<noteq> Failure)"
  and block_local_rel:
    "\<And> reached_bb_inter reached_cont_inter reached_state_inter. 
    (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb, cont1, (Normal ns1)) (reached_bb_inter, reached_cont_inter, reached_state_inter)) \<Longrightarrow> 
    (\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cmds (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure))) \<Longrightarrow>   
    (reached_state_inter \<noteq> Failure  \<and> (\<forall>ns1'. reached_state_inter = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(node_to_block G ! n), Normal ns1\<rangle> [\<rightarrow>] Normal ns1')))"
  and global_rel_succ:
        "\<And> ns2 k.
         k < j \<Longrightarrow>
         (\<forall>msuc2. List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl msuc2, Normal ns2) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)) \<Longrightarrow>
         A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> ((BigBlock name [] (Some (ParsedWhile guard invs (body_bb0#body_bbs))) None), KEndBlock cont1, Normal ns2) -n\<longrightarrow>^k 
                      (reached_bb, reached_cont, reached_state) \<Longrightarrow> 
         (valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
  shows "(valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
  using assms
proof cases
  assume "j = 0"
  then have "(reached_bb, reached_cont, reached_state) = 
             ((BigBlock name cmds (Some (WhileWrapper (ParsedWhile guard invs (body_bb0#body_bbs)))) None), cont1, Normal ns1)" using j_step_ast_trace assms(3) by auto
  thus ?thesis by (simp add: valid_configuration_def)
next
  assume "j \<noteq> 0"
  from this obtain j' where "j = Suc j'" using not0_implies_Suc by blast
  from this j_step_ast_trace assms(3) obtain inter_bb inter_cont inter_state where
    first_step: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock name cmds (Some (WhileWrapper (ParsedWhile guard invs (body_bb0#body_bbs)))) None), cont1, Normal ns1)\<rangle> \<longrightarrow> (inter_bb, inter_cont, inter_state)" and 
    rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb, inter_cont, inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)"
    by (metis (no_types, opaque_lifting) get_state.cases relpowp_Suc_D2)
  from this have a1: "(inter_bb, inter_cont, inter_state) = ((BigBlock name [] (Some (WhileWrapper (ParsedWhile guard invs (body_bb0#body_bbs)))) None), cont1, inter_state)"
  proof cases
    case RedSimpleCmds thus ?thesis by blast
  qed (auto simp add: \<open>cmds \<noteq> []\<close>)
  have Red_impl: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cmds (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))" using dag_verifies_propagate_2 cfg_is_correct assms(5) by blast
  have local_conclusion: "inter_state \<noteq> Failure  \<and> (\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cmds, Normal ns1\<rangle> [\<rightarrow>] Normal ns1'))" 
    using Red_impl first_step assms(3-4) block_local_rel_generic syn_rel by metis
  show ?thesis 
  proof (cases inter_state)
    case (Normal x1)
    hence "(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cmds, Normal ns1\<rangle> [\<rightarrow>] inter_state)" using local_conclusion by blast
    then show ?thesis
    proof (cases j')
      case 0
      then show ?thesis 
        by (metis Normal a1 nat.discI rest wrapper_to_endblock)
    next
      case 2: (Suc j'')

      hence Red_cfg_conc: 
        "(\<forall>msuc2. List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. (A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl msuc2, inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure))" 
        using dag_verifies_propagate Normal \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cmds,Normal ns1\<rangle> [\<rightarrow>] inter_state\<close> assms(5) cfg_is_correct by blast

      from 2 j_step_ast_trace assms(3) obtain inter_bb2 inter_cont2 inter_state2 where
        first_step_2: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>(inter_bb, inter_cont, inter_state)\<rangle> \<longrightarrow> (inter_bb2, inter_cont2, inter_state2)" and 
        rest_2: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb2, inter_cont2, inter_state2) -n\<longrightarrow>^j'' (reached_bb, reached_cont, reached_state)"
        by (metis get_state.cases relpowp_Suc_E2 rest)
      from this have a3: "(inter_bb2, inter_cont2, inter_state2) = 
                          ((BigBlock name [] (Some (ParsedWhile guard invs (body_bb0#body_bbs))) None), KEndBlock cont1, inter_state)"
        using a1 Normal
      proof cases
        case RedParsedWhileWrapper thus ?thesis using a1 by fastforce
      qed auto 

      have "j'' < j" by (simp add: "2" \<open>j = Suc j'\<close>)
      then show ?thesis using a3 rest_2 Normal Red_cfg_conc assms(8) by blast 
    qed
  next
    case Failure
    then show ?thesis using local_conclusion by blast
  next
    case Magic
    then show ?thesis by (metis valid_configuration_def get_state.simps local_conclusion magic_propagates rest state.simps(5))
  qed
qed

lemma ending_directly_after_loop_exit:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, KEndBlock KStop, (Normal ns1'')) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
      and "bb = (BigBlock name [] None None)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> [] reached_bb reached_cont reached_state)"
  using assms
proof (cases j)
  case 0
  hence "(reached_bb, reached_cont, reached_state) = ((BigBlock name [] None None), KEndBlock KStop, (Normal ns1''))" using assms by auto
  then show ?thesis by (simp add: Ast.valid_configuration_def)
next
  case (Suc j')
  from assms(1-2) obtain inter_bb inter_cont inter_state where
    step: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock name [] None None), KEndBlock KStop, (Normal ns1''))\<rangle> \<longrightarrow> (inter_bb, inter_cont, inter_state)" and
    rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb, inter_cont, inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)"
    by (metis (full_types) Suc prod_cases3 relpowp_Suc_E2)
  hence conc_inter: "(inter_bb, inter_cont, inter_state) = ((BigBlock name [] None None), KStop, (Normal ns1''))" 
    by (cases) auto
  hence "is_final (inter_bb, inter_cont, inter_state)" by simp 
  moreover have "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> [] inter_bb inter_cont inter_state)" 
    using valid_configuration_def conc_inter by (metis expr_all_sat_def get_state.simps list.pred_inject(1) state.simps(3))  
  ultimately show ?thesis using rest by (metis conc_inter final_is_static_propagate prod.sel(1) prod.sel(2) relpowp_imp_rtranclp)
qed

text \<open>Global lemma for a loop-head ast-bigblock with non-empty invariants. The loop is also required to be non-empty.\<close>
lemma block_global_rel_loop_head:
  assumes block_rel: "ast_cfg_rel None assertions bb assertions"
  and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, KEndBlock cont1, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and cfg_correct: "(\<And> m2 s2. ((red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G (Inl n, Normal ns1) (m2, s2)) \<Longrightarrow> (s2 \<noteq> Failure)))"
  and "bb = (BigBlock name [] any_str any_tr)"
  (* TODO: You're requiring that the loop isn't empty! What if it is? *)
  and bb_successor_while: "any_str = Some (ParsedWhile cont_guard invs (bb0#body_bbs))"
  and block_local_rel:
    "\<And> reached_bb_inter reached_cont_inter reached_state_inter. (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb, KEndBlock cont1, (Normal ns1)) (reached_bb_inter, reached_cont_inter, reached_state_inter)) \<Longrightarrow> 
    (\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> assertions (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure))) \<Longrightarrow>   
    (reached_state_inter \<noteq> Failure  \<and> (\<forall>ns1'. reached_state_inter = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>assertions, Normal ns1\<rangle> [\<rightarrow>] Normal ns1')))"
  and "node_to_block(G) ! n = assertions"
  and succ_correct: 
   "\<And> ns1'' loop_guard j'. 
    j = Suc j' \<Longrightarrow>
    (\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), Normal ns1'') -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure))) \<Longrightarrow>
    ((cont_guard = Some loop_guard) \<and> 
      (red_expr A \<Lambda> \<Gamma> \<Omega> loop_guard ns1'' (BoolV True)) \<and> 
      A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb0, convert_list_to_cont (bb#(rev body_bbs)) (KEndBlock cont1), (Normal ns1'')) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)) \<or> 
    ((cont_guard = Some loop_guard) \<and> 
      (red_expr A \<Lambda> \<Gamma> \<Omega> loop_guard ns1'' (BoolV False)) \<and> 
      A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> ((BigBlock name [] None None), KEndBlock cont1, (Normal ns1'')) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)) \<or>
    ((cont_guard = None) \<and> 
     ((A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> ((BigBlock name [] None None), KEndBlock cont1, (Normal ns1'')) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)) \<or>
      (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb0, convert_list_to_cont (bb#(rev body_bbs)) (KEndBlock cont1), (Normal ns1'')) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state))))  \<Longrightarrow>  
    (Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)" 
  using assms
proof cases
    case Rel_Invs
    thus ?thesis 
    proof cases
      assume "j = 0"
      hence "(reached_bb, reached_cont, reached_state) = ((BigBlock name [] any_str any_tr), KEndBlock cont1, (Normal ns1))" using ast_trace assms(4) by simp 
      thus ?thesis by (simp add: Ast.valid_configuration_def)
    next
      assume "j \<noteq> 0" 
      from this obtain j' where "j = Suc j'" using not0_implies_Suc by blast
  
      from ast_trace this assms(4) obtain inter_bb inter_cont inter_state where
        first_step: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock name [] any_str any_tr), KEndBlock cont1, (Normal ns1))\<rangle> \<longrightarrow> (inter_bb, inter_cont, inter_state)" and
        rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb, inter_cont, inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)"
        by (metis prod_cases3 relpowp_Suc_D2)
  
      show ?thesis
      proof (cases cont_guard)
        case None
        from first_step show ?thesis using bb_successor_while
        proof cases
          case RedParsedWhileTrue
          hence concrete_inter1: "(inter_bb, inter_cont, inter_state) = (bb0, convert_list_to_cont ((BigBlock name [] any_str any_tr)#(rev body_bbs)) (KEndBlock cont1), (Normal ns1))"
            using bb_successor_while None by blast
  
          from first_step
          have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
            by (metis Pair_inject assms(4) assms(7) block_local_rel cfg_correct concrete_inter1 dag_verifies_propagate dag_verifies_propagate_2)
  
          show ?thesis using \<open>j = Suc j'\<close> succ_cfg_correct None rest concrete_inter1 succ_correct assms(4) by blast 
        next 
          case RedParsedWhileFalse
          hence concrete_inter2: "(inter_bb, inter_cont, inter_state) = ((BigBlock name [] None None), KEndBlock cont1, (Normal ns1))" by simp
  
          from first_step
          have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
            by (metis assms(4) assms(7) block_local_rel cfg_correct dag_verifies_propagate dag_verifies_propagate_2 local.RedParsedWhileFalse(5))
  
          show ?thesis using \<open>j = Suc j'\<close> succ_cfg_correct None rest concrete_inter2 succ_correct by blast
        next 
          case RedParsedWhile_InvFail thus ?thesis using assms(7) block_local_rel cfg_correct dag_verifies_propagate_2 first_step assms(4) by blast
        qed auto
      next
        case (Some concrete_loop_guard)
        then show ?thesis 
        proof cases
          assume guard_true: "(red_expr A \<Lambda> \<Gamma> \<Omega> concrete_loop_guard ns1 (BoolV True))"
          hence guard_not_false: "\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> concrete_loop_guard ns1 (BoolV False))" using expr_eval_determ by blast
  
          from first_step show ?thesis 
          proof cases
            case RedParsedWhileTrue
            hence concrete_inter3: "(inter_bb, inter_cont, inter_state) = (bb0, convert_list_to_cont ((BigBlock name [] any_str any_tr)#(rev body_bbs)) (KEndBlock cont1), (Normal ns1))"
              using bb_successor_while Some by blast
  
            from first_step
            have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
              by (metis Pair_inject assms(4) assms(7) block_local_rel cfg_correct concrete_inter3 dag_verifies_propagate dag_verifies_propagate_2)
  
            show ?thesis using \<open>j = Suc j'\<close> succ_cfg_correct Some guard_true rest concrete_inter3 succ_correct assms(4) by blast 
        next 
            case RedParsedWhile_InvFail thus ?thesis using assms(7) block_local_rel cfg_correct dag_verifies_propagate_2 first_step assms(4) by blast
        qed (auto simp add: bb_successor_while Some guard_not_false)
      next
        assume guard_not_true: "\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> concrete_loop_guard ns1 (BoolV True))"
        thus ?thesis 
        proof cases
          assume guard_false: "(red_expr A \<Lambda> \<Gamma> \<Omega> concrete_loop_guard ns1 (BoolV False))"
  
          from first_step show ?thesis 
          proof cases
            case RedParsedWhileFalse
            hence concrete_inter4: "(inter_bb, inter_cont, inter_state) = ((BigBlock name [] None None), KEndBlock cont1, (Normal ns1))" by simp

          from first_step
          have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
            by (metis assms(4) assms(7) block_local_rel cfg_correct dag_verifies_propagate dag_verifies_propagate_2 local.RedParsedWhileFalse(5))
  
            show ?thesis using \<open>j = Suc j'\<close> succ_cfg_correct Some guard_false rest concrete_inter4 succ_correct by blast
          next
            case RedParsedWhile_InvFail thus ?thesis using Some bb_successor_while guard_not_true by blast
          qed (auto simp add: bb_successor_while Some guard_not_true)
        next
          assume guard_not_false: "\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> concrete_loop_guard ns1 (BoolV False))"
          from first_step show ?thesis
          proof cases
            case RedParsedWhile_InvFail thus ?thesis using Some bb_successor_while guard_not_true by blast
          qed (auto simp add: bb_successor_while Some guard_not_true guard_not_false)
        qed
      qed
    qed
  qed
next 
  case Rel_Main_test 
  thus ?thesis
    proof cases
      assume "j = 0"
      hence "(reached_bb, reached_cont, reached_state) = ((BigBlock name [] any_str any_tr), KEndBlock cont1, (Normal ns1))" using ast_trace assms(4) by simp 
      thus ?thesis by (simp add: Ast.valid_configuration_def)
    next
      assume "j \<noteq> 0" 
      from this obtain j' where "j = Suc j'" using not0_implies_Suc by blast
  
      from ast_trace this assms(4) obtain inter_bb inter_cont inter_state where
        first_step: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock name [] any_str any_tr), KEndBlock cont1, (Normal ns1))\<rangle> \<longrightarrow> (inter_bb, inter_cont, inter_state)" and
        rest: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb, inter_cont, inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)"
        by (metis prod_cases3 relpowp_Suc_D2)
  
      show ?thesis
      proof (cases cont_guard)
        case None
        from first_step show ?thesis using bb_successor_while
        proof cases
          case RedParsedWhileTrue
          hence concrete_inter1: "(inter_bb, inter_cont, inter_state) = (bb0, convert_list_to_cont ((BigBlock name [] any_str any_tr)#(rev body_bbs)) (KEndBlock cont1), (Normal ns1))"
            using bb_successor_while None by blast
  
          from first_step
          have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
            by (metis Pair_inject assms(4) assms(7) block_local_rel cfg_correct concrete_inter1 dag_verifies_propagate dag_verifies_propagate_2)
  
          show ?thesis using \<open>j = Suc j'\<close> succ_cfg_correct None rest concrete_inter1 succ_correct assms(4) by blast 
        next 
          case RedParsedWhileFalse
          hence concrete_inter2: "(inter_bb, inter_cont, inter_state) = ((BigBlock name [] None None), KEndBlock cont1, (Normal ns1))" by simp
  
          from first_step
          have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
            by (metis assms(4) assms(7) block_local_rel cfg_correct dag_verifies_propagate dag_verifies_propagate_2 local.RedParsedWhileFalse(5))
  
          show ?thesis using \<open>j = Suc j'\<close> succ_cfg_correct None rest concrete_inter2 succ_correct by blast
        next 
          case RedParsedWhile_InvFail thus ?thesis using assms(7) block_local_rel cfg_correct dag_verifies_propagate_2 first_step assms(4) by blast
        qed auto
      next
        case (Some concrete_loop_guard)
        then show ?thesis 
        proof cases
          assume guard_true: "(red_expr A \<Lambda> \<Gamma> \<Omega> concrete_loop_guard ns1 (BoolV True))"
          hence guard_not_false: "\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> concrete_loop_guard ns1 (BoolV False))" using expr_eval_determ by blast
  
          from first_step show ?thesis 
          proof cases
            case RedParsedWhileTrue
            hence concrete_inter3: "(inter_bb, inter_cont, inter_state) = (bb0, convert_list_to_cont ((BigBlock name [] any_str any_tr)#(rev body_bbs)) (KEndBlock cont1), (Normal ns1))"
              using bb_successor_while Some by blast
  
            from first_step
            have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
              by (metis Pair_inject assms(4) assms(7) block_local_rel cfg_correct concrete_inter3 dag_verifies_propagate dag_verifies_propagate_2)
  
            show ?thesis using \<open>j = Suc j'\<close> succ_cfg_correct Some guard_true rest concrete_inter3 succ_correct assms(4) by blast 
        next 
            case RedParsedWhile_InvFail thus ?thesis using assms(7) block_local_rel cfg_correct dag_verifies_propagate_2 first_step assms(4) by blast
        qed (auto simp add: bb_successor_while Some guard_not_false)
      next
        assume guard_not_true: "\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> concrete_loop_guard ns1 (BoolV True))"
        thus ?thesis 
        proof cases
          assume guard_false: "(red_expr A \<Lambda> \<Gamma> \<Omega> concrete_loop_guard ns1 (BoolV False))"
  
          from first_step show ?thesis 
          proof cases
            case RedParsedWhileFalse
            hence concrete_inter4: "(inter_bb, inter_cont, inter_state) = ((BigBlock name [] None None), KEndBlock cont1, (Normal ns1))" by simp

          from first_step
          have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
            by (metis assms(4) assms(7) block_local_rel cfg_correct dag_verifies_propagate dag_verifies_propagate_2 local.RedParsedWhileFalse(5))
  
            show ?thesis using \<open>j = Suc j'\<close> succ_cfg_correct Some guard_false rest concrete_inter4 succ_correct by blast
          next
            case RedParsedWhile_InvFail thus ?thesis using Some bb_successor_while guard_not_true by blast
          qed (auto simp add: bb_successor_while Some guard_not_true)
        next
          assume guard_not_false: "\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> concrete_loop_guard ns1 (BoolV False))"
          from first_step show ?thesis
          proof cases
            case RedParsedWhile_InvFail thus ?thesis using Some bb_successor_while guard_not_true by blast
          qed (auto simp add: bb_successor_while Some guard_not_true guard_not_false)
        qed
      qed
    qed
  qed
qed 

text \<open>Global lemma for an ast-bigblock with a non-empty set of simple cmds which enters an if-statement after executing its simple cmds.\<close>
lemma block_global_rel_if_successor:
  assumes block_rel: "ast_cfg_rel None [] bb cs2"
  and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, cont0, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and "bb = (BigBlock name cs1 any_str any_tr)"
  and "node_to_block(G) ! n = cs2"
  and cfg_correct: "(\<And> m2 s2. ((red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G (Inl n, Normal ns1) (m2, s2)) \<Longrightarrow> (s2 \<noteq> Failure)))"
  and bb_successor_if: "any_str = Some (ParsedIf cont_guard (then0#then_bbs) (else0#else_bbs))"
  and block_local_rel:
        "\<And> reached_bb_inter reached_cont_inter reached_state_inter. (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name cs1 any_str any_tr), cont0, (Normal ns1)) (reached_bb_inter, reached_cont_inter, reached_state_inter)) \<Longrightarrow> 
        (\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cs2 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure))) \<Longrightarrow> 
        cs1 \<noteq> [] \<Longrightarrow> cs2 \<noteq> [] \<Longrightarrow>  
        (reached_state_inter \<noteq> Failure  \<and> (\<forall>ns1'. reached_state_inter = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns1\<rangle> [\<rightarrow>] Normal ns1')))"
  and succ_correct: 
       "\<And> ns1'' block_guard k.
         k < j \<Longrightarrow> 
        (\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), Normal ns1'') -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure))) \<Longrightarrow>
        ((cont_guard = Some block_guard) \<and> 
          (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1'' (BoolV True)) \<and> 
          A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (then0, convert_list_to_cont (rev then_bbs) cont0, (Normal ns1'')) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state)) \<or> 
        ((cont_guard = Some block_guard) \<and> 
          (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1'' (BoolV False)) \<and> 
          A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (else0, convert_list_to_cont (rev else_bbs) cont0, (Normal ns1'')) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state)) \<or>
        ( (cont_guard = None) \<and> 
          ((A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (then0, convert_list_to_cont (rev then_bbs) cont0, (Normal ns1'')) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state)) \<or>
          (A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (else0, convert_list_to_cont (rev else_bbs) cont0, (Normal ns1'')) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state))) ) \<Longrightarrow>  
        (Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)" 
  using assms
proof cases
  case Rel_Main_test
  have not_end: "(cont0 \<noteq> KStop) \<or> any_str \<noteq> None \<or> any_tr \<noteq> None" using bb_successor_if by simp
  show ?thesis
  proof (cases cs2)
    case Nil 
    thus ?thesis
    proof (cases j)
      case 0
      hence "(reached_bb, reached_cont, reached_state) = ((BigBlock name cs1 any_str any_tr), cont0, (Normal ns1))" using ast_trace assms(3) by auto
      then show ?thesis by (simp add: Ast.valid_configuration_def bb_successor_if) 
    next
      case 1: (Suc j')
        from this assms(3) obtain snd_inter_bb snd_inter_cont snd_inter_state where
          snd_step: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name [] any_str any_tr), cont0, (Normal ns1))  (snd_inter_bb, snd_inter_cont, snd_inter_state)" and
          snd_rest_of_steps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (snd_inter_bb, snd_inter_cont, snd_inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)"
          by (metis ast_trace bigblock.inject local.Nil local.Rel_Main_test relpowp_Suc_E2 surj_pair)
  
        thus ?thesis 
        proof (cases cont_guard)
          case None
          from snd_step this show ?thesis
          proof cases
            case RedParsedIfTrue
            hence eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (then0, convert_list_to_cont (rev then_bbs) cont0, (Normal ns1))" using None bb_successor_if 1 by auto
  
            have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), (Normal ns1)) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
              using assms(4) cfg_correct correctness_propagates_through_empty local.Nil by blast
  
            have "j' < j" using 1 using Suc_lessD by blast
            
            thus ?thesis using eq snd_rest_of_steps succ_correct None succ_cfg_correct by blast
          next
            case RedParsedIfFalse
            hence eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (else0, convert_list_to_cont (rev else_bbs) cont0, (Normal ns1))" using None bb_successor_if 1 by auto
  
            from snd_step 
            have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), (Normal ns1)) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
              using assms(4) cfg_correct correctness_propagates_through_empty local.Nil by blast
  
            have "j' < j" using 1 using Suc_lessD by blast
  
            thus ?thesis using eq snd_rest_of_steps succ_correct None succ_cfg_correct by blast
          qed (auto simp add: bb_successor_if)
        next
          case (Some block_guard)
          then show ?thesis 
          proof cases
            assume guard_true: "(red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1 (BoolV True))"
            hence guard_not_false: "\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1 (BoolV False))" using expr_eval_determ by blast
            from snd_step have eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (then0, convert_list_to_cont (rev then_bbs) cont0, Normal ns1)" 
            proof cases
              case RedParsedIfTrue thus ?thesis using guard_true bb_successor_if by (simp add: RedParsedIfTrue)
            qed (auto simp add: guard_not_false bb_successor_if Some)
  
            from snd_step 
            have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), Normal ns1) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
              using assms(4) cfg_correct correctness_propagates_through_empty local.Nil by blast
  
            have "j' < j" using 1 using Suc_lessD by blast
            
            thus ?thesis using eq guard_true snd_rest_of_steps succ_correct Some succ_cfg_correct by blast
          next
            assume guard_not_true: "\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1 (BoolV True))"
            thus ?thesis 
            proof cases
              assume guard_false: "(red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1 (BoolV False))"
              from snd_step have eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (else0, convert_list_to_cont (rev else_bbs) cont0, Normal ns1)" 
              proof cases
                case RedParsedIfFalse thus ?thesis using guard_false bb_successor_if by (simp add: RedParsedIfFalse)
              qed (auto simp add: guard_not_true bb_successor_if Some)
  
              from snd_step 
              have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), Normal ns1) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
                using assms(4) cfg_correct correctness_propagates_through_empty local.Nil by blast              
  
              have "j' < j" using 1 using Suc_lessD by blast
        
              thus ?thesis using eq guard_false snd_rest_of_steps succ_correct Some succ_cfg_correct by blast
            next
              assume guard_not_false2: "(\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1 (BoolV False)))" and  
                     guard_not_true2: "(\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1 (BoolV True)))"
              thus ?thesis
              proof -
                from snd_step have False using guard_not_false2 guard_not_true2 bb_successor_if Some 
                  by (cases) auto
                thus ?thesis by simp
              qed
            qed  
          qed 
        qed
      qed
  next
    case (Cons) 
    hence "cs1 \<noteq> []" using assms(3) local.Rel_Main_test by auto
    thus ?thesis
    proof (cases j)
      case 0
      hence "(reached_bb, reached_cont, reached_state) = ((BigBlock name cs1 any_str any_tr), cont0, (Normal ns1))" using ast_trace assms(3) by auto
      then show ?thesis by (simp add: Ast.valid_configuration_def bb_successor_if) 
    next
      case 1: (Suc j')
      from this assms(3) obtain inter_bb inter_cont inter_state where
        first_step: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name cs1 any_str any_tr), cont0, (Normal ns1)) (inter_bb, inter_cont, inter_state)" and
        rest_of_steps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb, inter_cont, inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)" 
        by (metis ast_trace get_state.cases relpowp_Suc_E2)
  
      from cfg_correct Cons \<open>node_to_block(G) ! n = cs2\<close> 
      have local_rel_corr: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> (cs2) (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))"
        using dag_verifies_propagate_2 by blast
  
      from local_rel_corr first_step Cons
      have a2: "(inter_state \<noteq> Failure  \<and> (\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns1\<rangle> [\<rightarrow>] Normal ns1')))" 
        using block_local_rel local.Rel_Main_test assms(3) by blast
  
      from first_step Cons \<open>cs1 \<noteq> []\<close>
      have a1: "(inter_bb, inter_cont, inter_state) = ((BigBlock name [] any_str any_tr), cont0, inter_state)"
      proof cases
        case RedSimpleCmds then show ?thesis by (auto simp add: RedSimpleCmds)
      qed auto
  
      show ?thesis 
      proof (cases inter_state)
        case 2: (Normal x1)
        from rest_of_steps show ?thesis 
        proof (cases j')
          case 0
          then show ?thesis 
            by (metis Ast.valid_configuration_def a1 a2 bb_successor_if get_state.simps is_final.simps(3) relpowp_0_E rest_of_steps) 
        next
          case 3: (Suc j'')
          from this rest_of_steps obtain snd_inter_bb snd_inter_cont snd_inter_state where
            snd_step: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name [] any_str any_tr), cont0, inter_state)  (snd_inter_bb, snd_inter_cont, snd_inter_state)" and
            snd_rest_of_steps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (snd_inter_bb, snd_inter_cont, snd_inter_state) -n\<longrightarrow>^j'' (reached_bb, reached_cont, reached_state)"
            by (metis a1 get_state.cases relpowp_Suc_D2)
  
          thus ?thesis 
          proof (cases cont_guard)
            case None
            from snd_step this show ?thesis
            proof cases
              case RedParsedIfTrue
              hence eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (then0, convert_list_to_cont (rev then_bbs) cont0, inter_state)" using None bb_successor_if 1 by auto
  
              from first_step 
              have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
              proof cases
                case RedSimpleCmds show ?thesis using 2 eq RedSimpleCmds(3) dag_verifies_propagate assms(3-4) Rel_Main_test(1) cfg_correct by blast
              qed (auto simp add: \<open>cs1 \<noteq> Nil\<close>)
  
              have "j'' < j" using 1 3 using Suc_lessD by blast
              
              thus ?thesis using eq snd_rest_of_steps succ_correct None 2 succ_cfg_correct by blast
            next
              case RedParsedIfFalse
              hence eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (else0, convert_list_to_cont (rev else_bbs) cont0, inter_state)" using None bb_successor_if 1 by auto
  
              from first_step 
              have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
              proof cases
                case RedSimpleCmds show ?thesis using 2 eq RedSimpleCmds(3) dag_verifies_propagate assms(3-4) Rel_Main_test(1) cfg_correct by blast
              qed (auto simp add: \<open>cs1 \<noteq> Nil\<close>)
  
              have "j'' < j" using 1 3 using Suc_lessD by blast
  
              thus ?thesis using eq snd_rest_of_steps succ_correct None 2 succ_cfg_correct by blast
            qed (auto simp add: bb_successor_if 2)
          next
            case (Some block_guard)
            then show ?thesis 
            proof cases
              assume guard_true: "(red_expr A \<Lambda> \<Gamma> \<Omega> block_guard x1 (BoolV True))"
              hence guard_not_false: "\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard x1 (BoolV False))" using expr_eval_determ by blast
              from snd_step have eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (then0, convert_list_to_cont (rev then_bbs) cont0, inter_state)" 
              proof cases
                case RedParsedIfTrue thus ?thesis using guard_true bb_successor_if by (simp add: RedParsedIfTrue)
              qed (auto simp add: guard_not_false bb_successor_if 2 Some)
  
              from first_step 
              have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
              proof cases
                case RedSimpleCmds show ?thesis using 2 eq RedSimpleCmds(3) dag_verifies_propagate assms(3-4) Rel_Main_test(1) cfg_correct by blast
              qed (auto simp add: \<open>cs1 \<noteq> Nil\<close>)
  
              have "j'' < j" using 1 3 using Suc_lessD by blast
              
              thus ?thesis using eq guard_true snd_rest_of_steps succ_correct Some succ_cfg_correct 2 by blast
            next
              assume guard_not_true: "\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard x1 (BoolV True))"
              thus ?thesis 
              proof cases
                assume guard_false: "(red_expr A \<Lambda> \<Gamma> \<Omega> block_guard x1 (BoolV False))"
                from snd_step have eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (else0, convert_list_to_cont (rev else_bbs) cont0, inter_state)" 
                proof cases
                  case RedParsedIfFalse thus ?thesis using guard_false bb_successor_if by (simp add: RedParsedIfFalse)
                qed (auto simp add: guard_not_true bb_successor_if 2 Some)
  
                from first_step 
                have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
                proof cases
                  case RedSimpleCmds show ?thesis using 2 eq RedSimpleCmds(3) dag_verifies_propagate assms(3-4) Rel_Main_test(1) cfg_correct by blast
                qed (auto simp add: \<open>cs1 \<noteq> Nil\<close>)              
  
                have "j'' < j" using 1 3 using Suc_lessD by blast
          
                thus ?thesis using eq guard_false snd_rest_of_steps succ_correct Some 2 succ_cfg_correct by blast
              next
                assume guard_not_false2: "(\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard x1 (BoolV False)))" and  
                       guard_not_true2: "(\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard x1 (BoolV True)))"
                thus ?thesis
                proof -
                  from snd_step have False using guard_not_false2 guard_not_true2 bb_successor_if Some 2 
                    by (cases) auto
                  thus ?thesis by simp
                qed
              qed  
            qed 
          qed
        qed
      next
        case Failure
        then show ?thesis
          using \<open>inter_state \<noteq> Failure \<and> (\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2,Normal ns1\<rangle> [\<rightarrow>] Normal ns1')\<close> 
          by linarith
      next
        case Magic
        then show ?thesis by (metis Ast.valid_configuration_def a2 get_state.simps magic_propagates rest_of_steps state.distinct(3))
      qed
    qed
  qed
next
  case Rel_Invs
  hence "cs2 = []" by simp
  have not_end: "(cont0 \<noteq> KStop) \<or> any_str \<noteq> None \<or> any_tr \<noteq> None" using bb_successor_if by simp
  show ?thesis
  proof (cases cs2)
    case Nil 
    thus ?thesis
    proof (cases j)
      case 0
      hence "(reached_bb, reached_cont, reached_state) = ((BigBlock name cs1 any_str any_tr), cont0, (Normal ns1))" using ast_trace assms(3) by auto
      then show ?thesis by (simp add: Ast.valid_configuration_def bb_successor_if) 
    next
      case 1: (Suc j')
        from this assms(3) obtain snd_inter_bb snd_inter_cont snd_inter_state where
          snd_step: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name [] any_str any_tr), cont0, (Normal ns1))  (snd_inter_bb, snd_inter_cont, snd_inter_state)" and
          snd_rest_of_steps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (snd_inter_bb, snd_inter_cont, snd_inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)" 
          using Rel_Invs
          by (metis ast_trace bigblock.inject local.Rel_Invs(1) relpowp_Suc_E2 surj_pair)
  
        thus ?thesis 
        proof (cases cont_guard)
          case None
          from snd_step this show ?thesis
          proof cases
            case RedParsedIfTrue
            hence eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (then0, convert_list_to_cont (rev then_bbs) cont0, (Normal ns1))" using None bb_successor_if 1 by auto
  
            have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), (Normal ns1)) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
              using assms(4) cfg_correct correctness_propagates_through_empty local.Nil by blast
  
            have "j' < j" using 1 using Suc_lessD by blast
            
            thus ?thesis using eq snd_rest_of_steps succ_correct None succ_cfg_correct by blast
          next
            case RedParsedIfFalse
            hence eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (else0, convert_list_to_cont (rev else_bbs) cont0, (Normal ns1))" using None bb_successor_if 1 by auto
  
            from snd_step 
            have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), (Normal ns1)) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
              using assms(4) cfg_correct correctness_propagates_through_empty local.Nil by blast
  
            have "j' < j" using 1 using Suc_lessD by blast
  
            thus ?thesis using eq snd_rest_of_steps succ_correct None succ_cfg_correct by blast
          qed (auto simp add: bb_successor_if)
        next
          case (Some block_guard)
          then show ?thesis 
          proof cases
            assume guard_true: "(red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1 (BoolV True))"
            hence guard_not_false: "\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1 (BoolV False))" using expr_eval_determ by blast
            from snd_step have eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (then0, convert_list_to_cont (rev then_bbs) cont0, Normal ns1)" 
            proof cases
              case RedParsedIfTrue thus ?thesis using guard_true bb_successor_if by (simp add: RedParsedIfTrue)
            qed (auto simp add: guard_not_false bb_successor_if Some)
  
            from snd_step 
            have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), Normal ns1) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
              using assms(4) cfg_correct correctness_propagates_through_empty local.Nil by blast
  
            have "j' < j" using 1 using Suc_lessD by blast
            
            thus ?thesis using eq guard_true snd_rest_of_steps succ_correct Some succ_cfg_correct by blast
          next
            assume guard_not_true: "\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1 (BoolV True))"
            thus ?thesis 
            proof cases
              assume guard_false: "(red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1 (BoolV False))"
              from snd_step have eq: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (else0, convert_list_to_cont (rev else_bbs) cont0, Normal ns1)" 
              proof cases
                case RedParsedIfFalse thus ?thesis using guard_false bb_successor_if by (simp add: RedParsedIfFalse)
              qed (auto simp add: guard_not_true bb_successor_if Some)
  
              from snd_step 
              have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), Normal ns1) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
                using assms(4) cfg_correct correctness_propagates_through_empty local.Nil by blast              
  
              have "j' < j" using 1 using Suc_lessD by blast
        
              thus ?thesis using eq guard_false snd_rest_of_steps succ_correct Some succ_cfg_correct by blast
            next
              assume guard_not_false2: "(\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1 (BoolV False)))" and  
                     guard_not_true2: "(\<not> (red_expr A \<Lambda> \<Gamma> \<Omega> block_guard ns1 (BoolV True)))"
              thus ?thesis
              proof -
                from snd_step have False using guard_not_false2 guard_not_true2 bb_successor_if Some 
                  by (cases) auto
                thus ?thesis by simp
              qed
            qed  
          qed 
        qed
      qed
  next
    case (Cons) thus ?thesis using \<open>cs2 = []\<close> by simp
  qed
qed

text \<open>Global lemma for an ast-bigblock with a non-empty set of simple cmds which is the first bigblock in the else-branch of an if-statement.\<close>
lemma block_global_rel_if_false:
  assumes block_rel: "ast_cfg_rel None [] bb cs2"
  and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, cont0, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and "bb = (BigBlock name cs1 any_str any_tr)"
  and "cs1 \<noteq> Nil"
  and "cs2 \<noteq> Nil"
  and "node_to_block(G) ! n = cs3"
  and "cs3 = (c#cs2)"
  and cfg_correct: "(\<And> m2 s2. ((red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G (Inl n, Normal ns1) (m2, s2)) \<Longrightarrow> (s2 \<noteq> Failure)))"
  and trivial_bb_successor: "(cont0 = KSeq bb1 cont1) \<and> any_str = None \<and> any_tr = None"
  and "c = Assume some_cmd"
  and "(UnOp Not block_guard) \<sim> some_cmd"
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(UnOp Not block_guard), ns1\<rangle> \<Down> LitV (LBool True)"
  and block_local_rel: 
        "\<And> reached_bb_inter reached_cont_inter reached_state_inter. (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb, cont0, (Normal ns1)) (reached_bb_inter, reached_cont_inter, reached_state_inter)) \<Longrightarrow> 
        (\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cs3 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure))) \<Longrightarrow>   
        (reached_state_inter \<noteq> Failure  \<and> (\<forall>ns1'. reached_state_inter = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs3, Normal ns1\<rangle> [\<rightarrow>] Normal ns1')))"
  and succ_correct: 
       "\<And>  ns1'' k.
        k < j \<Longrightarrow> 
        \<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), Normal ns1'') -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)) \<Longrightarrow>
        A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb1, cont1, (Normal ns1'')) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state) \<Longrightarrow> 
        (Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
     shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)" 
  using assms
proof cases
  case Rel_Main_test
  have not_end: "(cont0 \<noteq> KStop) \<or> any_str \<noteq> None \<or> any_tr \<noteq> None" using trivial_bb_successor by simp
  from ast_trace show ?thesis
  proof (cases j)
    case 0
    hence "(reached_bb, reached_cont, reached_state) = ((BigBlock name cs1 any_str any_tr), cont0, (Normal ns1))" using ast_trace assms(3) by fastforce
    then show ?thesis unfolding Ast.valid_configuration_def by (simp add: trivial_bb_successor)
  next
    case succ_0: (Suc j')
    from this assms(3) obtain inter_bb inter_cont inter_state where
      first_step: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name cs1 any_str any_tr), cont0, (Normal ns1)) (inter_bb, inter_cont, inter_state)" and
      rest_of_steps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb, inter_cont, inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)" 
      by (metis ast_trace prod_cases3 relpowp_Suc_D2)

    from cfg_correct \<open>cs2 \<noteq> Nil\<close> \<open>node_to_block(G) ! n = cs3\<close> 
    have local_rel_corr: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cs3 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))"
      using dag_verifies_propagate_2 by blast

    from local_rel_corr first_step 
    have a2: "(inter_state \<noteq> Failure  \<and> (\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs3, Normal ns1\<rangle> [\<rightarrow>] Normal ns1')))" 
      using block_local_rel assms(3) by simp

    from first_step \<open>cs1 \<noteq> Nil\<close> 
    have a1: "(inter_bb, inter_cont, inter_state) = ((BigBlock name [] any_str any_tr), cont0, inter_state)"
    proof cases
      case RedSimpleCmds then show ?thesis by (auto simp add: RedSimpleCmds)
    qed auto

    show ?thesis 
    proof (cases inter_state)
      case 1: (Normal x1)
      from rest_of_steps show ?thesis 
      proof (cases j')
        case 0
        then show ?thesis
          by (metis Ast.valid_configuration_def a1 a2 get_state.simps is_final.simps(5) relpowp_0_E rest_of_steps trivial_bb_successor)
      next
        case 2: (Suc j'')
        from this rest_of_steps obtain snd_inter_bb snd_inter_cont snd_inter_state where
          snd_step: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name [] any_str any_tr), cont0, inter_state)  (snd_inter_bb, snd_inter_cont, snd_inter_state)" and
          snd_rest_of_steps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (snd_inter_bb, snd_inter_cont, snd_inter_state) -n\<longrightarrow>^j'' (reached_bb, reached_cont, reached_state)"
          by (metis a1 get_state.cases relpowp_Suc_D2)
        from snd_step have snd_step_equiv: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (bb1, cont1, inter_state)"
        proof cases
          case RedSkip thus ?thesis using trivial_bb_successor by (simp add: RedSkip)
        qed (auto simp add: trivial_bb_successor "1")

        from first_step 
        have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
        proof cases
          case RedSimpleCmds 
          hence cmds_red: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c#cs2, Normal ns1\<rangle> [\<rightarrow>] inter_state" 
            using  "1" a2 assms(7) 
            by blast
          show ?thesis by (metis (no_types, lifting) "1" RedNormalSucc assms(6-7) cfg_correct cmds_red converse_rtranclp_into_rtranclp)
        qed (auto simp add: \<open>cs1 \<noteq> Nil\<close>) 

        have "j'' < j" using succ_0 2 by simp

        then show ?thesis using snd_step_equiv succ_correct snd_rest_of_steps "1" succ_cfg_correct by blast 
      qed
    next
      case Failure
      then show ?thesis
        using \<open>inter_state \<noteq> Failure \<and> (\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs3,Normal ns1\<rangle> [\<rightarrow>] Normal ns1')\<close> 
        by linarith
    next
      case Magic
      then show ?thesis by (metis Ast.valid_configuration_def a2 get_state.simps magic_propagates rest_of_steps state.distinct(3))
    qed
  qed
qed auto

text \<open>Global lemma for an ast-bigblock with a non-empty set of simple cmds which is the first bigblock in the then-branch of an if-statement.\<close>
lemma block_global_rel_if_true:
  assumes block_rel: "ast_cfg_rel None [] bb cs2"
  and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, cont0, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and "bb = (BigBlock name cs1 any_str any_tr)"
  and "cs1 \<noteq> Nil"
  and "cs2 \<noteq> Nil"
  and "node_to_block(G) ! n = cs3"
  and "cs3 = c#cs2"
  and cfg_correct: "(\<And> m2 s2. ((red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G (Inl n, Normal ns1) (m2, s2)) \<Longrightarrow> (s2 \<noteq> Failure)))"
  and trivial_bb_successor: "(cont0 = KSeq bb1 cont1) \<and> any_str = None \<and> any_tr = None"
  and "c = Assume block_guard"
  and trace_is_possible: "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>block_guard, ns1\<rangle> \<Down> LitV (LBool True)"
  and block_local_rel: 
        "\<And> reached_bb_inter reached_cont_inter reached_state_inter. (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb, cont0, (Normal ns1)) (reached_bb_inter, reached_cont_inter, reached_state_inter)) \<Longrightarrow> 
        (\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cs3 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure))) \<Longrightarrow>   
        (reached_state_inter \<noteq> Failure  \<and> (\<forall>ns1'. reached_state_inter = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs3, Normal ns1\<rangle> [\<rightarrow>] Normal ns1')))"
  and succ_correct: 
       "\<And>  ns1'' k.
        k < j \<Longrightarrow> 
        \<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), Normal ns1'') -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)) \<Longrightarrow>
        A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb1, cont1, (Normal ns1'')) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state) \<Longrightarrow> 
        (Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
     shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)" 
  using assms
proof cases
  case Rel_Main_test
  have not_end: "(cont0 \<noteq> KStop) \<or> any_str \<noteq> None \<or> any_tr \<noteq> None" using trivial_bb_successor by simp
  from ast_trace show ?thesis
  proof (cases j)
    case 0
    hence "(reached_bb, reached_cont, reached_state) = ((BigBlock name cs1 any_str any_tr), cont0, (Normal ns1))" using ast_trace assms(3) by auto
    then show ?thesis unfolding Ast.valid_configuration_def by (metis assms(4) get_state.simps is_final.simps(2) neq_Nil_conv state.distinct(1))
  next
    case succ_0: (Suc j')
    from this assms(3) obtain inter_bb inter_cont inter_state where
      first_step: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name cs1 any_str any_tr), cont0, (Normal ns1)) (inter_bb, inter_cont, inter_state)" and
      rest_of_steps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb, inter_cont, inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)" 
      by (metis ast_trace get_state.cases relpowp_Suc_D2)

    from cfg_correct \<open>cs2 \<noteq> Nil\<close> \<open>node_to_block(G) ! n = cs3\<close> 
    have local_rel_corr: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cs3 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))"
      using dag_verifies_propagate_2 by blast

    from local_rel_corr first_step 
    have a2: "(inter_state \<noteq> Failure  \<and> (\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs3, Normal ns1\<rangle> [\<rightarrow>] Normal ns1')))" 
      using block_local_rel assms(3) by simp

    from first_step \<open>cs1 \<noteq> Nil\<close> 
    have a1: "(inter_bb, inter_cont, inter_state) = ((BigBlock name [] any_str any_tr), cont0, inter_state)"
    proof cases
      case RedSimpleCmds then show ?thesis by (auto simp add: RedSimpleCmds)
    qed auto

    show ?thesis 
    proof (cases inter_state)
      case 1: (Normal x1)
      from rest_of_steps show ?thesis 
      proof (cases j')
        case 0
        then show ?thesis 
          by (metis valid_configuration_def a1 a2 get_state.simps is_final.simps(5) relpowp_0_E rest_of_steps trivial_bb_successor)
      next
        case 2: (Suc j'')
        from this rest_of_steps obtain snd_inter_bb snd_inter_cont snd_inter_state where
          snd_step: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name [] any_str any_tr), cont0, inter_state)  (snd_inter_bb, snd_inter_cont, snd_inter_state)" and
          snd_rest_of_steps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (snd_inter_bb, snd_inter_cont, snd_inter_state) -n\<longrightarrow>^j'' (reached_bb, reached_cont, reached_state)"
          by (metis a1 get_state.cases relpowp_Suc_D2)

        from snd_step have snd_step_equiv: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (bb1, cont1, inter_state)"
        proof cases
          case RedSkip thus ?thesis using trivial_bb_successor by (simp add: RedSkip)
        qed (auto simp add: trivial_bb_successor "1")

        from first_step 
        have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
        proof cases
          case RedSimpleCmds 
          hence cmds_red: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c#cs2, Normal ns1\<rangle> [\<rightarrow>] inter_state" 
            using Rel_Main_test(1) \<open>c = Assume block_guard\<close> trace_is_possible RedAssumeOk RedCmdListCons assms(3) by blast
          show ?thesis using "1" assms(6-7) cfg_correct cmds_red dag_verifies_propagate by blast
        qed (auto simp add: \<open>cs1 \<noteq> Nil\<close>) 

        have "j'' < j" using succ_0 2 by simp

        then show ?thesis using snd_step_equiv succ_correct snd_rest_of_steps "1" succ_cfg_correct by blast 
      qed
    next
      case Failure
      then show ?thesis
        using \<open>inter_state \<noteq> Failure \<and> (\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs3,Normal ns1\<rangle> [\<rightarrow>] Normal ns1')\<close> 
        by linarith
    next
      case Magic
      then show ?thesis by (metis valid_configuration_def a2 get_state.simps magic_propagates rest_of_steps state.simps(5))
    qed
  qed
qed auto

text \<open>Global lemma for a generic ast-bigblock with a non-empty set of simple cmds.\<close>
lemma block_global_rel_generic:
  assumes block_rel: "ast_cfg_rel None [] bb cs2"
  and ast_trace: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb, cont0, (Normal ns1)) -n\<longrightarrow>^j (reached_bb, reached_cont, reached_state)"
  and "bb = (BigBlock name cs1 any_str any_tr)"
  and "cs1 \<noteq> Nil"
  and "cs2 \<noteq> Nil"
  and "node_to_block(G) ! n = cs2"
  and cfg_correct: "(\<And> m2 s2. ((red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> G (Inl n, Normal ns1) (m2, s2)) \<Longrightarrow> (s2 \<noteq> Failure)))"
  and trivial_bb_successor: "(cont0 = KSeq bb1 cont1) \<and> any_str = None \<and> any_tr = None"
  and block_local_rel: 
        "\<And> reached_bb_inter reached_cont_inter reached_state_inter. (red_bigblock A M \<Lambda> \<Gamma> \<Omega> T (bb, cont0, (Normal ns1)) (reached_bb_inter, reached_cont_inter, reached_state_inter)) \<Longrightarrow> 
        (\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cs2 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure))) \<Longrightarrow>   
        (reached_state_inter \<noteq> Failure  \<and> (\<forall>ns1'. reached_state_inter = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns1\<rangle> [\<rightarrow>] Normal ns1')))"
  and succ_correct: 
       "\<And>  ns1'' k.
        k < j \<Longrightarrow> 
        \<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), Normal ns1'') -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)) \<Longrightarrow>
        A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (bb1, cont1, (Normal ns1'')) -n\<longrightarrow>^k (reached_bb, reached_cont, reached_state) \<Longrightarrow> 
        (Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)"
  shows "(Ast.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts reached_bb reached_cont reached_state)" 
  using assms
proof cases
  case Rel_Main_test
  have not_end: "(cont0 \<noteq> KStop) \<or> any_str \<noteq> None \<or> any_tr \<noteq> None" using trivial_bb_successor by simp
  from ast_trace show ?thesis
  proof (cases j)
    case 0
    hence "(reached_bb, reached_cont, reached_state) = ((BigBlock name cs1 any_str any_tr), cont0, (Normal ns1))" using ast_trace assms(3) by auto
    then show ?thesis unfolding Ast.valid_configuration_def by (simp add: trivial_bb_successor)
  next
    case succ_0: (Suc j')
    from this assms(3) obtain inter_bb inter_cont inter_state where
      first_step: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name cs1 any_str any_tr), cont0, (Normal ns1)) (inter_bb, inter_cont, inter_state)" and
      rest_of_steps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (inter_bb, inter_cont, inter_state) -n\<longrightarrow>^j' (reached_bb, reached_cont, reached_state)"
      by (metis ast_trace get_state.cases relpowp_Suc_D2)

    from cfg_correct \<open>cs2 \<noteq> Nil\<close> \<open>node_to_block(G) ! n = cs2\<close> 
    have local_rel_corr: "(\<And> s2'.((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> cs2 (Normal ns1) s2') \<Longrightarrow> (s2' \<noteq> Failure)))"
      using dag_verifies_propagate_2 by blast

    from local_rel_corr first_step 
    have a2: "(inter_state \<noteq> Failure  \<and> (\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns1\<rangle> [\<rightarrow>] Normal ns1')))" 
      using block_local_rel assms(3) by simp

    from first_step \<open>cs1 \<noteq> Nil\<close> 
    have a1: "(inter_bb, inter_cont, inter_state) = ((BigBlock name [] any_str any_tr), cont0, inter_state)"
    proof cases
      case RedSimpleCmds then show ?thesis by (auto simp add: RedSimpleCmds)
    qed auto

    show ?thesis 
    proof (cases inter_state)
      case 1: (Normal x1)
      from rest_of_steps show ?thesis 
      proof (cases j')
        case 0
        then show ?thesis 
          by (metis valid_configuration_def a1 a2 get_state.simps is_final.simps(5) relpowp_0_E rest_of_steps trivial_bb_successor)
      next
        case 2: (Suc j'')
        from this rest_of_steps obtain snd_inter_bb snd_inter_cont snd_inter_state where
          snd_step: "red_bigblock A M \<Lambda> \<Gamma> \<Omega> T ((BigBlock name [] any_str any_tr), cont0, inter_state)  (snd_inter_bb, snd_inter_cont, snd_inter_state)" and
          snd_rest_of_steps: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> (snd_inter_bb, snd_inter_cont, snd_inter_state) -n\<longrightarrow>^j'' (reached_bb, reached_cont, reached_state)"
          by (metis a1 get_state.cases relpowp_Suc_D2)

        from snd_step have snd_step_equiv: "(snd_inter_bb, snd_inter_cont, snd_inter_state) = (bb1, cont1, inter_state)"
        proof cases
          case RedSkip thus ?thesis using trivial_bb_successor by (simp add: RedSkip)
        qed (auto simp add: trivial_bb_successor "1")

        from first_step 
        have succ_cfg_correct: "(\<forall>msuc2.  List.member (out_edges(G) ! n) msuc2 \<longrightarrow> (\<forall>m3 s3. ((A,M,\<Lambda>,\<Gamma>,\<Omega>,G \<turnstile> (Inl(msuc2), inter_state) -n\<rightarrow>* (m3, s3)) \<longrightarrow> s3 \<noteq> Failure)))"
        proof cases
          case RedSimpleCmds show ?thesis using 1 snd_step_equiv  RedSimpleCmds(3) dag_verifies_propagate Rel_Main_test(1) cfg_correct assms(6) assms(3) by blast
        qed (auto simp add: \<open>cs1 \<noteq> Nil\<close>) 

        have "j'' < j" using succ_0 2 by simp

        then show ?thesis using snd_step_equiv succ_correct snd_rest_of_steps "1" succ_cfg_correct by blast
      qed
    next
      case Failure
      then show ?thesis
        using \<open>inter_state \<noteq> Failure \<and> (\<forall>ns1'. inter_state = Normal ns1' \<longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2,Normal ns1\<rangle> [\<rightarrow>] Normal ns1')\<close> 
        by linarith
    next
      case Magic
      then show ?thesis by (metis valid_configuration_def a2 get_state.simps magic_propagates rest_of_steps state.distinct(3))
    qed
  qed
qed auto

text \<open>Helper lemmas used to complete the procedure correctness proof\<close>

lemma end_to_end_util2:
  assumes AExpanded: "\<And> \<Gamma> end_bb end_cont end_state ns M.
           rtranclp (red_bigblock B M \<Lambda> \<Gamma> [] ast) (init_ast ast ns) (end_bb, end_cont, end_state) \<Longrightarrow>
           (\<And> v. (closed ((type_of_val B) v))) \<Longrightarrow>
           (\<And> t. ((closed t) \<Longrightarrow> (\<exists> v. (((type_of_val B) v) = t)))) \<Longrightarrow>
           (fun_interp_wf B fun_decls \<Gamma>) \<Longrightarrow>
           (axiom_assm B \<Gamma> constants (ns::(('a)nstate)) axioms) \<Longrightarrow>
           (expr_all_sat B \<Lambda> \<Gamma> [] ns all_pres) \<Longrightarrow>
           (state_typ_wf B [] (local_state ns) (snd \<Lambda>)) \<Longrightarrow>
           (state_typ_wf B [] (global_state ns) (fst \<Lambda>)) \<Longrightarrow>
           ((global_state ns) = (old_global_state ns)) \<Longrightarrow>
           ((binder_state ns) = Map.empty) \<Longrightarrow> 
           (Ast.valid_configuration B \<Lambda> \<Gamma> [] checked_posts end_bb end_cont end_state)" and
          "all_pres = proc_all_pres proc_ast" and
          "checked_posts = proc_checked_posts proc_ast" and
          ABody: "ast_procedure.proc_body proc_ast = Some (locals, ast)" and
          AVarContext:"\<Lambda> = (constants@global_vars, (proc_args proc_ast)@locals)" and
          ARets:"proc_rets proc_ast = []" and
         (* "fun_decls = prog_funcs prog" and
          "axs = prog_axioms prog" and*)
          "proc_ty_args proc_ast = 0" 
          (*"const_decls = prog_consts prog"*)
  shows "Ast.proc_is_correct B fun_decls constants global_vars axioms proc_ast"
proof -
  show "proc_is_correct B fun_decls constants global_vars axioms proc_ast"
  proof( (simp only: proc_is_correct.simps), subst ABody, simp split: option.split, (rule allI | rule impI)+,
         unfold proc_body_satisfies_spec_def,(rule allI | rule impI)+)  
    fix \<Gamma> \<Omega> gs ls end_bb end_cont end_state
    assume Atyp:"(\<forall>t. closed t \<longrightarrow> (\<exists>v. type_of_val B v = t)) \<and> (\<forall>v. closed (type_of_val B v))" and
           FunWf:"fun_interp_wf B fun_decls \<Gamma>" and
           ARenv: "list_all closed \<Omega> \<and> length \<Omega> = proc_ty_args proc_ast" and
           WfGlobal: "state_typ_wf B \<Omega> gs (constants @ global_vars)" and
           WfLocal: "state_typ_wf B \<Omega> ls (proc_args proc_ast @ locals @ proc_rets proc_ast)" and
           AxSat: "axioms_sat B (constants, []) \<Gamma>
        \<lparr>old_global_state = Map.empty, global_state = state_restriction gs constants, local_state = Map.empty, binder_state = Map.empty\<rparr>
        axioms" and
        APres:  "expr_all_sat B (constants @ global_vars, proc_args proc_ast @ locals @ proc_rets proc_ast) \<Gamma> \<Omega>
        \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> (map fst (proc_pres proc_ast))" and
        Ared: "rtranclp 
               (red_bigblock 
                B [] (constants @ global_vars,
                proc_args proc_ast @
                locals @
                proc_rets
                 proc_ast) \<Gamma> \<Omega> ast) (init_ast ast \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr>)
       (end_bb, end_cont, end_state)"
    have Contexteq:"\<Lambda> = (constants @ global_vars, proc_args proc_ast @ locals @ proc_rets proc_ast)"
      using AVarContext ARets by simp
    from ARenv \<open>proc_ty_args proc_ast = 0\<close> have "\<Omega> = []" by simp
    have "Ast.valid_configuration B \<Lambda> \<Gamma> [] checked_posts end_bb end_cont end_state"
      apply (rule AExpanded)
                apply (subst Contexteq)
      using Ared \<open>\<Omega> = []\<close>
                apply fastforce
              apply (simp add: Atyp)
             apply (simp add: Atyp)
            apply (simp add: FunWf)
      unfolding nstate_global_restriction_def 
      using AxSat
           apply simp
      using APres \<open>\<Omega> = []\<close> \<open>all_pres = _\<close> Contexteq
          apply simp
      using Contexteq WfLocal \<open>\<Omega> = []\<close>
         apply simp
      using Contexteq WfGlobal \<open>\<Omega> = []\<close>      
        apply simp
       apply simp
      apply simp
      done
    thus "Ast.valid_configuration B (constants @ global_vars, proc_args proc_ast @ locals @ proc_rets proc_ast) \<Gamma> \<Omega>
        (map fst (filter (\<lambda>x. \<not> snd x) (proc_posts proc_ast))) end_bb end_cont end_state"
      using Contexteq \<open>\<Omega> = []\<close> \<open>checked_posts = _\<close>
      by simp
  qed
qed

lemma valid_config_implies_not_failure:
  assumes "Semantics.valid_configuration A \<Lambda> \<Gamma> \<Omega> posts m' s'"
  shows "s' \<noteq> Failure"
  using Semantics.valid_configuration_def assms by blast

end