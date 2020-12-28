theory BackedgeElim
imports Semantics Util
begin

fun mods_contained_in :: "vname set \<Rightarrow> cmd list \<Rightarrow> bool"
  where
    "mods_contained_in H [] = True"
  | "mods_contained_in H ((Havoc h)#cs) = ((h \<notin> H) \<and> mods_contained_in H cs)"
  | "mods_contained_in H ((Assign x e)#cs) = ((x \<notin> H) \<and> mods_contained_in H cs)"
  | "mods_contained_in H (c#cs) = mods_contained_in H cs"

definition nstate_same_on :: "var_context \<Rightarrow> 'a nstate \<Rightarrow> 'a nstate \<Rightarrow> vname set \<Rightarrow> bool"
  where "nstate_same_on \<Lambda> ns1 ns2 D = ((\<forall>d. d \<notin> D \<longrightarrow> lookup_var \<Lambda> ns1 d = lookup_var \<Lambda> ns2 d) \<and> 
                                            binder_state ns1 = binder_state ns2 \<and>
                                            old_global_state ns1 = old_global_state ns2)"

lemma nstate_same_on_empty: "nstate_same_on \<Lambda> ns1 ns1 {}"
  unfolding nstate_same_on_def
  by simp

(*shows "((A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, s\<rangle> \<Down> v) \<Longrightarrow> ((A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, s\<rangle> \<Down> v') \<Longrightarrow> v = v'))"  
    and "(A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es, s\<rangle> [\<Down>] vs) \<Longrightarrow> (A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es, s\<rangle> [\<Down>] vs') \<Longrightarrow> vs = vs' "
*)

lemma nstate_same_on_update_global:
  assumes "nstate_same_on \<Lambda> ns1 ns2 D"
  shows "nstate_same_on \<Lambda> (ns1\<lparr>global_state := gs\<rparr>) (ns2 \<lparr>global_state := gs\<rparr>) D"  
  unfolding nstate_same_on_def
proof (intro conjI, rule allI, rule impI)
  fix d
  assume "d \<notin> D"
  show "lookup_var \<Lambda> (ns1\<lparr>global_state := gs\<rparr>) d = lookup_var \<Lambda> (ns2\<lparr>global_state := gs\<rparr>) d"
  proof (cases "map_of (snd \<Lambda>) d \<noteq> None")
    case True
    have "lookup_var \<Lambda> ns2 d = lookup_var \<Lambda> ns1 d"
      by (metis (full_types) \<open>d \<notin> D\<close> assms nstate_same_on_def)
    then show ?thesis
      by (metis (no_types) True lookup_var_def nstate.select_convs(3) nstate.surjective nstate.update_convs(2) option.exhaust option.simps(5))
  next
    case False
    then show ?thesis 
      by (simp add: lookup_var_def)
  qed
next
  show "binder_state (ns1\<lparr>global_state := gs\<rparr>) = binder_state (ns2\<lparr>global_state := gs\<rparr>)"
    using assms
    by (simp add: nstate_same_on_def)
next
  show "old_global_state (ns1\<lparr>global_state := gs\<rparr>) = old_global_state (ns2\<lparr>global_state := gs\<rparr>)"
    using assms
    by (simp add: nstate_same_on_def)
qed

lemma nstate_same_on_full_ext_env:
  assumes "nstate_same_on \<Lambda> ns1 ns2 D"
  shows "nstate_same_on \<Lambda> (full_ext_env ns1 v) (full_ext_env ns2 v) D"
  using assms
  unfolding nstate_same_on_def
  by (simp add: lookup_var_binder_upd)

lemma nstate_same_on_update:
  assumes "nstate_same_on \<Lambda> ns1 ns2 (set (h#H))" and "lookup_var \<Lambda> ns1 h = Some v"
  shows "nstate_same_on \<Lambda> ns1 (update_var \<Lambda> ns2 h v) (set H)"
  using assms
  unfolding nstate_same_on_def
  by (simp add: update_var_binder_same update_var_old_global_same)

lemma nstate_same_on_update_2:
  assumes "nstate_same_on \<Lambda> ns1 ns2 D"
  shows "nstate_same_on \<Lambda> (update_var \<Lambda> ns1 h v) (update_var \<Lambda> ns2 h v) D"
  using assms
  unfolding nstate_same_on_def
  by (simp add: update_var_binder_same update_var_old_global_same)

lemma eval_nstate_same_on:
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns1\<rangle> \<Down> v \<Longrightarrow> nstate_same_on \<Lambda> ns1 ns2 {} \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns2\<rangle> \<Down> v" and 
        "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es, ns1\<rangle> [\<Down>] vs \<Longrightarrow> nstate_same_on \<Lambda> ns1 ns2 {} \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>es, ns2\<rangle> [\<Down>] vs"
proof (induction arbitrary: ns2 and ns2 rule: red_expr_red_exprs.inducts)
  case (RedOld \<Omega> e ns1 v ns2)
  hence "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns2\<lparr>global_state := old_global_state ns1\<rparr>\<rangle> \<Down> v" using nstate_same_on_update_global
    by blast
  thus ?case 
    using RedOld nstate_same_on_def
    by (metis red_expr_red_exprs.RedOld)
next
  case (RedForAllTrue \<Omega> ty e ns1 ns2) 
  thus ?case using nstate_same_on_full_ext_env
    by (metis red_expr_red_exprs.RedForAllTrue)
next
  case (RedForAllFalse \<Omega> ty e ns1 ns2)
   thus ?case using nstate_same_on_full_ext_env
     by (metis red_expr_red_exprs.RedForAllFalse) 
next
 case (RedExistsTrue \<Omega> ty e ns1 ns2)
 thus ?case using nstate_same_on_full_ext_env
   by (metis red_expr_red_exprs.RedExistsTrue) 
next
 case (RedExistsFalse \<Omega> ty e ns1 ns2)
 thus ?case using nstate_same_on_full_ext_env
   by (metis red_expr_red_exprs.RedExistsFalse) 
qed (auto simp: nstate_same_on_def intro: red_expr_red_exprs.intros)

definition state_well_typed :: "'a absval_ty_fun \<Rightarrow> var_context \<Rightarrow> rtype_env \<Rightarrow> 'a nstate \<Rightarrow> bool"
  where "state_well_typed A \<Lambda> \<Omega> ns = 
         (\<forall>x \<tau>. lookup_var_ty \<Lambda> x = Some \<tau> \<longrightarrow>
             (\<exists>v. lookup_var \<Lambda> ns x = Some v \<and> type_of_val A v = instantiate \<Omega> \<tau>))"

fun is_method_call :: "cmd \<Rightarrow> bool"
  where
    "is_method_call (MethodCall m args rets) = True"
  | "is_method_call _ = False"

(* TODO: nat argument may be redundant *)
inductive cfg_dag_rel :: "bool \<Rightarrow> vname list \<Rightarrow> expr list \<Rightarrow> expr list \<Rightarrow> cmd list \<Rightarrow> cmd list \<Rightarrow> bool"
  for "cut_edge" :: bool
  where      
     DagRel_Havoc:
     "\<lbrakk>cfg_dag_rel cut_edge H pre_invs post_invs cs1 cs2\<rbrakk> \<Longrightarrow>
     cfg_dag_rel cut_edge (h#H) pre_invs post_invs cs1 (Havoc h # cs2)"
   | DagRel_PreInv:
     "\<lbrakk>cfg_dag_rel cut_edge [] pre_invs post_invs cs1 cs2\<rbrakk> \<Longrightarrow>
     cfg_dag_rel cut_edge [] (e_inv#pre_invs) post_invs (Assert e_inv # cs1) (Assume e_inv # cs2)"
   | DagRel_PreInv_Assume:
     "\<lbrakk>cfg_dag_rel cut_edge [] (e_inv#pre_invs) post_invs cs1 cs2\<rbrakk> \<Longrightarrow>
     cfg_dag_rel cut_edge [] (e_inv#pre_invs) post_invs (Assume e # cs1) (Assume e # cs2)"
(* method call are already desugared in this phase *)
   | DagRel_Main:
     "\<lbrakk>\<not> is_method_call c; cfg_dag_rel cut_edge [] [] post_invs cs1 cs2\<rbrakk> \<Longrightarrow>
     cfg_dag_rel cut_edge [] [] post_invs (c # cs1) (c # cs2)"
   | DagRel_PostInv:
     "\<lbrakk>cfg_dag_rel cut_edge [] [] post_invs [] cs2\<rbrakk> \<Longrightarrow>
     cfg_dag_rel cut_edge [] [] (e_inv # post_invs) [] (Assert e_inv # cs2)"
   | DagRel_Nil:
     "cfg_dag_rel cut_edge [] [] [] [] []"
   | DagRel_CutEdge:
     "cut_edge \<Longrightarrow> cfg_dag_rel cut_edge [] [] [] [] [Assume (Lit (LBool False))]"

(* TODO: also need that ns1 is well-typed *)
lemma cfg_dag_rel_havoc:
  assumes "cfg_dag_rel c H pre_invs post_invs cs1 cs2" and
          "nstate_same_on \<Lambda> ns1 ns2 (set H)" and
          StateWt:"state_well_typed A \<Lambda> \<Omega> ns1" and
          TyExists:"list_all (\<lambda>x. lookup_var_ty \<Lambda> x \<noteq> None) H"
        shows "(\<exists>cs2A cs2B ns1'. cs2 = cs2A@cs2B \<and> nstate_same_on \<Lambda> ns1 ns1' {} \<and> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A, Normal ns2\<rangle> [\<rightarrow>] Normal ns1') \<and> cfg_dag_rel c [] pre_invs post_invs cs1 cs2B)"
  using assms
proof (induction arbitrary: ns2)
  case (DagRel_Havoc H pre_invs post_invs cs1 cs2 h)  
  hence TyH:"list_all (\<lambda>x. lookup_var_ty \<Lambda> x \<noteq> None) H" by simp
  from \<open>list_all (\<lambda>x. lookup_var_ty \<Lambda> x \<noteq> None) (h # H)\<close> obtain \<tau> where "lookup_var_ty \<Lambda> h = Some \<tau>" by auto
  from this obtain v where "lookup_var \<Lambda> ns1 h = Some v" and TyV: "type_of_val A v = instantiate \<Omega> \<tau>"
    using StateWt state_well_typed_def by blast  
  let ?ns2 = "update_var \<Lambda> ns2 h v"
  have HavocRed:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Havoc h, Normal ns2\<rangle> \<rightarrow> Normal ?ns2"
    by (simp add: RedHavoc \<open>lookup_var_ty \<Lambda> h = Some \<tau>\<close> TyV)   
  have "nstate_same_on \<Lambda> ns1 ?ns2 (set H)"
    using nstate_same_on_update[OF \<open>nstate_same_on \<Lambda> ns1 ns2 (set (h # H))\<close> \<open>lookup_var \<Lambda> ns1 h = Some v\<close>]
    by simp
  from this TyH StateWt DagRel_Havoc.IH obtain cs2A cs2B ns1' where
    "cs2 = cs2A @ cs2B" and
    FinalStateSame:"nstate_same_on \<Lambda> ns1 ns1' {}" and
    RedRest:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A,Normal ?ns2\<rangle> [\<rightarrow>] Normal ns1'" and 
    RelRest:"cfg_dag_rel c [] pre_invs post_invs cs1 cs2B"
    by blast
  show ?case
    apply (rule exI[where ?x="[Havoc h]@cs2A"], rule exI[where ?x=cs2B], rule exI[where ?x=ns1'])
    apply (intro conjI)
    using \<open>cs2 = cs2A @ cs2B\<close> apply simp
    apply (rule FinalStateSame)
    using HavocRed RedRest 
    using RedCmdListCons apply fastforce
    using RelRest by simp
qed (auto intro: RedCmdListNil cfg_dag_rel.intros)

lemma assume_red_true:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e, Normal ns\<rangle> \<rightarrow> s2" and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns\<rangle> \<Down> BoolV True"
  shows "s2 = Normal ns"
  using assms
  apply cases
  by (auto dest: expr_eval_determ(1))

lemma assume_red_false:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e, Normal ns\<rangle> \<rightarrow> s2" and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns\<rangle> \<Down> BoolV False"
  shows "s2 = Magic"
  using assms
  apply cases
  by (auto dest: expr_eval_determ(1))

lemma assume_determ:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e, s1\<rangle> \<rightarrow> s2" and "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e, s1\<rangle> \<rightarrow> s3"
  shows "s2 = s3"
  using assms
proof (cases s1)
  case (Normal ns)
  then show ?thesis 
  proof (cases "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns\<rangle> \<Down> BoolV True")
    case True
    then show ?thesis using assms Normal 
      using assume_red_true by blast
  next
    case False
    then show ?thesis using assms Normal 
      by (metis assume_cases_ext)
  qed
qed (auto dest: failure_stays_cmd magic_stays_cmd)


lemma cfg_dag_rel_pre_invs:
  assumes "cfg_dag_rel c H pre_invs post_invs cs1 cs2" and
          "H = []" and
          "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] s'" and
          "nstate_same_on \<Lambda> ns1 ns2 {}" and
          "list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns1) pre_invs"
  shows "(\<exists> cs1A cs1B cs2A cs2B s''. cs1 = cs1A@cs1B \<and> cs2 = cs2A@cs2B \<and>  
   (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1A, Normal ns1\<rangle> [\<rightarrow>] s'') \<and> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1B, s''\<rangle> [\<rightarrow>] s') \<and> 
    s'' \<noteq> Failure \<and>
   (s'' \<noteq> Magic \<longrightarrow> s'' = Normal ns1 \<and> cfg_dag_rel c [] [] post_invs cs1B cs2B \<and>
                    (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A, Normal ns2\<rangle> [\<rightarrow>] Normal ns2)))"
  using assms
proof (induction)
  case (DagRel_PreInv pre_invs post_invs cs1 cs2 e_inv)
  hence InvHolds:"A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e_inv, ns1\<rangle> \<Down> BoolV True" using expr_sat_def
    by (simp add: expr_sat_def RedAssertOk)
  with \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assert e_inv # cs1,Normal ns1\<rangle> [\<rightarrow>] s'\<close>
  have RedAssertInv:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assert e_inv, Normal ns1\<rangle> \<rightarrow> Normal ns1" and 
       RedCs1:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] s'"
    by (auto elim: assert_ml intro:  RedAssertOk)  
  with DagRel_PreInv obtain cs1A cs1B cs2A cs2B s'' where
    "cs1 = cs1A @ cs1B" and "cs2 = cs2A @ cs2B" and
    RedCs1A:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1A,Normal ns1\<rangle> [\<rightarrow>] s''" and RedCs1B:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1B, s''\<rangle> [\<rightarrow>] s'"    
    "s'' \<noteq> Failure" and NotMagic:"(s'' \<noteq> Magic \<longrightarrow> s'' = Normal ns1 \<and> cfg_dag_rel c [] [] post_invs cs1B cs2B \<and> 
                                       (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A,Normal ns2\<rangle> [\<rightarrow>] Normal ns2))"
    by fastforce        
  show ?case
  proof (cases "s'' = Magic")
    case True
    show ?thesis 
    apply (rule exI[where ?x="Assert e_inv # cs1A"])
    apply (rule exI[where ?x="cs1B"])
    apply (rule exI[where ?x="Assume e_inv # cs2A"])
      apply (rule exI[where ?x=cs2B])
      apply (rule exI[where ?x= Magic])
      apply (intro conjI)
      using \<open>cs1 = cs1A @ cs1B\<close> apply simp
      using \<open>cs2 = cs2A @ cs2B\<close> apply simp          
      using RedAssertInv RedCs1A RedCmdListCons True apply blast
      using RedCs1B True by auto
  next
    case False
    hence "s'' = Normal ns1" and RedCs2A:"(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A, Normal ns2\<rangle> [\<rightarrow>] Normal ns2)" and
          RelRest:"cfg_dag_rel c [] [] post_invs cs1B cs2B"
      using NotMagic by auto
    show ?thesis
    apply (rule exI[where ?x="Assert e_inv # cs1A"])
    apply (rule exI[where ?x="cs1B"])
    apply (rule exI[where ?x="Assume e_inv # cs2A"])
      apply (rule exI[where ?x=cs2B])
      apply (rule exI[where ?x="Normal ns1"])
      apply (intro conjI)
      using \<open>cs1 = cs1A @ cs1B\<close> apply simp
      using \<open>cs2 = cs2A @ cs2B\<close> apply simp
      using RedAssertInv RedCmdListCons RedCs1A \<open>s'' = Normal ns1\<close> apply blast
      using RedCs1B \<open>s'' = Normal ns1\<close> apply auto[1]
       apply simp
      using InvHolds RedCs2A RedCmdListCons RedAssumeOk RelRest
      by (metis assms(4) eval_nstate_same_on(1))
  qed
next
  case (DagRel_PreInv_Assume e_inv pre_invs post_invs cs1 cs2 e)
  then show ?case
  proof (cases "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns1\<rangle> \<Down> BoolV True")
    case True
    hence RedAssumeE:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e, Normal ns1\<rangle> \<rightarrow> Normal ns1"
      by (auto intro: red_cmd.intros)
    hence "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] s'"
      using \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e # cs1,Normal ns1\<rangle> [\<rightarrow>] s'\<close>
      by (metis RedCmdListCons_case assume_determ)
    with DagRel_PreInv_Assume obtain cs1A cs1B cs2A cs2B s'' where
        A: "cs1 = cs1A @ cs1B"  "cs2 = cs2A @ cs2B"
       "(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1A,Normal ns1\<rangle> [\<rightarrow>] s'')" 
       "(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1B,s''\<rangle> [\<rightarrow>] s')" 
       "s'' \<noteq> Failure" 
      "(s'' \<noteq> Magic \<longrightarrow> s'' = Normal ns1 \<and> cfg_dag_rel c [] [] post_invs cs1B cs2B \<and> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A,Normal ns2\<rangle> [\<rightarrow>] Normal ns2)"
      by fastforce
    have RedAssumeE2:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e, Normal ns2\<rangle> \<rightarrow> Normal ns2" using True \<open>nstate_same_on \<Lambda> ns1 ns2 {}\<close>
      using RedAssumeOk eval_nstate_same_on(1) by blast
    show ?thesis 
      apply (rule exI[where ?x="(Assume e)#cs1A"])
      apply (rule exI[where ?x=cs1B])
      apply (rule exI[where ?x="(Assume e)#cs2A"])
      apply (rule exI[where ?x=cs2B])
      apply (rule exI[where ?x=s''])
      apply (intro conjI)
      using A RedAssumeE RedAssumeE2
      by (auto intro: red_cmd.intros RedCmdListCons)      
  next
    case False
    hence InvFalse:"A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e,ns1\<rangle> \<Down> BoolV False" using \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e # cs1,Normal ns1\<rangle> [\<rightarrow>] s'\<close>
      by (metis (full_types) RedCmdListCons_case assume_red_bool)     
    show ?thesis
      apply (rule exI[where ?x="[Assume e]"])
      apply (rule exI[where ?x=cs1])
      apply (rule exI[where ?x="[Assume e]"])
      apply (rule exI[where ?x=cs2])
      apply (rule exI[where ?x=Magic])
      apply (intro conjI)
      using InvFalse 
            apply simp
          apply simp
      using InvFalse 
         apply (meson RedAssumeMagic RedCmdListCons RedCmdListNil)
        apply (metis \<open>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Assume e # cs1,Normal ns1\<rangle> [\<rightarrow>] s'\<close> False assume_ml magic_red_cmd_list)
      by auto
  qed
next
  case (DagRel_Main post_invs cs1 cs2 c)
  show ?case
    apply (rule exI[where ?x="[]"])
    using DagRel_Main
         by (auto intro: RedCmdListNil cfg_dag_rel.DagRel_Main)
     qed (auto intro: RedCmdListNil cfg_dag_rel.intros simp: nstate_same_on_def)

lemma red_cmd_nstate_same_on:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, Normal ns1\<rangle> \<rightarrow> s'" and
          "nstate_same_on \<Lambda> ns1 ns2 {}" and
          "\<not> (is_method_call c)"
  shows "(((s' = Failure) \<or> (s' = Magic)) \<longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, Normal ns2\<rangle> \<rightarrow> s') \<and>
         (\<forall>ns1'. s' = Normal ns1' \<longrightarrow> (\<exists>ns2'. nstate_same_on \<Lambda> ns1' ns2' {} \<and> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>c, Normal ns2\<rangle> \<rightarrow> Normal ns2'))"
  using assms
proof cases
  case (RedAssertOk e)
   then show ?thesis 
  using assms(2) eval_nstate_same_on(1) red_cmd.RedAssertOk by blast
next
  case (RedAssertFail e)
  then show ?thesis 
  using assms(2) eval_nstate_same_on(1) red_cmd.RedAssertFail by blast
next
  case (RedAssumeOk e)
  then show ?thesis 
    using assms(2) eval_nstate_same_on(1) red_cmd.RedAssumeOk by blast
next
  case (RedAssumeMagic e)
  then show ?thesis 
    using assms(2) eval_nstate_same_on(1) red_cmd.RedAssumeMagic by blast
next
  case (RedAssign x ty v e)
  then show ?thesis using nstate_same_on_update_2
  by (metis assms(2) eval_nstate_same_on(1) red_cmd.RedAssign state.distinct(1) state.distinct(3) state.inject)
next
  case (RedHavoc x ty v)
  then show ?thesis using nstate_same_on_update_2[OF assms(2)]
    using red_cmd.RedHavoc by blast
qed (simp)


lemma cfg_dag_rel_same:
  assumes "cfg_dag_rel c H pre_invs post_invs cs1 cs2" and
          "H = []" and
          "pre_invs = []" and
          "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] s'" and
          "nstate_same_on \<Lambda> ns1 ns2 {}" and
          "\<And> s2'. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns2\<rangle> [\<rightarrow>] s2' \<Longrightarrow> s2' \<noteq> Failure"
  shows "\<exists>cs2A cs2B. cs2 = cs2A@cs2B \<and>   
    s' \<noteq> Failure \<and> 
    (\<forall>ns'. s' = Normal ns1' \<longrightarrow> (\<exists>ns2'. nstate_same_on \<Lambda> ns1' ns2' {} \<and> cfg_dag_rel c [] [] post_invs [] cs2B \<and> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A, Normal ns2\<rangle> [\<rightarrow>] Normal ns2')))"
  using assms
proof (induction arbitrary: ns1 ns2)
  case (DagRel_Main cmd post_invs cs1 cs2)
  from this obtain s'' where
    RedC1:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cmd, Normal ns1\<rangle> \<rightarrow> s''" and RedCs1: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, s''\<rangle> [\<rightarrow>] s'"
    by auto
  show ?case 
  proof (cases s'')
    case (Normal ns1'')
    from this obtain ns2'' where RedCmd2:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cmd, Normal ns2\<rangle> \<rightarrow> Normal ns2''" and "nstate_same_on \<Lambda> ns1'' ns2'' {}"
      using DagRel_Main.hyps(1) \<open> nstate_same_on \<Lambda> ns1 ns2 {}\<close> RedC1 red_cmd_nstate_same_on by blast
    hence "(\<And>s2'. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2,Normal ns2''\<rangle> [\<rightarrow>] s2' \<Longrightarrow> s2' \<noteq> Failure)"
      using DagRel_Main.prems(5) RedCmdListCons by blast
    with DagRel_Main.IH RedCs1 Normal \<open>nstate_same_on \<Lambda> ns1'' ns2'' {}\<close> obtain cs2A cs2B where 
     Rec:"cs2 = cs2A @ cs2B" "s' \<noteq> Failure" 
         "\<forall>ns'. s' = Normal ns1' \<longrightarrow> (\<exists>ns2'. nstate_same_on \<Lambda> ns1' ns2' {} \<and> cfg_dag_rel c [] [] post_invs [] cs2B \<and> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A,Normal ns2''\<rangle> [\<rightarrow>] Normal ns2')"
      by metis    
    show ?thesis 
      apply (rule exI[where ?x = "(cmd)#cs2A"])
      apply (rule exI[where ?x = "cs2B"])
      using Rec RedCmd2 
      by (auto intro: RedCmdListCons)      
  next
    case Failure
    then show ?thesis 
      by (metis DagRel_Main.hyps(1) DagRel_Main.prems(4) DagRel_Main.prems(5) RedC1 failure_red_cmd_list red_cmd_list.simps red_cmd_nstate_same_on)
  next
    case Magic
    hence "s' = Magic" using RedCs1
      by (simp add: magic_stays_cmd_list)
    thus ?thesis 
      by auto     
  qed
next
 case (DagRel_PostInv post_invs cs2 e_inv)
  then show ?case 
    by (metis (full_types) RedCmdListNil append.left_neutral cfg_dag_rel.DagRel_PostInv nil_cmd_elim state.distinct(1) state.inject)
next
  case  DagRel_CutEdge
  then show ?case     
    by (metis RedCmdListNil append.left_neutral cfg_dag_rel.DagRel_CutEdge nil_cmd_elim state.distinct(1) state.inject)
qed (auto intro: RedCmdListNil cfg_dag_rel.intros)


lemma cfg_dag_rel_post_invs:
  assumes "cfg_dag_rel c [] [] post_invs [] cs2" and
          "\<And> s2'. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns\<rangle> [\<rightarrow>] s2' \<Longrightarrow> s2' \<noteq> Failure"
  shows "\<exists> cs2A cs2B.  cs2 = cs2A@cs2B \<and> 
    cfg_dag_rel c [] [] [] [] cs2B \<and> 
    (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A, Normal ns\<rangle> [\<rightarrow>] Normal ns) \<and>
    list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns) post_invs"
  using assms
proof induction


lemma dag_rel_block_lemma:
  assumes Red:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] s'" and
          InvsHold:"list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns1) pre_invs" and
          DagVerifies:"\<And>s2'. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns2\<rangle> [\<rightarrow>] s2' \<Longrightarrow> s2' \<noteq> Failure" and
          SameModH:"nstate_same_on \<Lambda> ns1 ns2 (set H)" and
          Rel:"cfg_dag_rel c H pre_invs post_invs cs1 cs2"
  shows "s' \<noteq> Failure \<and> (\<forall>ns'. s' = Normal ns' \<longrightarrow> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns') post_invs \<and> (\<not>c \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns2\<rangle> [\<rightarrow>] Normal ns')))"
proof -
  from cfg_dag_rel_havoc[OF Rel SameModH] obtain cs2A cs2B where
    "cs2 = cs2A@cs2B" and A2Red1:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A, Normal ns2\<rangle> [\<rightarrow>] Normal ns1" and RelHavoc:"cfg_dag_rel c [] pre_invs post_invs cs1 cs2B"
    by meson

  from cfg_dag_rel_pre_invs[OF RelHavoc Red InvsHold] obtain cs1A cs1B cs2A' cs2B' where
    "cs1 = cs1A@cs1B" and "cs2B = cs2A'@cs2B'" and RelPreInvs:"cfg_dag_rel c [] [] post_invs cs1B cs2B'" and
    A1Red1:"(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1A, Normal ns1\<rangle> [\<rightarrow>] Normal ns1)" and A1Red2:"(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1B, Normal ns1\<rangle> [\<rightarrow>] s')" and 
    A2Red2:"(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A', Normal ns1\<rangle> [\<rightarrow>] Normal ns1)" 
    by metis

  from A2Red1 A2Red2 have A2Red3:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A@cs2A',Normal ns2\<rangle> [\<rightarrow>] Normal ns1"
    using red_cmd_list_append by blast

  have "cs2 = (cs2A@cs2A')@cs2B'" using \<open>cs2 = cs2A@cs2B\<close> and \<open>cs2B = cs2A'@cs2B'\<close> by simp
  with A2Red3 have DagVerifies2:"\<And>s2'. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2B', Normal ns1\<rangle> [\<rightarrow>] s2' \<Longrightarrow> s2' \<noteq> Failure"
    using DagVerifies red_cmd_list_append
    by blast

  from cfg_dag_rel_same[OF RelPreInvs A1Red2 DagVerifies2] obtain cs2A'' cs2B''
    where "cs2B' = cs2A'' @ cs2B''" and RelSame:"cfg_dag_rel c [] [] post_invs [] cs2B''" and
     "s' \<noteq> Failure" and  NormalSame:"(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A'',Normal ns1\<rangle> [\<rightarrow>] s')"
    by blast

  show ?thesis
  proof (rule conjI[OF \<open>s' \<noteq> Failure\<close>], rule allI, rule impI)
    fix ns'
    assume "s' = Normal ns'"
    hence A2Red4:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A'',Normal ns1\<rangle> [\<rightarrow>] Normal ns'" using NormalSame
      by blast
    with \<open>cs2B' = cs2A'' @ cs2B''\<close>
    have DagVerifies3: "\<And>s2'. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2B'', Normal ns'\<rangle> [\<rightarrow>] s2' \<Longrightarrow> s2' \<noteq> Failure"
    using DagVerifies2  red_cmd_list_append
    by blast
      
    from cfg_dag_rel_post_invs[OF RelSame DagVerifies3] obtain cs2A''' cs2B'''
      where "cs2B'' = cs2A''' @ cs2B'''" and
      RelPostInv:"cfg_dag_rel c [] [] [] [] cs2B'''" and
      A2Red5:"(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2A''', Normal ns'\<rangle> [\<rightarrow>] Normal ns')" and
      PostInvsHold:"list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns') post_invs"
      by metis
  
    show "list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns') post_invs \<and> (\<not> c \<longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2,Normal ns2\<rangle> [\<rightarrow>] Normal ns')"
    proof (rule conjI[OF PostInvsHold], rule impI)
      assume "\<not>c"
      with RelPostInv have "cs2B''' = []"
        by (cases) auto
      with \<open>cs2 = (cs2A@cs2A')@cs2B'\<close> \<open>cs2B' = cs2A'' @ cs2B''\<close> \<open>cs2B'' = cs2A''' @ cs2B'''\<close>  A2Red3 A2Red4 A2Red5
      show "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2,Normal ns2\<rangle> [\<rightarrow>] Normal ns'"  
        using red_cmd_list_append
        by (metis append_Nil2)
    qed
  qed
qed

definition dag_lemma_assms :: "'a absval_ty_fun \<Rightarrow> method_context \<Rightarrow> var_context \<Rightarrow> 
                   'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> vname list \<Rightarrow> expr list \<Rightarrow> expr list \<Rightarrow>
                   cmd list \<Rightarrow> cmd list \<Rightarrow> 'a nstate \<Rightarrow> 'a nstate \<Rightarrow> bool \<Rightarrow> bool"
  where "dag_lemma_assms A M \<Lambda> \<Gamma> \<Omega> H pre_invs post_invs cs1 cs2 ns1 ns2 c \<equiv> 
         (list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns1) pre_invs) \<and>
         (\<forall>s2'. (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns2\<rangle> [\<rightarrow>] s2') \<longrightarrow> s2' \<noteq> Failure) \<and>
          (nstate_same_on \<Lambda> ns1 ns2 (set H))"

definition dag_lemma_conclusion :: "'a absval_ty_fun \<Rightarrow> method_context \<Rightarrow> var_context \<Rightarrow> 
                   'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> expr list \<Rightarrow>
                   cmd list \<Rightarrow> cmd list \<Rightarrow> 'a nstate \<Rightarrow> 'a nstate \<Rightarrow> 'a state \<Rightarrow> bool \<Rightarrow> bool"
  where "dag_lemma_conclusion A M \<Lambda> \<Gamma> \<Omega> post_invs cs1 cs2 ns1 ns2 s' c \<equiv>
          s' \<noteq> Failure \<and> 
         (\<forall>ns'. s' = Normal ns' \<longrightarrow> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns') post_invs \<and> 
               (\<not>c \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns2\<rangle> [\<rightarrow>] Normal ns'))
         )"

lemma dag_rel_block_lemma_compact:
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] s'" and
          "dag_lemma_assms A M \<Lambda> \<Gamma> \<Omega> H pre_invs post_invs cs1 cs2 ns1 ns2 c" and
          "cfg_dag_rel c H pre_invs post_invs cs1 cs2"
  shows "dag_lemma_conclusion A M \<Lambda> \<Gamma> \<Omega> post_invs cs1 cs2 ns1 ns2 s' c"
  using assms
  unfolding dag_lemma_assms_def dag_lemma_conclusion_def
  using dag_rel_block_lemma
  by blast

lemma cfg_dag_rel_lemma_no_havoc_no_cut:
  assumes Red:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] s'" and
          InvsHold:"list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns1) pre_invs" and
          DagVerifies:"\<And>s2'. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns1\<rangle> [\<rightarrow>] s2' \<Longrightarrow> s2' \<noteq> Failure" and
          Rel:"cfg_dag_rel False [] pre_invs post_invs cs1 cs2"
        shows "s' \<noteq> Failure \<and> 
              (\<forall>ns'. s' = Normal ns' \<longrightarrow> list_all (expr_sat A \<Lambda> \<Gamma> \<Omega> ns') post_invs \<and> 
                 (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns1\<rangle> [\<rightarrow>] Normal ns'))"
  oops

lemma cfg_dag_rel_lemma_basic:
  assumes Red:"A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] s'" and
          DagVerifies:"\<And>s2'. A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs1, Normal ns1\<rangle> [\<rightarrow>] s2' \<Longrightarrow> s2' \<noteq> Failure" 
  shows "s' \<noteq> Failure \<and> (\<forall>ns'. s' = Normal ns' \<longrightarrow> (A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs2, Normal ns1\<rangle> [\<rightarrow>] Normal ns'))"
  oops

end