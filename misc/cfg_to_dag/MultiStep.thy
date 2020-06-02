theory MultiStep
imports Main Semantics
begin

lemma relpow_E2:
  assumes "(x, z) \<in> R ^^ n" "n = 0 \<Longrightarrow> x = z \<Longrightarrow> P"
          "\<And>y m. n = Suc m \<Longrightarrow> (x, y) \<in> R \<Longrightarrow> (y, z) \<in> R ^^ m \<Longrightarrow> P"
        shows "P"
  oops


thm converse_rtranclp_induct
          
theorem rtranclp_induct_test [consumes 1, case_names refl step, induct set: rtranclp]:
  assumes a: "r\<^sup>*\<^sup>* a b"
    and cases: "P a b" "\<And>y z. r\<^sup>*\<^sup>* a y \<Longrightarrow> r y z \<Longrightarrow> P y b \<Longrightarrow> P z b"
  shows "P b b"
  using assms
  by (rule rtranclp_induct)

thm converse_rtranclp_induct

theorem converse_rtranclp_induct_test [consumes 1, case_names refl step, induct set: rtranclp]:
  assumes a: "r\<^sup>*\<^sup>* a b"
    and cases: "P b b" "\<And>y z. r y z \<Longrightarrow> r\<^sup>*\<^sup>* z b \<Longrightarrow>  P z b \<Longrightarrow> P y b"
  shows "P a b"
  using assms
  by (rule converse_rtranclp_induct)

lemmas converse_rtranclp_induct_test_2 =
  converse_rtranclp_induct_test[of _ "(ax,ay)" "(bx,by)", split_rule, consumes 1, case_names refl step]

lemma relpow_split:
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "(R^^(Suc n)) x y"
  shows "\<exists>z. R x z \<and> ((R^^n) z y)" 
  oops

lemmas relpowp_E2_2 =
  relpowp_E2[of _ _ "(n', s')" "(n'',s'')", split_rule]

lemma cfg_ind_strong: 
  shows "\<And> ns' ns''. \<lbrakk>(\<Lambda>, \<Gamma>, G \<turnstile> (Inl h, Normal ns') -n\<rightarrow>^k (m', s'));
                       ns' ''x'' = Some (IntV vc_x);
                       \<Gamma> \<turnstile> \<langle>e_inv, ns'\<rangle> \<Down> BoolV True\<rbrakk> \<Longrightarrow>
                       s' \<noteq> Failure"
proof (induction k rule: less_induct)
  case (less x ns' ns'')
  show ?case
  proof(cases x)
    case 0
    with less.prems(1) show ?thesis by auto
  next
    case (Suc k)
    with less.prems(1) obtain z where 
        "(\<Lambda>, \<Gamma>, G \<turnstile> (Inl h, Normal ns') -n\<rightarrow> z)" and "(\<Lambda>, \<Gamma>, G \<turnstile> z -n\<rightarrow>^k (m', s'))"
      by (meson relpowp_Suc_E2)
    from \<open>x = Suc k\<close> and less.IH have
        "\<And>k' ns2. k' \<le> k \<Longrightarrow>
    \<Lambda>,\<Gamma>,G \<turnstile>(Inl h, Normal ns2) -n\<rightarrow>^k' (m', s') \<Longrightarrow>
    ns2 ''x'' = Some (IntV vc_x) \<Longrightarrow> \<Gamma> \<turnstile> \<langle>e_inv,ns2\<rangle> \<Down> BoolV True \<Longrightarrow> s' \<noteq> Failure"
      using le_imp_less_Suc by blast      
    then show ?thesis sorry
  qed

  

  then show ?case sorry
qed


theorem converse_rtranclp_induct_strong [consumes 1, case_names refl step, induct set: rtranclp]:
  assumes a: "r\<^sup>*\<^sup>* a b"
    and cases: "P b b" "\<And>y z. r y z \<Longrightarrow> r\<^sup>*\<^sup>* z b \<Longrightarrow>  (\<forall>z'. r\<^sup>*\<^sup>* z z' \<longrightarrow> P z' b) \<Longrightarrow> P y b"
  shows "P a b"
proof-
  let ?Q = "\<lambda> z b. \<forall>z'. r\<^sup>*\<^sup>* z z' \<longrightarrow> P z' b"
  have "\<forall>z'. r\<^sup>*\<^sup>* a z' \<longrightarrow> P z' b" using a
  proof (rule converse_rtranclp_induct_test[where ?P = "\<lambda> z b. \<forall>z'. r\<^sup>*\<^sup>* z z' \<longrightarrow> P z' b"])
    show "\<forall>z'. r\<^sup>*\<^sup>* b z' \<longrightarrow> P z' b"
      sorry
  next
    fix y z
    assume "r y z"
    moreover assume "r\<^sup>*\<^sup>* z b"
    moreover assume "\<forall>z'. r\<^sup>*\<^sup>* z z' \<longrightarrow> P z' b"
    ultimately have "P y b" using cases (2) by simp
    show "\<forall>z'. r\<^sup>*\<^sup>* y z' \<longrightarrow> P z' b"
    proof (rule, rule)
      fix z'
      assume "r\<^sup>*\<^sup>* y z'"
      hence "P z' b"

lemmas converse_rtranclp_induct_strong_2 =
  converse_rtranclp_induct_strong[of _ "(ax,ay)" "(bx,by)", split_rule, consumes 1, case_names refl step]

lemma cfg_ind_strong: 
  assumes A1:"\<Lambda>, \<Gamma>, G \<turnstile> (m, s) -n\<rightarrow>* (m', s')" and "vc"
  shows "\<And> ns' ns''. \<lbrakk>(\<Lambda>, \<Gamma>, G \<turnstile> (m, s) -n\<rightarrow>* (m', s'));
                       s = Normal ns'; m = Inl h;
                       ns' ''x'' = Some (IntV vc_x);
                       \<Gamma> \<turnstile> \<langle>e_inv, ns'\<rangle> \<Down> BoolV True\<rbrakk> \<Longrightarrow>
                       s' \<noteq> Failure"
  using A1
proof (induction rule: converse_rtranclp_induct_strong_2)
case refl
then show ?case by simp
next
  case (step m s m' s')
  then show ?case sorry
qed


lemma cfg_ind: 
  fixes m' s'
  assumes A1:"\<Lambda>, \<Gamma>, G \<turnstile> (m, s) -n\<rightarrow>* (m', s')" and "vc" and "m = Inl h"
  shows "\<And> ns' ns''. \<lbrakk>(\<Lambda>, \<Gamma>, G \<turnstile> (m, s) -n\<rightarrow>* (Inl h, Normal ns'')); (m, s) = (m, Normal ns');
                       ns' ''x'' = Some (IntV vc_x);
                       \<Gamma> \<turnstile> \<langle>e_inv, ns'\<rangle> \<Down> BoolV True; 
                           (\<Lambda>, \<Gamma>, G \<turnstile> (Inl h, Normal ns'') -n\<rightarrow>* (m',s'))\<rbrakk> \<Longrightarrow>
                       s' \<noteq> Failure"
  using A1
proof (induction rule: converse_rtranclp_induct_test_2)
  case refl
  then show ?case by simp
next
  case (step a b a' b')
  then show ?case sorry
qed


lemma test_block_lemma:
  assumes "\<Gamma>, \<Lambda>, G \<turnstile> (m, s) -n\<rightarrow>* (m',s')"
  shows "\<forall> m'' s''. (((\<Gamma>, \<Lambda>, G \<turnstile> (m, s) -n\<rightarrow>* (m'', s'')) \<and> \<Gamma>, \<Lambda>, G \<turnstile> (m'', s'') -n\<rightarrow>* (m', s')) \<longrightarrow>
                  (m', s') \<noteq> (m',Failure))"
  using assms
proof (induction)

lemma test:
  assumes "r\<^sup>*\<^sup>* x y" and
   "P x x" and "\<And> y z . r x y \<Longrightarrow> r\<^sup>*\<^sup>* y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
 shows "P x y"
 using \<open>r\<^sup>*\<^sup>* x y\<close>
proof (induction )
case base
then show ?case using assms by simp
next
  case (step y z)
  then show ?case using assms 
qed


lemma rel_relate_1: 
  assumes "r\<^sup>*\<^sup>* x y"
  shows "(x,y) \<in> rtrancl {(a,b).  r a b}"
  using assms
  by (simp add: Enum.rtranclp_rtrancl_eq)

lemma rel_relate_2:
  assumes "(x, y) \<in> rtrancl {(a,b). r a b}"
  shows "r\<^sup>*\<^sup>* x y"
  by (simp add: Enum.rtranclp_rtrancl_eq assms)
  

  thm rtranclp.induct

theorem rtranclp_induct [consumes 1, case_names base step, induct set: rtranclp]:
  assumes a: "r\<^sup>*\<^sup>* a b"
    and cases: "a = b \<Longrightarrow> P a" "\<And>y z. r\<^sup>*\<^sup>* a y \<Longrightarrow> r y z \<Longrightarrow> P y \<Longrightarrow> P z"
  shows "P b"
  using a by (induct x\<equiv>a b) (rule cases)+

lemma rtrancl_step:
  assumes "r\<^sup>*\<^sup>* a b"
  shows "\<exists>n.(a,b) \<in> r ^^ n"
  using rtrancl_imp_UN_relpow
proof -
  from \<open>r\<^sup>*\<^sup>* a b\<close> have "(a,b) \<in> (r\<^sup>*)"

  from \<open>r\<^sup>*\<^sup>* a b\<close> have "(a,b) \<in> (\<Union>n. R ^^ n)" using rtrancl_imp_UN_relpow 
  

lemma step_induct:
assumes major: "r\<^sup>*\<^sup>* a b"
and cases: "P b" "\<And>y z. r y z \<Longrightarrow> r\<^sup>*\<^sup>* z b \<Longrightarrow> P z \<Longrightarrow> P y"
shows True


end