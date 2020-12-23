theory PassificationEndToEnd
imports  Semantics Util Passification VCExprHelper
begin

fun initial_set :: "'a absval_ty_fun \<Rightarrow> passive_rel \<Rightarrow> var_context \<Rightarrow> var_context \<Rightarrow> rtype_env \<Rightarrow> 'a nstate \<Rightarrow> ('a nstate) set"
  where "initial_set A R \<Lambda> \<Lambda>' \<Omega> ns = 
              {u. state_typ_wf A \<Omega> (local_state u) (snd \<Lambda>') \<and> state_typ_wf A \<Omega> (global_state u) (fst \<Lambda>') \<and>
              (\<forall>x y. R x = Some (Inl y) \<longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda>' u y) \<and> (\<forall> x y. map_of (fst \<Lambda>) x = Some y \<longrightarrow> (global_state u) x = (global_state ns) x) \<and>
              binder_state u = Map.empty}"

fun initial_state_local :: "'a absval_ty_fun \<Rightarrow> rtype_env \<Rightarrow> passive_rel \<Rightarrow> var_context \<Rightarrow> var_context \<Rightarrow> 'a nstate \<Rightarrow> 'a named_state"
  where "initial_state_local A \<Omega> R \<Lambda> \<Lambda>' ns x = 
         (case (map_of (snd \<Lambda>') x) of Some \<tau> =>
           (if (\<exists>z. R z = Some (Inl x)) then 
              lookup_var \<Lambda> ns (SOME z. R z = Some (Inl x)) 
            else 
              ( Some (val_of_type A (instantiate \<Omega> \<tau>)))             
           )
          | None \<Rightarrow> None)"

fun initial_state_global :: "'a absval_ty_fun \<Rightarrow> rtype_env \<Rightarrow> passive_rel \<Rightarrow> var_context \<Rightarrow> var_context \<Rightarrow> 'a nstate \<Rightarrow> 'a named_state"
  where "initial_state_global A \<Omega> R \<Lambda> \<Lambda>' ns x = 
           (case (map_of (fst \<Lambda>') x) of Some \<tau> =>
           (if (\<exists>z. R z = Some (Inl x)) then 
              lookup_var \<Lambda> ns (SOME z. R z = Some (Inl x)) 
            else 
              ( Some (val_of_type A (instantiate \<Omega> \<tau>)))             
           )
          | None \<Rightarrow> None)"

definition rel_range
  where "rel_range R = {y. \<exists>x. R x = Some (Inl y)}"

definition inj_on_defined 
  where "inj_on_defined R = (\<forall> x y z. R x = R y \<and> R x = Some (Inl z) \<longrightarrow> x = y)"

lemma initial_state_lookup: 
  assumes InjAssm:"inj_on_defined R" and "R x = Some (Inl y)" and "map_of (snd \<Lambda>') y = Some vd"
  shows "initial_state_local A \<Omega> R \<Lambda> \<Lambda>' ns y = lookup_var \<Lambda> ns x" (is "?u y = lookup_var \<Lambda> ns x")
proof -
  from \<open>R x = Some (Inl y)\<close> \<open>map_of (snd \<Lambda>') y = Some vd\<close> have "?u y = (lookup_var \<Lambda> ns (SOME z. R z = Some (Inl y)))" by auto
  thus "?u y = lookup_var \<Lambda> ns x" using InjAssm
    unfolding inj_on_defined_def
    by (metis (full_types, lifting) assms(2) tfl_some)       
qed

lemma initial_state_global_lookup: 
  assumes InjAssm: "inj_on_defined R" and "R x = Some (Inl y)" and "map_of (fst \<Lambda>') y = Some vd"
  shows "initial_state_global A \<Omega> R \<Lambda> \<Lambda>' ns y = lookup_var \<Lambda> ns x" (is "?u y = lookup_var \<Lambda> ns x")
proof -
  from \<open>R x = Some (Inl y)\<close> \<open>map_of (fst \<Lambda>') y = Some vd\<close> have "?u y = (lookup_var \<Lambda> ns (SOME z. R z = Some (Inl y)))" by auto
  thus "?u y = lookup_var \<Lambda> ns x" using InjAssm
    unfolding inj_on_defined_def
    by (metis (full_types, lifting) assms(2) tfl_some)    
qed

lemma init_state_elem_init_set:
  assumes 
          NonEmptyTypes:"\<And> t. closed t \<Longrightarrow> \<exists>v. type_of_val A v = t" and
          Closed:"\<And>y \<tau>. \<not>(\<exists> x. R x = Some (Inl y)) \<Longrightarrow> lookup_var_ty \<Lambda>' y = Some \<tau> \<Longrightarrow> closed (instantiate \<Omega> \<tau>)" and          
          RelTy:"\<And>x y. R x = Some (Inl y) \<Longrightarrow> lookup_var_ty \<Lambda> x = lookup_var_ty \<Lambda>' y" and
          RelWt:"rel_well_typed A \<Lambda> \<Omega> R ns" and
          InjAssm:"inj_on_defined R" and
          GlobalsSame: "fst \<Lambda> = fst \<Lambda>'" and
          WellTyp: "(state_typ_wf A \<Omega> (global_state ns) (fst \<Lambda>))" and
       (* since the initial state's global state is the same as for n_s (otherwise the axiom assumption cannot be satisfied)
          the lemma requires that that the R maps globals to globals (otherwise it cannot be shown that ns and u respect R)*)
          RelGlobalsSame: "\<forall>x y. R x = Some (Inl y) \<longrightarrow> map_of (fst \<Lambda>') y \<noteq> None \<longrightarrow> x = y" and 
       (* no shadowing *)
          ConstsDisj:"set (map fst (fst \<Lambda>)) \<inter> set (map fst (snd \<Lambda>)) = {}" and
          ConstsDisj2:"set (map fst (fst \<Lambda>')) \<inter> set (map fst (snd \<Lambda>')) = {}"
        shows "\<lparr>old_global_state = Map.empty, 
               global_state = global_state ns, 
               local_state = (initial_state_local A \<Omega> R \<Lambda> \<Lambda>' ns), 
               binder_state = Map.empty \<rparr> \<in> initial_set A R \<Lambda> \<Lambda>' \<Omega> ns" (is "?u \<in> ?U")
proof (simp only: initial_set.simps, rule, intro conjI)
  show "state_typ_wf A \<Omega> (local_state ?u) (snd \<Lambda>')"
    unfolding state_typ_wf_def
  proof ((rule allI)+, rule impI)
    fix y \<tau>
    assume localy:"map_of (snd \<Lambda>') y = Some \<tau>"
    hence LookupTyY:"lookup_var_ty \<Lambda>' y = Some \<tau>"
      by (simp add: lookup_var_ty_local) 
    show "map_option (type_of_val A) (local_state ?u y) = Some (instantiate \<Omega> \<tau>)"
    proof (cases "\<exists>x. R x = Some (Inl y)")
      case True
      from this obtain x where "R x = Some (Inl y)" by auto
      hence LookupUY:"local_state ?u y = lookup_var \<Lambda> ns x"
          by (metis (no_types) \<open>R x = Some (Inl y)\<close> initial_state_lookup[OF InjAssm] localy nstate.select_convs(3))
      from RelTy RelWt obtain v where
              "lookup_var \<Lambda> ns x = Some v" and "type_of_val A v = instantiate \<Omega> \<tau>"
        unfolding rel_well_typed_def using LookupTyY \<open>R x = Some (Inl y)\<close>
        by fastforce 
      thus ?thesis using LookupUY by auto
    next
      case False
      hence "local_state ?u y = Some (val_of_type A (instantiate \<Omega> \<tau>))"
        by (simp add: \<open>map_of (snd \<Lambda>') y = Some \<tau>\<close>) 
      thus ?thesis using  False LookupTyY Closed val_of_type_correct NonEmptyTypes
        by blast      
    qed
  qed
next
  show "state_typ_wf A \<Omega> (global_state ?u) (fst \<Lambda>')" using WellTyp GlobalsSame by simp
next
  show "\<forall> x y. R x = Some (Inl y) \<longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda>' ?u y"
  proof (rule+)
    fix x y
    assume "R x = Some (Inl y)"
    hence SameTy:"lookup_var_ty \<Lambda> x = lookup_var_ty \<Lambda>' y" using RelTy by simp
    moreover from \<open>R x = Some (Inl y)\<close> RelWt obtain \<tau> where LookupX:"lookup_var_ty \<Lambda> x = Some \<tau>"
      by (meson rel_well_typed_def)
    hence "lookup_var_ty \<Lambda>' y = Some \<tau>" using RelTy[OF \<open>R x = Some (Inl y)\<close>] by simp    
    show "lookup_var \<Lambda> ns x = lookup_var \<Lambda>' ?u y"
    proof (cases "map_of (snd \<Lambda>') y = None")
      case True
      hence global_y:"map_of (fst \<Lambda>') y = Some \<tau>" using \<open>lookup_var_ty \<Lambda>' y = Some \<tau>\<close> 
        by (simp add: lookup_var_ty_global_3)
      from True have "lookup_var \<Lambda>' ?u y = global_state ?u y"
        by (simp add: lookup_var_def)
      hence lookup_global_u:"lookup_var \<Lambda>' ?u y = global_state ns y" by simp
      from global_y have "map_of (fst \<Lambda>) y = Some \<tau>" using GlobalsSame by simp
      moreover from this have "map_of (snd \<Lambda>) y = None" using ConstsDisj 
        by (metis GlobalsSame disjoint_iff_not_equal list.set_map map_of_eq_None_iff option.distinct(1))
      ultimately have "lookup_var \<Lambda> ns y = (global_state ns) y" by (simp add: lookup_var_def)
      with lookup_global_u have "lookup_var \<Lambda> ns y = lookup_var \<Lambda>' ?u y" by simp
      moreover from \<open>map_of (fst \<Lambda>') y = Some \<tau>\<close> \<open>R x = Some (Inl y)\<close> RelGlobalsSame have "x = y" by simp
      ultimately show ?thesis by simp
    next
      case False
      hence "lookup_var \<Lambda>' ?u y = local_state ?u y"
        by (metis lookup_var_local option.exhaust_sel prod.collapse)      
      hence "\<dots> = (lookup_var \<Lambda> ns (SOME z. R z = Some (Inl y)))" using \<open>R x = Some (Inl y)\<close> False by auto      
      then show ?thesis using InjAssm \<open>R x = Some (Inl y)\<close> initial_state_lookup
        by (metis False \<open>lookup_var \<Lambda>' ?u y = local_state ?u y\<close> nstate.select_convs(3) option.collapse)
    qed
  qed
next
  show "\<forall>x y. map_of (fst \<Lambda>) x = Some y \<longrightarrow> (global_state ?u) x = (global_state ns) x" by simp
next
  show "binder_state ?u = Map.empty"
    by simp
qed

lemma init_set_non_empty:
  assumes NonEmptyTypes:"\<And> t. closed t \<Longrightarrow> \<exists>v. type_of_val A v = t" and
          Closed:"\<And>y \<tau>. \<not>(\<exists> x. R x = Some (Inl y)) \<Longrightarrow> lookup_var_ty \<Lambda>' y = Some \<tau> \<Longrightarrow> closed (instantiate \<Omega> \<tau>)" and          
          RelTy:"\<And>x y. R x = Some (Inl y) \<Longrightarrow> lookup_var_ty \<Lambda> x = lookup_var_ty \<Lambda>' y" and
          RelWt:"rel_well_typed A \<Lambda> \<Omega> R ns" and
          InjAssm:"inj_on_defined R" and
          GlobalsSame: "fst \<Lambda> = fst \<Lambda>'" and
          WellTyp: "(state_typ_wf A \<Omega> (global_state ns) (fst \<Lambda>))" and
          RelGlobalsSame: "\<forall>x y. R x = Some (Inl y) \<longrightarrow> map_of (fst \<Lambda>') y \<noteq> None \<longrightarrow> x = y" and 
          ConstsDisj:"set (map fst (fst \<Lambda>)) \<inter> set (map fst (snd \<Lambda>)) = {}" and
          ConstsDisj2:"set (map fst (fst \<Lambda>')) \<inter> set (map fst (snd \<Lambda>')) = {}"
  shows "initial_set A R \<Lambda> \<Lambda>' \<Omega> ns \<noteq> {}"
  using assms init_state_elem_init_set by blast

lemma init_state_dependent:"dependent A \<Lambda>' \<Omega> (initial_set A R \<Lambda> \<Lambda>' \<Omega> ns) ((rel_range R) \<union> set (map fst (fst \<Lambda>)))" 
         (is "dependent A \<Lambda>' \<Omega> ?U ((rel_range R) \<union> set (map fst (fst \<Lambda>))) ")
  unfolding dependent_def closed_set_ty_def
  proof (rule ballI, rule allI, rule allI, rule impI, rule conjI[OF _ impI[OF allI[OF impI]]])
    fix u \<tau> d
    assume "u \<in> ?U"
    hence S1:"state_typ_wf A \<Omega> (local_state u) (snd \<Lambda>')" and S2:"state_typ_wf A \<Omega> (global_state u) (fst \<Lambda>')" by auto
    assume LookupTy:"lookup_var_ty \<Lambda>' d = Some \<tau>"
    thus "lookup_var_ty_match A \<Lambda>' \<Omega> u d \<tau>"
      using state_typ_wf_lookup[OF S1 S2 LookupTy] 
      by (simp add: lookup_var_ty_match_def)
  next
    fix u \<tau> d v
    assume "u \<in> ?U"
    hence S1:"state_typ_wf A \<Omega> (local_state u) (snd \<Lambda>')" and
          S2:"state_typ_wf A \<Omega> (global_state u) (fst \<Lambda>')" and
          Rel1: "(\<forall>x y. R x = Some (Inl y) \<longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda>' u y)" and
          Binder1: "binder_state u = Map.empty" by auto
    assume LookupTy:"lookup_var_ty \<Lambda>' d = Some \<tau>"
    assume dNotElem:"d \<notin> rel_range R \<union> set (map fst (fst \<Lambda>))"
    assume TypV:"type_of_val A v = instantiate \<Omega> \<tau>"
    have S1Upd:"state_typ_wf A \<Omega> (local_state (update_var \<Lambda>' u d v)) (snd \<Lambda>')"
      unfolding state_typ_wf_def
    proof (rule allI, rule allI, rule impI)
      fix x \<tau>'
      assume MapOfX:"map_of (snd \<Lambda>') x = Some \<tau>'"
      show  "map_option (type_of_val A) (local_state (update_var \<Lambda>' u d v) x) = Some (instantiate \<Omega> \<tau>')"
      proof (cases "d = x")
        case True
        then show ?thesis 
          by (metis LookupTy MapOfX TypV lookup_var_local lookup_var_ty_local option.simps(9) prod.collapse update_var_same)
      next
        case False
        from S1 MapOfX have "map_option (type_of_val A) (local_state u x) = Some (instantiate \<Omega> \<tau>')"
          using state_typ_wf_def by blast        
        with False show ?thesis using local_state_update_other
          by metis
      qed
    qed
    have S2Upd:"state_typ_wf A \<Omega> (global_state (update_var \<Lambda>' u d v)) (fst \<Lambda>')"
      unfolding state_typ_wf_def
    proof (rule allI, rule allI, rule impI)
      fix x \<tau>'
      assume MapOfX:"map_of (fst \<Lambda>') x = Some \<tau>'"
      from S2 MapOfX have GlobalUX:"map_option (type_of_val A) (global_state u x) = Some (instantiate \<Omega> \<tau>')" using state_typ_wf_def by blast
      show  "map_option (type_of_val A) (global_state (update_var \<Lambda>' u d v) x) = Some (instantiate \<Omega> \<tau>')"
      proof (cases "map_of (snd \<Lambda>') d = None")
        case True 
        hence Aux1:"global_state (update_var \<Lambda>' u d v) = (global_state u)(d \<mapsto> v)"  by (simp add: global_update)
        show ?thesis
          proof (cases "d = x")
            case True
            moreover with MapOfX LookupTy \<open>map_of (snd \<Lambda>') d = None\<close> have "\<tau> = \<tau>'"
              by (simp add: lookup_var_ty_global) 
            ultimately show ?thesis
              apply (subst Aux1)
              using TypV MapOfX
              by simp
          next
            case False
            thus ?thesis using global_state_update_other GlobalUX
              by metis               
          qed
      next
        case False
        hence Aux2: "global_state (update_var \<Lambda>' u d v) = global_state u" using global_state_update_local by blast
        thus ?thesis using GlobalUX by simp             
        qed
    qed
    have Rel1Upd: "\<forall>x y. R x = Some (Inl y) \<longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda>' (update_var \<Lambda>' u d v) y"
    proof (rule allI, rule allI, rule impI)
      fix x y
      assume "R x = Some (Inl y)"
      show "lookup_var \<Lambda> ns x = lookup_var \<Lambda>' (update_var \<Lambda>' u d v) y"
        apply (cases "d = y")
        using \<open>R x = Some (Inl y)\<close> dNotElem
         apply (simp add: rel_range_def)
        using Rel1 \<open>R x = Some (Inl y)\<close> 
        apply simp
        done
    qed 
    have GlobalConstraint: "\<forall>x y. map_of (fst \<Lambda>) x = Some y \<longrightarrow> global_state (update_var \<Lambda>' u d v) x = global_state ns x"
    proof (rule+)
      fix x y
      assume "map_of (fst \<Lambda>) x = Some y"
      hence "d \<noteq> x" using dNotElem
        by (metis UnCI domI dom_map_of_2)
      thus "global_state (update_var \<Lambda>' u d v) x = global_state ns x" using \<open>u \<in> ?U\<close>
        by (simp add: \<open>map_of (fst \<Lambda>) x = Some y\<close> global_state_update_other)
    qed
    show "update_var \<Lambda>' u d v \<in> ?U" 
      apply (simp only: initial_set.simps)
      apply (rule Set.CollectI)
      apply (intro conjI)
         apply (rule S1Upd)
      apply (rule S2Upd)
        apply (rule Rel1Upd)
      apply (rule GlobalConstraint)
      using update_var_binder_same Binder1 
      by metis
  qed

lemma const_rel:
  assumes Rel:"nstate_rel ((consts@globals),locals) (consts@globals2, locals2) R ns u" and
          R_consts:"list_all (\<lambda>vd. R (fst vd) = Some (Inl (fst vd))) consts" and
          ConstsDisj:"set (map fst consts) \<inter> set (map fst locals) = {}" and
          ConstsDisj2:"set (map fst consts) \<inter> set (map fst locals2) = {}"
  shows "state_restriction (global_state ns) consts = state_restriction (global_state u) consts"  
proof (rule HOL.ext)
  fix x
  show "state_restriction (global_state ns) consts x = state_restriction (global_state u) consts x"
  proof (cases "map_of consts x \<noteq> None")
    case True
    from this obtain \<tau> where "map_of consts x = Some \<tau>" by auto
    moreover have "map_of locals x = None" and "map_of locals2 x = None" using ConstsDisj ConstsDisj2
      by (metis True disjoint_iff_not_equal domIff dom_map_of_2)+
    ultimately have LookupNs:"lookup_var ((consts@globals),locals) ns x = global_state ns x" and
                    LookupU:"lookup_var ((consts@globals2),locals2) u x = global_state u x"
      by (auto simp add: lookup_var_global)
    from \<open>map_of consts x = Some \<tau>\<close> have "(x,\<tau>) \<in> set (consts)"
      by (simp add: map_of_SomeD) 
    with R_consts have "R x = Some (Inl x)"
      by (metis (mono_tags, lifting) fst_conv in_set_conv_decomp_last list.pred_inject(2) list_all_append) 
    with Rel have "lookup_var ((consts@globals),locals) ns x = lookup_var ((consts@globals2),locals2) u x"
      by (simp add: nstate_rel_def)
    with LookupNs LookupU show ?thesis using \<open>map_of consts x \<noteq> None\<close> 
      by (simp add: state_restriction_def)
  next
    case False
    then show ?thesis 
      by (simp add: state_restriction_def)      
  qed
qed

lemma rel_well_typed_state_typ_wf: 
  assumes S1:"state_typ_wf A \<Omega> (local_state ns) (snd \<Lambda>)" and
          S2:"state_typ_wf A \<Omega> (global_state ns) (fst \<Lambda>)" and
          RelWtVar:"\<And>x y. R x = Some (Inl y) \<Longrightarrow> \<exists>\<tau>. lookup_var_ty \<Lambda> x = Some \<tau>" and
          RelWtConst:"\<And>x y. R x = Some (Inr y) \<Longrightarrow> lookup_var \<Lambda> ns x = Some (LitV y) \<and> (\<exists>\<tau>. lookup_var_ty \<Lambda> x = Some \<tau>)"
        shows "rel_well_typed A \<Lambda> \<Omega> R ns"
  unfolding rel_well_typed_def rel_const_correct_def
  apply (rule conjI, rule allI, rule allI, rule impI)
  using state_typ_wf_lookup[OF S1 S2] RelWtVar
   apply blast
  using RelWtConst
  using \<open>\<And>x \<tau>. lookup_var_ty \<Lambda> x = Some \<tau> \<Longrightarrow> \<exists>v. lookup_var \<Lambda> ns x = Some v \<and> type_of_val A v = instantiate \<Omega> \<tau>\<close> by force

lemma lookup_ty_passive_closed:
  assumes "lookup_var_ty \<Lambda> x = Some \<tau>" and
          PredGlobal:"list_all (\<lambda>t. P (snd t)) (fst \<Lambda>)" and
          PredLocal:"list_all (\<lambda>t. P (snd t)) (snd \<Lambda>)"
  shows "P \<tau>"
proof (cases "map_of (snd \<Lambda>) x = None")
  case True
  hence "map_of (fst \<Lambda>) x = Some \<tau>" using \<open>lookup_var_ty \<Lambda> x = Some \<tau>\<close>
    by (simp add: lookup_var_ty_global_3)  
  then have "(x,\<tau>) \<in> set (fst \<Lambda>)" by (simp add: map_of_SomeD) 
  moreover from PredGlobal have "\<forall>r \<in> set (fst \<Lambda>). (\<lambda>t. P (snd t)) r" by (simp add:  List.list_all_iff)
  ultimately have "(\<lambda>t. P (snd t)) (x,\<tau>)" by blast
  thus ?thesis by simp
next
  case False
  hence "map_of (snd \<Lambda>) x = Some \<tau>" using \<open>lookup_var_ty \<Lambda> x = Some \<tau>\<close>
    using lookup_var_ty_local by fastforce
  then have "(x,\<tau>) \<in> set (snd \<Lambda>)" by (simp add: map_of_SomeD) 
  moreover from PredLocal have "\<forall>r \<in> set (snd \<Lambda>). (\<lambda>t. P (snd t)) r" by (simp add:  List.list_all_iff)
  ultimately have "(\<lambda>t. P (snd t)) (x,\<tau>)" by blast
  thus ?thesis by simp
qed

lemma convert_fun_to_list:
assumes A0:"R_fun = map_of R_list" and
        A1:"list_all (\<lambda>t. P (fst t) (snd t)) R_list"
      shows  "R_fun x = Some y \<longrightarrow> P x y"    
proof (rule+)  
  assume "R_fun x = Some y"
  hence "(x,y) \<in> set (R_list)"
    using A0
    by (simp add: map_of_SomeD)
  moreover from A1 have "\<forall>t \<in> set (R_list). (\<lambda>t. P (fst t) (snd t)) t"
    by (simp only: List.list_all_iff)
  ultimately show "P x y" by auto
qed

fun custom_cmp :: "(nat + lit) \<Rightarrow> (nat + lit) \<Rightarrow> bool"
  where 
    "custom_cmp (Inl n) (Inl m) = (n < m)"
  | "custom_cmp _ _ = False"

lemma custom_cmp_diff: "custom_cmp a b \<Longrightarrow> a \<noteq> b"
  by (cases a, cases b) auto  

fun strictly_ordered :: "(nat + lit) list \<Rightarrow> bool"
  where 
    "strictly_ordered [] = True"
  | "strictly_ordered [x] = True"
  | "strictly_ordered (x#y#zs) = (custom_cmp x y \<and> strictly_ordered (y#zs))"

lemma strictly_ordered_smaller: "strictly_ordered ((Inl a)#xs) \<Longrightarrow> (\<forall> y \<in> (set xs). \<exists>a'. y= Inl a' \<and> a < a')"
proof (induction arbitrary:a rule: strictly_ordered.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case apply simp 
    using custom_cmp.elims(2) by blast
next
  case (3 x y zs)
  then show ?case apply simp
    by (smt Inl_inject custom_cmp.elims(2) order.strict_trans)
qed

lemma strictly_ordered_distinct: "strictly_ordered xs \<Longrightarrow> distinct xs"
proof (induction rule: strictly_ordered.induct)
case 1
then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x y zs)
  then show ?case apply simp
    by (metis (full_types) custom_cmp.elims(2) custom_cmp.simps(1) strictly_ordered_smaller sup.strict_boundedE sup.strict_order_iff)
qed

lemma distinct_helper:
  assumes A1:"(x, fx) \<in> set xs" and 
          A2:"(y, fy) \<in> set xs" and
          "x \<noteq> y"
          "distinct (map snd xs)"
        shows "fx \<noteq> fy"
  using assms
  by (smt distinct_conv_nth fst_conv in_set_zip snd_conv zip_map_fst_snd) 

lemma injective_fun_to_list:
  assumes R_fun_def: "R_fun = map_of R_list" and
          Distinct:"distinct (map snd R_list)"
  shows "inj_on_defined R_fun"
  unfolding inj_on_defined_def distinct_helper  
proof ((rule allI)+, rule impI, erule conjE)
  fix x y z
  let ?map_of_x = "map_of R_list x"
  let ?map_of_y = "map_of R_list y"
  assume "R_fun x = R_fun y" and "R_fun x = Some (Inl z)"
  hence "(x, Inl z) \<in> set R_list"
    using R_fun_def \<open>R_fun x = Some (Inl z)\<close> map_of_SomeD by force
  moreover have "(y, Inl z) \<in> set R_list" 
    using R_fun_def \<open>R_fun x = Some (Inl z)\<close> \<open>R_fun x = R_fun y\<close> map_of_SomeD by fastforce
  ultimately show "x = y"
  using distinct_helper Distinct by fastforce
qed

lemma injective_fun_to_list_2:
  assumes "R_fun = map_of R_list" and
          "strictly_ordered (map snd R_list)"
  shows "inj_on_defined R_fun"
  using assms injective_fun_to_list strictly_ordered_distinct by blast

fun max_rel :: "(nat + lit) list \<Rightarrow> nat"
  where 
    "max_rel [] = 0"
  | "max_rel ((Inl n) # xs) = (max n (max_rel xs))" 
  | "max_rel ((Inr l) # xs) = (max_rel xs)"


lemma max_rel_aux:
  assumes "max_rel xs = w_max" and "(Inl n) \<in> set xs" 
  shows "n \<le> w_max"
  using assms
  apply (induction arbitrary: n w_max rule: max_rel.induct)
    apply simp
   apply fastforce
  apply simp
  done

fun max_rel_tail :: "nat \<Rightarrow> (nat + lit) list \<Rightarrow> nat"
  where 
    "max_rel_tail k [] = k"
  | "max_rel_tail k ((Inl n) # xs) = (max_rel_tail (max n k) xs)" 
  | "max_rel_tail k ((Inr l) # xs) = (max_rel_tail k xs)"

lemma max_rel_tail_equiv_aux: "max_rel_tail k xs = max k (max_rel xs)"
  by (induction arbitrary: k rule: max_rel.induct) auto

lemma max_tail_equiv: "max_rel_tail 0 xs = max_rel xs"
  by (simp add: max_rel_tail_equiv_aux)

lemma rel_range_fun_to_list:
  assumes R_fun_def:"R_fun = map_of R_list" and
          "max_rel_tail 0 (map snd R_list) = w_max"
  shows "\<forall>x. x \<in> rel_range R_fun \<longrightarrow> x \<le> w_max"
  unfolding rel_range_def
proof (rule, rule)
  fix x
  assume "x \<in> {y. \<exists>x. R_fun x = Some (Inl y)}"
  from this obtain z where "R_fun z = Some (Inl x)" by auto
  hence "map_of R_list z = Some (Inl x)" using R_fun_def by simp
  hence "(z,Inl x) \<in> set (R_list)"
    by (simp add: map_of_SomeD)
  thus "x \<le> w_max" using max_tail_equiv max_rel_aux
    by (metis assms(2) set_zip_rightD zip_map_fst_snd)
qed


lemma axiom_assm_aux:
  assumes "axiom_assm A \<Gamma> consts ns1 axioms" and
          "\<And> x y. map_of consts x = Some y \<Longrightarrow> (global_state ns1) x = (global_state ns2) x"
        shows "axiom_assm A \<Gamma> consts ns2 axioms"
  using assms
  unfolding state_restriction_def
proof -
  have Aux:" (\<lambda>x. if map_of consts x \<noteq> None then global_state ns2 x else None) =  (\<lambda>x. if map_of consts x \<noteq> None then global_state ns1 x else None)"
    using assms(2) by fastforce
  show "axioms_sat A (consts, []) \<Gamma> (global_to_nstate (\<lambda>x. if map_of consts x \<noteq> None then global_state ns2 x else None)) axioms"
    apply (subst Aux)
    using assms(1)
    unfolding state_restriction_def
    apply assumption
    done
qed

lemma helper_init_disj:
  assumes Max1:"\<forall>x. x \<in> xs \<longrightarrow> x \<le> n" and "\<forall>y. y \<in> ys \<longrightarrow> y \<le> m" and "n < w_max" and "m < w_max"
  shows "{w. (w :: nat) \<ge> w_max} \<inter> (xs \<union> ys) = {}"
  using assms
  by auto


  
end