theory PassificationEndToEnd
imports  Semantics Util Passification VCExprHelper
begin

fun initial_set :: "'a absval_ty_fun \<Rightarrow> passive_rel \<Rightarrow> var_context \<Rightarrow> var_context \<Rightarrow> rtype_env \<Rightarrow> 'a nstate \<Rightarrow> ('a nstate) set"
  where "initial_set A R \<Lambda> \<Lambda>' \<Omega> ns = 
              {u. state_typ_wf A \<Omega> (local_state u) (snd \<Lambda>') \<and> state_typ_wf A \<Omega> (global_state u) (fst \<Lambda>') \<and>
              (\<forall>x y. R x = Some (Inl y) \<longrightarrow> lookup_var \<Lambda> ns x = lookup_var \<Lambda>' u y) \<and>
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

lemma initial_state_lookup: 
  assumes "inj R" and "R x = Some (Inl y)" and "map_of (snd \<Lambda>') y = Some vd"
  shows "initial_state_local A \<Omega> R \<Lambda> \<Lambda>' ns y = lookup_var \<Lambda> ns x" (is "?u y = lookup_var \<Lambda> ns x")
proof -
  from \<open>R x = Some (Inl y)\<close> \<open>map_of (snd \<Lambda>') y = Some vd\<close> have "?u y = (lookup_var \<Lambda> ns (SOME z. R z = Some (Inl y)))" by auto
  thus "?u y = lookup_var \<Lambda> ns x" using \<open>inj R\<close>
    by (metis assms(2) inv_def inv_f_f) 
qed

lemma initial_state_global_lookup: 
  assumes "inj R" and "R x = Some (Inl y)" and "map_of (fst \<Lambda>') y = Some vd"
  shows "initial_state_global A \<Omega> R \<Lambda> \<Lambda>' ns y = lookup_var \<Lambda> ns x" (is "?u y = lookup_var \<Lambda> ns x")
proof -
  from \<open>R x = Some (Inl y)\<close> \<open>map_of (fst \<Lambda>') y = Some vd\<close> have "?u y = (lookup_var \<Lambda> ns (SOME z. R z = Some (Inl y)))" by auto
  thus "?u y = lookup_var \<Lambda> ns x" using \<open>inj R\<close>
    by (metis assms(2) inv_def inv_f_f) 
qed

lemma init_state_elem_init_set:
  assumes 
          NonEmptyTypes:"\<And> t. closed t \<Longrightarrow> \<exists>v. type_of_val A v = t" and
          Closed:"\<And>y \<tau>. \<not>(\<exists> x. R x = Some (Inl y)) \<Longrightarrow> lookup_var_ty \<Lambda>' y = Some \<tau> \<Longrightarrow> closed (instantiate \<Omega> \<tau>)" and          
          RelTy:"\<And>x y. R x = Some (Inl y) \<Longrightarrow> lookup_var_ty \<Lambda> x = lookup_var_ty \<Lambda>' y" and
          RelWt:"rel_well_typed A \<Lambda> \<Omega> R ns" and
                "inj R" and
       (* no shadowing *)
          ConstsDisj:"set (map fst (fst \<Lambda>')) \<inter> set (map fst (snd \<Lambda>)) = {}" and
          ConstsDisj2:"set (map fst (fst \<Lambda>')) \<inter> set (map fst (snd \<Lambda>')) = {}"
        shows "\<lparr>old_global_state = Map.empty, 
               global_state = (initial_state_global A \<Omega> R \<Lambda> \<Lambda>' ns), 
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
          by (metis (no_types) \<open>R x = Some (Inl y)\<close> initial_state_lookup[OF \<open>inj R\<close>] localy nstate.select_convs(3))
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
  show "state_typ_wf A \<Omega> (global_state ?u) (fst \<Lambda>')"
    unfolding state_typ_wf_def
  proof ((rule allI)+, rule impI)
    fix y \<tau>
    assume global_y:"map_of (fst \<Lambda>') y = Some \<tau>"
    from this moreover have "map_of (snd \<Lambda>') y = None" using ConstsDisj2
      by (metis disjoint_iff_not_equal list.set_map map_of_eq_None_iff option.distinct(1)) 
    ultimately have LookupTyY:"lookup_var_ty \<Lambda>' y = Some \<tau>"
      by (simp add: lookup_var_ty_global) 
    from \<open>map_of (fst \<Lambda>') y = Some \<tau>\<close> have "(y, \<tau>) \<in> set (fst \<Lambda>')" 
      by (simp add: map_of_SomeD) 
    show "map_option (type_of_val A) (global_state ?u y) = Some (instantiate \<Omega> \<tau>)"
    proof (cases "\<exists>x. R x = Some (Inl y)")
      case True
      from this obtain x where "R x = Some (Inl y)" by auto
      hence LookupUY:"global_state ?u y = lookup_var \<Lambda> ns x"
        by (metis \<open>R x = Some (Inl y)\<close> initial_state_global_lookup[OF \<open>inj R\<close>] global_y nstate.select_convs(2))
      from RelTy RelWt obtain v where
              "lookup_var \<Lambda> ns x = Some v" and "type_of_val A v = instantiate \<Omega> \<tau>"
        unfolding rel_well_typed_def using LookupTyY \<open>R x = Some (Inl y)\<close>
        by fastforce 
      thus ?thesis using LookupUY by auto
    next
      case False
      hence "global_state ?u y = Some (val_of_type A (instantiate \<Omega> \<tau>))"
        by (simp add: global_y) 
      thus ?thesis using  False LookupTyY Closed val_of_type_correct NonEmptyTypes
        by blast      
    qed
  qed
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
      hence "\<dots> = (lookup_var \<Lambda> ns (SOME z. R z = Some (Inl y)))" using \<open>R x = Some (Inl y)\<close> True  global_y
        by auto
      then show ?thesis using \<open>inj R\<close> \<open>R x = Some (Inl y)\<close> 
        by (metis \<open>lookup_var \<Lambda>' ?u y = global_state ?u y\<close> global_y initial_state_global_lookup nstate.select_convs(2))
    next
      case False
      hence "lookup_var \<Lambda>' ?u y = local_state ?u y"
        by (metis lookup_var_local option.exhaust_sel prod.collapse)      
      hence "\<dots> = (lookup_var \<Lambda> ns (SOME z. R z = Some (Inl y)))" using \<open>R x = Some (Inl y)\<close> False by auto      
      then show ?thesis using \<open>inj R\<close> \<open>R x = Some (Inl y)\<close> initial_state_lookup
        by (metis False \<open>lookup_var \<Lambda>' ?u y = local_state ?u y\<close> nstate.select_convs(3) option.collapse)
    qed
  qed
next
  show "binder_state ?u = Map.empty"
    by simp
qed

lemma init_set_non_empty:
  assumes NonEmptyTypes:"\<And> t. closed t \<Longrightarrow> \<exists>v. type_of_val A v = t" and
          Closed:"\<And>y \<tau>. \<not>(\<exists> x. R x = Some (Inl y)) \<Longrightarrow> lookup_var_ty \<Lambda>' y = Some \<tau> \<Longrightarrow> closed (instantiate \<Omega> \<tau>)" and          
          RelTy:"\<And>x y. R x = Some (Inl y) \<Longrightarrow> lookup_var_ty \<Lambda> x = lookup_var_ty \<Lambda>' y" and
          RelWt:"rel_well_typed A \<Lambda> \<Omega> R ns" and
          Consts:"fst \<Lambda> = (fst \<Lambda>')@globals" and
          R_consts:"list_all (\<lambda>vd. R (fst vd) = Some (Inl (fst vd))) (fst \<Lambda>')" and
                "inj R" and
          ConstsDisj:"set (map fst (fst \<Lambda>')) \<inter> set (map fst (snd \<Lambda>)) = {}" and
          ConstsDisj2:"set (map fst (fst \<Lambda>')) \<inter> set (map fst (snd \<Lambda>')) = {}"
  shows "initial_set A R \<Lambda> \<Lambda>' \<Omega> ns \<noteq> {}"
  using assms init_state_elem_init_set by blast

lemma init_state_dependent:"dependent A \<Lambda>' \<Omega> (initial_set A R \<Lambda> \<Lambda>' \<Omega> ns) (rel_range R)" 
         (is "dependent A \<Lambda>' \<Omega> ?U (rel_range R)")
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
    assume "d \<notin> rel_range R"
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
        using \<open>R x = Some (Inl y)\<close> \<open>d \<notin> rel_range R\<close> 
         apply (simp add: rel_range_def)
        using Rel1 \<open>R x = Some (Inl y)\<close> 
        apply simp
        done
    qed      
    show "update_var \<Lambda>' u d v \<in> ?U" 
      apply (simp only: initial_set.simps)
      apply (rule Set.CollectI)
      apply (intro conjI)
         apply (rule S1Upd)
      apply (rule S2Upd)
       apply (rule Rel1Upd)
      using update_var_binder_same Binder1 
      by metis
  qed

lemma dom_map_of_2:"dom (map_of R) = set (map fst R)"
  by (simp add: Map.dom_map_of_conv_image_fst)

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
  assumes RelWtVar:"\<And>x y. R x = Some (Inl y) \<Longrightarrow> \<exists>\<tau>. lookup_var_ty \<Lambda> x = Some \<tau>" and
          RelWtConst:"\<And>x y. R x = Some (Inr y) \<Longrightarrow> lookup_var \<Lambda> ns x = Some (LitV y) \<and> (\<exists>\<tau>. lookup_var_ty \<Lambda> x = Some \<tau>)" and          
          S1:"state_typ_wf A \<Omega> (local_state ns) (snd \<Lambda>)" and
          S2:"state_typ_wf A \<Omega> (global_state ns) (fst \<Lambda>)"
        shows "rel_well_typed A \<Lambda> \<Omega> R ns"
  unfolding rel_well_typed_def rel_const_correct_def
  apply (rule conjI, rule allI, rule allI, rule impI)
  using state_typ_wf_lookup[OF S1 S2] RelWtVar
   apply blast
  using RelWtConst

  using \<open>\<And>x \<tau>. lookup_var_ty \<Lambda> x = Some \<tau> \<Longrightarrow> \<exists>v. lookup_var \<Lambda> ns x = Some v \<and> type_of_val A v = instantiate \<Omega> \<tau>\<close> by force

lemma rel_well_typed_state_typ_wf_2: 
  assumes RelWtVar:"\<And>x y. R x = Some z \<Longrightarrow> \<exists>\<tau> y. z = Inl y \<and> lookup_var_ty \<Lambda> x = Some \<tau>" and          
          S1:"state_typ_wf A \<Omega> (local_state ns) (snd \<Lambda>)" and
          S2:"state_typ_wf A \<Omega> (global_state ns) (fst \<Lambda>)"
        shows "rel_well_typed A \<Lambda> \<Omega> R ns"
  using assms rel_well_typed_state_typ_wf[OF _ _ S1 S2]
  oops


end