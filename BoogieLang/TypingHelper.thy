section \<open>A utility theory that is used to automate typing proofs\<close>

theory TypingHelper
imports TypeSafety Semantics
begin

definition hint_ty_subst :: "ty list \<Rightarrow> bool"
  where "hint_ty_subst ty_inst = True"

text\<open>\<^term>\<open>hint_ty_subst\<close> is a dummy definition that is used in the lemmas below to easily instantiate
the type substitution required for typing (in)equality\<close>

lemma typ_binop_poly_helper:
  assumes "hint_ty_subst ty_inst" and
          "binop_poly_type bop" and
          "F,\<Delta> \<turnstile> e1 : ty1" and
          "F,\<Delta> \<turnstile> e2 : ty2" and          
          "msubstT_opt ty_inst ty1 = msubstT_opt ty_inst ty2"
  shows "F,\<Delta> \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 : TPrim (TBool)"
  using assms TypBinopPoly
  by blast

lemma typ_binop_poly_helper_2:
  assumes "binop_poly_type bop" and
          "hint_ty_subst ty_inst" and
          "F,\<Delta> \<turnstile> e1 : ty1" and
          "F,\<Delta> \<turnstile> e2 : ty2" and          
          "msubstT_opt ty_inst ty1 = msubstT_opt ty_inst ty2"
  shows "F,\<Delta> \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 : TPrim (TBool)"
  using assms TypBinopPoly
  by blast

lemma typ_binop_poly_helper_empty:
  assumes "binop_poly_type bop" and
          "F,\<Delta> \<turnstile> e1 : ty1" and
          "F,\<Delta> \<turnstile> e2 : ty2" and          
          "ty1 = ty2"
  shows "F,\<Delta> \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 : TPrim (TBool)"
  using assms TypBinopPoly
  by blast

lemma typ_funexp_helper:
  assumes "map_of F f = Some (n_ty_params, args_ty, ret_ty)" and
          "length ty_params = n_ty_params" and
          "length args = length args_ty" and
          "\<tau> = (msubstT_opt ty_params ret_ty)" and
          "F,\<Delta> \<turnstile> args [:] (map (msubstT_opt ty_params) args_ty)"
        shows "F,\<Delta> \<turnstile> FunExp f ty_params args : \<tau>"
  using assms TypFunExp
  by blast

text \<open>The following corollary of type safety is used in the certification of the CFG-to-DAG phase 
to prove that that invariants reduce to booleans.\<close>

lemma type_safety_top_level_inv:
  assumes 
          Wf_\<Gamma>: "fun_interp_wf A F \<Gamma>" and
          Wf_F: "list_all (wf_fdecl \<circ> snd) F" and
          Wf_\<Lambda>: "\<forall>x \<tau>. lookup_var_ty \<Lambda> x = Some \<tau> \<longrightarrow> wf_ty 0 \<tau>" and    
          "state_well_typed A \<Lambda> [] n_s" and
          Wf_e: "wf_expr (length []) e" and
          "F, (lookup_var_ty \<Lambda>, Map.empty) \<turnstile> e : TPrim TBool"
        shows "\<exists>b. (A,\<Lambda>,\<Gamma>,[] \<turnstile> \<langle>e,n_s\<rangle> \<Down> (BoolV b))"
proof -
  have "\<exists>v. (A,\<Lambda>,\<Gamma>,[] \<turnstile> \<langle>e,n_s\<rangle> \<Down> v) \<and> type_of_val A v = instantiate [] (TPrim TBool)"
    apply (rule type_safety_top_level)
    using assms
    by auto
  thus ?thesis
    by (metis instantiate_nil type_of_val_bool_elim)
qed

lemma type_safety_top_level_inv_int:
  assumes 
          Wf_\<Gamma>: "fun_interp_wf A F \<Gamma>" and
          Wf_F: "list_all (wf_fdecl \<circ> snd) F" and
          Wf_\<Lambda>: "\<forall>x \<tau>. lookup_var_ty \<Lambda> x = Some \<tau> \<longrightarrow> wf_ty 0 \<tau>" and    
          "state_well_typed A \<Lambda> [] n_s" and
          Wf_e: "wf_expr (length []) e" and
          "F, (lookup_var_ty \<Lambda>, Map.empty) \<turnstile> e : TPrim TInt"
  shows "\<exists>i. (A,\<Lambda>,\<Gamma>,[] \<turnstile> \<langle>e,n_s\<rangle> \<Down> (IntV i))"
proof -
  have "\<exists>v. (A,\<Lambda>,\<Gamma>,[] \<turnstile> \<langle>e,n_s\<rangle> \<Down> v) \<and> type_of_val A v = instantiate [] (TPrim TInt)"
    apply (rule type_safety_top_level)
    using assms
    by auto
  thus ?thesis
    by (metis instantiate_nil type_of_val_int_elim)
qed

lemma type_safety_top_level_inv_real:
  assumes 
          Wf_\<Gamma>: "fun_interp_wf A F \<Gamma>" and
          Wf_F: "list_all (wf_fdecl \<circ> snd) F" and
          Wf_\<Lambda>: "\<forall>x \<tau>. lookup_var_ty \<Lambda> x = Some \<tau> \<longrightarrow> wf_ty 0 \<tau>" and    
          "state_well_typed A \<Lambda> [] n_s" and
          Wf_e: "wf_expr (length []) e" and
          "F, (lookup_var_ty \<Lambda>, Map.empty) \<turnstile> e : TPrim TReal"
  shows "\<exists>r. (A,\<Lambda>,\<Gamma>,[] \<turnstile> \<langle>e,n_s\<rangle> \<Down> (RealV r))"
proof -
  have "\<exists>v. (A,\<Lambda>,\<Gamma>,[] \<turnstile> \<langle>e,n_s\<rangle> \<Down> v) \<and> type_of_val A v = instantiate [] (TPrim TReal)"
    apply (rule type_safety_top_level)
    using assms
    by auto
  thus ?thesis
    by (metis instantiate_nil type_of_val_real_elim)
qed

end