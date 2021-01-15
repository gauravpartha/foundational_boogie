theory RedExprFunction
imports Semantics
begin

(* not up-to-date
fun red_expr_fun :: "'a absval_ty_fun \<Rightarrow> 'a fun_context \<Rightarrow> rtype_env \<Rightarrow> expr \<Rightarrow> 'a nstate \<Rightarrow> 'a val"
  where 
    "red_expr_fun A \<Gamma> \<Omega> (Var x) n_s = the (n_s(x))"
  | "red_expr_fun A \<Gamma> \<Omega> (Lit lit) n_s = LitV lit"
  | "red_expr_fun A \<Gamma> \<Omega> (UnOp uop e) n_s = the (unop_eval_val uop (red_expr_fun A \<Gamma> \<Omega> e n_s))"
  | "red_expr_fun A \<Gamma> \<Omega> (e1 \<guillemotleft>bop\<guillemotright> e2) n_s = the (binop_eval_val bop (red_expr_fun A \<Gamma> \<Omega> e1 n_s) (red_expr_fun A \<Gamma> \<Omega> e2 n_s))"
  | "red_expr_fun A \<Gamma> \<Omega> (FunExp f tys args) n_s = 
      (let f_interp = the ( (snd \<Gamma>) f) in
      (let v_args = map (\<lambda>e. red_expr_fun A \<Gamma> \<Omega> e n_s) args in
      the (f_interp (map (instantiate \<Omega>) tys) v_args)))"
  | "red_expr_fun A \<Gamma> \<Omega> (Forall ty e) n_s = 
        BoolV (\<forall>v. type_of_val A v = instantiate \<Omega> ty \<longrightarrow> ((red_expr_fun A \<Gamma> \<Omega> e (ext_env n_s v)) = BoolV True))"
  | "red_expr_fun A \<Gamma> \<Omega> (Exists ty e) n_s =
        BoolV (\<exists>v. type_of_val A v = instantiate \<Omega> ty \<and> ((red_expr_fun A \<Gamma> \<Omega> e (ext_env n_s v)) = BoolV True))"
  | "red_expr_fun A \<Gamma> \<Omega> (ForallT e) n_s = BoolV (\<forall>t. closed t \<longrightarrow> ((red_expr_fun A \<Gamma> (t#\<Omega>) e n_s) = BoolV True))"
  | "red_expr_fun A \<Gamma> \<Omega> (ExistsT e) n_s = BoolV (\<exists>t. closed t \<and> ((red_expr_fun A \<Gamma> (t#\<Omega>) e n_s) = BoolV True))"

lemma red_expr_fun_rel:
  shows "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v \<Longrightarrow> red_expr_fun A \<Gamma> \<Omega> e n_s = v" and
       "A,\<Gamma>,\<Omega> \<turnstile> \<langle>es, n_s\<rangle> [\<Down>] vs \<Longrightarrow> map (\<lambda> e. red_expr_fun A \<Gamma> \<Omega> e n_s) es = vs"
proof (induction rule: red_expr_red_exprs.inducts)
  case (RedForAllTrue \<Omega> ty e n_s)
  thus ?case by fastforce
next
  case (RedForAllFalse v \<Omega> ty e n_s)
  hence "\<not>((\<forall>v. type_of_val A v = instantiate \<Omega> ty \<longrightarrow> ((red_expr_fun A \<Gamma> \<Omega> e (ext_env n_s v)) = BoolV True)))"
    by (metis lit.inject(1) val.inject(1))
  thus ?case by simp       
next
  case (RedExistsTrue v \<Omega> ty e n_s)
  hence "(\<exists>v. type_of_val A v = instantiate \<Omega> ty \<and> ((red_expr_fun A \<Gamma> \<Omega> e (ext_env n_s v)) = BoolV True))"
    by blast  
  thus ?case by simp    
next
  case (RedExistsFalse \<Omega> ty e n_s)
  thus ?case by fastforce
qed (auto)

lemma red_expr_fun_rel_2:
  shows "red_expr_fun A \<Gamma> \<Omega> e n_s = v \<Longrightarrow> A,\<Gamma>,\<Omega> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v" and
       "map (\<lambda> e. red_expr_fun A \<Gamma> \<Omega> e n_s) es = vs \<Longrightarrow> A,\<Gamma>,\<Omega> \<turnstile> \<langle>es, n_s\<rangle> [\<Down>] vs"
  oops
*)

end