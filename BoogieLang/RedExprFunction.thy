theory RedExprFunction
imports Semantics
begin

fun expr_size :: "expr \<Rightarrow> nat"
  where
    "expr_size (Var x) = 0"
  | "expr_size (Val v) = 0"
  | "expr_size (BVar v) = 0"
  | "expr_size (UnOp up e) = size(e)+1"
  | "expr_size (e1 \<guillemotleft>bop\<guillemotright> e2) = size(e1)+size(e2)+1"
  | "expr_size (FunExp f args) = (sum_list (map size args))+1"
  | "expr_size (Forall ty e) = size(e)+1"
  | "expr_size (Exists ty e) = size(e)+1"

lemma map_eq: "\<lbrakk>\<forall>i. (f (xs ! i) = f (ys ! i)); length xs = length ys\<rbrakk> \<Longrightarrow> map f xs = map f ys"
  sorry

lemma size_eopen: "size (eopen i (Val v) e) = size e"
proof (induction e arbitrary: i; (fastforce | tactic \<open>all_tac\<close>))
case (FunExp f args)
  have "size (eopen i (Val v) (FunExp f args)) = size (FunExp f (map (eopen i (Val v)) args))" by simp
  have "map size args = (map size (map (eopen i (Val v)) args))" 
    apply (rule map_eq)
     apply rule
    using FunExp.IH 
    sorry
  show ?case sorry
qed

(* note that BVar x will never need to be evaluated if the expression reduces *)
function red_expr_fun :: "fun_context \<Rightarrow> expr \<Rightarrow> nstate \<Rightarrow> val"
  where 
    "red_expr_fun \<Gamma> (Var x) n_s = the (n_s(x))"
  | "red_expr_fun \<Gamma> (BVar x) n_s = BoolV False"
  | "red_expr_fun \<Gamma> (Val v) n_s = v"
  | "red_expr_fun \<Gamma> (UnOp uop e) n_s = the (unop_eval uop (red_expr_fun \<Gamma> e n_s))"
  | "red_expr_fun \<Gamma> (e1 \<guillemotleft>bop\<guillemotright> e2) n_s = the (binop_eval bop (red_expr_fun \<Gamma> e1 n_s) (red_expr_fun \<Gamma> e2 n_s))"
  | "red_expr_fun \<Gamma> (FunExp f args) n_s = 
      (let f_interp = the ( (snd \<Gamma>) f) in
      (let v_args = map (\<lambda>e. red_expr_fun \<Gamma> e n_s) args in
      the (f_interp v_args)))"
  | "red_expr_fun \<Gamma> (Forall ty e) n_s = 
        BoolV (\<forall>v. type_of_val v = ty \<longrightarrow> ((red_expr_fun \<Gamma> (eopen 0 (Val v) e) n_s) = BoolV True))"
  | "red_expr_fun \<Gamma> (Exists ty e) n_s =
        BoolV (\<exists>v. type_of_val v = ty \<and> ((red_expr_fun \<Gamma> (eopen 0 (Val v) e) n_s) = BoolV True))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(\<Gamma>, e, n_s). size(e))")
  apply (simp_all add: size_eopen)
  using not_less_eq size_list_estimation apply fastforce
  done

lemma red_expr_fun_rel:
  shows "\<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v \<Longrightarrow> red_expr_fun \<Gamma> e n_s = v" and
       "\<Gamma> \<turnstile> \<langle>es, n_s\<rangle> [\<Down>] vs \<Longrightarrow> map (\<lambda> e. red_expr_fun \<Gamma> e n_s) es = vs"
  by (induction rule: red_expr_red_exprs.inducts, auto)

end