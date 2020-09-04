theory VCExprHelper
imports Semantics Util
begin

lemma vc_to_expr:"\<lbrakk>vc; A,\<Gamma>,\<Omega> \<turnstile> \<langle>e,ns\<rangle> \<Down> LitV (LBool vc)\<rbrakk> \<Longrightarrow> A,\<Gamma>,\<Omega> \<turnstile> \<langle>e,ns\<rangle> \<Down> LitV (LBool True)"
  by simp

lemma expr_to_vc:"\<lbrakk>A,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns\<rangle> \<Down> LitV (LBool True); A,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns\<rangle> \<Down> LitV (LBool vc)\<rbrakk> \<Longrightarrow> vc"
  by (blast dest: expr_eval_determ)

(* boolean operations *)
lemma conj_vc_rel: 
  assumes "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> LitV (LBool vc1)" and "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> LitV (LBool vc2)"
  shows "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e1 \<guillemotleft>And\<guillemotright> e2, ns\<rangle> \<Down> LitV (LBool (vc1 \<and> vc2))"
  using assms
  by (auto intro: RedBinOp)

lemma disj_vc_rel: 
  assumes "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> LitV (LBool vc1)" and "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> LitV (LBool vc2)"
  shows "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e1 \<guillemotleft>Or\<guillemotright> e2, ns\<rangle> \<Down> LitV (LBool (vc1 \<or> vc2))"
  using assms
  by (auto intro: RedBinOp)

lemma imp_vc_rel: 
  assumes "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> LitV (LBool vc1)" and "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> LitV (LBool vc2)"
  shows "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e1 \<guillemotleft>Imp\<guillemotright> e2, ns\<rangle> \<Down> LitV (LBool (vc1 \<longrightarrow> vc2))"
  using assms
  by (auto intro: RedBinOp)

lemma not_vc_rel:
  assumes "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns\<rangle> \<Down> LitV (LBool vc)"
  shows "A,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp Not e, ns\<rangle> \<Down> LitV (LBool (\<not> vc))"
  using assms
  by (auto intro: RedUnOp)

(* integer operations *)
lemma add_vc_rel: 
  assumes "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> LitV (LInt vc1)" and "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> LitV (LInt vc2)"
  shows "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e1 \<guillemotleft>Add\<guillemotright> e2, ns\<rangle> \<Down> LitV (LInt (vc1 + vc2))"
  using assms
  by (auto intro: RedBinOp)

lemma sub_vc_rel: 
  assumes "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> LitV (LInt (vc1))" and "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> LitV (LInt vc2)"
  shows "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e1 \<guillemotleft>Sub\<guillemotright> e2, ns\<rangle> \<Down> LitV (LInt (vc1 - vc2))"
  using assms
  by (auto intro: RedBinOp)

lemma mul_vc_rel: 
  assumes "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> LitV (LInt vc1)" and "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> LitV (LInt vc2)"
  shows "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e1 \<guillemotleft>Mul\<guillemotright> e2, ns\<rangle> \<Down> LitV (LInt (vc1 * vc2))"
  using assms
  by (auto intro: RedBinOp)

lemma uminus_vc_rel:
  assumes "A,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns\<rangle> \<Down> LitV (LInt vc)"
  shows "A,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp UMinus e, ns\<rangle> \<Down> LitV (LInt (- vc))"
  using assms
  by (auto intro: RedUnOp)

(* quantifiers *)
lemma forall_vc_rel_general: 
  assumes "\<And> i. A,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ext_env ns (LitV (C i))\<rangle> \<Down> LitV (LBool (P i))" and
          "\<And> i v. type_of_val A v = Some (TPrim primty) \<Longrightarrow> \<exists>i. v = LitV (C i)"
          "\<And> i. type_of_val A (LitV (C i)) = Some (TPrim primty)"
  shows  "A,\<Gamma>,\<Omega> \<turnstile> \<langle>Forall (TPrim primty) e, ns\<rangle> \<Down> LitV (LBool (\<forall>i. P i))"
proof (cases "(\<forall>i. P i)")
  case True
  thus ?thesis using assms by (fastforce intro: RedForAllTrue)
next
  case False
  from this obtain z where "\<not>(P z)" by auto
  have "A,\<Gamma>,\<Omega> \<turnstile> \<langle>Forall (TPrim primty) e, ns\<rangle> \<Down> LitV (LBool False)"
    apply (rule RedForAllFalse[where ?v = "LitV (C z)"])
    apply simp
    using assms(3) apply auto[1]
    by (metis (full_types) \<open>\<not> P z\<close> assms(1))
  then show ?thesis by (simp add: False)
qed

lemma exists_vc_rel_general:
  assumes "\<And> i. A,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ext_env ns (LitV (C i))\<rangle> \<Down> LitV (LBool (P i))"
          "\<And> i v. type_of_val A v = Some (TPrim primty) \<Longrightarrow> \<exists>i. v = LitV (C i)"
          "\<And> i. type_of_val A (LitV (C i)) = Some (TPrim primty)"
  shows "A,\<Gamma>,\<Omega> \<turnstile> \<langle>Exists (TPrim primty) e, ns\<rangle> \<Down> LitV (LBool (\<exists>i. P i))"
proof (cases "\<exists>i. P i")
  case True
  from this obtain z where "P z" by auto
  have "A,\<Gamma>,\<Omega> \<turnstile> \<langle>Exists (TPrim primty) e, ns\<rangle> \<Down> LitV (LBool True)"
    apply (rule RedExistsTrue[where ?v = "LitV (C z)"])
    apply simp
    using assms(3) apply auto[1]
    using assms \<open>P z\<close> by (metis (full_types))     
  thus ?thesis by (simp add: True)
next
  case False
  thus ?thesis using assms by (fastforce intro: RedExistsFalse)
qed

lemma forall_vc_type:
  assumes "\<And> i. type_of_val A i = Some (instantiate \<Omega> ty) \<Longrightarrow> A,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ext_env ns i\<rangle> \<Down> BoolV (P i)"
  assumes "\<And> i. \<not> (P i) \<Longrightarrow> type_of_val A i = Some (instantiate \<Omega> ty)"
  shows "A,\<Gamma>,\<Omega> \<turnstile> \<langle>Forall ty e, ns\<rangle> \<Down> LitV (LBool (\<forall>i. P i))"
proof (cases "\<forall>i. P i")
  case True
  then show ?thesis 
    apply simp
    apply rule
    using True assms(1) by simp
next
  case False
  from this obtain z where "\<not>(P z)" by auto
  hence zType:"type_of_val A z = Some (instantiate \<Omega> ty)" using assms(2) by auto
  from False have "(\<forall>i. P i) = False" by simp
  then show ?thesis 
    apply (subst False)
    apply (rule RedForAllFalse[where ?v=z])
     apply (rule assms(2)[OF \<open>\<not>(P z)\<close>])
    using assms(1) zType \<open>\<not>(P z)\<close> by fastforce  
qed

lemma forall_vc_rel_int: 
  assumes "\<And> i. A,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ext_env ns (LitV (LInt i))\<rangle> \<Down> LitV (LBool (P i))"
  shows  "A,\<Gamma>,\<Omega> \<turnstile> \<langle>Forall (TPrim TInt) e, ns\<rangle> \<Down> LitV (LBool (\<forall>i. P i))"
  using assms
  by (rule forall_vc_rel_general, auto elim: type_of_val_int_elim)

lemma forall_vc_rel_bool: 
  assumes "\<And> b. A,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ext_env ns (LitV (LBool b))\<rangle> \<Down> LitV (LBool (P b))"
  shows  "A,\<Gamma>,\<Omega> \<turnstile> \<langle>Forall (TPrim TBool) e, ns\<rangle> \<Down> LitV (LBool (\<forall>b. P b))"
  using assms
  by (rule forall_vc_rel_general, auto elim: type_of_val_bool_elim)

lemma exists_vc_rel_int:
  assumes "\<And> i. A,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ext_env ns (LitV (LInt i))\<rangle> \<Down> LitV (LBool (P i))"
  shows "A,\<Gamma>,\<Omega> \<turnstile> \<langle>Exists (TPrim TInt) e, ns\<rangle> \<Down> LitV (LBool (\<exists>i. P i))"
  using assms
  by (rule exists_vc_rel_general, auto elim: type_of_val_int_elim)

lemma exists_vc_rel_bool:
  assumes "\<And> b. A,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ext_env ns (LitV (LBool b))\<rangle> \<Down> LitV (LBool (P b))"
  shows "A,\<Gamma>,\<Omega> \<turnstile> \<langle>Exists (TPrim TBool) e, ns\<rangle> \<Down> LitV (LBool (\<exists>b. P b))"
  using assms
  by (rule exists_vc_rel_general, auto elim: type_of_val_bool_elim)


(* Helper functions *)
fun vc_val_to_type :: "(('a)absval_ty_fun) \<Rightarrow> 'a val \<Rightarrow> ty"
  where
   "vc_val_to_type A v = (case (type_of_val A v) of Some t \<Rightarrow> t | None \<Rightarrow> TPrim TInt)"

fun vc_inv :: "nat \<Rightarrow> ty \<Rightarrow> ty"
  where
   "vc_inv n (TCon tcon_id xs) = (if n < length xs then xs ! n else TPrim (TInt))" 
 | "vc_inv n _ = TPrim (TInt)"

(* Type constructor functions *)
fun vc_type_constr1 :: "string \<Rightarrow> ty \<Rightarrow> ty"
  where
   "vc_type_constr1 s t = TCon s [t]"

fun vc_type_constr2 :: "string \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty"
  where
   "vc_type_constr2 s t1 t2 = TCon s [t1,t2]"

fun vc_type_constr3 :: "string \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty"
  where
   "vc_type_constr3 s t1 t2 t3 = TCon s [t1,t2,t3]"

fun vc_type_constr4 :: "string \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty"
  where
   "vc_type_constr4 s t1 t2 t3 t4 = TCon s [t1,t2,t3,t4]"

fun vc_type_constr5 :: "string \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty"
  where
   "vc_type_constr5 s t1 t2 t3 t4 t5 = TCon s [t1,t2,t3,t4,t5]"

(* Conversions *)
fun convert_val_to_int :: "'a val \<Rightarrow> int"
  where "convert_val_to_int (LitV (LInt i)) = i"
  |  "convert_val_to_int _ = undefined"

fun convert_val_to_bool :: "'a val \<Rightarrow> bool"
  where "convert_val_to_bool (LitV (LBool b)) = b"
  | "convert_val_to_bool _ = undefined"

lemma tint_intv: "\<lbrakk> type_of_val A v = Some (TPrim TInt) \<rbrakk> \<Longrightarrow> \<exists>i. v = LitV (LInt i)"
  by (auto elim: type_of_val_int_elim)

lemma tbool_boolv: "\<lbrakk> type_of_val A v = Some (TPrim TBool) \<rbrakk> \<Longrightarrow> \<exists>b. v = LitV (LBool b)"
  by (auto elim: type_of_val_bool_elim)

end