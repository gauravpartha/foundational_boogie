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
          "\<And> i v. ty_val_rel A v (TPrim primty) \<Longrightarrow> \<exists>i. v = LitV (C i)"
          "\<And> i. ty_val_rel A (LitV (C i)) (TPrim primty)"
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
          "\<And> i v. ty_val_rel A v (TPrim primty) \<Longrightarrow> \<exists>i. v = LitV (C i)"
          "\<And> i. ty_val_rel A (LitV (C i)) (TPrim primty)"
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

(* Conversions *)
fun convert_val_to_int :: "'a val \<Rightarrow> int"
  where "convert_val_to_int (LitV (LInt i)) = i"
  |  "convert_val_to_int _ = undefined"

fun convert_val_to_bool :: "'a val \<Rightarrow> bool"
  where "convert_val_to_bool (LitV (LBool b)) = b"
  | "convert_val_to_bool _ = undefined"

lemma tint_intv: "\<lbrakk> ty_val_rel A v (TPrim TInt) \<rbrakk> \<Longrightarrow> \<exists>i. v = LitV (LInt i)"
  by (auto elim: type_of_val_int_elim)

lemma tbool_boolv: "\<lbrakk> ty_val_rel A v (TPrim TBool) \<rbrakk> \<Longrightarrow> \<exists>b. v = LitV (LBool b)"
  by (auto elim: type_of_val_bool_elim)

end