theory VCExprHelper
imports Semantics Util
begin

lemma vc_to_expr:"\<lbrakk>vc; \<Gamma> \<turnstile> \<langle>e,ns\<rangle> \<Down> (BoolV vc)\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<langle>e,ns\<rangle> \<Down> (BoolV True)"
  by simp

lemma expr_to_vc:"\<lbrakk>\<Gamma> \<turnstile> \<langle>e, ns\<rangle> \<Down> BoolV (True); \<Gamma> \<turnstile> \<langle>e, ns\<rangle> \<Down> (BoolV vc)\<rbrakk> \<Longrightarrow> vc"
  by (blast dest: expr_eval_determ)

(* boolean operations *)
lemma conj_vc_rel: 
  assumes "\<Gamma> \<turnstile> \<langle>e1, ns\<rangle> \<Down> BoolV (vc1)" and "\<Gamma> \<turnstile> \<langle>e2, ns\<rangle> \<Down> BoolV (vc2)"
  shows "\<Gamma> \<turnstile> \<langle>e1 \<guillemotleft>And\<guillemotright> e2, ns\<rangle> \<Down> BoolV (vc1 \<and> vc2)"
  using assms
  by (auto intro: RedBinOp)

lemma disj_vc_rel: 
  assumes "\<Gamma> \<turnstile> \<langle>e1, ns\<rangle> \<Down> BoolV (vc1)" and "\<Gamma> \<turnstile> \<langle>e2, ns\<rangle> \<Down> BoolV (vc2)"
  shows "\<Gamma> \<turnstile> \<langle>e1 \<guillemotleft>Or\<guillemotright> e2, ns\<rangle> \<Down> BoolV (vc1 \<or> vc2)"
  using assms
  by (auto intro: RedBinOp)

lemma imp_vc_rel: 
  assumes "\<Gamma> \<turnstile> \<langle>e1, ns\<rangle> \<Down> BoolV (vc1)" and "\<Gamma> \<turnstile> \<langle>e2, ns\<rangle> \<Down> BoolV (vc2)"
  shows "\<Gamma> \<turnstile> \<langle>e1 \<guillemotleft>Imp\<guillemotright> e2, ns\<rangle> \<Down> BoolV (vc1 \<longrightarrow> vc2)"
  using assms
  by (auto intro: RedBinOp)

lemma not_vc_rel:
  assumes "\<Gamma> \<turnstile> \<langle>e, ns\<rangle> \<Down> BoolV (vc)"
  shows "\<Gamma> \<turnstile> \<langle>UnOp Not e, ns\<rangle> \<Down> BoolV (\<not> vc)"
  using assms
  by (auto intro: RedUnOp)

(* integer operations *)
lemma add_vc_rel: 
  assumes "\<Gamma> \<turnstile> \<langle>e1, ns\<rangle> \<Down> IntV (vc1)" and "\<Gamma> \<turnstile> \<langle>e2, ns\<rangle> \<Down> IntV (vc2)"
  shows "\<Gamma> \<turnstile> \<langle>e1 \<guillemotleft>Add\<guillemotright> e2, ns\<rangle> \<Down> IntV (vc1 + vc2)"
  using assms
  by (auto intro: RedBinOp)

lemma sub_vc_rel: 
  assumes "\<Gamma> \<turnstile> \<langle>e1, ns\<rangle> \<Down> IntV (vc1)" and "\<Gamma> \<turnstile> \<langle>e2, ns\<rangle> \<Down> IntV (vc2)"
  shows "\<Gamma> \<turnstile> \<langle>e1 \<guillemotleft>Sub\<guillemotright> e2, ns\<rangle> \<Down> IntV (vc1 - vc2)"
  using assms
  by (auto intro: RedBinOp)

lemma mul_vc_rel: 
  assumes "\<Gamma> \<turnstile> \<langle>e1, ns\<rangle> \<Down> IntV (vc1)" and "\<Gamma> \<turnstile> \<langle>e2, ns\<rangle> \<Down> IntV (vc2)"
  shows "\<Gamma> \<turnstile> \<langle>e1 \<guillemotleft>Mul\<guillemotright> e2, ns\<rangle> \<Down> IntV (vc1 * vc2)"
  using assms
  by (auto intro: RedBinOp)

lemma uminus_vc_rel:
  assumes "\<Gamma> \<turnstile> \<langle>e, ns\<rangle> \<Down> IntV (vc)"
  shows "\<Gamma> \<turnstile> \<langle>UnOp UMinus e, ns\<rangle> \<Down> IntV (- vc)"
  using assms
  by (auto intro: RedUnOp)

(* quantifiers *)
lemma forall_vc_rel_general: 
  assumes "\<And> i. \<Gamma> \<turnstile> \<langle>eopen 0 (Val (C i)) e, ns\<rangle> \<Down> BoolV (P i)" and
          "\<And> i v. type_of_val v = ty \<Longrightarrow> \<exists>i. v = (C i)"
          "\<And> i. type_of_val (C i) = ty"
  shows  "\<Gamma> \<turnstile> \<langle>Forall ty e, ns\<rangle> \<Down> BoolV (\<forall>i. P i)"
proof (cases "(\<forall>i. P i)")
  case True
  thus ?thesis using assms by (fastforce intro: RedForAllTrue)
next
  case False
  from this obtain z where "\<not>(P z)" by auto
  have "\<Gamma> \<turnstile> \<langle>Forall ty e, ns\<rangle> \<Down> BoolV False"
    apply (rule RedForAllFalse[where ?v = "C z"])
    apply (simp only: assms)
    by (metis (full_types) \<open>\<not> P z\<close> assms(1))
  then show ?thesis by (simp add: False)
qed

lemma exists_vc_rel_general:
  assumes "\<And> i. \<Gamma> \<turnstile> \<langle>eopen 0 (Val (C i)) e, ns\<rangle> \<Down> BoolV (P i)"
          "\<And> i v. type_of_val v = ty \<Longrightarrow> \<exists>i. v = (C i)"
          "\<And> i. type_of_val (C i) = ty"
  shows "\<Gamma> \<turnstile> \<langle>Exists ty e, ns\<rangle> \<Down> BoolV (\<exists>i. P i)"
proof (cases "\<exists>i. P i")
  case True
  from this obtain z where "P z" by auto
  have "\<Gamma> \<turnstile> \<langle>Exists ty e, ns\<rangle> \<Down> BoolV True"
    apply (rule RedExistsTrue[where ?v = "C z"])
     apply (simp only: assms)
    using assms \<open>P z\<close> by (metis (full_types))     
  thus ?thesis by (simp add: True)
next
  case False
  thus ?thesis using assms by (fastforce intro: RedExistsFalse)
qed

lemma forall_vc_rel_int: 
  assumes "\<And> i. \<Gamma> \<turnstile> \<langle>eopen 0 (Val (IntV i)) e, ns\<rangle> \<Down> BoolV (P i)"
  shows  "\<Gamma> \<turnstile> \<langle>Forall TInt e, ns\<rangle> \<Down> BoolV (\<forall>i. P i)"
  using assms
  by (rule forall_vc_rel_general, auto elim: type_of_val_int_elim)

lemma forall_vc_rel_bool: 
  assumes "\<And> b. \<Gamma> \<turnstile> \<langle>eopen 0 (Val (BoolV b)) e, ns\<rangle> \<Down> BoolV (P b)"
  shows  "\<Gamma> \<turnstile> \<langle>Forall TBool e, ns\<rangle> \<Down> BoolV (\<forall>b. P b)"
  using assms
  by (rule forall_vc_rel_general, auto elim: type_of_val_bool_elim)

lemma exists_vc_rel_int:
  assumes "\<And> i. \<Gamma> \<turnstile> \<langle>eopen 0 (Val (IntV i)) e, ns\<rangle> \<Down> BoolV (P i)"
  shows "\<Gamma> \<turnstile> \<langle>Exists TInt e, ns\<rangle> \<Down> BoolV (\<exists>i. P i)"
  using assms
  by (rule exists_vc_rel_general, auto elim: type_of_val_int_elim)

lemma exists_vc_rel_bool:
  assumes "\<And> b. \<Gamma> \<turnstile> \<langle>eopen 0 (Val (BoolV b)) e, ns\<rangle> \<Down> BoolV (P b)"
  shows "\<Gamma> \<turnstile> \<langle>Exists TBool e, ns\<rangle> \<Down> BoolV (\<exists>b. P b)"
  using assms
  by (rule exists_vc_rel_general, auto elim: type_of_val_bool_elim)

(* Conversions *)
fun convert_val_to_int :: "val \<Rightarrow> int"
  where "convert_val_to_int (IntV i) = i"
  |  "convert_val_to_int _ = undefined"

fun convert_val_to_bool :: "val \<Rightarrow> bool"
  where "convert_val_to_bool (BoolV b) = b"
  | "convert_val_to_bool _ = undefined"

lemma tint_intv: "\<lbrakk> type_of_val v = TInt \<rbrakk> \<Longrightarrow> \<exists>i. v = IntV i"
  by (auto elim: type_of_val_int_elim)

lemma tbool_boolv: "\<lbrakk> type_of_val v = TBool \<rbrakk> \<Longrightarrow> \<exists>i. v = BoolV i"
  by (auto elim: type_of_val_bool_elim)


end