theory VCExprHelper
imports Semantics Util
begin

lemma vc_to_expr:"\<lbrakk>vc; A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e,ns\<rangle> \<Down> LitV (LBool vc)\<rbrakk> \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e,ns\<rangle> \<Down> LitV (LBool True)"
  by simp

lemma expr_to_vc:"\<lbrakk>A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns\<rangle> \<Down> LitV (LBool True); A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns\<rangle> \<Down> LitV (LBool vc)\<rbrakk> \<Longrightarrow> vc"
  by (blast dest: expr_eval_determ)

(* equality *)
lemma eq_bool_vc_rel:
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> BoolV vc1" and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> BoolV vc2"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1 \<guillemotleft>Eq\<guillemotright> e2, ns\<rangle> \<Down> BoolV (vc1 = vc2)"
  using assms
  by (auto intro: RedBinOp)

lemma eq_int_vc_rel:
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> IntV vc1" and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> IntV vc2"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1 \<guillemotleft>Eq\<guillemotright> e2, ns\<rangle> \<Down> BoolV (vc1 = vc2)"
  using assms
  by (auto intro: RedBinOp)

lemma eq_abs_vc_rel:
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> vc1" and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> vc2"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1 \<guillemotleft>Eq\<guillemotright> e2, ns\<rangle> \<Down> BoolV (vc1 = vc2)"
  using assms
  by (auto intro: RedBinOp)

(* boolean operations *)
lemma conj_vc_rel: 
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> LitV (LBool vc1)" and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> LitV (LBool vc2)"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1 \<guillemotleft>And\<guillemotright> e2, ns\<rangle> \<Down> LitV (LBool (vc1 \<and> vc2))"
  using assms
  by (auto intro: RedBinOp)

lemma disj_vc_rel: 
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> LitV (LBool vc1)" and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> LitV (LBool vc2)"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1 \<guillemotleft>Or\<guillemotright> e2, ns\<rangle> \<Down> LitV (LBool (vc1 \<or> vc2))"
  using assms
  by (auto intro: RedBinOp)

lemma imp_vc_rel: 
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> LitV (LBool vc1)" and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> LitV (LBool vc2)"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1 \<guillemotleft>Imp\<guillemotright> e2, ns\<rangle> \<Down> LitV (LBool (vc1 \<longrightarrow> vc2))"
  using assms
  by (auto intro: RedBinOp)

lemma not_vc_rel:
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns\<rangle> \<Down> LitV (LBool vc)"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp Not e, ns\<rangle> \<Down> LitV (LBool (\<not> vc))"
  using assms
  by (auto intro: RedUnOp)

(* integer operations *)
lemma add_vc_rel: 
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> LitV (LInt vc1)" and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> LitV (LInt vc2)"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1 \<guillemotleft>Add\<guillemotright> e2, ns\<rangle> \<Down> LitV (LInt (vc1 + vc2))"
  using assms
  by (auto intro: RedBinOp)

lemma sub_vc_rel: 
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> LitV (LInt (vc1))" and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> LitV (LInt vc2)"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1 \<guillemotleft>Sub\<guillemotright> e2, ns\<rangle> \<Down> LitV (LInt (vc1 - vc2))"
  using assms
  by (auto intro: RedBinOp)

lemma mul_vc_rel: 
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1, ns\<rangle> \<Down> LitV (LInt vc1)" and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e2, ns\<rangle> \<Down> LitV (LInt vc2)"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e1 \<guillemotleft>Mul\<guillemotright> e2, ns\<rangle> \<Down> LitV (LInt (vc1 * vc2))"
  using assms
  by (auto intro: RedBinOp)

lemma uminus_vc_rel:
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns\<rangle> \<Down> LitV (LInt vc)"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp UMinus e, ns\<rangle> \<Down> LitV (LInt (- vc))"
  using assms
  by (auto intro: RedUnOp)

datatype closed_ty = 
  TPrimC prim_ty | TConC tcon_id "closed_ty list"

fun ty_to_closed :: "ty \<Rightarrow> closed_ty"
  where 
    "ty_to_closed (TPrim t) = TPrimC t"
 |  "ty_to_closed (TCon tcon_id ts) = TConC tcon_id (map ty_to_closed ts)"
 |  "ty_to_closed (TVar v) =  undefined"

fun closed_to_ty :: "closed_ty \<Rightarrow> ty"
  where 
    "closed_to_ty (TPrimC t) = TPrim t"
 |  "closed_to_ty (TConC tcon_id ts) = TCon tcon_id (map closed_to_ty ts)"

lemma closed_closed_to_ty: "closed (closed_to_ty t)"
  by (induction t) (auto simp: list.pred_set)

lemma closed_inv1: "ty_to_closed (closed_to_ty t) = t"
  by (induction t) (auto simp: map_idI)

lemma closed_inv2: "closed t \<Longrightarrow> closed_to_ty (ty_to_closed t) = t"
  by (induction t) (auto simp add: list.pred_set map_idI)

lemma closed_inv2_2: "closed t \<Longrightarrow> t = closed_to_ty (ty_to_closed t)"
  by (induction t) (auto simp add: list.pred_set map_idI)


lemma type_definition_closed_ty:
 "type_definition closed_to_ty ty_to_closed {t. closed t}"
  by standard (auto simp add: closed_closed_to_ty closed_inv1 closed_inv2)

setup_lifting type_definition_closed_ty

text\<open>instantiation of type function\<close>
fun vc_type_of_val :: "(('a)absval_ty_fun) \<Rightarrow> 'a val \<Rightarrow> closed_ty"
  where
   "vc_type_of_val A v = ty_to_closed (type_of_val A v)"

lemma vc_type_of_val_int: "vc_type_of_val A (IntV i) = TPrimC TInt"
  by simp

lemma vc_type_of_val_bool: "vc_type_of_val A (IntV i) = TPrimC TInt"
  by simp

text\<open>Return some arbitrary value of correct type\<close>

fun val_of_type :: "'a absval_ty_fun \<Rightarrow> ty \<Rightarrow> 'a val"
  where
   "val_of_type A t = (SOME v. type_of_val A v = t)"

definition val_of_closed_type ::"'a absval_ty_fun \<Rightarrow> closed_ty \<Rightarrow> 'a val"
  where
   "val_of_closed_type A t  = (val_of_type A (closed_to_ty t))"

lemma val_of_type_correct:
  assumes "\<And> t. closed t \<Longrightarrow> \<exists>v. type_of_val A v = t" and
         "closed t'"
  shows "type_of_val A (val_of_type A t') = t'"
  by (metis (mono_tags, lifting) assms(1) assms(2) someI val_of_type.simps)

lemma val_of_closed_type_correct: 
  assumes "\<And> t. closed t \<Longrightarrow> \<exists>v. type_of_val A v = t"
  shows "ty_to_closed (type_of_val A (val_of_closed_type A ct)) = ct"
  by (metis assms closed_closed_to_ty closed_inv1 val_of_closed_type_def val_of_type_correct)

(* quantifiers *)
lemma type_of_val_instantiate:
assumes "closed (instantiate \<Omega> ty)" and
        "closed (type_of_val A v)" and
        "ty_to_closed (type_of_val A v) = ty_to_closed (instantiate \<Omega> ty)"
shows "(type_of_val A v) = (instantiate \<Omega> ty)"
  by (metis assms(1) assms(2) assms(3) closed_inv2)

(* lifted implication simplification *)
lemma imp_vc:
assumes "vc0" and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns\<rangle> \<Down> BoolV vc"
shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, ns\<rangle> \<Down> BoolV (vc0 \<longrightarrow> vc)"
using assms
  by simp

(* Value quantification relation *)

(** primitive types **)
lemma forall_vc_rel_general: 
  assumes "\<And> i. A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, full_ext_env ns (LitV (C i))\<rangle> \<Down> LitV (LBool (P i))" and
          "\<And> i v. type_of_val A v = TPrim primty \<Longrightarrow> \<exists>i. v = LitV (C i)"
          "\<And> i. type_of_val A (LitV (C i)) = TPrim primty"
  shows  "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Forall (TPrim primty) e, ns\<rangle> \<Down> LitV (LBool (\<forall>i. P i))"
proof (cases "(\<forall>i. P i)")
  case True
  thus ?thesis using assms by (fastforce intro: RedForAllTrue)
next
  case False
  from this obtain z where "\<not>(P z)" by auto
  have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Forall (TPrim primty) e, ns\<rangle> \<Down> LitV (LBool False)"
    apply (rule RedForAllFalse[where ?v = "LitV (C z)"])
    apply simp
    using assms(3) apply auto[1]
    by (metis (full_types) \<open>\<not> P z\<close> assms(1))
  then show ?thesis by (simp add: False)
qed

lemma exists_vc_rel_general:
  assumes "\<And> i. A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, full_ext_env ns (LitV (C i))\<rangle> \<Down> LitV (LBool (P i))"
          "\<And> i v. type_of_val A v = TPrim primty \<Longrightarrow> \<exists>i. v = LitV (C i)"
          "\<And> i. type_of_val A (LitV (C i)) = TPrim primty"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Exists (TPrim primty) e, ns\<rangle> \<Down> LitV (LBool (\<exists>i. P i))"
proof (cases "\<exists>i. P i")
  case True
  from this obtain z where "P z" by auto
  have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Exists (TPrim primty) e, ns\<rangle> \<Down> LitV (LBool True)"
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
  assumes "\<And> i. A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, full_ext_env ns (LitV (LInt i))\<rangle> \<Down> LitV (LBool (P i))"
  shows  "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Forall (TPrim TInt) e, ns\<rangle> \<Down> LitV (LBool (\<forall>i. P i))"
  using assms
  by (rule forall_vc_rel_general, auto elim: type_of_val_int_elim)

lemma forall_vc_rel_bool: 
  assumes "\<And> b. A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, full_ext_env ns (LitV (LBool b))\<rangle> \<Down> LitV (LBool (P b))"
  shows  "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Forall (TPrim TBool) e, ns\<rangle> \<Down> LitV (LBool (\<forall>b. P b))"
  using assms
  by (rule forall_vc_rel_general, auto elim: type_of_val_bool_elim)

lemma exists_vc_rel_int:
  assumes "\<And> i. A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, full_ext_env ns (LitV (LInt i))\<rangle> \<Down> LitV (LBool (P i))"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Exists (TPrim TInt) e, ns\<rangle> \<Down> LitV (LBool (\<exists>i. P i))"
  using assms
  by (rule exists_vc_rel_general, auto elim: type_of_val_int_elim)

lemma exists_vc_rel_bool:
  assumes "\<And> b. A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, full_ext_env ns (LitV (LBool b))\<rangle> \<Down> LitV (LBool (P b))"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Exists (TPrim TBool) e, ns\<rangle> \<Down> LitV (LBool (\<exists>b. P b))"
  using assms
  by (rule exists_vc_rel_general, auto elim: type_of_val_bool_elim)

(** general types **)

lemma forall_vc_type:
  assumes closedTypeOfVal:"\<And> v. closed (type_of_val A v)" and
   closedInstTy:"closed (instantiate \<Omega> ty)" and
   vcTypeFalse:"\<And> i. \<not> (P i) \<Longrightarrow> vc_type_of_val A i = ty_to_closed (instantiate \<Omega> ty)" and
   body: "\<And> i. type_of_val A i = instantiate \<Omega> ty \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, full_ext_env ns i\<rangle> \<Down> BoolV (P i)"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Forall ty e, ns\<rangle> \<Down> LitV (LBool (\<forall>i. P i))"
proof (cases "\<forall>i. P i")
  case True
  then show ?thesis
    apply simp
    apply rule
    using True body by simp
next
  case False
  from this obtain z where "\<not>(P z)" by auto
  hence "vc_type_of_val A z = ty_to_closed (instantiate \<Omega> ty)" using vcTypeFalse by auto
  hence zType:"type_of_val A z  = instantiate \<Omega> ty" by (metis closedTypeOfVal closedInstTy closed_inv2 vc_type_of_val.simps)
  thus ?thesis
    apply (subst False)
    apply (rule RedForAllFalse[OF zType])
    using \<open>\<not> P z\<close> body by fastforce
qed

lemma exists_vc_type:
  assumes closedTypeOfVal:"\<And> v. closed (type_of_val A v)" and
   closedInstTy:"closed (instantiate \<Omega> ty)" and
   vcTypeTrue:"\<And> i. (P i) \<Longrightarrow> vc_type_of_val A i = ty_to_closed (instantiate \<Omega> ty)" and
   body: "\<And> i. type_of_val A i = instantiate \<Omega> ty \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>e, full_ext_env ns i\<rangle> \<Down> BoolV (P i)"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>Exists ty e, ns\<rangle> \<Down> LitV (LBool (\<exists>i. P i))"
proof (cases "\<exists>i. P i")
  case True
  from this obtain z where "P z" by auto
  hence witnessType:"type_of_val A z = instantiate \<Omega> ty" using vcTypeTrue
    by (simp add: closedInstTy closedTypeOfVal type_of_val_instantiate) 
  then show ?thesis
    apply (subst True)
    apply rule
     apply (rule witnessType)
    using \<open>P z\<close> body by fastforce    
next
  case False
  hence False2: "(\<exists>i. P i) = False" by simp
  show ?thesis
    apply (subst False2)
    apply rule
    using body False by simp
qed

(* Type quantification relation *)
lemma forallt_vc:
assumes "\<And>\<tau>. closed \<tau> \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<tau>#\<Omega> \<turnstile> \<langle>e,ns\<rangle> \<Down> BoolV (P (ty_to_closed \<tau>))"
shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>ForallT e, ns\<rangle> \<Down> BoolV (\<forall>t :: closed_ty. P t)"
proof (cases "\<forall>t :: closed_ty. P t")
  case True
  then show ?thesis 
    apply (subst True)
    apply simp
    apply rule
    using assms by auto
next
  case False
  from this obtain \<tau> where "\<not> P \<tau>" by auto
  have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>ForallT e,ns\<rangle> \<Down> BoolV False"
    apply (rule RedForallT_False[where ?\<tau>="closed_to_ty \<tau>"])
     apply (rule closed_closed_to_ty)
    by (metis (full_types) \<open>\<not> P \<tau>\<close> assms closed_closed_to_ty closed_inv1)
  thus ?thesis  by (simp add: \<open>\<not> (\<forall>t. P t)\<close>)
qed

lemma forallt_vc_extract:
assumes "\<And>\<tau>. closed \<tau> \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<tau>#\<Omega> \<turnstile> \<langle>e,ns\<rangle> \<Down> BoolV P"
shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>ForallT e, ns\<rangle> \<Down> BoolV P"
proof (cases P)
  case True
  thus ?thesis using assms by (auto intro: RedForallT_True)
next
  case False
  have "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>ForallT e,ns\<rangle> \<Down> BoolV False"
    apply (rule RedForallT_False[where ?\<tau>="TPrim TInt"])
     apply simp
    using False assms by auto
  thus ?thesis using \<open>\<not>P\<close> by auto
qed

(* Helper functions *)
fun vc_inv :: "nat \<Rightarrow> closed_ty \<Rightarrow> closed_ty"
  where
   "vc_inv n (TConC tcon_id xs) = (if n < length xs then xs ! n else TPrimC (TInt))" 
 | "vc_inv n _ = TPrimC (TInt)"

fun vc_inv_closed :: "nat \<Rightarrow> closed_ty \<Rightarrow> closed_ty"
  where
   "vc_inv_closed n (TConC tcon_id xs) = (if (n < length xs) then xs ! n else TPrimC (TInt))" 
 | "vc_inv_closed n _ = TPrimC (TInt)"

(* Type constructor functions *)
fun vc_type_constr0 :: "string \<Rightarrow> closed_ty"
  where
    "vc_type_constr0 s = TConC s []"

fun vc_type_constr1 :: "string \<Rightarrow> closed_ty \<Rightarrow> closed_ty"
  where
   "vc_type_constr1 s t = TConC s [t]"

fun vc_type_constr2 :: "string \<Rightarrow> closed_ty \<Rightarrow> closed_ty \<Rightarrow> closed_ty"
  where
   "vc_type_constr2 s t1 t2 = TConC s [t1,t2]"

fun vc_type_constr3 :: "string \<Rightarrow> closed_ty \<Rightarrow> closed_ty \<Rightarrow> closed_ty \<Rightarrow> closed_ty"
  where
   "vc_type_constr3 s t1 t2 t3 = TConC s [t1,t2,t3]"

fun vc_type_constr4 :: "string \<Rightarrow> closed_ty \<Rightarrow> closed_ty \<Rightarrow> closed_ty \<Rightarrow> closed_ty \<Rightarrow> closed_ty"
  where
   "vc_type_constr4 s t1 t2 t3 t4 = TConC s [t1,t2,t3,t4]"

fun vc_type_constr5 :: "string \<Rightarrow> closed_ty \<Rightarrow> closed_ty \<Rightarrow> closed_ty \<Rightarrow> closed_ty \<Rightarrow> closed_ty \<Rightarrow> closed_ty"
  where
   "vc_type_constr5 s t1 t2 t3 t4 t5 = TConC s [t1,t2,t3,t4,t5]"

(* inverse lemmas *)
lemma vc_inv_constr_10:"\<forall> t1. vc_inv_closed 0 (vc_type_constr1 s t1) = t1" by simp
lemma vc_inv_constr_20:"\<forall> t1 t2. vc_inv_closed 0 (vc_type_constr2 s t1 t2) = t1" by simp
lemma vc_inv_constr_21:"\<forall> t1 t2. vc_inv_closed 1 (vc_type_constr2 s t1 t2) = t2" by simp
lemma vc_inv_constr_30:"\<forall> t1 t2 t3. vc_inv_closed 0 (vc_type_constr3 s t1 t2 t3) = t1" by simp
lemma vc_inv_constr_31:"\<forall> t1 t2 t3. vc_inv_closed 1 (vc_type_constr3 s t1 t2 t3) = t2" by simp
lemma vc_inv_constr_32:"\<forall> t1 t2 t3. vc_inv_closed 2 (vc_type_constr3 s t1 t2 t3) = t3" by simp
lemma vc_inv_constr_40:"\<forall> t1 t2 t3 t4. vc_inv_closed 0 (vc_type_constr4 s t1 t2 t3 t4) = t1" by simp
lemma vc_inv_constr_41:"\<forall> t1 t2 t3 t4. vc_inv_closed 1 (vc_type_constr4 s t1 t2 t3 t4) = t2" by simp
lemma vc_inv_constr_42:"\<forall> t1 t2 t3 t4. vc_inv_closed 2 (vc_type_constr4 s t1 t2 t3 t4) = t3" by simp
lemma vc_inv_constr_43:"\<forall> t1 t2 t3 t4. vc_inv_closed 3 (vc_type_constr4 s t1 t2 t3 t4) = t4" by simp
lemma vc_inv_constr_50:"\<forall> t1 t2 t3 t4 t5. vc_inv_closed 0 (vc_type_constr5 s t1 t2 t3 t4 t5) = t1" by simp
lemma vc_inv_constr_51:"\<forall> t1 t2 t3 t4 t5. vc_inv_closed 1 (vc_type_constr5 s t1 t2 t3 t4 t5) = t2" by simp
lemma vc_inv_constr_52:"\<forall> t1 t2 t3 t4 t5. vc_inv_closed 2 (vc_type_constr5 s t1 t2 t3 t4 t5) = t3" by simp
lemma vc_inv_constr_53:"\<forall> t1 t2 t3 t4 t5. vc_inv_closed 3 (vc_type_constr5 s t1 t2 t3 t4 t5) = t4" by simp
lemma vc_inv_constr_54:"\<forall> t1 t2 t3 t4 t5. vc_inv_closed 4 (vc_type_constr5 s t1 t2 t3 t4 t5) = t5" by simp

text\<open>Conversions\<close>
fun convert_val_to_int :: "'a val \<Rightarrow> int"
  where "convert_val_to_int (LitV (LInt i)) = i"
  |  "convert_val_to_int _ = undefined"

fun convert_val_to_bool :: "'a val \<Rightarrow> bool"
  where "convert_val_to_bool (LitV (LBool b)) = b"
  | "convert_val_to_bool _ = undefined"

lemma tint_intv: "\<lbrakk> type_of_val A v = TPrim TInt \<rbrakk> \<Longrightarrow> \<exists>i. v = LitV (LInt i)"
  by (auto elim: type_of_val_int_elim)

lemma tbool_boolv: "\<lbrakk> type_of_val A v = TPrim TBool \<rbrakk> \<Longrightarrow> \<exists>b. v = LitV (LBool b)"
  by (auto elim: type_of_val_bool_elim)

(* cleaner proof *)
lemma vc_tint_intv: "vc_type_of_val A v = TPrimC TInt \<Longrightarrow> \<exists>i. v = IntV i"
  by (metis closed.simps(2) closed_inv2_2 closed_to_ty.simps(1) closed_ty.distinct(1) ty_to_closed.simps(2) type_of_val.elims type_of_val_int_elim vc_type_of_val.simps)

lemma vc_tbool_boolv: "vc_type_of_val A v = TPrimC TBool \<Longrightarrow> \<exists>i. v = BoolV i"
  by (metis closed.simps(2) closed_inv2_2 closed_to_ty.simps(1) closed_ty.distinct(1) ty_to_closed.simps(2) type_of_val.elims type_of_val_bool_elim vc_type_of_val.simps)

text \<open>Lemmas used for proving equivalence between VC quantifiers with and without extractors\<close>

lemmas prim_type_vc_lemmas = vc_type_of_val_int vc_type_of_val_bool vc_tint_intv vc_tbool_boolv

lemmas vc_extractor_lemmas = 
  prim_type_vc_lemmas 
  vc_inv_constr_10  
  vc_inv_constr_20 vc_inv_constr_21
  vc_inv_constr_30 vc_inv_constr_31 vc_inv_constr_32
  vc_inv_constr_40 vc_inv_constr_41 vc_inv_constr_42 vc_inv_constr_43
  vc_inv_constr_50 vc_inv_constr_51 vc_inv_constr_52 vc_inv_constr_53 vc_inv_constr_54

(* VC axioms *)
lemma int_inverse_1:"\<forall> i. convert_val_to_int (IntV i) = i"
  by simp

lemma int_inverse_2:"\<forall> v. vc_type_of_val A v = TPrimC TInt \<longrightarrow> IntV (convert_val_to_int v) = v"
proof (rule allI, rule impI)
  fix v
  assume "vc_type_of_val A v = TPrimC TInt"
  from this obtain i where "v = IntV i"
    by (metis closed.simps(2) closed_inv2 closed_to_ty.simps(1) closed_ty.distinct(1) ty_to_closed.simps(2) type_of_val.elims type_of_val_int_elim vc_type_of_val.simps) 
  thus "IntV (convert_val_to_int v) = v"
    by auto
qed

lemma bool_inverse_1:"\<forall>b. convert_val_to_bool (BoolV b) = b"
  by simp

lemma bool_inverse_2:"\<forall> v. vc_type_of_val A v = TPrimC TBool \<longrightarrow> BoolV (convert_val_to_bool v) = v"
proof (rule allI, rule impI)
  fix v
  assume "vc_type_of_val A v = TPrimC TBool"
  hence "type_of_val A v = TPrim TBool"
    by (metis closed.simps(2) closed_inv2 closed_to_ty.simps(1) closed_ty.distinct(1) ty_to_closed.simps(2) type_of_val.elims vc_type_of_val.simps) 
  from this obtain b where "v = BoolV b"
    using tbool_boolv by auto  
  thus "BoolV (convert_val_to_bool v) = v"
    by auto
qed

lemma int_type:"\<forall>b. vc_type_of_val A (IntV b) = TPrimC TInt"
  by simp

lemma bool_type:"\<forall>b. vc_type_of_val A (BoolV b) = TPrimC TBool"
  by simp

(** basic tactics **)

method fun_output_axiom uses NonEmptyTypes =
(  (simp add: Let_def),(rule allI)+, (simp split: option.split),(rule conjI), (rule impI),
  (rule val_of_closed_type_correct[OF NonEmptyTypes]), assumption, rule allI, rule impI
)


end