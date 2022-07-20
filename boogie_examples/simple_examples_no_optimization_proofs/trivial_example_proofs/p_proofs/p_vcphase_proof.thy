theory p_vcphase_proof
imports Boogie_Lang.Semantics Boogie_Lang.Util Boogie_Lang.VCHints Boogie_Lang.VCPhaseML p_passive_prog p_before_passive_prog
begin
locale vc = 
fixes f :: "(int => bool)"
begin

definition vc_anon0
  where
    "vc_anon0 a = ((f a) \<longrightarrow> (f a))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry a = (vc_anon0 a)"

end

locale passification = 
fixes A :: "(('a)absval_ty_fun)" and \<Lambda> :: "(var_context)" and \<Gamma> :: "(('a)fun_interp)" and n_s :: "(('a)nstate)" and f :: "(((ty)list) => (((('a)val)list) => ((('a)val)option)))" and vc_f :: "(int => bool)" and vc_x :: "int" and vc_a :: "int"
assumes 
G0: "((\<Gamma> ''f'') = (Some f))" and 
G1: "(\<And> farg0. ((f [] [(IntV farg0)]) = (Some (BoolV (vc_f farg0)))))" and 
G2: "((lookup_var \<Lambda> n_s 0) = (Some (IntV vc_x)))" and 
G3: "((lookup_var \<Lambda> n_s 1) = (Some (IntV vc_a)))" and 
G4: "(\<And> v. (closed ((type_of_val A) v)))"
begin

lemmas global_assms = G0 G1 G2 G3 G4
lemmas forall_poly_thm = forall_vc_type[OF G4]
lemmas exists_poly_thm = exists_vc_type[OF G4]
declare Nat.One_nat_def[simp del]

ML\<open>
val block_anon0_hints = [
(AssumeConjR 0,NONE), 
(AssertNoConj,NONE)]
\<close>
lemma block_anon0AA0:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.block_0 (Normal n_s) s') \<Longrightarrow> ((vc.vc_anon0 vc_f vc_a) \<Longrightarrow> ((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))))"
unfolding p_passive_prog.block_0_def vc.vc_anon0_def
apply (tactic \<open> boogie_vc_tac @{context} @{thms global_assms} (@{thm forall_poly_thm}, @{thm exists_poly_thm}) block_anon0_hints \<close>)
by (auto?)

lemma block_0:
assumes 
"(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.block_1 (Normal n_s) s')" and 
"(vc.vc_anon0 vc_f vc_a)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 vc_f vc_a)))))"
using assms
unfolding p_passive_prog.block_1_def
apply cases
by auto

lemma block_PreconditionGeneratedEntry:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.block_2 (Normal n_s) s') \<Longrightarrow> ((vc.vc_PreconditionGeneratedEntry vc_f vc_a) \<Longrightarrow> ((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 vc_f vc_a)))))))"
apply (erule red_cmd_list.cases)
using global_assms
unfolding p_passive_prog.block_2_def vc.vc_PreconditionGeneratedEntry_def
apply (handle_cmd_list_full?)
by (auto?)

lemma cfg_block_anon0:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.proc_body ((Inl 0),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon0 vc_f vc_a)"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step_no_succ[OF assms(1) p_passive_prog.node_0 p_passive_prog.outEdges_0])
using block_anon0AA0[OF _ assms(2)] by blast

lemma cfg_block_0:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.proc_body ((Inl 1),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon0 vc_f vc_a)"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) p_passive_prog.node_1])
apply (erule block_0[OF _ assms(2)])
apply ((simp add:p_passive_prog.outEdges_1))
apply (erule member_elim, simp)
apply (erule cfg_block_anon0, simp?)
by (simp add: member_rec(2))

lemma cfg_PreconditionGeneratedEntry:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.proc_body ((Inl 2),(Normal n_s)) (m',s'))" and 
"(vc.vc_PreconditionGeneratedEntry vc_f vc_a)"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) p_passive_prog.node_2])
apply (erule block_PreconditionGeneratedEntry[OF _ assms(2)])
apply ((simp add:p_passive_prog.outEdges_2))
apply (erule member_elim, simp)
apply (erule cfg_block_0, simp?)
by (simp add: member_rec(2))


end

locale axioms = 
fixes A :: "(('a)absval_ty_fun)" and \<Lambda> :: "(var_context)" and \<Gamma> :: "(('a)fun_interp)" and n_s :: "(('a)nstate)" and f :: "(((ty)list) => (((('a)val)list) => ((('a)val)option)))" and vc_f :: "(int => bool)"
assumes 
G0: "((\<Gamma> ''f'') = (Some f))" and 
G1: "(\<And> farg0. ((f [] [(IntV farg0)]) = (Some (BoolV (vc_f farg0)))))" and 
G2: "(\<And> v. (closed ((type_of_val A) v)))"
begin

lemmas global_assms = G0 G1 G2
lemmas forall_poly_thm = forall_vc_type[OF G2]
lemmas exists_poly_thm = exists_vc_type[OF G2]
declare Nat.One_nat_def[simp del]


end

fun vc_fun_f
  where
    "vc_fun_f A f x = (case (f [] [(IntV x)]) of 
(Some res) \<Rightarrow> (convert_val_to_bool res)
|(None ) \<Rightarrow> (convert_val_to_bool (val_of_closed_type A (TPrimC TBool)))
)"
lemma vc_f_corres:
assumes 
FInterp: "(fun_interp_single_wf A (0,[(TPrim TInt)],(TPrim TBool)) f)"
shows "((f [] [(IntV x)]) = (Some (BoolV (vc_fun_f A f x))))"
proof -
from  FInterp obtain z where W:"((f [] [(IntV x)]) = (Some (BoolV z)))"
  apply (simp only: fun_interp_single_wf.simps) 
  apply (erule allE[where ?x="[]"])
  apply (simp add: )
  apply (erule allE[where ?x="[(IntV x)]"])?
using tbool_boolv by auto
from this  show ?thesis 
by (simp add: W) qed

definition ctor_list
  where
    "ctor_list  = []"
fun ctor :: "((closed_ty) => int)"
  where
    "ctor (TConC s _) = (the (map_of ctor_list s))"
declare One_nat_def[simp del]

lemma end_to_end:
assumes 
Red: "(red_cfg_multi A M ((append p_before_ast_to_cfg_prog.constants_vdecls p_before_ast_to_cfg_prog.globals_vdecls),(append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls)) \<Gamma> [] p_passive_prog.proc_body ((Inl 2),(Normal n_s)) (m',s'))" and 
VC: "(\<And> (vc_x::int) (vc_a::int) (vc_f::(int => bool)). (vc.vc_PreconditionGeneratedEntry vc_f vc_a))" and 
Closed: "(\<And> v. (closed ((type_of_val A) v)))" and 
NonEmptyTypes: "(\<And> t. ((closed t) \<Longrightarrow> (\<exists> v. (((type_of_val A) v) = t))))" and 
FInterp: "(fun_interp_wf A p_before_ast_to_cfg_prog.fdecls \<Gamma>)" and 
Axioms: "(axiom_assm A \<Gamma> p_before_ast_to_cfg_prog.constants_vdecls (n_s::(('a)nstate)) p_before_ast_to_cfg_prog.axioms)" and 
ParamsLocal: "(state_typ_wf A [] (local_state n_s) (append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls))" and 
ConstsGlobal: "(state_typ_wf A [] (global_state n_s) (append p_before_ast_to_cfg_prog.constants_vdecls p_before_ast_to_cfg_prog.globals_vdecls))"
shows "(s' \<noteq> Failure)"
proof -
let ?n_s_c = "(nstate_global_restriction n_s p_before_ast_to_cfg_prog.constants_vdecls)"
let ?\<Lambda> = "((append p_before_ast_to_cfg_prog.constants_vdecls p_before_ast_to_cfg_prog.globals_vdecls),(append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls))"
let ?\<Lambda>c = "((p_before_ast_to_cfg_prog.constants_vdecls,[])::(var_context))"
let ?f = "opaque_comp the \<Gamma> ''f''"
have im_f:"((\<Gamma> ''f'') = (Some ?f))"
apply (simp only:opaque_comp_def)
by (rule finterp_member[OF FInterp p_before_ast_to_cfg_prog.mfun_f])
from ParamsLocal have sc_x:"(((lookup_var ?\<Lambda> n_s 0) = (Some (IntV (convert_val_to_int (the (lookup_var ?\<Lambda> n_s 0)))))) \<and> (((type_of_val A) (the (lookup_var ?\<Lambda> n_s 0))) = (TPrim TInt)))"
apply (simp only:state_typ_wf_def)
apply (erule allE, erule allE, erule impE, rule map_of_lookup_vdecls_ty[OF p_passive_prog.m_x])
apply (subst lookup_var_local[OF p_passive_prog.m_x])+
by (fastforce dest: tint_intv tbool_boolv)
from ParamsLocal have sc_a:"(((lookup_var ?\<Lambda> n_s 1) = (Some (IntV (convert_val_to_int (the (lookup_var ?\<Lambda> n_s 1)))))) \<and> (((type_of_val A) (the (lookup_var ?\<Lambda> n_s 1))) = (TPrim TInt)))"
apply (simp only:state_typ_wf_def)
apply (erule allE, erule allE, erule impE, rule map_of_lookup_vdecls_ty[OF p_passive_prog.m_a])
apply (subst lookup_var_local[OF p_passive_prog.m_a])+
by (fastforce dest: tint_intv tbool_boolv)
show "(s' \<noteq> Failure)"
apply (rule passification.cfg_PreconditionGeneratedEntry[OF _ Red])
apply (simp only:passification_def)
apply (intro conjI)?
apply (simp add:im_f)
apply ((rule allI | rule impI)+)?
apply ((tactic \<open> vc_fun_corres_tac @{context} @{thm vc_f_corres} @{thm FInterp} @{thm p_before_ast_to_cfg_prog.mfun_f} @{thm im_f} 1\<close>))
apply (rule HOL.conjunct1[OF sc_x])
apply (rule HOL.conjunct1[OF sc_a])
apply (simp add:Closed)
apply (rule VC)
done
qed



end
