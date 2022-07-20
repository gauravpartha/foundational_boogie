theory p_vcphase_proof
imports Boogie_Lang.Semantics Boogie_Lang.Util Boogie_Lang.VCHints Boogie_Lang.VCPhaseML p_passive_prog p_before_passive_prog
begin
locale vc
begin

definition vc_anon3_LoopBody
  where
    "vc_anon3_LoopBody  = (((0::int) > (0::int)) \<longrightarrow> ((0::int) \<ge> (0::int)))"
definition vc_anon2
  where
    "vc_anon2  = ((0::int) = (0::int))"
definition vc_anon3_LoopDone
  where
    "vc_anon3_LoopDone  = (((0::int) \<ge> (0::int)) \<longrightarrow> (vc_anon2 ))"
definition vc_anon3_LoopHead
  where
    "vc_anon3_LoopHead  = (((0::int) \<ge> (0::int)) \<longrightarrow> ((vc_anon3_LoopDone ) \<and> (vc_anon3_LoopBody )))"
definition vc_anon0
  where
    "vc_anon0  = (((0::int) \<ge> (0::int)) \<and> (((0::int) \<ge> (0::int)) \<longrightarrow> (vc_anon3_LoopHead )))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry  = (vc_anon0 )"

end

locale passification = 
fixes A :: "(('a)absval_ty_fun)" and \<Lambda> :: "(var_context)" and \<Gamma> :: "(('a)fun_interp)" and n_s :: "(('a)nstate)" and vc_x :: "int"
assumes 
G0: "((lookup_var \<Lambda> n_s 0) = (Some (IntV vc_x)))" and 
G1: "(\<And> v. (closed ((type_of_val A) v)))"
begin

lemmas global_assms = G0 G1
lemmas forall_poly_thm = forall_vc_type[OF G1]
lemmas exists_poly_thm = exists_vc_type[OF G1]
declare Nat.One_nat_def[simp del]

lemma block_GeneratedUnifiedExit:
assumes 
"(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.block_0 (Normal n_s) s')"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms
unfolding p_passive_prog.block_0_def
apply cases
by auto

ML\<open>
val block_anon3_LoopBody_hints = [
(AssumeConjR 0,NONE), 
(AssertNoConj,NONE), 
(AssumeFalse,NONE)]
\<close>
lemma block_anon3_LoopBodyAA0:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.block_1 (Normal n_s) s') \<Longrightarrow> ((vc.vc_anon3_LoopBody ) \<Longrightarrow> (s' = Magic)))"
unfolding p_passive_prog.block_1_def vc.vc_anon3_LoopBody_def
apply (tactic \<open> boogie_vc_tac @{context} @{thms global_assms} (@{thm forall_poly_thm}, @{thm exists_poly_thm}) block_anon3_LoopBody_hints \<close>)
by (auto?)

ML\<open>
val block_anon2_hints = [
(AssertNoConj,NONE)]
\<close>
lemma block_anon2AA0:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.block_2 (Normal n_s) s') \<Longrightarrow> ((vc.vc_anon2 ) \<Longrightarrow> ((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))))"
unfolding p_passive_prog.block_2_def vc.vc_anon2_def
apply (tactic \<open> boogie_vc_tac @{context} @{thms global_assms} (@{thm forall_poly_thm}, @{thm exists_poly_thm}) block_anon2_hints \<close>)
by (auto?)

ML\<open>
val block_anon3_LoopDone_hints = [
(AssumeConjR 0,NONE)]
\<close>
lemma block_anon3_LoopDoneAA0:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.block_3 (Normal n_s) s') \<Longrightarrow> ((vc.vc_anon3_LoopDone ) \<Longrightarrow> ((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon2 )))))))"
unfolding p_passive_prog.block_3_def vc.vc_anon3_LoopDone_def
apply (tactic \<open> boogie_vc_tac @{context} @{thms global_assms} (@{thm forall_poly_thm}, @{thm exists_poly_thm}) block_anon3_LoopDone_hints \<close>)
by (auto?)

ML\<open>
val block_anon3_LoopHead_hints = [
(AssumeConjR 0,NONE)]
\<close>
lemma block_anon3_LoopHeadAA0:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.block_4 (Normal n_s) s') \<Longrightarrow> ((vc.vc_anon3_LoopHead ) \<Longrightarrow> ((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon3_LoopDone ) \<and> (vc.vc_anon3_LoopBody ))))))))"
unfolding p_passive_prog.block_4_def vc.vc_anon3_LoopHead_def
apply (tactic \<open> boogie_vc_tac @{context} @{thms global_assms} (@{thm forall_poly_thm}, @{thm exists_poly_thm}) block_anon3_LoopHead_hints \<close>)
by (auto?)

ML\<open>
val block_anon0_hints = [
(AssertSub,NONE)]
\<close>
lemma block_anon0AA0:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.block_5 (Normal n_s) s') \<Longrightarrow> ((vc.vc_anon0 ) \<Longrightarrow> ((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon3_LoopHead )))))))"
unfolding p_passive_prog.block_5_def vc.vc_anon0_def
apply (tactic \<open> boogie_vc_tac @{context} @{thms global_assms} (@{thm forall_poly_thm}, @{thm exists_poly_thm}) block_anon0_hints \<close>)
by (auto?)

lemma block_0:
assumes 
"(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.block_6 (Normal n_s) s')" and 
"(vc.vc_anon0 )"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 )))))"
using assms
unfolding p_passive_prog.block_6_def
apply cases
by auto

lemma block_PreconditionGeneratedEntry:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.block_7 (Normal n_s) s') \<Longrightarrow> ((vc.vc_PreconditionGeneratedEntry ) \<Longrightarrow> ((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 )))))))"
apply (erule red_cmd_list.cases)
using global_assms
unfolding p_passive_prog.block_7_def vc.vc_PreconditionGeneratedEntry_def
apply (handle_cmd_list_full?)
by (auto?)

lemma cfg_block_GeneratedUnifiedExit:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.proc_body ((Inl 0),(Normal n_s)) (m',s'))"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step_no_succ[OF assms(1) p_passive_prog.node_0 p_passive_prog.outEdges_0])
using block_GeneratedUnifiedExit by blast

lemma cfg_block_anon3_LoopBody:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.proc_body ((Inl 1),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon3_LoopBody )"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step_magic[OF assms(1) p_passive_prog.node_1])
by (erule block_anon3_LoopBodyAA0[OF _ assms(2)])

lemma cfg_block_anon2:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.proc_body ((Inl 2),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon2 )"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step_2[OF assms(1) p_passive_prog.node_2])
apply (erule block_anon2AA0[OF _ assms(2)])
apply ((simp add:p_passive_prog.outEdges_2))
apply (erule member_elim, simp)
apply (erule cfg_block_GeneratedUnifiedExit, simp?)
by (simp add: member_rec(2))

lemma cfg_block_anon3_LoopDone:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.proc_body ((Inl 3),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon3_LoopDone )"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) p_passive_prog.node_3])
apply (erule block_anon3_LoopDoneAA0[OF _ assms(2)])
apply ((simp add:p_passive_prog.outEdges_3))
apply (erule member_elim, simp)
apply (erule cfg_block_anon2, simp?)
by (simp add: member_rec(2))

lemma cfg_block_anon3_LoopHead:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.proc_body ((Inl 4),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon3_LoopHead )"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) p_passive_prog.node_4])
apply (erule block_anon3_LoopHeadAA0[OF _ assms(2)])
apply ((simp add:p_passive_prog.outEdges_4))
apply (erule member_elim, simp)
apply (erule cfg_block_anon3_LoopDone, simp?)
apply (erule member_elim, simp)
apply (erule cfg_block_anon3_LoopBody, simp?)
by (simp add: member_rec(2))

lemma cfg_block_anon0:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.proc_body ((Inl 5),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon0 )"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) p_passive_prog.node_5])
apply (erule block_anon0AA0[OF _ assms(2)])
apply ((simp add:p_passive_prog.outEdges_5))
apply (erule member_elim, simp)
apply (erule cfg_block_anon3_LoopHead, simp?)
by (simp add: member_rec(2))

lemma cfg_block_0:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.proc_body ((Inl 6),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon0 )"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) p_passive_prog.node_6])
apply (erule block_0[OF _ assms(2)])
apply ((simp add:p_passive_prog.outEdges_6))
apply (erule member_elim, simp)
apply (erule cfg_block_anon0, simp?)
by (simp add: member_rec(2))

lemma cfg_PreconditionGeneratedEntry:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> p_passive_prog.proc_body ((Inl 7),(Normal n_s)) (m',s'))" and 
"(vc.vc_PreconditionGeneratedEntry )"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) p_passive_prog.node_7])
apply (erule block_PreconditionGeneratedEntry[OF _ assms(2)])
apply ((simp add:p_passive_prog.outEdges_7))
apply (erule member_elim, simp)
apply (erule cfg_block_0, simp?)
by (simp add: member_rec(2))


end

locale axioms = 
fixes A :: "(('a)absval_ty_fun)" and \<Lambda> :: "(var_context)" and \<Gamma> :: "(('a)fun_interp)" and n_s :: "(('a)nstate)"
assumes 
G0: "(\<And> v. (closed ((type_of_val A) v)))"
begin

lemmas global_assms = G0
lemmas forall_poly_thm = forall_vc_type[OF G0]
lemmas exists_poly_thm = exists_vc_type[OF G0]
declare Nat.One_nat_def[simp del]


end

definition ctor_list
  where
    "ctor_list  = []"
fun ctor :: "((closed_ty) => int)"
  where
    "ctor (TConC s _) = (the (map_of ctor_list s))"
declare One_nat_def[simp del]

lemma end_to_end:
assumes 
Red: "(red_cfg_multi A M ((append p_before_ast_to_cfg_prog.constants_vdecls p_before_ast_to_cfg_prog.globals_vdecls),(append p_passive_prog.params_vdecls p_passive_prog.locals_vdecls)) \<Gamma> [] p_passive_prog.proc_body ((Inl 7),(Normal n_s)) (m',s'))" and 
VC: "(\<And> (vc_x::int). (vc.vc_PreconditionGeneratedEntry ))" and 
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
from ParamsLocal have sc_x:"(((lookup_var ?\<Lambda> n_s 0) = (Some (IntV (convert_val_to_int (the (lookup_var ?\<Lambda> n_s 0)))))) \<and> (((type_of_val A) (the (lookup_var ?\<Lambda> n_s 0))) = (TPrim TInt)))"
apply (simp only:state_typ_wf_def)
apply (erule allE, erule allE, erule impE, rule map_of_lookup_vdecls_ty[OF p_passive_prog.m_x])
apply (subst lookup_var_local[OF p_passive_prog.m_x])+
by (fastforce dest: tint_intv tbool_boolv)
show "(s' \<noteq> Failure)"
apply (rule passification.cfg_PreconditionGeneratedEntry[OF _ Red])
apply (simp only:passification_def)
apply (intro conjI)?
apply (rule HOL.conjunct1[OF sc_x])
apply (simp add:Closed)
apply (rule VC)
done
qed



end
