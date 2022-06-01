theory triangle_vcphase_proof
imports Boogie_Lang.Semantics Boogie_Lang.Util Boogie_Lang.VCHints Boogie_Lang.VCPhaseML triangle_passive_prog triangle_before_passive_prog
begin
locale vc
begin

definition vc_anon2_LoopBody
  where
    "vc_anon2_LoopBody m_0 n t_1 t_0 m_1 = ((m_0 < n) \<longrightarrow> (((t_1 = (t_0 + m_0)) \<and> (m_1 = (m_0 + (1::int)))) \<longrightarrow> ((t_1 = (smt_div (m_1 * (m_1 - (1::int))) (2::int))) \<and> ((t_1 = (smt_div (m_1 * (m_1 - (1::int))) (2::int))) \<longrightarrow> (m_1 \<le> n)))))"
definition vc_GeneratedUnifiedExit
  where
    "vc_GeneratedUnifiedExit t_2 n = (t_2 = (smt_div (n * (n - (1::int))) (2::int)))"
definition vc_anon2_LoopDone
  where
    "vc_anon2_LoopDone n m_0 t_2 t_0 = (((n \<le> m_0) \<and> (t_2 = t_0)) \<longrightarrow> (vc_GeneratedUnifiedExit t_2 n))"
definition vc_anon2_LoopHead
  where
    "vc_anon2_LoopHead t_0 m_0 n t_2 t_1 m_1 = (((t_0 = (smt_div (m_0 * (m_0 - (1::int))) (2::int))) \<and> (m_0 \<le> n)) \<longrightarrow> ((vc_anon2_LoopDone n m_0 t_2 t_0) \<and> (vc_anon2_LoopBody m_0 n t_1 t_0 m_1)))"
definition vc_anon0
  where
    "vc_anon0 n t_0 m_0 t_2 t_1 m_1 = (((0::int) = (smt_div ((0::int) * ((0::int) - (1::int))) (2::int))) \<and> (((0::int) = (smt_div ((0::int) * ((0::int) - (1::int))) (2::int))) \<longrightarrow> (((0::int) \<le> n) \<and> (((0::int) \<le> n) \<longrightarrow> (vc_anon2_LoopHead t_0 m_0 n t_2 t_1 m_1)))))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry n t_0 m_0 t_2 t_1 m_1 = ((n \<ge> (0::int)) \<longrightarrow> (vc_anon0 n t_0 m_0 t_2 t_1 m_1))"

end

locale passification = 
fixes A :: "(('a)absval_ty_fun)" and \<Lambda> :: "(var_context)" and \<Gamma> :: "(('a)fun_interp)" and n_s :: "(('a)nstate)" and vc_n :: "int" and vc_m :: "int" and vc_t_0 :: "int" and vc_m_0 :: "int" and vc_t_1 :: "int" and vc_m_1 :: "int" and vc_t_2 :: "int" and vc_t :: "int"
assumes 
G0: "((lookup_var \<Lambda> n_s 0) = (Some (IntV vc_n)))" and 
G1: "((lookup_var \<Lambda> n_s 1) = (Some (IntV vc_m)))" and 
G2: "((lookup_var \<Lambda> n_s 3) = (Some (IntV vc_t_0)))" and 
G3: "((lookup_var \<Lambda> n_s 4) = (Some (IntV vc_m_0)))" and 
G4: "((lookup_var \<Lambda> n_s 5) = (Some (IntV vc_t_1)))" and 
G5: "((lookup_var \<Lambda> n_s 6) = (Some (IntV vc_m_1)))" and 
G6: "((lookup_var \<Lambda> n_s 7) = (Some (IntV vc_t_2)))" and 
G7: "((lookup_var \<Lambda> n_s 2) = (Some (IntV vc_t)))" and 
G8: "(\<And> v. (closed ((type_of_val A) v)))"
begin

lemmas global_assms = G0 G1 G2 G3 G4 G5 G6 G7 G8
lemmas forall_poly_thm = forall_vc_type[OF G8]
lemmas exists_poly_thm = exists_vc_type[OF G8]
declare Nat.One_nat_def[simp del]

ML\<open>
val block_GeneratedUnifiedExit_hints = [
(AssertNoConj,NONE)]
\<close>
lemma block_GeneratedUnifiedExitAA0:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> triangle_passive_prog.block_0 (Normal n_s) s') \<Longrightarrow> ((vc.vc_GeneratedUnifiedExit vc_t_2 vc_n) \<Longrightarrow> ((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))))"
unfolding triangle_passive_prog.block_0_def vc.vc_GeneratedUnifiedExit_def
apply (tactic \<open> boogie_vc_tac @{context} @{thms global_assms} (@{thm forall_poly_thm}, @{thm exists_poly_thm}) block_GeneratedUnifiedExit_hints \<close>)
by (auto?)

ML\<open>
val block_anon2_LoopDone_hints = [
(AssumeConjR 1,NONE), 
(AssumeConjR 0,NONE)]
\<close>
lemma block_anon2_LoopDoneAA0:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> triangle_passive_prog.block_1 (Normal n_s) s') \<Longrightarrow> ((vc.vc_anon2_LoopDone vc_n vc_m_0 vc_t_2 vc_t_0) \<Longrightarrow> ((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_GeneratedUnifiedExit vc_t_2 vc_n)))))))"
unfolding triangle_passive_prog.block_1_def vc.vc_anon2_LoopDone_def
apply (tactic \<open> boogie_vc_tac @{context} @{thms global_assms} (@{thm forall_poly_thm}, @{thm exists_poly_thm}) block_anon2_LoopDone_hints \<close>)
by (auto?)

ML\<open>
val block_anon2_LoopBody_hints = [
(AssumeConjR 0,NONE), 
(AssumeConjR 1,NONE), 
(AssumeConjR 0,NONE), 
(AssertSub,NONE), 
(AssertNoConj,NONE), 
(AssumeFalse,NONE)]
\<close>
lemma block_anon2_LoopBodyAA0:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> triangle_passive_prog.block_2 (Normal n_s) s') \<Longrightarrow> ((vc.vc_anon2_LoopBody vc_m_0 vc_n vc_t_1 vc_t_0 vc_m_1) \<Longrightarrow> (s' = Magic)))"
unfolding triangle_passive_prog.block_2_def vc.vc_anon2_LoopBody_def
apply (tactic \<open> boogie_vc_tac @{context} @{thms global_assms} (@{thm forall_poly_thm}, @{thm exists_poly_thm}) block_anon2_LoopBody_hints \<close>)
by (auto?)

ML\<open>
val block_anon2_LoopHead_hints = [
(AssumeConjR 1,NONE), 
(AssumeConjR 0,NONE)]
\<close>
lemma block_anon2_LoopHeadAA0:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> triangle_passive_prog.block_3 (Normal n_s) s') \<Longrightarrow> ((vc.vc_anon2_LoopHead vc_t_0 vc_m_0 vc_n vc_t_2 vc_t_1 vc_m_1) \<Longrightarrow> ((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon2_LoopDone vc_n vc_m_0 vc_t_2 vc_t_0) \<and> (vc.vc_anon2_LoopBody vc_m_0 vc_n vc_t_1 vc_t_0 vc_m_1))))))))"
unfolding triangle_passive_prog.block_3_def vc.vc_anon2_LoopHead_def
apply (tactic \<open> boogie_vc_tac @{context} @{thms global_assms} (@{thm forall_poly_thm}, @{thm exists_poly_thm}) block_anon2_LoopHead_hints \<close>)
by (auto?)

ML\<open>
val block_anon0_hints = [
(AssertSub,NONE), 
(AssertSub,NONE)]
\<close>
lemma block_anon0AA0:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> triangle_passive_prog.block_4 (Normal n_s) s') \<Longrightarrow> ((vc.vc_anon0 vc_n vc_t_0 vc_m_0 vc_t_2 vc_t_1 vc_m_1) \<Longrightarrow> ((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon2_LoopHead vc_t_0 vc_m_0 vc_n vc_t_2 vc_t_1 vc_m_1)))))))"
unfolding triangle_passive_prog.block_4_def vc.vc_anon0_def
apply (tactic \<open> boogie_vc_tac @{context} @{thms global_assms} (@{thm forall_poly_thm}, @{thm exists_poly_thm}) block_anon0_hints \<close>)
by (auto?)

lemma block_0:
assumes 
"(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> triangle_passive_prog.block_5 (Normal n_s) s')" and 
"(vc.vc_anon0 vc_n vc_t_0 vc_m_0 vc_t_2 vc_t_1 vc_m_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 vc_n vc_t_0 vc_m_0 vc_t_2 vc_t_1 vc_m_1)))))"
using assms
unfolding triangle_passive_prog.block_5_def
apply cases
by auto

ML\<open>
val block_PreconditionGeneratedEntry_hints = [
(AssumeConjR 0,NONE)]
\<close>
lemma block_PreconditionGeneratedEntryAA0:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> triangle_passive_prog.block_6 (Normal n_s) s') \<Longrightarrow> ((vc.vc_PreconditionGeneratedEntry vc_n vc_t_0 vc_m_0 vc_t_2 vc_t_1 vc_m_1) \<Longrightarrow> ((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 vc_n vc_t_0 vc_m_0 vc_t_2 vc_t_1 vc_m_1)))))))"
unfolding triangle_passive_prog.block_6_def vc.vc_PreconditionGeneratedEntry_def
apply (tactic \<open> boogie_vc_tac @{context} @{thms global_assms} (@{thm forall_poly_thm}, @{thm exists_poly_thm}) block_PreconditionGeneratedEntry_hints \<close>)
by (auto?)

lemma cfg_block_GeneratedUnifiedExit:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> triangle_passive_prog.proc_body ((Inl 0),(Normal n_s)) (m',s'))" and 
"(vc.vc_GeneratedUnifiedExit vc_t_2 vc_n)"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step_no_succ[OF assms(1) triangle_passive_prog.node_0 triangle_passive_prog.outEdges_0])
using block_GeneratedUnifiedExitAA0[OF _ assms(2)] by blast

lemma cfg_block_anon2_LoopDone:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> triangle_passive_prog.proc_body ((Inl 1),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon2_LoopDone vc_n vc_m_0 vc_t_2 vc_t_0)"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) triangle_passive_prog.node_1])
apply (erule block_anon2_LoopDoneAA0[OF _ assms(2)])
apply ((simp add:triangle_passive_prog.outEdges_1))
apply (erule member_elim, simp)
apply (erule cfg_block_GeneratedUnifiedExit, simp?)
by (simp add: member_rec(2))

lemma cfg_block_anon2_LoopBody:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> triangle_passive_prog.proc_body ((Inl 2),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon2_LoopBody vc_m_0 vc_n vc_t_1 vc_t_0 vc_m_1)"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step_magic[OF assms(1) triangle_passive_prog.node_2])
by (erule block_anon2_LoopBodyAA0[OF _ assms(2)])

lemma cfg_block_anon2_LoopHead:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> triangle_passive_prog.proc_body ((Inl 3),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon2_LoopHead vc_t_0 vc_m_0 vc_n vc_t_2 vc_t_1 vc_m_1)"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) triangle_passive_prog.node_3])
apply (erule block_anon2_LoopHeadAA0[OF _ assms(2)])
apply ((simp add:triangle_passive_prog.outEdges_3))
apply (erule member_elim, simp)
apply (erule cfg_block_anon2_LoopDone, simp?)
apply (erule member_elim, simp)
apply (erule cfg_block_anon2_LoopBody, simp?)
by (simp add: member_rec(2))

lemma cfg_block_anon0:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> triangle_passive_prog.proc_body ((Inl 4),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon0 vc_n vc_t_0 vc_m_0 vc_t_2 vc_t_1 vc_m_1)"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) triangle_passive_prog.node_4])
apply (erule block_anon0AA0[OF _ assms(2)])
apply ((simp add:triangle_passive_prog.outEdges_4))
apply (erule member_elim, simp)
apply (erule cfg_block_anon2_LoopHead, simp?)
by (simp add: member_rec(2))

lemma cfg_block_0:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> triangle_passive_prog.proc_body ((Inl 5),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon0 vc_n vc_t_0 vc_m_0 vc_t_2 vc_t_1 vc_m_1)"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) triangle_passive_prog.node_5])
apply (erule block_0[OF _ assms(2)])
apply ((simp add:triangle_passive_prog.outEdges_5))
apply (erule member_elim, simp)
apply (erule cfg_block_anon0, simp?)
by (simp add: member_rec(2))

lemma cfg_block_PreconditionGeneratedEntry:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> triangle_passive_prog.proc_body ((Inl 6),(Normal n_s)) (m',s'))" and 
"(vc.vc_PreconditionGeneratedEntry vc_n vc_t_0 vc_m_0 vc_t_2 vc_t_1 vc_m_1)"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) triangle_passive_prog.node_6])
apply (erule block_PreconditionGeneratedEntryAA0[OF _ assms(2)])
apply ((simp add:triangle_passive_prog.outEdges_6))
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
Red: "(red_cfg_multi A M ((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls)) \<Gamma> [] triangle_passive_prog.proc_body ((Inl 6),(Normal n_s)) (m',s'))" and 
VC: "(\<And> (vc_n::int) (vc_m::int) (vc_t_0::int) (vc_m_0::int) (vc_t_1::int) (vc_m_1::int) (vc_t_2::int) (vc_t::int). (vc.vc_PreconditionGeneratedEntry vc_n vc_t_0 vc_m_0 vc_t_2 vc_t_1 vc_m_1))" and 
Closed: "(\<And> v. (closed ((type_of_val A) v)))" and 
NonEmptyTypes: "(\<And> t. ((closed t) \<Longrightarrow> (\<exists> v. (((type_of_val A) v) = t))))" and 
FInterp: "(fun_interp_wf A global_data.fdecls \<Gamma>)" and 
Axioms: "(axiom_assm A \<Gamma> global_data.constants_vdecls (n_s::(('a)nstate)) global_data.axioms)" and 
ParamsLocal: "(state_typ_wf A [] (local_state n_s) (append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls))" and 
ConstsGlobal: "(state_typ_wf A [] (global_state n_s) (append global_data.constants_vdecls global_data.globals_vdecls))"
shows "(s' \<noteq> Failure)"
proof -
let ?n_s_c = "(nstate_global_restriction n_s global_data.constants_vdecls)"
let ?\<Lambda> = "((append global_data.constants_vdecls global_data.globals_vdecls),(append triangle_passive_prog.params_vdecls triangle_passive_prog.locals_vdecls))"
let ?\<Lambda>c = "((global_data.constants_vdecls,[])::(var_context))"
from ParamsLocal have sc_n:"(((lookup_var ?\<Lambda> n_s 0) = (Some (IntV (convert_val_to_int (the (lookup_var ?\<Lambda> n_s 0)))))) \<and> (((type_of_val A) (the (lookup_var ?\<Lambda> n_s 0))) = (TPrim TInt)))"
apply (simp only:state_typ_wf_def)
apply (erule allE, erule allE, erule impE, rule map_of_lookup_vdecls_ty[OF triangle_passive_prog.m_n])
apply (subst lookup_var_local[OF triangle_passive_prog.m_n])+
by (fastforce dest: tint_intv tbool_boolv)
from ParamsLocal have sc_m:"(((lookup_var ?\<Lambda> n_s 1) = (Some (IntV (convert_val_to_int (the (lookup_var ?\<Lambda> n_s 1)))))) \<and> (((type_of_val A) (the (lookup_var ?\<Lambda> n_s 1))) = (TPrim TInt)))"
apply (simp only:state_typ_wf_def)
apply (erule allE, erule allE, erule impE, rule map_of_lookup_vdecls_ty[OF triangle_passive_prog.m_m])
apply (subst lookup_var_local[OF triangle_passive_prog.m_m])+
by (fastforce dest: tint_intv tbool_boolv)
from ParamsLocal have sc_t_0:"(((lookup_var ?\<Lambda> n_s 3) = (Some (IntV (convert_val_to_int (the (lookup_var ?\<Lambda> n_s 3)))))) \<and> (((type_of_val A) (the (lookup_var ?\<Lambda> n_s 3))) = (TPrim TInt)))"
apply (simp only:state_typ_wf_def)
apply (erule allE, erule allE, erule impE, rule map_of_lookup_vdecls_ty[OF triangle_passive_prog.m_t_0])
apply (subst lookup_var_local[OF triangle_passive_prog.m_t_0])+
by (fastforce dest: tint_intv tbool_boolv)
from ParamsLocal have sc_m_0:"(((lookup_var ?\<Lambda> n_s 4) = (Some (IntV (convert_val_to_int (the (lookup_var ?\<Lambda> n_s 4)))))) \<and> (((type_of_val A) (the (lookup_var ?\<Lambda> n_s 4))) = (TPrim TInt)))"
apply (simp only:state_typ_wf_def)
apply (erule allE, erule allE, erule impE, rule map_of_lookup_vdecls_ty[OF triangle_passive_prog.m_m_0])
apply (subst lookup_var_local[OF triangle_passive_prog.m_m_0])+
by (fastforce dest: tint_intv tbool_boolv)
from ParamsLocal have sc_t_1:"(((lookup_var ?\<Lambda> n_s 5) = (Some (IntV (convert_val_to_int (the (lookup_var ?\<Lambda> n_s 5)))))) \<and> (((type_of_val A) (the (lookup_var ?\<Lambda> n_s 5))) = (TPrim TInt)))"
apply (simp only:state_typ_wf_def)
apply (erule allE, erule allE, erule impE, rule map_of_lookup_vdecls_ty[OF triangle_passive_prog.m_t_1])
apply (subst lookup_var_local[OF triangle_passive_prog.m_t_1])+
by (fastforce dest: tint_intv tbool_boolv)
from ParamsLocal have sc_m_1:"(((lookup_var ?\<Lambda> n_s 6) = (Some (IntV (convert_val_to_int (the (lookup_var ?\<Lambda> n_s 6)))))) \<and> (((type_of_val A) (the (lookup_var ?\<Lambda> n_s 6))) = (TPrim TInt)))"
apply (simp only:state_typ_wf_def)
apply (erule allE, erule allE, erule impE, rule map_of_lookup_vdecls_ty[OF triangle_passive_prog.m_m_1])
apply (subst lookup_var_local[OF triangle_passive_prog.m_m_1])+
by (fastforce dest: tint_intv tbool_boolv)
from ParamsLocal have sc_t_2:"(((lookup_var ?\<Lambda> n_s 7) = (Some (IntV (convert_val_to_int (the (lookup_var ?\<Lambda> n_s 7)))))) \<and> (((type_of_val A) (the (lookup_var ?\<Lambda> n_s 7))) = (TPrim TInt)))"
apply (simp only:state_typ_wf_def)
apply (erule allE, erule allE, erule impE, rule map_of_lookup_vdecls_ty[OF triangle_passive_prog.m_t_2])
apply (subst lookup_var_local[OF triangle_passive_prog.m_t_2])+
by (fastforce dest: tint_intv tbool_boolv)
from ParamsLocal have sc_t:"(((lookup_var ?\<Lambda> n_s 2) = (Some (IntV (convert_val_to_int (the (lookup_var ?\<Lambda> n_s 2)))))) \<and> (((type_of_val A) (the (lookup_var ?\<Lambda> n_s 2))) = (TPrim TInt)))"
apply (simp only:state_typ_wf_def)
apply (erule allE, erule allE, erule impE, rule map_of_lookup_vdecls_ty[OF triangle_passive_prog.m_t])
apply (subst lookup_var_local[OF triangle_passive_prog.m_t])+
by (fastforce dest: tint_intv tbool_boolv)
show "(s' \<noteq> Failure)"
apply (rule passification.cfg_block_PreconditionGeneratedEntry[OF _ Red])
apply (simp only:passification_def)
apply (intro conjI)?
apply (rule HOL.conjunct1[OF sc_n])
apply (rule HOL.conjunct1[OF sc_m])
apply (rule HOL.conjunct1[OF sc_t_0])
apply (rule HOL.conjunct1[OF sc_m_0])
apply (rule HOL.conjunct1[OF sc_t_1])
apply (rule HOL.conjunct1[OF sc_m_1])
apply (rule HOL.conjunct1[OF sc_t_2])
apply (rule HOL.conjunct1[OF sc_t])
apply (simp add:Closed)
apply (rule VC)
done
qed



end
