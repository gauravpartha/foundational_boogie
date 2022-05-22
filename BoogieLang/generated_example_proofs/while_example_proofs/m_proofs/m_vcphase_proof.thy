theory m_vcphase_proof
imports Boogie_Lang.Semantics Boogie_Lang.Util Boogie_Lang.VCHints Boogie_Lang.VCPhaseML m_passive_prog m_before_passive_prog
begin
locale vc
begin

definition vc_anon3_LoopDone
  where
    "vc_anon3_LoopDone n i_0 = ((n \<le> i_0) \<longrightarrow> (i_0 \<ge> n))"
definition vc_anon3_LoopBody
  where
    "vc_anon3_LoopBody i_0 n i_1 = (((i_0 < n) \<and> (i_1 = (i_0 + (1::int)))) \<longrightarrow> (i_1 \<le> n))"
definition vc_anon3_LoopHead
  where
    "vc_anon3_LoopHead i_0 n i_1 = ((i_0 \<le> n) \<longrightarrow> ((vc_anon3_LoopDone n i_0) \<and> (vc_anon3_LoopBody i_0 n i_1)))"
definition vc_anon0
  where
    "vc_anon0 n i_0 i_1 = ((n > (0::int)) \<longrightarrow> (((0::int) \<le> n) \<and> (((0::int) \<le> n) \<longrightarrow> (vc_anon3_LoopHead i_0 n i_1))))"
definition vc_PreconditionGeneratedEntry
  where
    "vc_PreconditionGeneratedEntry n i_0 i_1 = (vc_anon0 n i_0 i_1)"

end

locale passification = 
fixes A :: "(('a)absval_ty_fun)" and \<Lambda> :: "(var_context)" and \<Gamma> :: "(('a)fun_interp)" and n_s :: "(('a)nstate)" and vc_i :: "int" and vc_n :: "int" and vc_i_0 :: "int" and vc_i_1 :: "int"
assumes 
G0: "((lookup_var \<Lambda> n_s 0) = (Some (IntV vc_i)))" and 
G1: "((lookup_var \<Lambda> n_s 1) = (Some (IntV vc_n)))" and 
G2: "((lookup_var \<Lambda> n_s 2) = (Some (IntV vc_i_0)))" and 
G3: "((lookup_var \<Lambda> n_s 3) = (Some (IntV vc_i_1)))" and 
G4: "(\<And> v. (closed ((type_of_val A) v)))"
begin

lemmas global_assms = G0 G1 G2 G3 G4
lemmas forall_poly_thm = forall_vc_type[OF G4]
lemmas exists_poly_thm = exists_vc_type[OF G4]
declare Nat.One_nat_def[simp del]

lemma block_GeneratedUnifiedExit:
assumes 
"(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> m_passive_prog.block_0 (Normal n_s) s')"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))"
using assms
unfolding m_passive_prog.block_0_def
apply cases
by auto

ML\<open>
val block_anon3_LoopDone_hints = [
(AssumeConjR 0,NONE), 
(AssertNoConj,NONE)]
\<close>
lemma block_anon3_LoopDoneAA0:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> m_passive_prog.block_1 (Normal n_s) s') \<Longrightarrow> ((vc.vc_anon3_LoopDone vc_n vc_i_0) \<Longrightarrow> ((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> (n_s' = n_s))))))"
unfolding m_passive_prog.block_1_def vc.vc_anon3_LoopDone_def
apply (tactic \<open> boogie_vc_tac @{context} @{thms global_assms} (@{thm forall_poly_thm}, @{thm exists_poly_thm}) block_anon3_LoopDone_hints \<close>)
by (auto?)

ML\<open>
val block_anon3_LoopBody_hints = [
(AssumeConjR 1,NONE), 
(AssumeConjR 0,NONE), 
(AssertNoConj,NONE), 
(AssumeFalse,NONE)]
\<close>
lemma block_anon3_LoopBodyAA0:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> m_passive_prog.block_2 (Normal n_s) s') \<Longrightarrow> ((vc.vc_anon3_LoopBody vc_i_0 vc_n vc_i_1) \<Longrightarrow> (s' = Magic)))"
unfolding m_passive_prog.block_2_def vc.vc_anon3_LoopBody_def
apply (tactic \<open> boogie_vc_tac @{context} @{thms global_assms} (@{thm forall_poly_thm}, @{thm exists_poly_thm}) block_anon3_LoopBody_hints \<close>)
by (auto?)

ML\<open>
val block_anon3_LoopHead_hints = [
(AssumeConjR 0,NONE)]
\<close>
lemma block_anon3_LoopHeadAA0:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> m_passive_prog.block_3 (Normal n_s) s') \<Longrightarrow> ((vc.vc_anon3_LoopHead vc_i_0 vc_n vc_i_1) \<Longrightarrow> ((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> ((vc.vc_anon3_LoopDone vc_n vc_i_0) \<and> (vc.vc_anon3_LoopBody vc_i_0 vc_n vc_i_1))))))))"
unfolding m_passive_prog.block_3_def vc.vc_anon3_LoopHead_def
apply (tactic \<open> boogie_vc_tac @{context} @{thms global_assms} (@{thm forall_poly_thm}, @{thm exists_poly_thm}) block_anon3_LoopHead_hints \<close>)
by (auto?)

ML\<open>
val block_anon0_hints = [
(AssumeConjR 0,NONE), 
(AssertSub,NONE)]
\<close>
lemma block_anon0AA0:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> m_passive_prog.block_4 (Normal n_s) s') \<Longrightarrow> ((vc.vc_anon0 vc_n vc_i_0 vc_i_1) \<Longrightarrow> ((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon3_LoopHead vc_i_0 vc_n vc_i_1)))))))"
unfolding m_passive_prog.block_4_def vc.vc_anon0_def
apply (tactic \<open> boogie_vc_tac @{context} @{thms global_assms} (@{thm forall_poly_thm}, @{thm exists_poly_thm}) block_anon0_hints \<close>)
by (auto?)

lemma block_0:
assumes 
"(red_cmd_list A M \<Lambda> \<Gamma> \<Omega> m_passive_prog.block_5 (Normal n_s) s')" and 
"(vc.vc_anon0 vc_n vc_i_0 vc_i_1)"
shows "((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 vc_n vc_i_0 vc_i_1)))))"
using assms
unfolding m_passive_prog.block_5_def
apply cases
by auto

lemma block_PreconditionGeneratedEntry:
shows "((red_cmd_list A M \<Lambda> \<Gamma> \<Omega> m_passive_prog.block_6 (Normal n_s) s') \<Longrightarrow> ((vc.vc_PreconditionGeneratedEntry vc_n vc_i_0 vc_i_1) \<Longrightarrow> ((s' \<noteq> Failure) \<and> (\<forall> n_s'. ((s' = (Normal n_s')) \<longrightarrow> ((n_s' = n_s) \<and> (vc.vc_anon0 vc_n vc_i_0 vc_i_1)))))))"
apply (erule red_cmd_list.cases)
using global_assms
unfolding m_passive_prog.block_6_def vc.vc_PreconditionGeneratedEntry_def
apply (handle_cmd_list_full?)
by (auto?)

lemma cfg_block_GeneratedUnifiedExit:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> m_passive_prog.proc_body ((Inl 0),(Normal n_s)) (m',s'))"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step_no_succ[OF assms(1) m_passive_prog.node_0 m_passive_prog.outEdges_0])
using block_GeneratedUnifiedExit by blast

lemma cfg_block_anon3_LoopDone:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> m_passive_prog.proc_body ((Inl 1),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon3_LoopDone vc_n vc_i_0)"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step_2[OF assms(1) m_passive_prog.node_1])
apply (erule block_anon3_LoopDoneAA0[OF _ assms(2)])
apply ((simp add:m_passive_prog.outEdges_1))
apply (erule member_elim, simp)
apply (erule cfg_block_GeneratedUnifiedExit, simp?)
by (simp add: member_rec(2))

lemma cfg_block_anon3_LoopBody:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> m_passive_prog.proc_body ((Inl 2),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon3_LoopBody vc_i_0 vc_n vc_i_1)"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step_magic[OF assms(1) m_passive_prog.node_2])
by (erule block_anon3_LoopBodyAA0[OF _ assms(2)])

lemma cfg_block_anon3_LoopHead:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> m_passive_prog.proc_body ((Inl 3),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon3_LoopHead vc_i_0 vc_n vc_i_1)"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) m_passive_prog.node_3])
apply (erule block_anon3_LoopHeadAA0[OF _ assms(2)])
apply ((simp add:m_passive_prog.outEdges_3))
apply (erule member_elim, simp)
apply (erule cfg_block_anon3_LoopDone, simp?)
apply (erule member_elim, simp)
apply (erule cfg_block_anon3_LoopBody, simp?)
by (simp add: member_rec(2))

lemma cfg_block_anon0:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> m_passive_prog.proc_body ((Inl 4),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon0 vc_n vc_i_0 vc_i_1)"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) m_passive_prog.node_4])
apply (erule block_anon0AA0[OF _ assms(2)])
apply ((simp add:m_passive_prog.outEdges_4))
apply (erule member_elim, simp)
apply (erule cfg_block_anon3_LoopHead, simp?)
by (simp add: member_rec(2))

lemma cfg_block_0:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> m_passive_prog.proc_body ((Inl 5),(Normal n_s)) (m',s'))" and 
"(vc.vc_anon0 vc_n vc_i_0 vc_i_1)"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) m_passive_prog.node_5])
apply (erule block_0[OF _ assms(2)])
apply ((simp add:m_passive_prog.outEdges_5))
apply (erule member_elim, simp)
apply (erule cfg_block_anon0, simp?)
by (simp add: member_rec(2))

lemma cfg_PreconditionGeneratedEntry:
assumes 
"(red_cfg_multi A M \<Lambda> \<Gamma> \<Omega> m_passive_prog.proc_body ((Inl 6),(Normal n_s)) (m',s'))" and 
"(vc.vc_PreconditionGeneratedEntry vc_n vc_i_0 vc_i_1)"
shows "(s' \<noteq> Failure)"
apply (rule converse_rtranclpE2[OF assms(1)], fastforce)
apply (rule red_cfg_multi_backwards_step[OF assms(1) m_passive_prog.node_6])
apply (erule block_PreconditionGeneratedEntry[OF _ assms(2)])
apply ((simp add:m_passive_prog.outEdges_6))
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
Red: "(red_cfg_multi A M ((append global_data.constants_vdecls global_data.globals_vdecls),(append m_passive_prog.params_vdecls m_passive_prog.locals_vdecls)) \<Gamma> [] m_passive_prog.proc_body ((Inl 6),(Normal n_s)) (m',s'))" and 
VC: "(\<And> (vc_i::int) (vc_n::int) (vc_i_0::int) (vc_i_1::int). (vc.vc_PreconditionGeneratedEntry vc_n vc_i_0 vc_i_1))" and 
Closed: "(\<And> v. (closed ((type_of_val A) v)))" and 
NonEmptyTypes: "(\<And> t. ((closed t) \<Longrightarrow> (\<exists> v. (((type_of_val A) v) = t))))" and 
FInterp: "(fun_interp_wf A global_data.fdecls \<Gamma>)" and 
Axioms: "(axiom_assm A \<Gamma> global_data.constants_vdecls (n_s::(('a)nstate)) global_data.axioms)" and 
ParamsLocal: "(state_typ_wf A [] (local_state n_s) (append m_passive_prog.params_vdecls m_passive_prog.locals_vdecls))" and 
ConstsGlobal: "(state_typ_wf A [] (global_state n_s) (append global_data.constants_vdecls global_data.globals_vdecls))"
shows "(s' \<noteq> Failure)"
proof -
let ?n_s_c = "(nstate_global_restriction n_s global_data.constants_vdecls)"
let ?\<Lambda> = "((append global_data.constants_vdecls global_data.globals_vdecls),(append m_passive_prog.params_vdecls m_passive_prog.locals_vdecls))"
let ?\<Lambda>c = "((global_data.constants_vdecls,[])::(var_context))"
from ParamsLocal have sc_i:"(((lookup_var ?\<Lambda> n_s 0) = (Some (IntV (convert_val_to_int (the (lookup_var ?\<Lambda> n_s 0)))))) \<and> (((type_of_val A) (the (lookup_var ?\<Lambda> n_s 0))) = (TPrim TInt)))"
apply (simp only:state_typ_wf_def)
apply (erule allE, erule allE, erule impE, rule map_of_lookup_vdecls_ty[OF m_passive_prog.m_i])
apply (subst lookup_var_local[OF m_passive_prog.m_i])+
by (fastforce dest: tint_intv tbool_boolv)
from ParamsLocal have sc_n:"(((lookup_var ?\<Lambda> n_s 1) = (Some (IntV (convert_val_to_int (the (lookup_var ?\<Lambda> n_s 1)))))) \<and> (((type_of_val A) (the (lookup_var ?\<Lambda> n_s 1))) = (TPrim TInt)))"
apply (simp only:state_typ_wf_def)
apply (erule allE, erule allE, erule impE, rule map_of_lookup_vdecls_ty[OF m_passive_prog.m_n])
apply (subst lookup_var_local[OF m_passive_prog.m_n])+
by (fastforce dest: tint_intv tbool_boolv)
from ParamsLocal have sc_i_0:"(((lookup_var ?\<Lambda> n_s 2) = (Some (IntV (convert_val_to_int (the (lookup_var ?\<Lambda> n_s 2)))))) \<and> (((type_of_val A) (the (lookup_var ?\<Lambda> n_s 2))) = (TPrim TInt)))"
apply (simp only:state_typ_wf_def)
apply (erule allE, erule allE, erule impE, rule map_of_lookup_vdecls_ty[OF m_passive_prog.m_i_0])
apply (subst lookup_var_local[OF m_passive_prog.m_i_0])+
by (fastforce dest: tint_intv tbool_boolv)
from ParamsLocal have sc_i_1:"(((lookup_var ?\<Lambda> n_s 3) = (Some (IntV (convert_val_to_int (the (lookup_var ?\<Lambda> n_s 3)))))) \<and> (((type_of_val A) (the (lookup_var ?\<Lambda> n_s 3))) = (TPrim TInt)))"
apply (simp only:state_typ_wf_def)
apply (erule allE, erule allE, erule impE, rule map_of_lookup_vdecls_ty[OF m_passive_prog.m_i_1])
apply (subst lookup_var_local[OF m_passive_prog.m_i_1])+
by (fastforce dest: tint_intv tbool_boolv)
show "(s' \<noteq> Failure)"
apply (rule passification.cfg_PreconditionGeneratedEntry[OF _ Red])
apply (simp only:passification_def)
apply (intro conjI)?
apply (rule HOL.conjunct1[OF sc_i])
apply (rule HOL.conjunct1[OF sc_n])
apply (rule HOL.conjunct1[OF sc_i_0])
apply (rule HOL.conjunct1[OF sc_i_1])
apply (simp add:Closed)
apply (rule VC)
done
qed



end
