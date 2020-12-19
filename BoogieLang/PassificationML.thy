theory PassificationML
imports Boogie_Lang.Semantics HelperML Passification
begin

ML \<open>
fun type_rel_tac _ [] = (fn _ => all_tac)
 |  type_rel_tac ctxt ((thm1,thm2)::rest) = 
       ((asm_full_simp_tac (add_simps [thm1,thm2] ctxt)) |> SOLVED') THEN'
       type_rel_tac ctxt rest

(* apply resolve_tac for each thm in the provided list (in that order) *)
fun resolve_tac_list _ [] = (fn _ => all_tac)
 |  resolve_tac_list ctxt (thm::rest) = resolve_tac ctxt [thm] THEN' resolve_tac_list ctxt rest

(* 
  apply (rule passification_cfg_helper[OF assms(1) _ assms(2) sync_before_passive_prog.node_1 sync_passive_prog.node_1 ])           
       apply (simp add: sync_before_passive_prog.outEdges_1 sync_passive_prog.outEdges_1)     
      apply (erule block_anon4_Then, assumption)
  apply (tactic \<open>resolve_tac_list @{context} @{thms assms(3-)} 1\<close>)     
    apply (simp, simp, simp)  
  apply (simp only: sync_before_passive_prog.outEdges_1)
(* process next successor *)
  apply (erule member_elim)
   apply (rule cfg_block_anon3)
     apply simp
    apply (erule passive_assms_2_ext)
    apply simp
   apply (simp add: update_nstate_rel_def)
(* finished processing next successor *)
  by (simp add: member_rec(2))
*)

fun cfg_lemma_successors_tac ctxt _ [] = asm_full_simp_tac (add_simps [@{thm member_rec(2)}] ctxt)
 |  cfg_lemma_successors_tac ctxt assms (succ_cfg_lemma :: rest) =
      let val n_suc_state_assms = (Thm.nprems_of succ_cfg_lemma)-2 in
        eresolve_tac ctxt [@{thm member_elim}] THEN'
        resolve_tac ctxt [succ_cfg_lemma] THEN'
        asm_full_simp_tac ctxt THEN'
        eresolve_tac ctxt [@{thm passive_assms_2_ext}] THEN'
        asm_full_simp_tac ctxt THEN'        
        (* need to solve n_suc_state_assms many state relation goals *)
        repeat_n_tac' n_suc_state_assms (asm_full_simp_tac (add_simps (@{thm update_nstate_rel_def} :: assms) ctxt))THEN'
        cfg_lemma_successors_tac ctxt assms rest
      end

fun cfg_lemma_tac ctxt red_assm passive_lemma_assm state_rel_assms pre_node_edge_thms passive_node_edge_thms block_lemma succ_cfg_lemmas =
  let 
     val (pre_node_thm, pre_edge_thm) = pre_node_edge_thms
     val (passive_node_thm, passive_edge_thm) = passive_node_edge_thms
     val cfg_helper_inst = @{thm passification_cfg_helper} OF [red_assm, passive_lemma_assm, pre_node_thm, passive_node_thm]
  in
    resolve_tac ctxt [cfg_helper_inst] THEN'
    (asm_full_simp_tac (add_simps [pre_edge_thm, passive_edge_thm] ctxt)) THEN'
    eresolve_tac ctxt [block_lemma] THEN'
    assume_tac ctxt THEN'
    resolve_tac_list ctxt state_rel_assms THEN'
    asm_full_simp_tac ctxt THEN' fastforce_tac ctxt [] THEN' asm_full_simp_tac ctxt THEN'
    (asm_full_simp_tac (add_simps [pre_edge_thm] ctxt)) THEN'
    cfg_lemma_successors_tac ctxt state_rel_assms succ_cfg_lemmas
  end
\<close>

end