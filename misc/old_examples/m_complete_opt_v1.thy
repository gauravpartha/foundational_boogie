theory m_complete_opt_v1
imports Semantics "HOL-Eisbach.Eisbach" Util
begin

fun outEdges_m
  where
    "outEdges_m (0) = {(Suc(0))}"
    |"outEdges_m (Suc(0)) = {}"
    |"outEdges_m _ = {}"

fun nodeToBlocks_m
  where
    "nodeToBlocks_m (0) = (Some 
            [(Assume (BinOp (FunExp ''f'' [(Var ''x'')]) Le  (Val (IntV 5)))),
              Assume (BinOp (Val (IntV 6)) Le (Var ''y'') )])"
  |"nodeToBlocks_m (Suc(0)) = (Some [                  
                 (Assert (BinOp (FunExp ''f'' [(Var ''x'')]) Le (Var ''y'')))
                ])"
  |"nodeToBlocks_m _ = (None )"

abbreviation G
  where "G \<equiv> (|entry = 0, nodes = {(0), (Suc(0))}, out_edges = outEdges_m, node_to_block = nodeToBlocks_m|)"

definition ProgramM
  where
    "ProgramM  = (Program [(''f'', [TInt], TInt)] [(''m'', [], [(''x'', TInt), (''y'', TInt)], G)])"

locale vc =
  fixes x :: int and y :: int and f :: "int \<Rightarrow> int"
begin

definition block1
  where "block1 \<equiv> (f x \<le> y)"

abbreviation block0
  where "block0 \<equiv> ((f x \<le> 5 \<and> 6 \<le> y) \<longrightarrow> block1)"

abbreviation block0_normal
  where "block0_normal \<equiv> f x \<le> 5 \<and> 6 \<le> y"

lemma vc_correct: "block0"
  apply (simp only:  block1_def)
  by smt

end


lemma block1_correct_inversion:
  assumes 
   A1:"\<Gamma> \<turnstile> \<langle>[Assert (BinOp (FunExp ''f'' [(Var ''x'')]) Le (Var ''y''))], Normal s\<rangle> [\<rightarrow>] s'" and
   A2:"(snd \<Gamma>) ''f'' = Some f" and
   A3:"s ''x'' = Some (IntV ix)" and
   A4:"s ''y'' = Some (IntV iy)" and
   A5:"\<forall> i :: int. f [IntV i] = Some (IntV (f' i))" and
   A6:"vc.block1 ix iy f'"
 shows "s' \<noteq> Failure \<and> (\<forall> n_s'. s' = Normal n_s' \<longrightarrow> n_s' = s)"
  using assms  
  apply cases
  apply (simp only: vc.block1_def)
  apply (handle_cmd_list_full)
  by (auto?)
 (* apply (metis (no_types, lifting) binop_lessOrEqual.simps(1) list.collapse option.inject val.inject(1) 
         )? (* here metis not required *)*)
  (*
  apply (handle_assert P: assms)
  (* next statement *)
  apply (erule nil_cmd_elim)
  apply simp
  done
  *)
  (* next statement *)
(*  apply (rule RedCmdListNil_case)
  apply (simp add: red_cmd_list.RedCmdListNil) 
  apply (frule step_nil_same)
  apply simp
  apply done *)
(*
lemma block1_correct:  
  assumes 
   A2:"(snd \<Gamma>) ''f'' = Some f" and
   A3:"s ''x'' = Some (IntV ix)" and
   A4:"s ''y'' = Some (IntV iy)" and
   A5:"\<forall> i :: int. f [IntV i] = Some (IntV (f' i))" and
   A6:"vc.block1 ix iy f'"
 shows "\<exists>s'. (\<Gamma> \<turnstile> \<langle>[Assert (BinOp (FunExp ''f'' [(Var ''x'')]) Le (Var ''y''))], Normal s\<rangle> [\<rightarrow>] s')
          \<and> (s' \<noteq> Failure)"
  apply (rule exI, rule conjI)
   apply rule
    (* assert *)
    apply (rule RedAssertOk)
   (* reduce the expression *)
   apply (simp? ; ( (simp add: assms | (rule+)), (simp add: assms)?)+)
   apply rule
  apply simp
  done
*)

lemma block0_correct_inversion: 
  assumes 
   "\<Gamma> \<turnstile> \<langle>[(Assume (BinOp (FunExp ''f'' [(Var ''x'')]) Le  (Val (IntV 5)))),
              Assume (BinOp (Val (IntV 6)) Le (Var ''y'') )], Normal s\<rangle> [\<rightarrow>] s'" and
   A2: "(snd \<Gamma>) ''f'' = Some f" and
   A3: "s ''x'' = Some (IntV ix)" and
   A4: "s ''y'' = Some (IntV iy)" and
   A5: "\<forall> i :: int. f [IntV i] = Some (IntV (f' i))" and
   A6: "vc.block0 ix iy f'"
  shows  "s' \<noteq> Failure \<and> (\<forall> n_s'. s' = Normal n_s' \<longrightarrow> ( n_s' = s \<and> vc.block1 ix iy f'))"
  using assms
  apply cases
  apply (handle_cmd_list_full)
  using assms
  using list.collapse by force  

thm list.collapse
(* by (metis binop_lessOrEqual.elims hd_Cons_tl option.discI option.inject val.inject(1) val.inject(2))*)
  
  

 (*
  (* assume init tac *)
  apply (handle_assume)
  (* next statement *)
  apply (erule RedCmdListCons_case)
  (* assume init tac *)
  apply (handle_assume)
  (* no more statements *)
  apply (erule nil_cmd_elim)
  (* prove goal *)
  apply (rule+; simp_all)
  using assms
  by (metis (no_types, lifting) binop_lessOrEqual.simps(1) list.collapse option.inject val.inject(1))
 *)

end
