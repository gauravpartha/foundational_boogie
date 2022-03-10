theory Ast
  imports Main Semantics Lang

begin

type_synonym name = string
type_synonym label = string
type_synonym guard = expr
type_synonym invariant = expr

type_synonym break_flag = bool
type_synonym 'a ast_state = "break_flag * ('a state)" 

datatype transfer_cmd
 = Goto label

datatype raw_structured_cmd 
 = If guard "stmt" "stmt"
 | While guard "stmt"  
 | Break "label option"

and stmt 
 = SimpleCmd cmd
 | SeqCmds "stmt list"
 | StructCmd raw_structured_cmd
 | TransCmd transfer_cmd

datatype parsed_structured_cmd
 = ParsedIf guard "bigblock list" "bigblock list"
 | ParsedWhile guard "invariant list" "bigblock list"
 | ParsedBreak "label option"

and bigblock 
 = BigBlock "name option" "cmd list" "parsed_structured_cmd option" "transfer_cmd option"

(*
record ast = 
  start_of_ast :: "node"
  trivial_out_edges :: "(node list) list"
  node_to_bigblock :: "bigblock list"
*)

type_synonym ast = "bigblock list"

(*
inductive red_stmt :: "'a absval_ty_fun \<Rightarrow> proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> stmt \<Rightarrow> 'a state \<Rightarrow> 'a state \<Rightarrow> bool" 
  ("_,_,_,_,_ \<turnstile> ((\<langle>_,_\<rangle>) \<longrightarrow>/ _)" [51,0,0,0] 81)
and  red_stmt_list :: "'a absval_ty_fun \<Rightarrow> proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> stmt list \<Rightarrow> 'a state \<Rightarrow> 'a state \<Rightarrow> bool"
  ("_,_,_,_,_ \<turnstile> ((\<langle>_,_\<rangle>) {\<rightarrow>}/ _)" [51,0,0,0] 81)
  for A :: "'a absval_ty_fun" and M :: proc_context and \<Lambda> :: var_context and \<Gamma> :: "'a fun_interp" and \<Omega> :: rtype_env
  where 
    RedSimpleCmd: "red_cmd A M \<Lambda> \<Gamma> \<Omega> my_cmd n_s s \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(SimpleCmd my_cmd), n_s\<rangle> \<longrightarrow> s" 

  | RedIfTrue: "\<lbrakk> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>my_guard, n_s\<rangle> \<Down> LitV (LBool True);  A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>then_stmts, Normal n_s\<rangle> {\<rightarrow>} s' \<rbrakk> \<Longrightarrow> 
                  A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>StructCmd (If my_guard then_stmts else_stmts), Normal n_s\<rangle> \<longrightarrow> s'"

  | RedIfFalse: "\<lbrakk> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>my_guard, n_s\<rangle> \<Down> LitV (LBool False);  A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>else_stmts,Normal n_s\<rangle> {\<rightarrow>} s' \<rbrakk> \<Longrightarrow> 
                  A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>StructCmd (If my_guard then_stmts else_stmts), Normal n_s\<rangle> \<longrightarrow> s'"

  | RedWhileTrue: "\<lbrakk> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>my_guard, n_s\<rangle> \<Down> LitV (LBool True); A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>stmts, Normal n_s\<rangle> {\<rightarrow>} s1; A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>StructCmd (While my_guard stmts), s1\<rangle> \<longrightarrow> s2 \<rbrakk> \<Longrightarrow> 
                  A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>StructCmd (While my_guard stmts), Normal n_s\<rangle> \<longrightarrow> s2"

  | RedWhileFalse: "\<lbrakk> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>my_guard, n_s\<rangle> \<Down> LitV (LBool False) \<rbrakk> \<Longrightarrow> 
                  A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>StructCmd (While my_guard stmts), Normal n_s\<rangle> \<longrightarrow> Normal n_s"
*)

(*
inductive red_stmt :: "'a absval_ty_fun \<Rightarrow> proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> stmt \<Rightarrow> 'a ast_state \<Rightarrow> 'a ast_state \<Rightarrow> bool" 
  ("_,_,_,_,_ \<turnstile> ((\<langle>_,_\<rangle>) \<longrightarrow>/ _)" [51,0,0,0] 81)
and  red_stmt_list :: "'a absval_ty_fun \<Rightarrow> proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> stmt list \<Rightarrow> 'a ast_state \<Rightarrow> 'a ast_state \<Rightarrow> bool"
  ("_,_,_,_,_ \<turnstile> ((\<langle>_,_\<rangle>) {\<rightarrow>}/ _)" [51,0,0,0] 81)
  for A :: "'a absval_ty_fun" and M :: proc_context and \<Lambda> :: var_context and \<Gamma> :: "'a fun_interp" and \<Omega> :: rtype_env
  where 
    RedSimpleCmdExtended: "red_cmd A M \<Lambda> \<Gamma> \<Omega> my_cmd s0 s1 \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(SimpleCmd my_cmd), (False, s0)\<rangle> \<longrightarrow> (False, s1)" 

  | RedSimpleCmdBreak: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>SimpleCmd my_cmd, (True, s0)\<rangle> \<longrightarrow> (True, s0)"

  | RedIfTrueContinue: "\<lbrakk> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>my_guard, n_s\<rangle> \<Down> LitV (LBool True);  A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>then_stmts, (False, (Normal n_s))\<rangle> {\<rightarrow>} (False, s') \<rbrakk> \<Longrightarrow> 
                  A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>StructCmd (If my_guard then_stmts else_stmts), (False, Normal n_s)\<rangle> \<longrightarrow> (False, s')"

  | RedIfFalseContinue: "\<lbrakk> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>my_guard, n_s\<rangle> \<Down> LitV (LBool False);  A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>else_stmts, (False, (Normal n_s))\<rangle> {\<rightarrow>} (False, s') \<rbrakk> \<Longrightarrow> 
                  A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>StructCmd (If my_guard then_stmts else_stmts), (False, Normal n_s)\<rangle> \<longrightarrow> (False, s')"

  | RedIfBreak: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>StructCmd (If my_guard then_stmts else_stmts), (True, s0)\<rangle> \<longrightarrow> (True, s0)"

  | RedWhileTrueExtended: "\<lbrakk> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>my_guard, n_s\<rangle> \<Down> LitV (LBool True); A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>stmts, (False, Normal n_s)\<rangle> {\<rightarrow>} (False, s1); A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>StructCmd (While my_guard stmts), (False, s1)\<rangle> \<longrightarrow> (False, s2) \<rbrakk> \<Longrightarrow> 
                  A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>StructCmd (While my_guard stmts), (False, Normal n_s)\<rangle> \<longrightarrow> (False, s2)"

  | RedWhileTrueBreak: "\<lbrakk> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>my_guard, n_s\<rangle> \<Down> LitV (LBool True); A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>stmts, (False, Normal n_s)\<rangle> {\<rightarrow>} (True, s1) \<rbrakk> \<Longrightarrow> 
                  A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>StructCmd (While my_guard stmts), (False, Normal n_s)\<rangle> \<longrightarrow> (False, s1)"

  | RedWhileFalseExtended: "\<lbrakk> (A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>my_guard, n_s\<rangle> \<Down> LitV (LBool False)) \<or> (break_flag = True) \<rbrakk> \<Longrightarrow> 
                  A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>StructCmd (While my_guard stmts), (break_flag,  Normal n_s)\<rangle> \<longrightarrow> (break_flag, (Normal n_s))"

  | RedUnlabeledBreak: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>StructCmd (Break None), (break_flag, s)\<rangle> \<longrightarrow> (True, s)"
*)

(* arrow symbols clash if the exact same syntax is used as in red_cmd and red_cmd_list *)
inductive red_bigblock :: "'a absval_ty_fun \<Rightarrow> proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> bigblock \<Rightarrow> 'a ast_state \<Rightarrow> 'a ast_state \<Rightarrow> bool" 
  ("_,_,_,_,_ \<turnstile> ((\<langle>_,_\<rangle>) \<longrightarrow>/ _)" [51,0,0,0] 81)
and  red_bigblock_list :: "'a absval_ty_fun \<Rightarrow> proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> bigblock list \<Rightarrow> 'a ast_state \<Rightarrow> 'a ast_state \<Rightarrow> bool"
  ("_,_,_,_,_ \<turnstile> ((\<langle>_,_\<rangle>) {\<rightarrow>}/ _)" [51,0,0,0] 81)
  for A :: "'a absval_ty_fun" and M :: proc_context and \<Lambda> :: var_context and \<Gamma> :: "'a fun_interp" and \<Omega> :: rtype_env
  where 
    RedSimpleBigBlockExt: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] s1 \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BigBlock my_name simple_cmds None None), (False, Normal n_s)\<rangle> \<longrightarrow> (False, s1)"

  (* combine all three skip rules *)
  | RedSimpleBigBlockBreak: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BigBlock my_name simple_cmds None None), (True, s1)\<rangle> \<longrightarrow> (True, s1)"

  | RedParsedIfTrueExt: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>my_guard, n_s1\<rangle> \<Down> LitV (LBool True);  A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>then_bigblocks, (False, Normal n_s1)\<rangle> {\<rightarrow>} (False, s2) \<rbrakk>  \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BigBlock my_name simple_cmds (Some (ParsedIf my_guard thenbigblocks elsebigblocks)) None), (False, Normal n_s)\<rangle> \<longrightarrow> (False, s2)"

  | RedParsedIfFalseExt: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>my_guard, n_s1\<rangle> \<Down> LitV (LBool False); A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>else_bigblocks, (False, Normal n_s1)\<rangle> {\<rightarrow>} (False, s2) \<rbrakk>  \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BigBlock my_name simple_cmds (Some (ParsedIf my_guard thenbigblocks elsebigblocks)) None), (False, Normal n_s)\<rangle> \<longrightarrow> (False, s2)"

  | RedParsedIfBreak: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BigBlock my_name simple_cmds (Some (ParsedIf my_guard thenbigblocks elsebigblocks)) None), (True, s1)\<rangle> \<longrightarrow> (True, s1)"

  (* invariants not considered here *)
  | RedParsedWhileTrueExt: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>my_guard, n_s1\<rangle> \<Down> LitV (LBool True); A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>bigblocks, (False, Normal n_s1)\<rangle> {\<rightarrow>} (False, s2); A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>BigBlock some_name simple_cmds (Some (ParsedWhile my_guard my_invariants bigblocks)) None, (False, s2)\<rangle> \<longrightarrow> (False, s3)  \<rbrakk>  \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BigBlock my_name simple_cmds (Some (ParsedWhile my_guard my_invariants bigblocks)) None), (False, Normal n_s)\<rangle> \<longrightarrow> (False, s3)"

  | RedParsedWhileTrueBreak: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>my_guard, n_s1\<rangle> \<Down> LitV (LBool True); A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>bigblocks, (False, Normal n_s1)\<rangle> {\<rightarrow>} (True, s2) \<rbrakk>  \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BigBlock my_name simple_cmds (Some (ParsedWhile my_guard my_invariants bigblocks)) None), (False, Normal n_s)\<rangle> \<longrightarrow> (False, s2)"
  
  | RedParsedWhileFalseExt: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>my_guard, n_s1\<rangle> \<Down> LitV (LBool False) \<rbrakk>  \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BigBlock my_name simple_cmds (Some (ParsedWhile my_guard my_invariants bigblocks)) None), (False, Normal n_s)\<rangle> \<longrightarrow> (False, Normal n_s1)"

  | RedParsedWhileBreak: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BigBlock my_name simple_cmds (Some (ParsedWhile my_guard my_invariants bigblocks)) None), (True, s1)\<rangle> \<longrightarrow> (True, s1)"

  | RedUnlabeledBreak: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(BigBlock my_name simple_cmds (Some (ParsedBreak None)) None), (False, Normal n_s)\<rangle> \<longrightarrow> (True, Normal n_s1)"


(* I don't know if we need to reduce the ast the same way we reduce the cfg but I put it here anyway  *)

type_synonym 'a ast_config = "bigblock list \<times> ('a ast_state)"

inductive red_ast :: "'a absval_ty_fun \<Rightarrow> proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> 'a ast_config \<Rightarrow> 'a ast_config \<Rightarrow> bool"
  ("_,_,_,_,_ \<turnstile> (_ -b\<rightarrow>/ _)" [51,0,0,0] 81)
  for A :: "'a absval_ty_fun" and M :: proc_context and \<Lambda> :: var_context and \<Gamma> :: "'a fun_interp" and \<Omega> :: rtype_env
  where
    RedNormalSucc: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>bigblock0, (break_flag_begin, Normal ns)\<rangle> \<longrightarrow> (break_flag_after, Normal ns') \<rbrakk> \<Longrightarrow> 
              A,M,\<Lambda>,\<Gamma>,\<Omega>  \<turnstile> ((bigblock0 # bigblocks),break_flag_begin, Normal ns) -b\<rightarrow> (bigblocks, (break_flag_after, Normal ns'))"
  | RedNormalReturn: "\<lbrakk>node_to_bigblock(G)! n = bigblock0; A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>bigblock0, (break_flag_begin, Normal ns)\<rangle> \<longrightarrow> (break_flag_after, Normal ns'); (trivial_out_edges(G) ! n) = [] \<rbrakk> \<Longrightarrow> 
               A,M,\<Lambda>,\<Gamma>,\<Omega>,G  \<turnstile> (Inl n, (break_flag_begin, Normal ns)) -b\<rightarrow> (Inr (), (break_flag_after, Normal ns'))"
  | RedFailure: "\<lbrakk>node_to_bigblock(G) ! n = bigblock0; A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>bigblock0, (break_flag_begin, Normal ns)\<rangle> \<longrightarrow> (break_flag_after, Failure) \<rbrakk> \<Longrightarrow>
              A,M,\<Lambda>,\<Gamma>,\<Omega>,G  \<turnstile> (Inl n, (break_flag_begin, Normal ns)) -b\<rightarrow> (Inr (), (break_flag_after, Failure))"
  | RedMagic: "\<lbrakk>node_to_bigblock(G) ! n = bigblock0; A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>bigblock0, (break_flag_begin, Normal ns)\<rangle> \<longrightarrow> (break_flag_after, Magic) \<rbrakk> \<Longrightarrow>
              A,M,\<Lambda>,\<Gamma>,\<Omega>,G  \<turnstile> (Inl n, (break_flag_begin, Normal ns)) -b\<rightarrow> (Inr (), (break_flag_after, Magic))"

end
