theory Ast
  imports Main Semantics Lang

begin

type_synonym name = string
type_synonym label = string
type_synonym guard = expr
type_synonym invariant = expr

datatype transfer_cmd
 = Goto label

datatype parsed_structured_cmd
 = ParsedIf guard "bigblock list" "bigblock list"
 | ParsedWhile guard "invariant list" "bigblock list"
 | ParsedBreak "label option"

and bigblock 
 = Leave (* a special block that's only used internally; used for reducing a while loop *)
 | BigBlock "name option" "cmd list" "parsed_structured_cmd option" "transfer_cmd option"

type_synonym ast = "bigblock list"

(* continuations; used for formalizing Gotos and labeled Breaks *)
datatype cont 
 = KStop 
 | KSeq "bigblock list" cont
 | KEndBlock cont cont

type_synonym break_flag = bool
type_synonym 'a ast_state = "break_flag * ast  * bigblock  * cont * ('a state)"

(* auxillary function to find the label a goto statement is referring to *)
fun find_label :: "label \<Rightarrow> bigblock list \<Rightarrow> cont \<Rightarrow> ((bigblock * cont) option)" where
  (* this first case should be impossible because we can't have a structured cmd and a transfer cmd at the same time *)
  "find_label lbl ((BigBlock bb_name cmds (Some s) (Some t)) # bs) cont = None" |
  (* TODO: figure out examples of when this case could be entered *)
  "find_label lbl [] cont = None" |
  "find_label lbl (Leave # bs) cont = find_label lbl bs cont" |
  "find_label lbl ((BigBlock bb_name cmds None None) # []) cont = (if (Some lbl = bb_name) then ( Some ((BigBlock bb_name cmds None None), cont)) else (None))" |
  "find_label lbl ((BigBlock bb_name cmds None None) # bs) cont = (if (Some lbl = bb_name) then ( Some ((BigBlock bb_name cmds None None), (KSeq bs cont))) else (find_label lbl bs cont))" |
  "find_label lbl ((BigBlock bb_name cmds (Some (ParsedIf guard then_bbs else_bbs)) None) # bs) cont = (if (Some lbl = bb_name) then (Some ((BigBlock bb_name cmds (Some (ParsedIf guard then_bbs else_bbs)) None), (KSeq bs cont))) else (if (find_label lbl then_bbs cont \<noteq> None) then (find_label lbl then_bbs (KSeq bs cont)) else (find_label lbl else_bbs (KSeq bs cont))))" |
  (* TODO: the continuation here may not be correct, think about it *)
  "find_label lbl ((BigBlock bb_name cmds (Some (ParsedWhile guard invariants body_bbs)) None) # bs) cont = (if (Some lbl = bb_name) then (Some ((BigBlock bb_name cmds (Some (ParsedWhile guard invariants body_bbs)) None), (KSeq bs cont))) else (find_label lbl body_bbs (KSeq bs cont)))" |
  (* TODO: combine the two cases below with the 4th case as they all do the same. How? *)
  "find_label lbl ((BigBlock bb_name cmds (Some break_stmt) None) # bs) cont = (if (Some lbl = bb_name) then ( Some ((BigBlock bb_name cmds (Some break_stmt) None), (KSeq bs cont))) else (find_label lbl bs cont))" |
  "find_label lbl ((BigBlock bb_name cmds None (Some transfer_stmt)) # bs) cont = (if (Some lbl = bb_name) then ( Some ((BigBlock bb_name cmds None (Some transfer_stmt)), (KSeq bs cont))) else (find_label lbl bs cont))"

(* function defining the semantics of bigblocks; small-step semantics *)
(* arrow symbols in the 'syntactic sugar' clash if the exact same syntax is used as in red_cmd *)
inductive red_bigblock :: "'a absval_ty_fun \<Rightarrow> proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env  \<Rightarrow> 'a ast_state \<Rightarrow> 'a ast_state \<Rightarrow> bool" 
  ("_,_,_,_,_ \<turnstile> ((\<langle>_\<rangle>) \<longrightarrow>/ _)" [51,0,0,0] 81)
  for A :: "'a absval_ty_fun" and M :: proc_context and \<Lambda> :: var_context and \<Gamma> :: "'a fun_interp" and \<Omega> :: rtype_env
  where 
    (* this first rule exists only because I don't know how to reduce a while_false block or a simple block without a skip command *)
    RedSkipBlock: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(False, ast, (BigBlock None [Skip] None None),  (KSeq (b # bs) cont0),  Normal n_s)\<rangle> \<longrightarrow> (False, ast, b, (KSeq bs cont0), Normal n_s)"

  | RedLeaveTrue: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(True, ast, Leave, cont0,  Normal n_s)\<rangle> \<longrightarrow> (False, ast, (BigBlock None [Skip] None None), cont0, Normal n_s)"

  | RedLeaveFalse: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(False, ast, Leave, cont0,  Normal n_s)\<rangle> \<longrightarrow> (False, ast, (BigBlock None [Skip] None None), cont0, Normal n_s)"  

  | RedSimpleBigBlockExt: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] s1 \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(False, ast, (BigBlock my_name simple_cmds None None),  cont0,  Normal n_s)\<rangle> \<longrightarrow> (False, ast, (BigBlock None [Skip] None None), cont0, s1)"

  | RedBreakFlagSet: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(True, ast, (BigBlock my_name simple_cmds any_str any_tr), cont0, s1)\<rangle> \<longrightarrow> (True, ast, (BigBlock None [Skip] None None), cont0,  s1)"

  | RedParsedIfTrueExt: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>my_guard, n_s1\<rangle> \<Down> LitV (LBool True) \<rbrakk>  \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(False, ast, (BigBlock my_name simple_cmds (Some (ParsedIf my_guard (then_hd # then_bbs) elsebigblocks)) None), cont0, Normal n_s)\<rangle> \<longrightarrow> (False, ast, then_hd, (KSeq then_bbs cont0), Normal n_s1)"

  | RedParsedIfFalseExt: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>my_guard, n_s1\<rangle> \<Down> LitV (LBool False) \<rbrakk>  \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(False, ast, (BigBlock my_name simple_cmds (Some (ParsedIf my_guard thenbigblocks (else_hd # else_bbs))) None), cont0, Normal n_s)\<rangle> \<longrightarrow> (False, ast, else_hd, (KSeq else_bbs cont0), Normal n_s1)"
 
  (* invariants not considered here *)
  | RedParsedWhileTrueExt: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>my_guard, n_s1\<rangle> \<Down> LitV (LBool True) \<rbrakk>  \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(False, ast, (BigBlock my_name simple_cmds (Some (ParsedWhile my_guard my_invariants (bb_hd # body_bbs))) None), cont0,  Normal n_s)\<rangle> \<longrightarrow> (False, ast, bb_hd, (KSeq (body_bbs @ (Leave # [(BigBlock my_name [] (Some (ParsedWhile my_guard my_invariants (bb_hd # body_bbs))) None)])) cont0), Normal n_s1)"
  
  | RedParsedWhileFalseExt: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>my_guard, n_s1\<rangle> \<Down> LitV (LBool False) \<rbrakk>  \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(False, ast, (BigBlock my_name simple_cmds (Some (ParsedWhile my_guard my_invariants bigblocks)) None), cont0, Normal n_s)\<rangle> \<longrightarrow> (False, ast, (BigBlock None [Skip] None None), cont0, Normal n_s1)"

  | RedUnlabeledBreak: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(False, ast, (BigBlock my_name simple_cmds (Some (ParsedBreak None)) None), cont0, Normal n_s)\<rangle> \<longrightarrow> (True, ast, (BigBlock None [Skip] None None), cont0, Normal n_s1)"

  | RedGoto: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); (find_label label ast cont0) = Some (found_bigblock, found_cont) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(False, ast, (BigBlock my_name simple_cmds None (Some (Goto label))),  cont0,  Normal n_s)\<rangle> \<longrightarrow> (False, ast, found_bigblock, found_cont, (Normal n_s1))"


(* TODO: rework or remove the function below *)
type_synonym 'a ast_config = "bigblock list \<times> ('a ast_state)"

(*
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
*)

end
