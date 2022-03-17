theory Ast
  imports Main Semantics Lang

begin

type_synonym name = string
type_synonym label = string
type_synonym guard = expr
type_synonym invariant = expr

datatype transfer_cmd
 = Goto label
 | Return "expr option"

datatype parsed_structured_cmd
 = ParsedIf "guard option" "bigblock list" "bigblock list"
 | ParsedWhile "guard option" "invariant list" "bigblock list"
 | ParsedBreak nat
 | WhileWrapper parsed_structured_cmd

and bigblock 
 = BigBlock "name option" "cmd list" "parsed_structured_cmd option" "transfer_cmd option"

type_synonym ast = "bigblock list"

(* continuations; used for formalizing Gotos and numbered Breaks *)
datatype cont 
 = KStop 
 | KSeq "bigblock list" cont
 | KEndBlock cont 

type_synonym 'a ast_state = "ast  * bigblock  * cont * ('a state)"

(* auxillary function to check if the invariants of a loop hold true *)
fun red_invariants :: "'a absval_ty_fun \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env  \<Rightarrow> 'a nstate \<Rightarrow> invariant list \<Rightarrow> bool" where
    "red_invariants A \<Lambda> \<Gamma> \<Omega> n_s [] = True"
  | "red_invariants A \<Lambda> \<Gamma> \<Omega> n_s (i # invs) = (if (A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>i, n_s\<rangle> \<Down> LitV (LBool True)) then (red_invariants A \<Lambda> \<Gamma> \<Omega> n_s invs) else False)"
    

(* auxillary function to find the label a Goto statement is referring to *)
fun find_label :: "label \<Rightarrow> bigblock list \<Rightarrow> cont \<Rightarrow> ((bigblock * cont) option)" where
    "find_label lbl [] cont = None" 
  | "find_label lbl ((BigBlock bb_name cmds None None) # []) cont = (if (Some lbl = bb_name) then (Some ((BigBlock bb_name cmds None None), cont)) else (None))" 
  | "find_label lbl ((BigBlock bb_name cmds None None) # bs) cont = (if (Some lbl = bb_name) then (Some ((BigBlock bb_name cmds None None), (KSeq bs cont))) else (find_label lbl bs cont))" 
  | "find_label lbl ((BigBlock bb_name cmds (Some (ParsedIf guard then_bbs else_bbs)) None) # bs) cont = (if (Some lbl = bb_name) then (Some ((BigBlock bb_name cmds (Some (ParsedIf guard then_bbs else_bbs)) None), (KSeq bs cont))) else (if (find_label lbl then_bbs cont \<noteq> None) then (find_label lbl (then_bbs @ bs) cont) else (find_label lbl (else_bbs @ bs) cont)))" 
  | "find_label lbl ((BigBlock bb_name cmds (Some (ParsedWhile guard invariants body_bbs)) None) # bs) cont = (if (Some lbl = bb_name) then (Some ((BigBlock bb_name cmds (Some (ParsedWhile guard invariants body_bbs)) None), (KSeq bs cont))) else (if (find_label lbl body_bbs cont \<noteq> None) then (find_label lbl body_bbs (KSeq ((BigBlock None [] (Some (ParsedWhile guard invariants body_bbs)) None) # bs) cont)) else (find_label lbl bs cont)))"  
  | "find_label lbl ((BigBlock bb_name cmds (Some (ParsedBreak n)) None) # bs) cont = (if (Some lbl = bb_name) then (Some ((BigBlock bb_name cmds (Some (ParsedBreak n)) None), (KSeq bs cont))) else (find_label lbl bs cont))" 
  | "find_label lbl ((BigBlock bb_name cmds (Some (WhileWrapper while_loop)) None) # bs) cont = find_label lbl ((BigBlock bb_name cmds (Some while_loop) None) # bs) cont"
  | "find_label lbl ((BigBlock bb_name cmds None (Some transfer_stmt)) # bs) cont = (if (Some lbl = bb_name) then (Some ((BigBlock bb_name cmds None (Some transfer_stmt)), (KSeq bs cont))) else (find_label lbl bs cont))"
  | "find_label lbl ((BigBlock bb_name cmds (Some s) (Some t)) # bs) cont = None"


(* function defining the semantics of bigblocks; small-step semantics *)
(* Note: arrow symbols in the 'syntactic sugar' clash if the exact same syntax is used as in red_cmd *)
inductive red_bigblock :: "'a absval_ty_fun \<Rightarrow> proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env  \<Rightarrow> 'a ast_state \<Rightarrow> 'a ast_state \<Rightarrow> bool" 
  ("_,_,_,_,_ \<turnstile> ((\<langle>_\<rangle>) \<longrightarrow>/ _)" [51,0,0,0] 81)
  for A :: "'a absval_ty_fun" and M :: proc_context and \<Lambda> :: var_context and \<Gamma> :: "'a fun_interp" and \<Omega> :: rtype_env
  where 
    RedSkipBlock: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock None [] None None),  (KSeq (b # bs) cont0),  Normal n_s)\<rangle> \<longrightarrow> (ast, b, (KSeq bs cont0), Normal n_s)"

  | RedSkipEndBlock: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock None [] None None),  (KEndBlock cont0),  Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] None None), cont0, Normal n_s)"

  | RedReturn: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] s1 \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock my_name simple_cmds None (Some (Return val))),  cont0, Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] None None), KStop, s1)"

  | RedSimpleBigBlock: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] s1 \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock my_name simple_cmds None None),  cont0,  Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] None None), cont0, s1)"

  | RedParsedIfTrue: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); my_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s1\<rangle> \<Down> LitV (LBool True) \<rbrakk>  \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock my_name simple_cmds (Some (ParsedIf my_guard (then_hd # then_bbs) elsebigblocks)) None), cont0, Normal n_s)\<rangle> \<longrightarrow> (ast, then_hd, (KSeq then_bbs cont0), Normal n_s1)"

  | RedParsedIfFalse: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1);my_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s1\<rangle> \<Down> LitV (LBool False) \<rbrakk>  \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock my_name simple_cmds (Some (ParsedIf my_guard thenbigblocks (else_hd # else_bbs))) None), cont0, Normal n_s)\<rangle> \<longrightarrow> (ast, else_hd, (KSeq else_bbs cont0), Normal n_s1)"
 
  (* invariants processed in a strange way *)
  | RedParsedWhileTrue: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); my_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s1\<rangle> \<Down> LitV (LBool True); (red_invariants A \<Lambda> \<Gamma> \<Omega> n_s1 my_invariants) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock my_name simple_cmds (Some (ParsedWhile my_guard my_invariants (bb_hd # body_bbs))) None), cont0,  Normal n_s)\<rangle> \<longrightarrow> (ast, bb_hd, (KSeq body_bbs (KSeq [(BigBlock my_name [] (Some (ParsedWhile my_guard my_invariants (bb_hd # body_bbs))) None)] cont0)), Normal n_s1)"

  | RedParsedWhileWrapperTrue: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); my_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s1\<rangle> \<Down> LitV (LBool True); (red_invariants A \<Lambda> \<Gamma> \<Omega> n_s1 my_invariants) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock my_name simple_cmds (Some (WhileWrapper (ParsedWhile my_guard my_invariants (bb_hd # body_bbs)))) None), cont0,  Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock my_name simple_cmds (Some (ParsedWhile my_guard my_invariants (bb_hd # body_bbs))) None), (KEndBlock cont0),  Normal n_s1)"

  | RedParsedWhileFalse: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); my_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s1\<rangle> \<Down> LitV (LBool False) \<rbrakk>  \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock my_name simple_cmds (Some (ParsedWhile my_guard my_invariants bigblocks)) None), cont0, Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] None None), cont0, Normal n_s1)"

  | RedParsedWhileWrapperFalse: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); my_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s1\<rangle> \<Down> LitV (LBool False) \<rbrakk>  \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock my_name simple_cmds (Some (WhileWrapper (ParsedWhile my_guard my_invariants bigblocks))) None), cont0, Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] None None), cont0, Normal n_s1)"

  | RedBreak0: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock my_name simple_cmds (Some (ParsedBreak 0)) None), (KEndBlock cont0), Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] None None), cont0, Normal n_s1)"

  | RedBreakN: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock my_name simple_cmds (Some (ParsedBreak n)) None), (KSeq (b # bbs) cont0), Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] (Some (ParsedBreak n)) None), cont0, Normal n_s1)"

  | RedBreakNPlus1: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock my_name simple_cmds (Some (ParsedBreak (n + 1))) None), (KEndBlock cont0), Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] (Some (ParsedBreak n)) None), cont0, Normal n_s1)"

  | RedGoto: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); (find_label label ast KStop) = Some (found_bigblock, found_cont) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock my_name simple_cmds None (Some (Goto label))),  cont0,  Normal n_s)\<rangle> \<longrightarrow> (ast, found_bigblock, found_cont, (Normal n_s1))"

(* function defining how to reduce an ast *)
inductive red_bigblock_list :: "'a absval_ty_fun \<Rightarrow> proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env  \<Rightarrow> bigblock list  \<Rightarrow> cont \<Rightarrow> 'a ast_state \<Rightarrow> bool" 
  ("_,_,_,_,_ \<turnstile> ((\<langle>_,_\<rangle>) \<longrightarrow>/ _)" [51,0,0,0] 81)
  for A :: "'a absval_ty_fun" and M :: proc_context and \<Lambda> :: var_context and \<Gamma> :: "'a fun_interp" and \<Omega> :: rtype_env
  where 
    RedEmpty:  "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>[], cont\<rangle> \<longrightarrow> ([], (BigBlock None [] None None), cont, Normal n_s)"

  | RedAst: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(b # bs), cont\<rangle> \<longrightarrow> ((b # bs), b, (KSeq bs cont), Normal n_s)"

end
