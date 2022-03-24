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

(* auxillary function to find the label a Goto statement is referring to *)
fun find_label :: "label \<Rightarrow> bigblock list \<Rightarrow> cont \<Rightarrow> ((bigblock * cont) option)" where
    "find_label lbl [] cont = None" 
  | "find_label lbl ((BigBlock bb_name cmds None None) # []) cont = (if (Some lbl = bb_name) then (Some ((BigBlock bb_name cmds None None), cont)) else (None))" 
  | "find_label lbl ((BigBlock bb_name cmds None None) # bbs) cont = (if (Some lbl = bb_name) then (Some ((BigBlock bb_name cmds None None), (KSeq bbs cont))) else (find_label lbl bbs cont))" 
  | "find_label lbl ((BigBlock bb_name cmds (Some (ParsedIf guard then_bbs else_bbs)) None) # bbs) cont = (if (Some lbl = bb_name) then (Some ((BigBlock bb_name cmds (Some (ParsedIf guard then_bbs else_bbs)) None), (KSeq bbs cont))) else (if (find_label lbl then_bbs cont \<noteq> None) then (find_label lbl (then_bbs @ bbs) cont) else (find_label lbl (else_bbs @ bbs) cont)))" 
  | "find_label lbl ((BigBlock bb_name cmds (Some (ParsedWhile guard invariants body_bbs)) None) # bbs) cont = (if (Some lbl = bb_name) then (Some ((BigBlock bb_name cmds (Some (ParsedWhile guard invariants body_bbs)) None), (KSeq bbs cont))) else (if (find_label lbl body_bbs cont \<noteq> None) then (find_label lbl body_bbs (KSeq ((BigBlock None [] (Some (ParsedWhile guard invariants body_bbs)) None) # bbs) cont)) else (find_label lbl bbs cont)))"  
  | "find_label lbl ((BigBlock bb_name cmds (Some (ParsedBreak n)) None) # bbs) cont = (if (Some lbl = bb_name) then (Some ((BigBlock bb_name cmds (Some (ParsedBreak n)) None), (KSeq bbs cont))) else (find_label lbl bbs cont))" 
  | "find_label lbl ((BigBlock bb_name cmds (Some (WhileWrapper while_loop)) None) # bbs) cont = find_label lbl ((BigBlock bb_name cmds (Some while_loop) None) # bbs) cont"
  | "find_label lbl ((BigBlock bb_name cmds None (Some transfer_stmt)) # bbs) cont = (if (Some lbl = bb_name) then (Some ((BigBlock bb_name cmds None (Some transfer_stmt)), (KSeq bbs cont))) else (find_label lbl bbs cont))"
  | "find_label lbl ((BigBlock bb_name cmds (Some s) (Some t)) # bbs) cont = None"


(* function defining the semantics of bigblocks; small-step semantics *)
(* Note: arrow symbols in the 'syntactic sugar' clash if the exact same syntax is used as in red_cmd *)
inductive red_bigblock :: "'a absval_ty_fun \<Rightarrow> proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env  \<Rightarrow> 'a ast_state \<Rightarrow> 'a ast_state \<Rightarrow> bool" 
  ("_,_,_,_,_ \<turnstile> ((\<langle>_\<rangle>) \<longrightarrow>/ _)" [51,0,0,0] 81)
  for A :: "'a absval_ty_fun" and M :: proc_context and \<Lambda> :: var_context and \<Gamma> :: "'a fun_interp" and \<Omega> :: rtype_env
  where 
    RedFailure_or_Magic: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] s1; (s1 = Magic) \<or> (s1 = Failure) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock bb_name simple_cmds str_cmd tr_cmd),  cont0, Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] None None), KStop, s1)"
  
  | RedSkip: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock None [] None None),  (KSeq (b # bbs) cont0),  Normal n_s)\<rangle> \<longrightarrow> (ast, b, (KSeq bbs cont0), Normal n_s)"

  | RedSkipEndBlock: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock None [] None None),  (KEndBlock cont0),  Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] None None), cont0, Normal n_s)"

  | RedReturn: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock bb_name simple_cmds None (Some (Return val))),  cont0, Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] None None), KStop, Normal n_s1)"

  | RedSimpleBigBlock: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock bb_name simple_cmds None None),  cont0,  Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] None None), cont0, Normal n_s1)"

  | RedParsedIfTrue: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); bb_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s1\<rangle> \<Down> LitV (LBool True) \<rbrakk>  \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock bb_name simple_cmds (Some (ParsedIf bb_guard (then_hd # then_bbs) elsebigblocks)) None), cont0, Normal n_s)\<rangle> \<longrightarrow> (ast, then_hd, (KSeq then_bbs cont0), Normal n_s1)"

  | RedParsedIfFalse: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); bb_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s1\<rangle> \<Down> LitV (LBool False) \<rbrakk>  \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock bb_name simple_cmds (Some (ParsedIf bb_guard thenbigblocks (else_hd # else_bbs))) None), cont0, Normal n_s)\<rangle> \<longrightarrow> (ast, else_hd, (KSeq else_bbs cont0), Normal n_s1)"

  | RedParsedWhileWrapper: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock bb_name simple_cmds (Some (WhileWrapper (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs)))) None), cont0,  Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock bb_name simple_cmds (Some (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs))) None), (KEndBlock cont0),  Normal n_s)"
 
  (* invariants processed using auxillary function *)
  | RedParsedWhile_InvFail: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); bb_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s1\<rangle> \<Down> LitV (LBool True); (expr_all_sat A \<Lambda> \<Gamma> \<Omega> n_s  bb_invariants) = False \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock bb_name simple_cmds (Some (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs))) None), cont0,  Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] None None), KStop, Failure)"

  | RedParsedWhileTrue: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); bb_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s1\<rangle> \<Down> LitV (LBool True); (expr_all_sat A \<Lambda> \<Gamma> \<Omega> n_s  bb_invariants) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock bb_name simple_cmds (Some (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs))) None), cont0,  Normal n_s)\<rangle> \<longrightarrow> (ast, bb_hd, (KSeq (body_bbs @ [(BigBlock bb_name [] (Some (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs))) None)]) cont0), Normal n_s1)"

  | RedParsedWhileFalse: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); bb_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s1\<rangle> \<Down> LitV (LBool False) \<rbrakk>  \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock bb_name simple_cmds (Some (ParsedWhile bb_guard bb_invariants bigblocks)) None), cont0, Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] None None), cont0, Normal n_s1)"

  | RedBreak0: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock bb_name simple_cmds (Some (ParsedBreak 0)) None), (KEndBlock cont0), Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] None None), cont0, Normal n_s1)"

  | RedBreakN: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock bb_name simple_cmds (Some (ParsedBreak n)) None), (KSeq (b # bbs) cont0), Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] (Some (ParsedBreak n)) None), cont0, Normal n_s1)"

  | RedBreakNPlus1: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock bb_name simple_cmds (Some (ParsedBreak (n + 1))) None), (KEndBlock cont0), Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] (Some (ParsedBreak n)) None), cont0, Normal n_s1)"

  | RedGoto: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); (find_label label ast KStop) = Some (found_bigblock, found_cont) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock bb_name simple_cmds None (Some (Goto label))),  cont0,  Normal n_s)\<rangle> \<longrightarrow> (ast, found_bigblock, found_cont, (Normal n_s1))"

(* function defining how to reduce an ast *)
inductive red_bigblock_list :: "'a absval_ty_fun \<Rightarrow> proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env  \<Rightarrow> bigblock list  \<Rightarrow> cont \<Rightarrow> 'a ast_state \<Rightarrow> bool" 
  ("_,_,_,_,_ \<turnstile> ((\<langle>_,_\<rangle>) \<longrightarrow>/ _)" [51,0,0,0] 81)
  for A :: "'a absval_ty_fun" and M :: proc_context and \<Lambda> :: var_context and \<Gamma> :: "'a fun_interp" and \<Omega> :: rtype_env
  where 
    RedEmpty:  "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>[], cont\<rangle> \<longrightarrow> ([], (BigBlock None [] None None), cont, Normal n_s)"

  | RedAst: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(b # bbs), cont\<rangle> \<longrightarrow> ((b # bbs), b, (KSeq bbs cont), Normal n_s)"

end
