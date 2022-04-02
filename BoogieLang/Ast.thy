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
  | RedParsedWhile_InvFail: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); bb_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s1\<rangle> \<Down> LitV (LBool True); (expr_all_sat A \<Lambda> \<Gamma> \<Omega> n_s1  bb_invariants) = False \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock bb_name simple_cmds (Some (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs))) None), cont0,  Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] None None), KStop, Failure)"

  | RedParsedWhileTrue: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); bb_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s1\<rangle> \<Down> LitV (LBool True); (expr_all_sat A \<Lambda> \<Gamma> \<Omega> n_s1  bb_invariants) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock bb_name simple_cmds (Some (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs))) None), cont0,  Normal n_s)\<rangle> \<longrightarrow> (ast, bb_hd, (KSeq (body_bbs @ [(BigBlock bb_name [] (Some (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs))) None)]) cont0), Normal n_s1)"

  | RedParsedWhileFalse: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); bb_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s1\<rangle> \<Down> LitV (LBool False) \<rbrakk>  \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock bb_name simple_cmds (Some (ParsedWhile bb_guard bb_invariants bigblocks)) None), cont0, Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] None None), cont0, Normal n_s1)"

  | RedBreak0: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock bb_name simple_cmds (Some (ParsedBreak 0)) None), (KEndBlock cont0), Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] None None), cont0, Normal n_s1)"

  | RedBreakN: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock bb_name simple_cmds (Some (ParsedBreak n)) None), (KSeq (b # bbs) cont0), Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] (Some (ParsedBreak n)) None), cont0, Normal n_s1)"

  | RedBreakNPlus1: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock bb_name simple_cmds (Some (ParsedBreak (n + 1))) None), (KEndBlock cont0), Normal n_s)\<rangle> \<longrightarrow> (ast, (BigBlock None [] (Some (ParsedBreak n)) None), cont0, Normal n_s1)"

  | RedGoto: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>simple_cmds, (Normal n_s)\<rangle> [\<rightarrow>] (Normal n_s1); (find_label label ast KStop) = Some (found_bigblock, found_cont) \<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>(ast, (BigBlock bb_name simple_cmds None (Some (Goto label))),  cont0,  Normal n_s)\<rangle> \<longrightarrow> (ast, found_bigblock, found_cont, (Normal n_s1))"

(* defining correctness of the AST *)
fun get_state :: "'a ast_state \<Rightarrow> 'a state"
  where
    "get_state (ast, bb, cont, s1) = s1"

fun is_final :: "'a ast_state \<Rightarrow> bool" 
  where
    "is_final (ast, (BigBlock None [] None None), KStop, s1) = True"
  | "is_final other = False"

fun init_ast :: "ast \<Rightarrow> 'a nstate \<Rightarrow> 'a ast_state"
  where
    "init_ast [] ns1 = ([], (BigBlock None [] None None), KStop, Normal ns1)"
  | "init_ast (b#bbs) ns1 = ((b#bbs), b, KStop, Normal ns1)"

definition valid_configuration 
  where "valid_configuration A \<Lambda> \<Gamma> \<Omega> posts ast_state \<equiv> 
         (get_state ast_state) \<noteq> Failure \<and> 
         (is_final ast_state \<longrightarrow> (\<forall>ns'. (get_state ast_state) = Normal ns' \<longrightarrow> expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns' posts))"

definition proc_body_satisfies_spec :: "'a absval_ty_fun \<Rightarrow> proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> expr list \<Rightarrow> expr list \<Rightarrow> ast \<Rightarrow> 'a nstate \<Rightarrow> bool"
  where "proc_body_satisfies_spec A M \<Lambda> \<Gamma> \<Omega> pres posts (ast) ns \<equiv>
         expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns pres \<longrightarrow> 
          (\<forall> ast_reached. (rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega>) (init_ast ast ns) ast_reached) \<longrightarrow> 
                    valid_configuration A \<Lambda> \<Gamma> \<Omega> posts ast_reached)"

record ast_procedure =
  proc_ty_args :: nat
  proc_args :: vdecls
  proc_rets :: vdecls
  proc_modifs :: "vname list"
  proc_pres :: "(expr \<times> bool) list" 
  proc_posts :: "(expr \<times> bool) list"
  proc_body :: "(vdecls \<times> ast) option"

fun proc_all_pres :: "ast_procedure \<Rightarrow> expr list"
  where "proc_all_pres p = map fst (proc_pres p)"

fun proc_checked_posts :: "ast_procedure \<Rightarrow> expr list"
  where "proc_checked_posts p = map fst (filter (\<lambda>x. \<not> snd(x)) (proc_posts p))"

fun proc_is_correct :: "'a absval_ty_fun \<Rightarrow> fdecls \<Rightarrow> vdecls \<Rightarrow> vdecls \<Rightarrow> axiom list \<Rightarrow> ast_procedure \<Rightarrow> bool"
  where 
    "proc_is_correct A fun_decls constants global_vars axioms proc =
      (case proc_body(proc) of
        Some (locals, ast) \<Rightarrow>
          ( ( (\<forall>t. closed t \<longrightarrow> (\<exists>v. type_of_val A (v :: 'a val) = t)) \<and> (\<forall>v. closed ((type_of_val A) v)) ) \<longrightarrow>
          (\<forall> \<Gamma>. fun_interp_wf A fun_decls \<Gamma> \<longrightarrow>
          (
             (\<forall>\<Omega> gs ls. (list_all closed \<Omega> \<and> length \<Omega> = proc_ty_args proc) \<longrightarrow>        
             (state_typ_wf A \<Omega> gs (constants @ global_vars) \<longrightarrow>
              state_typ_wf A \<Omega> ls ((proc_args proc)@ (locals @ proc_rets proc)) \<longrightarrow>
              (axioms_sat A (constants, []) \<Gamma> (global_to_nstate (state_restriction gs constants)) axioms) \<longrightarrow>            
              proc_body_satisfies_spec A [] (constants@global_vars, (proc_args proc)@(locals@(proc_rets proc))) \<Gamma> \<Omega> 
                                       (proc_all_pres proc) (proc_checked_posts proc) ast 
                                       \<lparr>old_global_state = gs, global_state = gs, local_state = ls, binder_state = Map.empty\<rparr> )
            )
          )))
      | None \<Rightarrow> True)"


inductive ast_cfg_rel_block_list :: "mbodyCFG \<Rightarrow> ast \<Rightarrow> bigblock list \<Rightarrow> block \<Rightarrow> block list \<Rightarrow> bool"
  ("_,_ \<turnstile> (\<langle>_\<rangle> [\<leadsto>]/ _, _)" [51,0,0,0] 81)
  for G :: "mbodyCFG"
  where      
     RelateEmpty: "G, ast \<turnstile> \<langle>[]\<rangle> [\<leadsto>] [], []"

    (* what's the output of out_edges if there are no successors? *)
    | RelateSimpleBlock: "\<lbrakk> (node_to_block(G) ! n) = cmds; List.member (out_edges(G) ! n) n'; G, ast \<turnstile> \<langle>b#bbs\<rangle> [\<leadsto>] node_to_block(G) ! n', exit \<rbrakk> \<Longrightarrow>  G, ast \<turnstile> \<langle>(BigBlock _ cmds None None)#(b#bbs)\<rangle> [\<leadsto>] (node_to_block(G) ! n), exit"

    | RelateIfBlockNoGuard: "\<lbrakk> (node_to_block(G) ! n) = cmds; List.member (out_edges(G) ! n) n1; List.member (out_edges(G) ! n) n2; (node_to_block(G) ! n1) = then_beginning; (node_to_block(G) ! n2) = else_beginning; G, ast \<turnstile> \<langle>then_bbs @ (b#bbs)\<rangle> [\<leadsto>] then_beginning, end_then; G, ast \<turnstile> \<langle>else_bbs @ (b#bbs)\<rangle> [\<leadsto>] else_beginning, end_else \<rbrakk> \<Longrightarrow>  G, ast \<turnstile> \<langle>(BigBlock _ cmds (Some (ParsedIf None then_bbs else_bbs)) None)#(b#bbs)\<rangle> [\<leadsto>] (node_to_block(G) ! n), (end_then @ end_else)"
    
    | RelateIfBlock: "\<lbrakk> (node_to_block(G) ! n) = cmds; List.member (out_edges(G) ! n) n1; List.member (out_edges(G) ! n) n2; (node_to_block(G) ! n1) = then_beginning; (node_to_block(G) ! n2) = else_beginning; G, ast \<turnstile> \<langle>((BigBlock then_name ((Assume guard)#then_cmds) str tr)#then_bbs) @ (b#bbs)\<rangle> [\<leadsto>] then_beginning, end_then; G, ast \<turnstile> \<langle>((BigBlock else_name ((Assume (Unop Not guard))#else_cmds) str tr)#else_bbs) @ (b#bbs)\<rangle> [\<leadsto>] else_beginning, end_else \<rbrakk> \<Longrightarrow>  G, ast \<turnstile> \<langle>(BigBlock _ cmds (Some (ParsedIf (Some guard) ((BigBlock then_name then_cmds str tr)#then_bbs) ((BigBlock else_name else_cmds str tr)#else_bbs))) None)#(b#bbs)\<rangle> [\<leadsto>] (node_to_block(G) ! n), (end_then @ end_else)"

    (* how should invariants be accounted for in the while rules? *)
    | RelateWhileBlockNoGuard: "\<lbrakk> (node_to_block(G) ! n) = cmds; List.member (out_edges(G) ! n) n1; (node_to_block(G) ! n1) = body_beginning; G, ast \<turnstile> \<langle>body_bbs @ (b#bbs)\<rangle> [\<leadsto>] body_beginning, end \<rbrakk> \<Longrightarrow> G, ast \<turnstile> \<langle>(BigBlock _ cmds (Some (ParsedWhile (Some guard) invs body_bbs)) None)#(b#bbs)\<rangle> [\<leadsto>] (node_to_block(G) ! n), end" 

    | RelateWhileBlock: "\<lbrakk> (node_to_block(G) ! n) = cmds; List.member (out_edges(G) ! n) n1; (node_to_block(G) ! n1) = body_beginning; G, ast \<turnstile> \<langle>((BigBlock body_name ((Assume guard)#body_cmds) str tr)#body_bbs) @ (b#bbs)\<rangle> [\<leadsto>] body_beginning, end \<rbrakk> \<Longrightarrow> G, ast \<turnstile> \<langle>(BigBlock _ cmds (Some (ParsedWhile (Some guard) invs ((BigBlock body_name body_cmds str tr)#body_bbs))) None)#(b#bbs)\<rangle> [\<leadsto>] (node_to_block(G) ! n), end" 

    (* FIXME: rules for break and goto don't work *)

    (*
    | RelateBreakBlock: "\<lbrakk> (node_to_block(G) ! n) = cmds; List.member (out_edges(G) ! n) n' \<rbrakk> \<Longrightarrow> G, ast \<turnstile> \<langle>(BigBlock _ cmds (Some (ParsedBreak num)) None)\<rangle> \<leadsto> (node_to_block(G) ! n), (node_to_block(G) ! n')" 
    
    | RelateGotoBlock: "\<lbrakk> (node_to_block(G) ! n) = cmds; List.member (out_edges(G) ! n) n'; (find_label lbl ast KStop) = Some (found_bb, found_cont); G, ast \<turnstile> \<langle>found_bb\<rangle> \<leadsto> (node_to_block(G) ! n'), exit \<rbrakk> \<Longrightarrow> G, ast \<turnstile> \<langle>(BigBlock _ cmds None (Some (Goto lbl)))\<rangle> [\<leadsto>] (node_to_block(G) ! n)#(b#bbs), exit"
    *)

    | RelateReturnBlock: "\<lbrakk> (node_to_block(G) ! n) = cmds; (out_edges(G) ! n) = [] \<rbrakk> \<Longrightarrow> G, ast \<turnstile> \<langle>(BigBlock _ cmds None (Some (Return opt_val)))#anything\<rangle> [\<leadsto>] (node_to_block(G) ! n), []"

end

