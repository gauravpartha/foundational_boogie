theory Ast
  imports Main Semantics Lang BackedgeElim

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

type_synonym 'a ast_config = "bigblock * cont * ('a state)"

(* auxillary function to find the label a Goto statement is referring to *)
fun find_label :: "label \<Rightarrow> bigblock list \<Rightarrow> cont \<Rightarrow> ((bigblock * cont) option)" where
    "find_label lbl [] cont = None" 
  | "find_label lbl ((BigBlock bb_name cmds None None) # []) cont = 
      (if (Some lbl = bb_name) then (Some ((BigBlock bb_name cmds None None), cont)) else (None))" 
  | "find_label lbl ((BigBlock bb_name cmds None None) # bbs) cont = 
      (if (Some lbl = bb_name) 
        then (Some ((BigBlock bb_name cmds None None), (KSeq bbs cont))) 
        else (find_label lbl bbs cont))" 
  | "find_label lbl ((BigBlock bb_name cmds (Some (ParsedIf guard then_bbs else_bbs)) None) # bbs) cont = 
      (if (Some lbl = bb_name) 
        then (Some ((BigBlock bb_name cmds (Some (ParsedIf guard then_bbs else_bbs)) None), (KSeq bbs cont))) 
        else (if (find_label lbl then_bbs cont \<noteq> None) 
                then (find_label lbl (then_bbs @ bbs) cont) 
                else (find_label lbl (else_bbs @ bbs) cont)))" 
  | "find_label lbl ((BigBlock bb_name cmds (Some (ParsedWhile guard invariants body_bbs)) None) # bbs) cont = 
      (if (Some lbl = bb_name) 
        then (Some ((BigBlock bb_name cmds (Some (ParsedWhile guard invariants body_bbs)) None), (KSeq bbs cont))) 
        else (if (find_label lbl body_bbs cont \<noteq> None) 
                then (find_label lbl body_bbs (KSeq ((BigBlock None [] (Some (ParsedWhile guard invariants body_bbs)) None) # bbs) cont)) 
                else (find_label lbl bbs cont)))"  
  | "find_label lbl ((BigBlock bb_name cmds (Some (ParsedBreak n)) None) # bbs) cont = 
      (if (Some lbl = bb_name) 
        then (Some ((BigBlock bb_name cmds (Some (ParsedBreak n)) None), (KSeq bbs cont))) 
        else (find_label lbl bbs cont))" 
  | "find_label lbl ((BigBlock bb_name cmds (Some (WhileWrapper while_loop)) None) # bbs) cont = 
      find_label lbl ((BigBlock bb_name cmds (Some while_loop) None) # bbs) cont"
  | "find_label lbl ((BigBlock bb_name cmds None (Some transfer_stmt)) # bbs) cont = 
      (if (Some lbl = bb_name) 
        then (Some ((BigBlock bb_name cmds None (Some transfer_stmt)), (KSeq bbs cont))) 
        else (find_label lbl bbs cont))"
  | "find_label lbl ((BigBlock bb_name cmds (Some s) (Some t)) # bbs) cont = None"


(* function defining the semantics of bigblocks; small-step semantics *)
(* Note: arrow symbols in the 'syntactic sugar' clash if the exact same syntax is used as in red_cmd *)
inductive red_bigblock :: "'a absval_ty_fun \<Rightarrow> proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env  \<Rightarrow> ast \<Rightarrow> 'a ast_config \<Rightarrow> 'a ast_config \<Rightarrow> bool" 
  ("_,_,_,_,_,_ \<turnstile> (\<langle>_\<rangle> \<longrightarrow>/ _)" [51,0,0,0] 81)
  for A :: "'a absval_ty_fun" and M :: proc_context and \<Lambda> :: var_context and \<Gamma> :: "'a fun_interp" and \<Omega> :: rtype_env and T :: ast
  where
 (* RedStatic: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>a\<rangle> \<longrightarrow> a" *)
  
    RedSimpleCmds: 
    "\<lbrakk>A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, (Normal n_s)\<rangle> [\<rightarrow>] s1 \<rbrakk> 
      \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name cs str_cmd tr_cmd), cont0, Normal n_s)\<rangle> \<longrightarrow> 
                              ((BigBlock bb_name [] str_cmd tr_cmd), cont0, s1)"  

  | RedFailure_or_Magic: 
    "\<lbrakk> (s1 = Magic) \<or> (s1 = Failure) \<rbrakk> 
      \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] str_cmd tr_cmd), cont0, s1)\<rangle> \<longrightarrow> 
                          ((BigBlock bb_name [] None None), KStop, s1)"

  (* TODO: figure out when this rule would be used *)
  | RedSkip_emptyCont: 
    "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] None None),  (KSeq [] cont0),  Normal n_s)\<rangle> \<longrightarrow> 
                    ((BigBlock bb_name [] None None), cont0, Normal n_s)"
  
  | RedSkip: 
    "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] None None),  (KSeq (b # bbs) cont0),  Normal n_s)\<rangle> \<longrightarrow> 
                    (b, (KSeq bbs cont0), Normal n_s)"

  | RedSkipEndBlock: 
    "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] None None),  (KEndBlock cont0),  Normal n_s)\<rangle> \<longrightarrow> 
                    ((BigBlock bb_name [] None None), cont0, Normal n_s)"

  | RedReturn: 
    "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>(BigBlock bb_name [] None (Some (Return val)),  cont0, Normal n_s)\<rangle> \<longrightarrow> 
                          ((BigBlock bb_name [] None None), KStop, Normal n_s)"

  | RedParsedIfTrue: 
    "\<lbrakk> bb_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s1\<rangle> \<Down> LitV (LBool True) \<rbrakk>  
        \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] 
                                (Some (ParsedIf bb_guard (then_hd # then_bbs) elsebigblocks)) None), cont0, Normal n_s)\<rangle> \<longrightarrow> 
                            (then_hd, (KSeq then_bbs cont0), Normal n_s)"

  | RedParsedIfFalse: 
    "\<lbrakk> bb_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s1\<rangle> \<Down> LitV (LBool False) \<rbrakk> 
        \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name []
                                (Some (ParsedIf bb_guard thenbigblocks (else_hd # else_bbs))) None), cont0, Normal n_s)\<rangle> \<longrightarrow>
                            (else_hd, (KSeq else_bbs cont0), Normal n_s)"

  | RedParsedWhileWrapper: 
    "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> 
      \<langle>((BigBlock bb_name [] 
              (Some (WhileWrapper (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs)))) None), cont0,  Normal n_s)\<rangle> \<longrightarrow>
        ((BigBlock bb_name [] 
                (Some (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs))) None), (KEndBlock cont0),  Normal n_s)"
 
  | RedParsedWhile_InvFail: 
    "\<lbrakk> bb_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s1\<rangle> \<Down> LitV (LBool True); 
       bb_invariants = invs1@[I]@invs2;
       expr_all_sat A \<Lambda> \<Gamma> \<Omega> n_s invs1;
       A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>I, n_s\<rangle> \<Down> BoolV False \<rbrakk> 
       \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> 
           \<langle>((BigBlock bb_name [] 
                    (Some (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs))) None), cont0,  Normal n_s)\<rangle> \<longrightarrow> 
              ((BigBlock bb_name [] None None), KStop, Failure)"

  | RedParsedWhileTrue: 
    "\<lbrakk>  bb_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s1\<rangle> \<Down> LitV (LBool True); 
       (expr_all_sat A \<Lambda> \<Gamma> \<Omega> n_s1 bb_invariants) \<rbrakk> 
       \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> 
            \<langle>((BigBlock bb_name [] 
                     (Some (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs))) None), cont0,  Normal n_s)\<rangle> \<longrightarrow> 
              (bb_hd, (KSeq (body_bbs @ [(BigBlock bb_name [] (Some (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs))) None)]) cont0), Normal n_s)"

  | RedParsedWhileFalse: 
    "\<lbrakk> bb_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s1\<rangle> \<Down> LitV (LBool False);
       (expr_all_sat A \<Lambda> \<Gamma> \<Omega> n_s1 bb_invariants) \<rbrakk>  
       \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] 
                                (Some (ParsedWhile bb_guard bb_invariants bigblocks)) None), cont0, Normal n_s)\<rangle> \<longrightarrow> 
                          ((BigBlock bb_name [] None None), cont0, Normal n_s)"

  | RedBreak0: 
    "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] (Some (ParsedBreak 0)) None), (KEndBlock cont0), Normal n_s)\<rangle> \<longrightarrow> 
                          ((BigBlock bb_name [] None None), cont0, Normal n_s)"

  | RedBreakN: 
    "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> 
           \<langle>((BigBlock bb_name [] (Some (ParsedBreak n)) None), (KSeq bbs cont0), Normal n_s)\<rangle> \<longrightarrow> 
            ((BigBlock None [] (Some (ParsedBreak n)) None), cont0, Normal n_s)"

  | RedBreakNPlus1: 
    "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> 
           \<langle>((BigBlock bb_name [] (Some (ParsedBreak (n + 1))) None), (KEndBlock cont0), Normal n_s)\<rangle> \<longrightarrow> 
            ((BigBlock None [] (Some (ParsedBreak n)) None), cont0, Normal n_s1)"

  | RedGoto: 
    "\<lbrakk> (find_label label ast KStop) = Some (found_bigblock, found_cont) \<rbrakk> 
        \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] None (Some (Goto label))),  cont0,  Normal n_s)\<rangle> \<longrightarrow> 
                            (found_bigblock, found_cont, (Normal n_s))"

inductive red_bigblock_trans :: "'a absval_ty_fun \<Rightarrow> proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env  \<Rightarrow> ast \<Rightarrow> 'a ast_config \<Rightarrow> 'a ast_config \<Rightarrow> bool" 
  ("_,_,_,_,_,_ \<turnstile> (\<langle>_\<rangle> [\<longrightarrow>]/ _)" [51,0,0,0] 81)
  for A :: "'a absval_ty_fun" and M :: proc_context and \<Lambda> :: var_context and \<Gamma> :: "'a fun_interp" and \<Omega> :: rtype_env and T :: ast
  where
    BBRefl: "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>config\<rangle> [\<longrightarrow>] config"
  | BBTrans: "\<lbrakk> A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>start_config\<rangle> \<longrightarrow> inter_config;  A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>inter_config\<rangle> [\<longrightarrow>] end_config\<rbrakk> \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>start_config\<rangle> [\<longrightarrow>] end_config"



(* defining correctness of the AST *)
fun get_state :: "'a ast_config \<Rightarrow> 'a state"
  where
    "get_state (bb, cont, s1) = s1"

fun is_final :: "'a ast_config \<Rightarrow> bool" 
  where
    "is_final ((BigBlock bb_name [] None None), KStop, s1) = True"
  | "is_final other = False"

fun init_ast :: "ast \<Rightarrow> 'a nstate \<Rightarrow> 'a ast_config"
  where
    "init_ast [] ns1 = ((BigBlock None [] None None), KStop, Normal ns1)"
  | "init_ast (b#bbs) ns1 = (b, (KSeq bbs KStop), Normal ns1)"

definition valid_configuration 
  where "valid_configuration A \<Lambda> \<Gamma> \<Omega> posts ast_config \<equiv> 
         (get_state ast_config) \<noteq> Failure \<and> 
         (is_final ast_config \<longrightarrow> (\<forall>ns'. (get_state ast_config) = Normal ns' \<longrightarrow> expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns' posts))"

definition proc_body_satisfies_spec :: "'a absval_ty_fun \<Rightarrow> proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> expr list \<Rightarrow> expr list \<Rightarrow> ast \<Rightarrow> 'a nstate \<Rightarrow> bool"
  where "proc_body_satisfies_spec A M \<Lambda> \<Gamma> \<Omega> pres posts ast ns \<equiv>
         expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns pres \<longrightarrow> 
          (\<forall> ast_reached. (rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> ast) (init_ast ast ns) ast_reached) \<longrightarrow> 
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

inductive syntactic_equiv :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infixl "\<sim>" 40) 
  where
    refl [simp]:   "a \<sim> a"
  | sym:           "a \<sim> b \<Longrightarrow> b \<sim> a"
  | trans [trans]: "a \<sim> b \<Longrightarrow> b \<sim> c \<Longrightarrow> a \<sim> c"
  | neg_cong:      "a \<sim> b \<Longrightarrow> UnOp Not a \<sim> UnOp Not b"
  | conj_cong:     "a1 \<sim> b1 \<Longrightarrow> a2 \<sim> b2 \<Longrightarrow> (a1 \<guillemotleft>And\<guillemotright> a2) \<sim> (b1 \<guillemotleft>And\<guillemotright> b2)"
  | disj_cong:     "a1 \<sim> b1 \<Longrightarrow> a2 \<sim> b2 \<Longrightarrow> (a1 \<guillemotleft>Or\<guillemotright> a2) \<sim> (b1 \<guillemotleft>Or\<guillemotright> b2)"
  | conj_commute:  "(a \<guillemotleft>And\<guillemotright> b) \<sim> (b \<guillemotleft>And\<guillemotright> a)"
  | disj_commute:  "(a \<guillemotleft>Or\<guillemotright> b) \<sim> (b \<guillemotleft>Or\<guillemotright> a)"
  | conj_assoc:    "(a \<guillemotleft>And\<guillemotright> b) \<guillemotleft>And\<guillemotright> c \<sim> a \<guillemotleft>And\<guillemotright> (b \<guillemotleft>And\<guillemotright> c)"
  | disj_assoc:    "(a \<guillemotleft>Or\<guillemotright> b) \<guillemotleft>Or\<guillemotright> c \<sim> a \<guillemotleft>Or\<guillemotright> (b \<guillemotleft>Or\<guillemotright> c)"
  | disj_conj:     "a \<guillemotleft>Or\<guillemotright> (b \<guillemotleft>And\<guillemotright> c) \<sim> (a \<guillemotleft>Or\<guillemotright> b) \<guillemotleft>And\<guillemotright> (a \<guillemotleft>Or\<guillemotright> c)"
  | conj_disj:     "a \<guillemotleft>And\<guillemotright> (b \<guillemotleft>Or\<guillemotright> c) \<sim> (a \<guillemotleft>And\<guillemotright> b) \<guillemotleft>Or\<guillemotright> (a \<guillemotleft>And\<guillemotright> c)"
  | de_morgan1:    "UnOp Not (a \<guillemotleft>And\<guillemotright> b) \<sim> (UnOp Not a) \<guillemotleft>Or\<guillemotright> (UnOp Not b)"
  | de_morgan2:    "UnOp Not (a \<guillemotleft>Or\<guillemotright> b) \<sim> (UnOp Not a) \<guillemotleft>And\<guillemotright> (UnOp Not b)"
  | neg_neg:       "UnOp Not (UnOp Not a) \<sim> a"
  | tnd:           "a \<guillemotleft>Or\<guillemotright> (UnOp Not) a \<sim> (Lit (LBool True))"
  | contr:         "a \<guillemotleft>And\<guillemotright> (UnOp Not) a \<sim> (Lit (LBool False))"
  | disj_idem:     "a \<guillemotleft>Or\<guillemotright> a \<sim> a"
  | conj_idem:     "a \<guillemotleft>And\<guillemotright> a \<sim> a"
  | conj_True:     "a \<guillemotleft>And\<guillemotright> (Lit (LBool True)) \<sim> a"
  | disj_True:     "a \<guillemotleft>Or\<guillemotright> (Lit (LBool True)) \<sim> (Lit (LBool True))"
  | neg_lt:        "UnOp Not (a \<guillemotleft>Lt\<guillemotright> b) \<sim> (a \<guillemotleft>Ge\<guillemotright> b)"
  | neg_gt:        "UnOp Not (a \<guillemotleft>Gt\<guillemotright> b) \<sim> (a \<guillemotleft>Le\<guillemotright> b)"
  | neg_le:        "UnOp Not (a \<guillemotleft>Le\<guillemotright> b) \<sim> (a \<guillemotleft>Gt\<guillemotright> b)"
  | neg_ge:        "UnOp Not (a \<guillemotleft>Ge\<guillemotright> b) \<sim> (a \<guillemotleft>Lt\<guillemotright> b)"
  | neg_eq:        "UnOp Not (a \<guillemotleft>Eq\<guillemotright> b) \<sim> (a \<guillemotleft>Neq\<guillemotright> b)"
  | neg_neq:       "UnOp Not (a \<guillemotleft>Neq\<guillemotright> b) \<sim> (a \<guillemotleft>Eq\<guillemotright> b)"

(*
definition semantic_equiv :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infixl "\<approx>" 40) where
  "exp1 \<approx> exp2 \<longleftrightarrow> (\<forall> A \<Lambda> \<Gamma> \<Omega> ns val. ((red_expr A \<Lambda> \<Gamma> \<Omega> exp1 ns val) = (red_expr A \<Lambda> \<Gamma> \<Omega> exp2 ns val)))"
*)

inductive ast_cfg_rel :: "expr option \<Rightarrow> expr list \<Rightarrow> bigblock \<Rightarrow> cmd list \<Rightarrow> bool"
  where 
     Rel_Guard_true:
      "\<lbrakk>ast_cfg_rel None [] (BigBlock name cs1 any_str any_tr) cs2\<rbrakk> \<Longrightarrow>
        ast_cfg_rel (Some if_block_guard) [] (BigBlock name cs1 any_str any_tr) ((Assume if_block_guard) # cs2)"
   | Rel_Guard_false:
      "\<lbrakk>ast_cfg_rel None [] (BigBlock name cs1 any_str any_tr) cs2; (UnOp Not if_block_guard) \<sim> c \<rbrakk> \<Longrightarrow>
        ast_cfg_rel (Some if_block_guard) [] (BigBlock name cs1 any_str any_tr) ((Assume c) # cs2)"
   | Rel_Invs:
      "\<lbrakk>ast_cfg_rel None invs (BigBlock name cs1 any_str any_tr) cs2\<rbrakk> \<Longrightarrow>
        ast_cfg_rel None (e_inv # invs) (BigBlock name cs1 any_str any_tr) ((Assert e_inv) # cs2)"
   | Rel_Main:
      " ast_cfg_rel None [] (BigBlock name cs1 any_str any_tr) cs1"


end

