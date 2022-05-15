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
 | KSeq "bigblock" cont
 | KEndBlock cont 

type_synonym 'a ast_config = "bigblock * cont * ('a state)"

fun convert_list_to_cont :: "bigblock list \<Rightarrow> cont \<Rightarrow> cont" where
    "convert_list_to_cont [] cont0 = cont0"
  | "convert_list_to_cont (x#xs) cont0 = convert_list_to_cont xs (KSeq x cont0)" 


(* auxillary function to find the label a Goto statement is referring to *)
fun find_label :: "label \<Rightarrow> bigblock list \<Rightarrow> cont \<Rightarrow> ((bigblock * cont) option)" where
    "find_label lbl [] cont = None" 
  | "find_label lbl ((BigBlock bb_name cmds None None) # []) cont = 
      (if (Some lbl = bb_name) then (Some ((BigBlock bb_name cmds None None), cont)) else (None))" 
  | "find_label lbl ((BigBlock bb_name cmds None None) # bbs) cont = 
      (if (Some lbl = bb_name) 
        then (Some ((BigBlock bb_name cmds None None), (convert_list_to_cont (rev bbs) cont))) 
        else (find_label lbl bbs cont))" 
  | "find_label lbl ((BigBlock bb_name cmds (Some (ParsedIf guard then_bbs else_bbs)) None) # bbs) cont = 
      (if (Some lbl = bb_name) 
        then (Some ((BigBlock bb_name cmds (Some (ParsedIf guard then_bbs else_bbs)) None), (convert_list_to_cont (rev bbs) cont))) 
        else (if (find_label lbl then_bbs cont \<noteq> None) 
                then (find_label lbl (then_bbs @ bbs) cont) 
                else (find_label lbl (else_bbs @ bbs) cont)))" 
  | "find_label lbl ((BigBlock bb_name cmds (Some (ParsedWhile guard invariants body_bbs)) None) # bbs) cont = 
      (if (Some lbl = bb_name) 
        then (Some ((BigBlock bb_name cmds (Some (ParsedWhile guard invariants body_bbs)) None), (convert_list_to_cont (rev bbs) cont))) 
        else (if (find_label lbl body_bbs cont \<noteq> None) 
                then (find_label lbl body_bbs (convert_list_to_cont ((rev bbs) @ [(BigBlock None [] (Some (ParsedWhile guard invariants body_bbs)) None)]) cont)) 
                else (find_label lbl bbs cont)))"  
  | "find_label lbl ((BigBlock bb_name cmds (Some (ParsedBreak n)) None) # bbs) cont = 
      (if (Some lbl = bb_name) 
        then (Some ((BigBlock bb_name cmds (Some (ParsedBreak n)) None), (convert_list_to_cont (rev bbs) cont))) 
        else (find_label lbl bbs cont))" 
  | "find_label lbl ((BigBlock bb_name cmds (Some (WhileWrapper while_loop)) None) # bbs) cont = 
      find_label lbl ((BigBlock bb_name cmds (Some while_loop) None) # bbs) cont"
  | "find_label lbl ((BigBlock bb_name cmds None (Some transfer_stmt)) # bbs) cont = 
      (if (Some lbl = bb_name) 
        then (Some ((BigBlock bb_name cmds None (Some transfer_stmt)), (convert_list_to_cont (rev bbs) cont))) 
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
    "\<lbrakk>(A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>cs, (Normal n_s)\<rangle> [\<rightarrow>] s1) \<and> (cs \<noteq> Nil) \<rbrakk> 
      \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name cs str_cmd tr_cmd), cont0, Normal n_s)\<rangle> \<longrightarrow> 
                              ((BigBlock bb_name [] str_cmd tr_cmd), cont0, s1)"  

  (* TODO: fix this rule! *)
  | RedFailure_or_Magic: 
    "\<lbrakk> (s1 = Magic) \<or> (s1 = Failure) \<rbrakk> 
      \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] str_cmd tr_cmd), cont0, s1)\<rangle> \<longrightarrow> 
                          ((BigBlock bb_name [] None None), KStop, s1)"

  (* TODO: fix this rule! *)
  (*
  | RedSkip_emptyCont: 
    "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] None None),  (KSeq [] cont0),  Normal n_s)\<rangle> \<longrightarrow> 
                    ((BigBlock bb_name [] None None), cont0, Normal n_s)"
  *)
  | RedSkip: 
    "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] None None), (KSeq b cont0), Normal n_s)\<rangle> \<longrightarrow> 
                    (b, cont0, Normal n_s)"

  | RedSkipEndBlock: 
    "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] None None),  (KEndBlock cont0),  Normal n_s)\<rangle> \<longrightarrow> 
                    ((BigBlock bb_name [] None None), cont0, Normal n_s)"

  | RedReturn: 
    "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>(BigBlock bb_name [] None (Some (Return val)), cont0, Normal n_s)\<rangle> \<longrightarrow> 
                          ((BigBlock bb_name [] None None), KStop, Normal n_s)"

  | RedParsedIfTrue: 
    "\<lbrakk>\<And> b. bb_guard = (Some b) \<Longrightarrow>  A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s\<rangle> \<Down> LitV (LBool True) \<rbrakk>  
        \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] 
                                (Some (ParsedIf bb_guard (then_hd # then_bbs) elsebigblocks)) None), cont0, Normal n_s)\<rangle> \<longrightarrow> 
                            (then_hd, (convert_list_to_cont (rev then_bbs) cont0), Normal n_s)"

  | RedParsedIfFalse: 
    "\<lbrakk>\<And>b. bb_guard = (Some b) \<Longrightarrow>  A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s\<rangle> \<Down> LitV (LBool False) \<rbrakk> 
        \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name []
                                (Some (ParsedIf bb_guard thenbigblocks (else_hd # else_bbs))) None), cont0, Normal n_s)\<rangle> \<longrightarrow>
                            (else_hd, (convert_list_to_cont (rev else_bbs) cont0), Normal n_s)"

  | RedParsedWhileWrapper: 
    "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> 
      \<langle>((BigBlock bb_name [] 
              (Some (WhileWrapper (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs)))) None), cont0,  Normal n_s)\<rangle> \<longrightarrow>
        ((BigBlock bb_name [] 
                (Some (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs))) None), (KEndBlock cont0),  Normal n_s)"
 
  | RedParsedWhile_InvFail: 
    "\<lbrakk>\<And> b. bb_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s\<rangle> \<Down> LitV (LBool True); 
       bb_invariants = invs1@[I]@invs2;
       expr_all_sat A \<Lambda> \<Gamma> \<Omega> n_s invs1;
       A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>I, n_s\<rangle> \<Down> BoolV False \<rbrakk> 
       \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> 
           \<langle>((BigBlock bb_name [] 
                    (Some (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs))) None), cont0,  Normal n_s)\<rangle> \<longrightarrow> 
              ((BigBlock bb_name [] None None), KStop, Failure)"

  | RedParsedWhileTrue: 
    "\<lbrakk>\<And> b.  bb_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s\<rangle> \<Down> LitV (LBool True); 
       (expr_all_sat A \<Lambda> \<Gamma> \<Omega> n_s bb_invariants) \<rbrakk> 
       \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> 
            \<langle>((BigBlock bb_name [] 
                     (Some (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs))) None), cont0,  Normal n_s)\<rangle> \<longrightarrow> 
              (bb_hd, convert_list_to_cont (rev ((BigBlock bb_name [] (Some (ParsedWhile bb_guard bb_invariants (bb_hd # body_bbs))) None) # body_bbs)) cont0, Normal n_s)"


  | RedParsedWhileFalse: 
    "\<lbrakk>\<And> b. bb_guard = (Some b) \<Longrightarrow> A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>b, n_s\<rangle> \<Down> LitV (LBool False);
       (expr_all_sat A \<Lambda> \<Gamma> \<Omega> n_s bb_invariants) \<rbrakk>  
       \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] 
                                (Some (ParsedWhile bb_guard bb_invariants bigblocks)) None), cont0, Normal n_s)\<rangle> \<longrightarrow> 
                          ((BigBlock bb_name [] None None), cont0, Normal n_s)"

  | RedBreak0: 
    "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] (Some (ParsedBreak 0)) None), (KEndBlock cont0), Normal n_s)\<rangle> \<longrightarrow> 
                          ((BigBlock bb_name [] None None), cont0, Normal n_s)"

  | RedBreakN: 
    "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> 
           \<langle>((BigBlock bb_name [] (Some (ParsedBreak n)) None), (KSeq b cont0), Normal n_s)\<rangle> \<longrightarrow> 
            ((BigBlock None [] (Some (ParsedBreak n)) None), cont0, Normal n_s)"

  | RedBreakNPlus1: 
    "A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> 
           \<langle>((BigBlock bb_name [] (Some (ParsedBreak (n + 1))) None), (KEndBlock cont0), Normal n_s)\<rangle> \<longrightarrow> 
            ((BigBlock None [] (Some (ParsedBreak n)) None), cont0, Normal n_s1)"

  | RedGoto: 
    "\<lbrakk> (find_label label ast KStop) = Some (found_bigblock, found_cont) \<rbrakk> 
        \<Longrightarrow> A,M,\<Lambda>,\<Gamma>,\<Omega>,T \<turnstile> \<langle>((BigBlock bb_name [] None (Some (Goto label))), cont0, Normal n_s)\<rangle> \<longrightarrow> 
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
  | "init_ast (b#bbs) ns1 = (b, convert_list_to_cont (rev bbs) KStop, Normal ns1)"

definition valid_configuration 
  where "valid_configuration A \<Lambda> \<Gamma> \<Omega> posts bb cont state \<equiv> 
         (get_state (bb, cont, state)) \<noteq> Failure \<and> 
         (is_final (bb, cont, state) \<longrightarrow> (\<forall>ns'. (get_state (bb, cont, state)) = Normal ns' \<longrightarrow> expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns' posts))"

definition proc_body_satisfies_spec :: "'a absval_ty_fun \<Rightarrow> proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> expr list \<Rightarrow> expr list \<Rightarrow> ast \<Rightarrow> 'a nstate \<Rightarrow> bool"
  where "proc_body_satisfies_spec A M \<Lambda> \<Gamma> \<Omega> pres posts ast ns \<equiv>
         expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns pres \<longrightarrow> 
          (\<forall> bb cont state. (rtranclp (red_bigblock A M \<Lambda> \<Gamma> \<Omega> ast) (init_ast ast ns) (bb, cont, state)) \<longrightarrow> 
                    valid_configuration A \<Lambda> \<Gamma> \<Omega> posts bb cont state)"

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
  (* TODO: combine whichever rules you can and prove symmetry! *)
  | neg_gt1:        "UnOp Not (a \<guillemotleft>Gt\<guillemotright> b) \<sim> (a \<guillemotleft>Le\<guillemotright> b)"
  | neg_gt2:        "UnOp Not (a \<guillemotleft>Gt\<guillemotright> b) \<sim> (b \<guillemotleft>Ge\<guillemotright> a)"
  | neg_le:        "UnOp Not (a \<guillemotleft>Le\<guillemotright> b) \<sim> (a \<guillemotleft>Gt\<guillemotright> b)"
  | neg_ge:        "UnOp Not (a \<guillemotleft>Ge\<guillemotright> b) \<sim> (a \<guillemotleft>Lt\<guillemotright> b)"
  | neg_lt2:        "UnOp Not (a \<guillemotleft>Lt\<guillemotright> b) \<sim> (b \<guillemotleft>Le\<guillemotright> a)"
  | neg_eq:        "UnOp Not (a \<guillemotleft>Eq\<guillemotright> b) \<sim> (a \<guillemotleft>Neq\<guillemotright> b)"
  | neg_neq:       "UnOp Not (a \<guillemotleft>Neq\<guillemotright> b) \<sim> (a \<guillemotleft>Eq\<guillemotright> b)"

(*
definition semantic_equiv :: "expr \<Rightarrow> expr \<Rightarrow> bool" (infixl "\<approx>" 40) where
  "exp1 \<approx> exp2 \<longleftrightarrow> (\<forall> A \<Lambda> \<Gamma> \<Omega> ns val. ((red_expr A \<Lambda> \<Gamma> \<Omega> exp1 ns val) = (red_expr A \<Lambda> \<Gamma> \<Omega> exp2 ns val)))"
*)

lemma not_true_equals_false:
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp unop.Not expr, ns1\<rangle> \<Down> BoolV True"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>expr, ns1\<rangle> \<Down> BoolV False"
  using assms
  sorry

lemma not_false_equals_true:
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp unop.Not expr, ns1\<rangle> \<Down> BoolV False"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>expr, ns1\<rangle> \<Down> BoolV True"
  using assms
  sorry

lemma true_equals_not_false:
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>expr, ns1\<rangle> \<Down> BoolV True"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp unop.Not expr, ns1\<rangle> \<Down> BoolV False"
  using assms
  sorry

lemma false_equals_not_true:
  assumes "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>expr, ns1\<rangle> \<Down> BoolV False"
  shows "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>UnOp unop.Not expr, ns1\<rangle> \<Down> BoolV True"
  using assms
  sorry

lemma equiv_preserves_value:
  assumes "a \<sim> b"
  and "red_expr A \<Lambda> \<Gamma> \<Omega> a ns (BoolV boolean)"
  shows "red_expr A \<Lambda> \<Gamma> \<Omega> b ns (BoolV boolean)"
  using assms
  sorry

(* TODO: Can I avoid needing this? *)
fun inv_into_assertion :: "expr \<Rightarrow> cmd" where
  "inv_into_assertion e = (Assert e)"

lemma asserts_hold_if_invs_hold: 
  assumes "expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns1 invs"
  and "assertions = map inv_into_assertion invs"
  shows "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>assertions, Normal ns1\<rangle> [\<rightarrow>] Normal ns1"
  using assms
proof (induction invs arbitrary: assertions)
  case Nil
  then show ?case  by (simp add: RedCmdListNil)
next
  case (Cons e_inv invs_tail)
  from Cons(2) have prem1: "expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns1 invs_tail" by (simp add: expr_all_sat_def)
  from Cons(3) have prem2: "List.tl assertions = map inv_into_assertion invs_tail" by simp
  from prem1 prem2 have end2: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>List.tl assertions,Normal ns1\<rangle> [\<rightarrow>] Normal ns1" using Cons(1) by blast

  from Cons(2) have act1: "expr_sat A \<Lambda> \<Gamma> \<Omega> ns1 e_inv" by (simp add: expr_all_sat_def)
  from Cons(3) have act2: "List.hd assertions = (Assert e_inv)" by simp
  from act1 act2 have end1: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>List.hd assertions,Normal ns1\<rangle> \<rightarrow> Normal ns1" by (simp add: expr_sat_def red_cmd.intros(1))

  then show ?case using end1 end2 by (simp add: Cons.prems(2) RedCmdListCons)
qed

lemma invs_hold_if_asserts_reduce: 
  assumes "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>assertions, s0\<rangle> [\<rightarrow>] s1"
  and "s0 = Normal ns1"
  and "s1 \<noteq> Failure"
  and "assertions = map inv_into_assertion invs"
  shows "expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns1 invs"
  using assms
proof (induction arbitrary: invs rule: red_cmd_list.induct)
  case (RedCmdListNil s)
  hence "invs = []" by simp
  then show ?case by (simp add: expr_all_sat_def)
next
  case (RedCmdListCons c s s'' cs s')  
  from RedCmdListCons have "cs = map inv_into_assertion (List.tl invs)" using assms by auto
  from RedCmdListCons have "c = Assert (hd invs)" by auto 

  from RedCmdListCons(1) this \<open>s = Normal ns1\<close> show ?case
  proof cases
    case RedAssertOk thus ?thesis 
      using RedCmdListCons(1) \<open>c = Assert (hd invs)\<close> \<open>s = Normal ns1\<close> \<open>cs = map inv_into_assertion (List.tl invs)\<close> 
      by (metis RedCmdListCons.IH RedCmdListCons.prems(2)
          RedCmdListCons.prems(3) cmd.inject(1) expr_all_sat_def expr_sat_def 
          list.collapse list.discI list.map_disc_iff list_all_simps(1) state.inject)
  next
    case RedAssertFail thus ?thesis using failure_stays_cmd_list RedCmdListCons(2) RedCmdListCons(5) by blast
  qed auto
qed

lemma one_inv_fails_assertions: 
  assumes "invs = invs1 @ [I] @ invs2"
      and "expr_all_sat A \<Lambda> \<Gamma> \<Omega> ns1 invs1"
      and "A,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>I,ns1\<rangle> \<Down> BoolV False"
      and "assertions = map inv_into_assertion invs"
    shows "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>assertions, Normal ns1\<rangle> [\<rightarrow>] Failure"
  using assms
proof -
  from assms(4) assms(1) obtain assum1 a_fail assum2 where
    left: "assum1 = map inv_into_assertion invs1" and
    mid_fail: "a_fail = inv_into_assertion I" and
    right: "assum2 = map inv_into_assertion invs2" and
    concat: "assertions = assum1 @ [a_fail] @ assum2"
    by simp
  from assms(2) left have left_red: "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>assum1, Normal ns1\<rangle> [\<rightarrow>] Normal ns1" using asserts_hold_if_invs_hold by simp
  from mid_fail have "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>a_fail, Normal ns1\<rangle> \<rightarrow> Failure" using red_cmd.intros(2) assms(3) by simp
  from this left_red have "A,M,\<Lambda>,\<Gamma>,\<Omega> \<turnstile> \<langle>assum1 @ [a_fail] @ assum2, Normal ns1\<rangle> [\<rightarrow>] Failure" using failure_stays_cmd_list 
    by (simp add: RedCmdListCons failure_red_cmd_list red_cmd_list_append)
  thus ?thesis using concat by auto
qed


(* TODO: Discuss Rel_Invs case!  *)
inductive ast_cfg_rel :: "expr option \<Rightarrow> cmd list \<Rightarrow> bigblock \<Rightarrow> cmd list \<Rightarrow> bool"
  where 
     Rel_Guard_true:
      "\<lbrakk>ast_cfg_rel None [] (BigBlock name cs1 any_str any_tr) cs2\<rbrakk> \<Longrightarrow>
        ast_cfg_rel (Some block_guard) [] (BigBlock name cs1 any_str any_tr) ((Assume block_guard) # cs2)"
   | Rel_Guard_false:
      "\<lbrakk>ast_cfg_rel None [] (BigBlock name cs1 any_str any_tr) cs2; (UnOp Not block_guard) \<sim> c \<rbrakk> \<Longrightarrow>
        ast_cfg_rel (Some block_guard) [] (BigBlock name cs1 any_str any_tr) ((Assume c) # cs2)"
   | Rel_Invs:
       "ast_cfg_rel None assertions (BigBlock name [] any_str any_tr) assertions"
   | Rel_Main_test:
      "ast_cfg_rel None [] (BigBlock name cs1 any_str any_tr) cs1"

abbreviation red_bigblock_k_step :: "'a absval_ty_fun \<Rightarrow> proc_context \<Rightarrow> var_context \<Rightarrow> 'a fun_interp \<Rightarrow> rtype_env \<Rightarrow> ast \<Rightarrow> 'a ast_config \<Rightarrow> nat \<Rightarrow> 'a ast_config \<Rightarrow> bool"
  ("_,_,_,_,_,_ \<turnstile>_ -n\<longrightarrow>^_/ _" [51,0,0,0,0] 81)
where "red_bigblock_k_step A M \<Lambda> \<Gamma> \<Omega> T c1 n c2 \<equiv> ((red_bigblock A M \<Lambda> \<Gamma> \<Omega> T)^^n) c1 c2"

end

