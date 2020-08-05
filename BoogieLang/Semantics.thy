theory Semantics
imports Lang DeBruijn
begin

datatype 'a val = LitV lit | AbsV 'a  

type_synonym 'a nstate = "vname \<rightharpoonup> 'a val"

datatype 'a state = Normal "'a nstate" | Failure | Magic

(* define context *)
type_synonym 'a fun_interp = "fname \<rightharpoonup> ('a val list \<rightharpoonup> 'a val)"

(* type declarations *)
type_synonym 'a fun_context = "fdecls \<times> 'a fun_interp"
type_synonym var_context = vdecls

fun binop_less :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
  where
    "binop_less (LInt i1) (LInt i2) = Some (LBool (i1 < i2))"
  | "binop_less _ _ = None"

fun binop_lessOrEqual :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
where
  "binop_lessOrEqual (LInt i1) (LInt i2) = Some (LBool (i1 \<le> i2))"
| "binop_lessOrEqual _ _ = None"

fun binop_greater :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
  where
    "binop_greater (LInt i1) (LInt i2) = Some (LBool (i1 > i2))"
  | "binop_greater _ _ = None"

fun binop_greaterOrEqual :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
where
  "binop_greaterOrEqual (LInt i1) (LInt i2) = Some (LBool (i1 \<ge> i2))"
| "binop_greaterOrEqual _ _ = None"

fun binop_add :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
  where 
    "binop_add (LInt i1) (LInt i2) = Some (LInt (i1 + i2))"
  | "binop_add _ _ = None"

fun binop_sub :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
  where 
    "binop_sub (LInt i1) (LInt i2) = Some (LInt (i1 - i2))"
  | "binop_sub _ _ = None"

fun binop_mul :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
  where
    "binop_mul (LInt i1) (LInt i2) = Some (LInt (i1 * i2))"
  | "binop_mul _ _ = None"
   
fun binop_and :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
  where
    "binop_and (LBool b1) (LBool b2) = Some (LBool (b1 \<and> b2))"
  | "binop_and _ _ = None"

fun binop_or :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
  where
    "binop_or (LBool b1) (LBool b2) = Some (LBool (b1 \<or> b2))"
  | "binop_or _ _ = None"

fun binop_implies :: "lit \<Rightarrow> lit \<rightharpoonup> lit"
  where
    "binop_implies (LBool b1) (LBool b2) = Some (LBool (b1 \<longrightarrow> b2))"
  | "binop_implies _ _ = None"

fun binop_eval ::"binop \<Rightarrow> lit \<Rightarrow> lit \<rightharpoonup> lit"
  where
   (*equality gives false if v1 or v2 have different types, reconsider this?*)
   "binop_eval Eq v1 v2 = Some (LBool (v1 = v2))" 
 | "binop_eval Neq v1 v2 = Some (LBool (v1 \<noteq> v2))"
 | "binop_eval Add v1 v2 = binop_add v1 v2"
 | "binop_eval Sub v1 v2 = binop_sub v1 v2"
 | "binop_eval Mul v1 v2 = binop_mul v1 v2"
 | "binop_eval Lt v1 v2 = binop_less v1 v2"
 | "binop_eval Le v1 v2 = binop_lessOrEqual v1 v2"
 | "binop_eval Gt v1 v2 = binop_greater v1 v2"
 | "binop_eval Ge v1 v2 = binop_greaterOrEqual v1 v2"
 | "binop_eval And v1 v2 = binop_and v1 v2"
 | "binop_eval Or v1 v2 = binop_or v1 v2"
 | "binop_eval Imp v1 v2 = binop_implies v1 v2"

fun binop_eval_val :: "binop \<Rightarrow> 'a val \<Rightarrow> 'a val \<rightharpoonup> 'a val"
  where 
   "binop_eval_val bop (LitV v1) (LitV v2) = map_option LitV (binop_eval bop v1 v2)"
 | "binop_eval_val bop _ _ = None"

fun unop_not :: "lit \<rightharpoonup> lit"
  where
    "unop_not (LBool b) = Some (LBool (\<not> b))"
  | "unop_not _ = None"

fun unop_minus :: "lit \<rightharpoonup> lit"
  where 
    "unop_minus (LInt i) = Some (LInt (-i))"
  | "unop_minus _ = None"

fun unop_eval :: "unop \<Rightarrow> lit \<rightharpoonup> lit"
  where 
   "unop_eval Not v = unop_not v"
 | "unop_eval UMinus v = unop_minus v"

fun unop_eval_val :: "unop \<Rightarrow> 'a val \<rightharpoonup> 'a val"
  where
   "unop_eval_val uop (LitV v) = map_option LitV (unop_eval uop v)"
 | "unop_eval_val _ _ = None"

(* types *)

(** type information for abstract values **)
type_synonym 'a ty_absval_rel = "'a \<Rightarrow> tcon_id \<Rightarrow> ty list \<Rightarrow> bool"

fun ty_val_rel :: "'a ty_absval_rel \<Rightarrow> 'a val \<Rightarrow> ty \<Rightarrow> bool"
  where 
   "ty_val_rel A (LitV v) (TPrim tp) = (tp = (type_of_lit v))"
 | "ty_val_rel A (AbsV v) (TCon c ty_args) = A v c ty_args"
 | "ty_val_rel A _ _ = False"

(* big-step *)
inductive red_expr :: "'a ty_absval_rel \<Rightarrow> 'a fun_context \<Rightarrow> expr \<Rightarrow> 'a nstate \<Rightarrow> 'a val \<Rightarrow> bool"
  ("_,_ \<turnstile> ((\<langle>_,_\<rangle>) \<Down> _)" [51,0,0,0] 81)
  and red_exprs :: "'a ty_absval_rel \<Rightarrow> 'a fun_context \<Rightarrow> expr list \<Rightarrow> 'a nstate \<Rightarrow> 'a val list \<Rightarrow> bool"
  ("_,_ \<turnstile> ((\<langle>_,_\<rangle>) [\<Down>] _)" [51,0,0,0] 81)
  for  A :: "'a ty_absval_rel" and \<Gamma> :: "'a fun_context"
  where 
    RedVar: "\<lbrakk> n_s(x) = Some v \<rbrakk> \<Longrightarrow> A,\<Gamma> \<turnstile> \<langle>(Var x), n_s\<rangle> \<Down> v"
  | RedLit: "A,\<Gamma> \<turnstile> \<langle>(Lit v), n_s\<rangle> \<Down> LitV v" 
  | RedBinOp: "\<lbrakk>A,\<Gamma> \<turnstile> \<langle>e1, n_s\<rangle> \<Down> v1; A,\<Gamma> \<turnstile> \<langle>e2, n_s\<rangle> \<Down> v2;
                 binop_eval_val bop v1 v2 = (Some v) \<rbrakk> \<Longrightarrow> 
             A,\<Gamma> \<turnstile> \<langle>(e1 \<guillemotleft>bop\<guillemotright> e2), n_s\<rangle> \<Down> v"
  | RedUnOp: " \<lbrakk> A,\<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v; unop_eval_val uop v = Some v' \<rbrakk> \<Longrightarrow> A,\<Gamma> \<turnstile> \<langle>UnOp uop e, n_s\<rangle> \<Down> v'"
  | RedFunOp: "\<lbrakk>(snd \<Gamma>) f = Some f_interp;
                A,\<Gamma> \<turnstile> \<langle>args, n_s\<rangle> [\<Down>] v_args;
                f_interp v_args = Some v \<rbrakk> \<Longrightarrow>
             A,\<Gamma> \<turnstile> \<langle> FunExp f args, n_s \<rangle> \<Down> v"
  | RedExpListNil:
    "A,\<Gamma> \<turnstile> \<langle>[], n_s\<rangle> [\<Down>] []"
  | RedExpListCons:
    "\<lbrakk> A,\<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v; A,\<Gamma> \<turnstile> \<langle>es, n_s\<rangle> [\<Down>] vs \<rbrakk> \<Longrightarrow>
      A,\<Gamma> \<turnstile> \<langle>(e # es), n_s\<rangle> [\<Down>] (v # vs)"
  | RedForAllTrue:
    "\<lbrakk>\<And>v. ty_val_rel A v ty \<Longrightarrow> A,\<Gamma> \<turnstile> \<langle>e, (shift n_s)(0 \<mapsto> v)\<rangle> \<Down> LitV (LBool True) \<rbrakk> \<Longrightarrow> 
     A,\<Gamma> \<turnstile> \<langle>Forall ty e, n_s\<rangle> \<Down> LitV (LBool True)"
  | RedForAllFalse:
    "\<lbrakk>ty_val_rel A v ty;  A,\<Gamma> \<turnstile> \<langle>e, (shift n_s)(0 \<mapsto> v)\<rangle> \<Down> LitV (LBool False) \<rbrakk> \<Longrightarrow> 
     A,\<Gamma> \<turnstile> \<langle>Forall ty e, n_s\<rangle> \<Down> LitV (LBool False)"
  | RedExistsTrue:
    "\<lbrakk>ty_val_rel A v ty; A,\<Gamma> \<turnstile> \<langle>e, (shift n_s)(0 \<mapsto> v)\<rangle> \<Down> LitV (LBool True) \<rbrakk> \<Longrightarrow>
     A,\<Gamma> \<turnstile> \<langle>Exists ty e, n_s\<rangle> \<Down> LitV (LBool True)"
  | RedExistsFalse:
    "\<lbrakk>\<And>v. ty_val_rel A v ty \<Longrightarrow> A,\<Gamma> \<turnstile> \<langle>e, (shift n_s)(0 \<mapsto> v)\<rangle> \<Down> LitV (LBool False) \<rbrakk> \<Longrightarrow>
     A,\<Gamma> \<turnstile> \<langle>Exists ty e, n_s\<rangle> \<Down> LitV (LBool False)"


inductive_cases RedBinOp_case[elim!]: "A,\<Gamma> \<turnstile> \<langle>(e1 \<guillemotleft>bop\<guillemotright> e2), n_s\<rangle> \<Down> v"
inductive_cases RedUnOp_case[elim!]: "A,\<Gamma> \<turnstile> \<langle>UnOp uop e1, n_s\<rangle> \<Down> v"
inductive_cases RedFunOp_case[elim!]: "A,\<Gamma> \<turnstile> \<langle> FunExp f args, n_s \<rangle> \<Down> v"
inductive_cases RedVal_case[elim]: "A,\<Gamma> \<turnstile> \<langle>(Val v), n_s\<rangle> \<Down> v"
inductive_cases RedVar_case[elim!]: "A,\<Gamma> \<turnstile> \<langle>(Var x), n_s\<rangle> \<Down> v"
inductive_cases RedForAllTrue_case: "A,\<Gamma> \<turnstile> \<langle>Forall ty e, n_s\<rangle> \<Down> LitV (LBool True)"
inductive_cases RedForAllFalse_case: "A,\<Gamma> \<turnstile> \<langle>Forall ty e, n_s\<rangle> \<Down> LitV (LBool False)"

inductive red_cmd :: "'a ty_absval_rel \<Rightarrow> var_context \<Rightarrow> 'a fun_context \<Rightarrow> cmd \<Rightarrow> 'a state \<Rightarrow> 'a state \<Rightarrow> bool"
  ("_,_,_ \<turnstile> ((\<langle>_,_\<rangle>) \<rightarrow>/ _)" [51,51,0,0,0] 81)
  for A :: "'a ty_absval_rel" and \<Lambda> :: var_context and  \<Gamma> :: "'a fun_context"
  where
    RedAssertOk: "\<lbrakk> A,\<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool True) \<rbrakk> \<Longrightarrow> 
                 A,\<Lambda>,\<Gamma> \<turnstile> \<langle>Assert e, Normal n_s\<rangle> \<rightarrow> Normal n_s"
  | RedAssertFail: "\<lbrakk> A,\<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool False) \<rbrakk> \<Longrightarrow> 
                  A,\<Lambda>,\<Gamma> \<turnstile> \<langle>Assert e, Normal n_s\<rangle> \<rightarrow> Failure"
  | RedAssumeOk: "\<lbrakk> A,\<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool True) \<rbrakk> \<Longrightarrow> 
                A,\<Lambda>,\<Gamma> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> Normal n_s"
  | RedAssumeMagic: "\<lbrakk> A,\<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> LitV (LBool False) \<rbrakk> \<Longrightarrow> 
                A,\<Lambda>,\<Gamma> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> Magic"
  | RedAssign: "\<lbrakk>A,\<Gamma> \<turnstile> \<langle>(map snd upds), n_s\<rangle> [\<Down>] vs \<rbrakk> \<Longrightarrow>
               A,\<Lambda>,\<Gamma> \<turnstile> \<langle>Assign upds, Normal n_s\<rangle> \<rightarrow>  Normal (n_s((map fst upds) [\<mapsto>] vs))"  
  | RedHavoc: "\<lbrakk> map_of \<Lambda> x = Some ty; ty_val_rel A v ty \<rbrakk> \<Longrightarrow>
               A,\<Lambda>,\<Gamma> \<turnstile> \<langle>Havoc x, Normal n_s\<rangle> \<rightarrow> Normal (n_s(x \<mapsto> v))"
  | RedPropagateMagic: "A,\<Lambda>,\<Gamma> \<turnstile> \<langle>s, Magic\<rangle> \<rightarrow> Magic"
  | RedPropagateFailure: "A,\<Lambda>,\<Gamma> \<turnstile> \<langle>s, Failure\<rangle> \<rightarrow> Failure"

inductive_cases RedAssertOk_case: "A,\<Lambda>,\<Gamma> \<turnstile> \<langle>Assert e, Normal n_s\<rangle> \<rightarrow> Normal n_s"
inductive_cases RedAssumeOk_case: "A,\<Lambda>,\<Gamma> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> Normal n_s"

inductive red_cmd_list :: "'a ty_absval_rel \<Rightarrow> var_context \<Rightarrow> 'a fun_context \<Rightarrow> cmd list \<Rightarrow> 'a state \<Rightarrow> 'a state \<Rightarrow> bool"
  ("_,_,_ \<turnstile> ((\<langle>_,_\<rangle>) [\<rightarrow>]/ _)" [51,0,0,0] 81)
  for A :: "'a ty_absval_rel" and \<Lambda> :: var_context and \<Gamma> :: "'a fun_context"
  where
    RedCmdListNil: "A,\<Lambda>,\<Gamma> \<turnstile> \<langle>[],s\<rangle> [\<rightarrow>] s"
  | RedCmdListCons: "\<lbrakk> A,\<Lambda>,\<Gamma> \<turnstile> \<langle>c,s\<rangle> \<rightarrow> s'; A,\<Lambda>,\<Gamma> \<turnstile> \<langle>cs,s'\<rangle> [\<rightarrow>] s'' \<rbrakk> \<Longrightarrow> 
                   A,\<Lambda>,\<Gamma> \<turnstile> \<langle>(c # cs), s\<rangle> [\<rightarrow>] s''"

thm red_cmd_list.induct

inductive_cases RedCmdListNil_case [elim]: "A,\<Lambda>,\<Gamma> \<turnstile> \<langle>[],s\<rangle> [\<rightarrow>] s"
inductive_cases RedCmdListCons_case [elim]: "A,\<Lambda>,\<Gamma> \<turnstile> \<langle>(c # cs), s\<rangle> [\<rightarrow>] s''"

type_synonym 'a cfg_config = "(node+unit) \<times> 'a state"

inductive red_cfg :: "'a ty_absval_rel \<Rightarrow> var_context \<Rightarrow> 'a fun_context \<Rightarrow> mbodyCFG \<Rightarrow> 'a cfg_config \<Rightarrow> 'a cfg_config \<Rightarrow> bool"
  ("_,_,_,_ \<turnstile> (_ -n\<rightarrow>/ _)" [51,0,0,0] 81)
  for A :: "'a ty_absval_rel" and \<Lambda> :: var_context and \<Gamma> :: "'a fun_context" and G :: mbodyCFG
  where
    RedNode: "\<lbrakk>node_to_block(G) n = Some cs; A,\<Lambda>,\<Gamma> \<turnstile> \<langle>cs,s\<rangle> [\<rightarrow>] s'; n' \<in> out_edges(G) n  \<rbrakk> \<Longrightarrow> 
              A,\<Lambda>,\<Gamma>,G  \<turnstile> (Inl n,s) -n\<rightarrow> (Inl n',s')"
  | RedReturn: "\<lbrakk>node_to_block(G) n = Some cs; A,\<Lambda>,\<Gamma> \<turnstile> \<langle>cs,s\<rangle> [\<rightarrow>] s'; (out_edges(G) n) = {} \<rbrakk> \<Longrightarrow> 
               A,\<Lambda>,\<Gamma>,G  \<turnstile> (Inl n,s) -n\<rightarrow> (Inr (),s')"

inductive_cases RedNode_case: "A,\<Lambda>,\<Gamma>,G  \<turnstile> (Inl n,s) -n\<rightarrow> (Inl n',s')"

abbreviation red_cfg_multi :: "'a ty_absval_rel \<Rightarrow> var_context \<Rightarrow> 'a fun_context \<Rightarrow> mbodyCFG \<Rightarrow> 'a cfg_config \<Rightarrow> 'a cfg_config \<Rightarrow> bool"
  ("_, _,_,_ \<turnstile>_ -n\<rightarrow>*/ _" [51,0,0,0] 81)
  where "red_cfg_multi A \<Lambda> \<Gamma> G \<equiv> rtranclp (red_cfg A \<Lambda> \<Gamma> G)"

abbreviation red_cfg_k_step :: "'a ty_absval_rel \<Rightarrow> var_context \<Rightarrow> 'a fun_context \<Rightarrow> mbodyCFG \<Rightarrow> 'a cfg_config \<Rightarrow> nat \<Rightarrow> 'a cfg_config \<Rightarrow> bool"
  ("_,_,_,_ \<turnstile>_ -n\<rightarrow>^_/ _" [51,0,0,0,0] 81)
where "red_cfg_k_step A \<Lambda> \<Gamma> G c1 n c2 \<equiv> ((red_cfg A \<Lambda> \<Gamma> G)^^n) c1 c2"

fun fun_interp_single_wf :: "'a ty_absval_rel \<Rightarrow> ty list \<times> ty \<Rightarrow> ('a val list \<rightharpoonup> 'a val) \<Rightarrow> bool"
  where "fun_interp_single_wf A (args_ty, ret_ty) f =
         (\<forall> vs. list_all (\<lambda> v_ty. ty_val_rel A (fst v_ty) (snd v_ty)) (zip vs args_ty) \<longrightarrow> 
           (\<exists>v. f vs = Some v \<and> ty_val_rel A v ret_ty)) "

definition fun_interp_wf :: "'a ty_absval_rel \<Rightarrow> fdecls \<Rightarrow> 'a fun_interp \<Rightarrow> bool"
  where "fun_interp_wf A fds \<gamma>_interp = 
            (\<forall>fn fd. map_of fds fn = Some fd \<longrightarrow> 
                  (\<exists>f. \<gamma>_interp fn = Some f \<and> fun_interp_single_wf A fd f ))"

definition state_typ_wf :: "'a ty_absval_rel \<Rightarrow>'a nstate \<Rightarrow> vdecls \<Rightarrow> bool"
  where "state_typ_wf A ns vs = 
           (\<forall> v ty. map_of vs v = Some ty  \<longrightarrow> 
                          Option.map_option (\<lambda>v. ty_val_rel A v ty)  (ns(v)) = Some True)"

definition method_body_verifies :: "'a ty_absval_rel \<Rightarrow> vdecls \<Rightarrow> fdecls \<Rightarrow> 'a fun_interp \<Rightarrow> mbodyCFG \<Rightarrow> 'a nstate \<Rightarrow> bool"
  where "method_body_verifies A vds fds \<gamma>_interp mbody ns = 
      (\<forall> m' s'. (A, vds, (fds, \<gamma>_interp), mbody \<turnstile> (Inl (entry(mbody)), Normal ns) -n\<rightarrow>* (m',s')) \<longrightarrow> s' \<noteq> Failure)"

definition axiom_sat :: "'a ty_absval_rel \<Rightarrow> 'a fun_context \<Rightarrow> 'a nstate \<Rightarrow> axiom \<Rightarrow> bool"
  where "axiom_sat A \<Gamma> n_s a = (A,\<Gamma> \<turnstile> \<langle>a, n_s\<rangle> \<Down> LitV (LBool True))"

definition axioms_sat :: "'a ty_absval_rel \<Rightarrow> 'a fun_context \<Rightarrow> 'a nstate \<Rightarrow> axiom list \<Rightarrow> bool"
  where "axioms_sat A \<Gamma> n_s as = list_all (axiom_sat A \<Gamma> n_s) as"

(* not most compact representation (dom ns =... implied by ... state_typ wf ... ) *)
(* disjointness condition does not reflect Boogie which allows shadowing of global variables *)
fun method_verify :: "'a ty_absval_rel \<Rightarrow> prog \<Rightarrow> mdecl \<Rightarrow> bool"
  where 
    "method_verify A (Program fdecls consts gvars axioms mdecls) (mname, args, locals, mbody) =
    (\<forall> \<gamma>_interp. fun_interp_wf A fdecls \<gamma>_interp \<longrightarrow>
     (\<forall>ns. 
       (axioms_sat A (fdecls, \<gamma>_interp) ns axioms) \<longrightarrow>
       (state_typ_wf A ns consts \<and> state_typ_wf A ns gvars \<and> state_typ_wf A ns args \<and> state_typ_wf A ns locals) \<longrightarrow>
        method_body_verifies A (args@locals@gvars@consts) fdecls \<gamma>_interp mbody ns
      )
    )"

lemma expr_eval_determ: 
shows "((A,\<Gamma> \<turnstile> \<langle>e1, s\<rangle> \<Down> v) \<Longrightarrow> ((A,\<Gamma> \<turnstile> \<langle>e1, s\<rangle> \<Down> v') \<Longrightarrow> v = v'))"  
    and "(A,\<Gamma> \<turnstile> \<langle>es, s\<rangle> [\<Down>] vs) \<Longrightarrow> (A,\<Gamma> \<turnstile> \<langle>es, s\<rangle> [\<Down>] vs') \<Longrightarrow> vs = vs' "
proof (induction arbitrary: v' and vs' rule: red_expr_red_exprs.inducts)
  case (RedVar n_s x v)
  assume "n_s x = Some v"
  assume "A,\<Gamma> \<turnstile> \<langle>Var x,n_s\<rangle> \<Down> v'"
  then show ?case using \<open>n_s x = Some v\<close> by (cases; simp)
next
  case (RedLit l n_s)
  assume "A,\<Gamma> \<turnstile> \<langle>Lit l,n_s\<rangle> \<Down> v'"
  then show ?case by (cases; simp)
next
  case (RedBinOp e1 n_s v1 e2 v2 bop v)
  from RedBinOp.prems show ?case
  proof (cases)
    fix v1' v2'
    assume "A,\<Gamma> \<turnstile> \<langle>e1,n_s\<rangle> \<Down> v1'" hence "v1 = v1'" using RedBinOp.IH by simp
    assume "A,\<Gamma> \<turnstile> \<langle>e2,n_s\<rangle> \<Down> v2'" hence "v2 = v2'" using RedBinOp.IH by simp
    assume "binop_eval_val bop v1' v2' = Some v'"
    with \<open>v1 = v1'\<close> \<open>v2 = v2'\<close> show ?thesis using RedBinOp.hyps by simp
  qed
next
  case (RedUnOp e n_s v uop v' veval)
  from RedUnOp.prems show ?case
  proof (cases)
    fix v2
    assume "A,\<Gamma> \<turnstile> \<langle>e,n_s\<rangle> \<Down> v2" hence "v2 = v" using RedUnOp.IH by simp
    assume "unop_eval_val uop v2 = Some veval"
    with \<open>v2 = v\<close> show ?thesis using RedUnOp.hyps by simp
  qed
next
  case (RedFunOp f f_interp args n_s v_args v)
  from RedFunOp.prems show ?case
  proof (cases)
    fix v_args' f_interp'
    assume "A,\<Gamma> \<turnstile> \<langle>args,n_s\<rangle> [\<Down>] v_args'" hence "v_args = v_args'" using RedFunOp.IH by simp
    assume "snd \<Gamma> f = Some f_interp'" hence "f_interp = f_interp'" using RedFunOp.IH by simp
    assume "f_interp' v_args' = Some v'"
    thus ?case using \<open>v_args = v_args'\<close> \<open>f_interp = f_interp'\<close> using RedFunOp.hyps by simp
  qed
next
  case (RedExpListNil n_s vs')
  thus ?case by (cases; simp)
next
  case (RedExpListCons e n_s v es vs' vs'')
  assume "A,\<Gamma> \<turnstile> \<langle>e # es,n_s\<rangle> [\<Down>] vs''"
  thus ?case 
  proof cases
    fix w ws      
    assume "A,\<Gamma> \<turnstile> \<langle>e,n_s\<rangle> \<Down> w" hence "v = w" using RedExpListCons.IH by simp
    assume "A,\<Gamma> \<turnstile> \<langle>es,n_s\<rangle> [\<Down>] ws" hence "ws = vs'" using RedExpListCons.IH by simp  
    moreover assume "vs'' = w # ws"
    ultimately show ?thesis using \<open>v = w\<close>  by simp
  qed
next
  case (RedForAllTrue ty e n_s v')
  from \<open>A,\<Gamma> \<turnstile> \<langle>Forall ty e,n_s\<rangle> \<Down> v'\<close>
  show ?case
  proof cases
    fix v''
    assume "v' = LitV (LBool True)"
    thus ?thesis by simp
  next
    fix v''
    assume "v' = LitV (LBool False)"
    assume "ty_val_rel A v'' ty"
    moreover assume "A,\<Gamma> \<turnstile> \<langle>e, (shift n_s)(0 \<mapsto> v'')\<rangle> \<Down> LitV (LBool False)"
    ultimately show ?thesis using RedForAllTrue.IH(2)
      by blast
  qed
next
  case (RedForAllFalse v ty e n_s v')
  from \<open>A,\<Gamma> \<turnstile> \<langle>Forall ty e,n_s\<rangle> \<Down> v'\<close>
  show ?case
  proof cases
    case RedForAllTrue
    thus ?thesis using local.RedForAllFalse by metis
  next
    case RedForAllFalse
    thus ?thesis by simp
  qed
next
  case (RedExistsTrue v ty e n_s v')
  assume Hty:"ty_val_rel A v ty"
  from \<open>A,\<Gamma> \<turnstile> \<langle>Exists ty e,n_s\<rangle> \<Down> v'\<close>
  show ?case
  proof cases
    case (RedExistsTrue v'')
    thus ?thesis by simp
  next
    case RedExistsFalse
    with Hty have "A,\<Gamma> \<turnstile> \<langle>e, (shift n_s)(0 \<mapsto> v)\<rangle> \<Down> LitV (LBool False)" by simp
    thus ?thesis using RedExistsTrue.IH by blast
  qed
next
  case (RedExistsFalse ty e n_s v')
  from \<open>A,\<Gamma> \<turnstile> \<langle>Exists ty e, n_s\<rangle> \<Down> v'\<close> show ?case
  proof cases
    case (RedExistsTrue v'')
    thus ?thesis using RedExistsFalse.IH by blast
  next
    case RedExistsFalse
    thus ?thesis by simp
  qed
qed

lemma step_nil_same:
  assumes A1: "A,\<Lambda>,\<Gamma> \<turnstile> \<langle>[], s\<rangle> [\<rightarrow>] s''"
  shows "s = s''"
proof -
  from A1 show ?thesis by (cases; auto)
qed

lemma no_out_edges_return:
  assumes 
    A1: "A, \<Lambda>, \<Gamma>, G \<turnstile> (Inl n,s) -n\<rightarrow> (Inl n', s')" and 
    A2: "(out_edges(G) n) = {}"
  shows False
  using A1 A2 red_cfg.simps by blast

lemma magic_stays_cmd:
  assumes "A,\<Lambda>,\<Gamma> \<turnstile> \<langle>c, Magic\<rangle> \<rightarrow> s'"
  shows "s' = Magic"
  using assms
  by (cases rule: red_cmd.cases)

lemma magic_stays_cmd_list_aux:
  assumes "A,\<Lambda>,\<Gamma> \<turnstile> \<langle>cs, s\<rangle> [\<rightarrow>] s'" and "s = Magic"
  shows   "s' = Magic"
  using assms
proof (induct rule: red_cmd_list.induct)
  case RedCmdListNil
  then show ?case by simp
next
  case (RedCmdListCons c s' cs s'')
  then show ?case using magic_stays_cmd by blast
qed

lemma magic_stays_cmd_list:
  assumes "A,\<Lambda>,\<Gamma> \<turnstile> \<langle>cs, Magic\<rangle> [\<rightarrow>] s'"
  shows "s' = Magic"
  using assms
  by (simp add: magic_stays_cmd_list_aux)

lemma magic_stays_cfg:
  assumes "A, \<Lambda>, \<Gamma>, G \<turnstile> (m, Magic) -n\<rightarrow> (m', s')"
  shows " s' = Magic"
  using assms
proof (cases rule: red_cfg.cases)
  case (RedNode n cs n')
  then show ?thesis using magic_stays_cmd_list by blast
next
  case (RedReturn n cs)
  then show ?thesis using magic_stays_cmd_list by blast
qed

lemma magic_stays_cfg_multi:
  assumes
    "A, \<Lambda>, \<Gamma>, G \<turnstile> (m, Magic) -n\<rightarrow>* (m', s')"
  shows "s' = Magic"
  using assms
proof (induction rule: rtranclp_induct2)
  case refl
  then show ?case by simp
next
  case (step a1 b1 a2 b2)
  then show ?case using magic_stays_cfg by simp
qed

lemma magic_stays_cfg_k_step:
  assumes
    "A, \<Lambda>, \<Gamma>, G \<turnstile> (m, Magic) -n\<rightarrow>^k (m', s')"
  shows "s' = Magic"
  using assms
  by (meson magic_stays_cfg_multi relpowp_imp_rtranclp)

lemma finished_remains: 
  assumes "A, \<Lambda>, \<Gamma>, G \<turnstile> (Inr (), n_s) -n\<rightarrow>* (m',n')"
  shows "(m',n') = (Inr(), n_s)"
  using assms
proof (induction rule: rtranclp_induct2)
  case refl
  then show ?case by simp
next
  case (step a b a' b')
  with step.hyps(2) show ?case
    by (cases; simp)
qed

lemma forall_red:
  assumes "A, \<Gamma> \<turnstile> \<langle>Forall ty e, n_s\<rangle> \<Down> v"
  shows "\<exists>b. (v = LitV (LBool b)) \<and> (b = (\<forall>v'. ty_val_rel A v' ty \<longrightarrow> A, \<Gamma> \<turnstile> \<langle>e, (shift n_s)(0 \<mapsto> v')\<rangle> \<Down> LitV (LBool True)))"
  using assms
proof (cases)
  case RedForAllTrue
  thus ?thesis by auto
next
  case (RedForAllFalse v')
  thus ?thesis
   by (blast dest: expr_eval_determ(1))
qed

lemma exists_red:
  assumes "A, \<Gamma> \<turnstile> \<langle>Forall ty e, n_s\<rangle> \<Down> v"
  shows "\<exists>b. (v = LitV (LBool b)) \<and> (b = (\<forall>v'. ty_val_rel A v' ty \<longrightarrow> A,\<Gamma> \<turnstile> \<langle>e, (shift n_s)(0 \<mapsto> v')\<rangle> \<Down> LitV (LBool True)))"
  using assms
proof (cases)
  case RedForAllTrue
  thus ?thesis by auto
next
  case (RedForAllFalse v')
  thus ?thesis
   by (blast dest: expr_eval_determ(1))
qed

end