theory Semantics
imports Lang
begin

type_synonym nstate = "vname \<rightharpoonup> val"

datatype state = Normal nstate | Failure | Magic

(* define context *)
type_synonym fun_interp = "fname \<rightharpoonup> (val list \<rightharpoonup> val)"

(* type declarations *)
(*type_synonym fun_decl = "fname \<rightharpoonup> (ty list \<times> ty)"*)

type_synonym fun_context = "fdecl list \<times> fun_interp"

fun binop_lessOrEqual :: "val \<Rightarrow> val \<rightharpoonup> val"
where
  "binop_lessOrEqual (IntV i1) (IntV i2) = Some (BoolV (i1 \<le> i2))"
| "binop_lessOrEqual _ _ = None"

fun binop_add :: "val \<Rightarrow> val \<rightharpoonup> val"
  where 
    "binop_add (IntV i1) (IntV i2) = Some (IntV (i1 + i2))"
  | "binop_add _ _ = None"
   
fun binop_and :: "val \<Rightarrow> val \<rightharpoonup> val"
  where
    "binop_and (BoolV b1) (BoolV b2) = Some (BoolV (b1 \<and> b2))"
  | "binop_and _ _ = None"

fun binop_eval ::"binop \<Rightarrow> val \<Rightarrow> val \<rightharpoonup> val"
  where
   "binop_eval Eq v1 v2 = Some (BoolV (v1 = v2))"
 | "binop_eval Add v1 v2 = binop_add v1 v2"
 | "binop_eval Le v1 v2 = binop_lessOrEqual v1 v2"
 | "binop_eval And v1 v2 = binop_and v1 v2"

(* big-step *)
inductive red_expr :: "fun_context \<Rightarrow> expr \<Rightarrow> nstate \<Rightarrow> val \<Rightarrow> bool"
  ("_ \<turnstile> ((\<langle>_,_\<rangle>) \<Down> _)" [81,81,81] 99)
  and red_exprs :: "fun_context \<Rightarrow> expr list \<Rightarrow> nstate \<Rightarrow> val list \<Rightarrow> bool"
  ("_ \<turnstile> ((\<langle>_,_\<rangle>) [\<Down>] _)" [81,81,81] 99)
  for \<Gamma> :: fun_context
  where 
    RedVar: "\<lbrakk> n_s(x) = Some v \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<langle>(Var x), n_s\<rangle> \<Down> v"
  | RedVal: "\<Gamma> \<turnstile> \<langle>(Val v), n_s\<rangle> \<Down> v"
  | RedBinOp: "\<lbrakk> \<Gamma> \<turnstile>\<langle>e1, n_s\<rangle> \<Down> v1; \<Gamma> \<turnstile> \<langle>e2, n_s\<rangle> \<Down> v2;
                 binop_eval bop v1 v2 = (Some v) \<rbrakk> \<Longrightarrow> 
             \<Gamma> \<turnstile> \<langle>(e1 \<guillemotleft>bop\<guillemotright> e2), n_s\<rangle> \<Down> v"
  (* a function application only reduces if the arguments have the expected types *)
             (*(fst \<Gamma>) f = Some (ty_args, _);
             (snd \<Gamma>) f = Some f_interp;
             ty_args = map type_of_val v_args;*)
  | RedFunOp: "\<lbrakk> \<Gamma> \<turnstile> \<langle>args, n_s\<rangle> [\<Down>] v_args; 
                (snd \<Gamma>) f = Some f_interp;
                f_interp v_args = Some v \<rbrakk> \<Longrightarrow>
             \<Gamma> \<turnstile> \<langle> FunExp f args, n_s \<rangle> \<Down> v"
  | RedListNil:
    "\<Gamma> \<turnstile> \<langle>[], n_s\<rangle> [\<Down>] []"
  | RedListCons:
    "\<lbrakk> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v; \<Gamma> \<turnstile> \<langle>es, n_s\<rangle> [\<Down>] vs \<rbrakk> \<Longrightarrow>
      \<Gamma> \<turnstile> \<langle>(e # es), n_s\<rangle> [\<Down>] (v # vs)"

inductive red_cmd :: "fun_context \<Rightarrow> cmd \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  ("_ \<turnstile> ((\<langle>_,_\<rangle>) \<rightarrow>/ _)" [81,81,81] 99)
  and red_cmds :: "fun_context \<Rightarrow> cmd list \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  ("_ \<turnstile> ((\<langle>_,_\<rangle>) [\<rightarrow>]/ _)" [81,81,81] 99)
  for \<Gamma> :: fun_context
  where
    RedAssertOk: "\<lbrakk> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> (BoolV True) \<rbrakk> \<Longrightarrow> 
                 \<Gamma> \<turnstile> \<langle>Assert e, Normal n_s\<rangle> \<rightarrow> Normal n_s"
  | RedAssertFail: "\<lbrakk> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> (BoolV False) \<rbrakk> \<Longrightarrow> 
                   \<Gamma> \<turnstile> \<langle>Assert e, Normal n_s\<rangle> \<rightarrow> Failure"
  | RedAssumeOk: "\<lbrakk> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> (BoolV True) \<rbrakk> \<Longrightarrow> 
                 \<Gamma> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> Normal n_s"
  | RedAssumeMagic: "\<lbrakk> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> (BoolV False) \<rbrakk> \<Longrightarrow> 
                 \<Gamma> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> Magic"
  | RedPropagateMagic: "\<Gamma> \<turnstile> \<langle>s, Magic\<rangle> \<rightarrow> Magic"
  | RedPropagateFailure: "\<Gamma> \<turnstile> \<langle>s, Failure\<rangle> \<rightarrow> Failure"
  | RedListNil: "\<Gamma> \<turnstile> \<langle>[],s\<rangle> [\<rightarrow>] s"
  | RedListCons: "\<lbrakk> \<Gamma> \<turnstile> \<langle>c,s\<rangle> \<rightarrow> s'; \<Gamma> \<turnstile> \<langle>cs,s'\<rangle> [\<rightarrow>] s'' \<rbrakk> \<Longrightarrow> 
                    \<Gamma> \<turnstile> \<langle>(c # cs), s\<rangle> [\<rightarrow>] s''"

(* configurations on the left and right are not the same
   left configuration: \<langle>Node, State\<rangle>
   right configuration:  
               (1) \<langle>inl Node, State\<rangle> [if move to another node]
               (2) \<langle>inr (), State\<rangle> [if no outgoing node, i.e., return]
*)
inductive red_cfg :: "fun_context \<Rightarrow> mbodyCFG \<Rightarrow> node \<Rightarrow> state \<Rightarrow> (node + unit) \<Rightarrow> state \<Rightarrow> bool"
  ("_,_ \<turnstile> ((\<langle>_,_\<rangle>) -n\<rightarrow>/ (\<langle>_,_\<rangle>))" [81,81,81] 99)
  and red_cfg_multi :: "fun_context \<Rightarrow> mbodyCFG \<Rightarrow> node \<Rightarrow> state \<Rightarrow> (node + unit) \<Rightarrow> state \<Rightarrow> bool"
  ("_,_ \<turnstile> ((\<langle>_,_\<rangle>) -n\<rightarrow>*/ (\<langle>_,_\<rangle>))" [81,81,81] 99)
  for \<Gamma> :: fun_context and G :: mbodyCFG
  where
    RedNode: "\<lbrakk>node_to_block(G) n = Some cs; \<Gamma> \<turnstile> \<langle>cs,s\<rangle> [\<rightarrow>] s'; n' \<in> out_edges(G) n  \<rbrakk> \<Longrightarrow> 
               \<Gamma>, G  \<turnstile> \<langle>n,s\<rangle> -n\<rightarrow> \<langle>Inl n',s'\<rangle>"
  | RedReturn: "\<lbrakk>node_to_block(G) n = Some cs; \<Gamma> \<turnstile> \<langle>cs,s\<rangle> [\<rightarrow>] s'; (out_edges(G) n) = {} \<rbrakk> \<Longrightarrow> 
               \<Gamma>, G  \<turnstile> \<langle>n,s\<rangle> -n\<rightarrow> \<langle>Inr (),s'\<rangle>" 
  | RedMultiStep1: "\<Gamma>, G \<turnstile> \<langle>n,s\<rangle> -n\<rightarrow>* \<langle>Inl n, s\<rangle>"
  | RedMultiStep2: "\<lbrakk> \<Gamma>, G \<turnstile> \<langle>n,s\<rangle> -n\<rightarrow> \<langle>Inl n',s'\<rangle>; \<Gamma>, G \<turnstile> \<langle>n', s'\<rangle> -n\<rightarrow>* \<langle>nu, s''\<rangle> \<rbrakk> \<Longrightarrow>
                \<Gamma>, G \<turnstile> \<langle>n,s\<rangle> -n\<rightarrow>* \<langle>nu, s''\<rangle>"
  | RedMultiStep3: "\<lbrakk> \<Gamma>, G \<turnstile> \<langle>n,s\<rangle> -n\<rightarrow> \<langle>Inr (),s'\<rangle> \<rbrakk> \<Longrightarrow>
                \<Gamma>, G \<turnstile> \<langle>n,s\<rangle> -n\<rightarrow>* \<langle>Inr (), s'\<rangle>"

fun fun_interp_single_wf :: "fdecl \<Rightarrow> (val list \<rightharpoonup> val) \<Rightarrow> bool"
  where "fun_interp_single_wf (_, args_ty, ret_ty) f =
             ((\<forall> vs. map type_of_val vs = args_ty \<longleftrightarrow> (\<exists>v. f vs = Some v)) \<and>
              (\<forall> vs v. (f vs = Some v) \<longrightarrow> type_of_val v = ret_ty) ) "

definition fun_interp_wf :: "fdecl list \<Rightarrow> fun_interp \<Rightarrow> bool"
  where "fun_interp_wf fds \<gamma>_interp = 
            (\<forall>fd. List.ListMem fd fds \<longrightarrow> 
                  (\<exists>f. \<gamma>_interp (fst fd) = Some f \<and> fun_interp_single_wf fd f ))"

(* not most compact representation (dom ns =... implied by ... type_ofval (ns(v)) = Some v_ty) *)
fun method_verify :: "prog \<Rightarrow> mdecl \<Rightarrow> bool"
  where 
    "method_verify (Program fdecls mdecls) (mname, args, vdecls, mbody) = 
    (\<forall>\<gamma>_interp. fun_interp_wf fdecls \<gamma>_interp \<longrightarrow>
     (\<forall>n ns s'. 
        dom ns = List.list.set(map fst args) \<union> List.list.set(map fst vdecls) \<and> 
        (\<forall>(v,v_ty) \<in> List.list.set(args). Option.map_option type_of_val (ns(v)) = Some v_ty) \<and>
        (fdecls, \<gamma>_interp), mbody \<turnstile> \<langle>entry(mbody), Normal ns\<rangle> -n\<rightarrow>* \<langle>n,s'\<rangle> \<longrightarrow> s' \<noteq> Failure)
    )"

end