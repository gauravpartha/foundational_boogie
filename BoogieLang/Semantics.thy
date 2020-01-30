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
  ("_ \<turnstile> ((\<langle>_,_\<rangle>) \<Down> _)" [51,0,0,0] 81)
  and red_exprs :: "fun_context \<Rightarrow> expr list \<Rightarrow> nstate \<Rightarrow> val list \<Rightarrow> bool"
  ("_ \<turnstile> ((\<langle>_,_\<rangle>) [\<Down>] _)" [51,0,0,0] 81)
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
  ("_ \<turnstile> ((\<langle>_,_\<rangle>) \<rightarrow>/ _)" [51,0,0,0] 81)
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

inductive red_cmd_list :: "fun_context \<Rightarrow> cmd list \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  ("_ \<turnstile> ((\<langle>_,_\<rangle>) [\<rightarrow>]/ _)" [51,0,0,0] 81)
  for \<Gamma> :: fun_context
  where
    RedListNil: "\<Gamma> \<turnstile> \<langle>[],s\<rangle> [\<rightarrow>] s"
  | RedListCons: "\<lbrakk> \<Gamma> \<turnstile> \<langle>c,s\<rangle> \<rightarrow> s'; \<Gamma> \<turnstile> \<langle>cs,s'\<rangle> [\<rightarrow>] s'' \<rbrakk> \<Longrightarrow> 
                    \<Gamma> \<turnstile> \<langle>(c # cs), s\<rangle> [\<rightarrow>] s''"

type_synonym cfg_config = "(node+unit) \<times> state"

inductive red_cfg :: "fun_context \<Rightarrow> mbodyCFG \<Rightarrow> cfg_config \<Rightarrow> cfg_config \<Rightarrow> bool"
  ("_,_ \<turnstile> (_ -n\<rightarrow>/ _)" [51,0,0,0] 81)
  for \<Gamma> :: fun_context and G :: mbodyCFG
  where
    RedNode: "\<lbrakk>node_to_block(G) n = Some cs; \<Gamma> \<turnstile> \<langle>cs,s\<rangle> [\<rightarrow>] s'; n' \<in> out_edges(G) n  \<rbrakk> \<Longrightarrow> 
               \<Gamma>, G  \<turnstile> (Inl n,s) -n\<rightarrow> (Inl n',s')"
  | RedReturn: "\<lbrakk>node_to_block(G) n = Some cs; \<Gamma> \<turnstile> \<langle>cs,s\<rangle> [\<rightarrow>] s'; (out_edges(G) n) = {} \<rbrakk> \<Longrightarrow> 
               \<Gamma>, G  \<turnstile> (Inl n,s) -n\<rightarrow> (Inr (),s')"

abbreviation red_cfg_multi :: "fun_context \<Rightarrow> mbodyCFG \<Rightarrow> cfg_config \<Rightarrow> cfg_config \<Rightarrow> bool"
  ("_,_ \<turnstile>_ -n\<rightarrow>*/ _" [51,0,0,0] 81)
  where "red_cfg_multi \<Gamma> G \<equiv> rtranclp (red_cfg \<Gamma> G)"

fun fun_interp_single_wf :: "fdecl \<Rightarrow> (val list \<rightharpoonup> val) \<Rightarrow> bool"
  where "fun_interp_single_wf (_, args_ty, ret_ty) f =
             ((\<forall> vs. map type_of_val vs = args_ty \<longleftrightarrow> (\<exists>v. f vs = Some v)) \<and>
              (\<forall> vs v. (f vs = Some v) \<longrightarrow> type_of_val v = ret_ty) ) "

definition fun_interp_wf :: "fdecl list \<Rightarrow> fun_interp \<Rightarrow> bool"
  where "fun_interp_wf fds \<gamma>_interp = 
            (\<forall>fd. List.ListMem fd fds \<longrightarrow> 
                  (\<exists>f. \<gamma>_interp (fst fd) = Some f \<and> fun_interp_single_wf fd f ))"

definition domain_wf :: "vdecl list \<Rightarrow> vdecl list \<Rightarrow> vname set"
  where "domain_wf args vdecls = (List.list.set(map fst args) \<union> List.list.set(map fst vdecls))"

definition state_typ_wf :: "nstate \<Rightarrow> vdecl list \<Rightarrow> vdecl list \<Rightarrow> bool"
  where "state_typ_wf ns args vdecls = 
           (\<forall>(v,v_ty) \<in> List.list.set(args) \<union> List.list.set(vdecls). 
                          Option.map_option type_of_val (ns(v)) = Some v_ty)"

definition method_body_verifies :: "fdecl list \<Rightarrow> fun_interp \<Rightarrow> mbodyCFG \<Rightarrow> nstate \<Rightarrow> bool"
  where "method_body_verifies fdecls \<gamma>_interp mbody ns = 
      (\<forall> m s'. ((fdecls, \<gamma>_interp), mbody \<turnstile> (Inl (entry(mbody)), Normal ns) -n\<rightarrow>* (m,s')) \<longrightarrow> s' \<noteq> Failure)"

(* not most compact representation (dom ns =... implied by ... type_ofval (ns(v)) = Some v_ty) *)
fun method_verify :: "prog \<Rightarrow> mdecl \<Rightarrow> bool"
  where 
    "method_verify (Program fdecls mdecls) (mname, args, vdecls, mbody) = 
    (\<forall>\<gamma>_interp. fun_interp_wf fdecls \<gamma>_interp \<longrightarrow>
     (\<forall>ns. 
      ( dom ns = domain_wf args vdecls \<longrightarrow>
        state_typ_wf ns args vdecls \<longrightarrow>
        method_body_verifies fdecls \<gamma>_interp mbody ns
     )
    ))"

end