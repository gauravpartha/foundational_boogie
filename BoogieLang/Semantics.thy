theory Semantics
imports Lang CFG
begin

type_synonym nstate = "vname \<rightharpoonup> val"

datatype state = Normal nstate | Failure | Magic

(* define context *)
type_synonym fun_interp = "fname \<rightharpoonup> (val list \<Rightarrow> val)"

(* type declarations *)
type_synonym fun_decl = "fname \<rightharpoonup> (ty list \<times> ty)"

type_synonym fun_context = "fun_decl \<times> fun_interp"

fun binop_lessThan :: "val \<Rightarrow>  val \<rightharpoonup> val"
where
  "binop_lessThan (IntV i1) (IntV i2) = Some (BoolV (i1 < i2))"
| "binop_lessThan _ _ = None"

fun binop_add :: "val \<Rightarrow> val \<rightharpoonup> val"
  where 
    "binop_add (IntV i1) (IntV i2) = Some (IntV (i1 + i2))"
  | "binop_add _ _ = None"
   
fun binop_and :: "val \<Rightarrow> val \<rightharpoonup> val"
  where
    "binop_and (BoolV b1) (BoolV b2) = Some (BoolV (b1 \<and> b2))"
  | "binop_and _ _ = None"

(*
fun feval :: "'m prog \<Rightarrow> prog_context \<Rightarrow> fname  \<Rightarrow> val list \<rightharpoonup> val"
  where
    "feval P (Ctxt \<Gamma>) fn vs =
          (case (\<Gamma> fn) of (Some f_sem) \<Rightarrow> f_sem vs | None \<Rightarrow> None)"
*)

fun binop_eval ::"binop \<Rightarrow> val \<Rightarrow> val \<rightharpoonup> val"
  where
   "binop_eval Eq v1 v2 = Some (BoolV (v1 = v2))"
 | "binop_eval Add v1 v2 = binop_add v1 v2"
 | "binop_eval Le v1 v2 = binop_lessThan v1 v2"
 | "binop_eval And v1 v2 = binop_and v1 v2"


inductive red_expr :: "fun_context \<Rightarrow> expr \<Rightarrow> nstate \<Rightarrow> val \<Rightarrow> bool"
  ("_ \<turnstile> ((\<langle>_,_\<rangle>) \<Down> _)" [81,81,81] 99)
  and red_exprs :: "fun_context \<Rightarrow> expr list \<Rightarrow> nstate \<Rightarrow> val list \<Rightarrow> bool"
  ("_ \<turnstile> ((\<langle>_,_\<rangle>) [\<Down>] _)" [81,81,81] 99)
  for \<Gamma> :: fun_context
  where 
    RedVar: "\<lbrakk> n_s(x) = Some v \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<langle>(Var x), n_s\<rangle> \<Down> v"
  | RedVal: "\<Gamma> \<turnstile> \<langle>(Val v), n_s\<rangle> \<Down> v"
  | RedBinOp: "\<lbrakk> \<Gamma> \<turnstile>\<langle>e1, n_s\<rangle> \<Down> v1; \<Gamma> \<turnstile> \<langle>e1, n_s\<rangle> \<Down> v2;
                 binop_eval bop v1 v2 = (Some v) \<rbrakk> \<Longrightarrow> 
             \<Gamma> \<turnstile> \<langle>(e1 \<guillemotleft>bop\<guillemotright> e2), n_s\<rangle> \<Down> v"
  (* a function application only reduces if the arguments have the expected types *)
  | RedFunOp: "\<lbrakk> \<Gamma> \<turnstile> \<langle>args, n_s\<rangle> [\<Down>] v_args; 
             (fst \<Gamma>) f = Some (ty_args, _);
             (snd \<Gamma>) f = Some f_interp;
             ty_args = map ty_of_val v_args;
             v = f_interp v_args \<rbrakk> \<Longrightarrow>
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
    RedAssertOk: "\<lbrakk> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> (BoolV true) \<rbrakk> \<Longrightarrow> 
                 \<Gamma> \<turnstile> \<langle>Assert e, Normal n_s\<rangle> \<rightarrow> Normal n_s"
  | RedAssertFail: "\<lbrakk> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> (BoolV false) \<rbrakk> \<Longrightarrow> 
                   \<Gamma> \<turnstile> \<langle>Assert e, Normal n_s\<rangle> \<rightarrow> Failure"
  | RedAssumeOk: "\<lbrakk> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> (BoolV true) \<rbrakk> \<Longrightarrow> 
                 \<Gamma> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> Normal n_s"
  | RedAssumeMagic: "\<lbrakk> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> (BoolV false) \<rbrakk> \<Longrightarrow> 
                 \<Gamma> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> Magic"
  | RedPropagateMagic: "\<Gamma> \<turnstile> \<langle>s, Magic\<rangle> \<rightarrow> Magic"
  | RedPropagateFailure: "\<Gamma> \<turnstile> \<langle>s, Failure\<rangle> \<rightarrow> Failure"
  | RedListSingle: "\<Gamma> \<turnstile> \<langle>c,s\<rangle> \<rightarrow> s' \<Longrightarrow> \<Gamma> \<turnstile> \<langle>[c],s\<rangle> [\<rightarrow>] s'"
  | RedListCons: "\<lbrakk> \<Gamma> \<turnstile> \<langle>c,s\<rangle> \<rightarrow> s'; \<Gamma> \<turnstile> \<langle>cs,s'\<rangle> [\<rightarrow>] s'' \<rbrakk> \<Longrightarrow> 
                    \<Gamma> \<turnstile> \<langle>(c # cs), s\<rangle> [\<rightarrow>] s''"
                


end