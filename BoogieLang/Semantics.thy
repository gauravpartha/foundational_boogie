theory Semantics
imports Lang
begin

type_synonym nstate = "vname \<rightharpoonup> val"

datatype state = Normal nstate | Failure | Magic

(* define context *)
type_synonym fun_interp = "fname \<rightharpoonup> (val list \<rightharpoonup> val)"

(* type declarations *)
type_synonym fun_context = "fdecls \<times> fun_interp"
type_synonym var_context = vdecls

fun binop_less :: "val \<Rightarrow> val \<rightharpoonup> val"
  where
    "binop_less (IntV i1) (IntV i2) = Some (BoolV (i1 < i2))"
  | "binop_less _ _ = None"

fun binop_lessOrEqual :: "val \<Rightarrow> val \<rightharpoonup> val"
where
  "binop_lessOrEqual (IntV i1) (IntV i2) = Some (BoolV (i1 \<le> i2))"
| "binop_lessOrEqual _ _ = None"

fun binop_greater :: "val \<Rightarrow> val \<rightharpoonup> val"
  where
    "binop_greater (IntV i1) (IntV i2) = Some (BoolV (i1 > i2))"
  | "binop_greater _ _ = None"

fun binop_greaterOrEqual :: "val \<Rightarrow> val \<rightharpoonup> val"
where
  "binop_greaterOrEqual (IntV i1) (IntV i2) = Some (BoolV (i1 \<ge> i2))"
| "binop_greaterOrEqual _ _ = None"

fun binop_add :: "val \<Rightarrow> val \<rightharpoonup> val"
  where 
    "binop_add (IntV i1) (IntV i2) = Some (IntV (i1 + i2))"
  | "binop_add _ _ = None"

fun binop_sub :: "val \<Rightarrow> val \<rightharpoonup> val"
  where 
    "binop_sub (IntV i1) (IntV i2) = Some (IntV (i1 - i2))"
  | "binop_sub _ _ = None"

fun binop_mul :: "val \<Rightarrow> val \<rightharpoonup> val"
  where
    "binop_mul (IntV i1) (IntV i2) = Some (IntV (i1 * i2))"
  | "binop_mul _ _ = None"
   
fun binop_and :: "val \<Rightarrow> val \<rightharpoonup> val"
  where
    "binop_and (BoolV b1) (BoolV b2) = Some (BoolV (b1 \<and> b2))"
  | "binop_and _ _ = None"

fun binop_or :: "val \<Rightarrow> val \<rightharpoonup> val"
  where
    "binop_or (BoolV b1) (BoolV b2) = Some (BoolV (b1 \<or> b2))"
  | "binop_or _ _ = None"

fun binop_implies :: "val \<Rightarrow> val \<rightharpoonup> val"
  where
    "binop_implies (BoolV b1) (BoolV b2) = Some (BoolV (b1 \<longrightarrow> b2))"
  | "binop_implies _ _ = None"

fun binop_eval ::"binop \<Rightarrow> val \<Rightarrow> val \<rightharpoonup> val"
  where
   (*equality gives false if v1 or v2 have different types, reconsider this?*)
   "binop_eval Eq v1 v2 = Some (BoolV (v1 = v2))" 
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

fun unop_not :: "val \<rightharpoonup> val"
  where
    "unop_not (BoolV b) = Some (BoolV (\<not> b))"
  | "unop_not _ = None"

fun unop_eval :: "unop \<Rightarrow> val \<rightharpoonup> val"
  where 
   "unop_eval Not v1 = unop_not v1"

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
  | RedUnOp: " \<lbrakk> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v; unop_eval uop v = Some v' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<langle>UnOp uop e, n_s\<rangle> \<Down> v'"
  (* a function application only reduces if the arguments have the expected types *)
             (*(fst \<Gamma>) f = Some (ty_args, _);
             (snd \<Gamma>) f = Some f_interp;
             ty_args = map type_of_val v_args;*)
  | RedFunOp: "\<lbrakk> \<Gamma> \<turnstile> \<langle>args, n_s\<rangle> [\<Down>] v_args; 
                (snd \<Gamma>) f = Some f_interp;
                f_interp v_args = Some v \<rbrakk> \<Longrightarrow>
             \<Gamma> \<turnstile> \<langle> FunExp f args, n_s \<rangle> \<Down> v"
  | RedExpListNil:
    "\<Gamma> \<turnstile> \<langle>[], n_s\<rangle> [\<Down>] []"
  | RedExpListCons:
    "\<lbrakk> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> v; \<Gamma> \<turnstile> \<langle>es, n_s\<rangle> [\<Down>] vs \<rbrakk> \<Longrightarrow>
      \<Gamma> \<turnstile> \<langle>(e # es), n_s\<rangle> [\<Down>] (v # vs)"

inductive_cases RedBinOp_case[elim!]: "\<Gamma> \<turnstile> \<langle>(e1 \<guillemotleft>bop\<guillemotright> e2), n_s\<rangle> \<Down> v"
inductive_cases RedUnOp_case[elim!]: "\<Gamma> \<turnstile> \<langle>UnOp uop e1, n_s\<rangle> \<Down> v"
inductive_cases RedFunOp_case[elim!]: "\<Gamma> \<turnstile> \<langle> FunExp f args, n_s \<rangle> \<Down> v"
inductive_cases RedVal_case[elim]: "\<Gamma> \<turnstile> \<langle>(Val v), n_s\<rangle> \<Down> v"
inductive_cases RedVar_case[elim!]: "\<Gamma> \<turnstile> \<langle>(Var x), n_s\<rangle> \<Down> v"

inductive red_cmd :: "var_context \<Rightarrow> fun_context \<Rightarrow> cmd \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  ("_,_ \<turnstile> ((\<langle>_,_\<rangle>) \<rightarrow>/ _)" [51,51,0,0,0] 81)
  for \<Lambda> :: var_context and \<Gamma> :: fun_context
  where
    RedAssertOk: "\<lbrakk> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> (BoolV True) \<rbrakk> \<Longrightarrow> 
                 \<Lambda>,\<Gamma> \<turnstile> \<langle>Assert e, Normal n_s\<rangle> \<rightarrow> Normal n_s"
  | RedAssertFail: "\<lbrakk> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> (BoolV False) \<rbrakk> \<Longrightarrow> 
                  \<Lambda>,\<Gamma> \<turnstile> \<langle>Assert e, Normal n_s\<rangle> \<rightarrow> Failure"
  | RedAssumeOk: "\<lbrakk> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> (BoolV True) \<rbrakk> \<Longrightarrow> 
                \<Lambda>,\<Gamma> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> Normal n_s"
  | RedAssumeMagic: "\<lbrakk> \<Gamma> \<turnstile> \<langle>e, n_s\<rangle> \<Down> (BoolV False) \<rbrakk> \<Longrightarrow> 
                \<Lambda>,\<Gamma> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> Magic"
  | RedAssign: "\<lbrakk>\<Gamma> \<turnstile> \<langle>(map snd upds), n_s\<rangle> [\<Down>] vs \<rbrakk> \<Longrightarrow>
               \<Lambda>,\<Gamma> \<turnstile> \<langle>Assign upds, Normal n_s\<rangle> \<rightarrow>  Normal (n_s((map fst upds) [\<mapsto>] vs))"  
  | RedHavoc: "\<lbrakk> \<Lambda> x = Some ty; type_of_val v = ty \<rbrakk> \<Longrightarrow>
               \<Lambda>,\<Gamma> \<turnstile> \<langle>Havoc x, Normal n_s\<rangle> \<rightarrow> Normal (n_s(x \<mapsto> v))"
  | RedPropagateMagic: "\<Lambda>,\<Gamma> \<turnstile> \<langle>s, Magic\<rangle> \<rightarrow> Magic"
  | RedPropagateFailure: "\<Lambda>,\<Gamma> \<turnstile> \<langle>s, Failure\<rangle> \<rightarrow> Failure"

inductive_cases RedAssertOk_case: "\<Lambda>,\<Gamma> \<turnstile> \<langle>Assert e, Normal n_s\<rangle> \<rightarrow> Normal n_s"
inductive_cases RedAssumeOk_case: "\<Lambda>,\<Gamma> \<turnstile> \<langle>Assume e, Normal n_s\<rangle> \<rightarrow> Normal n_s"

inductive red_cmd_list :: "var_context \<Rightarrow> fun_context \<Rightarrow> cmd list \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  ("_,_ \<turnstile> ((\<langle>_,_\<rangle>) [\<rightarrow>]/ _)" [51,0,0,0] 81)
  for \<Lambda> :: var_context and \<Gamma> :: fun_context
  where
    RedCmdListNil: "\<Lambda>,\<Gamma> \<turnstile> \<langle>[],s\<rangle> [\<rightarrow>] s"
  | RedCmdListCons: "\<lbrakk> \<Lambda>,\<Gamma> \<turnstile> \<langle>c,s\<rangle> \<rightarrow> s'; \<Lambda>,\<Gamma> \<turnstile> \<langle>cs,s'\<rangle> [\<rightarrow>] s'' \<rbrakk> \<Longrightarrow> 
                   \<Lambda>,\<Gamma> \<turnstile> \<langle>(c # cs), s\<rangle> [\<rightarrow>] s''"

inductive_cases RedCmdListNil_case [elim]: "\<Lambda>,\<Gamma> \<turnstile> \<langle>[],s\<rangle> [\<rightarrow>] s"
inductive_cases RedCmdListCons_case [elim]: "\<Lambda>,\<Gamma> \<turnstile> \<langle>(c # cs), s\<rangle> [\<rightarrow>] s''"

type_synonym cfg_config = "(node+unit) \<times> state"

inductive red_cfg :: "var_context \<Rightarrow> fun_context \<Rightarrow> mbodyCFG \<Rightarrow> cfg_config \<Rightarrow> cfg_config \<Rightarrow> bool"
  ("_,_,_ \<turnstile> (_ -n\<rightarrow>/ _)" [51,0,0,0] 81)
  for \<Lambda> :: var_context and \<Gamma> :: fun_context and G :: mbodyCFG
  where
    RedNode: "\<lbrakk>node_to_block(G) n = Some cs; \<Lambda>,\<Gamma> \<turnstile> \<langle>cs,s\<rangle> [\<rightarrow>] s'; n' \<in> out_edges(G) n  \<rbrakk> \<Longrightarrow> 
              \<Lambda>, \<Gamma>, G  \<turnstile> (Inl n,s) -n\<rightarrow> (Inl n',s')"
  | RedReturn: "\<lbrakk>node_to_block(G) n = Some cs; \<Lambda>, \<Gamma> \<turnstile> \<langle>cs,s\<rangle> [\<rightarrow>] s'; (out_edges(G) n) = {} \<rbrakk> \<Longrightarrow> 
               \<Lambda>, \<Gamma>, G  \<turnstile> (Inl n,s) -n\<rightarrow> (Inr (),s')"

abbreviation red_cfg_multi :: "var_context \<Rightarrow> fun_context \<Rightarrow> mbodyCFG \<Rightarrow> cfg_config \<Rightarrow> cfg_config \<Rightarrow> bool"
  ("_,_,_ \<turnstile>_ -n\<rightarrow>*/ _" [51,0,0,0] 81)
  where "red_cfg_multi \<Lambda> \<Gamma> G \<equiv> rtranclp (red_cfg \<Lambda> \<Gamma> G)"

fun fun_interp_single_wf :: "ty list \<times> ty \<Rightarrow> (val list \<rightharpoonup> val) \<Rightarrow> bool"
  where "fun_interp_single_wf (args_ty, ret_ty) f =
             ((\<forall> vs. map type_of_val vs = args_ty \<longleftrightarrow> (\<exists>v. f vs = Some v)) \<and>
              (\<forall> vs v. (f vs = Some v) \<longrightarrow> type_of_val v = ret_ty) ) "

definition fun_interp_wf :: "fdecls \<Rightarrow> fun_interp \<Rightarrow> bool"
  where "fun_interp_wf fds \<gamma>_interp = 
            (\<forall>fn fd. fds fn = Some fd \<longrightarrow> 
                  (\<exists>f. \<gamma>_interp fn = Some f \<and> fun_interp_single_wf fd f ))"

definition domain_wf :: "vdecls \<Rightarrow> vdecls \<Rightarrow> vname set"
  where "domain_wf args locals = (Map.dom args \<union> Map.dom locals)"

(* definition does not make sense if args and locals have same names *)
definition state_typ_wf :: "nstate \<Rightarrow> vdecls \<Rightarrow> vdecls \<Rightarrow> bool"
  where "state_typ_wf ns args locals = 
           (\<forall> v v_ty. args v = Some v_ty \<or> locals v = Some v_ty \<longrightarrow> 
                          Option.map_option type_of_val (ns(v)) = Some v_ty)"

definition method_body_verifies :: "vdecls \<Rightarrow> fdecls \<Rightarrow> fun_interp \<Rightarrow> mbodyCFG \<Rightarrow> nstate \<Rightarrow> bool"
  where "method_body_verifies vds fds \<gamma>_interp mbody ns = 
      (\<forall> m s'. (vds, (fds, \<gamma>_interp), mbody \<turnstile> (Inl (entry(mbody)), Normal ns) -n\<rightarrow>* (m,s')) \<longrightarrow> s' \<noteq> Failure)"

(* not most compact representation (dom ns =... implied by ... type_ofval (ns(v)) = Some v_ty) *)
fun method_verify :: "prog \<Rightarrow> mdecl \<Rightarrow> bool"
  where 
    "method_verify (Program fdecls mdecls) (mname, args, locals, mbody) = 
    (\<forall>\<gamma>_interp. fun_interp_wf fdecls \<gamma>_interp \<longrightarrow>
     (\<forall>ns. 
      ( dom ns = domain_wf args locals \<longrightarrow>
        state_typ_wf ns args locals \<longrightarrow>
        method_body_verifies (map_add args locals) fdecls \<gamma>_interp mbody ns
     )
    ))"

lemma expr_eval_determ: 
shows "((\<Gamma> \<turnstile> \<langle>e1, s\<rangle> \<Down> v) \<Longrightarrow> ((\<Gamma> \<turnstile> \<langle>e1, s\<rangle> \<Down> v') \<Longrightarrow> v = v'))"  
    and "(\<Gamma> \<turnstile> \<langle>es, s\<rangle> [\<Down>] vs) \<Longrightarrow> (\<Gamma> \<turnstile> \<langle>es, s\<rangle> [\<Down>] vs') \<Longrightarrow> vs = vs' "
proof (induction arbitrary: v' and vs' rule: red_expr_red_exprs.inducts)
  case (RedVar n_s x v)
  assume "n_s x = Some v"
  assume "\<Gamma> \<turnstile> \<langle>Var x,n_s\<rangle> \<Down> v'"
  then show ?case using \<open>n_s x = Some v\<close> by (cases; simp)
next
  case (RedVal v n_s)
  assume "\<Gamma> \<turnstile> \<langle>Val v,n_s\<rangle> \<Down> v'"
  then show ?case by (cases; simp)
next
  case (RedBinOp e1 n_s v1 e2 v2 bop v)
  from RedBinOp.prems show ?case
  proof (cases)
    fix v1' v2'
    assume "\<Gamma> \<turnstile> \<langle>e1,n_s\<rangle> \<Down> v1'" hence "v1 = v1'" using RedBinOp.IH by simp
    assume "\<Gamma> \<turnstile> \<langle>e2,n_s\<rangle> \<Down> v2'" hence "v2 = v2'" using RedBinOp.IH by simp
    assume "binop_eval bop v1' v2' = Some v'"
    with \<open>v1 = v1'\<close> \<open>v2 = v2'\<close> show ?thesis using RedBinOp.hyps by simp
  qed
next
  case (RedUnOp e n_s v uop v' veval)
  from RedUnOp.prems show ?case
  proof (cases)
    fix v2
    assume "\<Gamma> \<turnstile> \<langle>e,n_s\<rangle> \<Down> v2" hence "v2 = v" using RedUnOp.IH by simp
    assume "unop_eval uop v2 = Some veval"
    with \<open>v2 = v\<close> show ?thesis using RedUnOp.hyps by simp
  qed
next
  case (RedFunOp args n_s v_args f f_interp v)
  from RedFunOp.prems show ?case
  proof (cases)
    fix v_args' f_interp'
    assume "\<Gamma> \<turnstile> \<langle>args,n_s\<rangle> [\<Down>] v_args'" hence "v_args = v_args'" using RedFunOp.IH by simp
    assume "snd \<Gamma> f = Some f_interp'" hence "f_interp = f_interp'" using RedFunOp.IH by simp
    assume "f_interp' v_args' = Some v'"
    thus ?case using \<open>v_args = v_args'\<close> \<open>f_interp = f_interp'\<close> using RedFunOp.hyps by simp
  qed
next
  case (RedExpListNil n_s vs')
  thus ?case by (cases; simp)
next
  case (RedExpListCons e n_s v es vs' vs'')
  assume "\<Gamma> \<turnstile> \<langle>e # es,n_s\<rangle> [\<Down>] vs''"
  thus ?case 
  proof cases
    fix w ws      
    assume "\<Gamma> \<turnstile> \<langle>e,n_s\<rangle> \<Down> w" hence "v = w" using RedExpListCons.IH by simp
    assume "\<Gamma> \<turnstile> \<langle>es,n_s\<rangle> [\<Down>] ws" hence "ws = vs'" using RedExpListCons.IH by simp  
    moreover assume "vs'' = w # ws"
    ultimately show ?thesis using \<open>v = w\<close>  by simp
  qed
qed

lemma step_nil_same:
  assumes A1: "\<Lambda>,\<Gamma> \<turnstile> \<langle>[], s\<rangle> [\<rightarrow>] s''"
  shows "s = s''"
proof -
  from A1 show ?thesis by (cases; auto)
qed

lemma no_out_edges_return:
  assumes 
    A1: "\<Lambda>, \<Gamma>, G \<turnstile> (Inl n,s) -n\<rightarrow> (Inl n', s')" and 
    A2: "(out_edges(G) n) = {}"
  shows False
  using A1 A2 red_cfg.simps by auto

lemma magic_stays_cmd:
  assumes "\<Lambda>,\<Gamma> \<turnstile> \<langle>c, Magic\<rangle> \<rightarrow> s'"
  shows "s' = Magic"
  using assms
  by (cases rule: red_cmd.cases)

lemma magic_stays_cmd_list:
  assumes "\<Lambda>,\<Gamma> \<turnstile> \<langle>cs, Magic\<rangle> [\<rightarrow>] s'"
  shows   " s' = Magic"
  using assms 
proof (induction cs Magic s' rule: red_cmd_list.induct)
  case RedCmdListNil
  then show ?case by simp
next
  case (RedCmdListCons c s' cs s'')
  then show ?case using magic_stays_cmd by simp
qed

lemma magic_stays_cfg:
  assumes "\<Lambda>, \<Gamma>, G \<turnstile> (m, Magic) -n\<rightarrow> (m', s')"
  shows " s' = Magic"
  using assms
proof (cases rule: red_cfg.cases)
  case (RedNode n cs n')
  then show ?thesis using magic_stays_cmd_list by simp
next
  case (RedReturn n cs)
  then show ?thesis using magic_stays_cmd_list by simp
qed

lemma magic_stays_cfg_multi:
  assumes
    "\<Lambda>, \<Gamma>, G \<turnstile> (m, Magic) -n\<rightarrow>* (m', s')"
  shows "s' = Magic"
  using assms
proof (induction rule: rtranclp_induct2)
  case refl
  then show ?case by simp
next
  case (step a1 b1 a2 b2)
  then show ?case using magic_stays_cfg by simp
qed

lemma finished_remains: 
  assumes "\<Lambda>, \<Gamma>, G \<turnstile> (Inr (), n_s) -n\<rightarrow>* (m',n')"
  shows "(m',n') = (Inr(), n_s)"
  using assms
proof (induction rule: rtranclp_induct2)
  case refl
  then show ?case by simp
next
  case (step a b a' b')
  from step.hyps(2) show ?case
  proof (cases)
    case (RedNode n cs n')
    then show ?thesis using step.IH by simp
  next
    case (RedReturn n cs)
    then show ?thesis using step.IH by simp
  qed
qed

end