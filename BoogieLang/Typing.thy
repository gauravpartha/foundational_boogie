section \<open>Boogie's Type System\<close>

theory Typing
imports Lang BoogieDeBruijn
begin

text \<open>A type environment consists of a type mapping for all the variable names and a type mapping for
the DeBruijn indices\<close>
type_synonym type_env = "(vname \<rightharpoonup> ty) \<times> (nat \<rightharpoonup> ty)"

fun unop_type :: "unop \<Rightarrow> prim_ty \<Rightarrow> prim_ty option"
  where 
    "unop_type UMinus TInt = Some TInt"
  | "unop_type UMinus TReal = Some TReal"
  | "unop_type UMinus TBool = None"
  | "unop_type Not TInt = None"
  | "unop_type Not TReal = None"
  | "unop_type Not TBool = Some TBool"
  | "unop_type IntToReal TInt = Some TReal"
  | "unop_type IntToReal TReal = None"
  | "unop_type IntToReal TBool = None"

primrec binop_type :: "binop \<Rightarrow> ((prim_ty \<times> prim_ty) set \<times> prim_ty) option"
  where
    "binop_type Eq = None"
  | "binop_type Neq = None"
  | "binop_type RealDiv = Some ({(TInt, TInt), (TReal, TReal), (TInt, TReal), (TReal, TInt)}, TReal)" 
  | "binop_type Add = Some ({(TInt, TInt)}, TInt)"
  | "binop_type Sub = Some ({(TInt, TInt)}, TInt)"
  | "binop_type Mul = Some ({(TInt, TInt)}, TInt)"
  | "binop_type Div = Some ({(TInt, TInt)}, TInt)"
  | "binop_type Mod = Some ({(TInt, TInt)}, TInt)"
  | "binop_type Lt = Some ({(TInt, TInt), (TReal, TReal)}, TBool)"
  | "binop_type Le = Some ({(TInt, TInt), (TReal, TReal)}, TBool)"
  | "binop_type Gt = Some ({(TInt, TInt), (TReal, TReal)}, TBool)"
  | "binop_type Ge = Some ({(TInt, TInt), (TReal, TReal)}, TBool)"
  | "binop_type And = Some ({(TBool, TBool)}, TBool)"
  | "binop_type Or = Some ({(TBool, TBool)}, TBool)"
  | "binop_type Imp = Some ({(TBool, TBool)}, TBool)"
  | "binop_type Iff = Some ({(TBool, TBool)}, TBool)"

fun binop_poly_type :: "binop \<Rightarrow> bool"
  where 
    "binop_poly_type Eq = True"
  | "binop_poly_type Neq = True"
  | "binop_poly_type _ = False"

inductive typing :: "fdecls \<Rightarrow> type_env \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool" ("_,_ \<turnstile> (_ : _)" [51,0,0,0] 81)
and typing_list :: "fdecls \<Rightarrow> type_env \<Rightarrow> expr list \<Rightarrow> ty list \<Rightarrow> bool" ("_,_ \<turnstile> (_ [:] _)" [51,0,0,0] 81)
  for F :: fdecls
  where
    TypVar: "\<lbrakk> (fst \<Delta>) x = Some ty \<rbrakk> \<Longrightarrow> F,\<Delta> \<turnstile> Var x : ty"
  | TypBVar: "\<lbrakk> (snd \<Delta>) i = Some ty \<rbrakk> \<Longrightarrow> F,\<Delta> \<turnstile> BVar i : ty"
  | TypPrim: "\<lbrakk> type_of_lit l = prim_ty \<rbrakk> \<Longrightarrow> F,\<Delta> \<turnstile> Lit l : TPrim prim_ty"
  | TypUnOp: "\<lbrakk> F,\<Delta> \<turnstile> e : TPrim arg_ty; unop_type uop arg_ty = Some ret_ty \<rbrakk>  \<Longrightarrow> 
               F,\<Delta> \<turnstile> UnOp uop e : TPrim ret_ty"
  | TypBinOpMono: "\<lbrakk> binop_type bop = Some (targs, ret_ty); 
                     F,\<Delta> \<turnstile> e1 : TPrim left_ty; 
                     F,\<Delta> \<turnstile> e2 : TPrim right_ty;
                     (left_ty, right_ty) \<in> targs  \<rbrakk> \<Longrightarrow>
                    F,\<Delta> \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 : TPrim ret_ty"
  (* equality and inequality are typed more liberally as also outlined in 
      This is Boogie (Leino) and
      A polymorphic intermediate verification language: Design and logical encoding (Leino and Ruemmer) *)
  | TypBinopPoly: "\<lbrakk> binop_poly_type bop; 
                     F,\<Delta> \<turnstile> e1 : ty1; F,\<Delta> \<turnstile> e2 : ty2;
                     msubstT_opt ty_inst ty1 = msubstT_opt ty_inst ty2\<rbrakk> \<Longrightarrow> 
        F,\<Delta> \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 : TPrim (TBool)"
  | TypFunExp: "\<lbrakk> map_of F f = Some (n_ty_params, args_ty, ret_ty);
                  length ty_params = n_ty_params;
                  length args = length args_ty;
                  F,\<Delta> \<turnstile> args [:] (map (msubstT_opt ty_params) args_ty) \<rbrakk> \<Longrightarrow> 
                F,\<Delta> \<turnstile> FunExp f ty_params args : (msubstT_opt ty_params ret_ty)"
  | TypCondExp: "\<lbrakk> F,\<Delta> \<turnstile> cond : TPrim (TBool);
                   F,\<Delta> \<turnstile> thn : ty;
                   F,\<Delta> \<turnstile> els : ty \<rbrakk> \<Longrightarrow>
                F,\<Delta> \<turnstile> CondExp cond thn els : ty"
  | TypOld: "\<lbrakk> F, \<Delta> \<turnstile> e : ty \<rbrakk> \<Longrightarrow> F, \<Delta>  \<turnstile> Old e : ty"
  | TypForall: "\<lbrakk> F, (fst \<Delta>, ext_env (snd \<Delta>) ty) \<turnstile> e : TPrim (TBool) \<rbrakk> \<Longrightarrow> F,\<Delta> \<turnstile> Forall ty e : TPrim (TBool)"
  | TypExists: "\<lbrakk> F, (fst \<Delta>, ext_env (snd \<Delta>) ty) \<turnstile> e : TPrim (TBool) \<rbrakk> \<Longrightarrow> F,\<Delta> \<turnstile> Exists ty e : TPrim (TBool)"
  | TypForallT: "\<lbrakk> F,(shift_env 1 0 (fst \<Delta>), shift_env 1 0 (snd \<Delta>)) \<turnstile> e : TPrim (TBool)\<rbrakk> \<Longrightarrow> F, \<Delta> \<turnstile> ForallT e : TPrim (TBool)"
  | TypExistsT: "\<lbrakk> F, (shift_env 1 0 (fst \<Delta>), shift_env 1 0 (snd \<Delta>)) \<turnstile> e : TPrim (TBool)\<rbrakk> \<Longrightarrow> F, \<Delta> \<turnstile> ExistsT e : TPrim (TBool)"
  | TypListNil: "F,\<Delta> \<turnstile> [] [:] []"
  | TypListCons: "\<lbrakk> F,\<Delta> \<turnstile> e : ty;  F,\<Delta> \<turnstile> es [:] tys \<rbrakk> \<Longrightarrow> F,\<Delta> \<turnstile> (e#es) [:] (ty#tys)"
end