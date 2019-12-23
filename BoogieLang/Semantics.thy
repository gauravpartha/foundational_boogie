theory Semantics
imports Lang CFG
begin

datatype state = Normal "vname \<rightharpoonup> val" | Failure

(* define context *)
datatype prog_context = Ctxt "fname \<rightharpoonup> (val list \<Rightarrow> val list)"

fun binop_lessThan :: "val \<Rightarrow>  val \<rightharpoonup> val"
where
  "binop_lessThan (Intg i1) (Intg i2) = Some (Bool (i1 < i2))"
| "binop_lessThan _ _ = None"

fun binop_add :: "val \<Rightarrow> val \<rightharpoonup> val"
  where 
    "binop_add (Intg i1) (Intg i2) = Some (Intg (i1 + i2))"
  | "binop_add _ _ = None"
   
fun binop_and :: "val \<Rightarrow> val \<rightharpoonup> val"
  where
    "binop_and (Bool b1) (Bool b2) = Some (Bool (b1 \<and> b2))"
  | "binop_and _ _ = None"

(*
fun feval :: "'m prog \<Rightarrow> prog_context \<Rightarrow> fname  \<Rightarrow> val list \<rightharpoonup> val"
  where
    "feval P (Ctxt \<Gamma>) fn vs =
          (case (\<Gamma> fn) of (Some f_sem) \<Rightarrow> f_sem vs | None \<Rightarrow> None)"
*)

fun binop_eval ::"binop \<Rightarrow> val \<Rightarrow> val \<rightharpoonup> val"
  where
   "binop_eval Eq v1 v2 = Some (Bool (v1 = v2))"
 | "binop_eval Add v1 v2 = binop_add v1 v2"
 | "binop_eval Le v1 v2 = binop_lessThan v1 v2"
 | "binop_eval And v1 v2 = binop_and v1 v2"


(*
  = Var vname
  | Val val
  | BinOp "(expr)" binop "(expr)" ("_ \<guillemotleft>_\<guillemotright> _" [80,0,81] 80) 
  | FunExp fname "(expr list)"
*)

fun expr_eval :: "prog_context \<Rightarrow> expr \<Rightarrow> state \<rightharpoonup> val"
  where 
    "expr_eval \<Gamma> (Var x) s = s(x)"
  | "expr_eval \<Gamma> (Val v ) s = v"
  | "expr_eval \<Gamma> (e1 \<guillemotleft>op\<guillemotright> e2) s = binop_eval op (expr_eval \<Gamma> e1 s) (expr_eval \<Gamma> e2 s)"
  | "FunExp fn vs = _"


inductive instr_step :: "prog_context \<Rightarrow> cmd \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  ("_\<turnstile> ((_,_) \<rightarrow>/ _)" [81,81,81] 100)
  for \<Gamma> :: prog_context
  where
    Assert: "\<lbrakk>\<Gamma> \<turnstile> (Assert e, s) \<rightarrow> s"

end