theory TypingML        
  imports TypingHelper HelperML
begin               

ML \<open>

(*
To prove a typing relation in the presence of type variables, one needs to know what 
type variable substitution to use for equality and inequality.
The tactic implemented here takes this information in the form of a tree (see typing_poly_hint) that
reflects the structure of the expression to be typed. At each node of the tree, the hint is either
NoPolyHint (in which case no hint is required for that entire subtree) or PolyyHintNode (in which
case there is a potential theorem indicating what needs to be applied at that point and a hint tree
for each subnode). 
For optimization reasons, we use trees that only reflect nodes that can branch (i.e., binary
operations and function calls currently). For all other nodes no hint is required and since they
only have one subnode one does not need to represent them using a separate node. 
*)

datatype typing_poly_hint = NoPolyHint | PolyHintNode of (thm option * (typing_poly_hint list))

fun has_poly_hint NoPolyHint = false
 |  has_poly_hint (PolyHintNode (NONE, _ )) = false
 |  has_poly_hint (PolyHintNode (SOME _, _ )) = true

fun the_poly_hint NoPolyHint = error("invoked the_poly_hint on NoPolyHint")
  | the_poly_hint (PolyHintNode (thm, hints)) = (thm, hints)

fun typing_tac ctxt hint_thm_tree lookup_assms func_assms =  
  FIRST_AND_THEN' 
    [ resolve_tac ctxt [@{thm TypVar}],
      resolve_tac ctxt [@{thm TypBVar}],
      resolve_tac ctxt [@{thm TypPrim}],
      resolve_tac ctxt [@{thm TypUnOp}],
      resolve_tac ctxt [@{thm TypBinOpMono}] THEN' assm_full_simp_solved_tac ctxt,
      if has_poly_hint hint_thm_tree then
        resolve_tac ctxt [@{thm typ_binop_poly_helper_2}] THEN' assm_full_simp_solved_tac ctxt
      else 
        resolve_tac ctxt [@{thm typ_binop_poly_helper_empty}] THEN' assm_full_simp_solved_tac ctxt,
      resolve_tac ctxt [@{thm typ_funexp_helper}],
      resolve_tac ctxt [@{thm TypOld}],
      resolve_tac ctxt [@{thm TypForall}],
      resolve_tac ctxt [@{thm TypExists}],
      resolve_tac ctxt [@{thm TypForallT}],
      resolve_tac ctxt [@{thm TypExistsT}]
    ]
    [ (* Var *)
      assm_full_simp_solved_tac (ctxt addsimps lookup_assms),
      (* BVar *)
      assm_full_simp_solved_tac ctxt,
      (* Prim *)
      assm_full_simp_solved_tac ctxt, 
      (* Unop *)
      fn i => fn st => (((typing_tac ctxt hint_thm_tree lookup_assms func_assms) |> SOLVED') THEN' 
                      assm_full_simp_solved_tac ctxt) i st,
      (* Binop Mono *)
      fn i => fn st => (i,st) |-> (
                        let val (hints1, hints2) = 
                                case hint_thm_tree of
                                  NoPolyHint => (NoPolyHint, NoPolyHint)
                                | PolyHintNode (_, ([h1, h2])) => (h1, h2)
                                | _ => error("hints not in correct format for binop mono")

                                   in
                        (typing_tac ctxt hints1 lookup_assms func_assms |> SOLVED') THEN'
                        (typing_tac ctxt hints2 lookup_assms func_assms |> SOLVED') THEN' 
                        assm_full_simp_solved_tac ctxt
                        end
                       ),

      (* Binop Poly *)
      binop_poly_tac ctxt hint_thm_tree lookup_assms func_assms,
      (* FunExp *)
      (assm_full_simp_solved_tac (ctxt addsimps func_assms)) THEN'
      assm_full_simp_solved_tac ctxt THEN' assm_full_simp_solved_tac ctxt THEN' 
        (* goal: \<tau> = (msubstT_opt ty_params ret_ty) *)
      asm_full_simp_tac (ctxt addsimps [@{thm msubstT_opt_def}]) THEN'
        (* before this final tactic the goal is of the form \<open>map (msubstT_opt ty_params) args_ty\<close>, which we want to simplify fully *)
      asm_full_simp_tac (ctxt addsimps [@{thm msubstT_opt_def}]) THEN'
      typing_list_tac ctxt hint_thm_tree lookup_assms func_assms,

      (* Old *)
      fn i => fn st  => ((typing_tac ctxt hint_thm_tree lookup_assms func_assms) |> SOLVED') i st,
    
      (* Forall *)
      fn i => fn st => ((typing_tac ctxt hint_thm_tree lookup_assms func_assms) |> SOLVED') i st,

      (* Exists *)
      fn i => fn st => ((typing_tac ctxt hint_thm_tree lookup_assms func_assms) |> SOLVED') i st,

      (* ForallT *)
      fn i => fn st => ((typing_tac ctxt hint_thm_tree lookup_assms func_assms) |> SOLVED') i st,

      (* ExistsT *)
      fn i => fn st => ((typing_tac ctxt hint_thm_tree lookup_assms func_assms) |> SOLVED') i st
    ]
 and  
   typing_list_tac ctxt hint_thm_tree lookup_assms func_assms = 
      resolve_tac ctxt [@{thm TypListNil}] ORELSE'
      (resolve_tac ctxt [@{thm TypListCons}] THEN' 
       (fn i => fn st => (i, st) |-> 
                          ( let val (hint1, hint_tail) = 
                                  case hint_thm_tree of
                                    NoPolyHint => (NoPolyHint, NoPolyHint)
                                  | PolyHintNode (t, h1 :: htail) => (h1, PolyHintNode (t, htail))
                                  | _ => error("hints not in correct format for binop mono")
                            in
                            (typing_tac ctxt hint1 lookup_assms func_assms |> SOLVED') THEN' 
                            (typing_list_tac ctxt hint_tail lookup_assms func_assms)
                            end
                          )
       )
      )
 and 
   binop_poly_tac ctxt hint_thm_tree lookup_assms func_assms i st = 
      case hint_thm_tree of
       PolyHintNode (hint_thm_opt, [h1,h2]) => 
        (i, st) |->
        ( (if is_some hint_thm_opt then resolve_tac ctxt [the hint_thm_opt] else K all_tac) THEN'
          ((typing_tac ctxt h1 lookup_assms func_assms) |> SOLVED') THEN'
          ((typing_tac ctxt h2 lookup_assms func_assms) |> SOLVED') THEN' 
          assm_full_simp_solved_tac (ctxt addsimps [@{thm msubstT_opt_def}])
        )
      | NoPolyHint => 
        (i, st) |->
        ( 
          ((typing_tac ctxt NoPolyHint lookup_assms func_assms) |> SOLVED') THEN'
          ((typing_tac ctxt NoPolyHint lookup_assms func_assms) |> SOLVED') THEN' 
          assm_full_simp_solved_tac ctxt
        )
     | _ => error("hints not in correct format for binop mono")
\<close>

end