theory TypingHelper
imports Typing
begin

(* Dummy definition making it easier to instantiate the type substitution
*)
definition hint_ty_subst :: "ty list \<Rightarrow> bool"
  where "hint_ty_subst ty_inst = True"

lemma typ_binop_poly_helper:
  assumes "hint_ty_subst ty_inst" and
          "binop_poly_type bop" and
          "F,\<Delta> \<turnstile> e1 : ty1" and
          "F,\<Delta> \<turnstile> e2 : ty2" and          
          "msubstT_opt ty_inst ty1 = msubstT_opt ty_inst ty2"
  shows "F,\<Delta> \<turnstile> e1 \<guillemotleft>bop\<guillemotright> e2 : TPrim (TBool)"
  using assms TypBinopPoly
  by blast

lemma typ_funexp_helper:
  assumes "map_of F f = Some (n_ty_params, args_ty, ret_ty)" and
          "length ty_params = n_ty_params" and
          "length args = length args_ty" and
          "\<tau> = (msubstT_opt ty_params ret_ty)" and
          "F,\<Delta> \<turnstile> args [:] (map (msubstT_opt ty_params) args_ty)"
        shows "F,\<Delta> \<turnstile> FunExp f ty_params args : \<tau>"
  using assms TypFunExp
  by blast
     
end