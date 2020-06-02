theory m
imports Lang Semantics
begin

fun outEdges_m
  where
    "outEdges_m (0) = {(Suc(0))}"
    |"outEdges_m (Suc(0)) = {}"
    |"outEdges_m _ = {}"

fun nodeToBlocks_m
  where
    "nodeToBlocks_m (0) = (Some 
            [(Assume (BinOp (FunExp ''f'' [(Var ''x'')]) Le  (Val (IntV 5)))),
              Assume (BinOp (Val (IntV 6)) Le (Var ''y'') )])"
  |"nodeToBlocks_m (Suc(0)) = (Some [                  
                 (Assert (BinOp (FunExp ''f'' [(Var ''x'')]) Le (Var ''y'')))
                ])"
  |"nodeToBlocks_m _ = (None )"

abbreviation G
  where "G \<equiv> (|entry = 0, nodes = {(0), (Suc(0))}, out_edges = outEdges_m, node_to_block = nodeToBlocks_m|)"

definition ProgramM
  where
    "ProgramM  = (Program [(''f'', [TInt], TInt)] [(''m'', [], [(''x'', TInt), (''y'', TInt)], G)])"

locale vc =
  fixes x :: int and y :: int and f :: "int \<Rightarrow> int"

context vc
begin

abbreviation block1
  where "block1 \<equiv> (f x \<le> y)"

abbreviation block0
  where "block0 \<equiv> ((f x \<le> 5 \<and> 6 \<le> y) \<longrightarrow> block1)"

abbreviation block0_normal
  where "block0_normal \<equiv> f x \<le> 5 \<and> 6 \<le> y"

lemma vc_correct: "block0"
  by smt

end

lemma block1_correct: 
  assumes 
   A1:"\<Gamma> \<turnstile> \<langle>Option.option.the(nodeToBlocks_m (Suc(0))), Normal s\<rangle> [\<rightarrow>] s'" and
   A2:"(snd \<Gamma>) ''f'' = Some f" and
   A3:"s ''x'' = Some (IntV ix)" and
   A4:"s ''y'' = Some (IntV iy)" and
   A5:"\<forall> i :: int. f [IntV i] = Some (IntV (f' i))" and
   A6:"vc.block1 ix iy f'"
 shows "s' \<noteq> Failure"
proof -
  from A1 have "\<Gamma> \<turnstile> \<langle>[Assert (BinOp (FunExp ''f'' [(Var ''x'')]) Le (Var ''y''))],Normal s\<rangle> [\<rightarrow>] s'"
    by simp
  then show ?thesis
  proof cases
    case (RedCmdListCons s'')
    hence Asame:"s'' = s'" by (simp add: step_nil_same)
 (*hence A7: "c =  (Assert (BinOp (FunExp ''f'' [(Var ''x'')]) Le (Var ''y'')))" by simp*)
    have ACorrect:"\<Gamma> \<turnstile> \<langle>(BinOp (FunExp ''f'' [(Var ''x'')]) Le (Var ''y'')), s\<rangle> \<Down> (BoolV True)"
    proof (rule RedBinOp)
      show "\<Gamma> \<turnstile> \<langle>FunExp ''f'' [Var ''x''],s\<rangle> \<Down> (IntV (f' ix))"
        proof (rule)
        show "\<Gamma> \<turnstile> \<langle>[Var ''x''],s\<rangle> [\<Down>] [IntV ix]"
        proof (rule)
          show "\<Gamma> \<turnstile> \<langle>Var ''x'',s\<rangle> \<Down> IntV ix" using A3 by rule
          show "\<Gamma> \<turnstile> \<langle>[],s\<rangle> [\<Down>] []" by rule
        qed
      next
        show "snd \<Gamma> ''f'' = Some f" using A2 by simp
      next
        show "f [IntV ix] = Some (IntV (f' ix))" using A5 by simp
      qed
    next
      show "\<Gamma> \<turnstile> \<langle>Var ''y'',s\<rangle> \<Down> (IntV (iy))" using A4 by rule
    next
      show "binop_eval Le (IntV (f' ix)) (IntV iy) = Some (BoolV True)" using A6 by simp
    qed
    (*assume "the (nodeToBlocks_m (Suc 0)) = c # cs"*)
    assume "\<Gamma> \<turnstile> \<langle>Assert (FunExp ''f'' [Var ''x''] \<guillemotleft>Le\<guillemotright> Var ''y''),Normal s\<rangle> \<rightarrow> s''"    
    thus ?thesis
    proof cases
      case (RedAssertOk)
      then show ?thesis using Asame by simp (* trivial: assertion goes through by assumption *)
    next
      case (RedAssertFail)
      then show ?thesis using expr_eval_determ ACorrect by fastforce (* use vc *)
    qed
  qed
qed

(* G is given above *)
lemma block1_verifies:
  assumes 
   A1: "\<Gamma>,G \<turnstile> (Inl (Suc 0), Normal n_s) -n\<rightarrow>* (n',s')" and
   A2:"(snd \<Gamma>) ''f'' = Some f" and
   A3:"n_s ''x'' = Some (IntV ix)" and
   A4:"n_s ''y'' = Some (IntV iy)" and
   A5:"\<forall> i :: int. f [IntV i] = Some (IntV (f' i))" and
   A6:"vc.block1 ix iy f'"
 shows "s' \<noteq> Failure"
  using assms
 proof (cases rule: converse_rtranclpE )
    case base
    thus ?thesis by auto
  next
    case (step cfg_config)
    assume B7:"\<Gamma>,G \<turnstile>cfg_config -n\<rightarrow>* (n', s')"
    assume A7: "\<Gamma>,G \<turnstile> (Inl (Suc 0),Normal n_s) -n\<rightarrow> cfg_config"
    thus ?thesis
    proof (cases)
      case (RedNode cs s' n')
      then show ?thesis by simp (* Suc 0 has no out dges *)
    next
      case (RedReturn cs s'')      
      hence C0:"(n',s') = (Inr (), s'')" using finished_remains B7 by simp      
      assume C1:"node_to_block G (Suc 0) = Some cs"
      assume C2:"\<Gamma> \<turnstile> \<langle>cs,Normal n_s\<rangle> [\<rightarrow>] s''"
      show ?thesis        
      proof (rule block1_correct)
        show "\<Gamma> \<turnstile> \<langle>the (nodeToBlocks_m (Suc 0)),Normal n_s\<rangle> [\<rightarrow>] s'" using C0 C1 C2 by simp
        show "snd \<Gamma> ''f'' = Some f" using assms by simp
        show "n_s ''x'' = Some (IntV ix)" using assms by simp
        show "n_s ''y'' = Some (IntV iy)" using assms by simp
        show "\<forall>i. f [IntV i] = Some (IntV (f' i))" using assms by simp
        show "f' ix \<le> iy" using assms by simp
      qed
    qed        
  qed

lemma block0_correct: 
  assumes 
   A1: "\<Gamma> \<turnstile> \<langle>Option.option.the(nodeToBlocks_m 0), Normal s\<rangle> [\<rightarrow>] s'" and
   A2: "(snd \<Gamma>) ''f'' = Some f" and
   A3: "s ''x'' = Some (IntV ix)" and
   A4: "s ''y'' = Some (IntV iy)" and
   A5: "\<forall> i :: int. f [IntV i] = Some (IntV (f' i))" and
   A6: "vc.block0 ix iy f'"
 shows "s' \<noteq> Failure \<and> (\<forall> n_s'. s' = Normal n_s' \<longrightarrow> (vc.block0_normal ix iy f' \<and> n_s' = s))" (is "?S1 \<and> ?S2")
proof -
  from A1 show ?thesis
  proof cases
  case RedCmdListNil
  then show ?thesis by simp
  next
    case (RedCmdListCons c s'' cs)
    (*hence Asame: "s'' = s'" using step_nil_same by simp*)
    assume A70: "\<Gamma> \<turnstile> \<langle>cs,s''\<rangle> [\<rightarrow>] s'"
    assume A7:"the (nodeToBlocks_m 0) = c # cs"
    assume A8:"\<Gamma> \<turnstile> \<langle>c,Normal s\<rangle> \<rightarrow> s''"
    thus ?thesis
    proof cases
      case (RedAssertOk e)
      then show ?thesis using A7 by simp
    next
      case (RedAssertFail e)
      then show ?thesis using A7 by simp
    next
      case (RedAssumeOk e)
      assume B1:"c = Assume e"
      assume B2:"s'' = Normal s"
      assume "\<Gamma> \<turnstile> \<langle>e,s\<rangle> \<Down> BoolV True"
      hence "f' ix \<le> 5" 
      proof cases
        case (RedVar x)
        then show ?thesis using B1 A7 by simp
      next
        case RedVal
        then show ?thesis using B1 A7 by simp
      next
        case (RedBinOp e1 v1 e2 v2 bop)          
        assume C1:"e = e1 \<guillemotleft>bop\<guillemotright> e2"
        assume C2:"\<Gamma> \<turnstile> \<langle>e2,s\<rangle> \<Down> v2"
        hence C3: "v2 = IntV 5" using C1 B1 A7 by (cases; auto)
        assume C4: "\<Gamma> \<turnstile> \<langle>e1,s\<rangle> \<Down> v1"
        hence C5: "v1 = IntV (f' ix)"
        proof cases
          case (RedVar x)
          then show ?thesis using C1 B1 A7 by simp
        next
          case RedVal
          then show ?thesis using C1 B1 A7 by simp
        next
          case (RedBinOp e1 v1 e2 v2 bop)
          then show ?thesis using C1 B1 A7 by simp
        next
          case (RedFunOp args v_args h f_interp)
          assume D1:"e1 = FunExp h args"
          assume D2:"snd \<Gamma> h = Some f_interp"
          assume D3:"f_interp v_args = Some v1"
          assume D4:"\<Gamma> \<turnstile> \<langle>args,s\<rangle> [\<Down>] v_args"
          hence "v_args = [(IntV ix)]"
          proof cases
            case RedExpListNil
            then show ?thesis using D1 C1 B1 A7 by simp
          next
            case (RedExpListCons e' v es' vs)
            hence E00: "es' = []" using A3 D1 C1 B1 A7 by simp
            assume E0: "\<Gamma> \<turnstile> \<langle>es',s\<rangle> [\<Down>] vs"
            hence E01: "vs = []" using E00 A3 D1 C1 B1 A7 by (cases; simp)              
            assume E1:"args = e' # es'"
            assume E2:"v_args = v # vs"
            assume E3:"\<Gamma> \<turnstile> \<langle>e',s\<rangle> \<Down> v"
            hence  E4:"v = (IntV ix)" using A3 E1 D1 C1 B1 A7 by (cases; simp)              
            then show ?thesis using E4 E01 E2 by simp
          qed
          then show ?thesis using C1 B1 A7 A3 A2 A5 D3 D2 D1 by auto
        qed                   
        assume "binop_eval bop v1 v2 = Some (BoolV True)"
        thus "f' ix \<le> 5" using C3 C5 C1 A7 B1  by simp        
      next
        case (RedFunOp args v_args f f_interp)
        then show ?thesis using B1 A7 by simp
      qed    
      from A70 show ?thesis
      proof cases
        case RedCmdListNil
        then show ?thesis using A7 by simp
      next
        case (RedCmdListCons c' s3 cs')          
        assume F1:"cs = c' # cs'"
        assume F2:"\<Gamma> \<turnstile> \<langle>cs',s3\<rangle> [\<rightarrow>] s'"
        hence "cs' = []" using A7 F1 by auto
        hence "s' = s3" using F2 step_nil_same by blast
        assume F3:"\<Gamma> \<turnstile> \<langle>c',s''\<rangle> \<rightarrow> s3"
        then show ?thesis
        proof (cases)
          case (RedAssertOk e n_s)         
            then show ?thesis using A7 F1 by simp
          next
          case (RedAssertFail e n_s)
            then show ?thesis using A7 F1 by simp
          next
            case (RedAssumeOk e n_s)
            assume G1:"c' = Assume e"
            assume G2:"s'' = Normal n_s"
            assume G3:"s3 = Normal n_s"
            assume G4:"\<Gamma> \<turnstile> \<langle>e,n_s\<rangle> \<Down> BoolV True"
            then show ?thesis 
            proof cases
              case (RedVar x)
              then show ?thesis using A7 G1 F1 by simp
            next
              case RedVal
              then show ?thesis using A7 G1 F1 by simp
            next
              case (RedBinOp e1 v1 e2 v2 bop)
              assume H1: "e = e1 \<guillemotleft>bop\<guillemotright> e2"
              assume H2: "\<Gamma> \<turnstile> \<langle>e1,n_s\<rangle> \<Down> v1"
              hence "v1 = (IntV 6)" using H1 A7 G1 F1 A4 by (cases; simp)
              assume H3: "\<Gamma> \<turnstile> \<langle>e2,n_s\<rangle> \<Down> v2"
              hence "v2 = (IntV iy)" using H1 A7 G1 F1 A4 G2 B2
                by(cases; fastforce)                  
              assume H4: "binop_eval bop v1 v2 = Some (BoolV True)"
              hence "6 \<le> iy" using \<open>v2 = IntV iy\<close> \<open>v1 = IntV 6\<close> H1 G1 F1 A7 by simp
              have "s' = Normal n_s" using \<open>s' = s3\<close> \<open>s3 = Normal n_s\<close> by simp
              show ?thesis
              proof (rule conjI)
                show "s' \<noteq> Failure" by (simp add: \<open>s' = Normal n_s\<close>) 
              next
                show "\<forall> n_s'. s' = Normal n_s' \<longrightarrow> ((f' ix \<le> 5 \<and> 6 \<le> iy) \<and> n_s' = s) "
                proof (rule allI)
                  fix n_s''
                  show "s' = Normal n_s'' \<longrightarrow> ((f' ix \<le> 5 \<and> 6 \<le> iy) \<and> n_s'' = s)"
                proof (rule impI)
                  assume "s' = Normal n_s''" 
                  show "((f' ix \<le> 5 \<and> 6 \<le> iy) \<and> n_s'' = s)"
                  proof (rule conjI)
                    show "f' ix \<le> 5 \<and> 6 \<le> iy" using \<open>f' ix \<le> 5\<close> \<open>6 \<le> iy\<close> by simp
                  next
                    show "n_s'' = s" using \<open>s' = Normal n_s''\<close> B2 G2 \<open>s' = s3\<close> \<open>s3 = Normal n_s\<close> by simp
                  qed
                qed
              qed
            qed 
              next
              case (RedFunOp args v_args f f_interp)
              then show ?thesis using A7 G1 F1 by simp
            qed              
          next
            case (RedAssumeMagic e n_s)
            with F2 show ?thesis using magic_stays_cmd_list by fastforce
          next
            case RedPropagateMagic
            then show ?thesis using B2 by simp
          next
            case RedPropagateFailure
            then show ?thesis using B2 by simp
          qed
        qed
      next      
    next
      case (RedAssumeMagic e)
      then show ?thesis using A70 magic_stays_cmd_list by fastforce
    qed
  qed
qed

lemma block0_verifies:
  fixes f' :: "int \<Rightarrow> int"
  assumes 
   A1: "\<Gamma>,G \<turnstile> (Inl 0, Normal n_s) -n\<rightarrow>* (n',s')" and
   A2:"(snd \<Gamma>) ''f'' = Some f" and
   A3:"n_s ''x'' = Some (IntV ix)" and
   A4:"n_s ''y'' = Some (IntV iy)" and
   A5:"\<forall> i :: int. f [IntV i] = Some (IntV (f' i))" and
   A6:"vc.block0 ix iy f'"
 shows "s' \<noteq> Failure"
proof -
  from A1 show ?thesis 
  proof (cases rule: converse_rtranclpE)
    case base
    then show ?thesis by auto
  next
    case (step cfg_config)
    assume A8: "\<Gamma>,G \<turnstile> cfg_config -n\<rightarrow>* (n',s')"
    assume "\<Gamma>,G \<turnstile> (Inl 0,Normal n_s) -n\<rightarrow> cfg_config"
    then show ?thesis
    proof cases
      case (RedNode cs s'' n'')
      assume "n'' \<in> out_edges G 0"
      hence "n'' = (Suc 0)" by simp
      assume "node_to_block G 0 = Some cs"
      moreover assume "\<Gamma> \<turnstile> \<langle>cs,Normal n_s\<rangle> [\<rightarrow>] s''"
      ultimately have A7: "\<Gamma> \<turnstile> \<langle>the (node_to_block G 0), Normal n_s\<rangle> [\<rightarrow>] s''" by simp
      have "s'' \<noteq> Failure \<and> (\<forall> n_s'. s'' = Normal n_s' \<longrightarrow> ( (f' ix \<le> 5 \<and> 6 \<le> iy) \<and> n_s' = n_s))"       
        thm block0_correct
      proof (rule block0_correct[of _ _ _ _ ix _ _ ])       
        show "\<Gamma> \<turnstile> \<langle>the (nodeToBlocks_m 0),Normal n_s\<rangle> [\<rightarrow>] s''" using A7 by simp
      next
        show "snd \<Gamma> ''f'' = Some f" using assms by simp
      next
        show "n_s ''x'' = Some (IntV ix)" using assms by simp 
      next
        show "n_s ''y'' = Some (IntV iy)" using assms by simp
      next
        show "\<forall>i. f [IntV i] = Some (IntV (f' i))" using assms by simp
      next
        show "vc.block0 ix iy f'" using assms by simp
      qed
      hence A9:"s'' \<noteq> Failure" and 
            A10:"(\<forall> n_s'. s'' = Normal n_s' \<longrightarrow> ((f' ix \<le> 5 \<and> 6 \<le> iy) \<and> n_s' = n_s))" by simp_all      
      show ?thesis
      proof (cases s'')
        case (Normal n_s')
        assume "s'' = Normal n_s'"
        hence A11:"\<Gamma>,G \<turnstile> (Inl n'', Normal n_s') -n\<rightarrow>* (n',s')" using A8 \<open>cfg_config = (Inl n'', s'')\<close> by simp
        from \<open>s'' = Normal n_s'\<close> have "(f' ix \<le> 5 \<and> 6 \<le> iy)" and "n_s' = n_s" using A10 by auto
        show ?thesis 
        proof (rule block1_verifies)
          show "\<Gamma>,G \<turnstile> (Inl (Suc 0), Normal n_s') -n\<rightarrow>* (n',s')" using \<open>n'' = Suc 0\<close> A11 by simp
        next
          show "(snd \<Gamma>) ''f'' = Some f" using assms by simp
        next
          show "n_s' ''x'' = Some (IntV ix)" using assms \<open>n_s' = n_s\<close> by simp
        next
          show "n_s' ''y'' = Some (IntV iy)" using assms \<open>n_s' = n_s\<close> by simp
        next
          show "\<forall>i. f [IntV i] = Some (IntV (f' i))" using assms by simp
        next
          show "f' ix \<le> iy" using assms \<open>f' ix \<le> 5 \<and> 6 \<le> iy\<close> by simp
        qed          
      next
        case Failure
        thus ?thesis using A9 by simp
      next
        case Magic
        then show ?thesis using A8 \<open>cfg_config = (Inl n'', s'')\<close> magic_stays_cfg_multi by fastforce
      qed
    next
      case (RedReturn cs s')
      thus ?thesis by simp
    qed
  qed
qed

(* method_verify (Program fdecls mdecls) (mname, args, vdecls, mbody) *)

lemma boogie_int_are_int:
  assumes "type_of_val v = TInt"
  obtains i where "v = IntV i"
  by (metis assms ty.distinct(1) type_of_val.simps(1) val.exhaust)

lemma boogie_bool_are_bool:
  assumes "type_of_val v = TBool"
  obtains b where "v = BoolV b"
  by (metis assms ty.distinct(1) type_of_val.simps(2) val.exhaust)

fun convert_val_to_int :: "val \<Rightarrow> int"
  where "convert_val_to_int (IntV i) = i"
  |  "convert_val_to_int _ = undefined"

(*
fun convert_val_to_int :: "(val list \<Rightarrow> val option) \<Rightarrow> int \<Rightarrow> int"
  where "convert_val_to_int f_isa i = Option.option.the (f_isa [IntV i])
*)

lemma prog_verifies: "method_verify ProgramM (''m'', [], [(''x'', TInt), (''y'', TInt)], G)"
proof (simp add: ProgramM_def; rule allI; rule impI; rule allI; rule impI; rule impI)
  fix \<gamma>_interp
  assume AInterp: "fun_interp_wf [(''f'', [TInt], TInt)] \<gamma>_interp"
  then obtain f_isa where A1:"\<gamma>_interp ''f'' = Some f_isa \<and> fun_interp_single_wf (''f'', [TInt], TInt) f_isa"
    using fun_interp_wf_def by (metis elem fst_conv)
  have "\<exists>f'. \<forall>i. f_isa [IntV i] = Some (IntV (f' i))" 
  proof (rule exI)
    let ?f = "\<lambda>i. convert_val_to_int (option.the (f_isa [IntV i]))"
    from A1 have "fun_interp_single_wf (''f'', [TInt], TInt) f_isa" by simp
    hence "(\<forall> vs. map type_of_val vs = [TInt] \<longleftrightarrow> (\<exists>v. f_isa vs = Some v))" by simp
    moreover have "\<forall> vs v. (f_isa vs = Some v) \<longrightarrow> type_of_val v = TInt" using A1 by simp
    ultimately show "\<forall>i. f_isa [IntV i] = Some (IntV (?f i))"
      by (metis (no_types, lifting) boogie_int_are_int convert_val_to_int.simps(1) list.simps(8) list.simps(9) option.sel type_of_val.simps(2)) 
  qed
  then obtain f' where "\<forall>i. f_isa [IntV i] = Some (IntV (f' i))" by (rule exE)
  fix ns :: nstate
  assume ADom: "dom ns = domain_wf [] [(''x'', TInt), (''y'', TInt)]"
  assume ATyp: "state_typ_wf ns [] [(''x'', TInt), (''y'', TInt)]"
  from ATyp have "Option.map_option type_of_val (ns(''x'')) = Some TInt"
    using state_typ_wf_def by simp
  then obtain ix where "ns(''x'') = Some (IntV ix)"
    using boogie_int_are_int by auto 
  from ATyp have "Option.map_option type_of_val (ns(''y'')) = Some TInt" 
      using state_typ_wf_def by simp
  then obtain iy where "ns(''y'') = Some (IntV iy)"
    using boogie_int_are_int by auto
  show "method_body_verifies [(''f'', [TInt], TInt)] \<gamma>_interp G ns"
    apply (simp add: method_body_verifies_def)
    apply (rule allI)+
    apply (rule impI)
    thm block0_verifies
    apply (rule block0_verifies[of _ _ _ _ _ _ _ f'])
         apply assumption
        apply (simp add: A1)
       apply (simp add: \<open>ns(''x'') = Some (IntV ix)\<close>)
      apply (simp add: \<open>ns(''y'') = Some (IntV iy)\<close>)
     apply (simp add: \<open>\<forall>i. f_isa [IntV i] = Some (IntV (f' i))\<close>)
    apply (simp add: vc.vc_correct)
    done
qed
    
end
