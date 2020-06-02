theory loop_demo
  imports Main
begin
(* 
\<forall>n_s.
  Invariant holds on entry and vc_while hold 
  \<langle>I, n_s\<rangle> \<Down> BoolV True \<and> vc_while \<longrightarrow>
  
    \<forall>vs \<in> mods(c). \<forall>s',a. 
       \<langle>b <<And>> I, n_s[mods(c) \<mapsto> vs]\<rangle> \<Down> BoolV True \<and> \<langle>c, Normal n_s[mods(c) \<mapsto> vs]\<rangle> \<rightarrow>* \<langle>a, s'\<rangle> \<longrightarrow> 
             s' \<noteq> Failure \<and> 
            (a = inr() \<Rightarrow> \<forall>n_s'. s' = Normal n_s' \<longrightarrow> \<langle>I, n_s'\<rangle> \<Down> BoolV True

  \<Longrightarrow>
  Goal:
   \<forall> s', a.
      \<langle>I, n_s\<rangle> \<Down> BoolV True \<and> vc_while \<longrightarrow>
        \<langle>while b {c}, Normal n_s\<rangle> \<rightarrow>* \<langle>a, s'\<rangle> \<longrightarrow> s' \<noteq> Failure  *)






(* Show via stronger property:
   \<forall> s', a, n_s*. 
      \<langle>I, n_s*\<rangle> \<Down> BoolV True \<and>
      \<langle>while b {c}, Normal n_s*\<rangle> \<rightarrow>* \<langle>a, s'\<rangle> \<longrightarrow>
          (\<forall>z \<notin> mods(c). n_s*(z) = n_s(z)) \<longrightarrow>
                                s' \<noteq> Failure  *)


           
end