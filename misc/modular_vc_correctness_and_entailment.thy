theory modular_vc_correctness_and_entailment
imports Semantics Util
begin
locale vc
begin

definition vc_anon3_Then
  where
    "vc_anon3_Then x_0 y = ((x_0 = (y + (1::int))) \<longrightarrow> (x_0 \<ge> (0::int)))"
definition vc_anon3_Else
  where
    "vc_anon3_Else x_1 y = ((x_1 = ((0::int) - y)) \<longrightarrow> (x_1 < (0::int)))"
definition vc_anon0
  where
    "vc_anon0 y x_0 x_1 = ((y > (0::int)) \<longrightarrow> ((vc_anon3_Then x_0 y) \<and> (vc_anon3_Else x_1 y)))"
definition vc_entry
  where
    "vc_entry y x_0 x_1 = (vc_anon0 y x_0 x_1)"
lemma vc_correct:

shows "(vc_entry y x_0 x_1)"
apply (simp only: vc_entry_def vc_anon0_def vc_anon3_Else_def vc_anon3_Then_def)
oops


end

locale vc_passive
begin

definition vc_anon3_Then
  where
    "vc_anon3_Then y = (\<forall> x_0. ((x_0 = (y + (1::int))) \<longrightarrow> (x_0 \<ge> (0::int))))"
definition vc_anon3_Else
  where
    "vc_anon3_Else y = (\<forall> x_1. ((x_1 = ((0::int) - y)) \<longrightarrow> (x_1 < (0::int))))"
definition vc_anon0
  where
    "vc_anon0  = (\<forall> y. ((y > (0::int)) \<longrightarrow> ((vc_anon3_Then y) \<and> (vc_anon3_Else y))))"
definition vc_entry
  where
    "vc_entry  = (vc_anon0 )"
lemma vc_correct:

shows "(vc_entry )"
apply (simp only: vc_entry_def vc_anon0_def vc_anon3_Else_def vc_anon3_Then_def)
oops


end

(* naive proof: unfold everything, then prove *)
lemma vc_entailment_naive_proof: "(\<forall> y x_0 x_1. vc.vc_entry y x_0 x_1) \<Longrightarrow> vc_passive.vc_entry"
apply (simp only: vc.vc_entry_def vc.vc_anon0_def vc.vc_anon3_Else_def vc.vc_anon3_Then_def)
apply (simp only: vc_passive.vc_entry_def vc_passive.vc_anon0_def vc_passive.vc_anon3_Else_def vc_passive.vc_anon3_Then_def)
  by simp

(* modular proof *)
lemma vc_entailment_anon3_Then: "(\<forall>x_0. vc.vc_anon3_Then x_0 y) \<Longrightarrow> vc_passive.vc_anon3_Then y"
  apply (simp only: vc.vc_anon3_Then_def vc_passive.vc_anon3_Then_def)
  done

lemma vc_entailment_anon3_Else: "(\<forall>x_1. vc.vc_anon3_Else x_1 y) \<Longrightarrow> vc_passive.vc_anon3_Else y"
  apply (simp only: vc.vc_anon3_Else_def vc_passive.vc_anon3_Else_def)
  done

lemma vc_entailment_anon0: "(\<forall> y x_0 x_1. vc.vc_anon0 y x_0 x_1) \<Longrightarrow> vc_passive.vc_anon0"
  apply (simp only: vc.vc_anon0_def vc_passive.vc_anon0_def)
  by (simp add: vc_entailment_anon3_Else vc_entailment_anon3_Then)

locale vc_modular
begin

definition vc_anon3_Then
  where
    "vc_anon3_Then x_0 y = ((x_0 = (y + (1::int))) \<longrightarrow> (x_0 \<ge> (0::int)))"
definition vc_anon3_Else
  where
    "vc_anon3_Else x_1 y = ((x_1 = ((0::int) - y)) \<longrightarrow> (x_1 < (0::int)))"
definition vc_anon0
  where
    "vc_anon0 y x_0 x_1 = ((y > (0::int)) \<longrightarrow> ((vc_anon3_Then x_0 y) \<and> (vc_anon3_Else x_1 y)))"
definition vc_entry
  where
    "vc_entry y x_0 x_1 = (vc_anon0 y x_0 x_1)"

(* naive proof: unfold everything and then prove \<rightarrow> can lead to exponential formulas *)
lemma vc_correct:
shows "(vc_entry y x_0 x_1)"
apply (simp only: vc_entry_def vc_anon0_def vc_anon3_Else_def vc_anon3_Then_def)
  oops

(* first prove a version that does not use definitions, but is still modular *)
lemma vc_modular: "
          \<lbrakk>
           B3 x_0 y \<longleftrightarrow> ((x_0 = (y + (1::int))) \<longrightarrow> (x_0 \<ge> (0::int)));
           B2 x_1 y \<longleftrightarrow> ((x_1 = ((0::int) - y)) \<longrightarrow> (x_1 < (0::int)));
           B1 y x_0 x_1 \<longleftrightarrow> ((y > (0::int)) \<longrightarrow> ((B3 x_0 y) \<and> (B2 x_1 y)));
           B0 y x_0 x_1 \<longleftrightarrow> (B1 y x_0 x_1)
          \<rbrakk> \<Longrightarrow> B0 y x_0 x_1"
  by auto

(* prove the version with definitions using the modular lemma *)
lemma vc_correct_modular: "vc_entry y x_0 x_1"
  apply (rule vc_modular[where ?B3.0=vc_anon3_Then and ?B2.0=vc_anon3_Else and ?B1.0=vc_anon0 and ?B0.0=vc_entry])
  apply (simp only: vc_anon3_Then_def)
    apply (simp only: vc_anon3_Else_def)
   apply (simp only: vc_anon0_def)
  apply (simp only: vc_entry_def)
  done
end

end
