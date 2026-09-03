Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Lra.
From mathcomp Require Import ssreflect ssrbool ssrnat seq ssralg ssrnum rat.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import DiscreteMC FrontierLiftEnum MeasureIterationEnum
  TwoLevelMeasure TwoLevelMeasureEnum.
From PTree.Eq Require Import PrimitiveStableHitting UnifiedFrontier
  OperationalProbabilisticPTS ProbabilisticEutt ProbabilisticTrace.
From PTree.Examples Require Import EnumMeasureRegression.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum GRing.Theory Num.Theory.
#[local] Open Scope ring_scope.

(** Pure silent divergence and a program which returns only on one side of
    a fair coin.  This is a program-level missing-mass regression for the
    canonical relation, rather than merely a statement about two measures. *)
CoFixpoint canonical_spin : ptree regE Enum bool := Tau canonical_spin.

Lemma observe_canonical_spin :
  observe canonical_spin = TauF canonical_spin.
Proof. reflexivity. Qed.

Definition half_return_half_diverge : ptree regE Enum bool :=
  Prob reg_fair (fun b => if b then Ret true else canonical_spin).

Definition half_return_heads : Enum (frontier_head regE Enum bool) :=
  [:: (reg_half, FHRet true)].

Lemma canonical_spin_target_approx_expect_zero fuel
    (P : frontier_head regE Enum bool -> bool) :
  enum_expect (fun x => if P x then 1 else 0)
    (@stable_target_approx Enum Enum_SemanticMeasure
      Enum_SemanticOmega _ _
      (@ptree_primitive_kernel regE Enum Enum
        Enum_SemanticMeasure Enum_MixedMeasure bool)
      fuel (SHInternal (observe canonical_spin))) = 0.
Proof.
  induction fuel as [|fuel IH].
  - reflexivity.
  - cbn [stable_target_approx].
    rewrite observe_canonical_spin.
    rewrite enum_expect_bind enum_expect_ret.
    exact IH.
Qed.

Lemma canonical_spin_hitting_approx_expect_zero fuel
    (P : frontier_head regE Enum bool -> bool) :
  enum_expect (fun x => if P x then 1 else 0)
    (@stable_hitting_approx Enum Enum_SemanticMeasure
      Enum_SemanticOmega _ _
      (@ptree_primitive_kernel regE Enum Enum
        Enum_SemanticMeasure Enum_MixedMeasure bool)
      fuel (observe canonical_spin)) = 0.
Proof.
  unfold stable_hitting_approx. rewrite observe_canonical_spin.
  rewrite enum_expect_bind enum_expect_ret.
  exact (canonical_spin_target_approx_expect_zero fuel P).
Qed.

Lemma canonical_spin_stable_hitting_zero :
  stable_hitting_weak
    (@ptree_primitive_kernel regE Enum Enum
      Enum_SemanticMeasure Enum_MixedMeasure bool)
    (observe canonical_spin) [::].
Proof.
  intros P eps Heps. exists 0%nat. intros n _.
  rewrite canonical_spin_hitting_approx_expect_zero.
  cbn [enum_expect]. rewrite subr0 normr0. exact Heps.
Qed.

(** A non-empty trace query on pure silent divergence has zero total mass.
    This is deliberately different from [sem_ret false]: divergence means
    that no next stable observation is reached, not that a visible event was
    observed and rejected. *)
Definition impossible_trace_step {X} (e : regE X) : option X :=
  match e with end.

Definition divergent_one_event_trace : @finite_event_trace regE :=
  cons (@impossible_trace_step) nil.

Definition divergent_trace_query : Enum bool := [::].

Lemma canonical_spin_nonempty_trace_query_zero :
  @finite_trace_query regE Enum Enum
    Enum_SemanticMeasure Enum_MixedMeasure
    Enum_SemanticOmega bool
    divergent_one_event_trace canonical_spin divergent_trace_query.
Proof.
  unfold divergent_one_event_trace, divergent_trace_query.
  exists ([::] : Enum (frontier_head regE Enum bool)),
    (fun _ : frontier_head regE Enum bool => [::]).
  repeat split.
  - exact canonical_spin_stable_hitting_zero.
  - cbn [TwoLevelMeasure.sem_ae Enum_SemanticMeasure
      FrontierLift.meas_ae Enum_MeasureInterface enum_ae].
    intros p x Hin Hnz. inversion Hin.
  - apply sem_eq_refl.
Qed.

Lemma divergent_trace_query_mass_zero :
  enum_expect (fun _ : bool => (1 : rat)) divergent_trace_query = 0.
Proof. reflexivity. Qed.

Lemma divergent_trace_query_not_rejection_mass :
  ~ @sem_same_mass Enum Enum_SemanticMeasure bool bool
      divergent_trace_query (sem_ret false).
Proof.
  intro Hmass.
  have Hweight := enum_sem_same_mass_expect_one Hmass.
  cbn [divergent_trace_query TwoLevelMeasure.sem_ret
    FrontierLift.meas_ret Enum_SemanticMeasure
    Enum_MeasureInterface ret_Enum enum_expect] in Hweight.
  discriminate Hweight.
Qed.

Lemma half_return_half_diverge_stable_hitting :
  stable_hitting_weak
    (@ptree_primitive_kernel regE Enum Enum
      Enum_SemanticMeasure Enum_MixedMeasure bool)
    (observe half_return_half_diverge) half_return_heads.
Proof.
  intros P eps Heps. exists 1%nat. intros [|fuel] Hfuel; first inversion Hfuel.
  unfold stable_hitting_approx.
  cbn [half_return_half_diverge ptree_primitive_kernel].
  rewrite !enum_expect_bind.
  cbn [reg_fair].
  cbn [TwoLevelMeasure.sem_ret FrontierLift.meas_ret
    Enum_SemanticMeasure Enum_MeasureInterface].
  cbn [ret_Enum enum_expect].
  ring_to_rat.
  rewrite !mul1r !addr0.
  cbn [reg_fair enum_expect].
  rewrite !enum_expect_app !enum_expect_scale /=.
  ring_to_rat.
  have Hspin := canonical_spin_target_approx_expect_zero fuel P.
  rewrite observe_canonical_spin in Hspin. rewrite Hspin.
  rewrite stable_target_stableE.
  cbn [TwoLevelMeasure.sem_ret FrontierLift.meas_ret
    Enum_SemanticMeasure Enum_MeasureInterface ret_Enum enum_expect].
  ring_to_rat.
  rewrite /half_return_heads /=.
  case HP: (P (FHRet true)); cbn; ring_to_rat; exact Heps.
Qed.

Lemma half_return_heads_not_same_mass_ret :
  ~ @sem_same_mass Enum Enum_SemanticMeasure
      (frontier_head regE Enum bool) (frontier_head regE Enum bool)
      half_return_heads (sem_ret (FHRet true)).
Proof.
  intro Hmass.
  have Hweight := enum_sem_same_mass_expect_one Hmass.
  cbn [half_return_heads TwoLevelMeasure.sem_ret FrontierLift.meas_ret
    Enum_SemanticMeasure Enum_MeasureInterface ret_Enum enum_expect]
    in Hweight.
  rewrite reg_half_val in Hweight.
  discriminate Hweight.
Qed.

Lemma enum_ret_true_stable_hitting :
  stable_hitting_weak
    (@ptree_primitive_kernel regE Enum Enum
      Enum_SemanticMeasure Enum_MixedMeasure bool)
    (observe (Ret true)) (sem_ret (FHRet true)).
Proof.
  intros P eps Heps. exists 0%nat. intros n _.
  unfold stable_hitting_approx. cbn [ptree_primitive_kernel].
  rewrite enum_expect_bind enum_expect_ret.
  rewrite stable_target_stableE enum_expect_ret subrr normr0.
  exact Heps.
Qed.

Theorem half_return_half_diverge_not_probabilistic_eutt_ret :
  ~ @probabilistic_eutt regE Enum Enum
      Enum_SemanticMeasure Enum_SemanticMeasureCoreLaws
      Enum_MixedMeasure Enum_SemanticOmega
      bool bool eq half_return_half_diverge (Ret true).
Proof.
  intro Hrel. apply probabilistic_eutt_unfold in Hrel.
  destruct Hrel as [Hforward _].
  destruct (Hforward half_return_heads
    half_return_half_diverge_stable_hitting) as [out [Hout Hlift]].
  have Hmass : sem_same_mass half_return_heads out.
  { eapply sem_lift_same_mass. exact Hlift. }
  have Hweight := enum_sem_same_mass_expect_one Hmass.
  unfold stable_hitting_weak in Hout.
  specialize (Hout (fun _ => true) (1 / 4 : rat)).
  have Hquarter : (0 : rat) < 1 / 4 by native_compute.
  destruct (Hout Hquarter) as [N HN].
  specialize (HN N (le_n N)).
  cbn [half_return_heads enum_expect] in Hweight.
  rewrite reg_half_val in Hweight.
  rewrite mulr1 addr0 in Hweight.
  unfold stable_hitting_approx in HN.
  cbn [ptree_primitive_kernel] in HN.
  rewrite enum_expect_bind enum_expect_ret stable_target_stableE
    enum_expect_ret in HN.
  cbn beta iota in HN. rewrite <- Hweight in HN.
  move: HN. native_compute. done.
Qed.
