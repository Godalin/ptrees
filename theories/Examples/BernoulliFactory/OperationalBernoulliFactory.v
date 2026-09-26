(** Case role: shared analysis.
    Proof mode: analysis-dominated.
    Reading entry: peutt_factory_vn_fair; peutt_factory_standard_direct.
    Scope: EnumQ / FreeOmega; genuine support/hitting/limit proofs, not presentation wrappers.
    See docs/CASE_STUDY_STANDARD.md and docs/CASE_STUDY_REFACTOR.md. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Unset Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Prob.Backend.Common Require Import FiniteRecordExtensionality FiniteEnum.

From Coq Require Import FunctionalExtensionality.
From Coq.Program Require Import Equality.

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssralg ssrnum order rat.

From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Bind.
Require Import PTree.Prob.Interface.Iteration.
Require Import PTree.Prob.Backend.EnumQ.Iteration.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.Support.
Require Import PTree.Prob.Backend.EnumQ.Support PTree.Prob.Backend.EnumQ.Map.
From PTree.Eq Require Import Shallow UnifiedFrontier PrimitiveStableHitting PTreeKernel ProbabilisticTrace.
From PTree.Eq.FreeOmega Require Import Base Hitting Relation Bind Algebra Iter.
From PTree.Interp.FreeOmega Require Import Base Guarded.
From PTree.Eq Require Import PEutt.
From PTree.Examples.BernoulliFactory Require Import VonNeumannUnbounded RationalBernoulli BernoulliFactory.

Set Implicit Arguments.
#[local] Existing Instance FreeOmegaSemanticMeasure.
#[local] Existing Instance FreeOmegaSemanticOmega.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ.
Import PTree.Prob.Backend.EnumQ.Map.
Import GRing.Theory.
Local Open Scope ring_scope.

Local Notation MF := (FreeOmega EnumQ).

Definition factoryE_no_event : forall X, factoryE X -> False :=
  fun X e => match e with end.

Section FactoryOperationalNormalization.
Variables pfalse ptrue : rat.
Hypotheses (pfalse0 : 0 <= pfalse) (ptrue0 : 0 <= ptrue).

Local Notation factory_head A := (stable_head factoryE EnumQ A).

Polymorphic Definition ptree_factory_head_value {X}
    (h : factory_head X) : X :=
  match h with
  | FHRet x => x
  | @FHVis _ _ _ Y e _ => False_rect X (factoryE_no_event e)
  end.

Fixpoint ptree_factory_fair_measure_row (outer : nat) : EnumQ bool :=
  match outer with
  | O => enumQ_zero
  | S outer' =>
      bind_EnumQ (factory_biased_coin pfalse0 ptrue0) (fun b1 =>
        bind_EnumQ (factory_biased_coin pfalse0 ptrue0) (fun b2 =>
          match vn_round_result b1 b2 with
          | inl _ => ptree_factory_fair_measure_row outer'
          | inr b => ret_EnumQ b
          end))
  end.

Lemma ptree_factory_fair_measure_row_eq outer :
  ptree_factory_fair_measure_row outer =
    meas_iter_approx outer
      (fun _ : unit => factory_round_measure pfalse0 ptrue0) tt.
Proof.
  induction outer as [|outer IH]; first reflexivity.
  cbn [ptree_factory_fair_measure_row meas_iter_approx].
  unfold factory_round_measure.
  cbn [FrontierLift.meas_bind FrontierLift.meas_ret
    PTree.Prob.Backend.EnumQ.FrontierLift.EnumQ_MeasureInterface].
  unfold bind_EnumQ, ret_EnumQ.
  rewrite finite_enum_bind_assoc_eq. apply finite_enum_bind_ext_eq=> b1.
  rewrite finite_enum_bind_assoc_eq. apply finite_enum_bind_ext_eq=> b2.
  rewrite finite_enum_bind_ret_eq.
  destruct (vn_round_result b1 b2) as [[]|b]; [exact IH|reflexivity].
Qed.

Definition ptree_factory_raw_after (next : unit + bool) :
    ptree factoryE EnumQ bool :=
  match next with
  | inl u => Tau (PTree.iter (factory_vn_step pfalse0 ptrue0) u)
  | inr b => Ret b
  end.

Definition ptree_factory_raw_second (b1 : bool) :
    ptree factoryE EnumQ bool :=
  PTree.bind
    (Prob (factory_biased_coin pfalse0 ptrue0) (fun b2 =>
      Ret (vn_round_result b1 b2)))
    ptree_factory_raw_after.

Lemma ptree_factory_raw_observe :
  observe (factory_fair_coin pfalse0 ptrue0) =
  ProbF (factory_biased_coin pfalse0 ptrue0)
    ptree_factory_raw_second.
Proof.
  unfold factory_fair_coin.
  pose proof (unfold_aloop_ (factory_vn_step pfalse0 ptrue0) tt) as Hunfold.
  rewrite (observing_observe Hunfold). rewrite observe_bind.
  assert (Hstep : observe (factory_vn_step pfalse0 ptrue0 tt) =
    ProbF (factory_biased_coin pfalse0 ptrue0) (fun b1 =>
      Prob (factory_biased_coin pfalse0 ptrue0) (fun b2 =>
        Ret (vn_round_result b1 b2)))) by reflexivity.
  rewrite Hstep. reflexivity.
Qed.

Lemma ptree_factory_raw_second_observe b1 :
  observe (ptree_factory_raw_second b1) =
  ProbF (factory_biased_coin pfalse0 ptrue0) (fun b2 =>
    PTree.bind (Ret (vn_round_result b1 b2))
      ptree_factory_raw_after).
Proof.
  unfold ptree_factory_raw_second. rewrite observe_bind. reflexivity.
Qed.

Definition ptree_factory_raw_hitting (fuel : nat) : MF (factory_head bool) :=
  ptree_hitting_approx (MF := MF) fuel
    (observe (factory_fair_coin pfalse0 ptrue0)).

Lemma ptree_factory_raw_hitting_three fuel :
  ptree_factory_raw_hitting
    (Datatypes.S (Datatypes.S (Datatypes.S fuel))) =
  FOSample (factory_biased_coin pfalse0 ptrue0) (fun b1 =>
    FOSample (factory_biased_coin pfalse0 ptrue0) (fun b2 =>
      match vn_round_result b1 b2 with
      | inl _ => ptree_factory_raw_hitting fuel
      | inr b => FORet (FHRet b)
      end)).
Proof.
  unfold ptree_factory_raw_hitting.
  rewrite ptree_factory_raw_observe.
  cbn [ptree_hitting_approx ptree_primitive_kernel ptree_stable_target_approx
    stable_hitting_approx stable_target_approx ptree_primitive_kernel
    sem_bind sem_ret mixed_bind free_omega_bind FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticMeasure
    FreeOmegaSemanticMeasure].
  f_equal. apply functional_extensionality=> b1.
  rewrite ptree_factory_raw_second_observe.
  cbn [ptree_primitive_kernel ptree_stable_target_approx stable_target_approx
    ptree_primitive_kernel sem_bind sem_ret
    mixed_bind free_omega_bind FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticMeasure FreeOmegaSemanticMeasure].
  f_equal. apply functional_extensionality=> b2. rewrite observe_bind.
  destruct (vn_round_result b1 b2) as [[]|b]; reflexivity.
Qed.

Fixpoint ptree_factory_raw_schedule (rounds : nat) : nat :=
  match rounds with
  | O => O
  | S rounds' => S (S (S (ptree_factory_raw_schedule rounds')))
  end.

Lemma ptree_factory_raw_hitting_zero_observes :
  free_omega_observes ptree_factory_head_value
    (ptree_factory_raw_hitting 0) (enumQ_zero : EnumQ bool).
Proof.
  unfold ptree_factory_raw_hitting.
  rewrite ptree_factory_raw_observe.
  change (free_omega_observes ptree_factory_head_value
    (FOSample (factory_biased_coin pfalse0 ptrue0) (fun _ => FOZero))
    (enumQ_zero : EnumQ bool)).
  replace (@enumQ_zero bool) with
    (bind_EnumQ (factory_biased_coin pfalse0 ptrue0) (fun _ => @enumQ_zero bool))
    by apply finite_enum_bind_zero_eq.
  constructor. intro b. constructor.
Qed.

Lemma ptree_factory_raw_hitting_rounds_observes rounds :
  free_omega_observes ptree_factory_head_value
    (ptree_factory_raw_hitting
      (ptree_factory_raw_schedule rounds))
    (ptree_factory_fair_measure_row rounds).
Proof.
  induction rounds as [|rounds IH].
  - exact ptree_factory_raw_hitting_zero_observes.
  - cbn [ptree_factory_raw_schedule
      ptree_factory_fair_measure_row].
    rewrite ptree_factory_raw_hitting_three.
    change (free_omega_observes ptree_factory_head_value
      (FOSample (factory_biased_coin pfalse0 ptrue0) (fun b1 =>
        FOSample (factory_biased_coin pfalse0 ptrue0) (fun b2 =>
          match vn_round_result b1 b2 with
          | inl _ => ptree_factory_raw_hitting
              (ptree_factory_raw_schedule rounds)
          | inr b => FORet (FHRet b)
          end)))
      (@sem_bind EnumQ EnumQ_SemanticMeasure _ _
        (factory_biased_coin pfalse0 ptrue0) (fun b1 =>
          @sem_bind EnumQ EnumQ_SemanticMeasure _ _
            (factory_biased_coin pfalse0 ptrue0) (fun b2 =>
              match vn_round_result b1 b2 with
              | inl _ => ptree_factory_fair_measure_row rounds
              | inr b => @sem_ret EnumQ EnumQ_SemanticMeasure _ b
              end)))).
    constructor=> b1. constructor=> b2.
    destruct (vn_round_result b1 b2) as [[]|b]; [exact IH|constructor].
Qed.

Lemma ptree_factory_raw_schedule_ge rounds :
  Peano.le rounds (ptree_factory_raw_schedule rounds).
Proof.
  induction rounds as [|rounds IH]; [apply le_n|].
  cbn. apply le_n_S. apply le_S, le_S. exact IH.
Qed.

Lemma ptree_factory_raw_chains_cofinal :
  free_omega_chains_cofinal eq ptree_factory_raw_hitting
    (fun rounds => ptree_factory_raw_hitting
      (ptree_factory_raw_schedule rounds)).
Proof.
  split.
  - intro fuel. exists fuel. apply ptree_hitting_mono.
    exact (ptree_factory_raw_schedule_ge fuel).
  - intro rounds. exists (ptree_factory_raw_schedule rounds).
    apply free_omega_approx_refl. intro h. reflexivity.
Qed.

Definition ptree_factory_raw_heads : MF (factory_head bool) :=
  FOLub (fun rounds => ptree_factory_raw_hitting
    (ptree_factory_raw_schedule rounds)).

Theorem ptree_factory_fair_coin_weak :
  @ptree_stable_hitting factoryE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (observe (factory_fair_coin pfalse0 ptrue0))
    ptree_factory_raw_heads.
Proof.
  change (free_omega_qlift eq
    (FOLub (fun n => ptree_factory_raw_hitting (ptree_factory_raw_schedule n)))
    (FOLub ptree_factory_raw_hitting)).
  apply FOQLSym. eapply FOQLMono.
  - apply FOQLCofinal.
    + intro n. apply ptree_hitting_mono. apply le_S, le_n.
    + intro n. apply ptree_hitting_mono.
      cbn [ptree_factory_raw_schedule]. repeat apply le_S. apply le_n.
    + exact ptree_factory_raw_chains_cofinal.
  - intros x y ->. reflexivity.
Qed.

Lemma ptree_factory_fair_heads_observes
    (pnormalized : pfalse + ptrue = 1)
    (pnontrivial : (0 < pfalse * ptrue)%Q) :
  free_omega_observes ptree_factory_head_value
    ptree_factory_raw_heads vn_fair.
Proof.
  unfold ptree_factory_raw_heads. eapply FOOObserveLub.
  - exact ptree_factory_raw_hitting_rounds_observes.
  - assert (Hrows : ptree_factory_fair_measure_row =
      fun outer => meas_iter_approx outer
        (fun _ : unit => param_round_measure pfalse0 ptrue0) tt).
    { apply functional_extensionality=> outer.
      rewrite ptree_factory_fair_measure_row_eq.
      rewrite (factory_round_is_param_round pfalse0 ptrue0). reflexivity. }
    rewrite Hrows.
    exact (param_iteration_converges_of_normalized_bias
      pfalse0 ptrue0 pnormalized pnontrivial).
  - intro n. apply ptree_hitting_mono.
    cbn [ptree_factory_raw_schedule]. repeat apply le_S. apply le_n.
Qed.

Lemma ptree_factory_fair_heads_total
    (pnormalized : pfalse + ptrue = 1)
    (pnontrivial : (0 < pfalse * ptrue)%Q) :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticOmega _
    ptree_factory_raw_heads.
Proof.
  apply free_omega_observable_total_intro.
  exists bool, ptree_factory_head_value, vn_fair.
  split.
  - exact (ptree_factory_fair_heads_observes
      pnormalized pnontrivial).
  - exact vn_fair_total.
Qed.

Theorem ptree_factory_fair_coin_ast
    (pnormalized : pfalse + ptrue = 1)
    (pnontrivial : (0 < pfalse * ptrue)%Q) :
  @ptree_stable_hitting_ast factoryE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (observe (factory_fair_coin pfalse0 ptrue0))
    ptree_factory_raw_heads.
Proof.
  split.
  - exact ptree_factory_fair_coin_weak.
  - exact (ptree_factory_fair_heads_total
      pnormalized pnontrivial).
Qed.

Section RationalTarget.
Variable q : rat.

Fixpoint ptree_factory_binary_measure_row
    (rounds : nat) (x : rat) : EnumQ (rat + bool) :=
  match rounds with
  | O => enumQ_zero
  | S rounds' =>
      bind_EnumQ (factory_biased_coin pfalse0 ptrue0) (fun b1 =>
        bind_EnumQ (factory_biased_coin pfalse0 ptrue0) (fun b2 =>
          match vn_round_result b1 b2 with
          | inl _ => ptree_factory_binary_measure_row rounds' x
          | inr b => ret_EnumQ (binary_round_result x b)
          end))
  end.

Lemma ptree_factory_binary_measure_row_eq rounds x :
  ptree_factory_binary_measure_row rounds x =
  bind_EnumQ (ptree_factory_fair_measure_row rounds)
    (fun b => ret_EnumQ (binary_round_result x b)).
Proof.
  induction rounds as [|rounds IH].
  - apply finite_enum_raw_eq; reflexivity.
  - cbn [ptree_factory_binary_measure_row ptree_factory_fair_measure_row].
  unfold bind_EnumQ, ret_EnumQ.
  rewrite finite_enum_bind_assoc_eq. apply finite_enum_bind_ext_eq=> b1.
  rewrite finite_enum_bind_assoc_eq. apply finite_enum_bind_ext_eq=> b2.
  destruct (vn_round_result b1 b2) as [[]|b]; first exact IH.
  rewrite finite_enum_bind_ret_eq; reflexivity.
Qed.

Lemma enumQ_converges_bind_ret_map {A B}
    (chain : nat -> EnumQ A) out (f : A -> B) :
  enumQ_converges chain out ->
  enumQ_converges
    (fun n => bind_EnumQ (chain n) (fun a => ret_EnumQ (f a)))
    (bind_EnumQ out (fun a => ret_EnumQ (f a))).
Proof.
  intros H P eps Heps.
  destruct (H (fun a => P (f a)) eps Heps) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn).
  rewrite !enumQ_expect_bind.
  assert (Hret :
    (fun a : A => enumQ_expect (fun b : B =>
      if P b then (1 : rat) else 0) (ret_EnumQ (f a))) =
    (fun a : A => if P (f a) then (1 : rat) else 0)).
  { apply functional_extensionality=> a. apply enumQ_expect_ret. }
  rewrite Hret. exact HN.
Qed.

Lemma ptree_factory_raw_hitting_rounds_observes_binary rounds x :
  free_omega_observes
    (fun h => binary_round_result x (ptree_factory_head_value h))
    (ptree_factory_raw_hitting
      (ptree_factory_raw_schedule rounds))
    (ptree_factory_binary_measure_row rounds x).
Proof.
  induction rounds as [|rounds IH].
  - unfold ptree_factory_raw_hitting.
    rewrite ptree_factory_raw_observe.
    change (free_omega_observes
      (fun h => binary_round_result x (ptree_factory_head_value h))
      (FOSample (factory_biased_coin pfalse0 ptrue0) (fun _ => FOZero))
      (enumQ_zero : EnumQ (rat + bool))).
    replace (@enumQ_zero (rat + bool)) with
      (bind_EnumQ (factory_biased_coin pfalse0 ptrue0) (fun _ => @enumQ_zero (rat + bool)))
      by apply finite_enum_bind_zero_eq.
    constructor=> b. constructor.
  - cbn [ptree_factory_raw_schedule
      ptree_factory_binary_measure_row].
    rewrite ptree_factory_raw_hitting_three.
    change (free_omega_observes
      (fun h => binary_round_result x (ptree_factory_head_value h))
      (FOSample (factory_biased_coin pfalse0 ptrue0) (fun b1 =>
        FOSample (factory_biased_coin pfalse0 ptrue0) (fun b2 =>
          match vn_round_result b1 b2 with
          | inl _ => ptree_factory_raw_hitting
              (ptree_factory_raw_schedule rounds)
          | inr b => FORet (FHRet b)
          end)))
      (@sem_bind EnumQ EnumQ_SemanticMeasure _ _
        (factory_biased_coin pfalse0 ptrue0) (fun b1 =>
          @sem_bind EnumQ EnumQ_SemanticMeasure _ _
            (factory_biased_coin pfalse0 ptrue0) (fun b2 =>
              match vn_round_result b1 b2 with
              | inl _ => ptree_factory_binary_measure_row rounds x
              | inr b => @sem_ret EnumQ EnumQ_SemanticMeasure _
                  (binary_round_result x b)
              end)))).
    constructor=> b1. constructor=> b2.
    destruct (vn_round_result b1 b2) as [[]|b]; [exact IH|constructor].
Qed.

Lemma ptree_factory_raw_heads_observes_binary
    (pnormalized : pfalse + ptrue = 1)
    (pnontrivial : (0 < pfalse * ptrue)%Q) x :
  free_omega_observes
    (fun h => binary_round_result x (ptree_factory_head_value h))
    ptree_factory_raw_heads (binary_coin_transition x).
Proof.
  unfold ptree_factory_raw_heads. eapply FOOObserveLub.
  - intro rounds.
    exact (ptree_factory_raw_hitting_rounds_observes_binary rounds x).
  - assert (Hfair : enumQ_converges ptree_factory_fair_measure_row
        vn_fair).
    { assert (Hrows : ptree_factory_fair_measure_row =
        fun rounds => meas_iter_approx rounds
          (fun _ : unit => param_round_measure pfalse0 ptrue0) tt).
      { apply functional_extensionality=> rounds.
        rewrite ptree_factory_fair_measure_row_eq.
        rewrite (factory_round_is_param_round pfalse0 ptrue0). reflexivity. }
      rewrite Hrows. exact (param_iteration_converges_of_normalized_bias
        pfalse0 ptrue0 pnormalized pnontrivial). }
    pose proof (@enumQ_converges_bind_ret_map bool (rat + bool)
      ptree_factory_fair_measure_row vn_fair
      (fun b => binary_round_result x b) Hfair)
      as Hmap.
    assert (Hchain : (fun rounds =>
        ptree_factory_binary_measure_row rounds x) =
      fun rounds => bind_EnumQ (ptree_factory_fair_measure_row rounds)
        (fun b => ret_EnumQ (binary_round_result x b))).
    { apply functional_extensionality=> rounds.
      apply ptree_factory_binary_measure_row_eq. }
    rewrite Hchain. rewrite <- fair_binary_round_measure. exact Hmap.
  - intro n. apply ptree_hitting_mono.
    cbn [ptree_factory_raw_schedule]. repeat apply le_S. apply le_n.
Qed.

Definition ptree_factory_binary_step_heads (x : rat) :
    MF (factory_head (rat + bool)) :=
  @sem_bind MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega)) _ _
    ptree_factory_raw_heads
    (stable_head_bind_front
      (fun b => Ret (binary_round_result x b) : ptree factoryE EnumQ _)
      (fun b => FORet (FHRet (binary_round_result x b)))).

Lemma ptree_factory_binary_ret_weak (next : rat + bool) :
  @ptree_stable_hitting factoryE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega (rat + bool)
    (observe (Ret next)) (FORet (FHRet next)).
Proof.
  assert (Hobserve : observe
    (Ret next : ptree factoryE EnumQ (rat + bool)) = RetF next)
    by reflexivity.
  rewrite Hobserve. apply (ptree_stable_hitting_ret
    (FI := FreeOmegaObservableSemanticMeasure)
    (FO := FreeOmegaObservableSemanticOmega)
    (MX := FreeOmegaMixedMeasure) (E := factoryE)).
Qed.

Lemma ptree_factory_binary_step_weak x :
  @ptree_stable_hitting factoryE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega (rat + bool)
    (observe (factory_binary_step pfalse0 ptrue0 x))
    (ptree_factory_binary_step_heads x).
Proof.
  unfold factory_binary_step, ptree_factory_binary_step_heads.
  eapply (ptree_stable_hitting_bind
    (FI := FreeOmegaObservableSemanticMeasure)
    (FO := FreeOmegaObservableSemanticOmega)
    (MX := FreeOmegaMixedMeasure)).
  - apply ptree_bind_cofinal_no_event. exact factoryE_no_event.
  - exact ptree_factory_fair_coin_weak.
  - intro b. apply ptree_factory_binary_ret_weak.
Qed.

Lemma ptree_factory_binary_step_heads_observes
    (pnormalized : pfalse + ptrue = 1)
    (pnontrivial : (0 < pfalse * ptrue)%Q) x :
  free_omega_observes
    (iter_head_next factoryE_no_event)
    (ptree_factory_binary_step_heads x)
    (binary_coin_transition x).
Proof.
  unfold ptree_factory_binary_step_heads.
  assert (Hfront :
    stable_head_bind_front
      (fun b => Ret (binary_round_result x b) : ptree factoryE EnumQ _)
      (fun b => FORet (FHRet (binary_round_result x b))) =
    (fun h => FORet (FHRet (binary_round_result x
      (ptree_factory_head_value h))))).
  { apply functional_extensionality=> h.
    destruct h as [b|X e k]; [reflexivity|destruct e]. }
  rewrite Hfront.
  eapply free_omega_observes_bind_ret
    with (obsA := fun h => binary_round_result x
      (ptree_factory_head_value h)).
  - exact (ptree_factory_raw_heads_observes_binary
      pnormalized pnontrivial x).
  - intro h. destruct h as [b|X e k]; [reflexivity|destruct e].
Qed.

(** The target of the implementation proof is the standard one-step
    distribution, embedded once into the free omega completion.  This is
    deliberately independent of the implementation's unbounded raw-coin
    schedule. *)
Definition ptree_factory_standard_step_heads (x : rat) :
    MF (factory_head (rat + bool)) :=
  FOSample (binary_coin_transition x) (fun next => FORet (FHRet next)).

Lemma ptree_factory_standard_step_heads_observes x :
  free_omega_observes
    (iter_head_next factoryE_no_event)
    (ptree_factory_standard_step_heads x)
    (@sem_bind EnumQ EnumQ_SemanticMeasure _ _
      (binary_coin_transition x) (fun next =>
        @sem_ret EnumQ EnumQ_SemanticMeasure _ next)).
Proof.
  unfold ptree_factory_standard_step_heads.
  eapply FOOObserveSample with
    (front := fun next : rat + bool =>
      @sem_ret EnumQ EnumQ_SemanticMeasure _ next).
  intro next. constructor.
Qed.

Class OperationalFactoryStepSupportLaws := {
  ptree_factory_binary_step_support : forall
      (pnormalized : pfalse + ptrue = 1)
      (pnontrivial : (0 < pfalse * ptrue)%Q) x,
    free_omega_support_lift eq
      (ptree_factory_binary_step_heads x)
      (ptree_factory_standard_step_heads x)
}.

Context `{FactoryStepSupport : OperationalFactoryStepSupportLaws}.

Lemma ptree_factory_binary_step_heads_lift
    (pnormalized : pfalse + ptrue = 1)
    (pnontrivial : (0 < pfalse * ptrue)%Q) x :
  free_omega_qlift eq
    (ptree_factory_binary_step_heads x)
    (ptree_factory_standard_step_heads x).
Proof.
  eapply FOQLObserve with
    (obsA := iter_head_next factoryE_no_event)
    (obsB := iter_head_next factoryE_no_event)
    (outA := binary_coin_transition x)
    (outB := @sem_bind EnumQ EnumQ_SemanticMeasure _ _
      (binary_coin_transition x) (fun next =>
        @sem_ret EnumQ EnumQ_SemanticMeasure _ next)) (S := eq).
  - exact (ptree_factory_binary_step_heads_observes
      pnormalized pnontrivial x).
  - exact (ptree_factory_standard_step_heads_observes x).
  - cbn [sem_bind sem_ret EnumQ_SemanticMeasure
      FrontierLift.meas_bind FrontierLift.meas_ret
      PTree.Prob.Backend.EnumQ.FrontierLift.EnumQ_MeasureInterface].
    rewrite /bind_EnumQ /ret_EnumQ finite_enum_bind_right_unit_eq.
    apply sem_lift_refl. intros next. reflexivity.
  - intros h1 h2 Hnext.
    destruct h1 as [next1|X e1 k1];
      destruct h2 as [next2|Y e2 k2];
      try destruct e1; try destruct e2.
    cbn in Hnext. subst next2. reflexivity.
  - exact (ptree_factory_binary_step_support
      pnormalized pnontrivial x).
Qed.

Fixpoint ptree_factory_standard_q_row
    (outer : nat) (x : rat) : MF (factory_head bool) :=
  match outer with
  | O => FOZero
  | S outer' =>
      free_omega_bind (ptree_factory_standard_step_heads x) (fun h =>
        match iter_head_next factoryE_no_event h with
        | inl x' => ptree_factory_standard_q_row outer' x'
        | inr b => FORet (FHRet b)
        end)
  end.

Definition ptree_factory_standard_q_heads : MF (factory_head bool) :=
  FOLub (fun outer => ptree_factory_standard_q_row outer q).

Lemma ptree_factory_q_row_lift
    (pnormalized : pfalse + ptrue = 1)
    (pnontrivial : (0 < pfalse * ptrue)%Q) :
  forall outer x,
    free_omega_qlift eq
      (iter_complete_rows factoryE_no_event
        ptree_factory_binary_step_heads outer x)
      (ptree_factory_standard_q_row outer x).
Proof.
  induction outer as [|outer IH]; intro x.
  - apply free_omega_qlift_refl. intros h. reflexivity.
  - cbn [iter_complete_rows ptree_factory_standard_q_row].
    eapply FOQLBind with (T := eq).
    + exact (ptree_factory_binary_step_heads_lift
        pnormalized pnontrivial x).
    + intros h1 h2 ->. destruct (iter_head_next factoryE_no_event h2)
        as [x'|b].
      * apply IH.
      * apply free_omega_qlift_refl. intros h. reflexivity.
Qed.

Definition ptree_factory_q_row (outer : nat) :
    MF (factory_head bool) :=
  iter_complete_rows factoryE_no_event
    ptree_factory_binary_step_heads outer q.

Definition ptree_factory_q_heads : MF (factory_head bool) :=
  FOLub ptree_factory_q_row.

Lemma ptree_factory_q_heads_lift_standard
    (pnormalized : pfalse + ptrue = 1)
    (pnontrivial : (0 < pfalse * ptrue)%Q) :
  free_omega_qlift eq ptree_factory_q_heads
    ptree_factory_standard_q_heads.
Proof.
  unfold ptree_factory_q_heads, ptree_factory_q_row,
    ptree_factory_standard_q_heads.
  apply FOQLLub. intro outer.
  exact (ptree_factory_q_row_lift pnormalized pnontrivial outer q).
Qed.

Lemma ptree_factory_standard_q_row_observes : forall outer x,
  free_omega_observes ptree_factory_head_value
    (ptree_factory_standard_q_row outer x)
    (meas_iter_approx outer binary_coin_transition x).
Proof.
  induction outer as [|outer IH]; intro x.
  - constructor.
  - cbn [ptree_factory_standard_q_row meas_iter_approx
      ptree_factory_standard_step_heads free_omega_bind].
    change (free_omega_observes ptree_factory_head_value
      (FOSample (binary_coin_transition x) (fun next : rat + bool =>
        match next with
        | inl x' => ptree_factory_standard_q_row outer x'
        | inr b => FORet (FHRet b)
        end))
      (@sem_bind EnumQ EnumQ_SemanticMeasure _ _
        (binary_coin_transition x) (fun next : rat + bool =>
          match next with
          | inl x' => meas_iter_approx outer binary_coin_transition x'
          | inr b => @sem_ret EnumQ EnumQ_SemanticMeasure _ b
          end))).
    eapply FOOObserveSample with (front := fun next : rat + bool =>
      match next with
      | inl x' => meas_iter_approx outer binary_coin_transition x'
      | inr b => ret_EnumQ b
      end).
    intros [x'|b].
    + apply IH.
    + constructor.
Qed.

Lemma ptree_factory_standard_q_heads_observes
    (q0 : 0 <= q) (q1 : q <= 1) :
  free_omega_observes ptree_factory_head_value
    ptree_factory_standard_q_heads
    (rational_bernoulli_measure q0 q1).
Proof.
  unfold ptree_factory_standard_q_heads.
  eapply FOOObserveLub.
  - intro outer. apply ptree_factory_standard_q_row_observes.
  - exact (rational_binary_iteration_converges q0 q1).
  - generalize q. intro x. intro n. revert x.
    induction n as [|n IH]; intro x; cbn [ptree_factory_standard_q_row].
    + apply FOApproxZero.
    + eapply free_omega_approx_bind with (R := eq).
      * apply free_omega_approx_refl. intro h. reflexivity.
      * intros h h' ->. destruct (iter_head_next factoryE_no_event h') as [next|b].
        -- apply IH.
        -- apply FOApproxRet. reflexivity.
Qed.

Lemma ptree_factory_standard_q_heads_total
    (q0 : 0 <= q) (q1 : q <= 1) :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticOmega _
    ptree_factory_standard_q_heads.
Proof.
  apply free_omega_observable_total_intro.
  exists bool, ptree_factory_head_value,
    (rational_bernoulli_measure q0 q1).
  split.
  - exact (ptree_factory_standard_q_heads_observes q0 q1).
  - exact (rational_bernoulli_total q0 q1).
Qed.

Theorem ptree_biased_to_rational_coin_weak :
  @ptree_stable_hitting factoryE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (observe (biased_to_rational_coin pfalse0 ptrue0 q))
    ptree_factory_q_heads.
Proof.
  unfold biased_to_rational_coin.
  eapply ptree_stable_hitting_iter_of_unbounded_steps
    with (step_out := ptree_factory_binary_step_heads).
  - exact ptree_factory_binary_step_weak.
  - unfold ptree_factory_q_heads, ptree_factory_q_row.
    apply free_omega_qlift_refl. intros h. reflexivity.
Qed.

Theorem ptree_biased_to_rational_coin_weak_standard
    (pnormalized : pfalse + ptrue = 1)
    (pnontrivial : (0 < pfalse * ptrue)%Q) :
  @ptree_stable_hitting factoryE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (observe (biased_to_rational_coin pfalse0 ptrue0 q))
    ptree_factory_standard_q_heads.
Proof.
  pose proof ptree_biased_to_rational_coin_weak as Hweak.
  unfold ptree_stable_hitting in Hweak |- *.
  eapply sem_eq_trans.
  - apply sem_eq_sym.
    exact (ptree_factory_q_heads_lift_standard
      pnormalized pnontrivial).
  - exact Hweak.
Qed.

Theorem ptree_biased_to_rational_coin_ast
    (pnormalized : pfalse + ptrue = 1)
    (pnontrivial : (0 < pfalse * ptrue)%Q)
    (q0 : 0 <= q) (q1 : q <= 1) :
  @ptree_stable_hitting_ast factoryE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (observe (biased_to_rational_coin pfalse0 ptrue0 q))
    ptree_factory_standard_q_heads.
Proof.
  split.
  - exact (ptree_biased_to_rational_coin_weak_standard
      pnormalized pnontrivial).
  - exact (ptree_factory_standard_q_heads_total q0 q1).
Qed.

Corollary ptree_biased_to_rational_coin_primitive_ast
    (pnormalized : pfalse + ptrue = 1)
    (pnontrivial : (0 < pfalse * ptrue)%Q)
    (q0 : 0 <= q) (q1 : q <= 1) :
  @stable_hitting_ast MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticOmega
    (ptree' factoryE EnumQ bool) (factory_head bool)
    (@ptree_primitive_kernel factoryE EnumQ MF
      (FreeOmegaObservableSemanticMeasure
        (NI := EnumQ_SemanticMeasure)
        (NO := EnumQ_SemanticOmega))
      FreeOmegaMixedMeasure bool)
    (observe (biased_to_rational_coin pfalse0 ptrue0 q))
    ptree_factory_standard_q_heads.
Proof.
  apply (proj2 (ptree_primitive_ast_adequate
    (observe (biased_to_rational_coin pfalse0 ptrue0 q))
    ptree_factory_standard_q_heads)).
  exact (ptree_biased_to_rational_coin_ast
    pnormalized pnontrivial q0 q1).
Qed.

Definition ptree_factory_direct_q_heads
    (q0 : 0 <= q) (q1 : q <= 1) : MF (factory_head bool) :=
  @mixed_bind EnumQ MF FreeOmegaMixedMeasure bool _
    (rational_bernoulli_measure q0 q1)
    (fun b => FORet (FHRet b)).

Definition ptree_factory_direct_q_observation
    (q0 : 0 <= q) (q1 : q <= 1) : EnumQ bool :=
  @sem_bind EnumQ EnumQ_SemanticMeasure _ _
    (rational_bernoulli_measure q0 q1) (fun b =>
      @sem_ret EnumQ EnumQ_SemanticMeasure _ b).

Lemma ptree_factory_direct_q_heads_observes
    (q0 : 0 <= q) (q1 : q <= 1) :
  free_omega_observes ptree_factory_head_value
    (ptree_factory_direct_q_heads q0 q1)
    (ptree_factory_direct_q_observation q0 q1).
Proof.
  unfold ptree_factory_direct_q_heads,
    ptree_factory_direct_q_observation.
  eapply FOOObserveSample with (front := fun b : bool => ret_EnumQ b).
  intro b. constructor.
Qed.

Lemma ptree_factory_direct_q_observation_eq
    (q0 : 0 <= q) (q1 : q <= 1) :
  ptree_factory_direct_q_observation q0 q1 =
    rational_bernoulli_measure q0 q1.
Proof.
  unfold ptree_factory_direct_q_observation.
  cbn [sem_bind sem_ret EnumQ_SemanticMeasure
    FrontierLift.meas_bind FrontierLift.meas_ret
    PTree.Prob.Backend.EnumQ.FrontierLift.EnumQ_MeasureInterface].
  apply finite_enum_bind_right_unit_eq.
Qed.

Lemma ptree_factory_direct_q_heads_total
    (q0 : 0 <= q) (q1 : q <= 1) :
  @sem_total MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticOmega _
    (ptree_factory_direct_q_heads q0 q1).
Proof.
  apply free_omega_observable_total_intro.
  exists bool, ptree_factory_head_value,
    (ptree_factory_direct_q_observation q0 q1).
  split; [apply ptree_factory_direct_q_heads_observes|].
  rewrite ptree_factory_direct_q_observation_eq.
  exact (rational_bernoulli_total q0 q1).
Qed.

Theorem ptree_factory_direct_q_ast
    (q0 : 0 <= q) (q1 : q <= 1) :
  @ptree_stable_hitting_ast factoryE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (observe (factory_direct_q q0 q1))
    (ptree_factory_direct_q_heads q0 q1).
Proof.
  assert (Hobserve : observe (factory_direct_q q0 q1) =
    ProbF (rational_bernoulli_measure q0 q1) (fun b => Ret b))
    by reflexivity.
  rewrite Hobserve.
  eapply ptree_stable_hitting_ast_prob with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b _. split.
    + assert (Hb : observe (Ret b : ptree factoryE EnumQ bool) = RetF b)
        by reflexivity.
      rewrite Hb. apply (ptree_stable_hitting_ret
        (FI := FreeOmegaObservableSemanticMeasure)
        (FO := FreeOmegaObservableSemanticOmega)
        (MX := FreeOmegaMixedMeasure) (E := factoryE)).
    + apply free_omega_observable_total_intro.
      exists bool, ptree_factory_head_value,
        (@sem_ret EnumQ EnumQ_SemanticMeasure bool b).
      split; [constructor|].
      change (enumQ_expect (fun _ : bool => (1 : rat)) (ret_EnumQ b) = 1).
      rewrite enumQ_expect_ret. reflexivity.
  - exact (ptree_factory_direct_q_heads_total q0 q1).
Qed.

(** Finite approximations retain exactly the support of their concrete
    observation.  No limit reasoning or example-specific law is used here. *)
Lemma ptree_factory_standard_q_row_ae : forall n x (P : bool -> Prop),
  free_omega_ae (fun h => P (ptree_factory_head_value h))
    (ptree_factory_standard_q_row n x) <->
  @sem_ae EnumQ EnumQ_SemanticMeasure _
    (meas_iter_approx n binary_coin_transition x) P.
Proof.
  induction n as [|n IH]; intros x P.
  - split; intro H.
    + intros w b Hin. contradiction.
    + constructor.
  - change (free_omega_ae (fun h => P (ptree_factory_head_value h))
      (FOSample (binary_coin_transition x) (fun next : rat + bool =>
        match next with
        | inl y => ptree_factory_standard_q_row n y
        | inr b => FORet (FHRet b)
        end)) <->
      sem_ae (sem_bind (binary_coin_transition x) (fun next : rat + bool =>
        match next with
        | inl y => meas_iter_approx n binary_coin_transition y
        | inr b => sem_ret b
        end)) P).
    rewrite sem_ae_bind_iff. split.
    + intro H. apply free_omega_ae_sample_inv in H.
      eapply sem_ae_mono; [|exact H]. intros [y|b] Hy.
      * apply (proj1 (IH y P)). exact Hy.
      * dependent destruction Hy. apply sem_ae_ret. assumption.
    + intro H. eapply FOAESample; [exact H|]. intros [y|b] Hy.
      * apply (proj2 (IH y P)). exact Hy.
      * constructor. apply (proj1 (sem_ae_ret_iff _ _)). exact Hy.
Qed.

Lemma ptree_factory_standard_q_heads_ae
    (q0 : 0 <= q) (q1 : q <= 1) (P : bool -> Prop) :
  free_omega_ae (fun h => P (ptree_factory_head_value h))
    ptree_factory_standard_q_heads <->
  @sem_ae EnumQ EnumQ_SemanticMeasure _ (rational_bernoulli_measure q0 q1) P.
Proof.
  change (free_omega_ae (fun h => P (ptree_factory_head_value h))
    (FOLub (fun n => ptree_factory_standard_q_row n q)) <->
    PTree.Prob.Backend.EnumQ.FrontierLift.enumQ_ae (rational_bernoulli_measure q0 q1) P).
  rewrite (enumQ_converges_ae_iff
    (enumQ_iter_approx_increasing binary_coin_transition q)
    (rational_binary_iteration_converges q0 q1)).
  split.
  - intro H. dependent destruction H. intro n.
    apply (proj1 (ptree_factory_standard_q_row_ae n q P)). apply H.
  - intro H. constructor. intro n.
    apply (proj2 (ptree_factory_standard_q_row_ae n q P)). apply H.
Qed.

Lemma ptree_factory_direct_q_heads_ae
    (q0 : 0 <= q) (q1 : q <= 1) (P : bool -> Prop) :
  free_omega_ae (fun h => P (ptree_factory_head_value h))
    (ptree_factory_direct_q_heads q0 q1) <->
  @sem_ae EnumQ EnumQ_SemanticMeasure _ (rational_bernoulli_measure q0 q1) P.
Proof.
  split.
  - intro H. apply free_omega_ae_sample_inv in H.
    eapply sem_ae_mono; [|exact H]. intros b Hb.
    inversion Hb; subst. assumption.
  - intro H. eapply FOAESample; [exact H|]. intros b Hb. constructor. exact Hb.
Qed.

Lemma ptree_factory_standard_q_support
    (q0 : 0 <= q) (q1 : q <= 1)
    (sim : ptree factoryE EnumQ bool -> ptree factoryE EnumQ bool -> Prop) :
  free_omega_support_lift (stable_head_rel eq sim)
    ptree_factory_standard_q_heads
    (ptree_factory_direct_q_heads q0 q1).
Proof.
  eapply free_omega_support_lift_observation_ae with
    (obsA := ptree_factory_head_value)
    (obsB := ptree_factory_head_value)
    (outA := rational_bernoulli_measure q0 q1)
    (outB := rational_bernoulli_measure q0 q1) (S := eq).
  - apply ptree_factory_standard_q_heads_ae.
  - apply ptree_factory_direct_q_heads_ae.
  - apply sem_lift_refl. intro b. reflexivity.
  - intros h1 h2 Heq.
    destruct h1 as [b1|X e1 k1], h2 as [b2|Y e2 k2];
      try destruct e1; try destruct e2.
    constructor. exact Heq.
Qed.

Lemma ptree_factory_standard_q_heads_lift_direct
    (q0 : 0 <= q) (q1 : q <= 1)
    (sim : ptree factoryE EnumQ bool -> ptree factoryE EnumQ bool -> Prop) :
  @sem_lift MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega)) _ _
    (stable_head_rel eq sim)
    ptree_factory_standard_q_heads
    (ptree_factory_direct_q_heads q0 q1).
Proof.
  eapply FOQLObserve with
    (obsA := ptree_factory_head_value)
    (obsB := ptree_factory_head_value)
    (outA := rational_bernoulli_measure q0 q1)
    (outB := ptree_factory_direct_q_observation q0 q1)
    (S := eq).
  - exact (ptree_factory_standard_q_heads_observes q0 q1).
  - exact (ptree_factory_direct_q_heads_observes q0 q1).
  - rewrite ptree_factory_direct_q_observation_eq.
    apply sem_lift_refl. intros b. reflexivity.
  - intros h1 h2 Hvalue.
    destruct h1 as [b1|X e1 k1];
      destruct h2 as [b2|Y e2 k2];
      try destruct e1; try destruct e2.
    cbn in Hvalue. subst b2. constructor. reflexivity.
  - exact (ptree_factory_standard_q_support q0 q1 sim).
Qed.

Theorem peutt_biased_to_rational_coin_direct
    (pnormalized : pfalse + ptrue = 1)
    (pnontrivial : (0 < pfalse * ptrue)%Q)
    (q0 : 0 <= q) (q1 : q <= 1) :
  @peutt factoryE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega
    bool bool eq
    (biased_to_rational_coin pfalse0 ptrue0 q) (factory_direct_q q0 q1).
Proof.
  eapply peutt_of_hitting_lift.
  - apply (proj2 (ptree_primitive_stable_hitting_adequate _ _)).
    exact (proj1 (ptree_biased_to_rational_coin_ast
      pnormalized pnontrivial q0 q1)).
  - apply (proj2 (ptree_primitive_stable_hitting_adequate _ _)).
    exact (proj1 (ptree_factory_direct_q_ast q0 q1)).
  - exact (ptree_factory_standard_q_heads_lift_direct q0 q1 _).
Qed.

End RationalTarget.

End FactoryOperationalNormalization.

Definition ptree_third_to_two_fifths_heads :
    MF (stable_head factoryE EnumQ bool) :=
  ptree_factory_q_heads third_false_nonnegative third_true_nonnegative (2 / 5).

Theorem ptree_third_to_two_fifths_weak :
  @ptree_stable_hitting factoryE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool
    (observe third_to_two_fifths)
    ptree_third_to_two_fifths_heads.
Proof.
  exact (ptree_biased_to_rational_coin_weak
    third_false_nonnegative third_true_nonnegative (2 / 5)).
Qed.

Theorem peutt_third_to_two_fifths_direct
    `{Hsupport : @OperationalFactoryStepSupportLaws vn_one_third vn_two_thirds
      third_false_nonnegative third_true_nonnegative} :
  @peutt factoryE EnumQ MF
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure)
      (NO := EnumQ_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega
    bool bool eq third_to_two_fifths direct_two_fifths.
Proof.
  exact (peutt_biased_to_rational_coin_direct
    (pfalse := vn_one_third) (ptrue := vn_two_thirds) (q := 2 / 5)
    third_bias_normalized third_bias_nontrivial
    two_fifths_nonnegative two_fifths_at_most_one).
Qed.

Import Num.Theory Order.Theory.

(** Independently verified components for the compositional Factory proof.
    The legacy nested normalization above remains available separately. *)
Local Notation peutt := (@peutt factoryE EnumQ MF
  (FreeOmegaObservableSemanticMeasure (NI := EnumQ_SemanticMeasure)
    (NO := EnumQ_SemanticOmega)) FreeOmegaObservableSemanticMeasureCoreLaws
  FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega).
Local Notation weak := (@ptree_stable_hitting factoryE EnumQ MF
  (FreeOmegaObservableSemanticMeasure (NI := EnumQ_SemanticMeasure)
    (NO := EnumQ_SemanticOmega)) FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega).

Definition factory_fair_heads : MF (stable_head factoryE EnumQ bool) :=
  FOSample vn_fair (fun b => FORet (FHRet b)).

Lemma factory_direct_fair_weak :
  weak (observe factory_direct_fair) factory_fair_heads.
Proof.
  unfold factory_direct_fair, factory_fair_heads.
  change (weak (ProbF vn_fair (fun b => Ret b))
    (mixed_bind vn_fair (fun b => FORet (FHRet b)))).
  eapply ptree_stable_hitting_prob with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b _. change (weak (RetF b) (FORet (FHRet b))).
    apply (ptree_stable_hitting_ret
      (FI := FreeOmegaObservableSemanticMeasure)
      (FO := FreeOmegaObservableSemanticOmega)
      (MX := FreeOmegaMixedMeasure) (E := factoryE)).
Qed.

Lemma factory_fair_heads_observes :
  free_omega_observes ptree_factory_head_value factory_fair_heads vn_fair.
Proof.
  unfold factory_fair_heads.
  replace vn_fair with (bind_EnumQ vn_fair (fun b => ret_EnumQ b)) at 2
    by apply finite_enum_bind_right_unit_eq.
  constructor. intro b. constructor.
Qed.

Section ParametricVN.
Variables pfalse ptrue : rat.
Hypotheses (pfalse0 : 0 <= pfalse) (ptrue0 : 0 <= ptrue).
Hypothesis pnormalized : pfalse + ptrue = 1.
Hypothesis pnontrivial : 0 < pfalse * ptrue.

Lemma factory_vn_fair_support
    (sim : ptree factoryE EnumQ bool -> ptree factoryE EnumQ bool -> Prop) :
  free_omega_support_lift (stable_head_rel eq sim)
    (ptree_factory_raw_heads pfalse0 ptrue0) factory_fair_heads.
Proof.
  assert (Hpfalse : pfalse <> 0).
  { intro Hzero. pose proof pnontrivial as Hpos. rewrite Hzero in Hpos.
    rewrite mul0r ltxx in Hpos. discriminate. }
  assert (Hptrue : ptrue <> 0).
  { intro Hzero. pose proof pnontrivial as Hpos. rewrite Hzero in Hpos.
    rewrite mulr0 ltxx in Hpos. discriminate. }
  unfold free_omega_support_lift. split.
    + intros P HP. unfold ptree_factory_raw_heads in HP.
      dependent destruction HP. specialize (H 1%nat).
      cbn [ptree_factory_raw_schedule] in H.
      rewrite ptree_factory_raw_hitting_three in H.
      pose proof (free_omega_ae_sample_inv H) as Hfirst.
      assert (Hfirst_false : free_omega_ae P
          (FOSample (factory_biased_coin pfalse0 ptrue0) (fun b2 =>
            match vn_round_result false b2 with
            | inl _ => ptree_factory_raw_hitting pfalse0 ptrue0 0
            | inr b => FORet (FHRet b)
            end))).
      { apply Hfirst with (p := pfalse).
        - cbn. auto.
        - exact Hpfalse. }
      assert (Hfirst_true : free_omega_ae P
          (FOSample (factory_biased_coin pfalse0 ptrue0) (fun b2 =>
            match vn_round_result true b2 with
            | inl _ => ptree_factory_raw_hitting pfalse0 ptrue0 0
            | inr b => FORet (FHRet b)
            end))).
      { apply Hfirst with (p := ptrue).
        - cbn. auto.
        - exact Hptrue. }
      pose proof (free_omega_ae_sample_inv Hfirst_false) as Hsecond_false.
      pose proof (free_omega_ae_sample_inv Hfirst_true) as Hsecond_true.
      assert (HPfalse : P (FHRet false)).
      { specialize (Hsecond_false ptrue true). cbn in Hsecond_false.
        pose proof (Hsecond_false (or_intror (or_introl Logic.eq_refl))
          Hptrue) as Hr.
        dependent destruction Hr. exact H0. }
      assert (HPtrue : P (FHRet true)).
      { specialize (Hsecond_true pfalse false). cbn in Hsecond_true.
        pose proof (Hsecond_true (or_introl Logic.eq_refl)
          Hpfalse) as Hr.
        dependent destruction Hr. exact H0. }
      unfold factory_fair_heads.
      eapply FOAESample with (Good := fun _ => True).
      * apply sem_ae_true.
      * intros b _. constructor. exists (FHRet b). split.
        -- constructor. reflexivity.
        -- destruct b; assumption.
    + intros Q HQ. unfold factory_fair_heads in HQ.
      pose proof (free_omega_ae_sample_inv HQ) as Hfair.
      assert (HQfalse : Q (FHRet false)).
      { specialize (Hfair one_div_two false). cbn in Hfair.
        pose proof (Hfair (or_introl Logic.eq_refl)
          ltac:(cbn; discriminate)) as Hr.
        dependent destruction Hr. exact H. }
      assert (HQtrue : Q (FHRet true)).
      { specialize (Hfair one_div_two true). cbn in Hfair.
        pose proof (Hfair (or_intror (or_introl Logic.eq_refl))
          ltac:(cbn; discriminate)) as Hr.
        dependent destruction Hr. exact H. }
      apply free_omega_ae_mono with (P := fun _ => True).
      * intros h _. destruct h as [b|X e k]; [|destruct e].
        exists (FHRet b). split; [constructor; reflexivity|].
        destruct b; assumption.
      * generalize (ptree_factory_raw_heads pfalse0 ptrue0). intro mu. induction mu.
        -- constructor. exact I.
        -- constructor.
        -- eapply FOAESample with (Good := fun _ => True).
           ++ apply (@sem_ae_true EnumQ EnumQ_SemanticMeasure
                EnumQ_SemanticMeasureCoreLaws).
           ++ intros x _. exact (H x).
        -- constructor. exact H.
Qed.

Lemma factory_vn_fair_heads_lift
    (sim : ptree factoryE EnumQ bool -> ptree factoryE EnumQ bool -> Prop) :
  free_omega_qlift (stable_head_rel eq sim)
    (ptree_factory_raw_heads pfalse0 ptrue0) factory_fair_heads.
Proof.
  eapply FOQLObserve with
    (obsA := ptree_factory_head_value)
    (obsB := ptree_factory_head_value)
    (outA := vn_fair) (outB := vn_fair) (S := eq).
  - exact (ptree_factory_fair_heads_observes pfalse0 ptrue0 pnormalized pnontrivial).
  - exact factory_fair_heads_observes.
  - apply sem_lift_refl. intro b. reflexivity.
  - intros h1 h2 Hvalue.
    destruct h1 as [b1|X e1 k1], h2 as [b2|Y e2 k2];
      try destruct e1; try destruct e2.
    cbn in Hvalue. subst b2. constructor. reflexivity.
  - exact (factory_vn_fair_support sim).
Qed.

Theorem peutt_factory_vn_fair :
  peutt eq (factory_fair_coin pfalse0 ptrue0) factory_direct_fair.
Proof.
  eapply peutt_of_hitting_lift.
  - exact (ptree_factory_fair_coin_weak pfalse0 ptrue0).
  - exact factory_direct_fair_weak.
  - exact (factory_vn_fair_heads_lift _).
Qed.
End ParametricVN.

Definition factory_standard_step (x : rat) : ptree factoryE EnumQ (rat + bool) :=
  Prob (binary_coin_transition x) (fun next => Ret next).
Definition factory_standard (q : rat) : ptree factoryE EnumQ bool :=
  PTree.iter factory_standard_step q.

Lemma factory_standard_step_weak x :
  weak (observe (factory_standard_step x)) (ptree_factory_standard_step_heads x).
Proof.
  unfold factory_standard_step, ptree_factory_standard_step_heads.
  change (weak (ProbF (binary_coin_transition x) (fun next => Ret next))
    (mixed_bind (binary_coin_transition x) (fun next => FORet (FHRet next)))).
  eapply ptree_stable_hitting_prob with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros next _. apply ptree_factory_binary_ret_weak.
Qed.

Lemma factory_standard_weak q :
  weak (observe (factory_standard q)) (ptree_factory_standard_q_heads q).
Proof.
  unfold factory_standard.
  eapply ptree_stable_hitting_iter_of_unbounded_steps
    with (step_out := ptree_factory_standard_step_heads)
         (no_event := factoryE_no_event).
  - exact factory_standard_step_weak.
  - unfold ptree_factory_standard_q_heads.
    apply FOQLLub. intro n.
    assert (Hrows : forall x,
      iter_complete_rows factoryE_no_event
        ptree_factory_standard_step_heads n x =
      ptree_factory_standard_q_row n x).
    { induction n as [|n IH]; intro x; [reflexivity|].
      cbn [iter_complete_rows ptree_factory_standard_q_row].
      f_equal. }
    rewrite Hrows. apply free_omega_qlift_refl. intro h. reflexivity.
Qed.

Section StandardRationalTarget.
Variable q : rat.
Hypotheses (q0 : 0 <= q) (q1 : q <= 1).

Theorem peutt_factory_standard_direct :
  peutt eq (factory_standard q) (factory_direct_q q0 q1).
Proof.
  eapply peutt_of_hitting_lift.
  - exact (factory_standard_weak q).
  - apply (proj2 (ptree_primitive_stable_hitting_adequate _ _)).
    exact (proj1 (ptree_factory_direct_q_ast q0 q1)).
  - exact (ptree_factory_standard_q_heads_lift_direct q0 q1 _).
Qed.

End StandardRationalTarget.
