(** Next-device action law. The frontier retains the FULL reply continuation;
    the boolean query only projects the chosen production mode afterwards. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order rat.
From ITree.Indexed Require Import Sum.
From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import EnumQ ProbabilisticTraceEnumQ.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.Observation.
From PTree.Prob.FreeOmega Require Import StructuralMeasure.
From PTree.Eq Require Import ProbabilisticTrace PTreeKernel.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Prob.Backend.EnumQ Require Import Measure Bind.
From PTree.Interp Require Import State StateFacts.
From PTree.Interp.FreeOmega Require Import Base State.
From PTree.Examples.BernoulliFactory Require Import BernoulliFactory RationalBernoulli.
From PTree.Examples.FactoryController Require Import Controller Facts.
Import ListNotations GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.
Set Default Timeout 20.

Definition resume sampler (v : phase + Empty_set) : tree Empty_set :=
  match v with
  | inl pc => Tau (controller sampler pc)
  | inr x => Ret x
  end.
Definition machine_cont sampler job reply := PTree.bind (respond job reply) (resume sampler).
Definition after_receive sampler job : tree Empty_set :=
  PTree.bind sampler (fun fast => Vis (inr1 (RunMachine job fast)) (machine_cont sampler job)).

Lemma controller_order_unfold sampler :
  controller sampler AwaitOrder ≈ₚ
  Vis (inr1 ReceiveOrder) (fun job => controller sampler (Manufacturing job)).
Proof.
  unfold controller at 1. rewrite peutt_iter_unfold.
  change (Vis (inr1 ReceiveOrder)
    (fun job => PTree.bind (Ret (inl (Manufacturing job))) (resume sampler)) ≈ₚ
    Vis (inr1 ReceiveOrder) (fun job => controller sampler (Manufacturing job))).
  apply peutt_vis. intro job.
  transitivity (resume sampler (inl (Manufacturing job))).
  - exact (PTree.Eq.Algebra.peutt_bind_ret_l _ (resume sampler)).
  - apply peutt_tau_l.
Qed.

Lemma controller_manufacturing_unfold sampler job :
  controller sampler (Manufacturing job) ≈ₚ after_receive sampler job.
Proof.
  unfold controller at 1. rewrite peutt_iter_unfold.
  change (PTree.bind (attempt sampler job) (resume sampler) ≈ₚ after_receive sampler job).
  unfold attempt, after_receive. rewrite peutt_bind_assoc.
  eapply peutt_bind; [reflexivity|]. intros x y ->.
  apply PTree.Eq.Algebra.peutt_observe_eq. reflexivity.
Qed.

Section NextAction.
Variable q : rat.
Variables (q0 : 0 <= q) (q1 : q <= 1).
Local Notation coin := (rational_bernoulli_measure q0 q1).
Definition native_sampler : tree bool := Prob coin (fun b => Ret b).

Lemma embedded_direct_native : embed (factory_direct_q q0 q1) ≈ₚ native_sampler.
Proof.
  unfold embed, factory_direct_q, native_sampler. rewrite peutt_interp_prob.
  eapply peutt_prob with (XR := eq).
  - apply sem_lift_refl. intros b. reflexivity.
  - intros b c ->. apply peutt_interp_ret.
Qed.

(** The simple normal form keeps the actual implementation continuation.
    Only the finite pre-Vis sampling computation is replaced. *)
Definition next_normal sampler job : tree Empty_set :=
  Prob coin (fun fast => Vis (inr1 (RunMachine job fast)) (machine_cont sampler job)).

Lemma next_normal_form sampler job : sampler ≈ₚ native_sampler ->
  after_receive sampler job ≈ₚ next_normal sampler job.
Proof.
  intro H. unfold after_receive.
  transitivity (PTree.bind native_sampler
    (fun fast => Vis (inr1 (RunMachine job fast)) (machine_cont sampler job))).
  - eapply peutt_bind; [exact H|]. intros b c ->. reflexivity.
  - change (Prob coin (fun b => PTree.bind (Ret b)
      (fun fast => Vis (inr1 (RunMachine job fast)) (machine_cont sampler job))) ≈ₚ
      next_normal sampler job).
    eapply peutt_prob with (XR := eq).
    + apply sem_lift_refl. intro b. reflexivity.
    + intros b c ->. exact (PTree.Eq.Algebra.peutt_bind_ret_l c
        (fun fast => Vis (inr1 (RunMachine job fast)) (machine_cont sampler job))).
Qed.

Definition next_device sampler job s := run_state (next_normal sampler job) s.
Definition device_front sampler job s :=
  FOSample coin (fun fast => FORet
    (FHVis (RunMachine job fast) (fun reply => run_state (machine_cont sampler job reply) s))).

Lemma next_device_hitting sampler job s :
  ptree_stable_hitting (MF := FreeOmega EnumQ)
    (FI := FreeOmegaObservableSemanticMeasure) (FO := FreeOmegaObservableSemanticOmega)
    (observe (next_device sampler job s)) (device_front sampler job s).
Proof.
  change (ptree_stable_hitting (MF := FreeOmega EnumQ)
    (FI := FreeOmegaObservableSemanticMeasure) (FO := FreeOmegaObservableSemanticOmega)
    (observe (Prob coin (fun fast =>
      Vis (RunMachine job fast) (fun reply => run_state (machine_cont sampler job reply) s))))
    (device_front sampler job s)).
  unfold device_front.
  apply (stable_hitting_prob (FI := FreeOmegaObservableSemanticMeasure)
    (FO := FreeOmegaObservableSemanticOmega) (MX := FreeOmegaMixedMeasure)
    (front := fun fast => FORet (FHVis (RunMachine job fast)
      (fun reply => run_state (machine_cont sampler job reply) s))))
    with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b _. apply (stable_hitting_vis
      (FI := FreeOmegaObservableSemanticMeasure) (FO := FreeOmegaObservableSemanticOmega)).
Qed.

(** Every complete implementation frontier couples with the explicit normal
    frontier, relating whole reply continuations, not just event labels. *)
Theorem next_device_frontier sampler job s out :
  sampler ≈ₚ native_sampler ->
  ptree_stable_hitting (MF := FreeOmega EnumQ)
    (FI := FreeOmegaObservableSemanticMeasure) (FO := FreeOmegaObservableSemanticOmega)
    (observe (run_state (controller sampler (Manufacturing job)) s)) out ->
  sem_lift (SemanticMeasure := FreeOmegaObservableSemanticMeasure)
    (stable_head_rel eq (fun t u => t ≈ₚ u)) out (device_front sampler job s).
Proof.
  intros H Hhit. eapply peutt_hitting_lift.
  - apply run_state_peutt_eq. transitivity (after_receive sampler job).
    + apply controller_manufacturing_unfold.
    + apply next_normal_form. exact H.
  - exact Hhit.
  - apply next_device_hitting.
Qed.

Definition accepts_mode (fast : bool) {X} (e : deviceE X) : bool :=
  match e with RunMachine _ b => Bool.eqb b fast | _ => false end.
Definition mode_query sampler job s fast :=
  sem_bind (SemanticMeasure := FreeOmegaObservableSemanticMeasure) (device_front sampler job s)
    (fun h => sem_ret (observe_stable_head (fun _ => false) (@accepts_mode fast) h)).

Lemma next_device_query sampler job s fast :
  next_event_query (MF := FreeOmega EnumQ)
    (FI := FreeOmegaObservableSemanticMeasure) (FO := FreeOmegaObservableSemanticOmega)
    (@accepts_mode fast) (next_device sampler job s) (mode_query sampler job s fast).
Proof. exists (device_front sampler job s). split; [apply next_device_hitting|apply sem_eq_refl]. Qed.

Definition mode_measure fast : EnumQ bool :=
  bind_EnumQ coin (fun b => ret_EnumQ (Bool.eqb b fast)).
Lemma mode_query_denotes sampler job s fast :
  free_omega_denotes (NI := EnumQ_SemanticMeasure) (NO := EnumQ_SemanticOmega)
    (fun b : bool => b) (mode_query sampler job s fast) (mode_measure fast).
Proof.
  exists (mode_measure fast). split; [|apply sem_eq_refl].
  unfold mode_query, device_front, mode_measure.
  cbn [sem_bind sem_ret free_omega_bind FreeOmegaObservableSemanticMeasure
    observe_stable_head accepts_mode].
  constructor. intro b.
  exact (@FOOObserveRet EnumQ EnumQ_SemanticMeasure EnumQ_SemanticOmega
    bool bool (fun x => x) (Bool.eqb b fast)).
Qed.

Lemma mode_measure_probability fast :
  enumQ_expect enumQ_bool_indicator (mode_measure fast) = if fast then q else 1-q.
Proof.
  unfold mode_measure. rewrite enumQ_expect_bind.
  replace (fun b => enumQ_expect enumQ_bool_indicator (ret_EnumQ (Bool.eqb b fast)))
    with (fun b => if Bool.eqb b fast then 1 else 0 : rat).
  2: { apply functional_extensionality. intro b. rewrite enumQ_expect_ret. reflexivity. }
  change (enumQ_expect (fun b => if Bool.eqb b fast then 1 else 0) coin =
    if fast then q else 1-q).
  rewrite rational_bernoulli_indicator. by destruct fast; rewrite /= ?addr0 ?add0r.
Qed.

Theorem next_action_distribution sampler job s fast :
  sampler ≈ₚ native_sampler ->
  exists query,
    next_event_query (MF := FreeOmega EnumQ)
      (FI := FreeOmegaObservableSemanticMeasure) (FO := FreeOmegaObservableSemanticOmega)
      (@accepts_mode fast) (run_state (controller sampler (Manufacturing job)) s) query /\
    sem_lift (SemanticMeasure := FreeOmegaObservableSemanticMeasure) eq
      (mode_query sampler job s fast) query.
Proof.
  intro H. eapply peutt_preserves_next_event_query.
  - apply peutt_sym, run_state_peutt_eq.
    transitivity (after_receive sampler job).
    + apply controller_manufacturing_unfold.
    + apply next_normal_form. exact H.
  - apply next_device_query.
Qed.

Definition select_mode (fast : bool) {X} (e : deviceE X) : option X :=
  match e in deviceE Y return option Y with
  | RunMachine _ b => if Bool.eqb b fast then Some Pass else None
  | _ => None
  end.

Lemma select_mode_accept fast :
  @selector_accept deviceE (@select_mode fast) = @accepts_mode fast.
Proof.
  apply functional_extensionality_dep. intro X.
  apply functional_extensionality. intro e. destruct e; try reflexivity.
  destruct fast0, fast; reflexivity.
Qed.

(** Numeric, paper-facing endpoint. The one-event selector merely supplies
    an arbitrary reply; for a singleton query the continuation is not run. *)
Theorem next_action_probability sampler job s fast :
  sampler ≈ₚ native_sampler ->
  Prₜ[ run_state (controller sampler (Manufacturing job)) s |
       [@select_mode fast] ] = (if fast then q else 1-q).
Proof.
  intro H. destruct (next_action_distribution job s fast H) as [query [Hquery Hlift]].
  eapply enumQ_finite_interaction_probability_intro
    with (query := query) (representative := mode_query sampler job s fast)
      (out := mode_measure fast).
  - apply (proj2 (finite_interaction_query_singleton_iff_next_event_query
      (@select_mode fast) _ _)).
    rewrite select_mode_accept. exact Hquery.
  - exact Hlift.
  - apply mode_query_denotes.
  - apply mode_measure_probability.
Qed.
End NextAction.

Theorem factory_next_action_probability job s fast :
  Prₜ[ run_state (controller implementation_sampler (Manufacturing job)) s |
       [@select_mode fast] ] = (if fast then 2/5 else 3/5).
Proof.
  replace (if fast then 2/5 else 3/5 : rat) with
    (if fast then 2/5 else 1-2/5 : rat) by (destruct fast; reflexivity).
  apply (next_action_probability (q0 := two_fifths_nonnegative)
    (q1 := two_fifths_at_most_one)).
  transitivity specification_sampler; [apply implementation_sampler_correct|].
  apply embedded_direct_native.
Qed.
