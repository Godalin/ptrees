(** Supporting example: unbounded biased-coin retries stop at a mixed
    return/visible frontier. Reading entry: absorbing_program_rewrite.
    The event's continuation is retained whole, not response-wise projected. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Morphisms.
From mathcomp Require Import ssreflect ssralg rat.
From PTree Require Import PTreeFacts.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import PStruct PEutt UnifiedFrontier PTreeKernel Shallow.
From PTree.Eq.FreeOmega Require Import Base Bind Hitting Iter.
From PTree.Prob.Interface Require Import Measure AE Omega Mixed.
From PTree.Prob.Backend.EnumQ Require Import Representation Measure.
From PTree.Prob.Backend.Common Require Import FiniteRecordExtensionality.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Measure StructuralMeasure Observation.
From PTree.Interp.FreeOmega Require Import Rewriting IterationSummary AbsorbingIteration.
From PTree.Examples.BernoulliFactory Require Import VonNeumannUnbounded OperationalVonNeumann.
Set Implicit Arguments.
Import EnumQ FreeOmegaRewriting GRing.Theory.
Local Open Scope ring_scope.

Variant queryE : Type -> Type := Query : queryE bool.
Local Notation tree := (ptree queryE EnumQ).
Local Notation MF := (FreeOmega EnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := EnumQ_SemanticMeasure) (NO := EnumQ_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := EnumQ_SemanticMeasure) (NO := EnumQ_SemanticOmega)).
Local Notation W := (PEutt.peutt (E := queryE) (FI := FI) (FO := FO) eq).
Local Notation "t ≈ₚ u" := (W t u) (at level 70, no associativity) : type_scope.
Local Notation hits t out := (ptree_stable_hitting (FI := FI) (FO := FO) (observe t) out).

(** Only a Boolean exit descriptor is sampled. Recursive heads themselves
    are not put into the native carrier, avoiding a recursive-universe demand. *)
Definition reveal (b : bool) : tree bool :=
  if b then Vis Query (fun answer => Ret answer) else Ret false.
Definition reveal_head b : stable_head queryE EnumQ bool :=
  if b then FHVis Query (fun answer => Ret answer) else FHRet false.
Definition reveal_front b := FORet (reveal_head b) : MF (stable_head queryE EnumQ bool).
Definition round := @vn_step_in queryE.
Definition absorbing_step := pstruct_iter_natural_step round reveal.
Definition absorbing_program : tree bool := PTree.iter absorbing_step tt.
Definition staged_program : tree bool := PTree.bind (PTree.iter round tt) reveal.
Definition direct_program : tree bool := PTree.bind direct_fair_in reveal.
Definition first_frontier := FOSample vn_fair reveal_front.
Definition round_frontier := absorbing_frontier (fun _ : unit => vn_transition) reveal_front tt.

(** The whole program calculation is a rewrite chain; no new probability
    analysis or hand-written recursive bisimulation is hidden here. *)
Theorem absorbing_program_rewrite : absorbing_program ≈ₚ direct_program.
Proof.
  unfold absorbing_program, absorbing_step, direct_program.
  rewrite <- peutt_iter_natural.
  change (PTree.bind (@von_neumann_third_in queryE) reveal ≈ₚ
    PTree.bind (@direct_fair_in queryE) reveal).
  setoid_rewrite von_neumann_third_in_equivalent_to_fair.
  reflexivity.
Qed.

Lemma round_hitting i : hits (round i)
  (FOSample vn_transition (fun next => FORet (FHRet next))).
Proof.
  assert (Heq : vn_round_measure = vn_transition).
  { apply finite_enum_raw_eq. exact vn_round_measure_eq. }
  rewrite <- Heq. unfold round, vn_step_in, vn_round_measure.
  eapply (stable_hitting_native_sample (NI := EnumQ_SemanticMeasure)); try typeclasses eauto. intro a.
  eapply (stable_hitting_native_sample (NI := EnumQ_SemanticMeasure)); try typeclasses eauto. intro b.
  apply (stable_hitting_native_ret (NI := EnumQ_SemanticMeasure)).
Qed.

Lemma reveal_hitting b : hits (reveal b) (reveal_front b).
Proof.
  destruct b; [apply (stable_hitting_vis (FI := FI) (FO := FO))|
    apply (stable_hitting_ret (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure))].
Qed.

Theorem staged_frontier_exact : hits staged_program round_frontier.
Proof. eapply absorbing_iteration_summary; [exact round_hitting|exact reveal_hitting]. Qed.

Theorem absorbing_round_frontier out : hits absorbing_program out ->
  @sem_lift MF FI _ _ (stable_head_rel eq W) out round_frontier.
Proof. eapply absorbing_iteration_heads; [exact round_hitting|exact reveal_hitting]. Qed.

Lemma direct_frontier_exact : hits direct_program first_frontier.
Proof.
  unfold direct_program, direct_fair_in. rewrite observe_bind.
  change (hits (Prob vn_fair (fun b => reveal b)) first_frontier).
  eapply (stable_hitting_prob (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure))
    with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros b _. exact (reveal_hitting b).
Qed.

(** An actual complete witness exists, and ANY witness has one coupling
    with the mixed Ret/Vis reference. No response-wise marginal shortcut. *)
Theorem absorbing_first_frontier out : hits absorbing_program out ->
  @sem_lift MF FI _ _ (stable_head_rel eq W) out first_frontier.
Proof.
  intro Hout. eapply peutt_hitting_lift.
  - exact absorbing_program_rewrite.
  - exact Hout.
  - exact direct_frontier_exact.
Qed.

Theorem absorbing_first_frontier_exists : exists out,
  hits absorbing_program out /\
  @sem_lift MF FI _ _ (stable_head_rel eq W) out first_frontier.
Proof.
  destruct (ptree_stable_hitting_exists (FI := FI) (FO := FO) (observe absorbing_program)) as [out Hout].
  exists out. split; [exact Hout|exact (absorbing_first_frontier Hout)].
Qed.

Definition offered (h : stable_head queryE EnumQ bool) : bool :=
  match h with FHRet _ => false | FHVis _ _ _ => true end.
Definition offer_law := sem_bind vn_fair (fun b => sem_ret b : EnumQ bool).
Theorem first_frontier_offers : free_omega_observes offered first_frontier offer_law.
Proof. constructor. intros []; constructor. Qed.
Theorem offer_probability : enumQ_expect (fun b => if b then 1 else 0) offer_law = 1/2.
Proof. by vm_compute. Qed.

(** The visible branch has not consumed a response in the first frontier. *)
Example visible_continuation_kept : reveal_head true = FHVis Query (fun answer => Ret answer).
Proof. reflexivity. Qed.
Example returning_branch_kept : reveal_head false = FHRet false.
Proof. reflexivity. Qed.
