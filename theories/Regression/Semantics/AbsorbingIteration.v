(** Boundary probes for first-observation absorption, not new case analysis. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure AE Omega.
From PTree.Prob.Backend.SubEnumQ Require Import Representation Measure.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import StructuralMeasure Measure.
From PTree.Eq Require Import PTreeKernel UnifiedFrontier PStruct PEutt.
From PTree.Eq.FreeOmega Require Import Base Hitting Bind.
From PTree.Interp.FreeOmega Require Import AbsorbingIteration.
Set Implicit Arguments.

Variant deadE : Type -> Type := DeadA : deadE Empty_set | DeadB : deadE Empty_set.
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation hits t out := (ptree_stable_hitting (FI := FI) (FO := FO) (observe t) out).

Definition dead_exit (_ : unit) : ptree deadE SubEnumQ bool :=
  Vis DeadA (fun x : Empty_set => match x with end).
Definition dead_front (_ : unit) :=
  FORet (FHVis DeadA (fun x : Empty_set => match x with end)) :
    FreeOmega SubEnumQ (stable_head deadE SubEnumQ bool).

Section Kernels.
(** No totality premise: includes zero-mass and partial native kernels. *)
Variable kernel : nat -> SubEnumQ (nat + unit).
Definition round i : ptree deadE SubEnumQ (nat + unit) := Prob (kernel i) (fun v => Ret v).
Lemma round_hits i : hits (round i) (FOSample (kernel i) (fun v => FORet (FHRet v))).
Proof.
  eapply (stable_hitting_prob (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure))
    with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros v _. apply (stable_hitting_ret (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)).
Qed.
Lemma dead_exit_hits b : hits (dead_exit b) (dead_front b).
Proof. apply (stable_hitting_vis (FI := FI) (FO := FO)). Qed.

Example empty_response_frontier i :
  hits (PTree.bind (PTree.iter round i) dead_exit)
    (absorbing_frontier kernel dead_front i).
Proof. eapply absorbing_iteration_summary; [exact round_hits|exact dead_exit_hits]. Qed.

Example actual_eventful_loop_exists i : exists out,
  hits (PTree.iter (pstruct_iter_natural_step round dead_exit) i) out /\
  @sem_lift (FreeOmega SubEnumQ) FI _ _
    (stable_head_rel eq (peutt (FI := FI) (FO := FO) eq))
    out (absorbing_frontier kernel dead_front i).
Proof. eapply absorbing_iteration_exists; [exact round_hits|exact dead_exit_hits]. Qed.
End Kernels.

Example zero_kernel_allowed :
  hits (PTree.bind (PTree.iter (round (fun _ => subenumQ_zero)) 0) dead_exit)
    (absorbing_frontier (fun _ : nat => @subenumQ_zero (nat + unit)%type) dead_front 0).
Proof. apply empty_response_frontier. Qed.

(** No response is executed to form the offered-event head. *)
Example dead_event_is_visible : dead_front tt = FORet (FHVis DeadA (fun x : Empty_set => match x with end)).
Proof. reflexivity. Qed.
Example distinct_dead_heads :
  (FHVis DeadA (fun x : Empty_set => match x with end) : stable_head deadE SubEnumQ bool) <>
  FHVis DeadB (fun x : Empty_set => match x with end).
Proof. discriminate. Qed.

Fail Check PTree.Eq.Backend.MathComp.Direct.mathcomp_direct_peutt.
