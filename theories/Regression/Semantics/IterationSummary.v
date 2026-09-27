(** Silent rounds in an inhabited event signature; no AST, finite-state,
    or finite full-result-limit premise. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import SubEnumQ.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
From PTree.Prob.Interface Require Import Measure AE Omega.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Measure Observation StructuralMeasure.
From PTree.Eq Require Import PTreeKernel UnifiedFrontier.
From PTree.Eq.FreeOmega Require Import Hitting.
From PTree.Interp.FreeOmega Require Import IterationSummary.
Set Implicit Arguments.

Variant questionE : Type -> Type := Question : questionE bool.
Local Notation NI := SubEnumQ_SemanticMeasure.
Local Notation NO := SubEnumQ_SemanticOmega.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Local Notation hits t out := (ptree_stable_hitting (FI := FI) (FO := FO) (observe t) out).

Section ArbitraryKernel.
Variable kernel : nat -> SubEnumQ (nat + (nat * bool)).
Definition delayed_round i : ptree questionE SubEnumQ (nat + (nat * bool)) :=
  Tau (Prob (kernel i) (fun x => Ret x)).

Example delayed_kernel_summary i :
  hits (PTree.iter delayed_round i) (iteration_frontier kernel i).
Proof.
  eapply iteration_frontier_summary_hitting; try typeclasses eauto.
  intro j. apply stable_hitting_tau.
  eapply (stable_hitting_prob (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure))
    with (Good := fun _ => True).
  - apply sem_ae_true.
  - intros x _. apply (stable_hitting_ret (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure)).
Qed.

Definition only_bit (h : stable_head questionE SubEnumQ (nat * bool)) :=
  match h with FHRet sb => Some (snd sb) | FHVis _ _ _ => None end.

(** Only the bit projection has a supplied native limit, not the nat/bit
    joint distribution. The state and returned nat remain unbounded. *)
Example projected_limit i (out : SubEnumQ (option bool)) :
  sem_lub (fun n => iteration_observation_round kernel
    (fun sb => Some (snd sb)) n i) out ->
  free_omega_observes only_bit (iteration_frontier kernel i) out.
Proof. apply iteration_frontier_observes. reflexivity. Qed.

Example observer_rejects_visible k : only_bit (FHVis Question k) = None.
Proof. reflexivity. Qed.
End ArbitraryKernel.

(** Zero is a legitimate partial kernel; the summary does not assert totality. *)
Example zero_mass_summary :
  hits (PTree.iter (delayed_round (fun _ => sem_zero)) 0)
    (iteration_frontier (fun _ : nat => @sem_zero SubEnumQ NI NO (nat + (nat * bool))%type) 0).
Proof. apply delayed_kernel_summary. Qed.

(** Every round returns a retry, but the loop never returns a value. *)
Definition retry_kernel (i : nat) : SubEnumQ (nat + bool) := sem_ret (inl (S i)).
Example endless_retry_summary i :
  hits (PTree.iter (fun j => (Ret (inl (S j)) : ptree questionE SubEnumQ (nat + bool))) i)
    (iteration_frontier retry_kernel i).
Proof.
  eapply iteration_frontier_summary_hitting; try typeclasses eauto.
  intro j. apply stable_hitting_native_ret.
Qed.

Fail Check PTree.Eq.Backend.MathComp.Direct.mathcomp_direct_peutt.
