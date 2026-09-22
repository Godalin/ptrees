(** Role: SubEnumQ-specific conditional resampling for internal kernels.
    Uses concrete disintegration; not generic FreeOmega theory or a new equality. *)
Set Universe Polymorphism.
From Coq.Logic Require Import ClassicalChoice.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure PTree.Prob.Backend.EnumQ.Disintegration.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.SubEnumQ.FreeOmega.Disintegration.
From PTree.Eq Require Import PrimitiveStableHitting.
From PTree.Eq.Internal.FreeOmega Require Import KernelCompletion KernelCongruence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Reconstruct a correlated sample in EVERY round, with the native joint,
    marginal, and conditional law allowed to depend on the whole state.
    Complete hitting is preserved, without AST or a round bound.  This is
    rescheduling of a given native joint, not extraction of an arbitrary
    FreeOmega quotient coupling or adequacy of arbitrary residual cuts. *)
Section Resampling.
Context {S O A B : Type}.
Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Variable joint : S -> SubEnumQ B.
Variable marginal : S -> SubEnumQ A.
Variable conditional : S -> A -> SubEnumQ B.
Variable continue : S -> B -> MF (stable_target S O).
Variable D : S -> Prop.
Hypothesis reconstruct : forall s, D s ->
  sem_eq (subenumQ_bind (marginal s) (conditional s)) (joint s).
Hypothesis closed : forall s, D s ->
  free_omega_ae (kernel_completion_invariant D)
    (FOSample (joint s) (continue s)).

Theorem kernel_resampling_stable_hitting s out1 out2 :
  D s ->
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega S O
    (fun s => FOSample (joint s) (continue s)) s out1 ->
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega S O
    (fun s => FOSample (marginal s)
      (fun a => FOSample (conditional s a) (continue s))) s out2 ->
  free_omega_qlift eq out1 out2.
Proof.
  intros HD Hleft Hright.
  eapply kernel_stable_hitting_eq with (D := D)
    (left := fun s => FOSample (joint s) (continue s))
    (right := fun s => FOSample (marginal s)
      (fun a => FOSample (conditional s a) (continue s))).
  - exact closed.
  - intros q Hq. apply FOQLMono with (T := fun x y => y = x).
    + apply FOQLSym. apply free_omega_sample_disintegration.
      apply reconstruct. exact Hq.
    + intros x y Hyx. symmetry. exact Hyx.
  - exact HD.
  - exact Hleft.
  - exact Hright.
Qed.
End Resampling.

(** S may contain a pair of trees and execution history.  The selected
    conditionals depend on that S; no unary-policy uniformization occurs.
    Only the sampled A/B values belong to the native carrier universe. *)
Theorem kernel_disintegration_exists {S O A B : Type}
    (joint : S -> SubEnumQ (A * B)) (marginal : S -> SubEnumQ A)
    (continue : S -> A * B -> FreeOmega SubEnumQ (stable_target S O))
    (Hgraph : forall s, sem_lift (fun p x => fst p = x) (joint s) (marginal s)) :
  exists conditional : S -> A -> SubEnumQ (A * B),
    (forall s, sem_eq (subenumQ_bind (marginal s) (conditional s)) (joint s)) /\
    (forall s a, sem_ae (conditional s a) (fun p => fst p = a)) /\
    (forall s, sem_ae (marginal s) (fun a => subenumQ_total (conditional s a))) /\
    forall s out1 out2,
      @stable_hitting (FreeOmega SubEnumQ)
        (FreeOmegaObservableSemanticMeasure
          (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega))
        FreeOmegaObservableSemanticOmega S O
        (fun s => FOSample (joint s) (continue s)) s out1 ->
      @stable_hitting (FreeOmega SubEnumQ)
        (FreeOmegaObservableSemanticMeasure
          (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega))
        FreeOmegaObservableSemanticOmega S O
        (fun s => FOSample (marginal s)
          (fun a => FOSample (conditional s a) (continue s))) s out2 ->
      free_omega_qlift eq out1 out2.
Proof.
  assert (Hex : forall s, exists k : A -> SubEnumQ (A * B),
    sem_eq (subenumQ_bind (marginal s) k) (joint s) /\
    (forall a, sem_ae (k a) (fun p => fst p = a)) /\
    sem_ae (marginal s) (fun a => subenumQ_total (k a))).
  { intro s. destruct (subenumQ_disintegration_over (Hgraph s))
      as [k [Hr [Hf [_ Ht]]]].
    exists k. repeat split; assumption. }
  destruct (choice _ Hex) as [k Hk]. exists k.
  split; [intro s; exact (proj1 (Hk s))|].
  split; [intro s; exact (proj1 (proj2 (Hk s)))|].
  split; [intro s; exact (proj2 (proj2 (Hk s)))|].
  intros s out1 out2 Hleft Hright.
  eapply kernel_resampling_stable_hitting with (D := fun _ => True).
  - intros q _. exact (proj1 (Hk q)).
  - intros q _. eapply free_omega_ae_mono with (P := fun _ => True).
    + intros [o|q'] _; exact I.
    + apply (@sem_ae_true (FreeOmega SubEnumQ)
        (FreeOmegaObservableSemanticMeasure
          (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega))
        FreeOmegaObservableSemanticMeasureCoreLaws).
  - exact I.
  - exact Hleft.
  - exact Hright.
Qed.
