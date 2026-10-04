(** One-way interpretation of the classical formal iteration into the
    independent least-fixed-point domain. No raw-syntax order completeness
    or new evaluator is postulated. *)
From Coq Require Import Utf8.

Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import reals.
From PTree.Prob.Interface Require Import Measure Omega KleisliIteration.
From PTree.Prob.Domain Require Import Expectation Iteration.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Measure IterationOrder.
From PTree.Prob.FreeOmega.Validation Require Import Model.
Set Implicit Arguments.
Unset Strict Implicit.

Section Validation.
Context {MN : Type → Type} `{NI : SemanticMeasure MN}
  `{NO : @SemanticOmega MN NI}.
Variable R : realType.
Variable native : ∀ X, MN X → OmegaVal R X.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Context {I A : Type} (K : I → FreeOmega MN (I+A)) (V : I → OmegaVal R (I+A)).
Hypothesis HK : ∀ i, free_omega_model_denotes native (K i) (V i).

Theorem free_omega_iter_approx_denotes n i :
  free_omega_model_denotes native
    (sem_iter_approx (MI := FI) (MO := FO) K n i) (oval_iter_approx V n i).
Proof.
  revert i; induction n as [|n IH]; intro i.
  - intros f Hf. reflexivity.
  - change (free_omega_model_denotes native
      (free_omega_bind (K i) (λ v, match v with
        | inl j => sem_iter_approx (MI := FI) (MO := FO) K n j
        | inr a => FORet a end))
      (oval_bind (V i) (λ v, match v with
        | inl j => oval_iter_approx V n j | inr a => oval_ret R a end))).
    apply model_denotes_bind; [apply HK|].
    intros [j|a]; [apply IH|intros f Hf; reflexivity].
Qed.

Theorem free_omega_iteration_denotes_lfp i :
  free_omega_model_denotes native
    (FOLub (λ n, sem_iter_approx (MI := FI) (MO := FO) K n i)) (oval_iter V i).
Proof. apply model_denotes_lub. intro n. apply free_omega_iter_approx_denotes. Qed.

Corollary free_omega_iteration_modelable i :
  free_omega_modelable native
    (FOLub (λ n, sem_iter_approx (MI := FI) (MO := FO) K n i)).
Proof.
  apply (proj2 (modelable_iff_denotes _ _)).
  exists (oval_iter V i). apply free_omega_iteration_denotes_lfp.
Qed.
End Validation.

(** Public iteration spelling: this is definitionally the existing formal
    approximant limit, so its independent lfp validation is reused verbatim. *)
Corollary free_omega_iter_denotes_lfp {MN : Type → Type}
    `{NI : SemanticMeasure MN} `{NO : @SemanticOmega MN NI}
    (R : realType) (native : ∀ X, MN X → OmegaVal R X)
    {I A} (K : I → FreeOmega MN (I+A)) (V : I → OmegaVal R (I+A)) :
  (∀ i, free_omega_model_denotes native (K i) (V i)) → ∀ i,
  free_omega_model_denotes native (free_omega_iter K i) (oval_iter V i).
Proof. apply free_omega_iteration_denotes_lfp. Qed.
