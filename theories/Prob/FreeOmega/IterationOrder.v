(** Public least-fixed-point rules for FreeOmega iteration. The fixed-point
    equation remains the existing qlift equality; only leastness uses the new
    preorder. No external model, probability validity premise, or replacement
    SemanticOmega instance is needed for these internal proof rules. *)
From Coq Require Import Utf8.
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega KleisliIteration.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Export DomainOrder.
From PTree.Prob.FreeOmega Require Import Quotient Measure.
Set Implicit Arguments.
Unset Strict Implicit.
Import FreeOmegaOrderNotations.
Local Open Scope freeomega_scope.

Section Iteration.
Context {MN : Type → Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI} `{NO : @SemanticOmega MN NI}.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Context {I A : Type} (K : I → FreeOmega MN (I+A)).
Local Notation step := (sem_iter_step (MI := FI) K).
Local Notation approx := (sem_iter_approx (MI := FI) (MO := FO) K).

Definition free_omega_iter i := FOLub (λ n, approx n i).

Theorem free_omega_iter_spec i :
  sem_iter (MI := FI) (MO := FO) K i (free_omega_iter i).
Proof. apply free_omega_qlift_refl. intro x; reflexivity. Qed.

Theorem free_omega_iter_step_sem_mono X Y :
  (∀ i, X i ⊑ω Y i) → ∀ i, step X i ⊑ω step Y i.
Proof.
  intros H i. apply free_omega_bind_sem_mono_k.
  intros [j|a]; [apply H|apply free_omega_sem_le_refl].
Qed.

Theorem free_omega_iter_approx_prefixed_bound Y :
  (∀ i, step Y i ⊑ω Y i) → ∀ n i, approx n i ⊑ω Y i.
Proof.
  intros H n. induction n as [|n IH]; intro i.
  - apply free_omega_sem_le_bottom.
  - eapply free_omega_sem_le_trans;
      [apply free_omega_iter_step_sem_mono; exact IH|apply H].
Qed.

Theorem free_omega_iter_least_prefixed Y :
  (∀ i, step Y i ⊑ω Y i) → ∀ i, free_omega_iter i ⊑ω Y i.
Proof.
  intros H i. apply free_omega_lub_least.
  - exact (sem_iter_approx_increasing (MI := FI) (MO := FO) K i).
  - intro n. apply free_omega_iter_approx_prefixed_bound, H.
Qed.

(** Selected or quotient-equivalent witnesses have the same leastness. *)
Theorem free_omega_sem_iter_least_prefixed X Y :
  (∀ i, sem_iter (MI := FI) (MO := FO) K i (X i)) →
  (∀ i, step Y i ⊑ω Y i) → ∀ i, X i ⊑ω Y i.
Proof.
  intros HX HY i. eapply free_omega_sem_le_trans;
    [apply free_omega_sem_eq_le; exact (HX i)|apply free_omega_iter_least_prefixed, HY].
Qed.

Context `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}.

Theorem free_omega_iter_fixed_point i :
  free_omega_qlift eq (free_omega_iter i) (step free_omega_iter i).
Proof.
  exact (sem_iter_fixed_point (MI := FI) (MO := FO)
    (λ j, free_omega_iter_spec j) i).
Qed.

Theorem free_omega_iter_least_fixed_point :
  (∀ i, free_omega_qlift eq (free_omega_iter i) (step free_omega_iter i)) ∧
  (∀ Y, (∀ i, step Y i ⊑ω Y i) → ∀ i, free_omega_iter i ⊑ω Y i).
Proof. split; [apply free_omega_iter_fixed_point|apply free_omega_iter_least_prefixed]. Qed.
End Iteration.
