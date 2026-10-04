(** Semantic least-fixed-point rules for complete Ret/Vis frontiers.
    The old structural order and generic summary are unchanged. Ret(inl)
    retries; Ret(inr) and Vis are absorbing results. No event-free signature,
    totality, finite native limit, or external validation is required. *)
From Coq Require Import Utf8.
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega KleisliIteration.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Measure BindOrder IterationOrder.
From PTree.Eq Require Import UnifiedFrontier PTreeKernel.
From PTree.Interp Require Import IterationMachine FrontierIteration ReturnIteration.
From PTree.Interp.FreeOmega Require Import AbsorbingIteration.
Set Implicit Arguments.
Unset Strict Implicit.
Import FreeOmegaOrderNotations.
Local Open Scope freeomega_scope.

Section FrontierOrder.
Context {E MN : Type → Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI} `{NO : @SemanticOmega MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Context {I A : Type} (step : I → ptree E MN (I+A)).
Variable front : I → FreeOmega MN (stable_head E MN (I+A)).

(** Ordinary Kleisli iteration with stable heads as its result type. Visible
    continuations retain the original recursive program, not its summary. *)
Definition free_omega_summary_kernel i :=
  @sem_bind _ FI _ _ (front i) (λ h,
    match h with
    | FHRet (inl j) => sem_ret (inl j)
    | FHRet (inr a) => sem_ret (inr (FHRet a))
    | @FHVis _ _ _ X e k =>
        sem_ret (inr (FHVis e (λ x, iter_active step (k x))))
    end).

Definition free_omega_summary_step X i :=
  @sem_bind _ FI _ _ (front i) (λ h,
    match h with
    | FHRet (inl j) => X j
    | FHRet (inr a) => sem_ret (FHRet a)
    | @FHVis _ _ _ X e k => sem_ret (FHVis e (λ x, iter_active step (k x)))
    end).

Local Notation summary := (complete_iteration_frontier (NI := NI) (NO := NO) step front).

Lemma free_omega_summary_step_kleisli X i :
  @sem_eq _ FI _ (sem_iter_step free_omega_summary_kernel X i)
    (free_omega_summary_step X i).
Proof.
  unfold sem_iter_step, free_omega_summary_kernel, free_omega_summary_step.
  eapply sem_eq_trans; [apply sem_bind_assoc|].
  apply sem_bind_ae_proper; eapply sem_ae_mono; [|apply sem_ae_true].
  intros [[j|a]|Y e k] _;
    exact (sem_bind_ret_l _ (λ next : I + stable_head E MN A,
      match next with inl j => X j | inr a => sem_ret a end)).
Qed.

(** Round zero already contains exits, hence the successor index. *)
Lemma free_omega_summary_round_kleisli n i :
  @sem_eq _ FI _ (iteration_summary_round (FO := FO) step front n i)
    (sem_iter_approx (MO := FO) free_omega_summary_kernel (S n) i).
Proof.
  revert i; induction n as [|n IH]; intro i.
  all: eapply sem_eq_trans;
    [apply (iteration_summary_round_unfold step (FC := _) (FB := _))|].
  all: cbn [sem_iter_approx]; eapply sem_eq_trans;
    [|apply sem_eq_sym; apply free_omega_summary_step_kleisli].
  all: unfold free_omega_summary_step;
    apply sem_bind_ae_proper; eapply sem_ae_mono; [|apply sem_ae_true].
  all: intros [[j|a]|Y e k] _; try apply sem_eq_refl.
  apply IH.
Qed.

Theorem free_omega_summary_spec i :
  iteration_summary (FI := FI) (FO := FO) step front i (summary i).
Proof. apply sem_eq_refl. Qed.

Theorem free_omega_summary_kleisli i out :
  iteration_summary (FI := FI) (FO := FO) step front i out ↔
  sem_iter (MI := FI) (MO := FO) free_omega_summary_kernel i out.
Proof.
  unfold iteration_summary. rewrite sem_iter_lub_shift. split; intro H.
  - eapply sem_lub_chain_proper; [|exact H].
    intro n; apply free_omega_summary_round_kleisli.
  - eapply sem_lub_chain_proper; [|exact H].
    intro n; apply sem_eq_sym, free_omega_summary_round_kleisli.
  all: typeclasses eauto.
Qed.

Theorem free_omega_summary_least_prefixed X Y :
  (∀ i, iteration_summary (FI := FI) (FO := FO) step front i (X i)) →
  (∀ i, free_omega_summary_step Y i ⊑ω Y i) → ∀ i, X i ⊑ω Y i.
Proof.
  intros HX HY. apply (free_omega_sem_iter_least_prefixed (K := free_omega_summary_kernel)).
  - intro i; apply free_omega_summary_kleisli, HX.
  - intro i. eapply free_omega_sem_le_trans;
      [apply free_omega_sem_eq_le, free_omega_summary_step_kleisli|apply HY].
Qed.

Context `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}.

Theorem free_omega_summary_fixed_point X :
  (∀ i, iteration_summary (FI := FI) (FO := FO) step front i (X i)) →
  ∀ i, @sem_eq _ FI _ (X i) (free_omega_summary_step X i).
Proof.
  intros HX i. eapply sem_eq_trans; [|apply free_omega_summary_step_kleisli].
  exact (sem_iter_fixed_point (MI := FI) (MO := FO)
    (λ j, proj1 (free_omega_summary_kleisli j (X j)) (HX j)) i).
Qed.

Theorem free_omega_summary_least_fixed_point :
  (∀ i, @sem_eq _ FI _ (summary i)
    (free_omega_summary_step summary i)) ∧
  (∀ Y, (∀ i, free_omega_summary_step Y i ⊑ω Y i) →
    ∀ i, summary i ⊑ω Y i).
Proof.
  split.
  - apply free_omega_summary_fixed_point, free_omega_summary_spec.
  - intro Y; apply free_omega_summary_least_prefixed, free_omega_summary_spec.
Qed.

(** Only the actual complete-step certificate remains a program obligation.
    Existence/exact hitting is already [complete_iteration_hitting]. *)
Theorem free_omega_summary_hitting_bound
    (Hfront : ∀ i, ptree_stable_hitting (FI := FI) (FO := FO)
      (observe (step i)) (front i)) Y i out :
  (∀ j, free_omega_summary_step Y j ⊑ω Y j) →
  ptree_stable_hitting (FI := FI) (FO := FO) (observe (PTree.iter step i)) out →
  out ⊑ω Y i.
Proof.
  intros HY Hout. eapply free_omega_sem_le_trans.
  - apply free_omega_sem_eq_le.
    exact (iteration_summary_hitting_eq Hfront (free_omega_summary_spec i) Hout).
  - exact (proj2 free_omega_summary_least_fixed_point Y HY i).
Qed.
End FrontierOrder.

Section ReturnOnly.
Context {E MN : Type → Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI} `{NO : @SemanticOmega MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Context {I A : Type} (step : I → ptree E MN (I+A))
  (K : I → FreeOmega MN (I+A)).

Theorem free_omega_summary_return_only i out :
  iteration_summary (FI := FI) (FO := FO) step (iteration_return_front K) i out →
  @sem_eq _ FI _ out (iteration_return_map (free_omega_iter K i)).
Proof.
  intro H. eapply iteration_summary_return_only;
    [exact H|apply free_omega_iter_spec].
Qed.

Theorem free_omega_summary_return_bound i out Y :
  iteration_summary (FI := FI) (FO := FO) step (iteration_return_front K) i out →
  (∀ j, sem_iter_step (MI := FI) K Y j ⊑ω Y j) →
  out ⊑ω iteration_return_map (E := E) (MN := MN) (Y i).
Proof.
  intros H HY. eapply free_omega_sem_le_trans.
  - apply free_omega_sem_eq_le, free_omega_summary_return_only, H.
  - apply free_omega_bind_sem_mono_l, free_omega_iter_least_prefixed, HY.
Qed.

Context `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}.

Theorem free_omega_iter_return_only
    (Hstep : ∀ i, ptree_stable_hitting (FI := FI) (FO := FO)
      (observe (step i)) (iteration_return_front K i)) i :
  ∃ out, ptree_stable_hitting (FI := FI) (FO := FO)
    (observe (PTree.iter step i)) out ∧
    @sem_eq _ FI _ out (iteration_return_map (free_omega_iter K i)).
Proof.
  eapply (ptree_iter_return_only (MO := _) (Diagonal := _) (Fubini := _));
    [exact Hstep|apply free_omega_iter_spec].
Qed.
End ReturnOnly.
