Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
From Coq Require Import FunctionalExtensionality.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure.
From PTree.Eq Require Import FiniteInternal PrimitiveStableHitting
  UnifiedFrontier PTreeKernel FiniteInternalHitting.
From PTree.Eq.FreeOmega Require Import FiniteInternalJoint KernelCompletion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CompleteMarginal.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
  `{NO : @SemanticOmega MN NI} {A : Type}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation tree := (ptree E MN A).
Local Notation head := (stable_head E MN A).
Local Notation Hitting := (@ptree_stable_hitting E MN MF FI
  FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega A).

Variable front : tree -> MF head.
Hypothesis front_hitting : forall t, Hitting (observe t) (front t).

Definition finite_internal_guard_complete (target : stable_target tree head) : MF head :=
  match target with
  | SHStable h => FORet h
  | SHInternal t => front t
  end.

Lemma finite_internal_guard_complete_hitting t :
  Hitting (observe t)
    (free_omega_bind (finite_internal_guard_transition t)
      finite_internal_guard_complete).
Proof.
  unfold finite_internal_guard_transition. destruct (observe t);
    cbn [free_omega_bind finite_internal_guard_complete].
  - apply (ptree_stable_hitting_ret (FI := FI)
      (MX := FreeOmegaMixedMeasure) (FO := FreeOmegaObservableSemanticOmega)).
  - apply (proj2 (ptree_stable_hitting_tau_iff (FI := FI)
      (MX := FreeOmegaMixedMeasure) (FO := FreeOmegaObservableSemanticOmega) _ _)).
    apply front_hitting.
  - apply (ptree_stable_hitting_vis (FI := FI)
      (MX := FreeOmegaMixedMeasure) (FO := FreeOmegaObservableSemanticOmega)).
  - apply (ptree_stable_hitting_prob (FI := FI)
      (MX := FreeOmegaMixedMeasure) (FO := FreeOmegaObservableSemanticOmega))
      with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros x _. apply front_hitting.
Qed.

Lemma finite_internal_guard_complete_eq t :
  free_omega_qlift eq
    (free_omega_bind (finite_internal_guard_transition t)
      finite_internal_guard_complete) (front t).
Proof.
  eapply (ptree_stable_hitting_unique (FI := FI)
    (MX := FreeOmegaMixedMeasure) (FO := FreeOmegaObservableSemanticOmega));
    [apply finite_internal_guard_complete_hitting|apply front_hitting].
Qed.

(** A realized macro round preserves the original complete hitting when
    each of its residuals is completed.  The source [joint] may live on
    PAIRS or richer correlated state: only its projected marginal is used.
    This is a probability-preservation result, not merely an AE invariant.
    It is still a one-round equation, not an omega acceleration theorem. *)
Theorem finite_internal_realized_round_hitting {Z}
    (joint : MF Z) (project : Z -> stable_target tree head)
    t (cut : MF tree) :
  @finite_internal E MN MF FI FreeOmegaMixedMeasure A t cut ->
  free_omega_qlift (fun z target => project z = target)
    joint (free_omega_bind cut finite_internal_guard_transition) ->
  free_omega_qlift eq
    (free_omega_bind joint (fun z => finite_internal_guard_complete (project z)))
    (front t).
Proof.
  intros Hcut Hproject.
  eapply FOQLComp with (T := eq) (U := eq)
    (mid := free_omega_bind
      (free_omega_bind cut finite_internal_guard_transition)
      finite_internal_guard_complete).
  - eapply FOQLBind; [exact Hproject|].
    intros z target <-. apply free_omega_qlift_refl. intro h. reflexivity.
  - rewrite free_omega_bind_assoc.
    eapply FOQLComp with (T := eq) (U := eq) (mid := free_omega_bind cut front).
    + eapply FOQLBind with (T := eq).
      * apply free_omega_qlift_refl. intro x. reflexivity.
      * intros x y ->. apply finite_internal_guard_complete_eq.
    + apply FOQLMono with (T := fun x y => y = x).
      * apply FOQLSym.
        exact (finite_internal_hitting_lift (FI := FI) Hcut front_hitting
          (front_hitting t)).
      * intros x y Hxy. symmetry. exact Hxy.
    + intros x z [y [-> ->]]. reflexivity.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

Section CorrelatedExecution.
Context {S O : Type}.
Variable kernel : S -> MF (stable_target S O).
Variable project_state : S -> tree.
Variable project_output : O -> head.
Variable D : S -> Prop.
Variable cut : S -> MF tree.

Definition finite_internal_execution_projection (target : stable_target S O) :=
  match target with
  | SHStable o => SHStable (project_output o)
  | SHInternal s => SHInternal (project_state s)
  end.

Hypothesis execution_closed : forall s, D s ->
  free_omega_ae (kernel_completion_invariant D) (kernel s).
Hypothesis cut_valid : forall s, D s ->
  @finite_internal E MN MF FI FreeOmegaMixedMeasure A (project_state s) (cut s).
Hypothesis execution_marginal : forall s, D s ->
  free_omega_qlift (fun z target => finite_internal_execution_projection z = target)
    (kernel s) (free_omega_bind (cut s) finite_internal_guard_transition).

(** Upper half of correlated acceleration adequacy, for actual valid cuts.
    A state can contain both trees or extra execution history; neither the
    cut nor the choice of the next state must factor through project_state.
    The explicit [upper] avoids assuming raw order is quotient-proper. *)
Theorem finite_internal_execution_hitting_upper s : D s ->
  exists upper,
    free_omega_approx eq
      (free_omega_bind
        (FOLub (fun n => @stable_hitting_approx MF FI
          FreeOmegaObservableSemanticOmega S O kernel n s))
        (fun o => FORet (project_output o))) upper /\
    free_omega_qlift eq upper (front (project_state s)).
Proof.
  intro HD. eapply kernel_hitting_limit_upper with
    (D := D) (tail := fun s => front (project_state s)).
  - exact execution_closed.
  - intros s' HD'.
    assert (Hresolve :
      kernel_completion_resolve project_output (fun s => front (project_state s)) =
      (fun z => finite_internal_guard_complete (finite_internal_execution_projection z))).
    { apply functional_extensionality. intros [o|state]; reflexivity. }
    cbn [kernel_completion]. rewrite Hresolve.
    eapply finite_internal_realized_round_hitting.
    + apply cut_valid. exact HD'.
    + apply execution_marginal. exact HD'.
  - exact HD.
Qed.

End CorrelatedExecution.

End CompleteMarginal.
