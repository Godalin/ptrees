(** Role: Internal execution/scheduling proof infrastructure. Supports hitting adequacy; not an additional behavioral equivalence. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
From Coq Require Import FunctionalExtensionality.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.
From PTree.Eq.Internal Require Import FiniteInternal.
From PTree.Eq Require Import PrimitiveStableHitting UnifiedFrontier PTreeKernel.
From PTree.Eq.Internal.FreeOmega Require Import FiniteInternal FiniteInternalJoint FiniteInternalJointHitting KernelCompletion KernelCongruence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CorrelatedCoverage.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NO : @SemanticOmega MN NI} {A S O : Type}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation tree := (ptree E MN A).
Local Notation head := (stable_head E MN A).
Local Notation hit := (@ptree_hitting_approx E MN MF FI
  FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega A).

Definition finite_internal_guard_approx n (target : stable_target tree head) : MF head :=
  match target with
  | SHStable h => FORet h
  | SHInternal t =>
      match n with 0 => FOZero | Datatypes.S m => hit m (observe t) end
  end.

Lemma finite_internal_guard_approxE n t :
  hit n (observe t) =
  free_omega_bind (finite_internal_guard_transition t) (finite_internal_guard_approx n).
Proof. unfold finite_internal_guard_transition. destruct (observe t), n; reflexivity. Qed.

Lemma finite_internal_cut_guard_approxE n (cut : MF tree) :
  free_omega_bind cut (fun t => hit n (observe t)) =
  free_omega_bind (free_omega_bind cut finite_internal_guard_transition)
    (finite_internal_guard_approx n).
Proof.
  rewrite free_omega_bind_assoc. f_equal.
  apply functional_extensionality. intro t. apply finite_internal_guard_approxE.
Qed.

Variable kernel : S -> MF (stable_target S O).
Variable project_state : S -> tree.
Variable project_output : O -> head.
Variable D : S -> Prop.
Variable cut : S -> MF tree.
Local Notation projection := (finite_internal_execution_projection project_state project_output).
Hypothesis execution_closed : forall s, D s ->
  free_omega_ae (kernel_completion_invariant D) (kernel s).
Hypothesis cut_valid : forall s, D s ->
  @finite_internal E MN MF FI FreeOmegaMixedMeasure A (project_state s) (cut s).

(** This stronger realization premise is intentional and VISIBLE.  A
    quotient graph coupling alone cannot be transported through the raw
    approximation order. This realization premise is supplied separately;
    it does not alter the canonical behavioral relation. *)
Hypothesis execution_marginal_structural : forall s, D s ->
  free_omega_lift (fun z target => projection z = target)
    (kernel s) (free_omega_bind (cut s) finite_internal_guard_transition).

Lemma finite_internal_joint_hitting_projectionE n s :
  free_omega_bind
    (@stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega S O kernel n s)
    (fun o => FORet (project_output o)) =
  free_omega_bind (kernel s) (fun target => free_omega_bind
    (@stable_target_approx MF FI FreeOmegaObservableSemanticOmega S O kernel n target)
    (fun o => FORet (project_output o))).
Proof. apply free_omega_bind_assoc. Qed.

Lemma finite_internal_marginal_structural_supported s : D s ->
  free_omega_lift
    (fun target z => projection z = target /\ kernel_completion_invariant D z)
    (free_omega_bind (cut s) finite_internal_guard_transition) (kernel s).
Proof.
  intro HD. eapply free_omega_lift_mono with
    (R := fun target z => projection z = target /\
      kernel_completion_invariant D z /\ True).
  - intros target z [Hproj [HD' _]]. split; assumption.
  - apply free_omega_lift_sym. eapply free_omega_lift_ae_restrict.
    + apply execution_marginal_structural. exact HD.
    + apply execution_closed. exact HD.
    + apply (@sem_ae_true MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
Qed.

(** Every round that continues internally spends a primitive internal step;
    a stable round emits its observation immediately.  Hence the same fuel
    index suffices for coverage: both approximants execute their first
    kernel step and allow n further residual transitions.  Cuts and future
    states may depend on both programs or on extra history. *)
Theorem finite_internal_execution_covers_hitting n s : D s ->
  free_omega_approx eq (hit n (observe (project_state s)))
    (free_omega_bind
      (@stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega S O kernel n s)
      (fun o => FORet (project_output o))).
Proof.
  induction n as [|n IH] in s |- *; intro HD;
    eapply free_omega_approx_trans.
  all: try exact (finite_internal_hitting_covered (cut_valid HD) _).
  all: rewrite finite_internal_cut_guard_approxE.
  all: rewrite finite_internal_joint_hitting_projectionE.
  all: eapply free_omega_approx_bind.
  1,3: apply free_omega_lift_to_approx;
    apply finite_internal_marginal_structural_supported; exact HD.
  - intros target z [<- Hgood]. destruct z as [o|state];
      [apply FOApproxRet; reflexivity|apply FOApproxZero].
  - intros target z [<- Hgood]. destruct z as [o|state].
    + apply FOApproxRet. reflexivity.
    + apply IH. exact Hgood.
Qed.

Corollary finite_internal_execution_limit_covers s : D s ->
  free_omega_approx eq
    (FOLub (fun n => hit n (observe (project_state s))))
    (free_omega_bind
      (FOLub (fun n => @stable_hitting_approx MF FI
        FreeOmegaObservableSemanticOmega S O kernel n s))
      (fun o => FORet (project_output o))).
Proof.
  intro HD. apply FOApproxLub. intro n.
  apply finite_internal_execution_covers_hitting. exact HD.
Qed.

Variable represented_kernel : S -> MF (stable_target S O).
Hypothesis kernels_equal : forall s, D s ->
  free_omega_qlift eq (kernel s) (represented_kernel s).

(** Representation-independent coverage for an equivalent presentation of
    a structurally realized kernel.  The raw inequality ends at an explicit
    representative; the second conjunct relates it to the requested one.
    An arbitrary quotient kernel is NOT assumed to have such a structural
    presentation. *)
Theorem finite_internal_execution_covers_modulo_eq n s : D s ->
  exists covered,
    free_omega_approx eq (hit n (observe (project_state s))) covered /\
    free_omega_qlift eq covered
      (free_omega_bind
        (@stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
          S O represented_kernel n s) (fun o => FORet (project_output o))).
Proof.
  intro HD. exists (free_omega_bind
    (@stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega S O kernel n s)
    (fun o => FORet (project_output o))). split.
  - apply finite_internal_execution_covers_hitting. exact HD.
  - eapply FOQLBind with (T := eq).
    + eapply (kernel_hitting_approx_eq (NI := NI) (NO := NO)) with (D := D).
      * exact execution_closed.
      * exact kernels_equal.
      * exact HD.
    + intros x y ->. apply FOQLStructural, FOLRet. reflexivity.
Qed.

(** The complete witness comes from one fixed reference kernel, not from
    an unproved monotone selection of the finite existential witnesses. *)
Theorem finite_internal_execution_limit_covers_modulo_eq s : D s ->
  exists covered,
    free_omega_approx eq
      (FOLub (fun n => hit n (observe (project_state s)))) covered /\
    free_omega_qlift eq covered
      (free_omega_bind
        (FOLub (fun n => @stable_hitting_approx MF FI
          FreeOmegaObservableSemanticOmega S O represented_kernel n s))
        (fun o => FORet (project_output o))).
Proof.
  intro HD. exists (free_omega_bind
    (FOLub (fun n => @stable_hitting_approx MF FI
      FreeOmegaObservableSemanticOmega S O kernel n s))
    (fun o => FORet (project_output o))). split.
  - apply finite_internal_execution_limit_covers. exact HD.
  - eapply FOQLBind with (T := eq).
    + eapply (kernel_hitting_limit_eq (NI := NI) (NO := NO)) with (D := D).
      * exact execution_closed.
      * exact kernels_equal.
      * exact HD.
    + intros x y ->. apply FOQLStructural, FOLRet. reflexivity.
Qed.

End CorrelatedCoverage.
