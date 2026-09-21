(** Role: Internal execution/scheduling proof infrastructure. Supports hitting adequacy; not an additional behavioral equivalence. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
From Coq Require Import FunctionalExtensionality.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq.Internal Require Import FiniteInternal.
From PTree.Eq Require Import PrimitiveStableHitting UnifiedFrontier PTreeKernel.
From PTree.Eq.Internal.FreeOmega Require Import FiniteInternal FiniteInternalJoint FiniteInternalAcceleration KernelCompletion KernelProjection.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A quotient graph marginal, not a structural reference, suffices if
    this marginal's selected cut depends only on its projected tree.
    The execution state may still contain a correlated partner/history.
    The other marginal is not required to have such a policy. *)
Section ProjectedPolicy.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
  `{NO : @SemanticOmega MN NI} {A S O : Type}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation tree := (ptree E MN A).
Local Notation head := (stable_head E MN A).
Variable kernel : S -> MF (stable_target S O).
Variable project_state : S -> tree.
Variable project_output : O -> head.
Variable D : S -> Prop.
Variable policy : tree -> MF tree.
Hypothesis policy_valid : forall t,
  @finite_internal E MN MF FI FreeOmegaMixedMeasure A t (policy t).
Hypothesis kernel_closed : forall s, D s ->
  free_omega_ae (kernel_completion_invariant D) (kernel s).
Hypothesis kernel_marginal : forall s, D s ->
  free_omega_qlift
    (fun z target => kernel_target_projection project_state project_output z = target)
    (kernel s) (free_omega_bind (policy (project_state s)) finite_internal_guard_transition).

Theorem finite_internal_projected_policy_adequate s out original : D s ->
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega S O kernel s out ->
  @ptree_stable_hitting E MN MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A (observe (project_state s)) original ->
  free_omega_qlift eq (free_omega_bind out (fun o => FORet (project_output o))) original.
Proof.
  intros HD Hout Horiginal.
  pose (macro := finite_internal_round_kernel policy).
  pose (macro_out := FOLub (fun n => @stable_hitting_approx MF FI
    FreeOmegaObservableSemanticOmega tree head macro n (project_state s))).
  assert (Hproject : free_omega_qlift eq
    (free_omega_bind out (fun o => FORet (project_output o))) macro_out).
  { eapply kernel_stable_hitting_projection with
      (state_projection := project_state) (D := D) (target := macro) (s := s).
    - exact kernel_closed.
    - exact kernel_marginal.
    - exact HD.
    - exact Hout.
    - apply free_omega_qlift_refl. intro h. reflexivity. }
  pose proof (finite_internal_acceleration policy_valid (project_state s)) as Hacc.
  assert (Hrounds : (fun n => finite_internal_rounds policy n (project_state s)) =
    (fun n => @stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
      tree head macro n (project_state s))).
  { apply functional_extensionality. intro n. apply finite_internal_rounds_kernelE. }
  rewrite Hrounds in Hacc.
  eapply FOQLComp with (T := eq) (U := eq); [exact Hproject| |].
  - eapply FOQLComp with (T := eq) (U := eq); [exact Hacc| |].
    + apply FOQLMono with (T := fun x y => y = x).
      * apply FOQLSym. exact Horiginal.
      * intros x y Heq. symmetry. exact Heq.
    + intros x z [y [-> ->]]. reflexivity.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

End ProjectedPolicy.
