(** Role: Internal execution/scheduling proof infrastructure. Supports hitting adequacy; not an additional behavioral equivalence. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
From Coq.Arith Require Import PeanoNat.
From Coq Require Import Lia.
From Coq.Logic Require Import ClassicalChoice.
From Coq Require Import FunctionalExtensionality.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed PTree.Prob.Interface.SemanticCoupling.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq.Internal Require Import FiniteInternal.
From PTree.Eq Require Import PrimitiveStableHitting UnifiedFrontier PTreeKernel.
From PTree.Eq.Internal.FreeOmega Require Import FiniteInternalJoint FiniteInternalJointHitting FiniteInternalJointCoverage FiniteInternalJointTruncation KernelCompletion KernelContinuity KernelCongruence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CorrelatedAcceleration.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
  `{NO : @SemanticOmega MN NI} {A S O : Type}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation tree := (ptree E MN A).
Local Notation head := (stable_head E MN A).
Local Notation hit := (@ptree_hitting_approx E MN MF FI
  FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega A).
Local Notation target_approx :=
  (@stable_target_approx MF FI FreeOmegaObservableSemanticOmega S O).
Local Notation kernel_hit :=
  (@stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega S O).
Local Notation guard_approx := (@finite_internal_guard_approx E MN NI NO A).

Variable kernel : S -> MF (stable_target S O).
Variable project_state : S -> tree.
Variable project_output : O -> head.
Variable D : S -> Prop.
Local Notation projection := (finite_internal_execution_projection project_state project_output).
Hypothesis kernel_closed : forall s, D s ->
  free_omega_ae (kernel_completion_invariant D) (kernel s).

Section TruncationGrid.
Variable trunc : S -> nat -> MF (stable_target S O).
Hypothesis trunc_increasing : forall n s,
  free_omega_approx eq (trunc s n) (trunc s (Datatypes.S n)).
Hypothesis trunc_limit : forall s, free_omega_qlift eq (kernel s) (FOLub (trunc s)).
Hypothesis trunc_spec : forall s, D s ->
  finite_internal_joint_approximates projection (project_state s) (kernel s) (trunc s).

Definition finite_internal_joint_grid n m s :=
  free_omega_bind (kernel_hit (fun u => trunc u m) n s)
    (fun o => FORet (project_output o)).

Lemma finite_internal_trunc_closed s m : D s ->
  free_omega_ae (kernel_completion_invariant D) (trunc s m).
Proof.
  intro HD. eapply free_omega_ae_mono with
    (P := fun x => exists y, x = y /\ kernel_completion_invariant D y).
  - intros x [y [-> Hy]]. exact Hy.
  - eapply free_omega_approx_ae_backward.
    + exact (proj1 (proj2 (proj2 (trunc_spec HD))) m).
    + apply kernel_closed. exact HD.
Qed.

Lemma finite_internal_trunc_supported s m : D s ->
  free_omega_approx (fun x y => x = y /\ kernel_completion_invariant D x)
    (trunc s m) (trunc s m).
Proof.
  intro HD. apply free_omega_lift_to_approx. eapply free_omega_lift_mono with
    (R := fun x y => x = y /\ kernel_completion_invariant D x /\ True).
  - intros x y [Hxy [HD' _]]. split; assumption.
  - eapply free_omega_lift_ae_restrict.
    + apply free_omega_lift_refl. intro x. reflexivity.
    + apply finite_internal_trunc_closed. exact HD.
    + apply (@sem_ae_true MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
Qed.

Lemma finite_internal_trunc_mono_on_state s n m : n <= m ->
  free_omega_approx eq (trunc s n) (trunc s m).
Proof.
  intro Hnm. induction Hnm.
  - apply free_omega_approx_refl. intro x. reflexivity.
  - eapply free_omega_approx_trans; [exact IHHnm|apply trunc_increasing].
Qed.

Lemma finite_internal_joint_gridE n m s :
  finite_internal_joint_grid n m s = free_omega_bind (trunc s m)
    (fun target => free_omega_bind (target_approx (fun u => trunc u m) n target)
      (fun o => FORet (project_output o))).
Proof. apply free_omega_bind_assoc. Qed.

Lemma finite_internal_joint_grid_upper n m s : D s ->
  free_omega_approx eq (finite_internal_joint_grid n m s)
    (hit ((Datatypes.S n) * (Datatypes.S m)) (observe (project_state s))).
Proof.
  induction n as [|n IH] in s |- *; intro HD.
  - eapply free_omega_approx_trans with
      (nu := free_omega_bind (trunc s m) (fun z => guard_approx 0 (projection z))).
    + rewrite finite_internal_joint_gridE.
      eapply free_omega_approx_bind with (R := eq).
      * apply free_omega_approx_refl. intro z. reflexivity.
      * intros z w ->. destruct w; [apply FOApproxRet; reflexivity|apply FOApproxZero].
    + eapply free_omega_approx_trans.
      * exact (proj1 (proj2 (proj2 (proj2 (trunc_spec HD)))) m 0).
      * apply (@PTreeKernel.ptree_hitting_mono E MN MF FI FreeOmegaMixedMeasure
          FreeOmegaObservableSemanticOmega FreeOmegaObservableSemanticMeasureOrderLaws A). lia.
  - eapply free_omega_approx_trans with
      (nu := free_omega_bind (trunc s m)
        (fun z => guard_approx (Datatypes.S ((Datatypes.S n) * (Datatypes.S m)))
          (projection z))).
    + rewrite finite_internal_joint_gridE.
      eapply free_omega_approx_bind; [apply finite_internal_trunc_supported; exact HD|].
      intros z w [<- Hgood]. destruct z as [o|s'].
      * apply FOApproxRet. reflexivity.
      * apply IH. exact Hgood.
    + eapply free_omega_approx_trans.
      * exact (proj1 (proj2 (proj2 (proj2 (trunc_spec HD))))
          m (Datatypes.S ((Datatypes.S n) * (Datatypes.S m)))).
      * apply (@PTreeKernel.ptree_hitting_mono E MN MF FI FreeOmegaMixedMeasure
          FreeOmegaObservableSemanticOmega FreeOmegaObservableSemanticMeasureOrderLaws A). lia.
Qed.

Lemma finite_internal_joint_grid_covers n m s : D s -> n <= m ->
  free_omega_approx eq (hit n (observe (project_state s)))
    (finite_internal_joint_grid n m s).
Proof.
  induction n as [|n IH] in s |- *; intros HD Hnm;
    eapply free_omega_approx_trans with
      (nu := free_omega_bind (trunc s m) (fun z => guard_approx _ (projection z))).
  - eapply free_omega_approx_trans.
    + exact (proj2 (proj2 (proj2 (proj2 (trunc_spec HD)))) 0).
    + eapply free_omega_approx_bind with (R := eq).
      * apply finite_internal_trunc_mono_on_state. exact Hnm.
      * intros z w ->. apply free_omega_approx_refl. intro h. reflexivity.
  - rewrite finite_internal_joint_gridE.
    eapply free_omega_approx_bind with (R := eq).
    + apply free_omega_approx_refl. intro z. reflexivity.
    + intros z w ->. destruct w; [apply FOApproxRet; reflexivity|apply FOApproxZero].
  - eapply free_omega_approx_trans.
    + exact (proj2 (proj2 (proj2 (proj2 (trunc_spec HD)))) (Datatypes.S n)).
    + eapply free_omega_approx_bind with (R := eq).
      * apply finite_internal_trunc_mono_on_state. exact Hnm.
      * intros z w ->. apply free_omega_approx_refl. intro h. reflexivity.
  - rewrite finite_internal_joint_gridE.
    eapply free_omega_approx_bind; [apply finite_internal_trunc_supported; exact HD|].
    intros z w [<- Hgood]. destruct z as [o|s'].
    + apply FOApproxRet. reflexivity.
    + apply IH; [exact Hgood|lia].
Qed.

Theorem finite_internal_joint_grid_cofinal s : D s ->
  free_omega_chains_cofinal eq (fun n => finite_internal_joint_grid n n s)
    (fun n => hit n (observe (project_state s))).
Proof.
  intro HD. split.
  - intro n. exists ((Datatypes.S n) * (Datatypes.S n)).
    apply finite_internal_joint_grid_upper. exact HD.
  - intro n. exists n. eapply free_omega_approx_mono with (R := eq).
    + intros x y ->. reflexivity.
    + apply finite_internal_joint_grid_covers; [exact HD|reflexivity].
Qed.

Theorem finite_internal_joint_truncated_execution_adequate s out reference_out :
  D s ->
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega S O kernel s out ->
  @ptree_stable_hitting E MN MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A (observe (project_state s)) reference_out ->
  free_omega_qlift eq
    (free_omega_bind out (fun o => FORet (project_output o))) reference_out.
Proof.
  intros HD Hhit Hreference.
  eapply (kernel_stable_hitting_diagonal_adequate trunc_increasing trunc_limit
    (reference := @ptree_primitive_kernel E MN MF FI FreeOmegaMixedMeasure A))
    with (s := s) (r := observe (project_state s)).
  - exact Hhit.
  - exact Hreference.
  - apply finite_internal_joint_grid_cofinal. exact HD.
Qed.

End TruncationGrid.

Variable cut : S -> MF tree.
Hypothesis cut_valid : forall s, D s ->
  @finite_internal E MN MF FI FreeOmegaMixedMeasure A (project_state s) (cut s).
Hypothesis marginal_structural : forall s, D s ->
  free_omega_lift (fun z target => projection z = target)
    (kernel s) (free_omega_bind (cut s) finite_internal_guard_transition).
Hypothesis node_realizes : forall {X Y} (R : X -> Y -> Prop)
    (mu : MN X) (nu : MN Y), sem_lift R mu nu ->
    exists joint, semantic_coupling R mu nu joint.

(** Choice is over complete states, which may include BOTH programs and
    their history.  Off the invariant domain use a constant chain, so the
    global kernel-continuity premises also hold there. *)
Theorem finite_internal_structural_execution_truncations :
  exists trunc : S -> nat -> MF (stable_target S O),
    (forall n s, free_omega_approx eq (trunc s n) (trunc s (Datatypes.S n))) /\
    (forall s, free_omega_qlift eq (kernel s) (FOLub (trunc s))) /\
    (forall s, D s -> finite_internal_joint_approximates
      projection (project_state s) (kernel s) (trunc s)).
Proof.
  assert (Hex : forall s, exists c : nat -> MF (stable_target S O),
    (forall n, free_omega_approx eq (c n) (c (Datatypes.S n))) /\
    free_omega_qlift eq (kernel s) (FOLub c) /\
    (D s -> finite_internal_joint_approximates projection (project_state s) (kernel s) c)).
  { intro s. destruct (classic (D s)) as [HD|Hnot].
    - destruct (finite_internal_joint_approximation_exists (project := projection) (@node_realizes)
        (cut_valid HD) (free_omega_lift_sym (marginal_structural HD))) as [c Hc].
      exists c. split; [exact (proj1 Hc)|].
      split; [exact (proj1 (proj2 Hc))|]. intros _. exact Hc.
    - exists (fun _ => kernel s). split.
      + intro n. apply free_omega_approx_refl. intro z. reflexivity.
      + split.
        * apply FOQLLubConstantR, free_omega_qlift_refl. intro z. reflexivity.
        * intro HD. contradiction. }
  destruct (choice _ Hex) as [trunc Htrunc]. exists trunc. split.
  - intros n s. exact (proj1 (Htrunc s) n).
  - split.
    + intro s. exact (proj1 (proj2 (Htrunc s))).
    + intros s HD. exact (proj2 (proj2 (Htrunc s)) HD).
Qed.

(** Full correlated acceleration adequacy for structurally realized round
    marginals.  Cuts need not be unary policies or uniformly bounded, and
    execution need not encounter Vis or terminate almost surely.  The
    structural qualification is not inferred for arbitrary quotient rounds. *)
Theorem finite_internal_structural_execution_adequate s out reference_out :
  D s ->
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega S O kernel s out ->
  @ptree_stable_hitting E MN MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A (observe (project_state s)) reference_out ->
  free_omega_qlift eq
    (free_omega_bind out (fun o => FORet (project_output o))) reference_out.
Proof.
  intros HD Hhit Hreference.
  destruct finite_internal_structural_execution_truncations as [trunc [Hinc [Hlim Hspec]]].
  exact (finite_internal_joint_truncated_execution_adequate
    Hinc Hlim Hspec HD Hhit Hreference).
Qed.

(** A quotient rewrite of the execution kernel inherits complete adequacy
    from a structurally realized reference.  This does not require raw
    coverage of the rewritten representation, which can be false. *)
Theorem finite_internal_structural_execution_adequate_modulo_eq
    (represented : S -> MF (stable_target S O))
    (kernels_equal : forall s, D s -> free_omega_qlift eq (kernel s) (represented s))
    s out reference_out :
  D s ->
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega S O represented s out ->
  @ptree_stable_hitting E MN MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A (observe (project_state s)) reference_out ->
  free_omega_qlift eq
    (free_omega_bind out (fun o => FORet (project_output o))) reference_out.
Proof.
  intros HD Hout Hreference.
  pose (front := FOLub (fun n => kernel_hit kernel n s)).
  assert (Hfront : @stable_hitting MF FI FreeOmegaObservableSemanticOmega S O kernel s front).
  { apply free_omega_qlift_refl. intro o. reflexivity. }
  pose proof (kernel_stable_hitting_eq kernel_closed kernels_equal HD Hfront Hout) as Heq.
  eapply FOQLComp with (T := eq) (U := eq)
    (mid := free_omega_bind front (fun o => FORet (project_output o))).
  - eapply FOQLBind with (T := fun x y => y = x).
    + apply FOQLSym. exact Heq.
    + intros x y <-. apply FOQLStructural, FOLRet. reflexivity.
  - eapply finite_internal_structural_execution_adequate;
      [exact HD|exact Hfront|exact Hreference].
  - intros x z [y [-> ->]]. reflexivity.
Qed.

End CorrelatedAcceleration.
