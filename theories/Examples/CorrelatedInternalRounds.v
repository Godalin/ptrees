Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
From Coq Require Import Program.Equality.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureEnum
  TwoLevelMeasureSubEnum DiscreteMC SemanticCoupling SemanticCouplingEnum
  FreeOmegaMeasure FreeOmegaCouplingEnum.
From PTree.Eq Require Import PrimitiveStableHitting UnifiedFrontier PFiniteResidual PTreeKernel.
From PTree.Eq.FreeOmega Require Import FiniteInternalJoint FiniteInternalJointHitting.
From PTree.Examples Require Import PairedFiniteCompression ResidualFinite.
Import Enum.
Set Implicit Arguments.

Module CorrelatedCompressionRounds.
Import PairedCompression.
Local Notation tree := (ptree event Enum bool).
Local Notation Pair := (tree * tree)%type.
Local Notation Heads := (stable_head event Enum bool * stable_head event Enum bool)%type.
Local Notation MF := (FreeOmega Enum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := Enum_SemanticMeasure) (NO := Enum_SemanticOmega)).

Definition round_spec (kernel : Pair -> MF (stable_target Pair Heads)) :=
  forall t u, candidate t u ->
    free_omega_qlift (fun z x => finite_internal_pair_left z = x)
      (kernel (t,u)) (free_omega_bind (left_cut (t,u)) finite_internal_guard_transition) /\
    free_omega_qlift (fun z y => finite_internal_pair_right z = y)
      (kernel (t,u)) (free_omega_bind (right_cut (t,u)) finite_internal_guard_transition) /\
    free_omega_ae (finite_internal_pair_invariant eq candidate) (kernel (t,u)).

(** This is the actual partner-dependent cut from PairedFiniteCompression,
    whose correlated marginal cannot be represented by any unary cut. *)
Example correlated_round_kernel_exists : exists kernel, round_spec kernel.
Proof.
  unfold round_spec. eapply finite_internal_paired_kernel_exists.
  - exact (@enum_coupling_realization).
  - intros t u Htu. exists (residual_joint (t,u)). split.
    + apply FOQLStructural, FOLRet. reflexivity.
    + split.
      * apply FOQLStructural, FOLRet. reflexivity.
      * apply FOAERet. exact (partner_guarded Htu).
Qed.

(** Support closure alone would accept an always-zero kernel.  The actual
    round certificate must also preserve the marginal transition, so it
    cannot erase an already-returning pair in that way. *)
Example zero_kernel_not_a_correlated_round : ~ round_spec (fun _ => FOZero).
Proof.
  intro Hkernel. destruct (Hkernel done done candidate_done) as [Hleft _].
  pose proof (proj1 (free_omega_qlift_support Hleft)) as Hsupport.
  assert (Hzero : @free_omega_ae Enum Enum_SemanticMeasure _
    (fun _ => False) (FOZero : MF (stable_target Pair Heads))).
  { apply FOAEZero. }
  specialize (Hsupport _ Hzero). cbn in Hsupport.
  dependent destruction Hsupport. destruct H as [z [_ Hfalse]]. exact Hfalse.
Qed.

(** Completing the true correlated round preserves the full ORIGINAL
    marginal distribution, not just the relation on paired outputs. *)
Example correlated_round_left_completed kernel (Hkernel : round_spec kernel)
    (front : tree -> MF (stable_head event Enum bool))
    (Hfront : forall t, @ptree_stable_hitting event Enum MF FI
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool
      (observe t) (front t)) t u : candidate t u ->
  free_omega_qlift eq
    (free_omega_bind (kernel (t,u))
      (fun z => finite_internal_guard_complete front (finite_internal_pair_left z)))
    (front t).
Proof.
  intro Htu. eapply finite_internal_realized_round_hitting
    with (cut := left_cut (t,u)).
  - exact Hfront.
  - exact (left_cut_valid Htu).
  - exact (proj1 (Hkernel t u Htu)).
Qed.

Example correlated_round_right_completed kernel (Hkernel : round_spec kernel)
    (front : tree -> MF (stable_head event Enum bool))
    (Hfront : forall t, @ptree_stable_hitting event Enum MF FI
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool
      (observe t) (front t)) t u : candidate t u ->
  free_omega_qlift eq
    (free_omega_bind (kernel (t,u))
      (fun z => finite_internal_guard_complete front (finite_internal_pair_right z)))
    (front u).
Proof.
  intro Htu. eapply finite_internal_realized_round_hitting
    with (cut := right_cut (t,u)).
  - exact Hfront.
  - exact (right_cut_valid Htu).
  - exact (proj1 (proj2 (Hkernel t u Htu))).
Qed.

Example correlated_round_complete_coupling kernel
    (Hkernel : round_spec kernel) t u : candidate t u ->
  exists out, @stable_hitting MF FI FreeOmegaObservableSemanticOmega
    Pair Heads kernel (t,u) out /\
    free_omega_qlift (stable_head_rel eq candidate)
      (free_omega_bind out (fun p => FORet (fst p)))
      (free_omega_bind out (fun p => FORet (snd p))).
Proof.
  intro Htu. destruct (@stable_hitting_exists MF FI
    FreeOmegaObservableSemanticOmega FreeOmegaObservableSemanticMeasureOrderLaws
    FreeOmegaObservableSemanticOmegaLaws Pair Heads kernel (t,u)) as [out Hout].
  exists out. split; [exact Hout|].
  apply (proj2 (@finite_internal_paired_hitting_coupled event Enum
    Enum_SemanticMeasure Enum_SemanticMeasureCoreLaws
    Enum_SemanticMeasureCouplingAELaws Enum_SemanticMeasureCountableAELaws
    Enum_SemanticOmega bool bool eq candidate kernel
    (fun x y Hxy => proj2 (proj2 (Hkernel x y Hxy))) t u out Htu Hout)).
Qed.
End CorrelatedCompressionRounds.

Module InternalRetryRounds.
Local Notation tree := (ptree residualE SubEnum bool).
Local Notation Pair := (tree * tree)%type.
Local Notation Heads :=
  (stable_head residualE SubEnum bool * stable_head residualE SubEnum bool)%type.
Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).

Definition round_spec (kernel : Pair -> MF (stable_target Pair Heads)) :=
  forall t u, residual_retry_pairs t u ->
    free_omega_qlift (fun z x => finite_internal_pair_left z = x)
      (kernel (t,u))
      (free_omega_bind (residual_retry_cut1 t) finite_internal_guard_transition) /\
    free_omega_qlift (fun z y => finite_internal_pair_right z = y)
      (kernel (t,u))
      (free_omega_bind (residual_retry_cut2 u) finite_internal_guard_transition) /\
    free_omega_ae (finite_internal_pair_invariant eq residual_retry_pairs) (kernel (t,u)).

(** The guard is Prob, not Vis.  Arbitrarily many failed tosses pass through
    the selected joint kernel again, with no external observation between. *)
Example retry_round_kernel_exists : exists kernel, round_spec kernel.
Proof.
  unfold round_spec. eapply finite_internal_paired_kernel_exists with
    (cut1 := fun p => residual_retry_cut1 (fst p))
    (cut2 := fun p => residual_retry_cut2 (snd p)).
  - exact (@subenum_coupling_realization).
  - intros t u Htu. apply free_subenum_structural_coupling_realization.
    exact (residual_retry_cuts_structural Htu).
Qed.

Example retry_round_complete_coupling kernel (Hkernel : round_spec kernel) :
  exists out, @stable_hitting MF FI FreeOmegaObservableSemanticOmega
    Pair Heads kernel (residual_retry_left, residual_retry_right) out /\
    free_omega_qlift (stable_head_rel eq residual_retry_pairs)
      (free_omega_bind out (fun p => FORet (fst p)))
      (free_omega_bind out (fun p => FORet (snd p))).
Proof.
  destruct (@stable_hitting_exists MF FI
    FreeOmegaObservableSemanticOmega FreeOmegaObservableSemanticMeasureOrderLaws
    FreeOmegaObservableSemanticOmegaLaws Pair Heads kernel
    (residual_retry_left, residual_retry_right)) as [out Hout].
  exists out. split; [exact Hout|].
  apply (proj2 (@finite_internal_paired_hitting_coupled residualE SubEnum
    SubEnum_SemanticMeasure SubEnum_SemanticMeasureCoreLaws
    SubEnum_SemanticMeasureCouplingAELaws SubEnum_SemanticMeasureCountableAELaws
    SubEnum_SemanticOmega bool bool eq residual_retry_pairs kernel
    (fun x y Hxy => proj2 (proj2 (Hkernel x y Hxy)))
    residual_retry_left residual_retry_right out ResidualRetryLoop Hout)).
Qed.
End InternalRetryRounds.
