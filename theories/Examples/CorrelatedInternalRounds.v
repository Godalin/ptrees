Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
From Coq Require Import Program.Equality.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureEnum
  TwoLevelMeasureSubEnum DiscreteMC SemanticCoupling SemanticCouplingEnum
  FreeOmegaMeasure FreeOmegaCouplingEnum.
From PTree.Eq Require Import PrimitiveStableHitting UnifiedFrontier PFiniteResidual PTreeKernel PEutt.
From PTree.Eq.FreeOmega Require Import FiniteInternalJoint FiniteInternalJointHitting
  FiniteInternalJointCoverage FiniteInternalJointAcceleration FiniteInternalJointCoinduction.
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

(** An explicit realization of the existing partner-dependent strategy.
    Both residuals equal the selected right partner, but the LEFT cut
    still depends on that partner, not just on the left source tree. *)
Definition diagonal_guard (t : tree) : MF (stable_target Pair Heads) :=
  match observe t with
  | RetF r => FORet (SHStable (FHRet r, FHRet r))
  | TauF u => FORet (SHInternal (u,u))
  | VisF _ e k => FORet (SHStable (FHVis e k, FHVis e k))
  | ProbF _ mu k => FOSample mu (fun x => FORet (SHInternal (k x,k x)))
  end.
Definition correlated_kernel (p : Pair) := diagonal_guard (snd p).

Lemma correlated_kernel_left_structural t u :
  free_omega_lift (fun z x => finite_internal_pair_left z = x)
    (correlated_kernel (t,u))
    (free_omega_bind (left_cut (t,u)) finite_internal_guard_transition).
Proof.
  unfold correlated_kernel, diagonal_guard, left_cut, finite_internal_guard_transition.
  cbn [snd free_omega_bind]. destruct (observe u).
  all: try solve [apply FOLRet; reflexivity].
  apply FOLSample with (S := eq).
  - apply sem_lift_refl. intro x. reflexivity.
  - intros x y ->. apply FOLRet. reflexivity.
Qed.

Lemma correlated_kernel_right_structural t u :
  free_omega_lift (fun z x => finite_internal_pair_right z = x)
    (correlated_kernel (t,u))
    (free_omega_bind (right_cut (t,u)) finite_internal_guard_transition).
Proof.
  unfold correlated_kernel, diagonal_guard, right_cut, finite_internal_guard_transition.
  cbn [snd free_omega_bind]. destruct (observe u).
  all: try solve [apply FOLRet; reflexivity].
  apply FOLSample with (S := eq).
  - apply sem_lift_refl. intro x. reflexivity.
  - intros x y ->. apply FOLRet. reflexivity.
Qed.

Lemma correlated_kernel_spec : round_spec correlated_kernel.
Proof.
  intros t u Htu. split.
  - apply FOQLStructural, correlated_kernel_left_structural.
  - split.
    + apply FOQLStructural, correlated_kernel_right_structural.
    + destruct Htu as [b|].
      * destruct b; apply FOAERet; cbn.
        -- constructor. reflexivity.
        -- constructor.
      * apply FOAERet. cbn. constructor. reflexivity.
Qed.

(** The actual partner-dependent strategy is now a sound native proof,
    without replacing its cuts by independent marginal policies. *)
Example correlated_cuts_prove_peutt t u : candidate t u ->
  @peutt event Enum MF FI FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool bool eq t u.
Proof.
  intro Htu. eapply peutt_coinduction_finite_internal_structural with
    (sim := candidate) (cut1 := left_cut) (cut2 := right_cut).
  - intros x y Hxy. exact (left_cut_valid Hxy).
  - intros x y Hxy. exact (right_cut_valid Hxy).
  - intros x y Hxy. apply FOLRet. exact (partner_guarded Hxy).
  - exact (@enum_coupling_realization).
  - exact Htu.
Qed.

(** An equivalent representation of every round still satisfies the
    QUOTIENT graph-marginal contract, but need not satisfy raw coverage. *)
Definition quotient_round_kernel (p : Pair) := FOLub (fun _ => correlated_kernel p).

Lemma quotient_round_kernel_spec : round_spec quotient_round_kernel.
Proof.
  intros t u Htu. destruct (correlated_kernel_spec Htu) as [Hl [Hr Hae]].
  split.
  - apply FOQLSym, FOQLLubConstantR, FOQLSym. exact Hl.
  - split.
    + apply FOQLSym, FOQLLubConstantR, FOQLSym. exact Hr.
    + apply FOAELub. intros _. exact Hae.
Qed.

Example quotient_round_raw_coverage_fails :
  ~ free_omega_approx eq
    (@ptree_hitting_approx event Enum MF FI FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega bool 0 (observe done))
    (free_omega_bind
      (@stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
        Pair Heads quotient_round_kernel 0 (done,done)) (fun h => FORet (fst h))).
Proof. intro H. inversion H. Qed.

(** Despite that raw failure, COMPLETE hitting is now proved equal to
    the original marginal, using a structurally realized reference kernel. *)
Example quotient_round_complete_hitting_exact t u joint_out original_out :
  candidate t u ->
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega
    Pair Heads quotient_round_kernel (t,u) joint_out ->
  @ptree_stable_hitting event Enum MF FI FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega bool (observe t) original_out ->
  free_omega_qlift eq
    (free_omega_bind joint_out (fun h => FORet (fst h))) original_out.
Proof.
  intros Htu Hjoint Horiginal.
  eapply finite_internal_structural_execution_adequate_modulo_eq with
    (kernel := correlated_kernel) (represented := quotient_round_kernel)
    (project_state := @fst tree tree)
    (D := fun p => candidate (fst p) (snd p)) (cut := left_cut) (s := (t,u)).
  - intros [x y] Hxy. eapply free_omega_ae_mono;
      [|exact (proj2 (proj2 (correlated_kernel_spec Hxy)))].
    intros [heads|trees] Hgood; cbn; [exact I|exact Hgood].
  - intros [x y] Hxy. exact (left_cut_valid Hxy).
  - intros [x y] _. apply correlated_kernel_left_structural.
  - exact (@enum_coupling_realization).
  - intros p _. apply FOQLLubConstantR, free_omega_qlift_refl. intro z. reflexivity.
  - exact Htu.
  - exact Hjoint.
  - exact Horiginal.
Qed.

(** The failed raw statement is repaired by retaining an equality-related
    representative, not by strengthening raw order with an unproved law. *)
Example quotient_round_coverage_modulo_eq n t u : candidate t u ->
  exists covered,
    free_omega_approx eq
      (@ptree_hitting_approx event Enum MF FI FreeOmegaMixedMeasure
        FreeOmegaObservableSemanticOmega bool n (observe t)) covered /\
    free_omega_qlift eq covered
      (free_omega_bind
        (@stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
          Pair Heads quotient_round_kernel n (t,u)) (fun h => FORet (fst h))).
Proof.
  intro Htu. eapply (finite_internal_execution_covers_modulo_eq
    (NI := Enum_SemanticMeasure) (NO := Enum_SemanticOmega)) with
    (kernel := correlated_kernel) (n := n) (s := (t,u))
    (project_output := @fst (stable_head event Enum bool) (stable_head event Enum bool))
    (project_state := @fst tree tree)
    (D := fun p => candidate (fst p) (snd p)) (cut := left_cut).
  - intros [x y] Hxy. eapply free_omega_ae_mono;
      [|exact (proj2 (proj2 (correlated_kernel_spec Hxy)))].
    intros [heads|trees] Hgood; cbn; [exact I|exact Hgood].
  - intros [x y] Hxy. exact (left_cut_valid Hxy).
  - intros [x y] _. apply correlated_kernel_left_structural.
  - intros p _. apply FOQLLubConstantR, free_omega_qlift_refl. intro z. reflexivity.
  - exact Htu.
Qed.

Example quotient_round_complete_coverage_modulo_eq t u : candidate t u ->
  exists covered,
    free_omega_approx eq
      (FOLub (fun n => @ptree_hitting_approx event Enum MF FI FreeOmegaMixedMeasure
        FreeOmegaObservableSemanticOmega bool n (observe t))) covered /\
    free_omega_qlift eq covered
      (free_omega_bind
        (FOLub (fun n => @stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
          Pair Heads quotient_round_kernel n (t,u))) (fun h => FORet (fst h))).
Proof.
  intro Htu. eapply (finite_internal_execution_limit_covers_modulo_eq
    (NI := Enum_SemanticMeasure) (NO := Enum_SemanticOmega)) with
    (kernel := correlated_kernel) (s := (t,u))
    (project_output := @fst (stable_head event Enum bool) (stable_head event Enum bool))
    (project_state := @fst tree tree)
    (D := fun p => candidate (fst p) (snd p)) (cut := left_cut).
  - intros [x y] Hxy. eapply free_omega_ae_mono;
      [|exact (proj2 (proj2 (correlated_kernel_spec Hxy)))].
    intros [heads|trees] Hgood; cbn; [exact I|exact Hgood].
  - intros [x y] Hxy. exact (left_cut_valid Hxy).
  - intros [x y] _. apply correlated_kernel_left_structural.
  - intros p _. apply FOQLLubConstantR, free_omega_qlift_refl. intro z. reflexivity.
  - exact Htu.
Qed.

Example correlated_primitive_steps_covered n t u : candidate t u ->
  free_omega_approx eq
    (@ptree_hitting_approx event Enum MF FI FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega bool n (observe t))
    (free_omega_bind
      (@stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
        Pair Heads correlated_kernel n (t,u)) (fun h => FORet (fst h))).
Proof.
  intro Htu. eapply (finite_internal_execution_covers_hitting
    (NI := Enum_SemanticMeasure) (NO := Enum_SemanticOmega)) with
    (kernel := correlated_kernel) (n := n) (s := (t,u))
    (project_output := @fst (stable_head event Enum bool) (stable_head event Enum bool))
    (project_state := @fst tree tree)
    (D := fun p => candidate (fst p) (snd p)) (cut := left_cut).
  - intros [x y] Hxy. eapply free_omega_ae_mono;
      [|exact (proj2 (proj2 (correlated_kernel_spec Hxy)))].
    intros [heads|trees] Hgood; cbn; [exact I|exact Hgood].
  - intros [x y] Hxy. exact (left_cut_valid Hxy).
  - intros [x y] _. apply correlated_kernel_left_structural.
  - exact Htu.
Qed.

Example correlated_complete_hitting_covered t u : candidate t u ->
  free_omega_approx eq
    (FOLub (fun n => @ptree_hitting_approx event Enum MF FI FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega bool n (observe t)))
    (free_omega_bind
      (FOLub (fun n => @stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
        Pair Heads correlated_kernel n (t,u))) (fun h => FORet (fst h))).
Proof. intro Htu. apply FOApproxLub. intro n. apply correlated_primitive_steps_covered, Htu. Qed.

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

(** The COMPLETE correlated execution is below a representative of the
    original left hitting.  This is not yet equality of their limits. *)
Example correlated_left_hitting_upper kernel (Hkernel : round_spec kernel)
    (front : tree -> MF (stable_head event Enum bool))
    (Hfront : forall t, @ptree_stable_hitting event Enum MF FI
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool
      (observe t) (front t)) t u : candidate t u ->
  exists upper,
    free_omega_approx eq
      (free_omega_bind
        (FOLub (fun n => @stable_hitting_approx MF FI
          FreeOmegaObservableSemanticOmega Pair Heads kernel n (t,u)))
        (fun h => FORet (fst h))) upper /\
    free_omega_qlift eq upper (front t).
Proof.
  intro Htu. eapply finite_internal_execution_hitting_upper with
    (project_state := @fst tree tree)
    (D := fun p => candidate (fst p) (snd p)) (cut := left_cut).
  - exact Hfront.
  - intros [x y] Hxy. eapply free_omega_ae_mono;
      [|exact (proj2 (proj2 (Hkernel x y Hxy)))].
    intros [heads|trees] Hgood; cbn; [exact I|exact Hgood].
  - intros [x y] Hxy. exact (left_cut_valid Hxy).
  - intros [x y] Hxy. exact (proj1 (Hkernel x y Hxy)).
  - exact Htu.
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

Definition structural_round_spec (kernel : Pair -> MF (stable_target Pair Heads)) :=
  forall t u, residual_retry_pairs t u ->
    free_omega_lift (fun z x => finite_internal_pair_left z = x)
      (kernel (t,u))
      (free_omega_bind (residual_retry_cut1 t) finite_internal_guard_transition) /\
    free_omega_lift (fun z y => finite_internal_pair_right z = y)
      (kernel (t,u))
      (free_omega_bind (residual_retry_cut2 u) finite_internal_guard_transition) /\
    free_omega_ae (finite_internal_pair_invariant eq residual_retry_pairs) (kernel (t,u)).

Example retry_structural_round_kernel_exists : exists kernel, structural_round_spec kernel.
Proof.
  unfold structural_round_spec. eapply finite_internal_structural_paired_kernel_exists with
    (cut1 := fun p => residual_retry_cut1 (fst p))
    (cut2 := fun p => residual_retry_cut2 (snd p)).
  - exact (@subenum_coupling_realization).
  - intros t u Htu. exact (residual_retry_cuts_structural Htu).
Qed.

(** The guard is Prob, not Vis.  Arbitrarily many failed tosses pass through
    the selected joint kernel again, with no external observation between. *)
Example retry_round_kernel_exists : exists kernel, round_spec kernel.
Proof.
  destruct retry_structural_round_kernel_exists as [kernel Hkernel].
  exists kernel. intros t u Htu. destruct (Hkernel t u Htu) as [Hl [Hr Hae]].
  split; [apply FOQLStructural; exact Hl|].
  split; [apply FOQLStructural; exact Hr|exact Hae].
Qed.

(** No assumption of [residual_retries_peutt] or independent policies:
    this uses the newly proved joint-execution route through arbitrarily
    many internal Prob guards. *)
Example retry_joint_coinduction_proves_peutt :
  @peutt residualE SubEnum MF FI FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool bool eq
    residual_retry_left residual_retry_right.
Proof.
  eapply peutt_coinduction_finite_internal_structural with
    (sim := residual_retry_pairs)
    (cut1 := fun p => residual_retry_cut1 (fst p))
    (cut2 := fun p => residual_retry_cut2 (snd p)).
  - intros x y _. apply residual_retry_cut1_valid.
  - intros x y _. apply residual_retry_cut2_valid.
  - intros x y Hxy. exact (residual_retry_cuts_structural Hxy).
  - exact (@subenum_coupling_realization).
  - constructor.
Qed.

Example retry_primitive_steps_covered kernel (Hkernel : structural_round_spec kernel)
    n t u : residual_retry_pairs t u ->
  free_omega_approx eq
    (@ptree_hitting_approx residualE SubEnum MF FI FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega bool n (observe t))
    (free_omega_bind
      (@stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
        Pair Heads kernel n (t,u)) (fun h => FORet (fst h))).
Proof.
  intro Htu. eapply (finite_internal_execution_covers_hitting
    (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)) with
    (kernel := kernel) (n := n) (s := (t,u))
    (project_output := @fst (stable_head residualE SubEnum bool)
      (stable_head residualE SubEnum bool))
    (project_state := @fst tree tree)
    (D := fun p => residual_retry_pairs (fst p) (snd p))
    (cut := fun p => residual_retry_cut1 (fst p)).
  - intros [x y] Hxy. eapply free_omega_ae_mono;
      [|exact (proj2 (proj2 (Hkernel x y Hxy)))].
    intros [heads|trees] Hgood; cbn; [exact I|exact Hgood].
  - intros [x y] _. apply residual_retry_cut1_valid.
  - intros [x y] Hxy. exact (proj1 (Hkernel x y Hxy)).
  - exact Htu.
Qed.

Example retry_complete_hitting_covered kernel (Hkernel : structural_round_spec kernel) :
  free_omega_approx eq
    (FOLub (fun n => @ptree_hitting_approx residualE SubEnum MF FI FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega bool n (observe residual_retry_left)))
    (free_omega_bind
      (FOLub (fun n => @stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
        Pair Heads kernel n (residual_retry_left, residual_retry_right)))
      (fun h => FORet (fst h))).
Proof.
  apply FOApproxLub. intro n. eapply retry_primitive_steps_covered;
    [exact Hkernel|constructor].
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

(** The upper bound also covers the purely internal retry loop; it does
    not require reaching a visible observation after each round. *)
Example retry_left_hitting_upper kernel (Hkernel : round_spec kernel)
    (front : tree -> MF (stable_head residualE SubEnum bool))
    (Hfront : forall t, @ptree_stable_hitting residualE SubEnum MF FI
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticOmega bool
      (observe t) (front t)) :
  exists upper,
    free_omega_approx eq
      (free_omega_bind
        (FOLub (fun n => @stable_hitting_approx MF FI
          FreeOmegaObservableSemanticOmega Pair Heads kernel n
          (residual_retry_left, residual_retry_right)))
        (fun h => FORet (fst h))) upper /\
    free_omega_qlift eq upper (front residual_retry_left).
Proof.
  eapply finite_internal_execution_hitting_upper with
    (project_state := @fst tree tree)
    (D := fun p => residual_retry_pairs (fst p) (snd p))
    (cut := fun p => residual_retry_cut1 (fst p)).
  - exact Hfront.
  - intros [x y] Hxy. eapply free_omega_ae_mono;
      [|exact (proj2 (proj2 (Hkernel x y Hxy)))].
    intros [heads|trees] Hgood; cbn; [exact I|exact Hgood].
  - intros [x y] _. apply residual_retry_cut1_valid.
  - intros [x y] Hxy. exact (proj1 (Hkernel x y Hxy)).
  - constructor.
Qed.
End InternalRetryRounds.
