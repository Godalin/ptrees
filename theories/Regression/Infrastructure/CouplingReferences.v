(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
From Coq.Program Require Import Equality.
From Coq.Logic Require Import ClassicalDescription.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg rat.
Require Import PTree.Prob.Backend.Common.RatSubTypes PTree.Prob.Backend.Enum.Representation PTree.Prob.Backend.Enum.FrontierLift.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnum.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure PTree.Prob.FreeOmega.Coupling.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq.Internal Require Import FiniteInternal.
From PTree.Eq Require Import PStrong PEutt PrimitiveStableHitting UnifiedFrontier PTreeKernel.
From PTree.Eq.Internal.FreeOmega Require Import FiniteInternalJoint.
From PTree.Regression.Backend Require Import EnumMeasureRegression SubEnumRegression.
From PTree.Regression.Probability Require Import CorrelatedSampleAlgebra.

Set Implicit Arguments.
Import Enum RatSubTypes GRing.Theory.
#[local] Open Scope ring_scope.
Local Notation MF := (FreeOmega SubEnum).

(** An actual total coin, not a non-monotone formal limit: discarding its
    result yields the Dirac distribution. *)
Lemma fair_discard_node :
  @sem_lift SubEnum SubEnum_SemanticMeasure bool bool eq
    (subenum_bind subenum_fair (fun _ => subenum_ret false)) (subenum_ret false).
Proof.
  change (enum_meas_eq (bind_Enum reg_fair (fun _ => ret_Enum false)) (ret_Enum false)).
  apply enum_meas_eq_of_eqenum.
  intro b. destruct b; rewrite /reg_fair /bind_Enum /ret_Enum /acc_mass /=.
  all: apply val_inj; cbn; ring_to_rat; reflexivity.
Qed.

Lemma fair_discard_same_mass :
  @sem_same_mass SubEnum SubEnum_SemanticMeasure bool bool
    subenum_fair (subenum_ret false).
Proof.
  assert (Hret : @sem_eq SubEnum SubEnum_SemanticMeasure bool
    (subenum_bind subenum_fair subenum_ret) subenum_fair).
  { change (enum_meas_eq (bind_Enum reg_fair ret_Enum) reg_fair).
    apply enum_meas_eq_of_eqenum.
    intro b. destruct b; rewrite /reg_fair /bind_Enum /ret_Enum /acc_mass /=.
    all: apply val_inj; cbn; ring_to_rat; reflexivity. }
  assert (Hbind : @sem_lift SubEnum SubEnum_SemanticMeasure bool bool (fun _ _ => True)
    (subenum_bind subenum_fair subenum_ret)
    (subenum_bind subenum_fair (fun _ => subenum_ret false))).
  { eapply (@sem_lift_bind SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticMeasureBindLaws bool bool bool bool eq
      (fun _ _ => True) subenum_fair subenum_fair subenum_ret
      (fun _ => subenum_ret false)).
    - apply sem_lift_refl. intro b. reflexivity.
    - intros x y _. apply (@sem_lift_ret SubEnum SubEnum_SemanticMeasure
        SubEnum_SemanticMeasureCoreLaws). exact I. }
  eapply sem_lift_mono with (R := fun x z => exists y, True /\ y = z).
  - intros x z _. exact I.
  - eapply sem_lift_comp; [|exact fair_discard_node].
    eapply sem_lift_proper_l; [exact Hret|exact Hbind].
Qed.

Definition reference_coin : MF bool := FOSample subenum_fair (fun b => FORet b).

Example reference_coin_quotient_discard :
  free_omega_qlift (fun _ _ : bool => True) reference_coin (FORet false).
Proof.
  eapply FOQLObserve with (obsA := fun _ : bool => false) (obsB := fun b : bool => b)
    (outA := subenum_bind subenum_fair (fun _ => subenum_ret false))
    (outB := subenum_ret false) (S := eq).
  - apply (FOOObserveSample (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
    intro b. apply (FOOObserveRet (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
  - apply (FOOObserveRet (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
  - exact fair_discard_node.
  - intros x y _. exact I.
  - split.
    + intros P HP. apply FOAERet.
      apply free_omega_ae_sample_inv in HP.
      pose proof (proj1 (exchange_fair_both_values HP)) as Htrue.
      dependent destruction Htrue. exists true. split; [exact I|assumption].
    + intros P HP. dependent destruction HP.
      apply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
      intros b _. apply FOAERet. exists false. split; [exact I|assumption].
Qed.

(** No pair of structurally marginalized references realizes this valid
    quotient coupling.  This refutes the proposed general reference-
    extraction shortcut, not behavioral equivalence. *)
Example reference_coin_discard_has_no_references :
  ~ exists left right, free_omega_coupling_references (fun _ _ : bool => True)
    reference_coin (FORet false) left right.
Proof.
  intros [left [right H]].
  destruct (free_omega_coupling_references_ret_deterministic H) as [b Hae].
  apply free_omega_ae_sample_inv in Hae.
  destruct (exchange_fair_both_values Hae) as [Htrue Hfalse].
  dependent destruction Htrue; dependent destruction Hfalse; congruence.
Qed.

(** The same coupling DOES have an ordinary joint witness.  It is the
    extra structural-reference requirement, not joint realizability,
    that fails in the preceding test. *)
Example reference_coin_discard_ordinary_joint :
  @SemanticCoupling.semantic_coupling MF
    (FreeOmegaObservableSemanticMeasure
      (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega))
    bool bool (fun _ _ => True) reference_coin (FORet false)
    (free_omega_graph_joint (fun _ : bool => false) reference_coin).
Proof.
  eapply SemanticCoupling.semantic_coupling_mono;
    [|apply free_omega_qlift_graph_realization].
  - intros x y _. exact I.
  - eapply FOQLAERestrict with (T := fun _ _ : bool => True)
      (P := fun _ => True) (Q := fun y => y = false).
    + exact reference_coin_quotient_discard.
    + apply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
      intros b _. apply FOAERet. exact I.
    + apply FOAERet. reflexivity.
    + intros x y [_ [_ ->]]. reflexivity.
Qed.

(** Equality, in contrast, always admits references; their representations
    may be entirely different, as in this constant-Lub test. *)
Example reference_constant_limit {A} (mu : MF A) :
  free_omega_coupling_references eq mu (FOLub (fun _ => mu))
    (free_omega_graph_joint (fun x => x) mu)
    (free_omega_graph_joint (fun x => x) (FOLub (fun _ => mu))).
Proof.
  apply free_omega_eq_coupling_references.
  apply FOQLLubConstantR, free_omega_qlift_refl. intro x. reflexivity.
Qed.

(** The obstruction already occurs on valid finite_internal cuts and the
    intended pstrongF guard, not only on an arbitrary test relation.  Both
    programs terminate; the coin only decides whether to insert one more
    Tau.  Different cuts can still be useful: this theorem rules out a
    universal extraction lemma for the GIVEN cuts, not their hitting semantics. *)
Local Notation tree := (ptree exchangeE SubEnum bool).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Local Notation residual := (@peutt exchangeE SubEnum MF FI
  FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
  FreeOmegaObservableSemanticOmega bool bool eq).

Definition discarded_coin_delay (b : bool) : tree :=
  if b then Tau (Tau (Ret false)) else Tau (Ret false).
Definition discarded_coin_cut : MF tree :=
  FOSample subenum_fair (fun b => FORet (discarded_coin_delay b)).

Definition discarded_left_observation (t : tree) : bool :=
  if excluded_middle_informative
    (t = discarded_coin_delay true \/ t = discarded_coin_delay false)
  then false else true.
Definition discarded_right_observation (t : tree) : bool :=
  if excluded_middle_informative (t = discarded_coin_delay false) then false else true.

Lemma discarded_left_observationE b :
  discarded_left_observation (discarded_coin_delay b) = false.
Proof.
  unfold discarded_left_observation. destruct excluded_middle_informative;
    [reflexivity|]. destruct b; exfalso; tauto.
Qed.
Lemma discarded_right_observationE :
  discarded_right_observation (discarded_coin_delay false) = false.
Proof.
  unfold discarded_right_observation. destruct excluded_middle_informative;
    [reflexivity|]. contradiction.
Qed.

Lemma discarded_coin_guard b :
  (fun t u => pstrongF eq residual (observe t) (observe u)) (discarded_coin_delay b) (discarded_coin_delay false).
Proof.
  unfold discarded_coin_delay. destruct b; cbn; constructor.
  - apply peutt_tau_l.
  - apply peutt_refl.
Qed.

Lemma discarded_coin_residual_lift :
  free_omega_qlift (fun t u => pstrongF eq residual (observe t) (observe u))
    discarded_coin_cut (FORet (discarded_coin_delay false)).
Proof.
  eapply FOQLObserve with
    (obsA := discarded_left_observation) (obsB := discarded_right_observation)
    (outA := subenum_bind subenum_fair (fun _ => subenum_ret false))
    (outB := subenum_ret false) (S := fun x y => x = y /\ y = false).
  - apply (FOOObserveSample (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
    intro b. rewrite <- (discarded_left_observationE b).
    apply (FOOObserveRet (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
  - replace (subenum_ret false) with
      (subenum_ret (discarded_right_observation (discarded_coin_delay false)))
      by (rewrite discarded_right_observationE; reflexivity).
    apply (FOOObserveRet (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
  - eapply sem_lift_mono with (R := fun x y => x = y /\ True /\ y = false).
    + intros x y [Heq [_ Hy]]. split; assumption.
    + eapply sem_lift_ae_restrict; [exact fair_discard_node|apply sem_ae_true|].
      apply (proj2 (@sem_ae_ret_iff SubEnum SubEnum_SemanticMeasure
        SubEnum_SemanticMeasureDiracAELaws bool false (fun y => y = false))).
      reflexivity.
  - intros t u [Heq Hu].
    unfold discarded_left_observation, discarded_right_observation in *.
    destruct (excluded_middle_informative
      (t = discarded_coin_delay true \/ t = discarded_coin_delay false)) as [Ht|Ht];
      destruct (excluded_middle_informative (u = discarded_coin_delay false)) as [Hu'|Hu'];
      try discriminate.
    destruct Ht as [Ht|Ht]; subst t; subst u; apply discarded_coin_guard.
  - split.
    + intros P HP. apply FOAERet.
      apply free_omega_ae_sample_inv in HP.
      pose proof (proj1 (exchange_fair_both_values HP)) as Htrue.
      dependent destruction Htrue. exists (discarded_coin_delay true).
      split; [apply discarded_coin_guard|assumption].
    + intros P HP. dependent destruction HP.
      apply FOAESample with (Good := fun _ => True); [apply sem_ae_true|].
      intros b _. apply FOAERet. exists (discarded_coin_delay false).
      split; [apply discarded_coin_guard|assumption].
Qed.

(** Compute the complete heads directly; the sampled bit is discarded,
    while both administrative delays disappear by Tau transparency. *)
Example discarded_coin_delay_peutt :
  residual (Prob subenum_fair discarded_coin_delay) (discarded_coin_delay false).
Proof.
  eapply (peutt_of_hitting_lift (FI := FI)
    (FO := FreeOmegaObservableSemanticOmega) (MX := FreeOmegaMixedMeasure)) with
    (out1 := FOSample subenum_fair (fun _ => FORet (FHRet false)))
    (out2 := FORet (FHRet false)).
  - eapply (stable_hitting_prob (FI := FI)
      (FO := FreeOmegaObservableSemanticOmega) (MX := FreeOmegaMixedMeasure))
      with (Good := fun _ => True).
    + apply sem_ae_true.
    + intros [] _; unfold discarded_coin_delay.
      * apply (proj2 (stable_hitting_tau_iff _ _)).
        apply (proj2 (stable_hitting_tau_iff _ _)).
        apply (stable_hitting_ret (FI := FI)
          (FO := FreeOmegaObservableSemanticOmega) (MX := FreeOmegaMixedMeasure)).
      * apply (proj2 (stable_hitting_tau_iff _ _)).
        apply (stable_hitting_ret (FI := FI)
          (FO := FreeOmegaObservableSemanticOmega) (MX := FreeOmegaMixedMeasure)).
  - unfold discarded_coin_delay.
    apply (proj2 (stable_hitting_tau_iff _ _)).
    apply (stable_hitting_ret (FI := FI)
      (FO := FreeOmegaObservableSemanticOmega) (MX := FreeOmegaMixedMeasure)).
  - eapply free_omega_sample_to_constant with (point := false).
    + intro P. apply sem_ae_ret_iff.
    + exact fair_discard_same_mass.
    + intro b. apply FOQLStructural, FOLRet. constructor. reflexivity.
Qed.

Example discarded_coin_cuts_have_no_references :
  ~ exists left right, free_omega_coupling_references (fun t u => pstrongF eq residual (observe t) (observe u))
    discarded_coin_cut (FORet (discarded_coin_delay false)) left right.
Proof.
  intros [left [right H]].
  destruct (free_omega_coupling_references_ret_deterministic H) as [t Hae].
  apply free_omega_ae_sample_inv in Hae.
  destruct (exchange_fair_both_values Hae) as [Htrue Hfalse].
  dependent destruction Htrue; dependent destruction Hfalse.
Qed.

(** Advancing the pstrongF guard does not remove the obstruction: the two
    residual successors are Ret false and Tau (Ret false).  Thus even the
    earlier execution-kernel reference premise is not universally
    extractable for these legitimate cuts. *)
Example discarded_coin_rounds_have_no_reference_kernels :
  ~ exists left right : MF (PrimitiveStableHitting.stable_target
      (tree * tree) (UnifiedFrontier.stable_head exchangeE SubEnum bool *
                    UnifiedFrontier.stable_head exchangeE SubEnum bool)),
    free_omega_qlift eq left right /\
    free_omega_lift (fun z target => finite_internal_pair_left z = target)
      left (free_omega_bind discarded_coin_cut finite_internal_guard_transition) /\
    free_omega_lift (fun z target => finite_internal_pair_right z = target)
      right (finite_internal_guard_transition (discarded_coin_delay false)).
Proof.
  intros [left [right [Heq [Hl Hr]]]].
  change (free_omega_lift (fun z target => finite_internal_pair_right z = target)
    right (FORet (PrimitiveStableHitting.SHInternal (Ret false : tree)))) in Hr.
  destruct (free_omega_reference_marginals_ret_deterministic Heq Hl Hr) as [z Hae].
  apply free_omega_ae_sample_inv in Hae.
  destruct (exchange_fair_both_values Hae) as [Htrue Hfalse].
  dependent destruction Htrue; dependent destruction Hfalse.
Qed.
