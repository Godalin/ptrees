(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

Require Import List.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat ssralg ssrnum order rat.
Require Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Bind PTree.Prob.Backend.EnumQ.Coupling PTree.Prob.Backend.EnumQ.IndexedCoupling.
From PTree.Prob.Interface Require Import FrontierLift.
Require Import PTree.Prob.Backend.EnumQ.FrontierLift.
Require Import PTree.Prob.Interface.Iteration.
Require Import PTree.Prob.Backend.EnumQ.Iteration.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ.
Import PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Coupling IndexedCoupling.
From PTree.Prob.Backend.Common Require Import FiniteEnum FinitePositions FinitePruning.
Import GRing.Theory Order.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

(** Compatibility adapter: EnumQ implements both layers of the new model with
    the same concrete representation.  The distinction remains visible to
    the generic theory even though it collapses in this instance. *)
#[global] Instance EnumQ_SemanticMeasure :
    SemanticMeasure EnumQ := {
  sem_ret := @meas_ret EnumQ EnumQ_MeasureInterface;
  sem_bind := @meas_bind EnumQ EnumQ_MeasureInterface;
  sem_eq := @meas_eq EnumQ EnumQ_MeasureInterface;
  sem_ae := @meas_ae EnumQ EnumQ_MeasureInterface;
  sem_lift := @meas_lift EnumQ EnumQ_MeasureInterface
}.

#[global] Instance EnumQ_SemanticMeasureCoreLaws :
    @SemanticMeasureCoreLaws EnumQ EnumQ_SemanticMeasure.
Proof.
  constructor.
  - exact (@meas_eq_refl EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureCoreLaws EnumQ_MeasureLaws).
  - exact (@meas_eq_sym EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureCoreLaws EnumQ_MeasureLaws).
  - exact (@meas_eq_trans EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureCoreLaws EnumQ_MeasureLaws).
  - exact (@meas_ae_true EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureCoreLaws EnumQ_MeasureLaws).
  - exact (@meas_ae_mono EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureCoreLaws).
  - exact (@meas_ae_conj EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureCoreLaws EnumQ_MeasureLaws).
  - exact (@meas_lift_mono EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureCoreLaws).
  - exact (@meas_lift_refl EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureCoreLaws).
  - exact (@meas_lift_ret EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureCoreLaws).
  - exact (@meas_lift_proper_l EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureCoreLaws EnumQ_MeasureLaws).
  - exact (@meas_lift_proper_r EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureCoreLaws EnumQ_MeasureLaws).
  - exact (@meas_lift_sym EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureCoreLaws EnumQ_MeasureLaws).
  - exact (@meas_lift_comp EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureCoreLaws EnumQ_MeasureLaws).
Qed.

#[global] Instance EnumQ_SemanticMeasureAELiftLaws :
    @SemanticMeasureAELiftLaws EnumQ EnumQ_SemanticMeasure.
Proof.
  constructor. move=> A mu P Hae. cbn in Hae |- *.
  unfold enumQ_meas_eq.
  eapply (coupling_mono (R := eq));
    [|exact (coupling_refl (indexed (enumQ_prune mu)))].
  move=> i j ->. split.
  - move=> p x Hi. exists p, x. split; first exact Hi.
    split; first reflexivity.
    have Hin : List.In (p, x) (enumQ_raw (enumQ_prune mu)).
    { eapply nth_error_In. exact Hi. }
    have [Hsrc Hnz] := enumQ_prune_in_source Hin.
    exact (Hae p x Hsrc Hnz).
  - move=> p x Hi. exists p, x. split; first exact Hi.
    split; first reflexivity.
    have Hin : List.In (p, x) (enumQ_raw (enumQ_prune mu)).
    { eapply nth_error_In. exact Hi. }
    have [Hsrc Hnz] := enumQ_prune_in_source Hin.
    exact (Hae p x Hsrc Hnz).
Qed.

#[global] Instance EnumQ_SemanticMeasureAEKleisliLaws :
    @SemanticMeasureAEKleisliLaws EnumQ EnumQ_SemanticMeasure.
Proof.
  constructor.
  - intros A P x Hx. exact (@meas_ae_ret EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureMonadLaws A x P Hx).
  - exact (@meas_ae_bind EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureAEKleisliLaws).
Qed.

#[global] Instance EnumQ_SemanticMeasureDiracAELaws :
    @SemanticMeasureDiracAELaws EnumQ EnumQ_SemanticMeasure.
Proof.
  constructor. intros A x P. split.
  - intro Hae. apply (Hae 1 x); cbn.
    + left. reflexivity.
    + discriminate.
  - intro Hx. exact (@meas_ae_ret EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureMonadLaws A x P Hx).
Qed.

Lemma enumQ_scale_entry_image {A} p (Hp : 0 <= p) q (x : A) (mu : EnumQ A) :
  List.In (q,x) (enumQ_raw mu) -> List.In (p*q,x) (enumQ_raw (scale_EnumQ Hp mu)).
Proof. move=> H; apply List.in_map_iff; exists (q,x); by split. Qed.
Lemma enumQ_bind_entry_image {A B} (mu : EnumQ A) (k : A -> EnumQ B) p (x : A) q (y : B) :
  List.In (p,x) (enumQ_raw mu) -> List.In (q,y) (enumQ_raw (k x)) ->
  List.In (p*q,y) (enumQ_raw (bind_EnumQ mu k)).
Proof.
  move=> H K; apply List.in_flat_map; exists (p,x); split; first exact H.
  apply List.in_map_iff; exists (q,y); by split.
Qed.

#[global] Instance EnumQ_SemanticMeasureBindAEExactLaws :
    @SemanticMeasureBindAEExactLaws EnumQ EnumQ_SemanticMeasure.
Proof.
  constructor. intros A B mu k P. split.
  - intros Hflat p x Hpx Hpn q y Hqy Hqn.
    apply (Hflat (p * q) y).
    + exact (enumQ_bind_entry_image Hpx Hqy).
    + move=> Hzero. have Hmul : p * q != 0.
      { rewrite mulf_eq0 negb_or; apply/andP; split; apply/eqP; assumption. }
      move/eqP: Hmul. contradiction.
  - intro Hnested. eapply sem_ae_bind.
    + exact Hnested.
    + intros x Hx. exact Hx.
Qed.

#[global] Instance EnumQ_SemanticMeasureCouplingAELaws :
    @SemanticMeasureCouplingAELaws EnumQ EnumQ_SemanticMeasure.
Proof.
  constructor.
  - exact (@meas_lift_ae_transport_r EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureLiftAELaws).
  - move=> A B R mu nu P Q Hlift HP HQ.
  cbn in Hlift, HP, HQ |- *.
  unfold indexed_coupling in Hlift |- *.
  eapply coupling_mono; [|exact Hlift].
  move=> i j [HL HR]. split.
  - move=> p x Hi.
    move: (HL p x Hi)=> [q [y [Hj Hxy]]].
    exists q, y. split; [exact Hj|]. split; [exact Hxy|]. split.
    + have Hin := @nth_error_In _ (enumQ_raw (enumQ_prune mu)) i (p, x) Hi.
      have [Hsrc Hnz] := enumQ_prune_in_source Hin.
      exact (HP p x Hsrc Hnz).
    + have Hin := @nth_error_In _ (enumQ_raw (enumQ_prune nu)) j (q, y) Hj.
      have [Hsrc Hnz] := enumQ_prune_in_source Hin.
      exact (HQ q y Hsrc Hnz).
  - move=> q y Hj.
    move: (HR q y Hj)=> [p [x [Hi Hxy]]].
    exists p, x. split; [exact Hi|]. split; [exact Hxy|]. split.
    + have Hin := @nth_error_In _ (enumQ_raw (enumQ_prune mu)) i (p, x) Hi.
      have [Hsrc Hnz] := enumQ_prune_in_source Hin.
      exact (HP p x Hsrc Hnz).
    + have Hin := @nth_error_In _ (enumQ_raw (enumQ_prune nu)) j (q, y) Hj.
      have [Hsrc Hnz] := enumQ_prune_in_source Hin.
      exact (HQ q y Hsrc Hnz).
Qed.

#[global] Instance EnumQ_SemanticMeasureCountableAELaws :
    @SemanticMeasureCountableAELaws EnumQ EnumQ_SemanticMeasure.
Proof.
  constructor. intros A mu P HP p x Hin Hnz n.
  exact (HP n p x Hin Hnz).
Qed.

(** Eventwise order on finite rational measures.  EnumQ is not globally
    omega-complete, so this adapter intentionally provides the omega
    operations but no unconditional [SemanticOmegaLaws] instance. *)
Definition enumQ_sem_le {A} (mu nu : EnumQ A) : Prop :=
  forall P : A -> bool,
    enumQ_expect (fun x => if P x then 1 else 0) mu <=
    enumQ_expect (fun x => if P x then 1 else 0) nu.

#[global] Instance EnumQ_SemanticOmega :
    @SemanticOmega EnumQ EnumQ_SemanticMeasure := {
  sem_zero := fun A => @enumQ_zero A;
  sem_le := @enumQ_sem_le;
  sem_lub := @enumQ_converges;
  sem_total := fun A mu => enumQ_expect (fun _ : A => 1) mu = 1
}.

#[global] Instance EnumQ_SemanticMeasureBindLaws :
    @SemanticMeasureBindLaws EnumQ EnumQ_SemanticMeasure.
Proof.
  constructor.
  - exact (@meas_bind_ret_l EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureMonadLaws).
  - exact (@meas_bind_assoc EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureMonadLaws).
  - exact (@meas_bind_ae_proper EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureBindLaws).
  - exact (@meas_lift_bind EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureLiftBindLaws).
Qed.

#[global] Instance EnumQ_MixedMeasure :
    MixedMeasure EnumQ EnumQ := {
  mixed_bind := @meas_bind EnumQ EnumQ_MeasureInterface
}.

#[global] Instance EnumQ_MixedMeasureLaws :
    @MixedMeasureLaws EnumQ EnumQ
      EnumQ_SemanticMeasure EnumQ_SemanticMeasure
      EnumQ_MixedMeasure.
Proof.
  constructor.
  - exact (@meas_bind_ae_proper EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureBindLaws).
  - exact (@meas_bind_assoc EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureMonadLaws).
  - exact (@meas_lift_bind EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureLiftBindLaws).
Qed.

#[global] Instance EnumQ_MixedMeasureUnitLaws :
    @MixedMeasureUnitLaws EnumQ EnumQ
      EnumQ_SemanticMeasure EnumQ_SemanticMeasure
      EnumQ_MixedMeasure.
Proof.
  constructor. intros A B x k.
  eapply sem_lift_proper_l.
  - apply sem_eq_sym. exact (@meas_bind_ret_l EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureMonadLaws A B x k).
  - apply sem_lift_refl. intro y. reflexivity.
Qed.

#[global] Instance EnumQ_MixedMeasureNodeBindLaws :
    @MixedMeasureNodeBindLaws EnumQ EnumQ
      EnumQ_SemanticMeasure EnumQ_SemanticMeasure
      EnumQ_MixedMeasure.
Proof.
  constructor. intros A B C mu h k.
  eapply sem_lift_proper_l.
  - exact (@meas_bind_assoc EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureMonadLaws A B C mu h k).
  - apply sem_lift_refl. intro z. reflexivity.
Qed.

(** Indexed couplings preserve the total finite weight even when the value
    carriers have no decidable equality.  This is the concrete numeric
    reflection of the abstract [sem_same_mass] predicate. *)
Lemma enumQ_expect_one_emap {A B} (f : A -> B) (mu : EnumQ A) :
  enumQ_expect (fun _ : B => 1) (emap f mu) =
  enumQ_expect (fun _ : A => 1) mu.
Proof. exact: enumQ_expect_map. Qed.

Lemma enumQ_expect_one_indexed {A} (mu : EnumQ A) :
  enumQ_expect (fun _ : nat => 1) (indexed mu) =
  enumQ_expect (fun _ : A => 1) mu.
Proof. exact: finite_index_mass. Qed.

Lemma enumQ_expect_one_prune {A} (mu : EnumQ A) :
  enumQ_expect (fun _ : A => 1) (enumQ_prune mu) =
  enumQ_expect (fun _ : A => 1) mu.
Proof. exact: finite_expect_prune_zero. Qed.

Lemma enumQ_expect_one_eqenum {A : eqType} (mu nu : EnumQ A) :
  mu ==EnumQ nu ->
  enumQ_expect (fun _ : A => 1) mu = enumQ_expect (fun _ : A => 1) nu.
Proof. exact: enumQ_weightQ_proper. Qed.

Lemma enumQ_sem_same_mass_expect_one {A B} (mu : EnumQ A) (nu : EnumQ B) :
  @sem_same_mass EnumQ EnumQ_SemanticMeasure A B mu nu ->
  enumQ_expect (fun _ : A => 1) mu = enumQ_expect (fun _ : B => 1) nu.
Proof.
  unfold sem_same_mass. cbn. unfold indexed_coupling.
  intros [j HjL HjR _].
  rewrite -(enumQ_expect_one_prune mu) -(enumQ_expect_one_prune nu).
  rewrite -(enumQ_expect_one_indexed (enumQ_prune mu)).
  rewrite -(enumQ_expect_one_indexed (enumQ_prune nu)).
  eapply eq_trans.
  - symmetry. exact (enumQ_expect_one_eqenum HjL).
  - eapply eq_trans; [exact (enumQ_expect_one_emap fst j)|].
    eapply eq_trans; [symmetry; exact (enumQ_expect_one_emap snd j)|].
    exact (enumQ_expect_one_eqenum HjR).
Qed.

(** Concrete mass-discipline regression: an empty subdistribution cannot
    be coupled with a point mass, even under the total relation. *)
Local Open Scope bool_scope.
Lemma enumQ_sem_same_mass_zero_ret_bool :
  ~ @sem_same_mass EnumQ EnumQ_SemanticMeasure bool bool
      (@enumQ_zero bool) (sem_ret true).
Proof.
  move=> H; have He := enumQ_sem_same_mass_expect_one H.
  change (0 = enumQ_expect (fun _ : bool => 1) (ret_EnumQ true)) in He.
  rewrite enumQ_expect_ret in He; discriminate.
Qed.
