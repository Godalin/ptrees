Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import List.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat ssralg ssrnum order rat.
From PTree.Prob Require Import DiscreteMC Coupling IndexedCoupling FrontierLift
  FrontierLiftEnum MeasureIteration MeasureIterationEnum TwoLevelMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.
Import EnumMap Coupling IndexedCoupling.
Import RatSubTypes.
Import GRing.Theory Order.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

(** Compatibility adapter: Enum implements both layers of the new model with
    the same concrete representation.  The distinction remains visible to
    the generic theory even though it collapses in this instance. *)
#[global] Instance Enum_SemanticMeasureInterface :
    SemanticMeasureInterface Enum := {
  sem_ret := @meas_ret Enum Enum_MeasureInterface;
  sem_bind := @meas_bind Enum Enum_MeasureInterface;
  sem_eq := @meas_eq Enum Enum_MeasureInterface;
  sem_ae := @meas_ae Enum Enum_MeasureInterface;
  sem_lift := @meas_lift Enum Enum_MeasureInterface
}.

#[global] Instance Enum_SemanticMeasureCoreLaws :
    @SemanticMeasureCoreLaws Enum Enum_SemanticMeasureInterface.
Proof.
  constructor.
  - exact (@meas_eq_refl Enum Enum_MeasureInterface
      Enum_MeasureCoreLaws Enum_MeasureLaws).
  - exact (@meas_eq_sym Enum Enum_MeasureInterface
      Enum_MeasureCoreLaws Enum_MeasureLaws).
  - exact (@meas_eq_trans Enum Enum_MeasureInterface
      Enum_MeasureCoreLaws Enum_MeasureLaws).
  - exact (@meas_ae_true Enum Enum_MeasureInterface
      Enum_MeasureCoreLaws Enum_MeasureLaws).
  - exact (@meas_ae_mono Enum Enum_MeasureInterface
      Enum_MeasureCoreLaws).
  - exact (@meas_ae_conj Enum Enum_MeasureInterface
      Enum_MeasureCoreLaws Enum_MeasureLaws).
  - exact (@meas_lift_mono Enum Enum_MeasureInterface
      Enum_MeasureCoreLaws).
  - exact (@meas_lift_refl Enum Enum_MeasureInterface
      Enum_MeasureCoreLaws).
  - exact (@meas_lift_ret Enum Enum_MeasureInterface
      Enum_MeasureCoreLaws).
  - exact (@meas_lift_proper_l Enum Enum_MeasureInterface
      Enum_MeasureCoreLaws Enum_MeasureLaws).
  - exact (@meas_lift_proper_r Enum Enum_MeasureInterface
      Enum_MeasureCoreLaws Enum_MeasureLaws).
  - exact (@meas_lift_sym Enum Enum_MeasureInterface
      Enum_MeasureCoreLaws Enum_MeasureLaws).
  - exact (@meas_lift_comp Enum Enum_MeasureInterface
      Enum_MeasureCoreLaws Enum_MeasureLaws).
Qed.

#[global] Instance Enum_SemanticMeasureAELiftLaws :
    @SemanticMeasureAELiftLaws Enum Enum_SemanticMeasureInterface.
Proof.
  constructor. move=> A mu P Hae. cbn in Hae |- *.
  unfold enum_meas_eq.
  eapply (coupling_mono (R := eq));
    [|exact (coupling_refl (indexed (enum_prune mu)))].
  move=> i j ->. split.
  - move=> p x Hi. exists p, x. split; first exact Hi.
    split; first reflexivity.
    have Hin : List.In (p, x) (enum_prune mu).
    { eapply nth_error_In. exact Hi. }
    have [Hsrc Hnz] := enum_prune_in_source Hin.
    exact (Hae p x Hsrc Hnz).
  - move=> p x Hi. exists p, x. split; first exact Hi.
    split; first reflexivity.
    have Hin : List.In (p, x) (enum_prune mu).
    { eapply nth_error_In. exact Hi. }
    have [Hsrc Hnz] := enum_prune_in_source Hin.
    exact (Hae p x Hsrc Hnz).
Qed.

#[global] Instance Enum_SemanticMeasureAEKleisliLaws :
    @SemanticMeasureAEKleisliLaws Enum Enum_SemanticMeasureInterface.
Proof.
  constructor.
  - intros A P x Hx. exact (@meas_ae_ret Enum Enum_MeasureInterface
      Enum_MeasureMonadLaws A x P Hx).
  - exact (@meas_ae_bind Enum Enum_MeasureInterface
      Enum_MeasureAEKleisliLaws).
Qed.

#[global] Instance Enum_SemanticMeasureCouplingAELaws :
    @SemanticMeasureCouplingAELaws Enum Enum_SemanticMeasureInterface.
Proof.
  constructor.
  - exact (@meas_lift_ae_transport_r Enum Enum_MeasureInterface
      Enum_MeasureLiftAELaws).
  - move=> A B R mu nu P Q Hlift HP HQ.
  cbn in Hlift, HP, HQ |- *.
  unfold indexed_coupling in Hlift |- *.
  eapply coupling_mono; [|exact Hlift].
  move=> i j [HL HR]. split.
  - move=> p x Hi.
    move: (HL p x Hi)=> [q [y [Hj Hxy]]].
    exists q, y. split; [exact Hj|]. split; [exact Hxy|]. split.
    + have Hin := @nth_error_In _ (enum_prune mu) i (p, x) Hi.
      have [Hsrc Hnz] := enum_prune_in_source Hin.
      exact (HP p x Hsrc Hnz).
    + have Hin := @nth_error_In _ (enum_prune nu) j (q, y) Hj.
      have [Hsrc Hnz] := enum_prune_in_source Hin.
      exact (HQ q y Hsrc Hnz).
  - move=> q y Hj.
    move: (HR q y Hj)=> [p [x [Hi Hxy]]].
    exists p, x. split; [exact Hi|]. split; [exact Hxy|]. split.
    + have Hin := @nth_error_In _ (enum_prune mu) i (p, x) Hi.
      have [Hsrc Hnz] := enum_prune_in_source Hin.
      exact (HP p x Hsrc Hnz).
    + have Hin := @nth_error_In _ (enum_prune nu) j (q, y) Hj.
      have [Hsrc Hnz] := enum_prune_in_source Hin.
      exact (HQ q y Hsrc Hnz).
Qed.

#[global] Instance Enum_SemanticMeasureCountableAELaws :
    @SemanticMeasureCountableAELaws Enum Enum_SemanticMeasureInterface.
Proof.
  constructor. intros A mu P HP p x Hin Hnz n.
  exact (HP n p x Hin Hnz).
Qed.

(** Eventwise order on finite rational measures.  Enum is not globally
    omega-complete, so this adapter intentionally provides the omega
    operations but no unconditional [SemanticOmegaLaws] instance. *)
Definition enum_sem_le {A} (mu nu : Enum A) : Prop :=
  forall P : A -> bool,
    enum_expect (fun x => if P x then 1 else 0) mu <=
    enum_expect (fun x => if P x then 1 else 0) nu.

#[global] Instance Enum_SemanticOmegaInterface :
    @SemanticOmegaInterface Enum Enum_SemanticMeasureInterface := {
  sem_zero := fun A => @nil (RatSubTypes.nnQ * A);
  sem_le := @enum_sem_le;
  sem_lub := @enum_converges;
  sem_total := fun A mu => enum_expect (fun _ : A => 1) mu = 1
}.

#[global] Instance Enum_SemanticMeasureBindLaws :
    @SemanticMeasureBindLaws Enum Enum_SemanticMeasureInterface.
Proof.
  constructor.
  - exact (@meas_bind_ret_l Enum Enum_MeasureInterface
      Enum_MeasureMonadLaws).
  - exact (@meas_bind_assoc Enum Enum_MeasureInterface
      Enum_MeasureMonadLaws).
  - exact (@meas_bind_ae_proper Enum Enum_MeasureInterface
      Enum_MeasureBindLaws).
  - exact (@meas_lift_bind Enum Enum_MeasureInterface
      Enum_MeasureLiftBindLaws).
Qed.

#[global] Instance Enum_MixedMeasureInterface :
    MixedMeasureInterface Enum Enum := {
  mixed_bind := @meas_bind Enum Enum_MeasureInterface
}.

#[global] Instance Enum_MixedMeasureLaws :
    @MixedMeasureLaws Enum Enum
      Enum_SemanticMeasureInterface Enum_SemanticMeasureInterface
      Enum_MixedMeasureInterface.
Proof.
  constructor.
  - exact (@meas_bind_ae_proper Enum Enum_MeasureInterface
      Enum_MeasureBindLaws).
  - exact (@meas_bind_assoc Enum Enum_MeasureInterface
      Enum_MeasureMonadLaws).
  - exact (@meas_lift_bind Enum Enum_MeasureInterface
      Enum_MeasureLiftBindLaws).
Qed.

(** Concrete mass-discipline regression: an empty subdistribution cannot
    be coupled with a point mass, even under the total relation. *)
Local Open Scope bool_scope.
Lemma enum_sem_same_mass_zero_ret_bool :
  ~ @sem_same_mass Enum Enum_SemanticMeasureInterface bool bool
      (@nil (RatSubTypes.nnQ * bool)) (sem_ret true).
Proof.
  unfold sem_same_mass. cbn.
  unfold indexed_coupling. intros [j HjL HjR Hrelated].
  have Hright : acc_mass 0 (emap snd j) != 0.
  { rewrite (HjR 0). cbn [indexed index_from enum_prune ret_Enum acc_mass].
    done. }
  move: (@emap_nonzero_preimage _ _ snd j 0 Hright)=>
    [[i q] [Hjoint Hq]].
  move: (joint_nonzero_marginals Hjoint)=> [Hleft _].
  move: Hleft. rewrite (HjL i).
  cbn [indexed index_from enum_prune acc_mass].
  done.
Qed.
