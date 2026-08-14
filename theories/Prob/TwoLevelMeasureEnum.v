Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order rat.
From PTree.Prob Require Import DiscreteMC FrontierLift FrontierLiftEnum
  MeasureIteration MeasureIterationEnum TwoLevelMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.
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
  - exact (@meas_lift_mono Enum Enum_MeasureInterface
      Enum_MeasureCoreLaws).
  - exact (@meas_lift_refl Enum Enum_MeasureInterface
      Enum_MeasureCoreLaws).
  - exact (@meas_lift_ret Enum Enum_MeasureInterface
      Enum_MeasureCoreLaws).
  - exact (@meas_lift_sym Enum Enum_MeasureInterface
      Enum_MeasureCoreLaws Enum_MeasureLaws).
  - exact (@meas_lift_comp Enum Enum_MeasureInterface
      Enum_MeasureCoreLaws Enum_MeasureLaws).
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
  - exact (@meas_lift_bind Enum Enum_MeasureInterface
      Enum_MeasureLiftBindLaws).
Qed.
