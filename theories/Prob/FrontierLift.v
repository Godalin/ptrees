Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A measure-monad interface for weak probabilistic bisimulation.

    The interface is deliberately independent of [DiscreteInterface].  In
    particular, neither carriers nor frontier values need decidable equality.
    [meas_ae mu P] is the assertion that [P] holds [mu]-almost everywhere. *)
Class MeasureInterface (M : Type -> Type) := {
  meas_ret : forall {A}, A -> M A;
  meas_bind : forall {A B}, M A -> (A -> M B) -> M B;
  meas_eq : forall {A}, M A -> M A -> Prop;
  meas_ae : forall {A}, M A -> (A -> Prop) -> Prop;

  meas_lift : forall {A B},
      (A -> B -> Prop) -> M A -> M B -> Prop
}.

(** The small law package needed merely to define [apweak] and prove
    reflexivity.  Stronger laws below are only needed by compositionality and
    transitivity proofs. *)
Class MeasureCoreLaws (M : Type -> Type) `{MI : MeasureInterface M} := {
  meas_ae_mono : forall {A} (mu : M A) (P Q : A -> Prop),
      (forall x, P x -> Q x) -> meas_ae mu P -> meas_ae mu Q;
  meas_lift_mono : forall {A B} (R S : A -> B -> Prop) mu nu,
      (forall x y, R x y -> S x y) ->
      meas_lift R mu nu -> meas_lift S mu nu;
  meas_lift_refl : forall {A} (R : A -> A -> Prop) mu,
      Reflexive R -> meas_lift R mu mu;
  meas_lift_ret : forall {A B} (R : A -> B -> Prop) x y,
      R x y -> meas_lift R (meas_ret x) (meas_ret y)
}.

(** Laws used by the coinductive relation.  A continuous implementation can
    read [meas_lift R mu nu] as existence of a coupling whose joint measure is
    concentrated on [R]. *)
Class MeasureLaws (M : Type -> Type) `{MI : MeasureInterface M}
    `{MC : @MeasureCoreLaws M MI} := {
  meas_eq_refl : forall A, Reflexive (@meas_eq M MI A);
  meas_eq_sym : forall A, Symmetric (@meas_eq M MI A);
  meas_eq_trans : forall A, Transitive (@meas_eq M MI A);

  meas_ae_true : forall {A} (mu : M A), meas_ae mu (fun _ => True);
  meas_ae_conj : forall {A} (mu : M A) (P Q : A -> Prop),
      meas_ae mu P -> meas_ae mu Q ->
      meas_ae mu (fun x => P x /\ Q x);
  meas_lift_proper_l : forall {A B} (R : A -> B -> Prop) mu mu' nu,
      meas_eq mu mu' -> meas_lift R mu nu -> meas_lift R mu' nu;
  meas_lift_proper_r : forall {A B} (R : A -> B -> Prop) mu nu nu',
      meas_eq nu nu' -> meas_lift R mu nu -> meas_lift R mu nu';
  meas_lift_sym : forall {A B} (R : A -> B -> Prop) mu nu,
      meas_lift R mu nu -> meas_lift (fun y x => R x y) nu mu;
  meas_lift_comp : forall {A B C}
      (R : A -> B -> Prop) (S : B -> C -> Prop) mu nu xi,
      meas_lift R mu nu -> meas_lift S nu xi ->
      meas_lift (fun x z => exists y, R x y /\ S y z) mu xi
}.

(** Congruence of integration/bind under almost-everywhere equality.  It is
    separated because it is the measure-theoretic ingredient needed to prove
    uniqueness of finite frontiers. *)
Class MeasureBindLaws (M : Type -> Type) `{MI : MeasureInterface M} := {
  meas_bind_ae_proper : forall {A B} (mu : M A)
      (k1 k2 : A -> M B),
      meas_ae mu (fun x => meas_eq (k1 x) (k2 x)) ->
      meas_eq (meas_bind mu k1) (meas_bind mu k2)
}.

(** Kleisli extension of almost-everywhere predicates. *)
Class MeasureAEKleisliLaws (M : Type -> Type)
    `{MI : MeasureInterface M} := {
  meas_ae_bind : forall {A B} (mu : M A) (k : A -> M B)
      (P : A -> Prop) (Q : B -> Prop),
      meas_ae mu P ->
      (forall x, P x -> meas_ae (k x) Q) ->
      meas_ae (meas_bind mu k) Q
}.

#[global] Instance meas_eq_equivalence
    {M} `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}
    `{ML : @MeasureLaws M MI MC} A :
  Equivalence (@meas_eq M MI A).
Proof.
  split; [apply meas_eq_refl | apply meas_eq_sym | apply meas_eq_trans].
Qed.
