Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Morphisms.

From mathcomp Require Import eqtype.

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

(** Relational Kleisli compatibility for coupling liftings.  It composes a
    coupling of source samples with a coupling of every related pair of
    continuation measures.  This is the probabilistic analogue of the
    relational bind rule and is strictly more general than congruence of
    bind under [meas_eq]. *)
Class MeasureLiftBindLaws (M : Type -> Type)
    `{MI : MeasureInterface M} := {
  meas_lift_bind : forall {A B C D}
      (R : A -> B -> Prop) (S : C -> D -> Prop)
      (mu : M A) (nu : M B) (k : A -> M C) (h : B -> M D),
      meas_lift R mu nu ->
      (forall x y, R x y -> meas_lift S (k x) (h y)) ->
      meas_lift S (meas_bind mu k) (meas_bind nu h)
}.

(** Almost-everywhere relational Kleisli compatibility.  Finite frontiers
    deliberately need continuation frontiers only on non-zero branches, so
    the unconditional rule above cannot express their probabilistic case:
    zero-mass continuations may have no finite frontier at all. *)
Class MeasureLiftAELaws (M : Type -> Type)
    `{MI : MeasureInterface M} := {
  meas_lift_ae_transport_r : forall {A B}
      (R : A -> B -> Prop) (mu : M A) (nu : M B) (P : A -> Prop),
      meas_lift R mu nu -> meas_ae mu P ->
      meas_ae nu (fun y => exists x, R x y /\ P x);
  meas_lift_bind_ae : forall {A B C D}
      (R : A -> B -> Prop) (S : C -> D -> Prop)
      (mu : M A) (nu : M B) (k : A -> M C) (h : B -> M D)
      (P : A -> Prop) (Q : B -> Prop),
      meas_lift R mu nu -> meas_ae mu P -> meas_ae nu Q ->
      (forall x y, R x y -> P x -> Q y ->
        meas_lift S (k x) (h y)) ->
      meas_lift S (meas_bind mu k) (meas_bind nu h)
}.

(** Extensional equality is a congruence for the measure monad and for
    almost-everywhere predicates.  This separates semantic equality from
    any concrete representation equality used by a backend. *)
Class MeasureCongruenceLaws (M : Type -> Type)
    `{MI : MeasureInterface M} := {
  meas_ret_proper : forall {A} (x y : A),
      x = y -> meas_eq (meas_ret x) (meas_ret y);
  meas_bind_proper : forall {A B} (mu nu : M A)
      (k h : A -> M B),
      meas_eq mu nu ->
      (forall x, meas_eq (k x) (h x)) ->
      meas_eq (meas_bind mu k) (meas_bind nu h);
  meas_ae_proper : forall {A} (mu nu : M A) (P : A -> Prop),
      meas_eq mu nu -> (meas_ae mu P <-> meas_ae nu P)
}.

(** Extensional monad equations used to normalize finite probabilistic
    computations.  A backend need not expose any representation-level
    equality for these laws. *)
Class MeasureMonadLaws (M : Type -> Type)
    `{MI : MeasureInterface M} := {
  meas_ae_ret : forall {A} (x : A) (P : A -> Prop),
      P x -> meas_ae (meas_ret x) P;
  meas_bind_ret_l : forall {A B} (x : A) (k : A -> M B),
      meas_eq (meas_bind (meas_ret x) k) (k x);
  meas_bind_assoc : forall {A B C} (mu : M A)
      (k : A -> M B) (h : B -> M C),
      meas_eq
        (meas_bind (meas_bind mu k) h)
        (meas_bind mu (fun x => meas_bind (k x) h))
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

(** Relational Fubini law for two independent samples.  It is stated through
    [meas_lift], rather than [meas_eq], so the result types need neither
    decidable equality nor a canonical enumeration order.  Keeping this in a
    separate class allows non-commutative measure-like effects to use the
    basic weak-bisimulation development. *)
Class MeasureCommutativeLaws (M : Type -> Type)
    `{MI : MeasureInterface M} := {
  meas_lift_bind_ret_exchange : forall {A B : eqType} {C D}
      (R : C -> D -> Prop) (mu : M A) (nu : M B)
      (f : A -> B -> C) (g : B -> A -> D),
      (forall x y, R (f x y) (g y x)) ->
      meas_lift R
        (meas_bind mu (fun x =>
          meas_bind nu (fun y => meas_ret (f x y))))
        (meas_bind nu (fun y =>
          meas_bind mu (fun x => meas_ret (g y x))))
}.

(** Full relational Fubini law for Kleisli kernels.  Unlike
    [MeasureCommutativeLaws], whose terminal computations are Dirac masses,
    this interface permits each pair of samples to continue with an
    arbitrary measure.  It is kept separate because proving it for a
    concrete representation requires a bind-preservation theorem for that
    representation's coupling. *)
Class MeasureKleisliCommutativeLaws (M : Type -> Type)
    `{MI : MeasureInterface M} := {
  meas_lift_bind_exchange : forall {A B : eqType} {C D}
      (R : C -> D -> Prop) (mu : M A) (nu : M B)
      (k1 : A -> B -> M C) (k2 : B -> A -> M D),
      (forall x y, meas_lift R (k1 x y) (k2 y x)) ->
      meas_lift R
        (meas_bind mu (fun x => meas_bind nu (fun y => k1 x y)))
        (meas_bind nu (fun y => meas_bind mu (fun x => k2 y x)))
}.

#[global] Instance meas_eq_equivalence
    {M} `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}
    `{ML : @MeasureLaws M MI MC} A :
  Equivalence (@meas_eq M MI A).
Proof.
  split; [apply meas_eq_refl | apply meas_eq_sym | apply meas_eq_trans].
Qed.
