(** Role: Generic measure interfaces. Depends on probability interfaces; provides operations/laws, not tree semantics. *)
From Coq Require Import Utf8.

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
Class MeasureInterface (M : Type → Type) := {
  meas_ret : ∀ {A}, A → M A;
  meas_bind : ∀ {A B}, M A → (A → M B) → M B;
  meas_eq : ∀ {A}, M A → M A → Prop;
  meas_ae : ∀ {A}, M A → (A → Prop) → Prop;

  meas_lift : ∀ {A B},
      (A → B → Prop) → M A → M B → Prop
}.

(** A polymorphic zero measure is needed whenever an AE-defined kernel must
    be represented as a total Coq function.  Values on null branches are
    semantically irrelevant, but still require a measure inhabitant. *)
Class MeasureZeroInterface (M : Type → Type) := {
  meas_empty : ∀ {A}, M A
}.

(** The basic finite-measure law package.  Stronger laws below are needed by
    compositionality and coupling-transitivity proofs. *)
Class MeasureCoreLaws (M : Type → Type) `{MI : MeasureInterface M} := {
  meas_ae_mono : ∀ {A} (mu : M A) (P Q : A → Prop),
      (∀ x, P x → Q x) → meas_ae mu P → meas_ae mu Q;
  meas_lift_mono : ∀ {A B} (R S : A → B → Prop) mu nu,
      (∀ x y, R x y → S x y) →
      meas_lift R mu nu → meas_lift S mu nu;
  meas_lift_refl : ∀ {A} (R : A → A → Prop) mu,
      Reflexive R → meas_lift R mu mu;
  meas_lift_ret : ∀ {A B} (R : A → B → Prop) x y,
      R x y → meas_lift R (meas_ret x) (meas_ret y)
}.

(** Laws used by the coinductive relation.  A continuous implementation can
    read [meas_lift R mu nu] as existence of a coupling whose joint measure is
    concentrated on [R]. *)
Class MeasureLaws (M : Type → Type) `{MI : MeasureInterface M}
    `{MC : @MeasureCoreLaws M MI} := {
  meas_eq_refl : ∀ A, Reflexive (@meas_eq M MI A);
  meas_eq_sym : ∀ A, Symmetric (@meas_eq M MI A);
  meas_eq_trans : ∀ A, Transitive (@meas_eq M MI A);

  meas_ae_true : ∀ {A} (mu : M A), meas_ae mu (λ _, True);
  meas_ae_conj : ∀ {A} (mu : M A) (P Q : A → Prop),
      meas_ae mu P → meas_ae mu Q →
      meas_ae mu (λ x, P x ∧ Q x);
  meas_lift_proper_l : ∀ {A B} (R : A → B → Prop) mu mu' nu,
      meas_eq mu mu' → meas_lift R mu nu → meas_lift R mu' nu;
  meas_lift_proper_r : ∀ {A B} (R : A → B → Prop) mu nu nu',
      meas_eq nu nu' → meas_lift R mu nu → meas_lift R mu nu';
  meas_lift_sym : ∀ {A B} (R : A → B → Prop) mu nu,
      meas_lift R mu nu → meas_lift (λ y x, R x y) nu mu;
  meas_lift_comp : ∀ {A B C}
      (R : A → B → Prop) (S : B → C → Prop) mu nu xi,
      meas_lift R mu nu → meas_lift S nu xi →
      meas_lift (λ x z, ∃ y, R x y ∧ S y z) mu xi
}.

(** Congruence of integration/bind under almost-everywhere equality.  It is
    separated because it is the measure-theoretic ingredient needed to prove
    uniqueness of finite frontiers. *)
Class MeasureBindLaws (M : Type → Type) `{MI : MeasureInterface M} := {
  meas_bind_ae_proper : ∀ {A B} (mu : M A)
      (k1 k2 : A → M B),
      meas_ae mu (λ x, meas_eq (k1 x) (k2 x)) →
      meas_eq (meas_bind mu k1) (meas_bind mu k2)
}.

(** Relational Kleisli compatibility for coupling liftings.  It composes a
    coupling of source samples with a coupling of every related pair of
    continuation measures.  This is the probabilistic analogue of the
    relational bind rule and is strictly more general than congruence of
    bind under [meas_eq]. *)
Class MeasureLiftBindLaws (M : Type → Type)
    `{MI : MeasureInterface M} := {
  meas_lift_bind : ∀ {A B C D}
      (R : A → B → Prop) (S : C → D → Prop)
      (mu : M A) (nu : M B) (k : A → M C) (h : B → M D),
      meas_lift R mu nu →
      (∀ x y, R x y → meas_lift S (k x) (h y)) →
      meas_lift S (meas_bind mu k) (meas_bind nu h)
}.

(** Almost-everywhere relational Kleisli compatibility.  Finite frontiers
    deliberately need continuation frontiers only on non-zero branches, so
    the unconditional rule above cannot express their probabilistic case:
    zero-mass continuations may have no finite frontier at all. *)
Class MeasureLiftAELaws (M : Type → Type)
    `{MI : MeasureInterface M} := {
  meas_lift_ae_transport_r : ∀ {A B}
      (R : A → B → Prop) (mu : M A) (nu : M B) (P : A → Prop),
      meas_lift R mu nu → meas_ae mu P →
      meas_ae nu (λ y, ∃ x, R x y ∧ P x);
  meas_lift_bind_ae : ∀ {A B C D}
      (R : A → B → Prop) (S : C → D → Prop)
      (mu : M A) (nu : M B) (k : A → M C) (h : B → M D)
      (P : A → Prop) (Q : B → Prop),
      meas_lift R mu nu → meas_ae mu P → meas_ae nu Q →
      (∀ x y, R x y → P x → Q y →
        meas_lift S (k x) (h y)) →
      meas_lift S (meas_bind mu k) (meas_bind nu h)
}.

(** Extensional equality is a congruence for the measure monad and for
    almost-everywhere predicates.  This separates semantic equality from
    any concrete representation equality used by a backend. *)
Class MeasureCongruenceLaws (M : Type → Type)
    `{MI : MeasureInterface M} := {
  meas_ret_proper : ∀ {A} (x y : A),
      x = y → meas_eq (meas_ret x) (meas_ret y);
  meas_bind_proper : ∀ {A B} (mu nu : M A)
      (k h : A → M B),
      meas_eq mu nu →
      (∀ x, meas_eq (k x) (h x)) →
      meas_eq (meas_bind mu k) (meas_bind nu h);
  meas_ae_proper : ∀ {A} (mu nu : M A) (P : A → Prop),
      meas_eq mu nu → (meas_ae mu P ↔ meas_ae nu P)
}.

(** Extensional monad equations used to normalize finite probabilistic
    computations.  A backend need not expose any representation-level
    equality for these laws. *)
Class MeasureMonadLaws (M : Type → Type)
    `{MI : MeasureInterface M} := {
  meas_ae_ret : ∀ {A} (x : A) (P : A → Prop),
      P x → meas_ae (meas_ret x) P;
  meas_bind_ret_l : ∀ {A B} (x : A) (k : A → M B),
      meas_eq (meas_bind (meas_ret x) k) (k x);
  meas_bind_assoc : ∀ {A B C} (mu : M A)
      (k : A → M B) (h : B → M C),
      meas_eq
        (meas_bind (meas_bind mu k) h)
        (meas_bind mu (λ x, meas_bind (k x) h))
}.

(** Kleisli extension of almost-everywhere predicates. *)
Class MeasureAEKleisliLaws (M : Type → Type)
    `{MI : MeasureInterface M} := {
  meas_ae_bind : ∀ {A B} (mu : M A) (k : A → M B)
      (P : A → Prop) (Q : B → Prop),
      meas_ae mu P →
      (∀ x, P x → meas_ae (k x) Q) →
      meas_ae (meas_bind mu k) Q
}.

(** Relational Fubini law for two independent samples.  It is stated through
    [meas_lift], rather than [meas_eq], so the result types need neither
    decidable equality nor a canonical enumeration order.  Keeping this in a
    separate class allows non-commutative measure-like effects to use the
    basic weak-bisimulation development. *)
Class MeasureCommutativeLaws (M : Type → Type)
    `{MI : MeasureInterface M} := {
  meas_lift_bind_ret_exchange : ∀ {A B : eqType} {C D}
      (R : C → D → Prop) (mu : M A) (nu : M B)
      (f : A → B → C) (g : B → A → D),
      (∀ x y, R (f x y) (g y x)) →
      meas_lift R
        (meas_bind mu (λ x,
          meas_bind nu (λ y, meas_ret (f x y))))
        (meas_bind nu (λ y,
          meas_bind mu (λ x, meas_ret (g y x))))
}.

(** Full relational Fubini law for Kleisli kernels.  Unlike
    [MeasureCommutativeLaws], whose terminal computations are Dirac masses,
    this interface permits each pair of samples to continue with an
    arbitrary measure.  It is kept separate because proving it for a
    concrete representation requires a bind-preservation theorem for that
    representation's coupling. *)
Class MeasureKleisliCommutativeLaws (M : Type → Type)
    `{MI : MeasureInterface M} := {
  meas_lift_bind_exchange : ∀ {A B : eqType} {C D}
      (R : C → D → Prop) (mu : M A) (nu : M B)
      (k1 : A → B → M C) (k2 : B → A → M D),
      (∀ x y, meas_lift R (k1 x y) (k2 y x)) →
      meas_lift R
        (meas_bind mu (λ x, meas_bind nu (λ y, k1 x y)))
        (meas_bind nu (λ y, meas_bind mu (λ x, k2 y x)))
}.

#[global] Instance meas_eq_equivalence
    {M} `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}
    `{ML : @MeasureLaws M MI MC} A :
  Equivalence (@meas_eq M MI A).
Proof.
  split; [apply meas_eq_refl | apply meas_eq_sym | apply meas_eq_trans].
Qed.
