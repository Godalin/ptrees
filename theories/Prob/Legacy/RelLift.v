(** Role: Retained legacy weighted-measure support. Required by explicit clients; not the native subprobability API. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Morphisms.

From mathcomp Require Import eqtype.

Require Import PTree.Prob.Legacy.RationalDiscrete.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
  Abstract relation lifting for probabilistic observations.

  This interface deliberately says nothing about the representation of a
  measure.  A finite enumeration can implement it with an explicit joint
  distribution; a measure library can implement it with its own notion of
  coupling.  The tree equivalences only consume these laws.

  The [DiscreteInterface M] parameter is present because [ptree E M R]
  currently requires it; none of the laws below inspect [disc_supp] or
  [disc_mass].  Thus an abstract measure implementation can be added as a
  separate instance without changing clients such as [PStrong].  Supporting a
  genuinely non-discrete carrier will first require weakening that constraint
  in [PTreeDefinition], which is intentionally outside this change.
*)
Class ProbRelLift (M : Type → Type) `{DiscreteInterface M} := {
  prob_lift : ∀ {A B : eqType},
      (A → B → Prop) → M A → M B → Prop;

  prob_lift_mono : ∀ {A B : eqType}
      (R S : A → B → Prop) (mu : M A) (nu : M B),
      (∀ a b, R a b → S a b) →
      prob_lift R mu nu →
      prob_lift S mu nu;

  prob_lift_proper_l : ∀ {A B : eqType}
      (R : A → B → Prop) (mu mu' : M A) (nu : M B),
      disc_eq mu mu' →
      prob_lift R mu nu →
      prob_lift R mu' nu;

  prob_lift_proper_r : ∀ {A B : eqType}
      (R : A → B → Prop) (mu : M A) (nu nu' : M B),
      disc_eq nu nu' →
      prob_lift R mu nu →
      prob_lift R mu nu';

  prob_lift_refl : ∀ {A : eqType} (mu : M A),
      prob_lift eq mu mu;

  prob_lift_of_eq : ∀ {A : eqType} (mu nu : M A),
      disc_eq mu nu →
      prob_lift eq mu nu;

  prob_lift_sym : ∀ {A B : eqType}
      (R : A → B → Prop) (mu : M A) (nu : M B),
      prob_lift R mu nu →
      prob_lift (λ b a, R a b) nu mu
}.

(** Composition is separated because many measure libraries expose coupling
    but require an additional gluing theorem for composition. *)
Class ComposableProbRelLift (M : Type → Type)
    (DI : DiscreteInterface M) (PL : @ProbRelLift M DI) := {
  prob_lift_comp : ∀ {A B C : eqType}
      (R : A → B → Prop) (S : B → C → Prop)
      (mu : M A) (nu : M B) (xi : M C),
      prob_lift R mu nu →
      prob_lift S nu xi →
      prob_lift
        (λ a c, ∃ b, R a b ∧ S b c)
        mu xi
}.
