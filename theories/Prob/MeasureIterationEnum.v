Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import List.

From mathcomp Require Import ssreflect ssrbool seq ssralg ssrnum order rat.
From PTree.Prob Require Import RatSubTypes DiscreteMC FrontierLift
  FrontierLiftEnum MeasureIteration.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.
Import GRing.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

(** Integration of an arbitrary rational-valued observable against a finite
    enumeration.  Unlike [disc_mass], this does not require decidable
    equality on the carrier. *)
Fixpoint enum_expect {A} (f : A -> rat) (mu : Enum A) : rat :=
  match mu with
  | [::] => 0
  | (p, x) :: tl => Qval p * f x + enum_expect f tl
  end.

(** Weak convergence tested by all rational-valued observables.  This is a
    relational limit: a chain may converge mathematically while its limit is
    not representable by a finite rational [Enum]. *)
Definition enum_converges {A} (chain : nat -> Enum A) (mu : Enum A) : Prop :=
  forall f : A -> rat, forall eps : rat, 0 < eps ->
    exists N, forall n, (N <= n)%nat ->
      `|enum_expect f (chain n) - enum_expect f mu| < eps.

#[global] Instance Enum_MeasureOmegaInterface :
    @MeasureOmegaInterface Enum Enum_MeasureInterface := {
  meas_zero := fun A => [::];
  meas_lub := @enum_converges
}.

Lemma enum_expect_nil {A} (f : A -> rat) :
  enum_expect f [::] = 0.
Proof. reflexivity. Qed.

Lemma enum_expect_cons {A} (f : A -> rat) p x tl :
  enum_expect f ((p, x) :: tl) =
    Qval p * f x + enum_expect f tl.
Proof. reflexivity. Qed.

Lemma enum_expect_ret {A} (f : A -> rat) x :
  enum_expect f (ret_Enum x) = f x.
Proof. by rewrite /ret_Enum /= mul1r addr0. Qed.

(** This interface intentionally has no global [MeasureOmegaLaws] instance:
    observational uniqueness of limits does not imply the current
    order-sensitive, list-shaped [Enum] [meas_eq]. *)
