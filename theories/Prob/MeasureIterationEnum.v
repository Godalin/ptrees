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
  forall P : A -> bool, forall eps : rat, 0 < eps ->
    exists N, forall n, (N <= n)%nat ->
      `|enum_expect (fun x => if P x then 1 else 0) (chain n) -
        enum_expect (fun x => if P x then 1 else 0) mu| < eps.

#[global] Instance Enum_MeasureOmegaInterface :
    @MeasureOmegaInterface Enum Enum_MeasureInterface := {
  meas_zero := fun A => [::];
  meas_lub := @enum_converges;
  meas_total := fun A mu => enum_expect (fun _ : A => 1) mu = 1
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

Lemma enum_expect_app {A} (f : A -> rat) (mu nu : Enum A) :
  enum_expect f (mu ++ nu) = enum_expect f mu + enum_expect f nu.
Proof.
  elim: mu=> [|[p x] mu IH] /=; first by rewrite add0r.
  by rewrite IH addrA.
Qed.

Lemma enum_expect_scale {A} (f : A -> rat) p (mu : Enum A) :
  enum_expect f (scale_Enum p mu) = Qval p * enum_expect f mu.
Proof.
  elim: mu=> [|[q x] mu IH] /=; first by rewrite mulr0.
  rewrite IH mulrDr. congr (_ + _).
  by rewrite !mulrA.
Qed.

Lemma enum_expect_bind {A B} (f : B -> rat)
    (mu : Enum A) (k : A -> Enum B) :
  enum_expect f (bind_Enum mu k) =
    enum_expect (fun x => enum_expect f (k x)) mu.
Proof.
  elim: mu=> [|[p x] mu IH] //=.
  by rewrite enum_expect_app enum_expect_scale IH.
Qed.

(** This interface intentionally has no global [MeasureOmegaLaws] instance:
    observational uniqueness of limits does not imply the current
    order-sensitive, list-shaped [Enum] [meas_eq]. *)
