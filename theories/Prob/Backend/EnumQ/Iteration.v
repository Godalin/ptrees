(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import List.

From mathcomp Require Import ssreflect ssrbool seq ssralg ssrnum order rat.
Require Import PTree.Prob.Backend.Common.RatSubTypes PTree.Prob.Backend.EnumQ.Representation.
From PTree.Prob.Interface Require Import FrontierLift.
Require Import PTree.Prob.Backend.EnumQ.FrontierLift.
Require Import PTree.Prob.Interface.Iteration.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ.
Import GRing.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

(** Integration of an arbitrary rational-valued observable against a finite
    enumeration.  Unlike [disc_mass], this does not require decidable
    equality on the carrier. *)
Fixpoint enumQ_expect {A} (f : A -> rat) (mu : EnumQ A) : rat :=
  match mu with
  | [::] => 0
  | (p, x) :: tl => Qval p * f x + enumQ_expect f tl
  end.

(** Weak convergence tested by all rational-valued observables.  This is a
    relational limit: a chain may converge mathematically while its limit is
    not representable by a finite rational [EnumQ]. *)
Definition enumQ_converges {A} (chain : nat -> EnumQ A) (mu : EnumQ A) : Prop :=
  forall P : A -> bool, forall eps : rat, 0 < eps ->
    exists N, forall n, (N <= n)%nat ->
      `|enumQ_expect (fun x => if P x then 1 else 0) (chain n) -
        enumQ_expect (fun x => if P x then 1 else 0) mu| < eps.

#[global] Instance EnumQ_MeasureOmegaInterface :
    @MeasureOmegaInterface EnumQ EnumQ_MeasureInterface := {
  meas_zero := fun A => [::];
  meas_lub := @enumQ_converges;
  meas_total := fun A mu => enumQ_expect (fun _ : A => 1) mu = 1
}.

Lemma enumQ_expect_nil {A} (f : A -> rat) :
  enumQ_expect f [::] = 0.
Proof. reflexivity. Qed.

Lemma enumQ_expect_cons {A} (f : A -> rat) p x tl :
  enumQ_expect f ((p, x) :: tl) =
    Qval p * f x + enumQ_expect f tl.
Proof. reflexivity. Qed.

Lemma enumQ_expect_ret {A} (f : A -> rat) x :
  enumQ_expect f (ret_EnumQ x) = f x.
Proof. by rewrite /ret_EnumQ /= mul1r addr0. Qed.

Lemma enumQ_expect_app {A} (f : A -> rat) (mu nu : EnumQ A) :
  enumQ_expect f (mu ++ nu) = enumQ_expect f mu + enumQ_expect f nu.
Proof.
  elim: mu=> [|[p x] mu IH] /=; first by rewrite add0r.
  by rewrite IH addrA.
Qed.

Lemma enumQ_expect_scale {A} (f : A -> rat) p (mu : EnumQ A) :
  enumQ_expect f (scale_EnumQ p mu) = Qval p * enumQ_expect f mu.
Proof.
  elim: mu=> [|[q x] mu IH] /=; first by rewrite mulr0.
  rewrite IH mulrDr. congr (_ + _).
  by rewrite !mulrA.
Qed.

Lemma enumQ_expect_bind {A B} (f : B -> rat)
    (mu : EnumQ A) (k : A -> EnumQ B) :
  enumQ_expect f (bind_EnumQ mu k) =
    enumQ_expect (fun x => enumQ_expect f (k x)) mu.
Proof.
  elim: mu=> [|[p x] mu IH] //=.
  by rewrite enumQ_expect_app enumQ_expect_scale IH.
Qed.

(** This interface intentionally has no global [MeasureOmegaLaws] instance:
    observational uniqueness of limits does not imply the current
    order-sensitive, list-shaped [EnumQ] [meas_eq]. *)
