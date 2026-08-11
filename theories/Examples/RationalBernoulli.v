Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Ring.

From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg ssrnum order
  rat.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import RatSubTypes DiscreteMC FrontierLift
  FrontierLiftEnum MeasureIteration MeasureIterationEnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.
Import GRing.Theory Num.Theory Order.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

Unset Automatic Proposition Inductives.
Variant rational_coinE : Type -> Type := .

(** Binary interval algorithm for Bernoulli(q).  At an interior state [x],
    one fair bit either terminates or moves to the fractional part of [2*x].
    Thus every round has continuation mass exactly one half, including for
    rationals with an infinite eventually-periodic binary expansion. *)
Definition binary_coin_transition (x : rat) : Enum (rat + bool) :=
  if x == 0 then ret_Enum (inr false)
  else if x == 1 then ret_Enum (inr true)
  else if x < 1 / 2 then
    [:: (one_div_two, inl (2 * x));
        (one_div_two, inr false)]
  else
    [:: (one_div_two, inr true);
        (one_div_two, inl (2 * x - 1))].

Definition binary_coin_step (x : rat) :
    ptree rational_coinE Enum (rat + bool) :=
  Prob (binary_coin_transition x) (fun next => Ret next).

Definition binary_rational_coin (q : rat) :
    ptree rational_coinE Enum bool :=
  PTree.iter binary_coin_step q.

Definition coin_potential (next : rat + bool) : rat :=
  match next with
  | inl x => x
  | inr false => 0
  | inr true => 1
  end.

Lemma one_div_two_val : Qval one_div_two = (1 / 2 : rat).
Proof. reflexivity. Qed.

Lemma half_double (x : rat) : (1 / 2 : rat) * (2 * x) = x.
Proof.
  rewrite div1r mulrA.
  have two_unit : (2 : rat) \is a GRing.unit.
  { by rewrite unitfE pnatr_eq0. }
  by rewrite (mulVr two_unit) mul1r.
Qed.

(** The desired success probability is a martingale for one binary round.
    This is the algebraic core of the eventual correctness proof. *)
Lemma binary_coin_transition_preserves_probability x :
  enum_expect coin_potential (binary_coin_transition x) = x.
Proof.
  rewrite /binary_coin_transition.
  case E0: (x == 0).
  - move/eqP: E0=> ->. rewrite enum_expect_ret. reflexivity.
  - case E1: (x == 1).
    + move/eqP: E1=> ->. rewrite enum_expect_ret. reflexivity.
    + case Ex: (x < 1 / 2); rewrite /=.
      * by rewrite !mulr0 add0r addr0 half_double.
      * rewrite mulr1 addr0 mulrBr mulr1 half_double.
        by rewrite addrC subrK.
Qed.

Lemma binary_coin_transition_total x :
  enum_expect (fun _ : rat + bool => 1)
    (binary_coin_transition x) = 1.
Proof.
  rewrite /binary_coin_transition.
  case: (x == 0); first by rewrite enum_expect_ret.
  case: (x == 1); first by rewrite enum_expect_ret.
  case: (x < 1 / 2); rewrite /= !mulr1 !addr0 -mulrDl.
  all: change ((2 : rat) / 2 = 1).
  all: by rewrite divrr // unitfE pnatr_eq0.
Qed.

(** At every nonterminal state the probability of another round is [1/2]. *)
Lemma binary_coin_transition_continue_mass x :
  x != 0 -> x != 1 ->
  enum_expect
    (fun next => match next with inl _ => 1 | inr _ => 0 end)
    (binary_coin_transition x) = 1 / 2.
Proof.
  move=> x0 x1. rewrite /binary_coin_transition (negPf x0) (negPf x1).
  case: (x < 1 / 2); rewrite /= !mulr1 !mulr0 !addr0; reflexivity.
Qed.
