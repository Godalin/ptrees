Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 FunctionalExtensionality.

From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg ssrnum order
  rat.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import RatSubTypes DiscreteMC FrontierLift
  FrontierLiftEnum EnumBindFacts MeasureIteration MeasureIterationEnum.
From PTree.Examples Require Import VonNeumannUnbounded RationalBernoulli.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.
Import EnumMap.
Import GRing.Theory Num.Theory Order.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

Unset Automatic Proposition Inductives.
Variant factoryE : Type -> Type := .

Section Factory.
Variables pfalse ptrue : nnQ.
Variable q : rat.

Definition factory_biased_coin : Enum bool :=
  [:: (pfalse, false); (ptrue, true)].

Definition factory_round_measure : Enum (unit + bool) :=
  bind_Enum factory_biased_coin (fun b1 =>
    bind_Enum factory_biased_coin (fun b2 =>
      ret_Enum (vn_round_result b1 b2))).

Definition factory_vn_step (_ : unit) :
    ptree factoryE Enum (unit + bool) :=
  Prob factory_biased_coin (fun b1 =>
    Prob factory_biased_coin (fun b2 => Ret (vn_round_result b1 b2))).

Definition factory_fair_coin : ptree factoryE Enum bool :=
  PTree.iter factory_vn_step tt.

Lemma factory_round_is_param_round :
  factory_round_measure = param_round_measure pfalse ptrue.
Proof. reflexivity. Qed.

Hypothesis pnormalized : Qval pfalse + Qval ptrue = 1.
Hypothesis pnontrivial : 0 < Qval pfalse * Qval ptrue.

Definition binary_round_result (x : rat) (b : bool) : rat + bool :=
  if x < 1 / 2 then
    if b then inr false else inl (2 * x)
  else
    if b then inl (2 * x - 1) else inr true.

Lemma fair_binary_round_measure x :
  bind_Enum vn_fair (fun b => ret_Enum (binary_round_result x b)) =
  binary_coin_transition x.
Proof.
  rewrite /vn_fair /binary_round_result /binary_coin_transition.
  by case: (x < 1 / 2); rewrite /bind_Enum /ret_Enum /= !mulr1.
Qed.

Definition factory_binary_step (x : rat) :
    ptree factoryE Enum (rat + bool) :=
  PTree.bind factory_fair_coin (fun b => Ret (binary_round_result x b)).

Definition biased_to_rational_coin : ptree factoryE Enum bool :=
  PTree.iter factory_binary_step q.

Definition factory_direct_q (q0 : 0 <= q) (q1 : q <= 1) :
    ptree factoryE Enum bool :=
  Prob (rational_bernoulli_measure q0 q1) (fun b => Ret b).

End Factory.

(** A closed, non-trivial executable instance: two tosses of the [1/3]
    source coin are repeatedly von-Neumann-filtered, and the resulting fair
    bits drive the binary algorithm for a [2/5] target coin. *)
Definition third_to_two_fifths : ptree factoryE Enum bool :=
  biased_to_rational_coin vn_one_third vn_two_thirds (2 / 5).

Lemma third_bias_normalized :
  Qval vn_one_third + Qval vn_two_thirds = 1.
Proof.
  change ((1 / 3 : rat) + 2 / 3 = 1).
  ring_to_rat; reflexivity.
Qed.

Lemma third_bias_nontrivial :
  0 < Qval vn_one_third * Qval vn_two_thirds.
Proof.
  change (0 < (1 / 3 : rat) * (2 / 3)).
  apply mulr_gt0.
  - apply divr_gt0; [exact (@ltr0Sn rat 0) | exact (@ltr0Sn rat 2)].
  - apply divr_gt0; [exact (@ltr0Sn rat 1) | exact (@ltr0Sn rat 2)].
Qed.

Lemma two_fifths_nonnegative : (0 : rat) <= 2 / 5.
Proof. exact (ltW (divr_gt0 (@ltr0Sn rat 1) (@ltr0Sn rat 4))). Qed.

Lemma two_fifths_at_most_one : (2 / 5 : rat) <= 1.
Proof.
  apply ler_pdivrMr; exact (@ltr0Sn rat 4).
Qed.

Definition direct_two_fifths : ptree factoryE Enum bool :=
  factory_direct_q (q := 2 / 5)
    two_fifths_nonnegative two_fifths_at_most_one.
