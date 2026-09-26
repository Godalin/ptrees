(** Case role: shared supporting program.
    Reading entry: biased_to_rational_coin; fair_binary_round_measure.
    Scope: EnumQ concrete distributions are intentional; composition is in BernoulliFactoryComposition.
    See docs/CASE_STUDY_STANDARD.md and docs/CASE_STUDY_REFACTOR.md. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

Require Import Utf8 FunctionalExtensionality.

From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg ssrnum order rat.

From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Backend.Common.FiniteRecordExtensionality PTree.Prob.Backend.Common.FiniteEnum PTree.Prob.Backend.EnumQ.Representation.
From PTree.Prob.Interface Require Import FrontierLift.
Require Import PTree.Prob.Backend.EnumQ.FrontierLift PTree.Prob.Backend.EnumQ.Bind.
Require Import PTree.Prob.Interface.Iteration.
Require Import PTree.Prob.Backend.EnumQ.Iteration.
From PTree.Examples.BernoulliFactory Require Import VonNeumannUnbounded RationalBernoulli.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ.
Import PTree.Prob.Backend.EnumQ.Map.
Import GRing.Theory Num.Theory Order.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

Unset Automatic Proposition Inductives.
Variant factoryE : Type -> Type := .

Section Factory.
Variables pfalse ptrue : rat.
Hypotheses (pfalse0 : 0 <= pfalse) (ptrue0 : 0 <= ptrue).
Variable q : rat.

Definition factory_biased_coin : EnumQ bool :=
  enumQ_cons pfalse0 false (enumQ_cons ptrue0 true enumQ_zero).

Definition factory_round_measure : EnumQ (unit + bool) :=
  bind_EnumQ factory_biased_coin (fun b1 =>
    bind_EnumQ factory_biased_coin (fun b2 =>
      ret_EnumQ (vn_round_result b1 b2))).

Definition factory_vn_step (_ : unit) :
    ptree factoryE EnumQ (unit + bool) :=
  Prob factory_biased_coin (fun b1 =>
    Prob factory_biased_coin (fun b2 => Ret (vn_round_result b1 b2))).

Definition factory_fair_coin : ptree factoryE EnumQ bool :=
  PTree.iter factory_vn_step tt.

Lemma factory_round_is_param_round :
  factory_round_measure = param_round_measure pfalse0 ptrue0.
Proof. reflexivity. Qed.

Hypothesis pnormalized : pfalse + ptrue = 1.
Hypothesis pnontrivial : 0 < pfalse * ptrue.

Definition binary_round_result (x : rat) (b : bool) : rat + bool :=
  if x < 1 / 2 then
    if b then inr false else inl (2 * x)
  else
    if b then inl (2 * x - 1) else inr true.

Lemma fair_binary_round_measure x :
  bind_EnumQ vn_fair (fun b => ret_EnumQ (binary_round_result x b)) =
  binary_coin_transition x.
Proof.
  apply finite_enum_raw_eq.
  rewrite /vn_fair /binary_round_result /binary_coin_transition.
  case: (x < 1 / 2); reflexivity.
Qed.

(** The algorithm only depends on the behavior of its Boolean sampler. *)
Definition factory_sampler_step {E : Type -> Type}
    (sampler : ptree E EnumQ bool) (x : rat) : ptree E EnumQ (rat + bool) :=
  PTree.bind sampler (fun b => Ret (binary_round_result x b)).

Definition factory_with_sampler {E : Type -> Type}
    (sampler : ptree E EnumQ bool) (target : rat) : ptree E EnumQ bool :=
  PTree.iter (factory_sampler_step sampler) target.

Definition factory_direct_fair : ptree factoryE EnumQ bool :=
  Prob vn_fair (fun b => Ret b).

Definition factory_binary_step (x : rat) :
    ptree factoryE EnumQ (rat + bool) :=
  factory_sampler_step factory_fair_coin x.

Definition biased_to_rational_coin : ptree factoryE EnumQ bool :=
  factory_with_sampler factory_fair_coin q.

Definition factory_direct_q (q0 : 0 <= q) (q1 : q <= 1) :
    ptree factoryE EnumQ bool :=
  Prob (rational_bernoulli_measure q0 q1) (fun b => Ret b).

End Factory.

(** A closed, non-trivial executable instance: two tosses of the [1/3]
    source coin are repeatedly von-Neumann-filtered, and the resulting fair
    bits drive the binary algorithm for a [2/5] target coin. *)
Lemma third_false_nonnegative : 0 <= vn_one_third.
Proof. vm_compute; reflexivity. Qed.
Lemma third_true_nonnegative : 0 <= vn_two_thirds.
Proof. vm_compute; reflexivity. Qed.
Definition third_to_two_fifths : ptree factoryE EnumQ bool :=
  biased_to_rational_coin third_false_nonnegative third_true_nonnegative (2 / 5).

Lemma third_bias_normalized :
  vn_one_third + vn_two_thirds = 1.
Proof.
  change ((1 / 3 : rat) + 2 / 3 = 1).
  ring_to_rat; reflexivity.
Qed.

Lemma third_bias_nontrivial :
  0 < vn_one_third * vn_two_thirds.
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

Definition direct_two_fifths : ptree factoryE EnumQ bool :=
  factory_direct_q (q := 2 / 5)
    two_fifths_nonnegative two_fifths_at_most_one.
