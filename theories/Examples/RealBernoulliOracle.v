Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Ring Field Lia Lra FunctionalExtensionality.

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq ssralg ssrnum
  order rat.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import RatSubTypes DiscreteMC FrontierLift
  FrontierLiftEnum MeasureIteration MeasureIterationEnum RatGeometric.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.
Import GRing.Theory Num.Theory Order.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

Unset Automatic Proposition Inductives.
Variant real_oracle_coinE : Type -> Type := .

(** A real parameter is exposed operationally by a stream of binary digits.
    The semantic connection between this stream and a real number is stated
    separately below, so execution only needs to query the next bit. *)
Definition binary_oracle := nat -> bool.

(** Compare a fresh fair random bit with the next bit of [q].  At the first
    difference, [random < q] returns [true] and [random > q] returns [false];
    equality consumes another bit. *)
Definition oracle_coin_transition (qbit : binary_oracle) (n : nat) :
    Enum (nat + bool) :=
  if qbit n then
    [:: (one_div_two, inr true); (one_div_two, inl n.+1)]
  else
    [:: (one_div_two, inl n.+1); (one_div_two, inr false)].

Definition oracle_coin_step (qbit : binary_oracle) (n : nat) :
    ptree real_oracle_coinE Enum (nat + bool) :=
  Prob (oracle_coin_transition qbit n)
    (fun next : nat + bool => Ret next).

Definition binary_oracle_coin (qbit : binary_oracle) :
    ptree real_oracle_coinE Enum bool :=
  PTree.iter (oracle_coin_step qbit) 0.

Definition oracle_continue (next : nat + bool) : rat :=
  match next with inl _ => 1 | inr _ => 0 end.

Definition oracle_true (next : nat + bool) : rat :=
  match next with inl _ => 0 | inr b => if b then 1 else 0 end.

Lemma oracle_transition_total qbit n :
  enum_expect (fun _ : nat + bool => 1)
    (oracle_coin_transition qbit n) = 1.
Proof.
  rewrite /oracle_coin_transition.
  case: (qbit n); rewrite /= !mulr1 !addr0 -mulrDl.
  all: change ((2 : rat) / 2 = 1).
  all: by rewrite divrr // unitfE pnatr_eq0.
Qed.

Lemma oracle_transition_continue qbit n :
  enum_expect oracle_continue (oracle_coin_transition qbit n) = 1 / 2.
Proof.
  rewrite /oracle_coin_transition.
  by case: (qbit n); rewrite /= !mulr1 !mulr0 !addr0 ?add0r.
Qed.

Lemma rat_half_add : (1 / 2 : rat) + 1 / 2 = 1.
Proof.
  rewrite -mulrDl.
  change ((2 : rat) / 2 = 1).
  by rewrite divrr // unitfE pnatr_eq0.
Qed.

Lemma rat_half_contract a :
  (1 / 2 : rat) + (1 / 2) * (1 - a) = 1 - (1 / 2) * a.
Proof.
  rewrite mulrBr mulr1.
  rewrite [((1 / 2 : rat) +
      ((1 / 2 : rat) - (1 / 2 : rat) * a))]addrC -addrA.
  rewrite [(- ((1 / 2 : rat) * a) + (1 / 2 : rat))]addrC addrA.
  by rewrite rat_half_add.
Qed.

(** Probability of returning [true] within [fuel] comparisons, starting at
    digit [n].  This is exactly the corresponding finite binary prefix. *)
Fixpoint oracle_prefix_from (qbit : binary_oracle)
    (n fuel : nat) : rat :=
  match fuel with
  | O => 0
  | S fuel' =>
      (if qbit n then 1 / 2 else 0) +
      (1 / 2) * oracle_prefix_from qbit n.+1 fuel'
  end.

Definition oracle_prefix qbit fuel := oracle_prefix_from qbit 0 fuel.

Definition oracle_true_indicator (b : bool) : rat := if b then 1 else 0.

Lemma oracle_iter_true_prefix qbit fuel n :
  enum_expect oracle_true_indicator
    (meas_iter_approx fuel (oracle_coin_transition qbit) n) =
  oracle_prefix_from qbit n fuel.
Proof.
  elim: fuel n=> [|fuel IH] n; first reflexivity.
  rewrite /= enum_expect_bind /oracle_coin_transition.
  case E: (qbit n); rewrite /=.
  - by rewrite /= mulr1 IH mulrDr mulr1 mulr0 !addr0.
  - by rewrite /= mulr0 add0r IH !addr0.
Qed.

Lemma oracle_iter_total_mass qbit fuel n :
  enum_expect (fun _ : bool => 1)
    (meas_iter_approx fuel (oracle_coin_transition qbit) n) =
  1 - (1 / 2 : rat) ^+ fuel.
Proof.
  elim: fuel n=> [|fuel IH] n.
  - by rewrite /= expr0 subrr.
  - rewrite /= enum_expect_bind /oracle_coin_transition.
    case: (qbit n); rewrite /= IH.
    all: rewrite !mulr1 !addr0 exprS.
    - exact: rat_half_contract.
    - rewrite addrC. exact: rat_half_contract.
Qed.

Lemma oracle_iter_missing_mass qbit fuel n :
  1 - enum_expect (fun _ : bool => 1)
        (meas_iter_approx fuel (oracle_coin_transition qbit) n) =
  (1 / 2 : rat) ^+ fuel.
Proof. by rewrite oracle_iter_total_mass subKr. Qed.

(** Uniform quantitative AST: independently of the oracle, the probability
    of requiring more than [fuel] comparisons tends to zero geometrically. *)
Theorem oracle_missing_mass_vanishes qbit n eps : 0 < eps ->
  exists N, forall fuel, Peano.le N fuel ->
    1 - enum_expect (fun _ : bool => 1)
          (meas_iter_approx fuel (oracle_coin_transition qbit) n) < eps.
Proof.
  move=> eps0.
  have Hvanish := rat_contract_vanishes
    (r := (1 / 2 : rat)) (K := 1%nat) (ltac:(lia))
    (ltac:(by [])) (ltac:(exact: lexx (1 / 2 : rat))) eps0.
  move: Hvanish=> [N HN]. exists N=> fuel Hfuel.
  rewrite oracle_iter_missing_mass.
  exact: HN fuel Hfuel.
Qed.

(** A representation predicate for a mathematical real parameter.  It is
    intentionally phrased through convergence of rational prefixes; a later
    backend theorem can instantiate [embed] with the canonical embedding
    into a MathComp [realType]. *)
Definition oracle_represents {T : Type}
    (embed : rat -> T) (converges : (nat -> T) -> T -> Prop)
    (qbit : binary_oracle) (q : T) : Prop :=
  converges (fun n => embed (oracle_prefix qbit n)) q.
