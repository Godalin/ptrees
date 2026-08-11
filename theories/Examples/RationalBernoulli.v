Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Ring FunctionalExtensionality List.

From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg ssrnum order
  rat.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import RatSubTypes DiscreteMC FrontierLift
  FrontierLiftEnum EnumBindFacts MeasureIteration MeasureIterationEnum
  RatGeometric.

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
  if x < 1 / 2 then
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
  case Ex: (x < 1 / 2); rewrite /=.
  - by rewrite !mulr0 add0r addr0 half_double.
  - rewrite mulr1 addr0 mulrBr mulr1 half_double.
    by rewrite addrC subrK.
Qed.

Lemma binary_coin_transition_total x :
  enum_expect (fun _ : rat + bool => 1)
    (binary_coin_transition x) = 1.
Proof.
  rewrite /binary_coin_transition.
  case: (x < 1 / 2); rewrite /= !mulr1 !addr0 -mulrDl.
  all: change ((2 : rat) / 2 = 1).
  all: by rewrite divrr // unitfE pnatr_eq0.
Qed.

(** At every nonterminal state the probability of another round is [1/2]. *)
Lemma binary_coin_transition_continue_mass x :
  enum_expect
    (fun next => match next with inl _ => 1 | inr _ => 0 end)
    (binary_coin_transition x) = 1 / 2.
Proof.
  rewrite /binary_coin_transition.
  case: (x < 1 / 2); rewrite /= !mulr1 !mulr0 !addr0; reflexivity.
Qed.

(** Fuelled executions which retain their unresolved state.  In contrast,
    [meas_iter_approx] discards that residual mass at fuel zero. *)
Fixpoint binary_coin_run (n : nat) (x : rat) : Enum (rat + bool) :=
  match n with
  | O => ret_Enum (inl x)
  | S n' =>
      bind_Enum (binary_coin_transition x) (fun next =>
        match next with
        | inl y => binary_coin_run n' y
        | inr b => ret_Enum (inr b)
        end)
  end.

Definition unresolved_indicator (next : rat + bool) : rat :=
  match next with inl _ => 1 | inr _ => 0 end.

Lemma binary_coin_run_potential n x :
  enum_expect coin_potential (binary_coin_run n x) = x.
Proof.
  elim: n x=> [|n IH] x.
  - exact: enum_expect_ret.
  - rewrite /= enum_expect_bind.
    have Hfun :
        (fun next : rat + bool =>
          enum_expect coin_potential
            match next with
            | inl y => binary_coin_run n y
            | inr b => ret_Enum (inr b)
            end) = coin_potential.
    { apply functional_extensionality=> next.
      destruct next as [y|b].
      - exact: IH.
      - destruct b; exact: enum_expect_ret. }
    rewrite Hfun. exact: binary_coin_transition_preserves_probability.
Qed.

Lemma binary_coin_run_unresolved n x :
  enum_expect unresolved_indicator (binary_coin_run n x) =
    (1 / 2 : rat) ^+ n.
Proof.
  elim: n x=> [|n IH] x.
  - by rewrite /= expr0.
  - rewrite /= enum_expect_bind exprS.
    have Hfun :
        (fun next : rat + bool =>
          enum_expect unresolved_indicator
            match next with
            | inl y => binary_coin_run n y
            | inr b => ret_Enum (inr b)
            end) =
        (fun next => unresolved_indicator next * (1 / 2 : rat) ^+ n).
    { apply functional_extensionality=> next.
      destruct next as [y|b].
      - by rewrite /unresolved_indicator mul1r IH.
      - destruct b; rewrite enum_expect_ret /unresolved_indicator mul0r;
          reflexivity. }
    rewrite Hfun.
    rewrite /binary_coin_transition.
    case: (x < 1 / 2); rewrite /= !mul1r !mul0r !addr0.
    all: rewrite ?mulr0 ?add0r.
    all: reflexivity.
Qed.

Lemma binary_coin_run_total n x :
  enum_expect (fun _ : rat + bool => 1) (binary_coin_run n x) = 1.
Proof.
  elim: n x=> [|n IH] x.
  - by rewrite /=.
  - rewrite /= enum_expect_bind.
    have Hfun :
        (fun next : rat + bool =>
          enum_expect (fun _ : rat + bool => 1)
            match next with
            | inl y => binary_coin_run n y
            | inr b => ret_Enum (inr b)
            end) = (fun _ => 1).
    { apply functional_extensionality=> next.
      destruct next as [y|b].
      - exact: IH.
      - exact: enum_expect_ret. }
    rewrite Hfun. exact: binary_coin_transition_total.
Qed.

Definition discard_unresolved (mu : Enum (rat + bool)) : Enum bool :=
  bind_Enum mu (fun next =>
    match next with
    | inl _ => [::]
    | inr b => ret_Enum b
    end).

Lemma iter_approx_as_discarded_run n x :
  meas_iter_approx n binary_coin_transition x =
    discard_unresolved (binary_coin_run n x).
Proof.
  elim: n x=> [|n IH] x.
  - reflexivity.
  - rewrite /= /discard_unresolved bind_Enum_assoc.
    apply bind_Enum_ext=> next.
    destruct next as [y|b].
    + exact: IH.
    + by rewrite /ret_Enum /bind_Enum /= mulr1.
Qed.

Definition absorbed_indicator (next : rat + bool) : rat :=
  match next with inl _ => 0 | inr _ => 1 end.

Lemma enum_expect_add {A} (f g : A -> rat) (mu : Enum A) :
  enum_expect (fun x => f x + g x) mu =
  enum_expect f mu + enum_expect g mu.
Proof.
  elim: mu=> [|[p x] mu IH] /=; first by rewrite add0r.
  rewrite mulrDr IH.
  exact: addrACA.
Qed.

Lemma discarded_run_total n x :
  enum_expect (fun _ : bool => 1)
      (discard_unresolved (binary_coin_run n x)) =
    1 - (1 / 2 : rat) ^+ n.
Proof.
  rewrite /discard_unresolved enum_expect_bind.
  have Hfun :
      (fun next : rat + bool =>
        enum_expect (fun _ : bool => 1)
          match next with
          | inl _ => [::]
          | inr b => ret_Enum b
          end) = absorbed_indicator.
  { apply functional_extensionality=> next.
    by destruct next as [y|b]. }
  rewrite Hfun.
  have Hsplit :
      (fun next : rat + bool => 1) =
      (fun next => absorbed_indicator next + unresolved_indicator next).
  { apply functional_extensionality=> next.
    by destruct next as [y|[]]. }
  have Hsum := enum_expect_add
    (absorbed_indicator) (unresolved_indicator) (binary_coin_run n x).
  rewrite -Hsplit binary_coin_run_total binary_coin_run_unresolved in Hsum.
  have Hsub := f_equal
    (fun z : rat => z - (1 / 2 : rat) ^+ n) Hsum.
  rewrite addrK in Hsub.
  exact: Logic.eq_sym Hsub.
Qed.

Lemma iter_approx_total n x :
  enum_expect (fun _ : bool => 1)
      (meas_iter_approx n binary_coin_transition x) =
    1 - (1 / 2 : rat) ^+ n.
Proof.
  rewrite iter_approx_as_discarded_run.
  exact: discarded_run_total.
Qed.

(** The state transformation never leaves the unit interval. *)
Definition unit_state (next : rat + bool) : Prop :=
  match next with
  | inl x => 0 <= x /\ x <= 1
  | inr _ => True
  end.

Lemma binary_coin_transition_unit x :
  0 <= x -> x <= 1 ->
  Forall (fun px => unit_state (snd px)) (binary_coin_transition x).
Proof.
  move=> x0 x1.
  have two_pos : (0 : rat) < 2 by [].
  have two_nonneg : (0 : rat) <= 2 := ltW two_pos.
  have half_nonneg : (0 : rat) <= 1 / 2 by [].
  rewrite /binary_coin_transition.
  case Hhalf: (x < 1 / 2).
  - constructor.
    + simpl. split.
      * exact: mulr_ge0 two_nonneg x0.
      * have H := ler_pM two_nonneg x0 (lexx (2 : rat)) (ltW Hhalf).
        exact H.
    + constructor; [done|constructor].
  - constructor; [done|].
    constructor.
    + simpl. split.
      * rewrite subr_ge0.
        have Hge : (1 / 2 : rat) <= x by rewrite leNgt Hhalf.
        have H := ler_pM two_nonneg half_nonneg (lexx (2 : rat)) Hge.
        exact H.
      * rewrite lerBlDr.
        have H := ler_pM two_nonneg x0 (lexx (2 : rat)) x1.
        exact H.
    + constructor.
Qed.

Definition residual_potential (next : rat + bool) : rat :=
  match next with inl x => x | inr _ => 0 end.

Lemma binary_coin_run_residual_bound n x :
  0 <= x -> x <= 1 ->
  0 <= enum_expect residual_potential (binary_coin_run n x) /\
  enum_expect residual_potential (binary_coin_run n x) <=
    (1 / 2 : rat) ^+ n.
Proof.
  elim: n x=> [|n IH] x x0 x1.
  - rewrite /= expr0 mul1r addr0. exact: conj x0 x1.
  - rewrite /= enum_expect_bind /binary_coin_transition.
    have two0 : (0 : rat) <= 2 by [].
    have half0 : (0 : rat) <= 1 / 2 by [].
    case Hhalf: (x < 1 / 2); rewrite /= !mulr0 !addr0 ?add0r exprS.
    + have y0 : 0 <= 2 * x by exact: mulr_ge0 two0 x0.
      have y1 : 2 * x <= 1.
      { have H := ler_pM two0 x0 (lexx (2 : rat)) (ltW Hhalf).
        exact H. }
      have [IH0 IH1] := IH (2 * x) y0 y1.
      split.
      * exact: mulr_ge0 half0 IH0.
      * have H := ler_wpM2l half0 IH1.
        by rewrite mulrC in H *.
    + have Hge : (1 / 2 : rat) <= x by rewrite leNgt Hhalf.
      have y0 : 0 <= 2 * x - 1.
      { rewrite subr_ge0.
        have H := ler_pM two0 half0 (lexx (2 : rat)) Hge.
        exact H. }
      have y1 : 2 * x - 1 <= 1.
      { rewrite lerBlDr.
        have H := ler_pM two0 x0 (lexx (2 : rat)) x1.
        exact H. }
      have [IH0 IH1] := IH (2 * x - 1) y0 y1.
      split.
      * exact: mulr_ge0 half0 IH0.
      * have H := ler_wpM2l half0 IH1.
        by rewrite mulrC in H *.
Qed.

Definition true_indicator (next : rat + bool) : rat :=
  match next with inr true => 1 | _ => 0 end.

Lemma coin_potential_split :
  coin_potential = (fun next => true_indicator next + residual_potential next).
Proof.
  apply functional_extensionality=> next.
  destruct next as [y|[]]; rewrite /coin_potential /true_indicator
    /residual_potential /= ?add0r ?addr0; reflexivity.
Qed.

Lemma binary_coin_run_true_plus_residual n x :
  enum_expect true_indicator (binary_coin_run n x) +
  enum_expect residual_potential (binary_coin_run n x) = x.
Proof.
  rewrite -enum_expect_add -coin_potential_split.
  exact: binary_coin_run_potential.
Qed.

Lemma discarded_run_true n x :
  enum_expect (fun b : bool => if b then 1 else 0)
      (discard_unresolved (binary_coin_run n x)) =
  enum_expect true_indicator (binary_coin_run n x).
Proof.
  rewrite /discard_unresolved enum_expect_bind.
  congr (enum_expect _ _).
  apply functional_extensionality=> next.
  destruct next as [y|[]]; rewrite /true_indicator /= ?mul1r ?addr0;
    reflexivity.
Qed.

Lemma iter_approx_true n x :
  enum_expect (fun b : bool => if b then 1 else 0)
      (meas_iter_approx n binary_coin_transition x) +
  enum_expect residual_potential (binary_coin_run n x) = x.
Proof.
  rewrite iter_approx_as_discarded_run discarded_run_true.
  exact: binary_coin_run_true_plus_residual.
Qed.
