(** Case role: shared analysis.
    Proof mode: analysis-dominated.
    Reading entry: rational_binary_iteration_converges; rational_binary_coin_almost_surely_terminates.
    Scope: Arbitrary bounded rational target, including endpoints; finite distribution definitions are intentional.
    See docs/CASE_STUDY_STANDARD.md and docs/CASE_STUDY_REFACTOR.md. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

Require Import Utf8 Ring Field Lia Lra FunctionalExtensionality List.

From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg ssrnum order rat.

From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Backend.Common.FiniteEnum PTree.Prob.Backend.EnumQ.Representation.
From PTree.Prob.Interface Require Import FrontierLift.
Require Import PTree.Prob.Backend.EnumQ.FrontierLift PTree.Prob.Backend.EnumQ.Bind.
Require Import PTree.Prob.Interface.Iteration.
Require Import PTree.Prob.Backend.EnumQ.Iteration PTree.Prob.Backend.Common.RatGeometric.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ.
Import GRing.Theory Num.Theory Order.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

Unset Automatic Proposition Inductives.
Variant rational_coinE : Type -> Type := .

(** Binary interval algorithm for Bernoulli(q).  At an interior state [x],
    one fair bit either terminates or moves to the fractional part of [2*x].
    Thus every round has continuation mass exactly one half, including for
    rationals with an infinite eventually-periodic binary expansion. *)
Definition binary_coin_transition (x : rat) : EnumQ (rat + bool) :=
  if x < 1 / 2 then
    unif2 (inl (2 * x)) (inr false)
  else
    unif2 (inr true) (inl (2 * x - 1)).

Definition binary_coin_step (x : rat) :
    ptree rational_coinE EnumQ (rat + bool) :=
  Prob (binary_coin_transition x) (fun next => Ret next).

Definition binary_rational_coin (q : rat) :
    ptree rational_coinE EnumQ bool :=
  PTree.iter binary_coin_step q.

Definition coin_potential (next : rat + bool) : rat :=
  match next with
  | inl x => x
  | inr false => 0
  | inr true => 1
  end.

Lemma one_div_two_val : one_div_two = (1 / 2 : rat).
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
  enumQ_expect coin_potential (binary_coin_transition x) = x.
Proof.
  rewrite /binary_coin_transition.
  case Ex: (x < 1 / 2); rewrite enumQ_expect_unif2 /one_div_two /=.
  - by rewrite !mulr0 add0r addr0 half_double.
  - rewrite mulr1 addr0 mulrBr mulr1 half_double.
    by rewrite addrC subrK.
Qed.

Lemma binary_coin_transition_total x :
  enumQ_expect (fun _ : rat + bool => 1)
    (binary_coin_transition x) = 1.
Proof.
  rewrite /binary_coin_transition.
  case: (x < 1 / 2); rewrite enumQ_expect_unif2 /one_div_two /= !mulr1 !addr0 -mulrDl.
  all: change ((2 : rat) / 2 = 1).
  all: by rewrite divrr // unitfE pnatr_eq0.
Qed.

(** At every nonterminal state the probability of another round is [1/2]. *)
Lemma binary_coin_transition_continue_mass x :
  enumQ_expect
    (fun next => match next with inl _ => 1 | inr _ => 0 end)
    (binary_coin_transition x) = 1 / 2.
Proof.
  rewrite /binary_coin_transition.
  case: (x < 1 / 2); rewrite enumQ_expect_unif2 /one_div_two /= !mulr1 !mulr0 !addr0; reflexivity.
Qed.

(** Fuelled executions which retain their unresolved state.  In contrast,
    [meas_iter_approx] discards that residual mass at fuel zero. *)
Fixpoint binary_coin_run (n : nat) (x : rat) : EnumQ (rat + bool) :=
  match n with
  | O => ret_EnumQ (inl x)
  | S n' =>
      bind_EnumQ (binary_coin_transition x) (fun next =>
        match next with
        | inl y => binary_coin_run n' y
        | inr b => ret_EnumQ (inr b)
        end)
  end.

Definition unresolved_indicator (next : rat + bool) : rat :=
  match next with inl _ => 1 | inr _ => 0 end.

Lemma binary_coin_run_potential n x :
  enumQ_expect coin_potential (binary_coin_run n x) = x.
Proof.
  elim: n x=> [|n IH] x.
  - exact: enumQ_expect_ret.
  - rewrite /= enumQ_expect_bind.
    have Hfun :
        (fun next : rat + bool =>
          enumQ_expect coin_potential
            match next with
            | inl y => binary_coin_run n y
            | inr b => ret_EnumQ (inr b)
            end) = coin_potential.
    { apply functional_extensionality=> next.
      destruct next as [y|b].
      - exact: IH.
      - destruct b; exact: enumQ_expect_ret. }
    rewrite Hfun. exact: binary_coin_transition_preserves_probability.
Qed.

Lemma binary_coin_run_unresolved n x :
  enumQ_expect unresolved_indicator (binary_coin_run n x) =
    (1 / 2 : rat) ^+ n.
Proof.
  elim: n x=> [|n IH] x.
  - by rewrite /= expr0.
  - rewrite /= enumQ_expect_bind exprS.
    have Hfun :
        (fun next : rat + bool =>
          enumQ_expect unresolved_indicator
            match next with
            | inl y => binary_coin_run n y
            | inr b => ret_EnumQ (inr b)
            end) =
        (fun next => unresolved_indicator next * (1 / 2 : rat) ^+ n).
    { apply functional_extensionality=> next.
      destruct next as [y|b].
      - by rewrite /unresolved_indicator mul1r IH.
      - destruct b; rewrite enumQ_expect_ret /unresolved_indicator mul0r;
          reflexivity. }
    rewrite Hfun.
    rewrite /binary_coin_transition.
    case: (x < 1 / 2); rewrite enumQ_expect_unif2 /one_div_two /= !mul1r !mul0r !addr0.
    all: rewrite ?mulr0 ?add0r.
    all: reflexivity.
Qed.

Lemma binary_coin_run_total n x :
  enumQ_expect (fun _ : rat + bool => 1) (binary_coin_run n x) = 1.
Proof.
  elim: n x=> [|n IH] x.
  - by rewrite /=.
  - rewrite /= enumQ_expect_bind.
    have Hfun :
        (fun next : rat + bool =>
          enumQ_expect (fun _ : rat + bool => 1)
            match next with
            | inl y => binary_coin_run n y
            | inr b => ret_EnumQ (inr b)
            end) = (fun _ => 1).
    { apply functional_extensionality=> next.
      destruct next as [y|b].
      - exact: IH.
      - exact: enumQ_expect_ret. }
    rewrite Hfun. exact: binary_coin_transition_total.
Qed.

Definition discard_unresolved (mu : EnumQ (rat + bool)) : EnumQ bool :=
  bind_EnumQ mu (fun next =>
    match next with
    | inl _ => enumQ_zero
    | inr b => ret_EnumQ b
    end).

Lemma iter_approx_as_discarded_run n x :
  enumQ_raw (meas_iter_approx n binary_coin_transition x) =
    enumQ_raw (discard_unresolved (binary_coin_run n x)).
Proof.
  elim: n x=> [|n IH] x.
  - reflexivity.
  - cbn [meas_iter_approx binary_coin_run]; unfold discard_unresolved.
    rewrite bind_EnumQ_assoc.
    apply bind_EnumQ_ext=> next.
    destruct next as [y|b].
    + exact: IH.
    + by rewrite /ret_EnumQ /bind_EnumQ /= mulr1.
Qed.

Definition absorbed_indicator (next : rat + bool) : rat :=
  match next with inl _ => 0 | inr _ => 1 end.

Lemma enumQ_expect_add {A} (f g : A -> rat) (mu : EnumQ A) :
  enumQ_expect (fun x => f x + g x) mu =
  enumQ_expect f mu + enumQ_expect g mu.
Proof. exact: finite_expect_add. Qed.

Lemma enumQ_expect_zero {A} (mu : EnumQ A) :
  enumQ_expect (fun _ : A => 0) mu = 0.
Proof. exact: finite_expect_zero. Qed.

Lemma discarded_run_total n x :
  enumQ_expect (fun _ : bool => 1)
      (discard_unresolved (binary_coin_run n x)) =
    1 - (1 / 2 : rat) ^+ n.
Proof.
  rewrite /discard_unresolved enumQ_expect_bind.
  have Hfun :
      (fun next : rat + bool =>
        enumQ_expect (fun _ : bool => 1)
          match next with
          | inl _ => enumQ_zero
          | inr b => ret_EnumQ b
          end) = absorbed_indicator.
  { apply functional_extensionality=> next.
    by destruct next as [y|b]. }
  rewrite Hfun.
  have Hsplit :
      (fun next : rat + bool => 1) =
      (fun next => absorbed_indicator next + unresolved_indicator next).
  { apply functional_extensionality=> next.
    by destruct next as [y|[]]. }
  have Hsum := enumQ_expect_add
    (absorbed_indicator) (unresolved_indicator) (binary_coin_run n x).
  rewrite -Hsplit binary_coin_run_total binary_coin_run_unresolved in Hsum.
  have Hsub := f_equal
    (fun z : rat => z - (1 / 2 : rat) ^+ n) Hsum.
  rewrite addrK in Hsub.
  exact: Logic.eq_sym Hsub.
Qed.

Lemma iter_approx_total n x :
  enumQ_expect (fun _ : bool => 1)
      (meas_iter_approx n binary_coin_transition x) =
    1 - (1 / 2 : rat) ^+ n.
Proof.
  change (finite_expect (fun _ : bool => 1) (enumQ_raw (meas_iter_approx n binary_coin_transition x)) = 1 - (1 / 2 : rat) ^+ n).
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
  Forall (fun px => unit_state (snd px)) (enumQ_raw (binary_coin_transition x)).
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
  0 <= enumQ_expect residual_potential (binary_coin_run n x) /\
  enumQ_expect residual_potential (binary_coin_run n x) <=
    (1 / 2 : rat) ^+ n.
Proof.
  elim: n x=> [|n IH] x x0 x1.
  - rewrite /= !enumQ_expect_ret /residual_potential expr0. exact: conj x0 x1.
  - rewrite /= !enumQ_expect_bind /binary_coin_transition.
    have two0 : (0 : rat) <= 2 by [].
    have half0 : (0 : rat) <= 1 / 2 by [].
    case Hhalf: (x < 1 / 2); rewrite !enumQ_expect_unif2 /one_div_two /= !enumQ_expect_ret /residual_potential /= !mulr0 !addr0 ?add0r exprS.
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
  enumQ_expect true_indicator (binary_coin_run n x) +
  enumQ_expect residual_potential (binary_coin_run n x) = x.
Proof.
  rewrite -enumQ_expect_add -coin_potential_split.
  exact: binary_coin_run_potential.
Qed.

Lemma discarded_run_true n x :
  enumQ_expect (fun b : bool => if b then 1 else 0)
      (discard_unresolved (binary_coin_run n x)) =
  enumQ_expect true_indicator (binary_coin_run n x).
Proof.
  rewrite /discard_unresolved enumQ_expect_bind.
  congr (enumQ_expect _ _).
  apply functional_extensionality=> next.
  destruct next as [y|[]]; rewrite /true_indicator /= ?mul1r ?addr0;
    reflexivity.
Qed.

Lemma iter_approx_true n x :
  enumQ_expect (fun b : bool => if b then 1 else 0)
      (meas_iter_approx n binary_coin_transition x) +
  enumQ_expect residual_potential (binary_coin_run n x) = x.
Proof.
  change (finite_expect (fun b : bool => if b then 1 else 0)
      (enumQ_raw (meas_iter_approx n binary_coin_transition x)) +
    enumQ_expect residual_potential (binary_coin_run n x) = x).
  rewrite iter_approx_as_discarded_run.
  change (enumQ_expect (fun b : bool => if b then 1 else 0) (discard_unresolved (binary_coin_run n x)) +
    enumQ_expect residual_potential (binary_coin_run n x) = x).
  rewrite discarded_run_true.
  exact: binary_coin_run_true_plus_residual.
Qed.

Definition false_bool_indicator (b : bool) : rat :=
  if b then 0 else 1.

Lemma rat_false_error_identity (t r u : rat) :
  (1 - u - t) - (1 - (t + r)) = r - u.
Proof.
  change ((1 - u - t) + - (1 - (t + r)) = r - u).
  have Hassoc : t + r - 1 = t + (r - 1) by rewrite addrA.
  rewrite opprB Hassoc subrKA.
  by rewrite [r - 1]addrC addrACA addrN add0r addrC.
Qed.

Lemma rat_true_error_identity (t r : rat) : t - (t + r) = - r.
Proof.
  rewrite opprD.
  change (t + (- t + - r) = - r).
  by rewrite addrA addrN add0r.
Qed.

Lemma half_power_nonnegative n : 0 <= (1 / 2 : rat) ^+ n.
Proof.
  have half0 : (0 : rat) <= 1 / 2 by [].
  elim: n=> [|n IH].
  - by rewrite expr0.
  - rewrite exprS. exact: mulr_ge0 half0 IH.
Qed.

Lemma enumQ_bool_total_split (mu : EnumQ bool) :
  enumQ_expect false_bool_indicator mu +
  enumQ_expect (fun b : bool => if b then 1 else 0) mu =
  enumQ_expect (fun _ : bool => 1) mu.
Proof.
  rewrite -enumQ_expect_add.
  congr (enumQ_expect _ mu).
  apply functional_extensionality=> b.
  by destruct b; rewrite /false_bool_indicator /= ?add0r ?addr0.
Qed.

Section RationalTarget.
Variable q : rat.
Hypothesis q0 : 0 <= q.
Hypothesis q1 : q <= 1.

Lemma one_minus_q0 : 0 <= 1 - q.
Proof. by rewrite subr_ge0. Qed.

Definition rational_bernoulli_measure : EnumQ bool :=
  enumQ_cons one_minus_q0 false (enumQ_cons q0 true enumQ_zero).

Lemma rational_bernoulli_total :
  enumQ_expect (fun _ : bool => 1) rational_bernoulli_measure = 1.
Proof.
  rewrite /rational_bernoulli_measure !enumQ_expect_cons enumQ_expect_nil !mulr1 !addr0.
  exact: subrK q 1.
Qed.

Lemma rational_bernoulli_indicator (P : bool -> bool) :
  enumQ_expect (fun b => if P b then 1 else 0)
    rational_bernoulli_measure =
  (if P false then 1 - q else 0) + (if P true then q else 0).
Proof.
  rewrite /rational_bernoulli_measure !enumQ_expect_cons enumQ_expect_nil.
  by case: (P false); case: (P true);
    rewrite /= ?mulr0 ?mulr1 ?addr0 ?add0r.
Qed.

Lemma rational_iter_indicator_error n (P : bool -> bool) :
  `|enumQ_expect (fun b => if P b then 1 else 0)
       (meas_iter_approx n binary_coin_transition q) -
     enumQ_expect (fun b => if P b then 1 else 0)
       rational_bernoulli_measure| <= (1 / 2 : rat) ^+ n.
Proof.
  pose mu : EnumQ bool :=
    @meas_iter_approx EnumQ EnumQ_MeasureInterface
      EnumQ_MeasureOmegaInterface rat bool n binary_coin_transition q.
  pose r := enumQ_expect residual_potential (binary_coin_run n q).
  pose u : rat := (1 / 2 : rat) ^+ n.
  pose t : rat :=
    enumQ_expect (fun b : bool => if b then 1 else 0) mu.
  have half0 : (0 : rat) <= 1 / 2 by [].
  have u0 : 0 <= u by exact: half_power_nonnegative.
  have [r0 ru] : 0 <= r /\ r <= u.
  { exact: binary_coin_run_residual_bound q0 q1. }
  have Htrue : t + r = q.
  { exact: iter_approx_true. }
  have Htotal : enumQ_expect (fun _ : bool => 1) mu = 1 - u.
  { exact: iter_approx_total. }
  have Hsplit := enumQ_bool_total_split mu.
  fold t in Hsplit.
  rewrite rational_bernoulli_indicator.
  case Hf: (P false); case Ht: (P true).
  - have HP : (fun b : bool => if P b then (1 : rat) else 0) =
        (fun _ : bool => (1 : rat)).
    { apply functional_extensionality=> b.
      destruct b; simpl; [by rewrite Ht|by rewrite Hf]. }
    rewrite HP Htotal.
    have Hu : (1 - u) - 1 = - u.
    { apply: (addrI 1). by rewrite addrC subrK. }
    by rewrite subrK Hu normrN ger0_norm.
  - have HP : (fun b : bool => if P b then (1 : rat) else 0) =
        false_bool_indicator.
    { apply functional_extensionality=> b.
      destruct b; rewrite /false_bool_indicator /=; [by rewrite Ht|by rewrite Hf]. }
    rewrite HP /=.
    have Hdiff : enumQ_expect false_bool_indicator mu - (1 - q) = r - u.
    { have HF : enumQ_expect false_bool_indicator mu = (1 - u) - t.
      { apply: (addrI t).
        rewrite [t + enumQ_expect false_bool_indicator mu]addrC Hsplit Htotal.
        by rewrite [t + ((1 - u) - t)]addrC subrK. }
      rewrite HF -Htrue. exact: rat_false_error_identity. }
    have Hru : r - u <= 0 by rewrite subr_le0.
    fold mu. rewrite addr0 Hdiff (ler0_norm Hru) opprB lerBlDr lerDl.
    exact r0.
  - have HP : (fun b : bool => if P b then (1 : rat) else 0) =
        (fun b : bool => if b then (1 : rat) else 0).
    { apply functional_extensionality=> b.
      destruct b; simpl; [by rewrite Ht|by rewrite Hf]. }
    rewrite HP /=.
    have Hdiff :
        t - q = - r.
    { rewrite -Htrue. exact: rat_true_error_identity. }
    fold mu t. by rewrite add0r Hdiff normrN ger0_norm.
  - have HP : (fun b : bool => if P b then (1 : rat) else 0) =
        (fun _ : bool => (0 : rat)).
    { apply functional_extensionality=> b.
      destruct b; simpl; [by rewrite Ht|by rewrite Hf]. }
    rewrite HP /=.
    have Hz : enumQ_expect (fun _ : bool => 0) mu = 0.
    { exact: enumQ_expect_zero. }
    fold mu. rewrite !add0r Hz subrr normr0.
    fold u. exact u0.
Qed.

Lemma half_power_vanishes eps : 0 < eps ->
  exists N, forall n, Peano.le N n -> (1 / 2 : rat) ^+ n < eps.
Proof.
  move=> eps0.
  eapply rat_contract_vanishes with (K := 1%nat).
  - lia.
  - by [].
  - change ((1 / 2 : rat) <= 1 / 2). exact: lexx _.
  - exact eps0.
Qed.

Theorem rational_binary_iteration_converges :
  meas_iter binary_coin_transition q rational_bernoulli_measure.
Proof.
  unfold meas_iter, meas_lub, EnumQ_MeasureOmegaInterface, enumQ_converges.
  move=> P eps eps0.
  destruct (half_power_vanishes eps0) as [N HN].
  exists N=> n HNn.
  exact: le_lt_trans (rational_iter_indicator_error n P) (HN n HNn).
Qed.

Theorem rational_binary_coin_almost_surely_terminates :
  meas_iter_ast binary_coin_transition q.
Proof.
  eapply meas_iter_total_ast.
  - exact rational_binary_iteration_converges.
  - exact rational_bernoulli_total.
Qed.

Definition direct_rational_coin : ptree rational_coinE EnumQ bool :=
  Prob rational_bernoulli_measure (fun b => Ret b).

End RationalTarget.
