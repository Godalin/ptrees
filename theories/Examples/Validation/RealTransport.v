(** Role: external mathematical-model example, not a reasoning dependency. *)
(** Finite real Hall existence: tests include unused capacity, empty source
    and target, real (not assumed rational) masses, and forbidden edges. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals.
From PTree.Prob.Backend.Common Require Import FiniteMatching RealTransport.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Core.PTreeDefinition.ptree.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section Tests.
Variable R : realType.

Lemma diagonal_neighbors {X : finType} (S : {set X}) :
  matching_neighbors (λ x y : X, x == y) finset.setT S = S.
Proof.
  apply/setP=> y; apply/idP/idP.
  - move/matching_neighborsP=> [_ [x [Hx /eqP Hxy]]]; by rewrite -Hxy.
  - intro Hy; apply/matching_neighborsP; split; first by rewrite inE.
    exists y; by split.
Qed.

Example diagonal_real_mass {X : finType} (p : X → R) :
  (∀ x, 0 <= p x) →
  ∃ w : X → X → R,
    (∀ x y, 0 <= w x y) ∧
    (∀ x, \sum_y w x y = p x) ∧
    (∀ y, \sum_x w x y = p y) ∧
    (∀ x y, x != y → w x y = 0).
Proof.
  intro Hp; apply finite_real_transport; auto.
  intro S; rewrite diagonal_neighbors; exact: lexx.
Qed.

Example sqrt_weight_transport :
  ∃ w : bool → bool → R,
    (∀ x y, 0 <= w x y) ∧
    (∀ x, \sum_y w x y = if x then Num.sqrt 2 else 1) ∧
    (∀ y, \sum_x w x y = if y then Num.sqrt 2 else 1) ∧
    (∀ x y, x != y → w x y = 0).
Proof.
  apply (@diagonal_real_mass _
    (λ x : bool, if x then Num.sqrt 2 else 1)).
  intros []; simpl.
  all: first [exact: sqrtr_ge0 | exact: ler01].
Qed.

(** Positive demand and slack target capacity, with no equality of totals. *)
Example unused_target_capacity (a b : R) : 0 <= a → a <= b →
  ∃ w : unit → unit → R,
    (∀ x y, 0 <= w x y) ∧
    (∀ x, \sum_y w x y = a) ∧
    (∀ y, \sum_x w x y <= b) ∧
    (∀ x y, ~~ true → w x y = 0).
Proof.
  intros Ha Hab; apply (@finite_real_subtransport R _ _ (λ _ : unit, a)
    (λ _ : unit, b) (λ _ _, true)).
  1: by intros.
  1: by intros; exact: le_trans Ha Hab.
  intro S; destruct (boolP (tt \in S)) as [Hin|Hout].
  - have HS : S = [set: unit].
    { apply/setP=> [[]]; by rewrite inE. }
    have HN : matching_neighbors (λ _ _ : unit, true) [set: unit] S = [set: unit].
    { apply/setP=> [[]]; apply/idP/idP; first by intros; rewrite inE.
      intros _; apply/matching_neighborsP; split; first by rewrite inE.
      exists tt; by split. }
    by rewrite HN HS !big_const /= cardsT card_unit /= !addr0.
  - have HS : S = set0.
    { apply/setP=> [[]]; by rewrite inE (negPf Hout). }
    rewrite HS big_set0; apply sumr_ge0=> y _; exact: le_trans Ha Hab.
Qed.

(** A row really splits across two differently weighted columns. *)
Example split_real_mass (a b : R) : 0 <= a → 0 <= b →
  ∃ w : unit → bool → R,
    (∀ x y, 0 <= w x y) ∧
    (∀ x, \sum_y w x y = a + b) ∧
    (∀ y, \sum_x w x y = if y then a else b) ∧
    (∀ x y, ~~ true → w x y = 0).
Proof.
  intros Ha Hb; apply (@finite_real_transport R _ _ (λ _ : unit, a + b)
    (λ y : bool, if y then a else b) (λ _ _, true)).
  - intros; exact: addr_ge0.
  - intros []; assumption.
  - intro S; destruct (boolP (tt \in S)) as [Hin|Hout].
    + have HS : S = [set: unit].
      { apply/setP=> [[]]; by rewrite inE. }
      have HN : matching_neighbors (λ (_ : unit) (_ : bool), true)
          [set: bool] S = [set: bool].
      { apply/setP=> y; apply/idP/idP; first by intros; rewrite inE.
        intros _; apply/matching_neighborsP; split; first by rewrite inE.
        exists tt; by split. }
      by rewrite HN HS big_const /= cardsT card_unit /= addr0 big_set big_bool /=.
    + have HS : S = set0.
      { apply/setP=> [[]]; by rewrite inE (negPf Hout). }
      rewrite HS big_set0; apply sumr_ge0=> [] [] _; assumption.
  - by rewrite big_const /= card_unit /= addr0 big_bool /=.
Qed.

Example empty_source (q : bool → R) : (∀ y, 0 <= q y) →
  ∃ w : 'I_0 → bool → R,
    (∀ x y, 0 <= w x y) ∧
    (∀ x, \sum_y w x y = 0) ∧
    (∀ y, \sum_x w x y <= q y) ∧
    (∀ x y, ~~ false → w x y = 0).
Proof.
  intro Hq; apply (@finite_real_subtransport R _ _ (λ _ : 'I_0, 0) q (λ _ _, false)).
  - intros; exact: lexx.
  - exact Hq.
  - intro S; rewrite big1; last by intros.
    apply sumr_ge0=> y _; exact (Hq y).
Qed.

Example zero_demand_empty_target :
  ∃ w : bool → 'I_0 → R,
    (∀ x y, 0 <= w x y) ∧
    (∀ x, \sum_y w x y = 0) ∧
    (∀ y, \sum_x w x y <= 0) ∧
    (∀ x y, ~~ false → w x y = 0).
Proof.
  apply (@finite_real_subtransport R _ _ (λ _ : bool, 0) (λ _ : 'I_0, 0) (λ _ _, false)).
  - intros; exact: lexx.
  - intros; exact: lexx.
  - intro S; rewrite !big1 //; exact: lexx.
Qed.

Example positive_demand_empty_target_impossible :
  ¬ ∃ w : unit → 'I_0 → R, ∀ x, \sum_y w x y = 1.
Proof.
  intros [w Hw]; have H := Hw tt; rewrite big_ord0 in H.
  have Hneq : (0 : R) != 1 by rewrite eq_sym oner_eq0.
  by rewrite H eqxx in Hneq.
Qed.
End Tests.
