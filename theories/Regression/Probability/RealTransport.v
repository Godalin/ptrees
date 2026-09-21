(** Finite real Hall existence: tests include unused capacity, empty source
    and target, real (not assumed rational) masses, and forbidden edges. *)
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
  matching_neighbors (fun x y : X => x == y) finset.setT S = S.
Proof.
  apply/setP=> y; apply/idP/idP.
  - move/matching_neighborsP=> [_ [x [Hx /eqP Hxy]]]; by rewrite -Hxy.
  - intro Hy; apply/matching_neighborsP; split; first by rewrite inE.
    exists y; by split.
Qed.

Example diagonal_real_mass {X : finType} (p : X -> R) :
  (forall x, 0 <= p x) ->
  exists w : X -> X -> R,
    (forall x y, 0 <= w x y) /\
    (forall x, \sum_y w x y = p x) /\
    (forall y, \sum_x w x y = p y) /\
    (forall x y, x != y -> w x y = 0).
Proof.
  intro Hp; apply finite_real_transport; auto.
  intro S; rewrite diagonal_neighbors; exact: lexx.
Qed.

Example sqrt_weight_transport :
  exists w : bool -> bool -> R,
    (forall x y, 0 <= w x y) /\
    (forall x, \sum_y w x y = if x then Num.sqrt 2 else 1) /\
    (forall y, \sum_x w x y = if y then Num.sqrt 2 else 1) /\
    (forall x y, x != y -> w x y = 0).
Proof.
  apply (@diagonal_real_mass _
    (fun x : bool => if x then Num.sqrt 2 else 1)).
  intros []; simpl.
  all: first [exact: sqrtr_ge0 | exact: ler01].
Qed.

(** Positive demand and slack target capacity, with no equality of totals. *)
Example unused_target_capacity (a b : R) : 0 <= a -> a <= b ->
  exists w : unit -> unit -> R,
    (forall x y, 0 <= w x y) /\
    (forall x, \sum_y w x y = a) /\
    (forall y, \sum_x w x y <= b) /\
    (forall x y, ~~ true -> w x y = 0).
Proof.
  intros Ha Hab; apply (@finite_real_subtransport R _ _ (fun _ : unit => a)
    (fun _ : unit => b) (fun _ _ => true)).
  1: by intros.
  1: by intros; exact: le_trans Ha Hab.
  intro S; destruct (boolP (tt \in S)) as [Hin|Hout].
  - have HS : S = [set: unit].
    { apply/setP=> [[]]; by rewrite inE. }
    have HN : matching_neighbors (fun _ _ : unit => true) [set: unit] S = [set: unit].
    { apply/setP=> [[]]; apply/idP/idP; first by intros; rewrite inE.
      intros _; apply/matching_neighborsP; split; first by rewrite inE.
      exists tt; by split. }
    by rewrite HN HS !big_const /= cardsT card_unit /= !addr0.
  - have HS : S = set0.
    { apply/setP=> [[]]; by rewrite inE (negPf Hout). }
    rewrite HS big_set0; apply sumr_ge0=> y _; exact: le_trans Ha Hab.
Qed.

(** A row really splits across two differently weighted columns. *)
Example split_real_mass (a b : R) : 0 <= a -> 0 <= b ->
  exists w : unit -> bool -> R,
    (forall x y, 0 <= w x y) /\
    (forall x, \sum_y w x y = a + b) /\
    (forall y, \sum_x w x y = if y then a else b) /\
    (forall x y, ~~ true -> w x y = 0).
Proof.
  intros Ha Hb; apply (@finite_real_transport R _ _ (fun _ : unit => a + b)
    (fun y : bool => if y then a else b) (fun _ _ => true)).
  - intros; exact: addr_ge0.
  - intros []; assumption.
  - intro S; destruct (boolP (tt \in S)) as [Hin|Hout].
    + have HS : S = [set: unit].
      { apply/setP=> [[]]; by rewrite inE. }
      have HN : matching_neighbors (fun (_ : unit) (_ : bool) => true)
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

Example empty_source (q : bool -> R) : (forall y, 0 <= q y) ->
  exists w : 'I_0 -> bool -> R,
    (forall x y, 0 <= w x y) /\
    (forall x, \sum_y w x y = 0) /\
    (forall y, \sum_x w x y <= q y) /\
    (forall x y, ~~ false -> w x y = 0).
Proof.
  intro Hq; apply (@finite_real_subtransport R _ _ (fun _ : 'I_0 => 0) q (fun _ _ => false)).
  - intros; exact: lexx.
  - exact Hq.
  - intro S; rewrite big1; last by intros.
    apply sumr_ge0=> y _; exact (Hq y).
Qed.

Example zero_demand_empty_target :
  exists w : bool -> 'I_0 -> R,
    (forall x y, 0 <= w x y) /\
    (forall x, \sum_y w x y = 0) /\
    (forall y, \sum_x w x y <= 0) /\
    (forall x y, ~~ false -> w x y = 0).
Proof.
  apply (@finite_real_subtransport R _ _ (fun _ : bool => 0) (fun _ : 'I_0 => 0) (fun _ _ => false)).
  - intros; exact: lexx.
  - intros; exact: lexx.
  - intro S; rewrite !big1 //; exact: lexx.
Qed.

Example positive_demand_empty_target_impossible :
  ~ exists w : unit -> 'I_0 -> R, forall x, \sum_y w x y = 1.
Proof.
  intros [w Hw]; have H := Hw tt; rewrite big_ord0 in H.
  have Hneq : (0 : R) != 1 by rewrite eq_sym oner_eq0.
  by rewrite H eqxx in Hneq.
Qed.
End Tests.
