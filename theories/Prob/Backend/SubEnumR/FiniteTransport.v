(** Native finite-real transport. Bounded tests on decoded values produce
    an actual joint on the original sample carriers, including duplicates
    and zero entries. No external domain or FreeOmega dependency. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype
  finset bigop ssralg ssrnum order reals boolp.
From PTree.Prob.Backend.Common Require Import FiniteEnum FinitePresentation FiniteMatching RealTransport.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling.
From PTree.Prob.Interface Require Import Measure SemanticCoupling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Transport.
Variable R : realType.

Lemma real_expect_weighted_list {I A} (xs : seq I) (w : I -> R) (v : I -> A) f :
  finite_expect f [seq (w i, v i) | i <- xs] = \sum_(i <- xs) w i * f (v i).
Proof.
  elim: xs=> [|i xs IH].
  - by rewrite big_nil.
  - by rewrite /= big_cons IH.
Qed.

Lemma subenumR_expect_positions {A} (mu : SubEnumR R A) f :
  subenumR_expect mu f =
    \sum_i finite_position_weight (subenumR_raw mu) i *
      f (finite_position_value (subenumR_raw mu) i).
Proof.
  rewrite /subenumR_expect /real_enum_expect -finite_positions_expect
    /finite_positions.
  rewrite real_expect_weighted_list.
  by rewrite big_enum.
Qed.

Theorem subenumR_transport_of_mapped_tests {X Y A B}
    (mu : SubEnumR R X) (nu : SubEnumR R Y)
    (f : X -> A) (g : Y -> B) (T : A -> B -> Prop) :
  (forall a b,
    (forall x, 0 <= a x /\ a x <= 1) ->
    (forall y, 0 <= b y /\ b y <= 1) ->
    (forall x y, T x y -> a x <= b y) ->
    subenumR_expect mu (fun x => a (f x)) <=
    subenumR_expect nu (fun y => b (g y))) ->
  subenumR_expect mu (fun _ => 1) = subenumR_expect nu (fun _ => 1) ->
  subenumR_lift (fun x y => T (f x) (g y)) mu nu.
Proof.
  intros Htests Hmass.
  pose I := finite_position (subenumR_raw mu).
  pose J := finite_position (subenumR_raw nu).
  pose p := finite_position_weight (subenumR_raw mu).
  pose q := finite_position_weight (subenumR_raw nu).
  pose x := finite_position_value (subenumR_raw mu).
  pose y := finite_position_value (subenumR_raw nu).
  have Hp i : 0 <= p i.
  { have H := finite_position_entry_in (subenumR_raw mu) i.
    rewrite (surjective_pairing (finite_position_entry (subenumR_raw mu) i)) in H.
    exact (@subenumR_nonnegative R X mu (p i) (x i) H). }
  have Hq j : 0 <= q j.
  { have H := finite_position_entry_in (subenumR_raw nu) j.
    rewrite (surjective_pairing (finite_position_entry (subenumR_raw nu) j)) in H.
    exact (@subenumR_nonnegative R Y nu (q j) (y j) H). }
  pose edge (i : I) (j : J) := asbool (T (f (x i)) (g (y j))).
  have Hall : real_transport_hall p q edge.
  { intro S.
    pose P a := exists i : I, i \in S /\ f (x i) = a.
    pose Q b := exists i : I, i \in S /\ T (f (x i)) b.
    pose a z : R := if asbool (P z) then 1 else 0.
    pose b z : R := if asbool (Q z) then 1 else 0.
    have Ha z : 0 <= a z /\ a z <= 1.
    { rewrite /a; case: (asbool (P z)); split; try exact: lexx; exact: ler01. }
    have Hb z : 0 <= b z /\ b z <= 1.
    { rewrite /b; case: (asbool (Q z)); split; try exact: lexx; exact: ler01. }
    have Hab z v : T z v -> a z <= b v.
    { intro H; rewrite /a /b; case Hpz: (asbool (P z)); last exact (proj1 (Hb v)).
      have /asboolP [i [Hi He]] := Hpz.
      subst z.
      have -> : asbool (Q v) = true by apply/asboolP; exists i; split.
      exact: lexx. }
    have H := Htests a b Ha Hb Hab.
    rewrite !subenumR_expect_positions in H.
    have Hright : \sum_j q j * b (g (y j)) =
        \sum_(j in matching_neighbors edge setT S) q j.
    { rewrite [RHS]big_mkcond; apply eq_bigr=> j _.
      have He : asbool (Q (g (y j))) = (j \in matching_neighbors edge setT S).
      { apply/idP/idP.
        - move/asboolP=> [i [Hi HT]]; apply/matching_neighborsP.
          split; first by rewrite inE.
          exists i; split; first exact Hi; exact/asboolP.
        - move/matching_neighborsP=> [_ [i [Hi /asboolP HT]]].
          apply/asboolP; exists i; by split. }
      rewrite /b He; by case: (j \in matching_neighbors edge setT S); rewrite ?mulr0 ?mulr1. }
    rewrite Hright in H; apply: le_trans H.
    rewrite [X in X <= _]big_mkcond; apply ler_sum=> i _.
      case Hi: (i \in S).
      + have -> : a (f (x i)) = 1 by rewrite /a; have -> : asbool (P (f (x i))) = true by apply/asboolP; exists i; split.
        by rewrite mulr1.
      + apply mulr_ge0; [exact (Hp i)|exact (proj1 (Ha _))]. }
  have Htotal : \sum_i p i = \sum_j q j.
  { rewrite !subenumR_expect_positions -!mulr_suml !mulr1 in Hmass.
    exact Hmass. }
  destruct (finite_real_transport Hp Hq Hall Htotal) as [w [Hw [Hr [Hc Hs]]]].
  pose raw := [seq (w z.1 z.2, (x z.1,y z.2)) |
    z <- enum (@Finite.Pack (I * J)%type (Finite.on (I * J)%type))].
  have Hraw h : real_enum_expect h raw =
      \sum_i \sum_j w i j * h (x i,y j).
  { by rewrite /raw /real_enum_expect real_expect_weighted_list big_enum pair_big. }
  have Hleft h : real_enum_expect (fun xy => h (fst xy)) raw = subenumR_expect mu h.
  { rewrite Hraw subenumR_expect_positions; apply eq_bigr=> i _.
    by rewrite /= -mulr_suml Hr. }
  have Hright h : real_enum_expect (fun xy => h (snd xy)) raw = subenumR_expect nu h.
  { rewrite Hraw exchange_big subenumR_expect_positions; apply eq_bigr=> j _.
    by rewrite /= -mulr_suml Hc. }
  have Hnn : real_enum_nonnegative raw.
  { intros r z Hz; apply List.in_map_iff in Hz.
    destruct Hz as [[i j] [He _]]; inversion He; subst; exact: Hw. }
  have Hbound : real_enum_expect (fun _ => 1) raw <= 1.
  { rewrite (Hleft (fun _ => 1)); exact: subenumR_mass_bound. }
  exists (subenumR_of_list Hnn Hbound); split; first exact Hleft.
  split; first exact Hright.
  intros r z Hz Hnz; apply List.in_map_iff in Hz.
  destruct Hz as [[i j] [He _]]; inversion He; subst.
  apply/asboolP; apply/negPn/negP=> Hmiss; apply Hnz; exact (Hs i j Hmiss).
Qed.

Lemma subenumR_lift_realization {A B} (T : A -> B -> Prop)
    (mu : SubEnumR R A) (nu : SubEnumR R B) :
  subenumR_lift T mu nu -> exists joint,
    @semantic_coupling (SubEnumR R) (SubEnumR_SemanticMeasure R) A B T mu nu joint.
Proof.
  intros [j [Hl [Hr Hj]]]; exists j; split.
  - eapply sem_lift_proper_r; [|exact (subenumR_lift_map fst j)].
    intro f; rewrite subenumR_expect_map; exact (Hl f).
  - split; last exact Hj.
    eapply sem_lift_proper_r; [|exact (subenumR_lift_map snd j)].
    intro f; rewrite subenumR_expect_map; exact (Hr f).
Qed.
End Transport.
