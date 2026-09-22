(** Positive support of finite ordinary-scalar weightings. Nonnegativity is
    an explicit container invariant, never a property of arbitrary scalars.
    No equality on values is required for indicator/support transport. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg ssrnum order.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteAtoms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Support.
Variable R : numDomainType.

Lemma finite_nonnegative_tail {A} (p : R) (x : A) mu :
  finite_nonnegative ((p,x)::mu) -> finite_nonnegative mu.
Proof. move=> H q y Hy; exact (H q y (or_intror Hy)). Qed.

Lemma finite_indicator_nonnegative {A} (mu : list (R*A)) (P : A -> bool) :
  finite_nonnegative mu -> 0 <= finite_expect (fun x => if P x then 1 else 0) mu.
Proof.
  move=> H; apply finite_expect_nonnegative; first exact H.
  move=> x; by case: (P x).
Qed.

Lemma finite_indicator_positive_member {A} (mu : list (R*A)) (P : A -> bool) :
  0 < finite_expect (fun x => if P x then 1 else 0) mu ->
  exists p x, List.In (p,x) mu /\ p <> 0 /\ P x.
Proof.
  elim: mu=> [|[p x] mu IH]; first by rewrite /= ltxx.
  move=> H; case Hp: (p == 0).
  - move/eqP: Hp=> Hp; subst p; rewrite /= mul0r add0r in H.
    have [q [y [Hy [Hq HP]]]] := IH H.
    exists q,y; split; first by right.
    by split.
  - case Hx: (P x).
    + exists p,x; split; first by left.
      split; last exact Hx.
      by apply/eqP; rewrite Hp.
    + rewrite /= Hx mulr0 add0r in H.
      have [q [y [Hy [Hq HP]]]] := IH H.
      exists q,y; split; first by right.
      by split.
Qed.

Lemma finite_indicator_member_positive {A} (mu : list (R*A)) (P : A -> bool) p x :
  finite_nonnegative mu -> List.In (p,x) mu -> p <> 0 -> P x ->
  0 < finite_expect (fun x => if P x then 1 else 0) mu.
Proof.
  elim: mu=> [|[q y] mu IH]; first by move=> _ [].
  move=> Hnn [He|Hin] Hnz Hx.
  - inversion He; subst q y; rewrite /= Hx mulr1.
    apply lt_le_trans with (y := p).
    + rewrite lt_neqAle; apply/andP; split.
      * apply/eqP=> Heq; apply Hnz; symmetry; exact Heq.
      * exact (Hnn p x (or_introl (Logic.eq_refl _))).
    + rewrite lerDl; apply finite_indicator_nonnegative.
      exact (finite_nonnegative_tail Hnn).
  - simpl; eapply lt_le_trans.
    + exact (IH (finite_nonnegative_tail Hnn) Hin Hnz Hx).
    + rewrite lerDr; apply mulr_ge0.
      * exact (Hnn q y (or_introl (Logic.eq_refl _))).
      * by case: (P y).
Qed.

Lemma finite_atom_positive_iff {A : eqType} (mu : list (R*A)) x :
  finite_nonnegative mu ->
  (0 < finite_atom x mu <-> exists p, List.In (p,x) mu /\ p <> 0).
Proof.
  move=> H; split.
  - move/finite_indicator_positive_member=> [p [y [Hin [Hp /eqP He]]]].
    subst y; by exists p.
  - move=> [p [Hin Hp]].
    exact (finite_indicator_member_positive (P := fun y => y == x) H Hin Hp (eqxx x)).
Qed.

Lemma finite_atom_zero_iff {A : eqType} (mu : list (R*A)) x :
  finite_nonnegative mu ->
  (finite_atom x mu = 0 <-> forall p, List.In (p,x) mu -> p = 0).
Proof.
  move=> H; split.
  - move=> Hz p Hin; case Hp: (p == 0); first exact (eqP Hp).
    have Hnz : p <> 0 by apply/eqP; rewrite Hp.
    have Hpos := finite_indicator_member_positive (P := fun y => y == x) H Hin Hnz (eqxx x).
    change (is_true (0 < finite_atom x mu)) in Hpos; by rewrite Hz ltxx in Hpos.
  - move=> Hz; case Hp: (finite_atom x mu == 0); first exact (eqP Hp).
    have Hpos : 0 < finite_atom x mu.
    { rewrite lt_neqAle eq_sym Hp /=; exact: finite_atom_nonnegative. }
    have [p [Hin Hnz]] := proj1 (finite_atom_positive_iff x H) Hpos.
    exfalso; exact (Hnz (Hz p Hin)).
Qed.

Lemma finite_expect_entry_le {A} (mu : list (R*A)) f p x :
  finite_nonnegative mu -> (forall x, 0 <= f x) -> List.In (p,x) mu ->
  p * f x <= finite_expect f mu.
Proof.
  elim: mu=> [|[q y] mu IH]; first by move=> _ _ [].
  move=> Hnn Hf [He|Hin].
  - inversion He; subst; rewrite /= lerDl.
    exact (finite_expect_nonnegative (finite_nonnegative_tail Hnn) Hf).
  - simpl; apply le_trans with (y := finite_expect f mu).
    + exact (IH (finite_nonnegative_tail Hnn) Hf Hin).
    + rewrite lerDr; apply mulr_ge0; last exact (Hf y).
      exact (Hnn q y (or_introl (Logic.eq_refl _))).
Qed.
End Support.
