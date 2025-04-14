Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Warnings "-redundant-canonical-projection".
Set Warnings "-projection-no-head-constant".

Require Import Utf8.

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From mathcomp Require Import order choice.
From mathcomp Require Import ssrint rat.
From mathcomp.algebra Require Import ssralg.

#[local] Open Scope order_scope.
#[local] Open Scope ring_scope.
#[local] Open Scope rat_scope.

Declare Scope subrat_scope.
Delimit Scope subrat_scope with subrat.
#[local] Open Scope subrat_scope.

(** Rational Subtypes *)



(** Non-negative Rational Numbers (as Probability Mass) *)
Section NonnegQ.

Structure nnQ : Type := mknnQ { Qval :> rat; _ : 0 <= Qval }.

HB.instance Definition _ := [isSub for Qval].
HB.instance Definition _ := [Equality of nnQ by <:].
HB.instance Definition _ := [Choice of nnQ by <:].

Lemma ge_zero_closed : semiring_closed (R:=rat_rat__canonical__GRing_ComSemiRing) (>= 0).
Proof.
  unfold semiring_closed, addr_closed, mulr_closed.
  rewrite //=.
  split.
  - split. rewrite //=.
    intros x y hx hy. unfold in_mem; rewrite //=.
    unfold in_mem in hx, hy. rewrite //= in hx, hy.
    exact (le_rat0D hx hy).
  - split. rewrite //=.
    unfold GRing.mulr_2closed.
    intros x y hx hy. unfold in_mem; rewrite //=.
    unfold in_mem in hx, hy. rewrite //= in hx, hy.
    exact (le_rat0M hx hy).
Qed.
HB.instance Definition _ := GRing.isSemiringClosed.Build _ _ ge_zero_closed.
HB.instance Definition _ := [SubChoice_isSubComSemiRing of nnQ by <:].
HB.instance Definition _ := [SubChoice_isSubOrder of nnQ by <: with ssrnum.ring_display].


Lemma le_nnQ0 (r : nnQ) : 0 <= r.
Proof. move: r => [r ler0]. apply: ler0. Qed.

Lemma le_nnQ_of_le_Q {p q : nnQ} (hq: Qval p <= Qval q) : p <= q.
Proof. exact hq. Qed.

Lemma lt_nnQ_of_lt_Q {p q : nnQ} (hq: Qval p < Qval q) : p < q.
Proof. exact hq. Qed.

Lemma le_nnQ_iff_le_Q {p q : nnQ}: Qval p <= Qval q = (p <= q).
Proof. reflexivity. Qed.

Lemma lt_nnQ_iff_lt_Q {p q : nnQ}: Qval p < Qval q = (p < q).
Proof. reflexivity. Qed.


#[local] Open Scope order_scope.
#[local] Open Scope ring_scope.

Definition nnQ_0 := mknnQ 0 (Order.POrderTheory.lexx (0:rat)).

Lemma lt_0_nnQ_iff_ne_0 {p: nnQ}: p != nnQ_0 <-> nnQ_0 < p.
Proof.
  split.
  - move => ne. rewrite /nnQ_0 //=.
    have le0 := le_nnQ0 p. rewrite Order.POrderTheory.lt_def. apply/andP. split.
    exact ne. exact le0.
  - move => lt. rewrite Order.POrderTheory.lt_def in lt. move: (andP lt) => [r _]. exact r.
Qed.

Lemma le_nnQ_0_iff_eq_0 {p: nnQ}: p <= nnQ_0 <-> p == nnQ_0 .
Proof.
  have le0 := le_nnQ0 p.
  split.
  - move => lep0. rewrite ssrnum.Num.Theory.le0r in le0.
    rewrite -le_nnQ_iff_le_Q //= in lep0.
    case: le0 => /orP [eq0|lt0p]. exact: eq0.
    rewrite Order.TotalTheory.ltNge in lt0p.
    rewrite lep0 //= in lt0p.
  - move => /eqP e. rewrite e //=.
Qed.

Lemma nnQ_lerD {p q m n: nnQ}: p <= q -> m <= n -> p + m <= q + n.
Proof.
  move => h1 h2.
  apply le_nnQ_of_le_Q. apply ssrnum.Num.Theory.lerD.
  exact: h1. exact: h2.
Qed.

Lemma pos_of_pos_add {p q: nnQ} (p_pos: nnQ_0 < p): nnQ_0 < p + q.
Proof.
  apply ssrnum.Num.Theory.ltr_wpDr. exact (le_nnQ0 q). exact p_pos.
Qed.

Lemma pos_of_add_pos {p q: nnQ} (q_pos: nnQ_0 < q): nnQ_0 < p + q.
Proof.
  apply ssrnum.Num.Theory.ltr_wpDl. exact (le_nnQ0 p). exact q_pos.
Qed.

Lemma ne0_of_ne0_add {p q: nnQ} (p_pos: p != nnQ_0): p + q != nnQ_0.
Proof.
  rewrite lt_0_nnQ_iff_ne_0. rewrite lt_0_nnQ_iff_ne_0 in p_pos. exact (pos_of_pos_add p_pos).
Qed.

Lemma ne0_of_add_ne0 {p q: nnQ} (q_pos: q != nnQ_0): p + q != nnQ_0.
Proof.
  rewrite lt_0_nnQ_iff_ne_0. rewrite lt_0_nnQ_iff_ne_0 in q_pos. exact (pos_of_add_pos q_pos).
Qed.

End NonnegQ.

Module NonnegQNotations.
Open Scope order_scope.
Open Scope ring_scope.
Open Scope subrat_scope.

Notation "ℚ≥0" := nnQ : subrat_scope.
Notation "'[nn'  r ']'" := (mknnQ r _) : subrat_scope.

End NonnegQNotations.


(** The Standard Unit Interval *)
Section IntervalQ.
Import NonnegQNotations.
Structure IntervalQ : Type := mkIntervalQ { IntervalVal :> ℚ≥0; _ : IntervalVal <= 1 }.

HB.instance Definition _ := [isSub for IntervalVal].
HB.instance Definition _ := [Equality of IntervalQ by <:].
HB.instance Definition _ := [Choice of IntervalQ by <:].
HB.instance Definition _ := [SubChoice_isSubOrder of IntervalQ by <: with ssrnum.ring_display].


Lemma le_0IntervalQ r : mkIntervalQ 0 ssrnum.Num.Theory.ler01 <= r.
Proof. move: r => [[r le0r] ler1]. apply: le0r. Qed.

#[program]
Lemma le_IntervalQ1 r : r <= mkIntervalQ 1 _.
Proof. move: r => [r ler1]. apply: ler1. Qed.

Lemma mulq_IntervalQP (x y: IntervalQ) : (IntervalVal x) * (IntervalVal y) <= 1.
Proof.
  have h1 := ssrnum.Num.Theory.ler_piMr (le_0IntervalQ x) (le_IntervalQ1 y).
  have h2 := le_IntervalQ1 x.
  apply (Order.POrderTheory.le_trans h1 h2).
Qed.
Canonical mulq_IntervalQ x y := mkIntervalQ ((IntervalVal x) * (IntervalVal y)) (mulq_IntervalQP x y).

End IntervalQ.
