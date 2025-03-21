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

(* 
TODO: prove nnQ is SubLattice
Lemma ge_zero_meet_closed: Order.ClosedPredicates.meet_closed (T:=rat_rat__canonical__Order_Lattice) (>= 0).
Proof.
  unfold Order.ClosedPredicates.meet_closed.
  intros x y hx hy.
  unfold in_mem; rewrite //=.
  unfold in_mem in hx, hy. rewrite //= in hx, hy.
  Unset Printing Notations.
  unfold Order.meet, Order.MeetSemilattice.class, Order_Lattice__to__Order_MeetSemilattice, Order.Lattice.class, rat_rat__canonical__Order_Lattice.
  unfold Order.POrder_isMeetSemilattice.meet.
Admitted.

Lemma ge_zero_join_closed: Order.ClosedPredicates.join_closed (T:=rat_rat__canonical__Order_Lattice) (>= 0).
Proof.
Admitted.

HB.instance Definition _ := Order.isMeetLatticeClosed.Build _ _ _ ge_zero_meet_closed.
HB.instance Definition _ := Order.isJoinLatticeClosed.Build _ _ _ ge_zero_join_closed.

HB.instance Definition _ := [SubChoice_isSubLattice of nnQ by <: with ssrnum.ring_display]. *)


Implicit Type r s x y : nnQ.

Lemma le_nnQ0 r : 0 <= r.
Proof. move: r => [r ler0]. apply: ler0. Qed.


End NonnegQ.

Module NonnegQNotations.
Open Scope order_scope.
Open Scope ring_scope.
Open Scope subrat_scope.

Notation "ℚ≥0" := nnQ : subrat_scope.
Notation "'[nn'  r ']'" := (mknnQ r _) : subrat_scope.

End NonnegQNotations.




(* Class RatSub (T : Type) := { *)
(*   inject : T -> Q; *)
(* }. *)

(** The Standard Unit Interval *)

(* Variant Interval : Type := *)
(* | mkInterval (r : R) (_ : Rle 0 r) (_ : Rle r 1). *)

(* Notation 𝕀 := R. *)

(* Global Instance Interval_RealSub : RealSub Interval := {| *)
(*   inject := fun '(mkInterval r _ _) => r *)
(* |}. *)


(** The Positive Reals *)
(* Variant NNR : Type := *)
(* | mkNNR (r : R) (_ : Rle 0 r). *)

(* Notation "ℝ₊" := R : type_scope. *)



(** The Extended Non-Negative Real Numbers
  Which is not an injection *)

(* Inductive ENNR : Type := *)
(* | mkENNR (r : R) (_ : Rle 0 r) *)
(* | pinfty. *)

(* Notation "ℝ₊∞" := R : type_scope. *)
