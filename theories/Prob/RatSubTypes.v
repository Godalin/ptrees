Require Import Utf8.

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From mathcomp Require Import order.
From mathcomp Require Import ssrint rat.

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

HB.instance Definition _ : hasDecEq nnQ :=
  [Equality of nnQ by <:].
(* Canonical nnQ_predType := PredType (pred_of_rat :  -> bool) *)

Implicit Type r s x y : nnQ.

Lemma le_nnQ0 r : 0 <= r.
Proof. move: r => [r ler0]. apply: ler0. Qed.

Lemma mulq_nnQP x y : 0 <= x * y.
Proof. apply: le_rat0M; apply le_nnQ0. Qed.
Canonical mulq_nnQ x y := mknnQ (x * y) (mulq_nnQP x y).

Lemma addq_nnQP x y : 0 <= x + y.
Proof. apply: le_rat0D; apply le_nnQ0. Qed.
Canonical addq_nnQ x y := mknnQ (x + y) (addq_nnQP x y).

#[program] Canonical zero_nnQ := mknnQ 0 _.
#[program] Canonical one_nnQ := mknnQ (1 : rat) _.

End NonnegQ.

Module NonnegQNotations.
Open Scope order_scope.
Open Scope ring_scope.
Open Scope rat_scope.
Open Scope subrat_scope.

Notation "ℚ≥0" := nnQ : subrat_scope.
Notation "'[nn'  r ']'" := (mknnQ r _) : subrat_scope.

End NonnegQNotations.

Section test.
Check 0 : nnQ.
End test.

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
