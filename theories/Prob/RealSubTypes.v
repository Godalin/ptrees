Require Import Reals.
Require Export Rbase.
Open Scope R_scope.

From ExtLib Require Import Structures.Monoid.

Declare Scope real_sub_scope.
Delimit Scope real_sub_scope with real_sub.
Local Open Scope real_sub_scope.



(** Real Subtypes *)

Class RealSub (T : Type) := {
  inject : T -> R;
}.



(** The Standard Unit Interval *)

Variant Interval : Type :=
| mkInterval (r : R) (_ : Rle 0 r) (_ : Rle r 1).

Notation 𝕀 := R.

Global Instance Interval_RealSub : RealSub Interval := {|
  inject := fun '(mkInterval r _ _) => r
|}.

(** The Non-Negative Real Numbers *)



(** The Positive Reals *)
Variant NNR : Type :=
| mkNNR (r : R) (_ : Rle 0 r).

Notation "ℝ₊" := R : type_scope.



(** The Extended Non-Negative Real Numbers
  Which is not an injection *)

Inductive ENNR : Type :=
| mkENNR (r : R) (_ : Rle 0 r)
| pinfty.

Notation "ℝ₊∞" := R : type_scope.
