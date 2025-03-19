Require Import Utf8.
Require Import Reals.
Require Import ProofIrrelevance.

From mathcomp Require Import all_ssreflect.

#[local] Open Scope R_scope.

Declare Scope real_sub_scope.
Delimit Scope real_sub_scope with real_sub.
#[local] Open Scope real_sub_scope.

(** Real Subtypes *)



(** [nonneg] from StdLib *)
Notation "ℝ≥0" := nonnegreal : type_scope.
Notation "'[nn'  r ']'" :=
  {| nonneg := r; cond_nonneg := _ |}
    : real_sub_scope.


Definition nonneg_inj : nonnegreal → R
  := nonneg.

#[program]
Definition nonneg_mult (x y : ℝ≥0) : ℝ≥0 := [nn x * y].
Next Obligation. destruct x, y.
  apply Rmult_le_pos; auto.
Defined.

#[program]
Definition nonneg_add (x y : ℝ≥0) : ℝ≥0 := [nn x + y].
Next Obligation. destruct x, y.
  apply Rplus_le_le_0_compat; auto.
Defined.

Infix "*" := nonneg_mult : real_sub_scope.
Infix "+" := nonneg_add : real_sub_scope.

Lemma nonnegreal_eq : ∀ {x y : R} {Hx : 0 <= x} {Hy : 0 <= y},
    x = y → mknonnegreal x Hx = mknonnegreal y Hy.
Proof. intros. simpl in H.
  subst. assert (Hx = Hy). apply proof_irrelevance.
  subst. reflexivity.
Qed.

Lemma nonnegreal_eta : ∀ {x : nonnegreal},
    x = {| nonneg := nonneg x; cond_nonneg := cond_nonneg x |}.
Proof. intros. destruct x. simpl. reflexivity. Qed.

Ltac __nonnegreal_eq :=
  match goal with
  | |- [nn ?x] = [nn ?y] => apply nonnegreal_eq
  | _ => idtac
  end.



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
