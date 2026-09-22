(** Native finite-real order and convergence predicates. Finite support is
    NOT omega-complete; no native SemanticOmegaLaws instance is asserted.
    The generic FreeOmega construction supplies completion. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Interface Require Import Measure Omega.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling.
Set Implicit Arguments.
Unset Strict Implicit.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section NativeOmega.
Variable R : realType.
Definition subenumR_test {A} (f : A -> R) := forall x, 0 <= f x /\ f x <= 1.
Definition subenumR_le {A} (mu nu : SubEnumR R A) :=
  forall f, subenumR_test f -> subenumR_expect mu f <= subenumR_expect nu f.
Definition subenumR_lub {A} (c : nat -> SubEnumR R A) (out : SubEnumR R A) :=
  forall f, subenumR_test f ->
    (forall n, subenumR_expect (c n) f <= subenumR_expect out f) /\
    (forall b, (forall n, subenumR_expect (c n) f <= b) -> subenumR_expect out f <= b).
Definition subenumR_total {A} (mu : SubEnumR R A) := subenumR_expect mu (fun _ => 1) = 1.

#[global] Instance SubEnumR_SemanticOmega :
  @SemanticOmega (SubEnumR R) (SubEnumR_SemanticMeasure R) := {
  sem_zero := @subenumR_zero R;
  sem_le := @subenumR_le;
  sem_lub := @subenumR_lub;
  sem_total := @subenumR_total
}.

Lemma subenumR_expect_test {A} (mu : SubEnumR R A) f :
  subenumR_test f -> 0 <= subenumR_expect mu f /\ subenumR_expect mu f <= 1.
Proof.
  intro H; split.
  - apply real_enum_expect_nonnegative; [exact (@subenumR_nonnegative R A mu)|intro x; exact (proj1 (H x))].
  - apply: le_trans (_ : subenumR_expect mu (fun _ => 1) <= 1).
    + apply real_enum_expect_mono; [exact (@subenumR_nonnegative R A mu)|intro x; exact (proj2 (H x))].
    + exact (@subenumR_mass_bound R A mu).
Qed.

#[global] Instance SubEnumR_SemanticMeasureOrderLaws :
  @SemanticMeasureOrderLaws (SubEnumR R) (SubEnumR_SemanticMeasure R) SubEnumR_SemanticOmega.
Proof.
  constructor; cbn.
  - intros A mu f Hf; exact: lexx.
  - intros A mu nu xi H1 H2 f Hf; exact: le_trans (H1 f Hf) (H2 f Hf).
  - intros A mu f Hf; exact (proj1 (subenumR_expect_test mu Hf)).
  - intros A B mu nu k H f Hf; rewrite !subenumR_expect_bind.
    apply H; intro x; exact (subenumR_expect_test (k x) Hf).
  - intros A B mu k h H f Hf; rewrite !subenumR_expect_bind.
    apply real_enum_expect_mono; [exact (@subenumR_nonnegative R A mu)|intro x; exact (H x f Hf)].
Qed.

#[global] Instance SubEnumR_SemanticTotalProperLaws :
  @SemanticTotalProperLaws (SubEnumR R) (SubEnumR_SemanticMeasure R) SubEnumR_SemanticOmega.
Proof.
  constructor; intros A mu nu He.
  change (subenumR_total mu <-> subenumR_total nu).
  unfold subenumR_total; rewrite (He (fun _ => 1)); reflexivity.
Qed.
End NativeOmega.
