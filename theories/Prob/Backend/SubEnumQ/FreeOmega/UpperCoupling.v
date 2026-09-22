(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From Coq.Program Require Import Equality.
From Coq.Arith Require Import PeanoNat.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat ssralg ssrnum order rat reals.
Require Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Bind PTree.Prob.Backend.EnumQ.Coupling PTree.Prob.Backend.EnumQ.SemanticCoupling.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure PTree.Prob.Backend.SubEnumQ.Measure PTree.Prob.Backend.EnumQ.FrontierLift.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperExpectation.

Require Import PTree.Prob.Backend.SubEnumQ.Expectation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Coupling GRing.Theory Num.Theory Order.Theory.
Import EnumQCouplingClassical.
Local Open Scope ring_scope.

(** Raw finite-subbehavior order is numerically monotone even on arbitrary
    formal Lub terms.  This is a proved bridge to the numeric model, not
    a new order/reflection capability imposed on the backend. *)
Section RawScalarCoupling.
Variable F : realType.
Local Notation upper := (free_omega_upper (R := F)).

Theorem free_omega_sample_bind_upper {A X Y} (mu : SubEnumQ X)
    (k : X -> SubEnumQ Y) (h : Y -> FreeOmega SubEnumQ A) (f : A -> F) :
  upper (FOSample mu (fun x => FOSample (k x) h)) f =
  upper (FOSample (subenumQ_bind mu k) h) f.
Proof. cbn [free_omega_upper subenumQ_bind subenumQ_raw]. symmetry. apply enumQ_real_expect_bind. Qed.

Theorem free_omega_approx_upper {A B} (T : A -> B -> Prop)
    (mu : FreeOmega SubEnumQ A) (nu : FreeOmega SubEnumQ B)
    (f : A -> F) (g : B -> F) :
  free_omega_approx T mu nu ->
  (forall y, 0 <= g y /\ g y <= 1) ->
  (forall x y, T x y -> f x <= g y) -> upper mu f <= upper nu g.
Proof.
  intros Happrox Hg Hfg. induction Happrox; cbn [free_omega_upper].
  - exact (proj1 (free_omega_upper_bounds nu Hg)).
  - exact (Hfg x y H).
  - apply (subenumQ_lift_real_expect H). exact H1.
  - apply countable_upper_le. intro n. apply: le_trans (H0 n) _.
    exact (@countable_upper_ge F (fun i => upper (d i) g) 1 n
      (fun i => proj2 (free_omega_upper_bounds (d i) Hg))).
Qed.

Theorem free_omega_structural_upper {A B} (T : A -> B -> Prop)
    (mu : FreeOmega SubEnumQ A) (nu : FreeOmega SubEnumQ B)
    (f : A -> F) (g : B -> F) :
  free_omega_lift T mu nu ->
  (forall y, 0 <= g y /\ g y <= 1) ->
  (forall x y, T x y -> f x <= g y) -> upper mu f <= upper nu g.
Proof. intro H. apply free_omega_approx_upper. exact (free_omega_lift_to_approx H). Qed.

Theorem free_omega_upper_ae_mono {A} (mu : FreeOmega SubEnumQ A)
    (f g : A -> F) :
  (forall y, 0 <= g y /\ g y <= 1) ->
  free_omega_ae (fun x => f x <= g x) mu -> upper mu f <= upper mu g.
Proof.
  intro Hg. induction mu as [x| |X node k IH|chain IH]; intro Hae;
    cbn [free_omega_upper].
  - dependent destruction Hae. assumption.
  - exact: lexx.
  - apply enumQ_real_expect_ae_mono.
    change (@sem_ae SubEnumQ SubEnumQ_SemanticMeasure X node
      (fun x => upper (k x) f <= upper (k x) g)).
    eapply sem_ae_mono; [|exact (free_omega_ae_sample_inv Hae)].
    intros x Hx. exact (IH x Hx).
  - dependent destruction Hae. apply countable_upper_le. intro n.
    apply: le_trans (IH n (H n)) _.
    exact (@countable_upper_ge F (fun i => upper (chain i) g) 1 n
      (fun i => proj2 (free_omega_upper_bounds (chain i) Hg))).
Qed.

Theorem free_omega_upper_ae_ext {A} (mu : FreeOmega SubEnumQ A)
    (f g : A -> F) :
  (forall x, 0 <= f x /\ f x <= 1) ->
  (forall y, 0 <= g y /\ g y <= 1) ->
  free_omega_ae (fun x => f x = g x) mu -> upper mu f = upper mu g.
Proof.
  intros Hf Hg Hae. apply/eqP. rewrite eq_le. apply/andP. split.
  - apply free_omega_upper_ae_mono; [exact Hg|].
    eapply free_omega_ae_mono; [|exact Hae].
    intros x Hx. rewrite Hx. exact: lexx.
  - apply free_omega_upper_ae_mono; [exact Hf|].
    eapply free_omega_ae_mono; [|exact Hae].
    intros x Hx. rewrite Hx. exact: lexx.
Qed.

Lemma free_omega_upper_approx_mono {A} (mu nu : FreeOmega SubEnumQ A) (f : A -> F) :
  free_omega_approx eq mu nu ->
  (forall x, 0 <= f x /\ f x <= 1) -> upper mu f <= upper nu f.
Proof.
  intros H Hf. eapply free_omega_approx_upper; [exact H|exact Hf|].
  intros x y ->. exact: lexx.
Qed.

(** One-sided cofinal domination already suffices for the corresponding
    numeric inequality; mutual domination gives equality below.  No
    quotient conclusion is used in either proof. *)
Theorem free_omega_cofinal_upper_le {A B} (T : A -> B -> Prop)
    (left : nat -> FreeOmega SubEnumQ A) (right : nat -> FreeOmega SubEnumQ B)
    (f : A -> F) (g : B -> F) :
  (forall n, exists m, free_omega_approx T (left n) (right m)) ->
  (forall y, 0 <= g y /\ g y <= 1) ->
  (forall x y, T x y -> f x <= g y) ->
  upper (FOLub left) f <= upper (FOLub right) g.
Proof.
  intros Hcover Hg Hfg. cbn [free_omega_upper]. apply countable_upper_le. intro n.
  destruct (Hcover n) as [m Hnm].
  eapply le_trans; [exact (free_omega_approx_upper Hnm Hg Hfg)|].
  exact (@countable_upper_ge F (fun i => upper (right i) g) 1 m
    (fun i => proj2 (free_omega_upper_bounds (right i) Hg))).
Qed.

Theorem free_omega_cofinal_upper_eq {A}
    (left right : nat -> FreeOmega SubEnumQ A) (f : A -> F) :
  free_omega_chains_cofinal eq left right ->
  (forall x, 0 <= f x /\ f x <= 1) ->
  upper (FOLub left) f = upper (FOLub right) f.
Proof.
  intros [Hl Hr] Hf. apply/eqP. rewrite eq_le. apply/andP. split.
  - eapply free_omega_cofinal_upper_le; [exact Hl|exact Hf|].
    intros x y ->. exact: lexx.
  - eapply free_omega_cofinal_upper_le; [exact Hr|exact Hf|].
    intros x y ->. exact: lexx.
Qed.

(** Numeric validation of the same monotone-grid hypothesis used by
    FOQLDoubleDiagonal.  Suprema commute with the diagonal because every
    grid cell is dominated by a later diagonal cell, not because arbitrary
    convergent double sequences may be exchanged. *)
Theorem free_omega_diagonal_upper {A}
    (grid : nat -> nat -> FreeOmega SubEnumQ A) (f : A -> F) :
  (forall i j, free_omega_approx eq (grid i j) (grid i (S j))) ->
  (forall i j, free_omega_approx eq (grid i j) (grid (S i) j)) ->
  (forall x, 0 <= f x /\ f x <= 1) ->
  upper (FOLub (fun i => FOLub (grid i))) f =
  upper (FOLub (fun n => grid n n)) f.
Proof.
  intros Hrow Hcol Hf.
  have Hbound : forall i j, upper (grid i j) f <= 1 :=
    fun i j => proj2 (free_omega_upper_bounds (grid i j) Hf).
  have Hcover : forall i j, free_omega_approx eq (grid i j)
      (grid (Nat.add i j) (Nat.add i j)).
  { intros i j. eapply free_omega_approx_trans with (nu := grid i (Nat.add i j)).
    - pose proof (free_omega_approx_steps (Hrow i) j i) as Hr.
      rewrite (Nat.add_comm j i) in Hr. exact Hr.
    - exact (free_omega_approx_steps (fun k => Hcol k (Nat.add i j)) i j). }
  apply/eqP. rewrite eq_le. apply/andP. split; cbn [free_omega_upper].
  - apply countable_upper_le. intro i. apply countable_upper_le. intro j.
    eapply le_trans; [exact (free_omega_upper_approx_mono (Hcover i j) Hf)|].
    exact (@countable_upper_ge F (fun n => upper (grid n n) f) 1 (Nat.add i j)
      (fun n => Hbound n n)).
  - apply countable_upper_le. intro n.
    eapply le_trans.
    + exact (@countable_upper_ge F (fun j => upper (grid n j) f) 1 n (Hbound n)).
    + exact (@countable_upper_ge F
        (fun i => countable_upper (fun j => upper (grid i j) f)) 1 n
        (fun i => countable_upper_le (Hbound i))).
Qed.
End RawScalarCoupling.
