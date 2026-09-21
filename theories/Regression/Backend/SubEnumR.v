(** Finite-real native and generic completion validation contracts. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List Arith.PeanoNat.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Interface Require Import Measure Subprobability AE.
From PTree.Prob.Domain Require Import Expectation.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega.Validation Require Import Expectation.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Domain.
From PTree.Prob.Backend.SubEnumR.FreeOmega Require Import Validation.

Fail Check PTree.Prob.Backend.SubEnum.Measure.SubEnum.
Fail Check PTree.Prob.Backend.SubEnum.FreeOmega.Admissibility.free_omega_admissible.
Fail Check PTree.Prob.Backend.MathComp.Kernel.MathCompKernelMeasure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.

Section Tests.
Variable R : realType.
Local Notation native := (fun X => @subenumR_domain R X).

Definition real_sqrt_weight : R := Num.sqrt (1 / 2).
Lemma real_sqrt_weight_nonnegative : 0 <= real_sqrt_weight.
Proof. exact: sqrtr_ge0. Qed.
Lemma real_sqrt_weight_bounded : real_sqrt_weight <= 1.
Proof.
  have Hhalf : (1 : R) / 2 <= 1 by rewrite ler_pdivrMr ?ltr0n // mul1r ler1n.
  have H := ler_wsqrtr Hhalf; by rewrite sqrtr1 in H.
Qed.
Definition real_sqrt_coin := subenumR_coin real_sqrt_weight_nonnegative real_sqrt_weight_bounded.
Example real_sqrt_coin_probability :
  oval_eval (subenumR_domain real_sqrt_coin) (fun b => if b then 1 else 0) = real_sqrt_weight.
Proof. by rewrite /= /subenumR_expect /= mulr1 mulr0 !addr0. Qed.
Example real_sqrt_coin_total : oval_mass (subenumR_domain real_sqrt_coin) = 1.
Proof. by rewrite /oval_mass /= /subenumR_expect /= !mulr1 addr0 addrC subrK. Qed.

Example real_bind_valid {A B} (mu : SubEnumR R A) (k : A -> SubEnumR R B) :
  sem_subprob (sem_bind mu k).
Proof. apply sem_subprob_all. Qed.

Definition real_alternating : FreeOmega (SubEnumR R) bool :=
  FOLub (fun n => FORet (if Nat.even n then false else true)).
Lemma real_alternating_test f b : oval_test f -> f b = 1 ->
  free_omega_model_upper native real_alternating f = 1.
Proof.
  intros Hf Hb; apply/eqP; rewrite eq_le; apply/andP; split.
  - exact (proj2 (model_upper_bounds native real_alternating Hf)).
  - rewrite -Hb; unfold real_alternating; cbn [free_omega_model_upper].
    destruct b.
    + exact (@oval_sup_ge R (fun n => f (if Nat.even n then false else true)) 1 1%nat (fun n => proj2 (Hf _))).
    + exact (@oval_sup_ge R (fun n => f (if Nat.even n then false else true)) 1 0%nat (fun n => proj2 (Hf _))).
Qed.
Example real_alternating_invalid : ~ free_omega_modelable native real_alternating.
Proof.
  intro H; pose f := fun b : bool => if b then (1 : R) else 0.
  pose g := fun b : bool => if b then (0 : R) else 1.
  have Hf : oval_test f by intros []; split; try exact: lexx; exact: ler01.
  have Hg : oval_test g by intros []; split; try exact: lexx; exact: ler01.
  have Hfg : forall b, f b + g b <= 1 by intros []; rewrite /f /g ?addr0 ?add0r.
  have Hsum := oval_test_add Hf Hg Hfg.
  have Hbad := oval_add H Hf Hg Hfg.
  rewrite (@real_alternating_test f true Hf (Logic.eq_refl _))
    (@real_alternating_test g false Hg (Logic.eq_refl _))
    (@real_alternating_test (fun b => f b + g b) true Hsum (addr0 1)) in Hbad.
  have Hlt : (1 : R) < 1 + 1 by rewrite ltrDr ltr01.
  by rewrite -Hbad ltxx in Hlt.
Qed.

Definition real_certain_coin := subenumR_coin (R := R) ler01 (lexx 1).
Example real_null_bad_branch_valid :
  free_omega_modelable native
    (FOSample real_certain_coin (fun b => if b then FORet true else real_alternating)).
Proof.
  apply subenumR_free_omega_sample_ae.
  intros p b [H|[H|[]]] Hnz; inversion H; subst.
  - exact: modelable_ret.
  - exfalso; apply Hnz; exact: subrr.
Qed.

Definition real_delayed_dirac : FreeOmega (SubEnumR R) bool :=
  FOLub (fun n => match n with O => FOZero | S _ => FORet true end).
Example real_delayed_dirac_valid : free_omega_modelable native real_delayed_dirac.
Proof.
  apply modelable_lub.
  - intros [|n]; [apply modelable_zero|apply modelable_ret].
  - intros [|n] f Hf; [exact (proj1 (Hf true))|exact: lexx].
Qed.
End Tests.
