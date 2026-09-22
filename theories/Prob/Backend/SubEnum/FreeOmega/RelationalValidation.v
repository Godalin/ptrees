(** Role: Rational instance of the same generic raw-qlift validation used
    by SubEnumR. Frozen DS5 proofs remain unchanged. Only the native scalar
    convergence lemma is reused; no old qlift soundness theorem is assumed. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
From PTree.Prob.Interface Require Import Measure Omega.
From PTree.Prob.Domain Require Import Expectation Coupling.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Quotient.
From PTree.Prob.FreeOmega.Validation Require Import Expectation Quotient.
From PTree.Prob.Backend.SubEnum Require Import Measure Expectation Domain.
From PTree.Prob.Backend.SubEnum.FreeOmega Require Import
  GenericValidation UpperExpectation UpperObservation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section RationalValidation.
Variable R : realType.
Local Notation native := (fun X => @subenum_domain R X).

Lemma subenum_native_model_lub {A} (c : nat -> SubEnum A) out :
  (forall n f, oval_test f -> oval_eval (subenum_domain R (c n)) f <=
    oval_eval (subenum_domain R (c (S n))) f) ->
  sem_lub c out -> forall f, oval_test f ->
  oval_sup (fun n => oval_eval (subenum_domain R (c n)) f) = oval_eval (subenum_domain R out) f.
Proof.
  intros Hi Hl f Hf; apply enum_monotone_converges_upper; [|exact Hl|].
  - intros P n m Hnm.
    have HP : oval_test (fun x => if P x then (1 : R) else 0).
    { intro x; case: (P x); split; try exact: ler01; exact: lexx. }
    have Hstep : forall i,
      enum_real_expect (fun x => if P x then (1 : R) else 0) (subenum_raw (c i)) <=
      enum_real_expect (fun x => if P x then (1 : R) else 0) (subenum_raw (c (S i))).
    { intro i; exact (Hi i _ HP). }
    have Hreal := scalar_increasing_le Hstep Hnm.
    rewrite !enum_real_expect_indicator ler_rat in Hreal; exact Hreal.
  - intro x; exact (proj1 (Hf x)).
Qed.

Theorem subenum_qlift_bidual_raw {A B} (T : A -> B -> Prop)
    (t : FreeOmega SubEnum A) (u : FreeOmega SubEnum B) :
  free_omega_qlift T t u -> model_upper_birel native T t u.
Proof.
  eapply model_qlift_bidual_raw.
  - exact (@subenum_native_model_ae R).
  - exact (@subenum_domain_ret R).
  - exact (@subenum_domain_zero R).
  - exact (@subenum_domain_bind R).
  - exact (@subenum_native_model_lift R).
  - exact (@subenum_native_model_lub).
Qed.

Theorem subenum_generic_qlift_bidual {A B} (T : A -> B -> Prop) t u
    (Ht : free_omega_modelable native t) (Hu : free_omega_modelable native u) :
  free_omega_qlift T t u -> oval_bidual T (free_omega_model Ht) (free_omega_model Hu).
Proof. exact: subenum_qlift_bidual_raw. Qed.

(** The conclusion agrees with DS5 at the evaluator level, without
    replacing or depending on the frozen DS5 quotient induction. *)
Theorem subenum_generic_qlift_tests {A B} (T : A -> B -> Prop) t u (f : A -> R) (g : B -> R) :
  free_omega_qlift T t u -> oval_test f -> oval_test g ->
  (forall x y, T x y -> f x <= g y) ->
  free_omega_upper t f <= free_omega_upper u g.
Proof. intro H; exact (proj1 (subenum_qlift_bidual_raw H) f g). Qed.
End RationalValidation.
