(** Role: External, SubEnum-qualified sound interpretation of admissible
    FreeOmega terms. Denotation packages the existing upper evaluator;
    this file defines no second evaluator and no new free construction.
    Quotient equality and general joint-coupling realization are later stages. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.Domain Require Import Expectation.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation.
From PTree.Prob.FreeOmega Require Import StructuralMeasure.
From PTree.Prob.Backend.SubEnum Require Import Measure Domain.
From PTree.Prob.Backend.SubEnum.FreeOmega Require Import
  UpperExpectation UpperCoupling Admissibility.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section DomainSoundness.
Variable R : realType.

Theorem free_omega_domain_spec {A} (t : FreeOmega SubEnum A)
    (H : free_omega_admissible R t) :
  free_omega_domain_denotes t (free_omega_domain H).
Proof. intros f Hf; reflexivity. Qed.

Theorem free_omega_domain_proof_independent {A} (t : FreeOmega SubEnum A)
    (H H' : free_omega_admissible R t) :
  oval_eq (free_omega_domain H) (free_omega_domain H').
Proof. intros f Hf; reflexivity. Qed.

Theorem free_omega_denote_ret {A} (x : A) :
  free_omega_domain_denotes (FORet x) (oval_ret R x).
Proof. intros f Hf; reflexivity. Qed.
Theorem free_omega_denote_zero {A} :
  free_omega_domain_denotes (@FOZero SubEnum A) (@oval_bottom R A).
Proof. intros f Hf; reflexivity. Qed.

Theorem free_omega_denote_sample {A X} (mu : SubEnum X)
    (k : X -> FreeOmega SubEnum A) (K : X -> OmegaVal R A) :
  (forall x, free_omega_domain_denotes (k x) (K x)) ->
  free_omega_domain_denotes (FOSample mu k) (oval_bind (subenum_domain R mu) K).
Proof.
  intros H f Hf; cbn [free_omega_upper oval_bind oval_eval subenum_domain].
  f_equal; apply functional_extensionality=> x; exact (H x f Hf).
Qed.

Theorem free_omega_denote_native {A} (mu : SubEnum A) :
  free_omega_domain_denotes (FOSample mu (fun x => FORet x)) (subenum_domain R mu).
Proof. intros f Hf; reflexivity. Qed.

Theorem free_omega_denote_bind {A B} (t : FreeOmega SubEnum A)
    (k : A -> FreeOmega SubEnum B) (L : OmegaVal R A) (K : A -> OmegaVal R B) :
  free_omega_domain_denotes t L ->
  (forall x, free_omega_domain_denotes (k x) (K x)) ->
  free_omega_domain_denotes (free_omega_bind t k) (oval_bind L K).
Proof.
  intros H Hk f Hf; rewrite free_omega_upper_bind.
  rewrite (H _ (fun x => free_omega_upper_bounds (k x) Hf)).
  cbn [oval_bind oval_eval].
  apply oval_eval_ext=> x; exact (Hk x f Hf).
Qed.

Theorem free_omega_denote_bind_ae {A B} (t : FreeOmega SubEnum A)
    (k : A -> FreeOmega SubEnum B) (L : OmegaVal R A) (K : A -> OmegaVal R B) :
  free_omega_domain_denotes t L ->
  free_omega_ae (fun x => free_omega_domain_denotes (k x) (K x)) t ->
  free_omega_domain_denotes (free_omega_bind t k) (oval_bind L K).
Proof.
  intros H Hk f Hf; rewrite free_omega_upper_bind.
  transitivity (free_omega_upper t (fun x => oval_eval (K x) f)).
  - apply free_omega_upper_ae_ext.
    + intro x; exact (free_omega_upper_bounds _ Hf).
    + intro x; exact (oval_eval_bounds (K x) Hf).
    + eapply free_omega_ae_mono; [|exact Hk]. intros x Hx; exact (Hx f Hf).
  - exact (H _ (fun x => oval_eval_bounds (K x) Hf)).
Qed.

Theorem free_omega_denote_sample_ae {A X} (mu : SubEnum X)
    (k : X -> FreeOmega SubEnum A) (K : X -> OmegaVal R A) :
  sem_ae mu (fun x => free_omega_domain_denotes (k x) (K x)) ->
  free_omega_domain_denotes (FOSample mu k) (oval_bind (subenum_domain R mu) K).
Proof.
  intro H; change (free_omega_domain_denotes
    (free_omega_bind (FOSample mu (fun x => FORet x)) k)
    (oval_bind (subenum_domain R mu) K)).
  apply free_omega_denote_bind_ae; first exact: free_omega_denote_native.
  eapply FOAESample; [exact H|]. intros x Hx; exact (FOAERet Hx).
Qed.

Theorem free_omega_denote_lub {A} (c : nat -> FreeOmega SubEnum A)
    (L : nat -> OmegaVal R A) (Hi : oval_increasing L) :
  (forall n, free_omega_domain_denotes (c n) (L n)) ->
  free_omega_domain_denotes (FOLub c) (oval_lub Hi).
Proof.
  intros H f Hf; apply oval_sup_ext=> n; exact (H n f Hf).
Qed.

(** Approximation is sound for the mathematical information order.
    The heterogeneous test inequality below is not called a joint coupling. *)
Theorem free_omega_denote_approx {A} (t u : FreeOmega SubEnum A)
    (L M : OmegaVal R A) :
  free_omega_domain_denotes t L -> free_omega_domain_denotes u M ->
  free_omega_approx eq t u -> oval_le L M.
Proof.
  intros Ht Hu H f Hf; rewrite -(Ht f Hf) -(Hu f Hf).
  exact (free_omega_upper_approx_mono H Hf).
Qed.

Theorem free_omega_denote_approx_test {A B} (S : A -> B -> Prop)
    (t : FreeOmega SubEnum A) (u : FreeOmega SubEnum B)
    (L : OmegaVal R A) (M : OmegaVal R B) (f : A -> R) (g : B -> R) :
  free_omega_domain_denotes t L -> free_omega_domain_denotes u M ->
  free_omega_approx S t u -> oval_test f -> oval_test g ->
  (forall x y, S x y -> f x <= g y) -> oval_eval L f <= oval_eval M g.
Proof.
  intros Ht Hu H Hf Hg Hfg; rewrite -(Ht f Hf) -(Hu g Hg).
  exact (free_omega_approx_upper H Hg Hfg).
Qed.

Theorem free_omega_domain_increasing_of_approx {A} (c : nat -> FreeOmega SubEnum A)
    (H : forall n, free_omega_admissible R (c n)) :
  (forall n, free_omega_approx eq (c n) (c (S n))) ->
  oval_increasing (fun n => free_omega_domain (H n)).
Proof. intros Hi n f Hf; exact (free_omega_upper_approx_mono (Hi n) Hf). Qed.
End DomainSoundness.
