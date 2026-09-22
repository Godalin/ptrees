(** Role: External validity boundary for the existing raw upper evaluator.
    No new syntax, recursive interpretation, or mainline premise is added.
    Admissibility is scalar-model qualified; arbitrary raw FOLub is NOT
    claimed to denote a probability. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals boolp.
From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.Domain Require Import Expectation.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation.
From PTree.Prob.FreeOmega Require Import StructuralMeasure.
From PTree.Prob.Backend.SubEnumQ Require Import Measure Domain.
From PTree.Prob.Backend.SubEnumQ.FreeOmega Require Import UpperExpectation UpperCoupling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Admissibility.
Variable R : realType.

Definition free_omega_admissible {A} (t : FreeOmega SubEnumQ A) : Prop :=
  OmegaValLaws (free_omega_upper (R := R) t).

Definition free_omega_domain {A} (t : FreeOmega SubEnumQ A)
    (H : free_omega_admissible t) : OmegaVal R A :=
  {| oval_eval := free_omega_upper t; oval_laws := H |}.

(** Avoid shadowing the maintained internal [free_omega_denotes] relation:
    this name explicitly denotes the independent mathematical domain. *)
Definition free_omega_domain_denotes {A} (t : FreeOmega SubEnumQ A)
    (L : OmegaVal R A) : Prop :=
  forall f, oval_test f -> free_omega_upper t f = oval_eval L f.

Theorem free_omega_admissible_iff_denotes {A} (t : FreeOmega SubEnumQ A) :
  free_omega_admissible t <-> exists L, free_omega_domain_denotes t L.
Proof.
  split.
  - intro H; exists (free_omega_domain H); intros f Hf; reflexivity.
  - intros [L H]; eapply oval_laws_ext; [exact (oval_laws L)|].
    intros f Hf; symmetry; exact: H.
Qed.

Lemma free_omega_admissible_ext {A} (t u : FreeOmega SubEnumQ A) :
  free_omega_admissible t ->
  (forall f : A -> R, oval_test f -> free_omega_upper t f = free_omega_upper u f) ->
  free_omega_admissible u.
Proof. exact: oval_laws_ext. Qed.

Lemma admissible_ret {A} (x : A) : free_omega_admissible (FORet x).
Proof. exact (oval_laws (oval_ret R x)). Qed.
Lemma admissible_zero {A} : free_omega_admissible (@FOZero SubEnumQ A).
Proof. exact (oval_laws (@oval_bottom R A)). Qed.

Lemma admissible_sample {A X} (mu : SubEnumQ X) (k : X -> FreeOmega SubEnumQ A) :
  (forall x, free_omega_admissible (k x)) ->
  free_omega_admissible (FOSample mu k).
Proof.
  intro H; exact (oval_laws (oval_bind (subenumQ_domain R mu)
    (fun x => free_omega_domain (H x)))).
Qed.

Definition free_omega_domain_increasing {A} (c : nat -> FreeOmega SubEnumQ A) :=
  forall n (f : A -> R), oval_test f ->
    free_omega_upper (c n) f <= free_omega_upper (c (S n)) f.

Lemma admissible_lub {A} (c : nat -> FreeOmega SubEnumQ A)
    (H : forall n, free_omega_admissible (c n)) :
  free_omega_domain_increasing c -> free_omega_admissible (FOLub c).
Proof.
  intro Hi; exact (oval_laws (oval_lub
    (c := fun n => free_omega_domain (H n)) Hi)).
Qed.

Lemma admissible_lub_approx {A} (c : nat -> FreeOmega SubEnumQ A) :
  (forall n, free_omega_admissible (c n)) ->
  (forall n, free_omega_approx eq (c n) (c (S n))) ->
  free_omega_admissible (FOLub c).
Proof.
  intros H Hi; apply (admissible_lub H)=> n f Hf.
  exact (free_omega_upper_approx_mono (Hi n) Hf).
Qed.

Lemma admissible_bind {A B} (t : FreeOmega SubEnumQ A)
    (k : A -> FreeOmega SubEnumQ B) :
  free_omega_admissible t -> (forall x, free_omega_admissible (k x)) ->
  free_omega_admissible (free_omega_bind t k).
Proof.
  intros H Hk; eapply oval_laws_ext.
  - exact (oval_laws (oval_bind (free_omega_domain H)
      (fun x => free_omega_domain (Hk x)))).
  - intros f Hf; symmetry; exact: free_omega_upper_bind.
Qed.

(** A proof-only replacement outside the AE support. This is not a denotation
    for inadmissible terms: replacing them by zero is sound only under the
    explicit support hypothesis in the closure theorems below. *)
Definition admissible_support_kernel {A} (t : FreeOmega SubEnumQ A) :
    FreeOmega SubEnumQ A :=
  if pselect (free_omega_admissible t) then t else FOZero.

Lemma admissible_support_kernel_valid {A} (t : FreeOmega SubEnumQ A) :
  free_omega_admissible (admissible_support_kernel t).
Proof. rewrite /admissible_support_kernel; case: pselect=> H; [exact H|exact: admissible_zero]. Qed.
Lemma admissible_support_kernel_eq {A} (t : FreeOmega SubEnumQ A) :
  free_omega_admissible t -> admissible_support_kernel t = t.
Proof. intro H; rewrite /admissible_support_kernel; case: pselect=> // Hn; contradiction. Qed.

Theorem admissible_bind_ae {A B} (t : FreeOmega SubEnumQ A)
    (k : A -> FreeOmega SubEnumQ B) :
  free_omega_admissible t ->
  free_omega_ae (fun x => free_omega_admissible (k x)) t ->
  free_omega_admissible (free_omega_bind t k).
Proof.
  intros H Hk; eapply free_omega_admissible_ext
    with (t := free_omega_bind t (fun x => admissible_support_kernel (k x))).
  - apply (admissible_bind H); intro x; exact: admissible_support_kernel_valid.
  - intros f Hf; rewrite !free_omega_upper_bind.
    apply free_omega_upper_ae_ext.
    + intro x; exact (free_omega_upper_bounds _ Hf).
    + intro x; exact (free_omega_upper_bounds _ Hf).
    + eapply free_omega_ae_mono; [|exact Hk].
      intros x Hx; by rewrite (admissible_support_kernel_eq Hx).
Qed.

Theorem admissible_sample_ae {A X} (mu : SubEnumQ X)
    (k : X -> FreeOmega SubEnumQ A) :
  sem_ae mu (fun x => free_omega_admissible (k x)) ->
  free_omega_admissible (FOSample mu k).
Proof.
  intro H; change (free_omega_admissible
    (free_omega_bind (FOSample mu (fun x => FORet x)) k)).
  apply admissible_bind_ae.
  - apply admissible_sample=> x; exact: admissible_ret.
  - eapply FOAESample; [exact H|]. intros x Hx; exact (FOAERet Hx).
Qed.
End Admissibility.
