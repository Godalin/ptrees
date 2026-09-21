(** Role: Finite subbehavior order and cofinal chains for the free completion. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import FunctionalExtensionality.
From Coq.Program Require Import Equality.
Require Import Morphisms Arith.

From PTree.Prob.Interface Require Import Measure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PTree.Prob.FreeOmega.Definition.


(** Finite subbehavior order.  Unlike the earlier placeholder [sem_le :=
    True], this relation records the concrete information needed for
    cofinality arguments: missing mass is bottom, and existing Ret/Sample/Lub
    structure must be preserved relationally. *)
Polymorphic Inductive free_omega_approx {MN}
    `{NI : SemanticMeasure MN} {A B}
    (R : A -> B -> Prop) : FreeOmega MN A -> FreeOmega MN B -> Prop :=
  | FOApproxZero nu : free_omega_approx R FOZero nu
  | FOApproxRet x y : R x y ->
      free_omega_approx R (FORet x) (FORet y)
  | FOApproxSample {X Y} (S : X -> Y -> Prop)
      (mu : MN X) (nu : MN Y) k h :
      sem_lift S mu nu ->
      (forall x y, S x y -> free_omega_approx R (k x) (h y)) ->
      free_omega_approx R (FOSample mu k) (FOSample nu h)
  | FOApproxLub c d :
      (forall n, free_omega_approx R (c n) (d n)) ->
      free_omega_approx R (FOLub c) (FOLub d).

Lemma free_omega_lift_to_approx {MN}
    `{NI : SemanticMeasure MN} {A B}
    (R : A -> B -> Prop) (mu : FreeOmega MN A) (nu : FreeOmega MN B) :
  free_omega_lift R mu nu -> free_omega_approx R mu nu.
Proof.
  intro Hlift. induction Hlift.
  - constructor. exact H.
  - constructor.
  - eapply FOApproxSample with (S := S).
    + exact H.
    + intros x y Hxy. exact (H1 x y Hxy).
  - constructor. exact H0.
Qed.

Definition free_omega_chains_cofinal {MN}
    `{NI : SemanticMeasure MN} {A B} (R : A -> B -> Prop)
    (left : nat -> FreeOmega MN A) (right : nat -> FreeOmega MN B) : Prop :=
  (forall n, exists m, free_omega_approx R (left n) (right m)) /\
  (forall m, exists n, free_omega_approx (fun y x => R x y)
    (right m) (left n)).

Lemma free_omega_approx_bind {MN}
    `{NI : SemanticMeasure MN} {A B C D}
    (R : A -> B -> Prop) (T : C -> D -> Prop)
    (mu : FreeOmega MN A) (nu : FreeOmega MN B)
    (k : A -> FreeOmega MN C) (h : B -> FreeOmega MN D) :
  free_omega_approx R mu nu ->
  (forall x y, R x y -> free_omega_approx T (k x) (h y)) ->
  free_omega_approx T (free_omega_bind mu k) (free_omega_bind nu h).
Proof.
  intros Happrox Hkh. induction Happrox; cbn.
  - constructor.
  - exact (Hkh _ _ H).
  - eapply FOApproxSample; [exact H|].
    intros x y Hxy. exact (H1 x y Hxy).
  - apply FOApproxLub. exact H0.
Qed.
