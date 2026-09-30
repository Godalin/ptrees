(** Role: Compatibility between the legacy rational evaluator/admissibility
    names and the canonical generic Model API. New clients use Validation. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.Domain Require Import Expectation Countable.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Quotient.
From PTree.Prob.FreeOmega.Validation Require Import Model.
From PTree.Prob.Backend.SubEnumQ Require Import Measure Expectation Domain.
From PTree.Prob.Backend.SubEnumQ.FreeOmega Require Import UpperExpectation Admissibility Validation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section SubEnumQValidation.
Variable R : realType.
Local Notation native := (fun X => @subenumQ_domain R X).

Theorem subenumQ_model_upper {A} (t : FreeOmega SubEnumQ A) f :
  free_omega_model_upper native t f = free_omega_upper t f.
Proof.
  reflexivity.
Qed.

Theorem subenumQ_modelable_iff_admissible {A} (t : FreeOmega SubEnumQ A) :
  free_omega_modelable native t <-> free_omega_admissible R t.
Proof.
  split; intro H; eapply oval_laws_ext; [exact H| |exact H|];
    intros f Hf; [symmetry|]; exact: subenumQ_model_upper.
Qed.

Theorem subenumQ_model_denotes_iff {A} (t : FreeOmega SubEnumQ A) L :
  free_omega_model_denotes native t L <-> free_omega_domain_denotes t L.
Proof.
  split; intros H f Hf.
  - rewrite -(subenumQ_model_upper t f); exact (H f Hf).
  - rewrite subenumQ_model_upper; exact (H f Hf).
Qed.

Theorem subenumQ_generic_domain_agrees {A} (t : FreeOmega SubEnumQ A)
    (H : free_omega_modelable native t) (Hds : free_omega_admissible R t) :
  oval_eq (free_omega_model H) (free_omega_domain Hds).
Proof. intros f Hf; exact: subenumQ_model_upper. Qed.

End SubEnumQValidation.

Section LegacyTests.
Variable R : realType.
(** The conclusion agrees with DS5 at the evaluator level, without
    replacing or depending on the frozen DS5 quotient induction. *)
Theorem subenumQ_generic_qlift_tests {A B} (T : A -> B -> Prop) t u (f : A -> R) (g : B -> R) :
  free_omega_qlift T t u -> oval_test f -> oval_test g ->
  (forall x y, T x y -> f x <= g y) ->
  free_omega_upper t f <= free_omega_upper u g.
Proof. intro H; exact (proj1 (subenumQ_qlift_bidual_raw R H) f g). Qed.
End LegacyTests.
