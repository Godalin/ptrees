(** Role: SubEnumQ specialization of native-parametric external validation.
    Existing DS definitions/proofs remain unchanged. Native Domain remains
    below FreeOmega: only this adapter imports both validation developments. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.Domain Require Import Expectation Countable.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega.Validation Require Import Expectation.
From PTree.Prob.Backend.SubEnumQ Require Import Measure Expectation Domain.
From PTree.Prob.Backend.SubEnumQ.FreeOmega Require Import UpperExpectation Admissibility.
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

Theorem subenumQ_native_model_ae {X} (mu : SubEnumQ X) P :
  sem_ae mu P -> oval_ae (subenumQ_domain R mu) P.
Proof.
  intros Ha f g Hf Hg He; apply/eqP; rewrite eq_le; apply/andP; split;
    apply enumQ_real_expect_ae_mono; intros p x Hin Hnz.
  - rewrite (He x (Ha p x Hin Hnz)); exact: lexx.
  - rewrite (He x (Ha p x Hin Hnz)); exact: lexx.
Qed.

Theorem subenumQ_native_model_lift {X Y} (S : X -> Y -> Prop)
    (mu : SubEnumQ X) (nu : SubEnumQ Y) f g :
  sem_lift S mu nu -> oval_test f -> oval_test g ->
  (forall x y, S x y -> f x <= g y) ->
  oval_eval (subenumQ_domain R mu) f <= oval_eval (subenumQ_domain R nu) g.
Proof. intros H _ _ Hfg; exact (subenumQ_sem_lift_test_sound H Hfg). Qed.
End SubEnumQValidation.
