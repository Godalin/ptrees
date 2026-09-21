(** Thin specialization only: all completion validity/limit proofs live in
    Prob/FreeOmega/Validation, and are not copied from the rational backend. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.Domain Require Import Expectation Countable.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega.Validation Require Import Expectation.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Domain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Validation.
Variable R : realType.
Local Notation native := (fun X => @subenumR_domain R X).

Theorem subenumR_native_model_ae {X} (mu : SubEnumR R X) P :
  sem_ae mu P -> oval_ae (subenumR_domain mu) P.
Proof. exact: subenumR_domain_ae. Qed.
Theorem subenumR_native_model_lift {X Y} (S : X -> Y -> Prop)
    (mu : SubEnumR R X) (nu : SubEnumR R Y) f g :
  sem_lift S mu nu -> oval_test f -> oval_test g ->
  (forall x y, S x y -> f x <= g y) ->
  oval_eval (subenumR_domain mu) f <= oval_eval (subenumR_domain nu) g.
Proof. intros H _ _ Hfg; exact (subenumR_domain_lift H Hfg). Qed.

Theorem subenumR_free_omega_sample_ae {A X} (mu : SubEnumR R X) (k : X -> FreeOmega (SubEnumR R) A) :
  sem_ae mu (fun x => free_omega_modelable native (k x)) ->
  free_omega_modelable native (FOSample mu k).
Proof. intro H; exact (modelable_sample_ae (@subenumR_native_model_ae) H). Qed.
Theorem subenumR_free_omega_bind_ae {A B} (t : FreeOmega (SubEnumR R) A) (k : A -> FreeOmega (SubEnumR R) B) :
  free_omega_modelable native t -> free_omega_ae (fun x => free_omega_modelable native (k x)) t ->
  free_omega_modelable native (free_omega_bind t k).
Proof. intros H Hk; exact (modelable_bind_ae (@subenumR_native_model_ae) H Hk). Qed.
Theorem subenumR_free_omega_lub {A} (c : nat -> FreeOmega (SubEnumR R) A) :
  (forall n, free_omega_modelable native (c n)) -> model_chain_increasing native c ->
  free_omega_modelable native (FOLub c).
Proof. exact: modelable_lub. Qed.
End Validation.
