(** Role: Thin finite-real instance of native-parametric quotient validation.
    This proves bounded-test/dual constraints, not external joint existence.
    No copy of the rational backend's quotient induction is needed. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Interface Require Import Measure Omega.
From PTree.Prob.Domain Require Import Expectation Coupling.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Quotient.
From PTree.Prob.FreeOmega.Validation Require Import Expectation Quotient.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega Domain.
From PTree.Prob.Backend.SubEnumR.FreeOmega Require Import Validation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section RealValidation.
Variable R : realType.
Local Notation native := (fun X => @subenumR_domain R X).

Lemma subenumR_native_model_lub {A} (c : nat -> SubEnumR R A) out :
  (forall n f, oval_test f -> oval_eval (subenumR_domain (c n)) f <=
    oval_eval (subenumR_domain (c (S n))) f) ->
  sem_lub c out -> forall f, oval_test f ->
  oval_sup (fun n => oval_eval (subenumR_domain (c n)) f) = oval_eval (subenumR_domain out) f.
Proof.
  intros _ Hl f Hf; destruct (Hl f Hf) as [Hub Hleast].
  apply/eqP; rewrite eq_le; apply/andP; split.
  - exact: oval_sup_le Hub.
  - apply Hleast=> n.
    exact (oval_sup_ge n (fun i => proj2 (oval_eval_bounds (subenumR_domain (c i)) Hf))).
Qed.

Theorem subenumR_qlift_bidual_raw {A B} (T : A -> B -> Prop)
    (t : FreeOmega (SubEnumR R) A) (u : FreeOmega (SubEnumR R) B) :
  free_omega_qlift T t u -> model_upper_birel native T t u.
Proof.
  eapply model_qlift_bidual_raw.
  - exact (@subenumR_native_model_ae R).
  - exact (@subenumR_domain_ret R).
  - exact (@subenumR_domain_zero R).
  - exact (@subenumR_domain_bind R).
  - exact (@subenumR_native_model_lift R).
  - exact (@subenumR_native_model_lub).
Qed.

Theorem subenumR_qlift_bidual {A B} (T : A -> B -> Prop) t u
    (Ht : free_omega_modelable native t) (Hu : free_omega_modelable native u) :
  free_omega_qlift T t u -> oval_bidual T (free_omega_model Ht) (free_omega_model Hu).
Proof. exact: subenumR_qlift_bidual_raw. Qed.

Theorem subenumR_qlift_eq_upper {A} (t u : FreeOmega (SubEnumR R) A) f :
  free_omega_qlift eq t u -> oval_test f ->
  free_omega_model_upper native t f = free_omega_model_upper native u f.
Proof.
  intros H Hf; destruct (subenumR_qlift_bidual_raw H) as [Hl Hr].
  apply/eqP; rewrite eq_le; apply/andP; split;
    [apply Hl|apply Hr]; try exact Hf; intros x y ->; exact: lexx.
Qed.

Theorem subenumR_qlift_eq_modelable {A} (t u : FreeOmega (SubEnumR R) A) :
  free_omega_qlift eq t u -> (free_omega_modelable native t <-> free_omega_modelable native u).
Proof.
  intro H; split; intro Hv; eapply modelable_ext; [exact Hv| |exact Hv|];
    intros f Hf; [exact (subenumR_qlift_eq_upper H Hf)|symmetry; exact (subenumR_qlift_eq_upper H Hf)].
Qed.
End RealValidation.
