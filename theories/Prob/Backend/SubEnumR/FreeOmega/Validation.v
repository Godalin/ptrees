(** Thin specialization only: all completion validity/limit proofs live in
    Prob/FreeOmega/Validation, and are not copied from the rational backend. *)
From Coq Require Import Utf8.
From PTree.Prob.FreeOmega Require Import DomainOrder.
From PTree.Prob.FreeOmega.Validation Require Import DomainOrder.

Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.Domain Require Import Expectation Countable.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega.Validation Require Import Model.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Domain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

From PTree.Prob.Interface Require Import Measure Omega.
From PTree.Prob.Domain Require Import Expectation Coupling.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Quotient.
From PTree.Prob.FreeOmega.Validation Require Import Model Quotient.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega Domain.

Section Validation.
Variable R : realType.
Local Notation native := (fun X => @subenumR_domain R X).

Theorem subenumR_native_model_ae {X} (mu : SubEnumR R X) P :
  sem_ae mu P → oval_ae (subenumR_domain mu) P.
Proof. exact: subenumR_domain_ae. Qed.
Theorem subenumR_native_model_lift {X Y} (S : X → Y → Prop)
    (mu : SubEnumR R X) (nu : SubEnumR R Y) f g :
  sem_lift S mu nu → oval_test f → oval_test g →
  (∀ x y, S x y → f x <= g y) →
  oval_eval (subenumR_domain mu) f <= oval_eval (subenumR_domain nu) g.
Proof. intros H _ _ Hfg; exact (subenumR_domain_lift H Hfg). Qed.

Theorem subenumR_free_omega_sample_ae {A X} (mu : SubEnumR R X) (k : X → FreeOmega (SubEnumR R) A) :
  sem_ae mu (λ x, free_omega_modelable native (k x)) →
  free_omega_modelable native (FOSample mu k).
Proof. intro H; exact (modelable_sample_ae (@subenumR_native_model_ae) H). Qed.
Theorem subenumR_free_omega_bind_ae {A B} (t : FreeOmega (SubEnumR R) A) (k : A → FreeOmega (SubEnumR R) B) :
  free_omega_modelable native t → free_omega_ae (λ x, free_omega_modelable native (k x)) t →
  free_omega_modelable native (free_omega_bind t k).
Proof. intros H Hk; exact (modelable_bind_ae (@subenumR_native_model_ae) H Hk). Qed.
Theorem subenumR_free_omega_lub {A} (c : nat → FreeOmega (SubEnumR R) A) :
  (∀ n, free_omega_modelable native (c n)) → model_chain_increasing native c →
  free_omega_modelable native (FOLub c).
Proof. exact: modelable_lub. Qed.
End Validation.

Section RealValidation.
Variable R : realType.
Local Notation native := (fun X => @subenumR_domain R X).

Lemma subenumR_native_model_lub {A} (c : nat → SubEnumR R A) out :
  (∀ n f, oval_test f → oval_eval (subenumR_domain (c n)) f <=
    oval_eval (subenumR_domain (c (S n))) f) →
  sem_lub c out → ∀ f, oval_test f →
  oval_sup (λ n, oval_eval (subenumR_domain (c n)) f) = oval_eval (subenumR_domain out) f.
Proof.
  intros _ Hl f Hf; destruct (Hl f Hf) as [Hub Hleast].
  apply/eqP; rewrite eq_le; apply/andP; split.
  - exact: oval_sup_le Hub.
  - apply Hleast=> n.
    exact (oval_sup_ge n (λ i, proj2 (oval_eval_bounds (subenumR_domain (c i)) Hf))).
Qed.

Theorem subenumR_qlift_bidual_raw {A B} (T : A → B → Prop)
    (t : FreeOmega (SubEnumR R) A) (u : FreeOmega (SubEnumR R) B) :
  free_omega_qlift T t u → model_upper_birel native T t u.
Proof.
  eapply model_qlift_bidual_raw.
  - exact (@subenumR_native_model_ae R).
  - exact (@subenumR_domain_ret R).
  - exact (@subenumR_domain_zero R).
  - exact (@subenumR_domain_bind R).
  - exact (@subenumR_native_model_lift R).
  - exact (@subenumR_native_model_lub).
Qed.

Theorem subenumR_qlift_bidual {A B} (T : A → B → Prop) t u
    (Ht : free_omega_modelable native t) (Hu : free_omega_modelable native u) :
  free_omega_qlift T t u → oval_bidual T (free_omega_model Ht) (free_omega_model Hu).
Proof. exact: subenumR_qlift_bidual_raw. Qed.

Theorem subenumR_qlift_eq_upper {A} (t u : FreeOmega (SubEnumR R) A) f :
  free_omega_qlift eq t u → oval_test f →
  free_omega_model_upper native t f = free_omega_model_upper native u f.
Proof.
  intros H Hf; destruct (subenumR_qlift_bidual_raw H) as [Hl Hr].
  apply/eqP; rewrite eq_le; apply/andP; split;
    [apply Hl|apply Hr]; try exact Hf; intros x y ->; exact: lexx.
Qed.

Theorem subenumR_qlift_eq_modelable {A} (t u : FreeOmega (SubEnumR R) A) :
  free_omega_qlift eq t u → (free_omega_modelable native t ↔ free_omega_modelable native u).
Proof.
  intro H; split; intro Hv; eapply modelable_ext; [exact Hv| |exact Hv|];
    intros f Hf; [exact (subenumR_qlift_eq_upper H Hf)|symmetry; exact (subenumR_qlift_eq_upper H Hf)].
Qed.
(** Backend instance of the public semantic approximation order. *)
Theorem subenumR_sem_le_upper {A} (t u : FreeOmega (SubEnumR R) A) f :
  free_omega_sem_le t u → oval_test f →
  free_omega_model_upper native t f <= free_omega_model_upper native u f.
Proof.
  intros H Hf. eapply free_omega_sem_le_upper.
  - exact (@subenumR_native_model_ae R).
  - exact (@subenumR_domain_ret R).
  - exact (@subenumR_domain_zero R).
  - exact (@subenumR_domain_bind R).
  - exact (@subenumR_native_model_lift R).
  - exact (@subenumR_native_model_lub).
  - exact H.
  - exact Hf.
Qed.

Theorem subenumR_sem_le_sound {A} (t u : FreeOmega (SubEnumR R) A)
    (Ht : free_omega_modelable native t) (Hu : free_omega_modelable native u) :
  free_omega_sem_le t u → oval_le (free_omega_model Ht) (free_omega_model Hu).
Proof. intros H f Hf; exact (subenumR_sem_le_upper H Hf). Qed.

End RealValidation.
