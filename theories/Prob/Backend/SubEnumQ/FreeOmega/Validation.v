(** Role: Native rational interpretation adapter for generic FreeOmega validation.
    Only native AE/return/zero/bind/lift/lub obligations are discharged here.
    No legacy evaluator or backend-specific quotient induction is used. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order rat reals.
From PTree.Prob.Interface Require Import Measure Omega.
From PTree.Prob.Domain Require Import Expectation Countable Coupling.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Quotient.
From PTree.Prob.FreeOmega.Validation Require Import Model Quotient.
From PTree.Prob.Backend.SubEnumQ Require Import Measure Expectation Domain NativeLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section RationalValidation.
Variable R : realType.
Local Notation native := (fun X => @subenumQ_domain R X).

Theorem subenumQ_native_model_ae {X} (mu : SubEnumQ X) P :
  sem_ae mu P → oval_ae (subenumQ_domain R mu) P.
Proof.
  intros Ha f g Hf Hg He; apply/eqP; rewrite eq_le; apply/andP; split;
    apply enumQ_real_expect_ae_mono; intros p x Hin Hnz.
  - rewrite (He x (Ha p x Hin Hnz)); exact: lexx.
  - rewrite (He x (Ha p x Hin Hnz)); exact: lexx.
Qed.

Theorem subenumQ_native_model_lift {X Y} (S : X → Y → Prop)
    (mu : SubEnumQ X) (nu : SubEnumQ Y) f g :
  sem_lift S mu nu → oval_test f → oval_test g →
  (∀ x y, S x y → f x <= g y) →
  oval_eval (subenumQ_domain R mu) f <= oval_eval (subenumQ_domain R nu) g.
Proof. intros H _ _ Hfg; exact (subenumQ_sem_lift_test_sound H Hfg). Qed.

Lemma subenumQ_native_model_lub {A} (c : nat → SubEnumQ A) out :
  (∀ n f, oval_test f → oval_eval (subenumQ_domain R (c n)) f <=
    oval_eval (subenumQ_domain R (c (S n))) f) →
  sem_lub c out → ∀ f, oval_test f →
  oval_sup (λ n, oval_eval (subenumQ_domain R (c n)) f) = oval_eval (subenumQ_domain R out) f.
Proof.
  intros Hi Hl f Hf; apply enumQ_monotone_converges_upper; [|exact Hl|].
  - intros P n m Hnm.
    have HP : oval_test (λ x, if P x then (1 : R) else 0).
    { intro x; case: (P x); split; try exact: ler01; exact: lexx. }
    have Hstep : ∀ i,
      enumQ_real_expect (λ x, if P x then (1 : R) else 0) (subenumQ_raw (c i)) <=
      enumQ_real_expect (λ x, if P x then (1 : R) else 0) (subenumQ_raw (c (S i))).
    { intro i; exact (Hi i _ HP). }
    have Hreal := scalar_increasing_le Hstep Hnm.
    rewrite !enumQ_real_expect_indicator ler_rat in Hreal; exact Hreal.
  - intro x; exact (proj1 (Hf x)).
Qed.

Theorem subenumQ_qlift_bidual_raw {A B} (T : A → B → Prop)
    (t : FreeOmega SubEnumQ A) (u : FreeOmega SubEnumQ B) :
  free_omega_qlift T t u → model_upper_birel native T t u.
Proof.
  eapply model_qlift_bidual_raw.
  - exact (@subenumQ_native_model_ae).
  - exact (@subenumQ_domain_ret R).
  - exact (@subenumQ_domain_zero R).
  - exact (@subenumQ_domain_bind R).
  - exact (@subenumQ_native_model_lift).
  - exact (@subenumQ_native_model_lub).
Qed.

Theorem subenumQ_generic_qlift_bidual {A B} (T : A → B → Prop) t u
    (Ht : free_omega_modelable native t) (Hu : free_omega_modelable native u) :
  free_omega_qlift T t u → oval_bidual T (free_omega_model Ht) (free_omega_model Hu).
Proof. exact: subenumQ_qlift_bidual_raw. Qed.


Theorem subenumQ_qlift_eq_upper {A} (t u : FreeOmega SubEnumQ A) f :
  free_omega_qlift eq t u → oval_test f →
  free_omega_model_upper native t f = free_omega_model_upper native u f.
Proof.
  intros H Hf; destruct (subenumQ_qlift_bidual_raw H) as [Hl Hr].
  apply/eqP; rewrite eq_le; apply/andP; split;
    [apply Hl|apply Hr]; try exact Hf; intros x y ->; exact: lexx.
Qed.

Theorem subenumQ_qlift_eq_modelable {A} (t u : FreeOmega SubEnumQ A) :
  free_omega_qlift eq t u →
  (free_omega_modelable native t ↔ free_omega_modelable native u).
Proof.
  intro H; split; intro Hv; eapply modelable_ext; [exact Hv| |exact Hv|];
    intros f Hf; [exact (subenumQ_qlift_eq_upper H Hf)|symmetry; exact (subenumQ_qlift_eq_upper H Hf)].
Qed.

Theorem subenumQ_qlift_eq_sound {A} (t u : FreeOmega SubEnumQ A)
    (Ht : free_omega_modelable native t) (Hu : free_omega_modelable native u) :
  free_omega_qlift eq t u → oval_eq (free_omega_model Ht) (free_omega_model Hu).
Proof. intros H f Hf; exact (subenumQ_qlift_eq_upper H Hf). Qed.

End RationalValidation.
