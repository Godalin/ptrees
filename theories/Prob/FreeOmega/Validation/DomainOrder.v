(** External validation of the internal rule-generated preorder. All raw
    derivations are sound as bounded upper-evaluator inequalities; only the
    endpoints need modelability to obtain an OmegaVal order theorem.
    This module is NOT a dependency of DomainOrder, iteration or pGCL. *)
From Coq Require Import Utf8.
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Interface Require Import Measure Omega.
From PTree.Prob.Domain Require Import Expectation Countable.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import DomainOrder.
From PTree.Prob.FreeOmega.Validation Require Import Model Quotient.
Set Implicit Arguments.
Unset Strict Implicit.
Import GRing.Theory Num.Theory Order.Theory FreeOmegaOrderNotations.
Local Open Scope ring_scope.
Local Open Scope freeomega_scope.

Section Validation.
Context {MN : Type → Type} {R : realType}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Variable native : ∀ X, MN X → OmegaVal R X.
Arguments native {X} _.
Hypothesis native_ae : ∀ X (mu : MN X) P, sem_ae mu P → oval_ae (native mu) P.
Hypothesis native_ret : ∀ X (x : X), oval_eq (native (sem_ret x)) (oval_ret R x).
Hypothesis native_zero : ∀ X, oval_eq (native (@sem_zero MN NI NO X)) (@oval_bottom R X).
Hypothesis native_bind : ∀ X Y (mu : MN X) (k : X → MN Y),
  oval_eq (native (sem_bind mu k)) (oval_bind (native mu) (λ x, native (k x))).
Hypothesis native_lift : ∀ X Y (T : X → Y → Prop) (mu : MN X) (nu : MN Y) f g,
  sem_lift T mu nu → oval_test f → oval_test g →
  (∀ x y, T x y → f x <= g y) → oval_eval (native mu) f <= oval_eval (native nu) g.
Hypothesis native_lub : ∀ X (c : nat → MN X) out,
  (∀ n f, oval_test f → oval_eval (native (c n)) f <= oval_eval (native (c (S n))) f) →
  sem_lub c out → ∀ f, oval_test f →
  oval_sup (λ n, oval_eval (native (c n)) f) = oval_eval (native out) f.
Local Notation upper := (free_omega_model_upper (@native)).

Theorem free_omega_sem_le_upper {A} (t u : FreeOmega MN A) :
  t ⊑ω u → ∀ f, oval_test f → upper t f <= upper u f.
Proof.
  intro H. induction H as [t u H|t u H|t u v H IH G IG|
    X mu k h H IH|c d H IH|c Hi n|c u Hi H IH]; intros f Hf;
    cbn [free_omega_model_upper].
  - eapply model_upper_approx; [exact native_lift|exact H|exact Hf|exact Hf|].
    intros x y ->; exact: lexx.
  - have He : upper t f = upper u f.
    { eapply model_qlift_eq_upper; eassumption. }
    rewrite He; exact: lexx.
  - exact: le_trans (IH f Hf) (IG f Hf).
  - apply (oval_mono (oval_laws (native mu))).
    + intro x; exact (model_upper_bounds (@native) (k x) Hf).
    + intro x; exact (model_upper_bounds (@native) (h x) Hf).
    + intro x; exact (IH x f Hf).
  - apply (oval_sup_mono (b := 1)).
    + intro n; exact (proj2 (model_upper_bounds (@native) (d n) Hf)).
    + intro n; exact (IH n f Hf).
  - apply (oval_sup_ge (c := λ m, upper (c m) f) (b := 1) n).
    intro m; exact (proj2 (model_upper_bounds (@native) (c m) Hf)).
  - apply oval_sup_le. intro n; exact (IH n f Hf).
Qed.

Theorem free_omega_sem_le_sound {A} (t u : FreeOmega MN A)
    (Ht : free_omega_modelable (@native) t) (Hu : free_omega_modelable (@native) u) :
  t ⊑ω u → oval_le (free_omega_model Ht) (free_omega_model Hu).
Proof. intros H f Hf; exact (free_omega_sem_le_upper H Hf). Qed.

Corollary free_omega_sem_le_mutual_sound {A} (t u : FreeOmega MN A)
    (Ht : free_omega_modelable (@native) t) (Hu : free_omega_modelable (@native) u) :
  t ⊑ω u → u ⊑ω t → oval_eq (free_omega_model Ht) (free_omega_model Hu).
Proof. intros H G; apply oval_le_antisym; apply free_omega_sem_le_sound; assumption. Qed.

(** Non-collapse is conditional on an actual compatible native model, not
    claimed for arbitrary possibly degenerate abstract native interfaces. *)
Theorem free_omega_sem_ret_not_bottom {A} (x : A) :
  ¬ (@FORet MN A x ⊑ω FOZero).
Proof.
  intro H. have Hbad := free_omega_sem_le_upper H (@oval_test_one R A).
  change (is_true ((1 : R) <= 0)) in Hbad. by move: Hbad; rewrite ler10.
Qed.
End Validation.
