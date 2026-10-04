(** Public, quotient-compatible approximation preorder on the EXISTING raw
    carrier. This is a least rule-generated relation, not another probability
    syntax, a new SemanticOmega instance, or a change to qlift equality.
    Supremum rules require structural increasingness. Pointwise congruence
    of raw Lub does not assert that arbitrary sequences are probability laws.
    External validation of these rules lives in Validation/DomainOrder. *)
From Coq Require Import Utf8 Morphisms RelationClasses.
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Prob.Interface Require Import Measure Omega.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Approximation StructuralMeasure Quotient Measure.
Set Implicit Arguments.
Unset Strict Implicit.

Section Construction.
Context {MN : Type → Type} `{NI : SemanticMeasure MN} `{NO : @SemanticOmega MN NI}.

Definition free_omega_struct_increasing {A} (c : nat → FreeOmega MN A) :=
  ∀ n, free_omega_approx eq (c n) (c (S n)).

Inductive free_omega_sem_le {A} : FreeOmega MN A → FreeOmega MN A → Prop :=
| FOSLeApprox t u : free_omega_approx eq t u → free_omega_sem_le t u
| FOSLeEq t u : free_omega_qlift eq t u → free_omega_sem_le t u
| FOSLeTrans t u v : free_omega_sem_le t u → free_omega_sem_le u v → free_omega_sem_le t v
| FOSLeSample {X} (mu : MN X) k h :
    (∀ x, free_omega_sem_le (k x) (h x)) →
    free_omega_sem_le (FOSample mu k) (FOSample mu h)
| FOSLeLub c d :
    (∀ n, free_omega_sem_le (c n) (d n)) → free_omega_sem_le (FOLub c) (FOLub d)
| FOSLeUpper c : free_omega_struct_increasing c →
    ∀ n, free_omega_sem_le (c n) (FOLub c)
| FOSLeLeast c u : free_omega_struct_increasing c →
    (∀ n, free_omega_sem_le (c n) u) → free_omega_sem_le (FOLub c) u.
End Construction.

Module FreeOmegaOrderNotations.
Notation "t '⊑ω' u" := (free_omega_sem_le t u)
  (at level 70, no associativity) : freeomega_scope.
End FreeOmegaOrderNotations.

Section Laws.
Context {MN : Type → Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI} `{NO : @SemanticOmega MN NI}.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).
Import FreeOmegaOrderNotations.
Local Open Scope freeomega_scope.

Theorem free_omega_approx_sem_le {A} (t u : FreeOmega MN A) :
  free_omega_approx eq t u → t ⊑ω u.
Proof. apply FOSLeApprox. Qed.
Theorem free_omega_sem_eq_le {A} (t u : FreeOmega MN A) :
  free_omega_qlift eq t u → t ⊑ω u.
Proof. apply FOSLeEq. Qed.
Theorem free_omega_sem_le_refl {A} (t : FreeOmega MN A) : t ⊑ω t.
Proof. apply FOSLeApprox, free_omega_approx_refl. intro x; reflexivity. Qed.
Theorem free_omega_sem_le_trans {A} (t u v : FreeOmega MN A) :
  t ⊑ω u → u ⊑ω v → t ⊑ω v.
Proof. apply FOSLeTrans. Qed.
Theorem free_omega_sem_le_bottom {A} (t : FreeOmega MN A) : FOZero ⊑ω t.
Proof. apply FOSLeApprox, FOApproxZero. Qed.

#[global] Instance free_omega_sem_le_preorder A : PreOrder (@free_omega_sem_le MN NI NO A).
Proof. split; [intro x; apply free_omega_sem_le_refl|intros x y z; apply free_omega_sem_le_trans]. Qed.

(** Expose the existing observable equivalence to setoid rewriting without
    asking instance search to guess a SemanticMeasure from its projection. *)
#[global] Instance free_omega_qlift_eq_equivalence A :
  Equivalence (@free_omega_qlift MN NI NO A A eq).
Proof. exact (@sem_eq_equivalence (FreeOmega MN) FI _ A). Qed.

#[global] Instance free_omega_sem_eq_le_proper A :
  Proper (free_omega_qlift eq ==> free_omega_qlift eq ==> iff)
    (@free_omega_sem_le MN NI NO A).
Proof.
  intros t t' Ht u u' Hu. split; intro H.
  - eapply FOSLeTrans; [apply FOSLeEq; apply (sem_eq_sym (SI := FI)); exact Ht|].
    eapply FOSLeTrans; [exact H|apply FOSLeEq; exact Hu].
  - eapply FOSLeTrans; [apply FOSLeEq; exact Ht|].
    eapply FOSLeTrans; [exact H|apply FOSLeEq; apply (sem_eq_sym (SI := FI)); exact Hu].
Qed.

Theorem free_omega_lub_upper {A} (c : nat → FreeOmega MN A) :
  free_omega_struct_increasing c → ∀ n, c n ⊑ω FOLub c.
Proof. apply FOSLeUpper. Qed.
Theorem free_omega_lub_least {A} (c : nat → FreeOmega MN A) u :
  free_omega_struct_increasing c → (∀ n, c n ⊑ω u) → FOLub c ⊑ω u.
Proof. apply FOSLeLeast. Qed.

(** The same rules apply to any witness of the existing sem_lub relation,
    not only to a syntactically displayed FOLub. *)
Theorem free_omega_sem_lub_upper {A} (c : nat → FreeOmega MN A) out :
  free_omega_struct_increasing c → @sem_lub (FreeOmega MN) FI FO A c out →
  ∀ n, c n ⊑ω out.
Proof.
  intros Hi Hout n. eapply FOSLeTrans; [apply free_omega_lub_upper, Hi|].
  apply FOSLeEq, (sem_eq_sym (SI := FI)), Hout.
Qed.

Theorem free_omega_sem_lub_least {A} (c : nat → FreeOmega MN A) out bound :
  free_omega_struct_increasing c → @sem_lub (FreeOmega MN) FI FO A c out →
  (∀ n, c n ⊑ω bound) → out ⊑ω bound.
Proof.
  intros Hi Hout Hbound. eapply FOSLeTrans; [apply FOSLeEq; exact Hout|].
  apply free_omega_lub_least; assumption.
Qed.

(** Bind monotonicity is DERIVED from the rules, not a generating axiom. *)
Theorem free_omega_bind_sem_mono_l {A B} (t u : FreeOmega MN A)
    (k : A → FreeOmega MN B) :
  t ⊑ω u → free_omega_bind t k ⊑ω free_omega_bind u k.
Proof.
  intro H. induction H as [t u H|t u H|t u v H IH G IG|
    X mu h h' H IH|c d H IH|c Hi n|c u Hi H IH]; cbn [free_omega_bind].
  - apply FOSLeApprox. eapply free_omega_approx_bind; [exact H|].
    intros x y ->. apply free_omega_approx_refl. intro z; reflexivity.
  - apply FOSLeEq. eapply FOQLBind; [exact H|].
    intros x y ->. apply free_omega_qlift_refl. intro z; reflexivity.
  - eapply FOSLeTrans; eassumption.
  - apply FOSLeSample. exact IH.
  - apply FOSLeLub. exact IH.
  - apply FOSLeUpper with (c := λ m, free_omega_bind (c m) k) (n := n).
    intro m. eapply free_omega_approx_bind; [apply Hi|].
    intros x y ->. apply free_omega_approx_refl. intro z; reflexivity.
  - apply FOSLeLeast; [|exact IH].
    intro m. eapply free_omega_approx_bind; [apply Hi|].
    intros x y ->. apply free_omega_approx_refl. intro z; reflexivity.
Qed.

Theorem free_omega_bind_sem_mono_k {A B} (t : FreeOmega MN A)
    (k h : A → FreeOmega MN B) :
  (∀ x, k x ⊑ω h x) → free_omega_bind t k ⊑ω free_omega_bind t h.
Proof.
  intro H. induction t; cbn [free_omega_bind].
  - apply H.
  - apply free_omega_sem_le_refl.
  - apply FOSLeSample. exact H0.
  - apply FOSLeLub. exact H0.
Qed.

Theorem free_omega_bind_sem_mono {A B} (t u : FreeOmega MN A)
    (k h : A → FreeOmega MN B) :
  t ⊑ω u → (∀ x, k x ⊑ω h x) → free_omega_bind t k ⊑ω free_omega_bind u h.
Proof.
  intros H G. eapply FOSLeTrans;
    [apply free_omega_bind_sem_mono_l; exact H|apply free_omega_bind_sem_mono_k; exact G].
Qed.
End Laws.
