(** Role: One-way native-parametric PTree stable-hitting validation.
    Finite mathematical iterates are defined directly in OmegaVal; their
    formal counterparts commute with interpretation. Complete witnesses
    inherit validity by quotient equality, with no validity premise on the
    witness or on raw intermediate terms. Mainline theory never imports this. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Domain Require Import Expectation Countable.
From PTree.Prob.Interface Require Import Measure Omega.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import StructuralMeasure Measure Quotient.
From PTree.Prob.FreeOmega.Validation Require Import Model Quotient.
From PTree.Eq Require Import PrimitiveStableHitting UnifiedFrontier PTreeKernel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section DomainKernel.
Variable R : realType.
Context {S H : Type}.
Variable K : S → OmegaVal R (stable_target S H).

Fixpoint domain_target_approx (n : nat) (z : stable_target S H) : OmegaVal R H :=
  match z with
  | SHStable h => oval_ret R h
  | SHInternal s =>
      match n with
      | O => oval_bottom R
      | Datatypes.S m => oval_bind (K s) (domain_target_approx m)
      end
  end.

Definition domain_hitting_approx n s := oval_bind (K s) (domain_target_approx n).

Lemma domain_target_approx_increasing n z :
  oval_le (domain_target_approx n z) (domain_target_approx (Datatypes.S n) z).
Proof.
  induction n as [|n IH] in z |- *; destruct z; cbn [domain_target_approx].
  - apply oval_le_refl.
  - apply oval_bottom_le.
  - apply oval_le_refl.
  - apply oval_bind_mono; [apply oval_le_refl|exact IH].
Qed.

Lemma domain_hitting_approx_increasing s : oval_increasing (λ n, domain_hitting_approx n s).
Proof.
  intro n; apply oval_bind_mono; [apply oval_le_refl|intro z].
  exact: domain_target_approx_increasing.
Qed.

Definition domain_hitting s : OmegaVal R H := oval_lub (domain_hitting_approx_increasing s).
End DomainKernel.

Section Validation.
Context {MN : Type → Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI} `{NO : @SemanticOmega MN NI}.
Variable R : realType.
Variable native : ∀ X, MN X → OmegaVal R X.
Arguments native X _ : clear implicits.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).

Section FiniteCommutation.
Context {S H : Type}.
Variable K : S → FreeOmega MN (stable_target S H).
Variable D : S → OmegaVal R (stable_target S H).
Hypothesis HK : ∀ s, free_omega_model_denotes native (K s) (D s).

Theorem stable_target_denotational_commutation n z :
  free_omega_model_denotes native
    (@stable_target_approx _ FI FO S H K n z) (domain_target_approx D n z).
Proof.
  induction n as [|n IH] in z |- *; destruct z;
    cbn [stable_target_approx domain_target_approx].
  - intros f Hf; reflexivity.
  - intros f Hf; reflexivity.
  - intros f Hf; reflexivity.
  - apply model_denotes_bind; [apply HK|exact IH].
Qed.

Theorem stable_hitting_finite_commutation n s :
  free_omega_model_denotes native
    (@stable_hitting_approx _ FI FO S H K n s) (domain_hitting_approx D n s).
Proof.
  apply model_denotes_bind; [apply HK|intro z].
  exact: stable_target_denotational_commutation.
Qed.
End FiniteCommutation.

Section PTreeModel.
Context {E : Type → Type} {A : Type}.
Local Notation state := (ptree' E MN A).
Local Notation head := (stable_head E MN A).
Local Notation K := (@ptree_primitive_kernel E MN (FreeOmega MN)
  FI FreeOmegaMixedMeasure A).
Local Notation approx := (@ptree_hitting_approx E MN (FreeOmega MN)
  FI FreeOmegaMixedMeasure FO A).
Local Notation hits := (@ptree_stable_hitting E MN (FreeOmega MN)
  FI FreeOmegaMixedMeasure FO A).

(** Independent mathematical one-step kernel; internal probability keeps
    missing mass. Vis is an absorbing head with its WHOLE continuation. *)
Definition ptree_model_kernel (s : state) : OmegaVal R (stable_target state head) :=
  match s with
  | RetF a => oval_ret R (SHStable (FHRet a))
  | VisF _ e k => oval_ret R (SHStable (FHVis e k))
  | TauF t => oval_ret R (SHInternal (observe t))
  | ProbF X mu k => oval_bind (native X mu)
      (λ x, oval_ret R (SHInternal (observe (k x))))
  end.
Definition ptree_model_approx := domain_hitting_approx ptree_model_kernel.
Definition ptree_model_hitting := domain_hitting ptree_model_kernel.

Theorem ptree_kernel_model_commutation s :
  free_omega_model_denotes native (K s) (ptree_model_kernel s).
Proof. destruct s; intros f Hf; reflexivity. Qed.

Theorem ptree_hitting_model_commutation n s :
  free_omega_model_denotes native (approx n s) (ptree_model_approx n s).
Proof. apply stable_hitting_finite_commutation; exact ptree_kernel_model_commutation. Qed.

Theorem ptree_hitting_approx_modelable n s : free_omega_modelable native (approx n s).
Proof.
  apply (proj2 (modelable_iff_denotes _ _)).
  exists (ptree_model_approx n s); exact: ptree_hitting_model_commutation.
Qed.

Theorem ptree_hitting_approx_model_increasing s :
  model_chain_increasing native (λ n, approx n s).
Proof.
  intros n f Hf.
  rewrite (ptree_hitting_model_commutation n s Hf)
    (ptree_hitting_model_commutation (Datatypes.S n) s Hf).
  exact (domain_hitting_approx_increasing ptree_model_kernel s n Hf).
Qed.

Definition ptree_canonical_hitting (s : state) := FOLub (λ n, approx n s).

Theorem ptree_canonical_hitting_spec s : hits s (ptree_canonical_hitting s).
Proof. apply free_omega_qlift_refl; intros h; reflexivity. Qed.

Theorem ptree_canonical_hitting_modelable s :
  free_omega_modelable native (ptree_canonical_hitting s).
Proof.
  apply modelable_lub; [intro n; exact: ptree_hitting_approx_modelable|].
  exact: ptree_hitting_approx_model_increasing.
Qed.

Theorem ptree_canonical_hitting_denotes s :
  free_omega_model_denotes native (ptree_canonical_hitting s) (ptree_model_hitting s).
Proof. apply model_denotes_lub=> n; exact: ptree_hitting_model_commutation. Qed.

(** Only transport to an arbitrary quotient-equal witness needs the native
    interpretation obligations. Canonical validity above needs none of them. *)
Hypothesis native_ae : ∀ X (mu : MN X) P,
  sem_ae mu P → oval_ae (native X mu) P.
Hypothesis native_ret : ∀ X (x : X),
  oval_eq (native X (sem_ret x)) (oval_ret R x).
Hypothesis native_zero : ∀ X,
  oval_eq (native X (@sem_zero MN NI NO X)) (@oval_bottom R X).
Hypothesis native_bind : ∀ X Y (mu : MN X) (k : X → MN Y),
  oval_eq (native Y (sem_bind mu k)) (oval_bind (native X mu) (λ x, native Y (k x))).
Hypothesis native_lift : ∀ X Y (T : X → Y → Prop) (mu : MN X) (nu : MN Y) f g,
  sem_lift T mu nu → oval_test f → oval_test g →
  (∀ x y, T x y → f x <= g y) → oval_eval (native X mu) f <= oval_eval (native Y nu) g.
Hypothesis native_lub : ∀ X (c : nat → MN X) out,
  (∀ n f, oval_test f → oval_eval (native X (c n)) f <= oval_eval (native X (c (S n))) f) →
  sem_lub c out → ∀ f, oval_test f →
  oval_sup (λ n, oval_eval (native X (c n)) f) = oval_eval (native X out) f.

Theorem stable_hitting_modelable s out : hits s out → free_omega_modelable native out.
Proof.
  intro H.
  apply (proj2 (model_qlift_eq_modelable native_ae native_ret native_zero
    native_bind native_lift native_lub H)).
  exact: ptree_canonical_hitting_modelable.
Qed.

Theorem stable_hitting_denotational_adequacy s out :
  hits s out → free_omega_model_denotes native out (ptree_model_hitting s).
Proof.
  intros H f Hf.
  rewrite (model_qlift_eq_upper native_ae native_ret native_zero
    native_bind native_lift native_lub H Hf).
  exact (ptree_canonical_hitting_denotes s Hf).
Qed.

Corollary stable_hitting_model_eq s out (Hv : free_omega_modelable native out) :
  hits s out → oval_eq (free_omega_model Hv) (ptree_model_hitting s).
Proof. intros H f Hf; exact (stable_hitting_denotational_adequacy H Hf). Qed.

Corollary stable_hitting_model_mass_lub s out (H : hits s out) :
  oval_mass (free_omega_model (stable_hitting_modelable H)) =
  oval_sup (λ n, oval_mass (ptree_model_approx n s)).
Proof. exact (stable_hitting_denotational_adequacy H (oval_test_one R)). Qed.
End PTreeModel.
End Validation.
