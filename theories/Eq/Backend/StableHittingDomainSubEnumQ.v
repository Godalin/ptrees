(** Role: One-way external validation of SubEnumQ PTree stable hitting.
    The mathematical kernel/iterates below use OmegaVal operations directly;
    FreeOmega finite iterates are related by a separate induction on fuel.
    This module is not imported by the maintained equational API. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Domain Require Import Expectation.
From PTree.Prob.Interface Require Import Measure Omega.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import StructuralMeasure Measure.
From PTree.Prob.Backend.SubEnumQ Require Import Measure Domain Expectation.
From PTree.Prob.Backend.SubEnumQ.FreeOmega Require Import
  Admissibility DomainSoundness QuotientSoundness.
From PTree.Eq Require Import PrimitiveStableHitting UnifiedFrontier PTreeKernel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

(** Mathematical hitting for any OmegaVal kernel. No FreeOmega evaluator
    or syntactic approximation occurs in these definitions or proofs. *)
Section DomainKernel.
Variable R : realType.
Context {S H : Type}.
Variable K : S -> OmegaVal R (stable_target S H).

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

Lemma domain_hitting_approx_increasing s : oval_increasing (fun n => domain_hitting_approx n s).
Proof.
  intro n; apply oval_bind_mono; [apply oval_le_refl|intro z].
  exact: domain_target_approx_increasing.
Qed.

Definition domain_hitting s : OmegaVal R H := oval_lub (domain_hitting_approx_increasing s).
End DomainKernel.

Local Notation FI := (@FreeOmegaObservableSemanticMeasure SubEnumQ
  SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).
Local Notation FO := (@FreeOmegaObservableSemanticOmega SubEnumQ
  SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega).

Section FiniteCommutation.
Variable R : realType.
Context {S H : Type}.
Variable K : S -> FreeOmega SubEnumQ (stable_target S H).
Variable D : S -> OmegaVal R (stable_target S H).
Hypothesis HK : forall s, free_omega_domain_denotes (K s) (D s).

Theorem stable_target_denotational_commutation n z :
  free_omega_domain_denotes
    (@stable_target_approx _ FI FO S H K n z) (domain_target_approx D n z).
Proof.
  induction n as [|n IH] in z |- *; destruct z; cbn [stable_target_approx domain_target_approx].
  - exact: free_omega_denote_ret.
  - exact: free_omega_denote_zero.
  - exact: free_omega_denote_ret.
  - apply free_omega_denote_bind; [apply HK|exact IH].
Qed.

Theorem stable_hitting_finite_commutation n s :
  free_omega_domain_denotes
    (@stable_hitting_approx _ FI FO S H K n s) (domain_hitting_approx D n s).
Proof.
  apply free_omega_denote_bind; [apply HK|intro z].
  exact: stable_target_denotational_commutation.
Qed.
End FiniteCommutation.

Section PTreeDomain.
Variable R : realType.
Context {E : Type -> Type} {A : Type}.
Local Notation state := (ptree' E SubEnumQ A).
Local Notation head := (stable_head E SubEnumQ A).
Local Notation K := (@ptree_primitive_kernel E SubEnumQ (FreeOmega SubEnumQ)
  FI FreeOmegaMixedMeasure A).
Local Notation approx := (@ptree_hitting_approx E SubEnumQ (FreeOmega SubEnumQ)
  FI FreeOmegaMixedMeasure FO A).
Local Notation hits := (@ptree_stable_hitting E SubEnumQ (FreeOmega SubEnumQ)
  FI FreeOmegaMixedMeasure FO A).

(** Direct mathematical interpretation of one primitive observation.
    A Prob samples the native subdistribution without normalizing its mass. *)
Definition ptree_domain_kernel (s : state) : OmegaVal R (stable_target state head) :=
  match s with
  | RetF a => oval_ret R (SHStable (FHRet a))
  | VisF _ e k => oval_ret R (SHStable (FHVis e k))
  | TauF t => oval_ret R (SHInternal (observe t))
  | ProbF _ mu k => oval_bind (subenumQ_domain R mu)
      (fun x => oval_ret R (SHInternal (observe (k x))))
  end.

Definition ptree_domain_approx := domain_hitting_approx ptree_domain_kernel.
Definition ptree_domain_hitting := domain_hitting ptree_domain_kernel.

Lemma ptree_domain_approx_ret n a f :
  oval_eval (ptree_domain_approx n (RetF a)) f = f (FHRet a).
Proof. destruct n; reflexivity. Qed.

Lemma ptree_domain_approx_vis {X} n (e : E X) k f :
  oval_eval (ptree_domain_approx n (VisF e k)) f = f (FHVis e k).
Proof. destruct n; reflexivity. Qed.

Lemma ptree_domain_approx_tau_zero t f :
  oval_eval (ptree_domain_approx O (TauF t)) f = 0.
Proof. reflexivity. Qed.

Lemma ptree_domain_approx_tau_succ n t f :
  oval_eval (ptree_domain_approx (Datatypes.S n) (TauF t)) f =
  oval_eval (ptree_domain_approx n (observe t)) f.
Proof. reflexivity. Qed.

Lemma ptree_domain_approx_prob_zero {X} (mu : SubEnumQ X) k f :
  oval_eval (ptree_domain_approx O (ProbF mu k)) f = 0.
Proof. apply enumQ_real_expect_zero. Qed.

Lemma ptree_domain_approx_prob_succ {X} n (mu : SubEnumQ X) k f :
  oval_eval (ptree_domain_approx (Datatypes.S n) (ProbF mu k)) f =
  enumQ_real_expect (fun x => oval_eval (ptree_domain_approx n (observe (k x))) f)
    (subenumQ_raw mu).
Proof. reflexivity. Qed.

Theorem ptree_kernel_denotational_commutation s :
  free_omega_domain_denotes (K s) (ptree_domain_kernel s).
Proof.
  destruct s; try exact: free_omega_denote_ret.
  apply free_omega_denote_sample=> x; exact: free_omega_denote_ret.
Qed.

Theorem ptree_hitting_finite_commutation n s :
  free_omega_domain_denotes (approx n s) (ptree_domain_approx n s).
Proof. apply stable_hitting_finite_commutation; exact ptree_kernel_denotational_commutation. Qed.

Theorem ptree_hitting_approx_admissible n s : free_omega_admissible R (approx n s).
Proof.
  apply (proj2 (free_omega_admissible_iff_denotes R _)).
  exists (ptree_domain_approx n s); exact: ptree_hitting_finite_commutation.
Qed.

Theorem ptree_hitting_approx_domain_increasing s :
  free_omega_domain_increasing R (fun n => approx n s).
Proof.
  intros n f Hf.
  rewrite (ptree_hitting_finite_commutation n s Hf)
    (ptree_hitting_finite_commutation (Datatypes.S n) s Hf).
  exact (domain_hitting_approx_increasing ptree_domain_kernel s n Hf).
Qed.

Definition ptree_canonical_hitting (s : state) := FOLub (fun n => approx n s).

Theorem ptree_canonical_hitting_spec s : hits s (ptree_canonical_hitting s).
Proof. apply free_omega_qlift_refl; intros h; reflexivity. Qed.

Theorem ptree_canonical_hitting_admissible s :
  free_omega_admissible R (ptree_canonical_hitting s).
Proof.
  apply admissible_lub; [intro n; exact: ptree_hitting_approx_admissible|].
  exact: ptree_hitting_approx_domain_increasing.
Qed.

Theorem ptree_canonical_hitting_denotes s :
  free_omega_domain_denotes (ptree_canonical_hitting s) (ptree_domain_hitting s).
Proof. apply free_omega_denote_lub=> n; exact: ptree_hitting_finite_commutation. Qed.

(** An arbitrary complete witness is not assumed valid: DS3 transports
    validity from the canonical Lub along observable quotient equality. *)
Theorem stable_hitting_admissible s out : hits s out -> free_omega_admissible R out.
Proof.
  intro H; apply (proj2 (free_omega_sem_eq_admissible R H)).
  exact: ptree_canonical_hitting_admissible.
Qed.

Theorem stable_hitting_denotational_adequacy s out :
  hits s out -> free_omega_domain_denotes out (ptree_domain_hitting s).
Proof.
  intro H.
  have Heq := free_omega_sem_eq_sound (stable_hitting_admissible H)
    (ptree_canonical_hitting_admissible s) H.
  intros f Hf; transitivity (oval_eval (free_omega_domain (ptree_canonical_hitting_admissible s)) f).
  - exact (Heq f Hf).
  - exact (ptree_canonical_hitting_denotes s Hf).
Qed.

Corollary stable_hitting_domain_eq s out (Hv : free_omega_admissible R out) :
  hits s out -> oval_eq (free_omega_domain Hv) (ptree_domain_hitting s).
Proof. intros H f Hf; exact (stable_hitting_denotational_adequacy H Hf). Qed.

Corollary stable_hitting_mass_lub s out (H : hits s out) :
  oval_mass (free_omega_domain (stable_hitting_admissible H)) =
  oval_sup (fun n => oval_mass (ptree_domain_approx n s)).
Proof. exact (stable_hitting_denotational_adequacy H (oval_test_one R)). Qed.
End PTreeDomain.
