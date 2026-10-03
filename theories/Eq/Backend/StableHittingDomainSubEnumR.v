(** Role: Finite-real specialization of generic stable-hitting validation.
    Every complete witness is modelable; no user-supplied validity, totality,
    finite support of the limit, or event-free signature is required.
    This external adapter is never imported by the behavioral backend. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import reals.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import UnifiedFrontier PTreeKernel.
From PTree.Prob.Domain Require Import Expectation.
From PTree.Prob.FreeOmega Require Import Measure StructuralMeasure.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega.Validation Require Import Model StableHitting.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega Domain.
From PTree.Prob.Backend.SubEnumR.FreeOmega Require Import Validation.
Set Implicit Arguments.
Unset Strict Implicit.

Section RealHitting.
Variable R : realType.
Context {E : Type → Type} {A : Type}.
Local Notation MN := (SubEnumR R).
Local Notation native := (fun X => @subenumR_domain R X).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumR_SemanticMeasure R) (NO := SubEnumR_SemanticOmega R)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumR_SemanticMeasure R) (NO := SubEnumR_SemanticOmega R)).
Local Notation hits := (@ptree_stable_hitting E MN (FreeOmega MN)
  FI FreeOmegaMixedMeasure FO A).

Definition subenumR_ptree_domain_approx := @ptree_model_approx MN R native E A.
Definition subenumR_ptree_domain_hitting := @ptree_model_hitting MN R native E A.

Theorem subenumR_stable_hitting_modelable s out :
  hits s out → free_omega_modelable native out.
Proof.
  apply stable_hitting_modelable.
  - exact (@subenumR_native_model_ae R).
  - exact (@subenumR_domain_ret R).
  - exact (@subenumR_domain_zero R).
  - exact (@subenumR_domain_bind R).
  - exact (@subenumR_native_model_lift R).
  - exact (@subenumR_native_model_lub R).
Qed.

Theorem subenumR_stable_hitting_denotational_adequacy s out :
  hits s out → free_omega_model_denotes native out (subenumR_ptree_domain_hitting s).
Proof.
  apply stable_hitting_denotational_adequacy.
  - exact (@subenumR_native_model_ae R).
  - exact (@subenumR_domain_ret R).
  - exact (@subenumR_domain_zero R).
  - exact (@subenumR_domain_bind R).
  - exact (@subenumR_native_model_lift R).
  - exact (@subenumR_native_model_lub R).
Qed.

Corollary subenumR_stable_hitting_domain_eq s out
    (Hv : free_omega_modelable native out) :
  hits s out → oval_eq (free_omega_model Hv) (subenumR_ptree_domain_hitting s).
Proof. intros H f Hf; exact (subenumR_stable_hitting_denotational_adequacy H Hf). Qed.

Corollary subenumR_stable_hitting_mass_lub s out (H : hits s out) :
  oval_mass (free_omega_model (subenumR_stable_hitting_modelable H)) =
  oval_sup (λ n, oval_mass (subenumR_ptree_domain_approx n s)).
Proof. exact (subenumR_stable_hitting_denotational_adequacy H (oval_test_one R)). Qed.
End RealHitting.
