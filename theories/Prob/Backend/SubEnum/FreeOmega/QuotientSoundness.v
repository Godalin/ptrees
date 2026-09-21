(** Role: External, SubEnum-qualified soundness of quotient equality.
    Reuse bounded-test equality for ALL raw terms, then transport validity.
    No induction on qlift and no validity premise for intermediate terms.
    This is equality soundness, not general relational joint realization. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg ssrnum order reals.
From PTree.Prob.Interface Require Import Measure.
From PTree.Prob.Domain Require Import Expectation.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Quotient Measure.
From PTree.Prob.Backend.SubEnum Require Import Measure.
From PTree.Prob.Backend.SubEnum.FreeOmega Require Import
  UpperExpectation UpperQuotient Admissibility.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section QuotientSoundness.
Variable R : realType.

(** Only equality preserves admissibility this way: arbitrary relational
    liftings may pass through inadmissible raw terms on other carriers. *)
Theorem free_omega_qlift_eq_admissible {A} (t u : FreeOmega SubEnum A) :
  free_omega_qlift eq t u ->
  (free_omega_admissible R t <-> free_omega_admissible R u).
Proof.
  intro H; split; intro Hv; eapply free_omega_admissible_ext; [exact Hv| |exact Hv|].
  - intros f Hf; exact (free_omega_qlift_eq_upper H Hf).
  - intros f Hf; symmetry; exact (free_omega_qlift_eq_upper H Hf).
Qed.

(** Both proof arguments can be arbitrary; obtain either one's existence
    from the preceding iff when only one endpoint is initially valid. *)
Theorem free_omega_qlift_eq_sound {A} (t u : FreeOmega SubEnum A)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  free_omega_qlift eq t u ->
  oval_eq (free_omega_domain Ht) (free_omega_domain Hu).
Proof. intros H f Hf; exact (free_omega_qlift_eq_upper H Hf). Qed.

(** Pin sem_eq to the maintained observable instance, not the auxiliary
    structural instance. No Semantic capability becomes a new premise. *)
Theorem free_omega_sem_eq_admissible {A} (t u : FreeOmega SubEnum A) :
  @sem_eq (FreeOmega SubEnum)
    (@FreeOmegaObservableSemanticMeasure SubEnum
      SubEnum_SemanticMeasure SubEnum_SemanticOmega) A t u ->
  (free_omega_admissible R t <-> free_omega_admissible R u).
Proof. exact: free_omega_qlift_eq_admissible. Qed.

Theorem free_omega_sem_eq_sound {A} (t u : FreeOmega SubEnum A)
    (Ht : free_omega_admissible R t) (Hu : free_omega_admissible R u) :
  @sem_eq (FreeOmega SubEnum)
    (@FreeOmegaObservableSemanticMeasure SubEnum
      SubEnum_SemanticMeasure SubEnum_SemanticOmega) A t u ->
  oval_eq (free_omega_domain Ht) (free_omega_domain Hu).
Proof. exact: free_omega_qlift_eq_sound. Qed.
End QuotientSoundness.
