(** Role: external mathematical-model example, not a reasoning dependency. *)
(** Leastness rejects an endless retry; a native rational loop interprets
    into that independent domain. Production LFP laws are audited at their owners. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import reals.
From PTree.Prob.Domain Require Import Expectation Iteration.
Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Set Implicit Arguments.

Example domain_retry_least_is_bottom (R : realType) i :
  oval_eq
    (oval_iter (λ n : nat, oval_ret R (inl (S n) : nat+bool)) i)
    (@oval_bottom R bool).
Proof.
  apply oval_le_antisym.
  - apply (oval_iter_least_prefixed (Y := λ _, @oval_bottom R bool)).
    intros j f Hf. exact (oval_le_refl (@oval_bottom R bool) Hf).
  - apply oval_bottom_le.
Qed.

From PTree.Prob.Interface Require Import Measure Omega KleisliIteration.
Fail Check PTree.Core.PTreeDefinition.ptree.

Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Measure.
From PTree.Prob.FreeOmega.Validation Require Import Model Iteration.
From PTree.Prob.Backend.SubEnumQ Require Import Representation Measure Domain.
Section RationalInterpretation.
Variable R : realType.
Variable kernel : nat → SubEnumQ (nat+bool).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation native := (fun X => @subenumQ_domain R X).
Definition formal_kernel i := FOSample (kernel i) (λ v, FORet v).

Example rational_loop_denotes_lfp i :
  free_omega_model_denotes native
    (FOLub (λ n, sem_iter_approx (MI := FI) (MO := FO) formal_kernel n i))
    (oval_iter (λ j, subenumQ_domain R (kernel j)) i).
Proof.
  apply free_omega_iteration_denotes_lfp.
  intros j f Hf. reflexivity.
Qed.
Example rational_loop_modelable i :
  free_omega_modelable native
    (FOLub (λ n, sem_iter_approx (MI := FI) (MO := FO) formal_kernel n i)).
Proof.
  apply (proj2 (modelable_iff_denotes _ _)).
  exists (oval_iter (λ j, subenumQ_domain R (kernel j)) i).
  apply rational_loop_denotes_lfp.
Qed.
End RationalInterpretation.
