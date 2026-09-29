(** Independent leastness, checked MathComp instantiation, and rational
    FreeOmega interpretation. None is an AST or normalization assertion. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import reals.
From PTree.Prob.Domain Require Import Expectation Iteration.
Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Set Implicit Arguments.

Section IndependentDomain.
Variable R : realType.
Context {I A : Type} (K : I -> OmegaVal R (I+A)).
Example domain_fixed_point i : oval_eq (oval_iter K i) (oval_iter_step K (oval_iter K) i).
Proof. apply oval_iter_fixed_point. Qed.
Example domain_least_prefixed Y :
  (forall i, oval_le (oval_iter_step K Y i) (Y i)) ->
  forall i, oval_le (oval_iter K i) (Y i).
Proof. apply oval_iter_least_prefixed. Qed.
End IndependentDomain.

Example domain_retry_least_is_bottom (R : realType) i :
  oval_eq
    (oval_iter (fun n : nat => oval_ret R (inl (S n) : nat+bool)) i)
    (@oval_bottom R bool).
Proof.
  apply oval_le_antisym.
  - apply (oval_iter_least_prefixed (Y := fun _ => @oval_bottom R bool)).
    intros j f Hf. exact (oval_le_refl (@oval_bottom R bool) Hf).
  - apply oval_bottom_le.
Qed.

From PTree.Prob.Interface Require Import Measure Omega KleisliIteration.
From PTree.Prob.Backend.MathComp Require Import Kernel Measure Iteration.
Section CheckedMathComp.
Variable R : realType.
Context {I A : Type} (K : I -> MathCompKernelMeasure R (I+A)).
Example checked_lfp_exists i :
  sem_iter (MI := MathCompNodeSemanticMeasure R) (MO := MathCompNodeSemanticOmega R)
    K i (mathcomp_iteration K i).
Proof. apply mathcomp_iteration_spec. Qed.
Example checked_lfp_least Y :
  (forall i, sem_le (sem_iter_step K Y i) (Y i)) ->
  forall i, sem_le (mathcomp_iteration K i) (Y i).
Proof. exact (proj2 (mathcomp_iteration_least_fixed_point K) Y). Qed.
End CheckedMathComp.
Fail Check PTree.Core.PTreeDefinition.ptree.
Fail Check PTree.Eq.Backend.MathComp.mathcomp_peutt.

Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Measure.
From PTree.Prob.FreeOmega.Validation Require Import Expectation Iteration.
From PTree.Prob.Backend.SubEnumQ Require Import Representation Measure Domain.
Section RationalInterpretation.
Variable R : realType.
Variable kernel : nat -> SubEnumQ (nat+bool).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation native := (fun X => @subenumQ_domain R X).
Definition formal_kernel i := FOSample (kernel i) (fun v => FORet v).

Example rational_loop_denotes_lfp i :
  free_omega_model_denotes native
    (FOLub (fun n => sem_iter_approx (MI := FI) (MO := FO) formal_kernel n i))
    (oval_iter (fun j => subenumQ_domain R (kernel j)) i).
Proof.
  apply free_omega_iteration_denotes_lfp.
  intros j f Hf. reflexivity.
Qed.
Example rational_loop_modelable i :
  free_omega_modelable native
    (FOLub (fun n => sem_iter_approx (MI := FI) (MO := FO) formal_kernel n i)).
Proof.
  apply (proj2 (modelable_iff_denotes _ _)).
  exists (oval_iter (fun j => subenumQ_domain R (kernel j)) i).
  apply rational_loop_denotes_lfp.
Qed.
End RationalInterpretation.
