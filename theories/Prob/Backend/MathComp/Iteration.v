(** Checked classical least-fixed-point semantics. This is native measure
    mathematics, with no recursive PTree assembly or universe relaxation. *)
From mathcomp Require Import reals.
From PTree.Prob.Interface Require Import Measure Omega KleisliIteration.
From PTree.Prob.Backend.MathComp Require Import Kernel Measure NativeLaws OrderLaws OmegaLaws.
Set Implicit Arguments.
Unset Strict Implicit.

Section Iteration.
Variable R : realType.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Context {I A : Type} (K : I -> M (I+A)).

Definition mathcomp_iteration i : M A :=
  mathcomp_native_lub (sem_iter_approx_increasing (MI := NI) (MO := NO) K i).

Lemma mathcomp_iteration_spec i :
  sem_iter (MI := NI) (MO := NO) K i (mathcomp_iteration i).
Proof. apply mathcomp_native_lub_spec. Qed.

Theorem mathcomp_iteration_fixed_point i :
  sem_eq (mathcomp_iteration i) (sem_iter_step K mathcomp_iteration i).
Proof.
  apply (sem_iter_fixed_point (MI := NI) (MO := NO)); try typeclasses eauto.
  exact mathcomp_iteration_spec.
Qed.

Theorem mathcomp_iteration_least_fixed_point :
  (forall i, sem_le (sem_iter_step K mathcomp_iteration i) (mathcomp_iteration i) /\
             sem_le (mathcomp_iteration i) (sem_iter_step K mathcomp_iteration i)) /\
  (forall Y, (forall i, sem_le (sem_iter_step K Y i) (Y i)) ->
             forall i, sem_le (mathcomp_iteration i) (Y i)).
Proof.
  apply (sem_iter_least_fixed_point (MI := NI) (MO := NO)); try typeclasses eauto.
  - intros c out H n. exact (mathcomp_native_lub_upper n H).
  - intros c out bound H Hb. exact (mathcomp_native_lub_least H Hb).
  - exact mathcomp_iteration_spec.
Qed.
End Iteration.
