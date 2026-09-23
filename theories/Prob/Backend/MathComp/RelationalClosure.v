(** Checked native relational certificates. Relational lub is deliberately
    absent: ordinary omega completeness does not prove coupling compactness. *)
From mathcomp Require Import reals.
From PTree.Prob.Interface Require Import Measure Omega Mixed RelationalClosure.
From PTree.Prob.Backend.MathComp Require Import Kernel Measure NativeLaws BindLaws.
Set Implicit Arguments.

Section NativeRelationalClosure.
Variable R : realType.
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).

Theorem mathcomp_relational_bind : relational_bind NI.
Proof. apply relational_bind_of_laws. typeclasses eauto. Qed.

Theorem mathcomp_relational_mixed_bind :
  relational_mixed_bind NI NI (MathCompNativeMixedMeasure R).
Proof. apply relational_mixed_bind_of_laws. typeclasses eauto. Qed.

Theorem mathcomp_relational_zero : relational_zero NO.
Proof.
  intros A B T.
  pose (k := fun x : Empty_set => match x return MathCompKernelMeasure R A with end).
  pose (h := fun x : Empty_set => match x return MathCompKernelMeasure R B with end).
  eapply mathcomp_kernel_lift_proper_l with
    (mu := mathcomp_kernel_bind (mathcomp_kernel_zero R) k).
  - apply mathcomp_native_bind_zero_left.
  - eapply mathcomp_kernel_lift_proper_r with
      (nu := mathcomp_kernel_bind (mathcomp_kernel_zero R) h).
    + apply mathcomp_native_bind_zero_left.
    + eapply mathcomp_native_lift_bind with (S := @eq Empty_set).
      * apply mathcomp_kernel_lift_refl. intros x. reflexivity.
      * intros x. destruct x.
Qed.
End NativeRelationalClosure.
