(** Universe-checked native obligations for generic finite bind scheduling.
    No PTree or recursive frontier is instantiated here. *)
From mathcomp Require Import reals.
From PTree.Prob.Interface Require Import Measure Omega Mixed BindOrder.
From PTree.Prob.Backend.MathComp Require Import Kernel Measure NativeLaws
  OrderLaws OmegaLaws BindLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Laws.
Variable R : realType.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Local Notation MX := (MathCompNativeMixedMeasure R).

#[global] Instance MathCompNativeBindOrderLaws :
  @SemanticMeasureBindOrderLaws M NI NO.
Proof.
  constructor.
  - intros A B x k; split; apply mathcomp_native_eq_le.
    + apply mathcomp_kernel_bind_ret_l.
    + apply mathcomp_kernel_eq_sym, mathcomp_kernel_bind_ret_l.
  - intros A B k; apply mathcomp_native_eq_le, mathcomp_native_bind_zero_left.
Qed.

#[global] Instance MathCompNativeMixedBindOrderLaws :
  @MixedMeasureBindOrderLaws M M NI MX NO.
Proof.
  constructor.
  - intros A B C mu k h; split; apply mathcomp_native_eq_le.
    + apply mathcomp_kernel_bind_assoc.
    + apply mathcomp_kernel_eq_sym, mathcomp_kernel_bind_assoc.
  - intros A B mu k h H; apply mathcomp_native_bind_le_k; exact H.
Qed.

#[global] Instance MathCompNativeDirectedCofinalityLaws :
  @SemanticOmegaDirectedCofinalityLaws M NI NO.
Proof.
  constructor. intros A c d out Hc Hd Hcd Hdc.
  apply mathcomp_native_lub_cofinal; assumption.
Qed.

#[global] Instance MathCompNativeOmegaSelection :
  @SemanticOmegaSelection M NI NO.
Proof.
  constructor. intros A c Hi.
  exists (mathcomp_native_lub Hi). apply mathcomp_native_lub_spec.
Defined.
End Laws.
