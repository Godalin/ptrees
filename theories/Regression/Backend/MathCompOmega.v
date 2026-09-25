(** Gate S: all new native capabilities are inferred, not supplied. *)
From mathcomp Require Import reals.
From PTree.Prob.Interface Require Import Measure Omega Mixed.
From PTree.Prob.Backend.MathComp Require Import Kernel Measure NativeLaws OrderLaws OmegaLaws BindLaws.
Fail Check PTree.Eq.Backend.MathComp.Direct.mathcomp_direct_frontier.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Set Implicit Arguments.
Section Checked.
Variable R : realType.
Local Notation M := (MathCompKernelMeasure R).
Local Notation NI := (MathCompNodeSemanticMeasure R).
Local Notation NO := (MathCompNodeSemanticOmega R).
Local Notation MX := (MathCompNativeMixedMeasure R).
Definition checked_omega : @SemanticOmegaLaws M NI NO := _.
Definition checked_mixed_omega : @MixedMeasureOmegaLaws M M NI NI MX NO := _.
Definition checked_diagonal : @SemanticMeasureDiagonalLaws M NI NO := _.
Definition checked_fubini : @SemanticOmegaFubiniLaws M NI NO := _.
Definition checked_bind : @SemanticMeasureBindLaws M NI := _.
Definition checked_mixed : @MixedMeasureLaws M M NI NI MX := _.
Definition checked_omega_ae : @SemanticOmegaAELaws M NI NO := _.

Example increasing_has_actual_lub {A} (c : nat -> M A) :
  sem_increasing c -> exists out, sem_lub c out.
Proof. apply sem_lub_exists. Qed.

Example null_branches_need_no_continuity {A B}
    (c : A -> nat -> M B) (out : A -> M B) :
  sem_lub (fun n => sem_bind (@sem_zero M NI NO A) (fun x => c x n))
    (sem_bind sem_zero out).
Proof.
  apply (@mathcomp_native_bind_lub_ae R A B sem_zero (fun _ => False) c out).
  - apply mathcomp_native_ae_zero.
  - intros x H; contradiction.
  - intros x H; contradiction.
Qed.

Example relation_survives_kernel_bind :
  sem_lift (fun x y : bool => x = negb y)
    (sem_bind (sem_ret true : M bool) (fun b => sem_ret b))
    (sem_bind (sem_ret false : M bool) (fun b => sem_ret b)).
Proof.
  eapply sem_lift_bind with (R := fun x y : bool => x = negb y).
  - apply mathcomp_kernel_lift_ret; reflexivity.
  - intros x y H; apply mathcomp_kernel_lift_ret; exact H.
Qed.
End Checked.

(** Map reflection stays universe-checked and does not need totality, an
    injective decoder, a countable carrier, or an external validation model. *)
Section NativeMapReflection.
Variable R : realType.
Context `{G : MathCompCouplingGluing R}.
Local Notation M := (MathCompKernelMeasure R).

Example noninjective_map_reflection (mu : M bool) (nu : M nat) :
  mathcomp_kernel_lift eq
    (mathcomp_kernel_bind mu (fun _ => mathcomp_kernel_ret R tt))
    (mathcomp_kernel_bind nu (fun _ => mathcomp_kernel_ret R tt)) ->
  mathcomp_kernel_lift (fun _ _ => True) mu nu.
Proof.
  intro H.
  pose proof (@mathcomp_kernel_map_reflect R G bool nat unit unit
    mu nu (fun _ => tt) (fun _ => tt) eq H) as Hr.
  eapply (@sem_lift_mono M (MathCompNodeSemanticMeasure R)
    (@MathCompNodeSemanticMeasureCoreLaws R G)); [|exact Hr].
  intros x y _. exact I.
Qed.

Example empty_map_reflection (mu : M Empty_set) :
  mathcomp_kernel_lift (fun _ _ => False) mu mu.
Proof.
  apply (@mathcomp_kernel_map_reflect R G Empty_set Empty_set
    Empty_set Empty_set mu mu (fun x => x) (fun x => x) (fun _ _ => False)).
  apply mathcomp_kernel_lift_refl. intros [].
Qed.
End NativeMapReflection.
