From Coq Require Import Program.Equality.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum FreeOmegaMeasure.
From PTree.Eq Require Import PrimitiveStableHitting.
From PTree.Eq.FreeOmega Require Import KernelCompletion.

Set Implicit Arguments.
Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).

Definition spinning_kernel (_ : unit) : MF (stable_target unit unit) :=
  FORet (SHInternal tt).
Definition returning_tail (_ : unit) : MF bool := FORet true.

(** Every proposed tail is a fixed point of this purely internal loop.
    Hence a completion equation cannot identify the least hitting limit. *)
Example spin_returning_completion_step s :
  free_omega_qlift eq
    (kernel_completion spinning_kernel (fun _ => true) returning_tail 1 s)
    (returning_tail s).
Proof. apply free_omega_qlift_refl. intro x. reflexivity. Qed.

Lemma spinning_approx_zero n s :
  @stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
    unit unit spinning_kernel n s = FOZero.
Proof.
  induction n as [|n IH] in s |- *; [reflexivity|].
  change (@stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
    unit unit spinning_kernel n tt = FOZero). apply IH.
Qed.

(** Even a correct completion equation need not give a RAW increasing
    completion chain.  The residual tail chooses an equivalent Lub-shaped
    representative, which disappears after one more execution step. *)
Definition two_stage_kernel (done : bool) : MF (stable_target bool unit) :=
  if done then FORet (SHStable tt) else FORet (SHInternal true).

Definition two_stage_tail (done : bool) : MF bool :=
  if done then FOLub (fun _ => FORet true) else FORet true.

Example two_stage_completion_step s :
  free_omega_qlift eq
    (kernel_completion two_stage_kernel (fun _ => true) two_stage_tail 1 s)
    (two_stage_tail s).
Proof.
  destruct s.
  - apply FOQLLubConstantR, free_omega_qlift_refl. intro x. reflexivity.
  - apply FOQLSym, FOQLLubConstantR, free_omega_qlift_refl.
    intro x. reflexivity.
Qed.

Example completed_rounds_need_not_be_raw_increasing :
  ~ free_omega_approx eq
    (kernel_completion two_stage_kernel (fun _ => true) two_stage_tail 1 false)
    (kernel_completion two_stage_kernel (fun _ => true) two_stage_tail 2 false).
Proof. intro H. inversion H. Qed.

Definition spinning_limit : MF unit :=
  FOLub (fun n => @stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
    unit unit spinning_kernel n tt).

Example spin_limit_not_returning_tail :
  ~ free_omega_qlift eq
    (free_omega_bind spinning_limit (fun _ => FORet true)) (returning_tail tt).
Proof.
  intro Hlift. pose proof (proj1 (free_omega_qlift_support Hlift)) as Hsupport.
  assert (Hzero : @free_omega_ae SubEnum SubEnum_SemanticMeasure bool
    (fun _ => False)
    (free_omega_bind spinning_limit (fun _ => FORet true))).
  { apply FOAELub. intro n. rewrite spinning_approx_zero. apply FOAEZero. }
  specialize (Hsupport _ Hzero). dependent destruction Hsupport.
  destruct H as [x [_ Hfalse]]. exact Hfalse.
Qed.

(** An explicit upper bound exists, despite the false equality ruled out
    above.  Upper bounds of this form must not be promoted to equality. *)
Example spin_limit_has_returning_upper :
  exists upper,
    free_omega_approx eq
      (free_omega_bind spinning_limit (fun _ => FORet true)) upper /\
    free_omega_qlift eq upper (returning_tail tt).
Proof.
  exists (FOLub (fun _ => returning_tail tt)). split.
  - apply FOApproxLub. intro n. rewrite spinning_approx_zero. apply FOApproxZero.
  - apply FOQLSym, FOQLLubConstantR, free_omega_qlift_refl.
    intro x. reflexivity.
Qed.
