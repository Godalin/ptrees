From Coq Require Import Utf8.

From PTree.Prob.Backend.EnumQ.FreeOmega Require Import Coupling.
(** Maintained internal kernel contracts: leastness, raw-order boundaries,
    continuity and congruence. Not a public equivalence or application. *)

From Coq Require Program.Equality.
Require PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require PTree.Prob.Backend.SubEnumQ.Measure.
Require PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require PTree.Eq.PrimitiveStableHitting.
Require PTree.Eq.Internal.FreeOmega.KernelCompletion.
Module KernelCompletion.
(** Role: supporting compression/scheduling/recovery example; not public theory. *)
Import Program.Equality.
Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Import PTree.Prob.Backend.SubEnumQ.Measure.
Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Import PTree.Eq.PrimitiveStableHitting.
Import PTree.Eq.Internal.FreeOmega.KernelCompletion.

Set Implicit Arguments.
Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).

Definition spinning_kernel (_ : unit) : MF (stable_target unit unit) :=
  FORet (SHInternal tt).
Definition returning_tail (_ : unit) : MF bool := FORet true.

(** Every proposed tail is a fixed point of this purely internal loop.
    Hence a completion equation cannot identify the least hitting limit. *)
Example spin_returning_completion_step s :
  free_omega_qlift eq
    (kernel_completion spinning_kernel (λ _, true) returning_tail 1 s)
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
  if done then FOLub (λ _, FORet true) else FORet true.

Example two_stage_completion_step s :
  free_omega_qlift eq
    (kernel_completion two_stage_kernel (λ _, true) two_stage_tail 1 s)
    (two_stage_tail s).
Proof.
  destruct s.
  - apply FOQLLubConstantR, free_omega_qlift_refl. intro x. reflexivity.
  - apply FOQLSym, FOQLLubConstantR, free_omega_qlift_refl.
    intro x. reflexivity.
Qed.

Example completed_rounds_need_not_be_raw_increasing :
  ¬ free_omega_approx eq
    (kernel_completion two_stage_kernel (λ _, true) two_stage_tail 1 false)
    (kernel_completion two_stage_kernel (λ _, true) two_stage_tail 2 false).
Proof. intro H. inversion H. Qed.

Definition spinning_limit : MF unit :=
  FOLub (λ n, @stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
    unit unit spinning_kernel n tt).

Example spin_limit_not_returning_tail :
  ¬ free_omega_qlift eq
    (free_omega_bind spinning_limit (λ _, FORet true)) (returning_tail tt).
Proof.
  intro Hlift. pose proof (proj1 (free_omega_qlift_support Hlift)) as Hsupport.
  assert (Hzero : @free_omega_ae SubEnumQ SubEnumQ_SemanticMeasure bool
    (λ _, False)
    (free_omega_bind spinning_limit (λ _, FORet true))).
  { apply FOAELub. intro n. rewrite spinning_approx_zero. apply FOAEZero. }
  specialize (Hsupport _ Hzero). dependent destruction Hsupport.
  destruct H as [x [_ Hfalse]]. exact Hfalse.
Qed.

(** An explicit upper bound exists, despite the false equality ruled out
    above.  Upper bounds of this form must not be promoted to equality. *)
Example spin_limit_has_returning_upper :
  ∃ upper,
    free_omega_approx eq
      (free_omega_bind spinning_limit (λ _, FORet true)) upper ∧
    free_omega_qlift eq upper (returning_tail tt).
Proof.
  exists (FOLub (λ _, returning_tail tt)). split.
  - apply FOApproxLub. intro n. rewrite spinning_approx_zero. apply FOApproxZero.
  - apply FOQLSym, FOQLLubConstantR, free_omega_qlift_refl.
    intro x. reflexivity.
Qed.

End KernelCompletion.

From Coq Require Arith.PeanoNat.
From Coq Require Lia.
From Coq Require Program.Equality.
Require PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require PTree.Prob.Backend.SubEnumQ.Measure.
Require PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require PTree.Eq.PrimitiveStableHitting.
Require PTree.Eq.Internal.FreeOmega.KernelContinuity.
Module KernelContinuity.
(** Role: supporting compression/scheduling/recovery example; not public theory. *)
Set Universe Polymorphism.
Import Arith.PeanoNat.
Import Lia.
Import Program.Equality.
Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Import PTree.Prob.Backend.SubEnumQ.Measure.
Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Import PTree.Eq.PrimitiveStableHitting.
Import PTree.Eq.Internal.FreeOmega.KernelContinuity.

Set Implicit Arguments.

(** Truncate by a rank of the CURRENT state, not by a bound on all states
    an execution can visit.  The full kernel may be probabilistic, eventful,
    internally divergent, or have infinitely many reachable states. *)
Section StateTruncation.
Context {S O : Type}.
Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Variable kernel : S → MF (stable_target S O).
Variable rank : S → nat.

Definition ranked_kernel n s : MF (stable_target S O) :=
  if Nat.leb (rank s) n then kernel s else FOZero.

Lemma ranked_kernel_increasing n s :
  free_omega_approx eq (ranked_kernel n s) (ranked_kernel (Datatypes.S n) s).
Proof.
  unfold ranked_kernel.
  destruct (Nat.leb (rank s) n) eqn:Hn;
    destruct (Nat.leb (rank s) (Datatypes.S n)) eqn:Hnext.
  - apply free_omega_approx_refl. intro x. reflexivity.
  - apply Nat.leb_le in Hn. apply Nat.leb_gt in Hnext. lia.
  - apply FOApproxZero.
  - apply FOApproxZero.
Qed.

Lemma ranked_kernel_limit s :
  free_omega_qlift eq (kernel s) (FOLub (λ n, ranked_kernel n s)).
Proof.
  eapply FOQLComp with (T := eq) (U := eq)
    (mid := FOLub (λ _, kernel s)).
  - apply FOQLLubConstantR, free_omega_qlift_refl. intro x. reflexivity.
  - apply FOQLCofinal.
    + intro n. apply free_omega_approx_refl. intro x. reflexivity.
    + intro n. apply ranked_kernel_increasing.
    + split.
      * intro n. exists (rank s). unfold ranked_kernel. rewrite Nat.leb_refl.
        apply free_omega_approx_refl. intro x. reflexivity.
      * intro n. exists 0. unfold ranked_kernel. destruct (Nat.leb (rank s) n).
        -- apply free_omega_approx_refl. intro x. reflexivity.
        -- apply FOApproxZero.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

Example state_truncation_recovers_complete_hitting s out :
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega S O kernel s out →
  free_omega_qlift eq out
    (FOLub (λ n, @stable_hitting_approx MF FI
      FreeOmegaObservableSemanticOmega S O (ranked_kernel n) n s)).
Proof.
  intro Hhit. exact (kernel_stable_hitting_diagonal
    (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)
    ranked_kernel_increasing ranked_kernel_limit Hhit).
Qed.

End StateTruncation.

(** There is no global cutoff hiding in the preceding theorem.  Every
    fixed cutoff loses a returning state, so its hitting differs from the
    original.  Increasing the cutoff at the diagonal is essential. *)
Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).

Definition return_index_kernel (s : nat) : MF (stable_target nat nat) :=
  FORet (SHStable s).

Example no_uniform_state_cutoff n :
  ¬ free_omega_qlift eq
    (FOLub (λ fuel, @stable_hitting_approx MF FI
      FreeOmegaObservableSemanticOmega nat nat
      (ranked_kernel return_index_kernel (λ s, s) n) fuel (Datatypes.S n)))
    (FORet (Datatypes.S n)).
Proof.
  intro Hlift.
  assert (Hzero : free_omega_ae (λ _ : nat, False)
    (FOLub (λ fuel, @stable_hitting_approx MF FI
      FreeOmegaObservableSemanticOmega nat nat
      (ranked_kernel return_index_kernel (λ s, s) n) fuel (Datatypes.S n)))).
  { apply FOAELub. intro fuel. unfold stable_hitting_approx, ranked_kernel.
    assert (Hcut : Nat.leb (Datatypes.S n) n = false) by
      (apply Nat.leb_gt; lia).
    rewrite Hcut. apply FOAEZero. }
  pose proof (proj1 (free_omega_qlift_support Hlift) _ Hzero) as Hfalse.
  dependent destruction Hfalse. destruct H as [x [_ Hfalse]]. exact Hfalse.
Qed.

End KernelContinuity.

From mathcomp Require eqtype.
Require PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require PTree.Prob.Backend.EnumQ.Measure PTree.Prob.Backend.SubEnumQ.Measure.
Require PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require PTree.Eq.PrimitiveStableHitting.
Require PTree.Eq.Internal.FreeOmega.KernelCompletion PTree.Eq.Internal.FreeOmega.KernelCongruence.
Module KernelCongruence.
(** Role: supporting compression/scheduling/recovery example; not public theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Import eqtype.
Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Import PTree.Prob.Backend.EnumQ.Measure PTree.Prob.Backend.SubEnumQ.Measure.
Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Import PTree.Eq.PrimitiveStableHitting.
Import PTree.Eq.Internal.FreeOmega.KernelCompletion PTree.Eq.Internal.FreeOmega.KernelCongruence.

Set Implicit Arguments.

(** A nonstructural algebraic rewrite can be made in EVERY kernel round,
    including after arbitrary internal state changes.  This is not a
    bounded-prefix test, and no AST or round bound is assumed. *)
Section ExchangeInEveryRound.
Context {S O : Type}.
Variables mu nu : SubEnumQ bool.
Variable next : S → bool → bool → stable_target S O.
Local Notation MF := (FreeOmega SubEnumQ).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).

Definition first_sample_kernel s : MF (stable_target S O) :=
  FOSample mu (λ x, FOSample nu (λ y, FORet (next s x y))).
Definition swapped_sample_kernel s : MF (stable_target S O) :=
  FOSample nu (λ y, FOSample mu (λ x, FORet (next s x y))).

Lemma sample_exchange_kernel_equal s :
  free_omega_qlift eq (first_sample_kernel s) (swapped_sample_kernel s).
Proof.
  apply free_omega_mixed_exchange_of_product.
  - exact (enumQ_semantic_product_swap (subenumQ_raw mu) (subenumQ_raw nu)).
  - intros x y. apply free_omega_qlift_refl. intro z. reflexivity.
Qed.

Lemma first_sample_kernel_closed s :
  free_omega_ae (kernel_completion_invariant (λ _ : S, True))
    (first_sample_kernel s).
Proof.
  apply FOAESample with (Good := λ _, True); [apply sem_ae_true|].
  intros x _. apply FOAESample with (Good := λ _, True); [apply sem_ae_true|].
  intros y _. apply FOAERet. destruct (next s x y); exact I.
Qed.

Example sample_exchange_preserves_complete_hitting s out1 out2 :
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega
    S O first_sample_kernel s out1 →
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega
    S O swapped_sample_kernel s out2 →
  free_omega_qlift eq out1 out2.
Proof.
  intros Hleft Hright.
  eapply (kernel_stable_hitting_eq
    (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega))
    with (D := λ _, True) (s := s).
  - intros state _. apply first_sample_kernel_closed.
  - intros state _. apply sample_exchange_kernel_equal.
  - exact I.
  - exact Hleft.
  - exact Hright.
Qed.

End ExchangeInEveryRound.

End KernelCongruence.
