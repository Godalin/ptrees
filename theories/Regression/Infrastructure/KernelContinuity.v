Set Universe Polymorphism.
From Coq Require Import Arith.PeanoNat Lia Program.Equality.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum FreeOmegaMeasure.
From PTree.Eq Require Import PrimitiveStableHitting.
From PTree.Eq.FreeOmega Require Import KernelContinuity.

Set Implicit Arguments.

(** Truncate by a rank of the CURRENT state, not by a bound on all states
    an execution can visit.  The full kernel may be probabilistic, eventful,
    internally divergent, or have infinitely many reachable states. *)
Section StateTruncation.
Context {S O : Type}.
Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).
Variable kernel : S -> MF (stable_target S O).
Variable rank : S -> nat.

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
  free_omega_qlift eq (kernel s) (FOLub (fun n => ranked_kernel n s)).
Proof.
  eapply FOQLComp with (T := eq) (U := eq)
    (mid := FOLub (fun _ => kernel s)).
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
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega S O kernel s out ->
  free_omega_qlift eq out
    (FOLub (fun n => @stable_hitting_approx MF FI
      FreeOmegaObservableSemanticOmega S O (ranked_kernel n) n s)).
Proof.
  intro Hhit. exact (kernel_stable_hitting_diagonal
    (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)
    ranked_kernel_increasing ranked_kernel_limit Hhit).
Qed.

End StateTruncation.

(** There is no global cutoff hiding in the preceding theorem.  Every
    fixed cutoff loses a returning state, so its hitting differs from the
    original.  Increasing the cutoff at the diagonal is essential. *)
Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).

Definition return_index_kernel (s : nat) : MF (stable_target nat nat) :=
  FORet (SHStable s).

Example no_uniform_state_cutoff n :
  ~ free_omega_qlift eq
    (FOLub (fun fuel => @stable_hitting_approx MF FI
      FreeOmegaObservableSemanticOmega nat nat
      (ranked_kernel return_index_kernel (fun s => s) n) fuel (Datatypes.S n)))
    (FORet (Datatypes.S n)).
Proof.
  intro Hlift.
  assert (Hzero : free_omega_ae (fun _ : nat => False)
    (FOLub (fun fuel => @stable_hitting_approx MF FI
      FreeOmegaObservableSemanticOmega nat nat
      (ranked_kernel return_index_kernel (fun s => s) n) fuel (Datatypes.S n)))).
  { apply FOAELub. intro fuel. unfold stable_hitting_approx, ranked_kernel.
    assert (Hcut : Nat.leb (Datatypes.S n) n = false) by
      (apply Nat.leb_gt; lia).
    rewrite Hcut. apply FOAEZero. }
  pose proof (proj1 (free_omega_qlift_support Hlift) _ Hzero) as Hfalse.
  dependent destruction Hfalse. destruct H as [x [_ Hfalse]]. exact Hfalse.
Qed.
