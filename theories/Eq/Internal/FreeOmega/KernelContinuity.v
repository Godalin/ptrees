(** Role: Internal execution/scheduling proof infrastructure. Supports hitting adequacy; not an additional behavioral equivalence. *)
Set Universe Polymorphism.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.
From PTree.Eq Require Import PrimitiveStableHitting.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Continuity of complete hitting in an increasing family of kernels.
    States may encode correlated program pairs or their execution history.
    All monotonicity premises are RAW approximation statements: no order
    properness under quotient equality is assumed. *)
Section KernelContinuity.
Context {MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI} {S O : Type}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation target_approx :=
  (@stable_target_approx MF FI FreeOmegaObservableSemanticOmega S O).
Local Notation hit :=
  (@stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega S O).

Lemma kernel_target_approx_mono (left right : S -> MF (stable_target S O)) :
  (forall s, free_omega_approx eq (left s) (right s)) ->
  forall n target, free_omega_approx eq
    (target_approx left n target) (target_approx right n target).
Proof.
  intro Hkernel. intro n. induction n as [|n IH]; intros [o|s].
  - apply FOApproxRet. reflexivity.
  - apply FOApproxZero.
  - apply FOApproxRet. reflexivity.
  - eapply free_omega_approx_bind; [apply Hkernel|].
    intros x y ->. apply IH.
Qed.

Theorem kernel_hitting_approx_mono (left right : S -> MF (stable_target S O)) :
  (forall s, free_omega_approx eq (left s) (right s)) ->
  forall n s, free_omega_approx eq (hit left n s) (hit right n s).
Proof.
  intros Hkernel n s. eapply free_omega_approx_bind; [apply Hkernel|].
  intros x y ->. apply kernel_target_approx_mono. exact Hkernel.
Qed.

Variable kernel : S -> MF (stable_target S O).
Variable chain : nat -> S -> MF (stable_target S O).
Hypothesis chain_increasing : forall n s,
  free_omega_approx eq (chain n s) (chain (Datatypes.S n) s).
Hypothesis kernel_limit : forall s,
  free_omega_qlift eq (kernel s) (FOLub (fun n => chain n s)).

Lemma kernel_hitting_grid_rows n m s :
  free_omega_approx eq (hit (chain m) n s) (hit (chain (Datatypes.S m)) n s).
Proof. apply kernel_hitting_approx_mono. apply chain_increasing. Qed.

Lemma kernel_hitting_grid_columns n m s :
  free_omega_approx eq (hit (chain m) n s) (hit (chain m) (Datatypes.S n) s).
Proof.
  exact (@stable_hitting_increasing MF FI FreeOmegaObservableSemanticOmega
    FreeOmegaObservableSemanticMeasureOrderLaws S O (chain m) s n).
Qed.

Context `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCountAE : @SemanticMeasureCountableAELaws MN NI}.

Lemma kernel_target_approx_limit n target :
  free_omega_qlift eq (target_approx kernel n target)
    (FOLub (fun m => target_approx (chain m) n target)).
Proof.
  induction n as [|n IH] in target |- *; destruct target as [o|s].
  - cbn [stable_target_approx].
    apply FOQLLubConstantR, free_omega_qlift_refl. intro x. reflexivity.
  - cbn [stable_target_approx].
    apply FOQLLubConstantR, free_omega_qlift_refl. intro x. reflexivity.
  - cbn [stable_target_approx].
    apply FOQLLubConstantR, free_omega_qlift_refl. intro x. reflexivity.
  - change (free_omega_qlift eq
      (free_omega_bind (kernel s) (target_approx kernel n))
      (FOLub (fun m => free_omega_bind (chain m s) (target_approx (chain m) n)))).
    apply FOQLBindLub.
    + intro m. apply chain_increasing.
    + intros t m. apply kernel_target_approx_mono. apply chain_increasing.
    + apply kernel_limit.
    + apply IH.
    + apply free_omega_support_lift_bind_diagonal.
      * intro m. apply chain_increasing.
      * intros t m. apply kernel_target_approx_mono. apply chain_increasing.
      * apply free_omega_qlift_support, kernel_limit.
      * intro t. apply free_omega_qlift_support, IH.
Qed.

Theorem kernel_hitting_approx_limit n s :
  free_omega_qlift eq (hit kernel n s) (FOLub (fun m => hit (chain m) n s)).
Proof.
  unfold stable_hitting_approx. apply FOQLBindLub.
  - intro m. apply chain_increasing.
  - intros t m. apply kernel_target_approx_mono. apply chain_increasing.
  - apply kernel_limit.
  - apply kernel_target_approx_limit.
  - apply free_omega_support_lift_bind_diagonal.
    + intro m. apply chain_increasing.
    + intros t m. apply kernel_target_approx_mono. apply chain_increasing.
    + apply free_omega_qlift_support, kernel_limit.
    + intro t. apply free_omega_qlift_support, kernel_target_approx_limit.
Qed.

(** One diagonal suffices for BOTH limits: truncated-kernel accuracy and
    the number of executed residual steps.  This is not a finite bound on
    either the kernel or an execution. *)
Theorem kernel_hitting_limit_diagonal s :
  free_omega_qlift eq (FOLub (fun n => hit kernel n s))
    (FOLub (fun n => hit (chain n) n s)).
Proof.
  eapply FOQLComp with (T := eq) (U := eq)
    (mid := FOLub (fun n => FOLub (fun m => hit (chain m) n s))).
  - apply FOQLLub. intro n. apply kernel_hitting_approx_limit.
  - eapply FOQLDoubleDiagonal with (HAB := eq_refl).
    + intros n m. apply kernel_hitting_grid_rows.
    + intros n m. apply kernel_hitting_grid_columns.
    + intro o. reflexivity.
    + apply free_omega_support_lift_double_diagonal.
      * intros n m. apply kernel_hitting_grid_rows.
      * intros n m. apply kernel_hitting_grid_columns.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

(** Client-facing endpoint for any complete hitting representative. *)
Theorem kernel_stable_hitting_diagonal s out :
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega S O kernel s out ->
  free_omega_qlift eq out (FOLub (fun n => hit (chain n) n s)).
Proof.
  intro Hhit. eapply FOQLComp with (T := eq) (U := eq).
  - exact Hhit.
  - apply kernel_hitting_limit_diagonal.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

Lemma kernel_hitting_diagonal_increasing n s :
  free_omega_approx eq (hit (chain n) n s)
    (hit (chain (Datatypes.S n)) (Datatypes.S n) s).
Proof.
  eapply free_omega_approx_trans.
  - apply kernel_hitting_grid_rows.
  - apply kernel_hitting_grid_columns.
Qed.

(** Adequacy criterion for a projected, possibly correlated execution.
    The remaining obligations concern finite approximants on BOTH sides.
    They are stronger than a completion equation or upper bounds modulo
    equality, and cannot be inferred from either of those alone. *)
Theorem kernel_stable_hitting_diagonal_adequate {S' O'}
    (reference : S' -> MF (stable_target S' O')) (project : O -> O')
    s r out reference_out :
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega S O kernel s out ->
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega S' O'
    reference r reference_out ->
  free_omega_chains_cofinal eq
    (fun n => free_omega_bind (hit (chain n) n s) (fun o => FORet (project o)))
    (fun n => @stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
      S' O' reference n r) ->
  free_omega_qlift eq (free_omega_bind out (fun o => FORet (project o))) reference_out.
Proof.
  intros Hhit Hreference Hcofinal.
  eapply FOQLComp with (T := eq) (U := eq)
    (mid := FOLub (fun n => free_omega_bind (hit (chain n) n s)
      (fun o => FORet (project o)))).
  - change (free_omega_qlift eq (free_omega_bind out (fun o => FORet (project o)))
      (free_omega_bind (FOLub (fun n => hit (chain n) n s))
        (fun o => FORet (project o)))).
    eapply FOQLBind with (T := eq).
    + apply kernel_stable_hitting_diagonal. exact Hhit.
    + intros x y ->. apply FOQLStructural, FOLRet. reflexivity.
  - eapply FOQLComp with (T := eq) (U := eq).
    + apply FOQLCofinal.
      * intro n. eapply free_omega_approx_bind with (R := eq).
        -- apply kernel_hitting_diagonal_increasing.
        -- intros x y ->. apply FOApproxRet. reflexivity.
      * exact (@stable_hitting_increasing MF FI FreeOmegaObservableSemanticOmega
          FreeOmegaObservableSemanticMeasureOrderLaws S' O' reference r).
      * exact Hcofinal.
    + apply FOQLMono with (T := fun x y => y = x).
      * apply FOQLSym. exact Hreference.
      * intros x y Hxy. symmetry. exact Hxy.
    + intros x z [y [-> ->]]. reflexivity.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

End KernelContinuity.
