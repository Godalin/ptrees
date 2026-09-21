(** Role: Internal execution/scheduling proof infrastructure. Supports hitting adequacy; not an additional behavioral equivalence. *)
Set Universe Polymorphism.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import PrimitiveStableHitting.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Completion of a finite execution prefix by a proposed full behavior.
    A one-step completion equation does NOT characterize the least hitting
    solution.  The theorems below establish only the upper-bound direction,
    retaining an explicit representative where the raw order applies. *)
Section KernelCompletion.
Context {MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Context {S O A : Type}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Variable kernel : S -> MF (stable_target S O).
Variable output : O -> A.
Variable tail : S -> MF A.

Definition kernel_completion_resolve (next : S -> MF A)
    (target : stable_target S O) : MF A :=
  match target with
  | SHStable o => FORet (output o)
  | SHInternal s => next s
  end.

Fixpoint kernel_completion (n : nat) (s : S) : MF A :=
  match n with
  | 0 => tail s
  | Datatypes.S m => free_omega_bind (kernel s)
      (kernel_completion_resolve (kernel_completion m))
  end.

Variable D : S -> Prop.
Definition kernel_completion_invariant (target : stable_target S O) : Prop :=
  match target with SHStable _ => True | SHInternal s => D s end.
Hypothesis kernel_closed : forall s, D s ->
  free_omega_ae kernel_completion_invariant (kernel s).
Hypothesis completion_step : forall s, D s ->
  free_omega_qlift eq (kernel_completion 1 s) (tail s).

(** All finite completed prefixes have exactly the proposed full behavior.
    States may encode both programs and their correlated choices. *)
Theorem kernel_completion_eq n s : D s ->
  free_omega_qlift eq (kernel_completion n s) (tail s).
Proof.
  induction n as [|n IH] in s |- *; intro HD.
  - apply free_omega_qlift_refl. intro x. reflexivity.
  - eapply FOQLComp with (T := eq) (U := eq) (mid := kernel_completion 1 s).
    + cbn [kernel_completion]. eapply FOQLBind with
        (T := fun p q => p = q /\ kernel_completion_invariant p).
      * eapply FOQLAERestrict with (T := eq)
          (P := kernel_completion_invariant) (Q := kernel_completion_invariant).
        -- apply free_omega_qlift_refl. intro p. reflexivity.
        -- apply kernel_closed. exact HD.
        -- apply kernel_closed. exact HD.
        -- intros p q [Hp [Hgood _]]. split; assumption.
      * intros p q [<- Hgood]. destruct p as [o|s']; cbn.
        -- apply free_omega_qlift_refl. intro x. reflexivity.
        -- apply IH. exact Hgood.
    + apply completion_step. exact HD.
    + intros x z [y [-> ->]]. reflexivity.
Qed.

(** This bound is raw and requires no semantic equality/order properness.
    Dropping unresolved residuals is below completing them with [tail]. *)
Lemma kernel_target_approx_below_completion n target :
  free_omega_approx eq
    (free_omega_bind
      (@stable_target_approx MF FI FreeOmegaObservableSemanticOmega S O kernel n target)
      (fun o => FORet (output o)))
    (kernel_completion_resolve (kernel_completion n) target).
Proof.
  induction n as [|n IH] in target |- *; destruct target as [o|s].
  - apply FOApproxRet. reflexivity.
  - apply FOApproxZero.
  - apply FOApproxRet. reflexivity.
  - change (free_omega_approx eq
      (free_omega_bind
        (free_omega_bind (kernel s)
          (@stable_target_approx MF FI FreeOmegaObservableSemanticOmega S O kernel n))
        (fun o => FORet (output o)))
      (free_omega_bind (kernel s) (kernel_completion_resolve (kernel_completion n)))).
    rewrite free_omega_bind_assoc.
    eapply free_omega_approx_bind with (R := eq).
    + apply free_omega_approx_refl. intro x. reflexivity.
    + intros x y ->. apply IH.
Qed.

Theorem kernel_hitting_approx_below_completion n s :
  free_omega_approx eq
    (free_omega_bind
      (@stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega S O kernel n s)
      (fun o => FORet (output o)))
    (kernel_completion (Datatypes.S n) s).
Proof.
  unfold stable_hitting_approx. cbn [kernel_completion].
  change (free_omega_approx eq
    (free_omega_bind
      (free_omega_bind (kernel s)
        (@stable_target_approx MF FI FreeOmegaObservableSemanticOmega S O kernel n))
      (fun o => FORet (output o)))
    (free_omega_bind (kernel s) (kernel_completion_resolve (kernel_completion n)))).
  rewrite free_omega_bind_assoc.
  eapply free_omega_approx_bind with (R := eq).
  - apply free_omega_approx_refl. intro x. reflexivity.
  - intros x y ->. apply kernel_target_approx_below_completion.
Qed.

(** A representative-sensitive upper bound for the COMPLETE projected
    hitting.  We do not claim raw order against [tail s], nor equality of
    the two limits.  The completion chain need not be raw-increasing: its
    quotient equality below uses pointwise equality, not cofinality. *)
Theorem kernel_hitting_limit_upper s : D s ->
  exists upper,
    free_omega_approx eq
      (free_omega_bind
        (FOLub (fun n => @stable_hitting_approx MF FI
          FreeOmegaObservableSemanticOmega S O kernel n s))
        (fun o => FORet (output o))) upper /\
    free_omega_qlift eq upper (tail s).
Proof.
  intro HD. exists (FOLub (fun n => kernel_completion (Datatypes.S n) s)). split.
  - apply FOApproxLub. intro n. apply kernel_hitting_approx_below_completion.
  - eapply FOQLComp with (T := eq) (U := eq)
      (mid := FOLub (fun _ => tail s)).
    + apply FOQLLub. intro n. apply kernel_completion_eq. exact HD.
    + apply FOQLSym. apply FOQLLubConstantR.
      apply free_omega_qlift_refl. intro x. reflexivity.
    + intros x z [y [-> ->]]. reflexivity.
Qed.

End KernelCompletion.
