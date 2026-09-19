Set Universe Polymorphism.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure.
From PTree.Eq Require Import PrimitiveStableHitting.
From PTree.Eq.FreeOmega Require Import KernelCompletion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Changing the representation of a primitive/macro kernel does not
    change its hitting semantics.  This theorem uses quotient coupling,
    not transport of raw approximation order across quotient equality. *)
Section KernelCongruence.
Context {MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI} {S O : Type}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Variable left right : S -> MF (stable_target S O).
Variable D : S -> Prop.
Hypothesis left_closed : forall s, D s ->
  free_omega_ae (kernel_completion_invariant D) (left s).
Hypothesis kernels_equal : forall s, D s -> free_omega_qlift eq (left s) (right s).

Lemma kernel_equality_supported s : D s ->
  free_omega_qlift
    (fun p q => p = q /\ kernel_completion_invariant D p) (left s) (right s).
Proof.
  intro HD. eapply FOQLAERestrict with (T := eq)
    (P := kernel_completion_invariant D) (Q := fun _ => True).
  - apply kernels_equal. exact HD.
  - apply left_closed. exact HD.
  - apply (@sem_ae_true MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
  - intros p q [Hp [Hgood _]]. split; assumption.
Qed.

Lemma kernel_target_approx_eq n target : kernel_completion_invariant D target ->
  free_omega_qlift eq
    (@stable_target_approx MF FI FreeOmegaObservableSemanticOmega S O left n target)
    (@stable_target_approx MF FI FreeOmegaObservableSemanticOmega S O right n target).
Proof.
  induction n as [|n IH] in target |- *; intros HD; destruct target as [o|s].
  - apply free_omega_qlift_refl. intro x. reflexivity.
  - apply FOQLStructural, FOLZero.
  - apply free_omega_qlift_refl. intro x. reflexivity.
  - eapply FOQLBind; [apply kernel_equality_supported; exact HD|].
    intros p q [<- Hgood]. apply IH. exact Hgood.
Qed.

Theorem kernel_hitting_approx_eq n s : D s ->
  free_omega_qlift eq
    (@stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega S O left n s)
    (@stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega S O right n s).
Proof.
  intro HD. eapply FOQLBind; [apply kernel_equality_supported; exact HD|].
  intros p q [<- Hgood]. apply kernel_target_approx_eq. exact Hgood.
Qed.

Theorem kernel_hitting_limit_eq s : D s ->
  free_omega_qlift eq
    (FOLub (fun n => @stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
      S O left n s))
    (FOLub (fun n => @stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
      S O right n s)).
Proof.
  intro HD. apply FOQLLub. intro n. apply kernel_hitting_approx_eq. exact HD.
Qed.

(** The result applies to any complete hitting representatives, not only
    the canonical formal Lub used in the finite approximation proof. *)
Theorem kernel_stable_hitting_eq s out1 out2 : D s ->
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega S O left s out1 ->
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega S O right s out2 ->
  free_omega_qlift eq out1 out2.
Proof.
  intros HD Hleft Hright.
  eapply FOQLComp with (T := eq) (U := eq); [exact Hleft| |].
  - eapply FOQLComp with (T := eq) (U := eq).
    + apply kernel_hitting_limit_eq. exact HD.
    + apply FOQLMono with (T := fun x y => y = x).
      * apply FOQLSym. exact Hright.
      * intros x y Hxy. symmetry. exact Hxy.
    + intros x z [y [-> ->]]. reflexivity.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

End KernelCongruence.
