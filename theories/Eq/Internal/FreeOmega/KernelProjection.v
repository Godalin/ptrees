(** Role: Internal execution/scheduling proof infrastructure. Supports hitting adequacy; not an additional behavioral equivalence. *)
Set Universe Polymorphism.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure FreeOmegaCoupling.
From PTree.Eq Require Import PrimitiveStableHitting.
From PTree.Eq.Internal.FreeOmega Require Import KernelCompletion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A quotient graph marginal may forget random state.  Unlike a
    structural graph, it need not retain the source sampling shape.
    Iterating such a kernel still commutes with projection whenever its
    projected transition depends only on the projected state. *)
Section Projection.
Context {MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI} {S T O P : Type}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Variable source : S -> MF (stable_target S O).
Variable target : T -> MF (stable_target T P).
Variable state_projection : S -> T.
Variable output_projection : O -> P.
Variable D : S -> Prop.

Definition kernel_target_projection (z : stable_target S O) : stable_target T P :=
  match z with
  | SHStable o => SHStable (output_projection o)
  | SHInternal s => SHInternal (state_projection s)
  end.

Hypothesis source_closed : forall s, D s ->
  free_omega_ae (kernel_completion_invariant D) (source s).
Hypothesis kernel_marginal : forall s, D s ->
  free_omega_qlift (fun z w => kernel_target_projection z = w)
    (source s) (target (state_projection s)).

Lemma kernel_projection_supported s : D s ->
  free_omega_qlift (fun z w => kernel_target_projection z = w /\
    kernel_completion_invariant D z) (source s) (target (state_projection s)).
Proof.
  intro HD. eapply FOQLAERestrict with
    (T := fun z w => kernel_target_projection z = w)
    (P := kernel_completion_invariant D) (Q := fun _ => True).
  - apply kernel_marginal. exact HD.
  - apply source_closed. exact HD.
  - apply (@sem_ae_true MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
  - intros z w [Heq [Hgood _]]. split; assumption.
Qed.

Lemma kernel_target_approx_projection n z : kernel_completion_invariant D z ->
  free_omega_qlift (fun o p => output_projection o = p)
    (@stable_target_approx MF FI FreeOmegaObservableSemanticOmega S O source n z)
    (@stable_target_approx MF FI FreeOmegaObservableSemanticOmega T P target n
      (kernel_target_projection z)).
Proof.
  induction n as [|n IH] in z |- *; intros HD; destruct z as [o|s].
  - apply FOQLStructural, FOLRet. reflexivity.
  - apply FOQLStructural, FOLZero.
  - apply FOQLStructural, FOLRet. reflexivity.
  - eapply FOQLBind; [apply kernel_projection_supported; exact HD|].
    intros x y [<- Hx]. apply IH. exact Hx.
Qed.

Theorem kernel_hitting_approx_projection n s : D s ->
  free_omega_qlift (fun o p => output_projection o = p)
    (@stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega S O source n s)
    (@stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega T P target n
      (state_projection s)).
Proof.
  intro HD. eapply FOQLBind; [apply kernel_projection_supported; exact HD|].
  intros z w [<- Hz]. apply kernel_target_approx_projection. exact Hz.
Qed.

Theorem kernel_hitting_limit_projection s : D s ->
  free_omega_qlift (fun o p => output_projection o = p)
    (FOLub (fun n => @stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
      S O source n s))
    (FOLub (fun n => @stable_hitting_approx MF FI FreeOmegaObservableSemanticOmega
      T P target n (state_projection s))).
Proof.
  intro HD. apply FOQLLub. intro n. apply kernel_hitting_approx_projection. exact HD.
Qed.

Theorem kernel_stable_hitting_projection s out1 out2 : D s ->
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega S O source s out1 ->
  @stable_hitting MF FI FreeOmegaObservableSemanticOmega T P target
    (state_projection s) out2 ->
  free_omega_qlift eq
    (free_omega_bind out1 (fun o => FORet (output_projection o))) out2.
Proof.
  intros HD Hleft Hright. apply free_omega_qlift_map_left.
  eapply FOQLComp with (T := eq) (U := fun o p => output_projection o = p).
  - exact Hleft.
  - eapply FOQLComp with (T := fun o p => output_projection o = p) (U := eq).
    + apply kernel_hitting_limit_projection. exact HD.
    + apply FOQLMono with (T := fun x y => y = x).
      * apply FOQLSym. exact Hright.
      * intros x y Heq. symmetry. exact Heq.
    + intros o p [q [Hq ->]]. exact Hq.
  - intros o p [q [-> Hq]]. exact Hq.
Qed.

End Projection.
