Set Universe Polymorphism.
From Coq Require Import Logic.ClassicalChoice.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure FreeOmegaNative.
From PTree.Eq Require Import FiniteInternal PFiniteResidual.
From PTree.Eq.FreeOmega Require Import FiniteInternalJoint.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Every well-founded internal compression can be presented as ONE native
    sample decoded to its residual tree.  The sampled type is small; the
    residual tree need not be.  Dependent sigma samples combine complete
    branch distributions, not just selected supported results.  This is a
    distribution-presentation certificate, not yet a primitive execution
    trace/schedule certificate.  There is no fuel, uniform branch-depth
    bound, or AST premise here. *)
Section NativeCompression.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI} {R : Type}.
Local Notation tree := (ptree E MN R).
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).

Theorem finite_internal_native_presentation t out :
  @finite_internal E MN MF FI FreeOmegaMixedMeasure R t out ->
  exists p : free_omega_native_presentation MN tree,
    free_omega_qlift eq out (free_omega_native p).
Proof.
  intro Hcut. induction Hcut as [t|t out Hcut IH|X mu k out Hcut IH].
  - apply free_omega_ret_native_presentation.
  - exact IH.
  - destruct (choice _ IH) as [p Hp].
    exists {| native_sample_type := {x : X & native_sample_type (p x)};
      native_sample_measure := sem_bind mu (fun x =>
        sem_bind (native_sample_measure (p x))
          (fun y => sem_ret (existT (fun x => native_sample_type (p x)) x y)));
      native_sample_value := fun z =>
        native_sample_value (p (projT1 z)) (projT2 z) |}.
    eapply FOQLComp with (T := eq) (U := eq)
      (mid := FOSample mu (fun x => free_omega_native (p x))).
    + eapply FOQLSample with (T := eq).
      * apply sem_lift_refl. intro x. reflexivity.
      * intros x y ->. apply Hp.
    + unfold free_omega_native. cbn.
      exact (@free_omega_sample_sigma MN NI NC NO ND NBAE X
        (fun x => native_sample_type (p x)) tree mu
        (fun x => native_sample_measure (p x))
        (fun x y => FORet (native_sample_value (p x) y))).
    + intros x z [y [-> ->]]. reflexivity.
Qed.

Lemma finite_internal_guard_native_presentation t :
  exists p, free_omega_qlift eq
    (@finite_internal_guard_transition E MN R t) (free_omega_native p).
Proof.
  unfold finite_internal_guard_transition.
  destruct (observe t) as [r|u|X e k|X mu k].
  - apply free_omega_ret_native_presentation.
  - apply free_omega_ret_native_presentation.
  - apply free_omega_ret_native_presentation.
  - exists {| native_sample_type := X; native_sample_measure := mu;
      native_sample_value := fun x => PrimitiveStableHitting.SHInternal (k x) |}.
    apply free_omega_qlift_refl. intro z. reflexivity.
Qed.

(** The full compression-plus-guard round is native-presentable as well.
    This includes guard sampling and high-universe Ret/Vis stable heads. *)
Theorem finite_internal_round_native_presentation t out :
  @finite_internal E MN MF FI FreeOmegaMixedMeasure R t out ->
  exists p, free_omega_qlift eq
    (free_omega_bind out finite_internal_guard_transition) (free_omega_native p).
Proof.
  intro Hcut. destruct (finite_internal_native_presentation Hcut) as [p Hp].
  eapply free_omega_native_bind_presentation; [exact Hp|].
  intro u. apply finite_internal_guard_native_presentation.
Qed.
End NativeCompression.

(** Exact reduction of a candidate round to native SAMPLE PRESENTATIONS.
    The coupling here remains the full FreeOmega quotient lifting.  Do not
    replace it by a native path coupling without proving the required
    pullback/inversion theorem: normalization alone does not give that. *)
Section NativeCandidate.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI} {A B : Type}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Variable RR : A -> B -> Prop.
Variable sim : ptree E MN A -> ptree E MN B -> Prop.

Theorem pfinite_residual_native_characterization t u :
  @pfinite_residualF E MN MF NI FI FreeOmegaMixedMeasure A B RR sim t u <->
  exists out1 out2
    (p : free_omega_native_presentation MN (ptree E MN A))
    (q : free_omega_native_presentation MN (ptree E MN B)),
    @finite_internal E MN MF FI FreeOmegaMixedMeasure A t out1 /\
    @finite_internal E MN MF FI FreeOmegaMixedMeasure B u out2 /\
    free_omega_qlift eq out1 (free_omega_native p) /\
    free_omega_qlift eq out2 (free_omega_native q) /\
    free_omega_qlift (pfinite_guard RR sim) (free_omega_native p) (free_omega_native q).
Proof.
  split.
  - intros [t' u' out1 out2 Hcut1 Hcut2 Hlift].
    destruct (finite_internal_native_presentation Hcut1) as [p Hp].
    destruct (finite_internal_native_presentation Hcut2) as [q Hq].
    exists out1, out2, p, q.
    split; [exact Hcut1|]. split; [exact Hcut2|].
    split; [exact Hp|]. split; [exact Hq|].
    change (@sem_lift MF FI _ _ (pfinite_guard RR sim)
      (free_omega_native p) (free_omega_native q)).
    eapply sem_lift_proper_l; [exact Hp|].
    eapply sem_lift_proper_r; [exact Hq|exact Hlift].
  - intros [out1 [out2 [p [q [Hcut1 [Hcut2 [Hp [Hq Hlift]]]]]]]].
    eapply PFiniteResidualStep; [exact Hcut1|exact Hcut2|].
    eapply (@sem_lift_proper_l MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
    + apply (@sem_eq_sym MF FI FreeOmegaObservableSemanticMeasureCoreLaws). exact Hp.
    + eapply (@sem_lift_proper_r MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
      * apply (@sem_eq_sym MF FI FreeOmegaObservableSemanticMeasureCoreLaws). exact Hq.
      * exact Hlift.
Qed.
End NativeCandidate.
