Set Universe Polymorphism.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure FreeOmegaNative.
From PTree.Eq Require Import FiniteInternal FiniteInternalPlan PFiniteResidual.
From PTree.Eq.FreeOmega Require Import FiniteInternalJoint.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Reified plans retain actual Tau/Prob histories, while the native
    sample type stays small.  Their normalization preserves the complete
    distribution, not merely its support.  A joint online scheduler and
    its adequacy still require additional proof. *)
Section NativeCompression.
Context {E MN : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NO : @SemanticOmega MN NI}
  `{ND : @SemanticMeasureDiracAELaws MN NI}
  `{NBAE : @SemanticMeasureBindAEExactLaws MN NI} {R : Type}.
Local Notation tree := (ptree E MN R).
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).

Definition internal_plan_native {t} (p : @finite_internal_plan E MN R t) :
    free_omega_native_presentation MN tree :=
  {| native_sample_type := internal_plan_path p;
     native_sample_measure := internal_plan_measure p;
     native_sample_value := internal_plan_residual p |}.

Lemma internal_plan_native_eq t (p : @finite_internal_plan E MN R t) :
  free_omega_qlift eq
    (@internal_plan_frontier E MN R MF FI FreeOmegaMixedMeasure t p)
    (free_omega_native (internal_plan_native p)).
Proof.
  induction p as [t|t next IH|X mu k next IH].
  - apply FOQLMono with (T := fun x y => y = x).
    + apply FOQLSym, FOQLSampleRetL.
      * apply sem_ae_ret_iff.
      * apply FOQLStructural, FOLRet. reflexivity.
    + intros x y Hyx. symmetry. exact Hyx.
  - exact IH.
  - cbn [internal_plan_frontier].
    eapply FOQLComp with (T := eq) (U := eq)
      (mid := FOSample mu (fun x => free_omega_native (internal_plan_native (next x)))).
    + eapply FOQLSample with (T := eq).
      * apply sem_lift_refl. intro x. reflexivity.
      * intros x y ->. apply IH.
    + unfold free_omega_native, internal_plan_native. cbn.
      exact (@free_omega_sample_sigma MN NI NC NO ND NBAE X
        (fun x => internal_plan_path (next x)) tree mu
        (fun x => internal_plan_measure (next x))
        (fun x y => FORet (internal_plan_residual (next x) y))).
    + intros x z [y [-> ->]]. reflexivity.
Qed.

Theorem finite_internal_native_plan t out :
  @finite_internal E MN MF FI FreeOmegaMixedMeasure R t out ->
  exists p : @finite_internal_plan E MN R t,
    @internal_plan_frontier E MN R MF FI FreeOmegaMixedMeasure t p = out /\
    free_omega_qlift eq out (free_omega_native (internal_plan_native p)).
Proof.
  intro Hcut. destruct (finite_internal_plan_exists Hcut) as [p Hp].
  exists p. split; [exact Hp|]. rewrite <- Hp. apply internal_plan_native_eq.
Qed.

Theorem finite_internal_native_presentation t out :
  @finite_internal E MN MF FI FreeOmegaMixedMeasure R t out ->
  exists p : free_omega_native_presentation MN tree,
    free_omega_qlift eq out (free_omega_native p).
Proof.
  intro Hcut. destruct (finite_internal_native_plan Hcut) as [p [_ Hp]].
  exists (internal_plan_native p). exact Hp.
Qed.

Definition internal_guard_native (t : tree) :
    free_omega_native_presentation MN
      (PrimitiveStableHitting.stable_target tree (UnifiedFrontier.stable_head E MN R)) :=
  match observe t with
  | RetF r => {| native_sample_type := unit; native_sample_measure := sem_ret tt;
      native_sample_value := fun _ => PrimitiveStableHitting.SHStable (UnifiedFrontier.FHRet r) |}
  | TauF u => {| native_sample_type := unit; native_sample_measure := sem_ret tt;
      native_sample_value := fun _ => PrimitiveStableHitting.SHInternal u |}
  | VisF _ e k => {| native_sample_type := unit; native_sample_measure := sem_ret tt;
      native_sample_value := fun _ => PrimitiveStableHitting.SHStable (UnifiedFrontier.FHVis e k) |}
  | ProbF _ mu k => {| native_sample_type := _; native_sample_measure := mu;
      native_sample_value := fun x => PrimitiveStableHitting.SHInternal (k x) |}
  end.

Lemma internal_guard_native_eq t :
  free_omega_qlift eq (@finite_internal_guard_transition E MN R t)
    (free_omega_native (internal_guard_native t)).
Proof.
  unfold finite_internal_guard_transition, internal_guard_native.
  destruct (observe t) as [r|u|X e k|X mu k].
  all: try solve [apply free_omega_qlift_refl; intro z; reflexivity].
  all: apply FOQLMono with (T := fun x y => y = x).
  all: try solve [intros x y Hyx; symmetry; exact Hyx].
  all: apply FOQLSym, FOQLSampleRetL; [apply sem_ae_ret_iff|].
  all: apply FOQLStructural, FOLRet; reflexivity.
Qed.

Lemma finite_internal_guard_native_presentation t :
  exists p, free_omega_qlift eq
    (@finite_internal_guard_transition E MN R t) (free_omega_native p).
Proof. exists (internal_guard_native t). apply internal_guard_native_eq. Qed.

Definition internal_plan_round_native {t} (p : @finite_internal_plan E MN R t) :=
  free_omega_native_bind (internal_plan_native p) internal_guard_native.

Lemma internal_plan_round_native_eq t (p : @finite_internal_plan E MN R t) :
  free_omega_qlift eq
    (free_omega_bind (@internal_plan_frontier E MN R MF FI FreeOmegaMixedMeasure t p)
      finite_internal_guard_transition)
    (free_omega_native (internal_plan_round_native p)).
Proof.
  eapply FOQLComp with (T := eq) (U := eq).
  - eapply FOQLBind with (T := eq); [apply internal_plan_native_eq|].
    intros x y ->. apply internal_guard_native_eq.
  - apply free_omega_native_bind_eq.
  - intros x z [y [-> ->]]. reflexivity.
Qed.

(** The full compression-plus-guard round is native-presentable as well.
    This includes guard sampling and high-universe Ret/Vis stable heads. *)
Theorem finite_internal_round_native_presentation t out :
  @finite_internal E MN MF FI FreeOmegaMixedMeasure R t out ->
  exists p, free_omega_qlift eq
    (free_omega_bind out finite_internal_guard_transition) (free_omega_native p).
Proof.
  intro Hcut. destruct (finite_internal_plan_exists Hcut) as [p Hp].
  exists (internal_plan_round_native p). rewrite <- Hp.
  apply internal_plan_round_native_eq.
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
  exists (p : @finite_internal_plan E MN A t) (q : @finite_internal_plan E MN B u),
    free_omega_qlift (pfinite_guard RR sim)
      (free_omega_native (internal_plan_native p))
      (free_omega_native (internal_plan_native q)).
Proof.
  split.
  - intros [t' u' out1 out2 Hcut1 Hcut2 Hlift].
    destruct (finite_internal_native_plan Hcut1) as [p [_ Hp]].
    destruct (finite_internal_native_plan Hcut2) as [q [_ Hq]].
    exists p, q.
    change (@sem_lift MF FI _ _ (pfinite_guard RR sim)
      (free_omega_native (internal_plan_native p))
      (free_omega_native (internal_plan_native q))).
    eapply sem_lift_proper_l; [exact Hp|].
    eapply sem_lift_proper_r; [exact Hq|exact Hlift].
  - intros [p [q Hlift]].
    eapply PFiniteResidualStep.
    + exact (@internal_plan_frontier_valid E MN A MF FI FreeOmegaMixedMeasure t p).
    + exact (@internal_plan_frontier_valid E MN B MF FI FreeOmegaMixedMeasure u q).
    + eapply (@sem_lift_proper_l MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
      * apply (@sem_eq_sym MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
        apply internal_plan_native_eq.
      * eapply (@sem_lift_proper_r MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
        -- apply (@sem_eq_sym MF FI FreeOmegaObservableSemanticMeasureCoreLaws).
           apply internal_plan_native_eq.
        -- exact Hlift.
Qed.
End NativeCandidate.
