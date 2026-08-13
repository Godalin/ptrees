Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program.Equality.

From Coinduction Require Import all.
From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import FrontierLift MeasureIteration.
From PTree.Eq Require Import PWeakAbstract PWeakUnbounded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A distribution-valued probabilistic transition system induced by a
    [ptree].  A transition target is either a stable observable head or a
    residual tree which must perform more internal computation. *)
Variant ppts_target (E : Type -> Type) (M : Type -> Type) (R : Type) :=
  | PPTSStable (h : aphead E M R)
  | PPTSInternal (t : ptree E M R).

Arguments PPTSStable {E M R} _.
Arguments PPTSInternal {E M R} _.

Section DistributionValuedPTS.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M}.

(** The primitive distribution-valued transition.  [Ret]/[Vis] enter an
    absorbing stable state, [Tau] has one deterministic residual state, and
    [Prob] distributes over its residual continuations. *)
Inductive ppts_step {R} :
    ptree' E M R -> M (ppts_target E M R) -> Prop :=
  | PPTSStepReturn r :
      ppts_step (RetF r) (meas_ret (PPTSStable (APHRet r)))
  | PPTSStepVisible {X} (e : E X) k :
      ppts_step (VisF e k) (meas_ret (PPTSStable (APHVis e k)))
  | PPTSStepTau t :
      ppts_step (TauF t) (meas_ret (PPTSInternal t))
  | PPTSStepProb {X} (mu : M X) k :
      ppts_step (ProbF mu k)
        (meas_bind mu (fun x => meas_ret (PPTSInternal (k x)))).

(** Finite weak transition of the induced PTS.  It repeatedly resolves
    internal target states and stops at the first stable heads.  Unlike
    [apfrontier], this presentation factors each source node through an
    explicit distribution-valued primitive transition. *)
Inductive ppts_weak {R} :
    ptree' E M R -> M (aphead E M R) -> Prop :=
  | PPTSWeakReturn r targets :
      ppts_step (RetF r) targets ->
      ppts_weak (RetF r) (meas_ret (APHRet r))
  | PPTSWeakVisible {X} (e : E X) k targets :
      ppts_step (VisF e k) targets ->
      ppts_weak (VisF e k) (meas_ret (APHVis e k))
  | PPTSWeakTau t targets hs :
      ppts_step (TauF t) targets ->
      ppts_weak (observe t) hs ->
      ppts_weak (TauF t) hs
  | PPTSWeakProb {X} (mu : M X) k targets
      (front : X -> M (aphead E M R)) (Good : X -> Prop) :
      ppts_step (ProbF mu k) targets ->
      meas_ae mu Good ->
      (forall x, Good x -> ppts_weak (observe (k x)) (front x)) ->
      ppts_weak (ProbF mu k) (meas_bind mu front).

End DistributionValuedPTS.

Section FiniteCorrespondence.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}
  `{ML : @MeasureLaws M MI MC} `{MB : @MeasureBindLaws M MI}
  `{MM : @MeasureMonadLaws M MI}
  `{MG : @MeasureCongruenceLaws M MI}.

(** Every operational finite frontier is a weak transition of the induced
    distribution-valued PTS, up to extensional measure equality. *)
Theorem apfrontier_to_ppts_weak {R}
    (ot : ptree' E M R) hs :
  apfrontier ot hs -> ppts_weak ot hs.
Proof.
  intro Hf. induction Hf.
  - apply PPTSWeakReturn with
        (targets := meas_ret (PPTSStable (APHRet r))). constructor.
  - apply PPTSWeakVisible with
        (targets := meas_ret (PPTSStable (APHVis e k))). constructor.
  - apply PPTSWeakTau with
        (targets := meas_ret (PPTSInternal t)); [constructor|exact IHHf].
  - apply PPTSWeakProb with
        (targets := meas_bind mu
          (fun x => meas_ret (PPTSInternal (k x))))
        (Good := Good).
    + constructor.
    + exact H.
    + exact H1.
Qed.

(** Conversely, erasing the explicit primitive-step witnesses recovers the
    original finite frontier derivation. *)
Theorem ppts_weak_to_apfrontier {R}
    (ot : ptree' E M R) hs :
  ppts_weak ot hs -> apfrontier ot hs.
Proof.
  intro Hw. induction Hw.
  - constructor.
  - constructor.
  - exact (APFTau IHHw).
  - exact (APFProb H0 H2).
Qed.

Theorem ppts_weak_iff_apfrontier {R}
    (ot : ptree' E M R) hs :
  ppts_weak ot hs <-> apfrontier ot hs.
Proof.
  split; [apply ppts_weak_to_apfrontier|apply apfrontier_to_ppts_weak].
Qed.

Definition ppts_weak_sem {R} (ot : ptree' E M R)
    (hs : M (aphead E M R)) : Prop :=
  exists hs0, ppts_weak ot hs0 /\ meas_eq hs0 hs.

Theorem ppts_weak_sem_iff_apfrontier_sem {R}
    (ot : ptree' E M R) hs :
  ppts_weak_sem ot hs <-> apfrontier_sem ot hs.
Proof.
  split; intros [hs0 [Hweak Heq]]; exists hs0; split; try exact Heq.
  - exact (ppts_weak_to_apfrontier Hweak).
  - exact (apfrontier_to_ppts_weak Hweak).
Qed.

Theorem ppts_weak_sem_unique {R}
    (ot : ptree' E M R) hs1 hs2 :
  ppts_weak_sem ot hs1 -> ppts_weak_sem ot hs2 -> meas_eq hs1 hs2.
Proof.
  rewrite !ppts_weak_sem_iff_apfrontier_sem.
  exact (apfrontier_sem_unique (ot := ot) (hs1 := hs1) (hs2 := hs2)).
Qed.

End FiniteCorrespondence.

Section ASTWeakTransitions.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M}
  `{MO : @MeasureOmegaInterface M MI}.

(** AST weak transitions of the induced PTS.  Finite internal closure is
    delegated to [ppts_weak]; unbounded loops are justified by the same
    absorbing distribution iteration and total-mass condition used by the
    measure semantics. *)
Inductive ppts_ast_weak {R} :
    ptree' E M R -> M (aphead E M R) -> Prop :=
  | PPTSAFinite ot hs :
      ppts_weak ot hs -> ppts_ast_weak ot hs
  | PPTSATau t hs :
      ppts_ast_weak (observe t) hs -> ppts_ast_weak (TauF t) hs
  | PPTSAProb {X} (mu : M X) k
      (front : X -> M (aphead E M R)) (Good : X -> Prop) :
      meas_ae mu Good ->
      (forall x, Good x -> ppts_ast_weak (observe (k x)) (front x)) ->
      ppts_ast_weak (ProbF mu k) (meas_bind mu front)
  | PPTSAIter {I}
      (step : I -> ptree E M (I + R))
      (transition : I -> M (I + R)) i out :
      (forall j, ppts_weak (observe (step j))
        (meas_bind (transition j)
          (fun next => meas_ret (APHRet next)))) ->
      meas_iter transition i out -> meas_total out ->
      ppts_ast_weak (observe (PTree.iter step i))
        (meas_bind out (fun r => meas_ret (APHRet r)))
  | PPTSABind {A} (t : ptree E M A) (k : A -> ptree E M R)
      hs (front : A -> M (aphead E M R)) :
      ppts_ast_weak (observe t) hs ->
      (forall a, ppts_ast_weak (observe (k a)) (front a)) ->
      ppts_ast_weak (observe (PTree.bind t k))
        (meas_bind hs (aphead_bind_front k front))
  | PPTSANestedIter {I}
      (step : I -> ptree E M (I + R))
      (transition : I -> M (I + R)) i out :
      (forall j, ppts_ast_weak (observe (step j))
        (meas_bind (transition j)
          (fun next => meas_ret (APHRet next)))) ->
      meas_iter transition i out -> meas_total out ->
      ppts_ast_weak (observe (PTree.iter step i))
        (meas_bind out (fun r => meas_ret (APHRet r))).

End ASTWeakTransitions.

Section ASTCorrespondence.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}
  `{ML : @MeasureLaws M MI MC} `{MB : @MeasureBindLaws M MI}
  `{MM : @MeasureMonadLaws M MI}
  `{MG : @MeasureCongruenceLaws M MI}
  `{MO : @MeasureOmegaInterface M MI}.

Theorem aufrontier_to_ppts_ast_weak {R}
    (ot : ptree' E M R) hs :
  aufrontier ot hs -> ppts_ast_weak ot hs.
Proof.
  revert R ot hs. fix IH 4. intros R0 ot hs Hf. destruct Hf.
  - exact (PPTSAFinite (apfrontier_to_ppts_weak H)).
  - exact (PPTSATau (IH _ _ _ Hf)).
  - apply PPTSAProb with (Good := Good); [exact H|].
    intros x Hx. exact (IH _ _ _ (H0 x Hx)).
  - eapply PPTSAIter; [|exact H0|exact H1].
    intro j. exact (apfrontier_to_ppts_weak (H j)).
  - apply PPTSABind.
    + exact (IH _ _ _ Hf).
    + intros a. match goal with
      | Hk : forall x, aufrontier _ _ |- _ => exact (IH _ _ _ (Hk a))
      end.
  - apply PPTSANestedIter with (transition := transition).
    + intros j. exact (IH _ _ _ (H j)).
    + exact H0.
    + exact H1.
Qed.

Theorem ppts_ast_weak_to_aufrontier {R}
    (ot : ptree' E M R) hs :
  ppts_ast_weak ot hs -> aufrontier ot hs.
Proof.
  revert R ot hs. fix IH 4. intros R0 ot hs Hw. destruct Hw.
  - exact (AUFFinite (ppts_weak_to_apfrontier H)).
  - exact (AUFTau (IH _ _ _ Hw)).
  - apply AUFProb with (Good := Good); [exact H|].
    intros x Hx. exact (IH _ _ _ (H0 x Hx)).
  - eapply AUFIter; [|exact H0|exact H1].
    intro j. exact (ppts_weak_to_apfrontier (H j)).
  - apply AUFBind.
    + exact (IH _ _ _ Hw).
    + intros a. match goal with
      | Hk : forall x, ppts_ast_weak _ _ |- _ => exact (IH _ _ _ (Hk a))
      end.
  - apply AUFNestedIter with (transition := transition).
    + intros j. exact (IH _ _ _ (H j)).
    + exact H0.
    + exact H1.
Qed.

Theorem ppts_ast_weak_iff_aufrontier {R}
    (ot : ptree' E M R) hs :
  ppts_ast_weak ot hs <-> aufrontier ot hs.
Proof.
  split; [apply ppts_ast_weak_to_aufrontier|
          apply aufrontier_to_ppts_ast_weak].
Qed.

End ASTCorrespondence.

Section PTSBisimulation.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}
  `{MO : @MeasureOmegaInterface M MI}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

(** Independent weak probabilistic bisimulation on the induced PTS: every
    AST weak transition must be matchable by a coupled weak transition in
    the other system. *)
Definition ppts_bisimF
    (sim : ptree E M R1 -> ptree E M R2 -> Prop)
    (t1 : ptree E M R1) (t2 : ptree E M R2) : Prop :=
  (forall hs1, ppts_ast_weak (observe t1) hs1 -> exists hs2,
      ppts_ast_weak (observe t2) hs2 /\
      meas_lift (aphead_rel RR sim) hs1 hs2) /\
  (forall hs2, ppts_ast_weak (observe t2) hs2 -> exists hs1,
      ppts_ast_weak (observe t1) hs1 /\
      meas_lift (aphead_rel RR sim) hs1 hs2).

Lemma ppts_bisimF_monotone sim1 sim2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall t1 t2, ppts_bisimF sim1 t1 t2 -> ppts_bisimF sim2 t1 t2.
Proof.
  intros Hsim t1 t2 [HL HR]. split; intros hs Hweak.
  - destruct (HL _ Hweak) as [hs' [Hw' Hlift]].
    exists hs'. split; [exact Hw'|].
    eapply meas_lift_mono; [|exact Hlift].
    exact (aphead_rel_mono Hsim).
  - destruct (HR _ Hweak) as [hs' [Hw' Hlift]].
    exists hs'. split; [exact Hw'|].
    eapply meas_lift_mono; [|exact Hlift].
    exact (aphead_rel_mono Hsim).
Qed.

Program Definition fppts_bisim :
    mon (ptree E M R1 -> ptree E M R2 -> Prop) :=
  {| body := ppts_bisimF |}.
Next Obligation.
  intros sim1 sim2 Hsub t1 t2 H.
  eapply ppts_bisimF_monotone; eauto.
Qed.

Definition ppts_bisim : ptree E M R1 -> ptree E M R2 -> Prop :=
  gfp fppts_bisim.

Lemma ppts_bisim_unfold t1 t2 :
  ppts_bisim t1 t2 -> ppts_bisimF ppts_bisim t1 t2.
Proof. intro H. apply (gfp_pfp fppts_bisim) in H. exact H. Qed.

Lemma ppts_bisim_fold t1 t2 :
  ppts_bisimF ppts_bisim t1 t2 -> ppts_bisim t1 t2.
Proof. intro H. unfold ppts_bisim. apply (gfp_fp fppts_bisim). exact H. Qed.

(** The weak-transition-only relation is intentionally termination
    observational: if neither side has any AST weak transition, its matching
    clauses are vacuous.  This theorem records the exact reason unrestricted
    completeness to guarded [auweak] cannot hold. *)
Lemma ppts_bisim_of_no_weak_transitions t1 t2 :
  (forall hs, ~ ppts_ast_weak (observe t1) hs) ->
  (forall hs, ~ ppts_ast_weak (observe t2) hs) ->
  ppts_bisim t1 t2.
Proof.
  intros Hnone1 Hnone2. apply ppts_bisim_fold. split.
  - intros hs Hweak. exfalso. exact (Hnone1 _ Hweak).
  - intros hs Hweak. exfalso. exact (Hnone2 _ Hweak).
Qed.

End PTSBisimulation.

Section AuweakPTSSoundness.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}
  `{ML : @MeasureLaws M MI MC} `{MB : @MeasureBindLaws M MI}
  `{MM : @MeasureMonadLaws M MI}
  `{MG : @MeasureCongruenceLaws M MI}
  `{MO : @MeasureOmegaInterface M MI}
  `{UC : @UnboundedFrontierCoherence E M MI MO}.

Theorem auweak_ppts_bisim_sound {R1 R2}
    (RR : R1 -> R2 -> Prop) :
  forall t1 t2,
    @auweak E M MI MC MO R1 R2 RR t1 t2 ->
    @ppts_bisim E M MI MC MO R1 R2 RR t1 t2.
Proof.
  unfold ppts_bisim. coinduction CH CIH.
  intros t1 t2 Hrel. unfold fppts_bisim, ppts_bisimF; cbn.
  assert (Hmatch : aufrontier_match RR (auweak RR)
      (observe t1) (observe t2)).
  { exact (auweakF_frontier_match (auweak_unfold Hrel)). }
  destruct Hmatch as [HL HR]. split.
  - intros hs1 Hpts1.
    pose proof (ppts_ast_weak_to_aufrontier Hpts1) as Hf1.
    destruct (HL _ Hf1) as [hs2 [Hf2 Hlift]].
    exists hs2. split.
    + exact (aufrontier_to_ppts_ast_weak Hf2).
    + eapply meas_lift_mono; [|exact Hlift].
      intros h1 h2 Hh. eapply aphead_rel_mono; [exact CIH|exact Hh].
  - intros hs2 Hpts2.
    pose proof (ppts_ast_weak_to_aufrontier Hpts2) as Hf2.
    destruct (HR _ Hf2) as [hs1 [Hf1 Hlift]].
    exists hs1. split.
    + exact (aufrontier_to_ppts_ast_weak Hf1).
    + eapply meas_lift_mono; [|exact Hlift].
      intros h1 h2 Hh. eapply aphead_rel_mono; [exact CIH|exact Hh].
Qed.

End AuweakPTSSoundness.

Section PTSCompleteness.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}
  `{ML : @MeasureLaws M MI MC} `{MB : @MeasureBindLaws M MI}
  `{MM : @MeasureMonadLaws M MI}
  `{MG : @MeasureCongruenceLaws M MI}
  `{MO : @MeasureOmegaInterface M MI}.

Theorem ppts_bisim_complete_productive {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (productive : forall u v,
      @ppts_bisim E M MI MC MO R1 R2 RR u v ->
      exists hs, ppts_ast_weak (observe u) hs) :
  forall t1 t2,
    @ppts_bisim E M MI MC MO R1 R2 RR t1 t2 ->
    @auweak E M MI MC MO R1 R2 RR t1 t2.
Proof.
  unfold auweak. coinduction CH CIH. intros t1 t2 Hbisim.
  unfold fauweak, auweak_body; cbn.
  destruct (productive _ _ Hbisim) as [hs1 Hweak1].
  destruct (ppts_bisim_unfold Hbisim) as [HL HR].
  destruct (HL _ Hweak1) as [hs2 [Hweak2 Hlift]].
  eapply AUWFrontier with (hs1 := hs1) (hs2 := hs2).
  - exact (ppts_ast_weak_to_aufrontier Hweak1).
  - exact (ppts_ast_weak_to_aufrontier Hweak2).
  - eapply meas_lift_mono; [|exact Hlift].
    intros h1 h2 Hh. dependent destruction Hh.
    + constructor. assumption.
    + constructor. intro x.
      apply CIH. auto.
Qed.

End PTSCompleteness.

Section GuardedPTSBisimulation.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}
  `{MO : @MeasureOmegaInterface M MI}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

Definition ppts_ast_match
    (sim : ptree E M R1 -> ptree E M R2 -> Prop)
    (ot1 : ptree' E M R1) (ot2 : ptree' E M R2) : Prop :=
  (forall hs1, ppts_ast_weak ot1 hs1 -> exists hs2,
      ppts_ast_weak ot2 hs2 /\ meas_lift (aphead_rel RR sim) hs1 hs2) /\
  (forall hs2, ppts_ast_weak ot2 hs2 -> exists hs1,
      ppts_ast_weak ot1 hs1 /\ meas_lift (aphead_rel RR sim) hs1 hs2).

(** Divergence-sensitive PTS bisimulation.  The frontier rule observes an
    actual AST weak transition; the guarded Tau/Prob rules retain primitive
    residual transitions when no such transition exists. *)
Inductive ppts_guardedF
    (sim : ptree E M R1 -> ptree E M R2 -> Prop) :
    ptree' E M R1 -> ptree' E M R2 -> Prop :=
  | PPTSGFrontier ot1 ot2 hs1 hs2 :
      ppts_ast_weak ot1 hs1 -> ppts_ast_weak ot2 hs2 ->
      meas_lift (aphead_rel RR sim) hs1 hs2 ->
      ppts_guardedF sim ot1 ot2
  | PPTSGTau t1 t2 :
      ppts_ast_match sim (TauF t1) (TauF t2) ->
      sim t1 t2 -> ppts_guardedF sim (TauF t1) (TauF t2)
  | PPTSGProb {X Y} (mu : M X) (nu : M Y) k1 k2 :
      ppts_ast_match sim (ProbF mu k1) (ProbF nu k2) ->
      meas_lift (fun x y => sim (k1 x) (k2 y)) mu nu ->
      ppts_guardedF sim (ProbF mu k1) (ProbF nu k2)
  | PPTSGTauL t1 ot2 :
      ppts_guardedF sim (observe t1) ot2 ->
      ppts_guardedF sim (TauF t1) ot2
  | PPTSGTauR ot1 t2 :
      ppts_guardedF sim ot1 (observe t2) ->
      ppts_guardedF sim ot1 (TauF t2).

Lemma ppts_ast_match_mono sim1 sim2 ot1 ot2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  ppts_ast_match sim1 ot1 ot2 -> ppts_ast_match sim2 ot1 ot2.
Proof.
  intros Hsim [HL HR]. split; intros hs Hweak.
  - destruct (HL _ Hweak) as [hs' [Hw' Hlift]]. exists hs'. split; auto.
    eapply meas_lift_mono; [|exact Hlift]. exact (aphead_rel_mono Hsim).
  - destruct (HR _ Hweak) as [hs' [Hw' Hlift]]. exists hs'. split; auto.
    eapply meas_lift_mono; [|exact Hlift]. exact (aphead_rel_mono Hsim).
Qed.

Lemma ppts_guardedF_monotone sim1 sim2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall ot1 ot2, ppts_guardedF sim1 ot1 ot2 ->
    ppts_guardedF sim2 ot1 ot2.
Proof.
  intros Hsim ot1 ot2 Hstep. induction Hstep.
  - eapply PPTSGFrontier; [exact H|exact H0|].
    eapply meas_lift_mono; [|exact H1]. exact (aphead_rel_mono Hsim).
  - apply PPTSGTau; [exact (ppts_ast_match_mono Hsim H)|exact (Hsim _ _ H0)].
  - apply PPTSGProb; [exact (ppts_ast_match_mono Hsim H)|].
    eapply meas_lift_mono; [|exact H0]. intros x y Hxy. exact (Hsim _ _ Hxy).
  - exact (PPTSGTauL IHHstep).
  - exact (PPTSGTauR IHHstep).
Qed.

Definition ppts_guarded_body sim (t1 : ptree E M R1)
    (t2 : ptree E M R2) :=
  ppts_guardedF sim (observe t1) (observe t2).

Program Definition fppts_guarded :
    mon (ptree E M R1 -> ptree E M R2 -> Prop) :=
  {| body := ppts_guarded_body |}.
Next Obligation.
  intros sim1 sim2 Hsub t1 t2 H.
  eapply ppts_guardedF_monotone; eauto.
Qed.

Definition ppts_guarded_bisim :
    ptree E M R1 -> ptree E M R2 -> Prop := gfp fppts_guarded.

Lemma ppts_guarded_unfold t1 t2 :
  ppts_guarded_bisim t1 t2 ->
  ppts_guardedF ppts_guarded_bisim (observe t1) (observe t2).
Proof. intro H. apply (gfp_pfp fppts_guarded) in H. exact H. Qed.

Lemma ppts_guarded_fold t1 t2 :
  ppts_guardedF ppts_guarded_bisim (observe t1) (observe t2) ->
  ppts_guarded_bisim t1 t2.
Proof.
  intro H. unfold ppts_guarded_bisim. apply (gfp_fp fppts_guarded). exact H.
Qed.

End GuardedPTSBisimulation.

Section GuardedPTSCharacterization.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}
  `{ML : @MeasureLaws M MI MC} `{MB : @MeasureBindLaws M MI}
  `{MM : @MeasureMonadLaws M MI}
  `{MG : @MeasureCongruenceLaws M MI}
  `{MO : @MeasureOmegaInterface M MI}.

Lemma aufrontier_match_to_ppts_ast_match {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (sim : ptree E M R1 -> ptree E M R2 -> Prop)
    (ot1 : ptree' E M R1) (ot2 : ptree' E M R2) :
  aufrontier_match RR sim ot1 ot2 -> ppts_ast_match RR sim ot1 ot2.
Proof.
  intros [HL HR]. split; intros hs Hpts.
  - destruct (HL _ (ppts_ast_weak_to_aufrontier Hpts))
      as [hs' [Hf' Hlift]].
    exists hs'. split; [exact (aufrontier_to_ppts_ast_weak Hf')|exact Hlift].
  - destruct (HR _ (ppts_ast_weak_to_aufrontier Hpts))
      as [hs' [Hf' Hlift]].
    exists hs'. split; [exact (aufrontier_to_ppts_ast_weak Hf')|exact Hlift].
Qed.

Lemma ppts_ast_match_to_aufrontier_match {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (sim : ptree E M R1 -> ptree E M R2 -> Prop)
    (ot1 : ptree' E M R1) (ot2 : ptree' E M R2) :
  ppts_ast_match RR sim ot1 ot2 -> aufrontier_match RR sim ot1 ot2.
Proof.
  intros [HL HR]. split; intros hs Hf.
  - destruct (HL _ (aufrontier_to_ppts_ast_weak Hf))
      as [hs' [Hw' Hlift]].
    exists hs'. split; [exact (ppts_ast_weak_to_aufrontier Hw')|exact Hlift].
  - destruct (HR _ (aufrontier_to_ppts_ast_weak Hf))
      as [hs' [Hw' Hlift]].
    exists hs'. split; [exact (ppts_ast_weak_to_aufrontier Hw')|exact Hlift].
Qed.

Lemma aufrontier_match_sim_mono {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (sim1 sim2 : ptree E M R1 -> ptree E M R2 -> Prop) ot1 ot2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  aufrontier_match RR sim1 ot1 ot2 -> aufrontier_match RR sim2 ot1 ot2.
Proof.
  intros Hsim [HL HR]. split; intros hs Hf.
  - destruct (HL _ Hf) as [hs' [Hf' Hlift]]. exists hs'. split; auto.
    eapply meas_lift_mono; [|exact Hlift]. exact (aphead_rel_mono Hsim).
  - destruct (HR _ Hf) as [hs' [Hf' Hlift]]. exists hs'. split; auto.
    eapply meas_lift_mono; [|exact Hlift]. exact (aphead_rel_mono Hsim).
Qed.

Theorem auweak_to_ppts_guarded {R1 R2}
    (RR : R1 -> R2 -> Prop) :
  forall t1 t2,
    @auweak E M MI MC MO R1 R2 RR t1 t2 ->
    @ppts_guarded_bisim E M MI MC MO R1 R2 RR t1 t2.
Proof.
  unfold ppts_guarded_bisim. coinduction CH CIH.
  intros t1 t2 Hrel. unfold fppts_guarded, ppts_guarded_body; cbn.
  pose proof (auweak_unfold Hrel) as Hstep.
  induction Hstep.
  - eapply PPTSGFrontier.
    + exact (aufrontier_to_ppts_ast_weak H).
    + exact (aufrontier_to_ppts_ast_weak H0).
    + eapply meas_lift_mono; [|exact H1]. exact (aphead_rel_mono CIH).
  - apply PPTSGTau.
    + apply aufrontier_match_to_ppts_ast_match.
      exact (aufrontier_match_sim_mono CIH H).
    + exact (CIH _ _ H0).
  - apply PPTSGProb.
    + apply aufrontier_match_to_ppts_ast_match.
      exact (aufrontier_match_sim_mono CIH H).
    + eapply meas_lift_mono; [|exact H0]. intros x y Hxy. exact (CIH _ _ Hxy).
  - exact (PPTSGTauL IHHstep).
  - exact (PPTSGTauR IHHstep).
Qed.

Theorem ppts_guarded_to_auweak {R1 R2}
    (RR : R1 -> R2 -> Prop) :
  forall t1 t2,
    @ppts_guarded_bisim E M MI MC MO R1 R2 RR t1 t2 ->
    @auweak E M MI MC MO R1 R2 RR t1 t2.
Proof.
  unfold auweak. coinduction CH CIH.
  intros t1 t2 Hrel. unfold fauweak, auweak_body; cbn.
  pose proof (ppts_guarded_unfold Hrel) as Hstep.
  induction Hstep.
  - eapply AUWFrontier.
    + exact (ppts_ast_weak_to_aufrontier H).
    + exact (ppts_ast_weak_to_aufrontier H0).
    + eapply meas_lift_mono; [|exact H1]. exact (aphead_rel_mono CIH).
  - apply AUWTau.
    + apply ppts_ast_match_to_aufrontier_match.
      exact (ppts_ast_match_mono CIH H).
    + exact (CIH _ _ H0).
  - apply AUWProb.
    + apply ppts_ast_match_to_aufrontier_match.
      exact (ppts_ast_match_mono CIH H).
    + eapply meas_lift_mono; [|exact H0]. intros x y Hxy. exact (CIH _ _ Hxy).
  - exact (AUWTauL IHHstep).
  - exact (AUWTauR IHHstep).
Qed.

Theorem ppts_guarded_iff_auweak {R1 R2}
    (RR : R1 -> R2 -> Prop) (t1 : ptree E M R1) (t2 : ptree E M R2) :
  ppts_guarded_bisim RR t1 t2 <-> auweak RR t1 t2.
Proof.
  split; [apply ppts_guarded_to_auweak|apply auweak_to_ppts_guarded].
Qed.

(** Productive weak-only PTS bisimulation coincides with the guarded/raw
    semantics.  Without [productive], [ppts_bisim] deliberately quotients
    all states that expose no AST weak transition. *)
Corollary ppts_bisim_productive_iff_guarded {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (productive : forall u v,
      @ppts_bisim E M MI MC MO R1 R2 RR u v ->
      exists hs, ppts_ast_weak (observe u) hs)
    (t1 : ptree E M R1) (t2 : ptree E M R2) :
  ppts_bisim RR t1 t2 -> ppts_guarded_bisim RR t1 t2.
Proof.
  intro H. apply auweak_to_ppts_guarded.
  exact (ppts_bisim_complete_productive productive H).
Qed.

End GuardedPTSCharacterization.
