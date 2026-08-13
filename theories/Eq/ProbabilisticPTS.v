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
