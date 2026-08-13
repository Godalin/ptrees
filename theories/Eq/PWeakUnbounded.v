Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program.

From Coinduction Require Import all.
From mathcomp Require Import eqtype.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import FrontierLift MeasureIteration.
From PTree.Eq Require Import PWeakAbstract.

(** Relational composition, re-exported here so clients of the unbounded
    theory do not need to import the finite weak-bisimulation module
    explicitly. *)
Definition aurelcomp {A B C}
    (R : A -> B -> Prop) (S : B -> C -> Prop) : A -> C -> Prop :=
  aprelcomp R S.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Frontiers which may cross an unbounded, almost-surely terminating
    internal iteration.  The ordinary finite frontier remains available
    unchanged through [AUFFinite]. *)
Section UnboundedFrontier.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M}
  `{MO : @MeasureOmegaInterface M MI}.

Definition aphead_bind_front {A B}
    (k : A -> ptree E M B)
    (front : A -> M (aphead E M B))
    (h : aphead E M A) : M (aphead E M B) :=
  match h with
  | APHRet a => front a
  | @APHVis _ _ _ X e c =>
      meas_ret (APHVis e (fun x => PTree.bind (c x) k))
  end.

Inductive aufrontier {R} :
    ptree' E M R -> M (aphead E M R) -> Prop :=
  | AUFFinite ot hs :
      apfrontier ot hs -> aufrontier ot hs
  | AUFTau t hs :
      aufrontier (observe t) hs ->
      aufrontier (TauF t) hs
  | AUFProb {X : Type} (mu : M X) k
      (front : X -> M (aphead E M R)) (Good : X -> Prop) :
      meas_ae mu Good ->
      (forall x, Good x -> aufrontier (observe (k x)) (front x)) ->
      aufrontier (ProbF mu k) (meas_bind mu front)
  | AUFIter {I : Type}
      (step : I -> ptree E M (I + R))
      (transition : I -> M (I + R)) i out :
      (forall j,
        apfrontier (observe (step j))
          (meas_bind (transition j)
            (fun next => meas_ret (APHRet next)))) ->
      meas_iter transition i out ->
      meas_total out ->
      aufrontier (observe (PTree.iter step i))
        (meas_bind out (fun r => meas_ret (APHRet r)))
  | AUFBind {A : Type}
      (t : ptree E M A) (k : A -> ptree E M R)
      hs (front : A -> M (aphead E M R)) :
      aufrontier (observe t) hs ->
      (forall a, aufrontier (observe (k a)) (front a)) ->
      aufrontier (observe (PTree.bind t k))
        (meas_bind hs (aphead_bind_front k front))
  | AUFNestedIter {I : Type}
      (step : I -> ptree E M (I + R))
      (transition : I -> M (I + R)) i out :
      (forall j,
        aufrontier (observe (step j))
          (meas_bind (transition j)
            (fun next => meas_ret (APHRet next)))) ->
      meas_iter transition i out ->
      meas_total out ->
      aufrontier (observe (PTree.iter step i))
        (meas_bind out (fun r => meas_ret (APHRet r))).

(** Coherence of the unbounded closure.  Unlike finite frontier
    determinism, this is not derivable from [MeasureBindLaws] alone:
    [AUFBind] and [AUFNestedIter] also require continuity/coherence between
    bind and omega limits.  Keeping the obligation explicit prevents raw
    [auweak] transitivity from silently assuming a canonical limit
    representation. *)
Class UnboundedFrontierCoherence := {
  aufrontier_unique : forall {R} (ot : ptree' E M R) hs1 hs2,
      aufrontier ot hs1 -> aufrontier ot hs2 -> meas_eq hs1 hs2;
  aufrontier_tau_inv : forall {R} (t : ptree E M R) hs,
      aufrontier (TauF t) hs -> aufrontier (observe t) hs
}.


Lemma apfrontier_aufrontier {R} ot hs :
  @apfrontier E M MI R ot hs -> aufrontier ot hs.
Proof. apply AUFFinite. Qed.

Lemma aufrontier_tau {R} (t : ptree E M R) hs :
  aufrontier (observe t) hs -> aufrontier (TauF t) hs.
Proof. apply AUFTau. Qed.

(** Unbounded iteration is functional up to measure equality whenever the
    model's omega-limit is unique. *)
Lemma aufrontier_iter_unique
    `{OL : @MeasureOmegaLaws M MI MO}
    {I R} (transition : I -> M (I + R)) i out1 out2 :
  meas_iter transition i out1 ->
  meas_iter transition i out2 ->
  meas_eq out1 out2.
Proof. eapply meas_iter_unique. Qed.

(** Public, representation-independent unbounded frontier semantics.  As in
    the finite case, the inductive judgment records a canonical witness and
    this closure exposes every extensionally equal measure to clients. *)
Definition aufrontier_sem
    `{MC : @MeasureCoreLaws M MI} `{ML : @MeasureLaws M MI MC}
    {R} (ot : ptree' E M R) (hs : M (aphead E M R)) : Prop :=
  exists hs0, aufrontier ot hs0 /\ meas_eq hs0 hs.

Lemma aufrontier_aufrontier_sem
    `{MC : @MeasureCoreLaws M MI} `{ML : @MeasureLaws M MI MC}
    {R} (ot : ptree' E M R) (hs : M (aphead E M R)) :
  aufrontier ot hs -> aufrontier_sem ot hs.
Proof. intros Hf. exists hs. split; [exact Hf|apply meas_eq_refl]. Qed.

Lemma apfrontier_aufrontier_sem
    `{MC : @MeasureCoreLaws M MI} `{ML : @MeasureLaws M MI MC}
    {R} (ot : ptree' E M R) (hs : M (aphead E M R)) :
  apfrontier ot hs -> aufrontier_sem ot hs.
Proof.
  intros Hf. apply aufrontier_aufrontier_sem. exact (AUFFinite Hf).
Qed.

Lemma aufrontier_sem_proper
    `{MC : @MeasureCoreLaws M MI} `{ML : @MeasureLaws M MI MC}
    {R} (ot : ptree' E M R) hs hs' :
  aufrontier_sem ot hs -> meas_eq hs hs' -> aufrontier_sem ot hs'.
Proof.
  intros [hs0 [Hf E0]] E1. exists hs0. split; [exact Hf|].
  eapply meas_eq_trans; eassumption.
Qed.

End UnboundedFrontier.

Section UnboundedWeak.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M}
  `{MC : @MeasureCoreLaws M MI}
  `{MO : @MeasureOmegaInterface M MI}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

Definition aufrontier_match
    (sim : ptree E M R1 -> ptree E M R2 -> Prop)
    (ot1 : ptree' E M R1) (ot2 : ptree' E M R2) : Prop :=
  (forall hs1, aufrontier ot1 hs1 -> exists hs2,
      aufrontier ot2 hs2 /\ meas_lift (aphead_rel RR sim) hs1 hs2) /\
  (forall hs2, aufrontier ot2 hs2 -> exists hs1,
      aufrontier ot1 hs1 /\ meas_lift (aphead_rel RR sim) hs1 hs2).

Inductive auweakF
    (sim : ptree E M R1 -> ptree E M R2 -> Prop) :
    ptree' E M R1 -> ptree' E M R2 -> Prop :=
  | AUWFrontier ot1 ot2 hs1 hs2 :
      aufrontier ot1 hs1 -> aufrontier ot2 hs2 ->
      meas_lift (aphead_rel RR sim) hs1 hs2 ->
      auweakF sim ot1 ot2
  | AUWTau t1 t2 :
      aufrontier_match sim (TauF t1) (TauF t2) ->
      sim t1 t2 -> auweakF sim (TauF t1) (TauF t2)
  | AUWProb {X Y : Type} (mu : M X) (nu : M Y) k1 k2 :
      aufrontier_match sim (ProbF mu k1) (ProbF nu k2) ->
      meas_lift (fun x y => sim (k1 x) (k2 y)) mu nu ->
      auweakF sim (ProbF mu k1) (ProbF nu k2)
  | AUWTauL t1 ot2 :
      auweakF sim (observe t1) ot2 -> auweakF sim (TauF t1) ot2
  | AUWTauR ot1 t2 :
      auweakF sim ot1 (observe t2) -> auweakF sim ot1 (TauF t2).

Lemma auweakF_monotone sim1 sim2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall ot1 ot2, auweakF sim1 ot1 ot2 -> auweakF sim2 ot1 ot2.
Proof.
  intros Hsim ot1 ot2 Hstep. induction Hstep.
  - eapply AUWFrontier; [exact H|exact H0|].
    eapply meas_lift_mono; [|exact H1].
    eapply aphead_rel_mono. exact Hsim.
  - apply AUWTau.
    + destruct H as [HL HR]. split; intros hs Hf.
      * destruct (HL hs Hf) as [hs' [Hf' Hlift]].
        exists hs'. split; [exact Hf'|].
        eapply meas_lift_mono; [|exact Hlift].
        eapply aphead_rel_mono. exact Hsim.
      * destruct (HR hs Hf) as [hs' [Hf' Hlift]].
        exists hs'. split; [exact Hf'|].
        eapply meas_lift_mono; [|exact Hlift].
        eapply aphead_rel_mono. exact Hsim.
    + exact (Hsim _ _ H0).
  - apply AUWProb.
    + destruct H as [HL HR]. split; intros hs Hf.
      * destruct (HL hs Hf) as [hs' [Hf' Hlift]].
        exists hs'. split; [exact Hf'|].
        eapply meas_lift_mono; [|exact Hlift].
        eapply aphead_rel_mono. exact Hsim.
      * destruct (HR hs Hf) as [hs' [Hf' Hlift]].
        exists hs'. split; [exact Hf'|].
        eapply meas_lift_mono; [|exact Hlift].
        eapply aphead_rel_mono. exact Hsim.
    + eapply meas_lift_mono; [|exact H0].
      intros x y Hxy. exact (Hsim _ _ Hxy).
  - exact (AUWTauL IHHstep).
  - exact (AUWTauR IHHstep).
Qed.

Definition auweak_body sim (t1 : ptree E M R1) (t2 : ptree E M R2) :=
  auweakF sim (observe t1) (observe t2).

Program Definition fauweak :
    mon (ptree E M R1 -> ptree E M R2 -> Prop) :=
  {| body := auweak_body |}.
Next Obligation.
  intros sim1 sim2 Hsub t1 t2 H.
  eapply auweakF_monotone; eauto.
Qed.

Definition auweak : ptree E M R1 -> ptree E M R2 -> Prop :=
  gfp fauweak.

Lemma auweak_unfold t1 t2 :
  auweak t1 t2 -> auweakF auweak (observe t1) (observe t2).
Proof. intro H. apply (gfp_pfp fauweak) in H. exact H. Qed.

Lemma auweak_fold t1 t2 :
  auweakF auweak (observe t1) (observe t2) -> auweak t1 t2.
Proof. intro H. unfold auweak. apply (gfp_fp fauweak). exact H. Qed.

End UnboundedWeak.

Section UnboundedFrontierCoherentFacts.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}
  `{ML : @MeasureLaws M MI MC} `{MO : @MeasureOmegaInterface M MI}
  `{UC : @UnboundedFrontierCoherence E M MI MO}.

Lemma auweakF_frontier_l {R1 R2} (RR : R1 -> R2 -> Prop)
    (sim : ptree E M R1 -> ptree E M R2 -> Prop)
    ot1 ot2 hs1 :
  auweakF RR sim ot1 ot2 -> aufrontier ot1 hs1 ->
  exists hs2, aufrontier ot2 hs2 /\
    meas_lift (aphead_rel RR sim) hs1 hs2.
Proof.
  intros Hstep. revert hs1.
  induction Hstep; intros hs Hfront.
  - assert (Heq : meas_eq hs hs1).
    { eapply aufrontier_unique; eassumption. }
    exists hs2. split; [exact H0|].
    apply (@meas_lift_proper_l M MI MC ML _ _
      (aphead_rel RR sim) hs1 hs hs2).
    + apply meas_eq_sym. exact Heq.
    + exact H1.
  - exact (proj1 H _ Hfront).
  - exact (proj1 H _ Hfront).
  - exact (IHHstep _ (aufrontier_tau_inv Hfront)).
  - destruct (IHHstep _ Hfront) as [hs2 [Hf2 Hlift]].
    exists hs2. split; [exact (AUFTau Hf2)|exact Hlift].
Qed.

Lemma auweakF_frontier_r {R1 R2} (RR : R1 -> R2 -> Prop)
    (sim : ptree E M R1 -> ptree E M R2 -> Prop)
    ot1 ot2 hs2 :
  auweakF RR sim ot1 ot2 -> aufrontier ot2 hs2 ->
  exists hs1, aufrontier ot1 hs1 /\
    meas_lift (aphead_rel RR sim) hs1 hs2.
Proof.
  intros Hstep. revert hs2.
  induction Hstep; intros hs Hfront.
  - assert (Heq : meas_eq hs2 hs).
    { eapply aufrontier_unique; eassumption. }
    exists hs1. split; [exact H|].
    exact (@meas_lift_proper_r M MI MC ML _ _
      (aphead_rel RR sim) hs1 hs2 hs Heq H1).
  - exact (proj2 H _ Hfront).
  - exact (proj2 H _ Hfront).
  - destruct (IHHstep _ Hfront) as [hs1 [Hf1 Hlift]].
    exists hs1. split; [exact (AUFTau Hf1)|exact Hlift].
  - exact (IHHstep _ (aufrontier_tau_inv Hfront)).
Qed.

Lemma auweakF_frontier_match {R1 R2} (RR : R1 -> R2 -> Prop)
    (sim : ptree E M R1 -> ptree E M R2 -> Prop) ot1 ot2 :
  auweakF RR sim ot1 ot2 -> aufrontier_match RR sim ot1 ot2.
Proof.
  intros Hstep. split; intros hs Hfront.
  - exact (auweakF_frontier_l Hstep Hfront).
  - exact (auweakF_frontier_r Hstep Hfront).
Qed.

Lemma aufrontier_match_tau {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (t1 : ptree E M R1) (t2 : ptree E M R2) sim :
  aufrontier_match RR sim (observe t1) (observe t2) ->
  aufrontier_match RR sim (TauF t1) (TauF t2).
Proof.
  intros [HL HR]. split.
  - intros hs1 Hf1.
    destruct (HL _ (aufrontier_tau_inv Hf1)) as [hs2 [Hf2 Hlift]].
    exists hs2. split; [exact (AUFTau Hf2)|exact Hlift].
  - intros hs2 Hf2.
    destruct (HR _ (aufrontier_tau_inv Hf2)) as [hs1 [Hf1 Hlift]].
    exists hs1. split; [exact (AUFTau Hf1)|exact Hlift].
Qed.

Lemma aufrontier_match_untau_r {R1 R2}
    (RR : R1 -> R2 -> Prop) ot1 (t2 : ptree E M R2) sim :
  aufrontier_match RR sim ot1 (TauF t2) ->
  aufrontier_match RR sim ot1 (observe t2).
Proof.
  intros [HL HR]. split.
  - intros hs1 Hf1. destruct (HL _ Hf1) as [hs2 [Hf2 Hlift]].
    exists hs2. split; [exact (aufrontier_tau_inv Hf2)|exact Hlift].
  - intros hs2 Hf2. exact (HR _ (AUFTau Hf2)).
Qed.

Lemma aufrontier_match_untau_l {R1 R2}
    (RR : R1 -> R2 -> Prop) (t1 : ptree E M R1) ot2 sim :
  aufrontier_match RR sim (TauF t1) ot2 ->
  aufrontier_match RR sim (observe t1) ot2.
Proof.
  intros [HL HR]. split.
  - intros hs1 Hf1. exact (HL _ (AUFTau Hf1)).
  - intros hs2 Hf2. destruct (HR _ Hf2) as [hs1 [Hf1 Hlift]].
    exists hs1. split; [exact (aufrontier_tau_inv Hf1)|exact Hlift].
Qed.

Lemma auhead_rel_comp {R1 R2 R3}
    (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
    (sim1 : ptree E M R1 -> ptree E M R2 -> Prop)
    (sim2 : ptree E M R2 -> ptree E M R3 -> Prop)
    (sim3 : ptree E M R1 -> ptree E M R3 -> Prop)
    (Hsim : forall t1 t2 t3,
      sim1 t1 t2 -> sim2 t2 t3 -> sim3 t1 t3) :
  forall h1 h2 h3,
    aphead_rel RR1 sim1 h1 h2 ->
    aphead_rel RR2 sim2 h2 h3 ->
    aphead_rel (aprelcomp RR1 RR2) sim3 h1 h3.
Proof.
  intros h1 h2 h3 H12 H23.
  dependent destruction H12; dependent destruction H23.
  - constructor. econstructor; eassumption.
  - constructor. intro x. eapply Hsim; eauto.
Qed.

Lemma aufrontier_match_comp {R1 R2 R3}
    (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
    (sim1 : ptree E M R1 -> ptree E M R2 -> Prop)
    (sim2 : ptree E M R2 -> ptree E M R3 -> Prop)
    (sim3 : ptree E M R1 -> ptree E M R3 -> Prop)
    (Hsim : forall t1 t2 t3,
      sim1 t1 t2 -> sim2 t2 t3 -> sim3 t1 t3) :
  forall ot1 ot2 ot3,
    aufrontier_match RR1 sim1 ot1 ot2 ->
    aufrontier_match RR2 sim2 ot2 ot3 ->
    aufrontier_match (aprelcomp RR1 RR2) sim3 ot1 ot3.
Proof.
  intros ot1 ot2 ot3 [H12L H12R] [H23L H23R]. split.
  - intros hs1 Hf1.
    destruct (H12L _ Hf1) as [hs2 [Hf2 Hc12]].
    destruct (H23L _ Hf2) as [hs3 [Hf3 Hc23]].
    exists hs3. split; [exact Hf3|].
    eapply meas_lift_mono; [|eapply meas_lift_comp; eassumption].
    intros h1 h3 [h2 [Hh12 Hh23]].
    eapply auhead_rel_comp; eauto.
  - intros hs3 Hf3.
    destruct (H23R _ Hf3) as [hs2 [Hf2 Hc23]].
    destruct (H12R _ Hf2) as [hs1 [Hf1 Hc12]].
    exists hs1. split; [exact Hf1|].
    eapply meas_lift_mono; [|eapply meas_lift_comp; eassumption].
    intros h1 h3 [h2 [Hh12 Hh23]].
    eapply auhead_rel_comp; eauto.
Qed.

End UnboundedFrontierCoherentFacts.

Section UnboundedWeakCoherentTauInversion.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}
  `{ML : @MeasureLaws M MI MC} `{MO : @MeasureOmegaInterface M MI}
  `{UC : @UnboundedFrontierCoherence E M MI MO}.

Lemma auweakF_inv_tau_l_step {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (t1 : ptree E M R1) (ot2 : ptree' E M R2) :
  auweakF RR (auweak RR) (TauF t1) ot2 ->
  auweakF RR (auweak RR) (observe t1) ot2.
Proof.
  intros Hstep.
  remember (TauF t1) as lhs eqn:Elhs in Hstep.
  dependent induction Hstep; try discriminate.
  - dependent destruction Elhs.
    eapply AUWFrontier; [exact (aufrontier_tau_inv H)|exact H0|exact H1].
  - injection Elhs as Et. subst t0.
    apply AUWTauR. exact (auweak_unfold H0).
  - injection Elhs as Et. subst t0. exact Hstep.
  - apply AUWTauR. eapply IHHstep; eauto.
Qed.

Lemma auweakF_inv_tau_r_step {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (ot1 : ptree' E M R1) (t2 : ptree E M R2) :
  auweakF RR (auweak RR) ot1 (TauF t2) ->
  auweakF RR (auweak RR) ot1 (observe t2).
Proof.
  intros Hstep.
  remember (TauF t2) as rhs eqn:Erhs in Hstep.
  dependent induction Hstep; try discriminate.
  - dependent destruction Erhs.
    eapply AUWFrontier; [exact H|exact (aufrontier_tau_inv H0)|exact H1].
  - injection Erhs as Et. subst t2.
    apply AUWTauL. exact (auweak_unfold H0).
  - apply AUWTauL. eapply IHHstep; eauto.
  - injection Erhs as Et. subst t2. exact Hstep.
Qed.

Lemma auweak_inv_tau_r {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : ptree E M R1) (t2 : ptree E M R2) :
  auweak RR t1 (Tau t2) -> auweak RR t1 t2.
Proof.
  revert t1 t2. unfold auweak at 2. coinduction CH CIH.
  intros t1' t2' Hrel. unfold fauweak, auweak_body; cbn.
  eapply (auweakF_monotone
    (sim1 := auweak RR) (sim2 := elem CH)).
  - intros u v Huv. apply (gfp_chain (b := fauweak RR) CH). exact Huv.
  - exact (auweakF_inv_tau_r_step (auweak_unfold Hrel)).
Qed.

Lemma auweak_inv_tau_l {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : ptree E M R1) (t2 : ptree E M R2) :
  auweak RR (Tau t1) t2 -> auweak RR t1 t2.
Proof.
  revert t1 t2. unfold auweak at 2. coinduction CH CIH.
  intros t1' t2' Hrel. unfold fauweak, auweak_body; cbn.
  eapply (auweakF_monotone
    (sim1 := auweak RR) (sim2 := elem CH)).
  - intros u v Huv. apply (gfp_chain (b := fauweak RR) CH). exact Huv.
  - exact (auweakF_inv_tau_l_step (auweak_unfold Hrel)).
Qed.

Lemma auweak_inv_tau {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : ptree E M R1) (t2 : ptree E M R2) :
  auweak RR (Tau t1) (Tau t2) -> auweak RR t1 t2.
Proof.
  intros H. apply auweak_inv_tau_l in H.
  exact (auweak_inv_tau_r H).
Qed.

End UnboundedWeakCoherentTauInversion.

Section UnboundedWeakRelationFacts.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M}
  `{MC : @MeasureCoreLaws M MI}
  `{MO : @MeasureOmegaInterface M MI}.

Lemma auhead_rel_rel_mono {R1 R2}
    (RR SS : R1 -> R2 -> Prop)
    (sim : ptree E M R1 -> ptree E M R2 -> Prop) :
  (forall x y, RR x y -> SS x y) ->
  forall h1 h2, aphead_rel RR sim h1 h2 -> aphead_rel SS sim h1 h2.
Proof.
  intros HRS h1 h2 H. inversion H; subst; constructor; auto.
Qed.

Lemma aufrontier_match_rel_mono {R1 R2}
    (RR SS : R1 -> R2 -> Prop)
    (sim : ptree E M R1 -> ptree E M R2 -> Prop) ot1 ot2 :
  (forall x y, RR x y -> SS x y) ->
  aufrontier_match RR sim ot1 ot2 ->
  aufrontier_match SS sim ot1 ot2.
Proof.
  intros HRS [HL HR]. split; intros hs Hf.
  - destruct (HL hs Hf) as [hs' [Hf' Hlift]].
    exists hs'. split; [exact Hf'|].
    eapply meas_lift_mono; [|exact Hlift].
    intros h1 h2 Hh. eapply auhead_rel_rel_mono; eauto.
  - destruct (HR hs Hf) as [hs' [Hf' Hlift]].
    exists hs'. split; [exact Hf'|].
    eapply meas_lift_mono; [|exact Hlift].
    intros h1 h2 Hh. eapply auhead_rel_rel_mono; eauto.
Qed.

Lemma auweakF_rel_mono {R1 R2}
    (RR SS : R1 -> R2 -> Prop)
    (sim : ptree E M R1 -> ptree E M R2 -> Prop) ot1 ot2 :
  (forall x y, RR x y -> SS x y) ->
  auweakF RR sim ot1 ot2 -> auweakF SS sim ot1 ot2.
Proof.
  intros HRS Hstep. induction Hstep.
  - eapply AUWFrontier; [exact H|exact H0|].
    eapply meas_lift_mono; [|exact H1].
    intros h1 h2 Hh. eapply auhead_rel_rel_mono; eauto.
  - apply AUWTau; [eapply aufrontier_match_rel_mono; eauto|exact H0].
  - apply AUWProb; [eapply aufrontier_match_rel_mono; eauto|exact H0].
  - exact (AUWTauL IHHstep).
  - exact (AUWTauR IHHstep).
Qed.

Lemma auweak_rel_mono {R1 R2}
    (RR SS : R1 -> R2 -> Prop)
    (HRS : forall x y, RR x y -> SS x y) :
  forall t1 t2, @auweak E M MI MC MO R1 R2 RR t1 t2 ->
    @auweak E M MI MC MO R1 R2 SS t1 t2.
Proof.
  unfold auweak at 2. coinduction CH CIH.
  intros t1 t2 Hrel. apply auweak_unfold in Hrel.
  unfold auweak_body. eapply auweakF_rel_mono; [exact HRS|].
  eapply auweakF_monotone; [exact CIH|exact Hrel].
Qed.

End UnboundedWeakRelationFacts.

Section UnboundedWeakSymmetry.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M}
  `{MC : @MeasureCoreLaws M MI}
  `{ML : @MeasureLaws M MI MC}
  `{MO : @MeasureOmegaInterface M MI}.

Lemma auhead_rel_sym {R1 R2} (RR : R1 -> R2 -> Prop)
    (sim : ptree E M R1 -> ptree E M R2 -> Prop)
    (sim' : ptree E M R2 -> ptree E M R1 -> Prop) :
  (forall t1 t2, sim t1 t2 -> sim' t2 t1) ->
  forall h1 h2, aphead_rel RR sim h1 h2 ->
    aphead_rel (fun y x => RR x y) sim' h2 h1.
Proof.
  intros Hsim h1 h2 H. inversion H; subst.
  - constructor. assumption.
  - constructor. intro x. apply Hsim. auto.
Qed.

Lemma aufrontier_match_sym {R1 R2} (RR : R1 -> R2 -> Prop)
    (sim : ptree E M R1 -> ptree E M R2 -> Prop)
    (sim' : ptree E M R2 -> ptree E M R1 -> Prop)
    (Hsim : forall t1 t2, sim t1 t2 -> sim' t2 t1) :
  forall ot1 ot2, aufrontier_match RR sim ot1 ot2 ->
    aufrontier_match (fun y x => RR x y) sim' ot2 ot1.
Proof.
  intros ot1 ot2 [HL HR]. split; intros hs Hf.
  - destruct (HR hs Hf) as [hs' [Hf' Hlift]].
    exists hs'. split; [exact Hf'|].
    eapply meas_lift_mono; [|eapply meas_lift_sym; exact Hlift].
    intros h2 h1 Hh. eapply auhead_rel_sym; eauto.
  - destruct (HL hs Hf) as [hs' [Hf' Hlift]].
    exists hs'. split; [exact Hf'|].
    eapply meas_lift_mono; [|eapply meas_lift_sym; exact Hlift].
    intros h2 h1 Hh. eapply auhead_rel_sym; eauto.
Qed.

Lemma auweakF_sym {R1 R2} (RR : R1 -> R2 -> Prop)
    (sim : ptree E M R1 -> ptree E M R2 -> Prop)
    (sim' : ptree E M R2 -> ptree E M R1 -> Prop) :
  (forall t1 t2, sim t1 t2 -> sim' t2 t1) ->
  forall ot1 ot2, auweakF RR sim ot1 ot2 ->
    auweakF (fun y x => RR x y) sim' ot2 ot1.
Proof.
  intros Hsim ot1 ot2 Hstep. induction Hstep.
  - eapply AUWFrontier; [exact H0|exact H|].
    eapply meas_lift_mono; [|eapply meas_lift_sym; exact H1].
    intros h2 h1 Hh. eapply auhead_rel_sym; eauto.
  - apply AUWTau.
    + eapply aufrontier_match_sym; eauto.
    + eauto.
  - apply AUWProb.
    + eapply aufrontier_match_sym; eauto.
    + eapply meas_lift_mono; [|eapply meas_lift_sym; exact H0].
      intros y x Hxy. eauto.
  - exact (AUWTauR IHHstep).
  - exact (AUWTauL IHHstep).
Qed.

Lemma auweak_sym {R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : ptree E M R1) (t2 : ptree E M R2),
    auweak RR t1 t2 -> auweak (fun y x => RR x y) t2 t1.
Proof.
  unfold auweak at 2. coinduction CH CIH.
  intros t1 t2 Hrel. apply auweak_unfold in Hrel.
  unfold auweak_body. eapply auweakF_sym; eauto.
Qed.

Lemma auweak_sym_eq {R} :
  Symmetric (@auweak E M MI MC MO R R eq).
Proof.
  intros t1 t2 H12.
  eapply (auweak_rel_mono
    (RR := fun y x : R => x = y) (SS := eq)).
  - intros x y Hxy. symmetry. exact Hxy.
  - exact (auweak_sym H12).
Qed.

End UnboundedWeakSymmetry.

Section UnboundedWeakReflexivity.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M}
  `{MC : @MeasureCoreLaws M MI}
  `{MO : @MeasureOmegaInterface M MI}.

Lemma auhead_rel_refl {R}
    (sim : ptree E M R -> ptree E M R -> Prop) :
  Reflexive sim -> Reflexive (aphead_rel eq sim).
Proof.
  intros Hsim h. destruct h as [r|X e k].
  - constructor. reflexivity.
  - constructor. intro x. apply Hsim.
Qed.

Lemma aufrontier_match_refl {R}
    (sim : ptree E M R -> ptree E M R -> Prop)
    (Hhead : Reflexive (aphead_rel eq sim)) :
  forall ot, aufrontier_match eq sim ot ot.
Proof.
  intro ot. split; intros hs Hf; exists hs; split; auto.
  all: apply meas_lift_refl; exact Hhead.
Qed.

Lemma auweak_refl {R} :
  Reflexive (@auweak E M MI MC MO R R eq).
Proof.
  intro t. revert t. unfold auweak.
  coinduction CH CIH. intro t.
  unfold auweak_body. set (ot := observe t).
  change (auweakF eq (elem CH) ot ot).
  destruct ot as [r|u|X e k|X mu k].
  - eapply AUWFrontier with
        (hs1 := meas_ret (APHRet r))
        (hs2 := meas_ret (APHRet r)).
    + apply AUFFinite. constructor.
    + apply AUFFinite. constructor.
    + apply meas_lift_refl. apply auhead_rel_refl. exact CIH.
  - apply AUWTau.
    + apply aufrontier_match_refl.
      apply auhead_rel_refl. exact CIH.
    + exact (CIH u).
  - eapply AUWFrontier with
        (hs1 := meas_ret (APHVis e k))
        (hs2 := meas_ret (APHVis e k)).
    + apply AUFFinite. constructor.
    + apply AUFFinite. constructor.
    + apply meas_lift_refl. apply auhead_rel_refl. exact CIH.
  - apply AUWProb.
    + apply aufrontier_match_refl.
      apply auhead_rel_refl. exact CIH.
    + apply meas_lift_refl. intro x. exact (CIH (k x)).
Qed.

(** Two computations are weakly bisimilar as soon as they expose one common
    (possibly unbounded) frontier.  This is the main backend boundary: a
    concrete measure model only has to identify the limiting frontier; all
    coinductive obligations are discharged here. *)
Lemma auweak_of_common_frontier {R}
    (t1 t2 : ptree E M R) hs :
  aufrontier (observe t1) hs ->
  aufrontier (observe t2) hs ->
  @auweak E M MI MC MO R R eq t1 t2.
Proof.
  intros H1 H2. apply auweak_fold.
  eapply AUWFrontier; [exact H1|exact H2|].
  apply meas_lift_refl.
  apply auhead_rel_refl.
  exact auweak_refl.
Qed.

(** Extensional version of [auweak_of_common_frontier].  The two programs
    may expose different concrete representatives of the same limiting
    measure. *)
Lemma auweak_of_common_frontier_sem
    `{ML : @MeasureLaws M MI MC} {R}
    (t1 t2 : ptree E M R) hs :
  aufrontier_sem (observe t1) hs ->
  aufrontier_sem (observe t2) hs ->
  @auweak E M MI MC MO R R eq t1 t2.
Proof.
  intros [hs1 [Hf1 E1]] [hs2 [Hf2 E2]]. apply auweak_fold.
  eapply AUWFrontier with (hs1 := hs1) (hs2 := hs2).
  - exact Hf1.
  - exact Hf2.
  - assert (Hrefl : meas_lift (aphead_rel eq (auweak eq)) hs1 hs1).
    { apply meas_lift_refl. apply auhead_rel_refl. exact auweak_refl. }
    apply (meas_lift_proper_r
      (R := aphead_rel eq (auweak eq)) (nu := hs1)).
    + eapply meas_eq_trans; [exact E1|].
      apply meas_eq_sym. exact E2.
    + exact Hrefl.
Qed.

(** A precise positive bind rule.  Unrestricted bind congruence is false:
    an arbitrary continuation may diverge and reveal an internal node that
    finite frontier equivalence had consumed.  Here every continuation is
    required to expose a (possibly unbounded AST) frontier.  The two source
    programs then share the bound frontier constructed by [AUFBind]. *)
Lemma auweak_bind_common_frontier {A R}
    (t1 t2 : ptree E M A) (k : A -> ptree E M R)
    hs (front : A -> M (aphead E M R)) :
  aufrontier (observe t1) hs ->
  aufrontier (observe t2) hs ->
  (forall a, aufrontier (observe (k a)) (front a)) ->
  auweak eq (PTree.bind t1 k) (PTree.bind t2 k).
Proof.
  intros Ht1 Ht2 Hk. apply auweak_of_common_frontier with
      (hs := meas_bind hs (aphead_bind_front k front)).
  - exact (AUFBind Ht1 Hk).
  - exact (AUFBind Ht2 Hk).
Qed.

(** Extensional source frontiers are also sufficient when bind is proper in
    its source measure.  This is the public representation-independent
    version used by measure backends. *)
Lemma auweak_bind_common_frontier_sem
    `{ML : @MeasureLaws M MI MC}
    `{MG : @MeasureCongruenceLaws M MI}
    {A R} (t1 t2 : ptree E M A) (k : A -> ptree E M R)
    hs (front : A -> M (aphead E M R)) :
  aufrontier_sem (observe t1) hs ->
  aufrontier_sem (observe t2) hs ->
  (forall a, aufrontier (observe (k a)) (front a)) ->
  auweak eq (PTree.bind t1 k) (PTree.bind t2 k).
Proof.
  intros [hs1 [Ht1 E1]] [hs2 [Ht2 E2]] Hk.
  apply auweak_of_common_frontier_sem with
      (hs := meas_bind hs (aphead_bind_front k front)).
  - exists (meas_bind hs1 (aphead_bind_front k front)). split.
    + exact (AUFBind Ht1 Hk).
    + apply meas_bind_proper; [exact E1|].
      intro h. apply meas_eq_refl.
  - exists (meas_bind hs2 (aphead_bind_front k front)). split.
    + exact (AUFBind Ht2 Hk).
    + apply meas_bind_proper; [exact E2|].
      intro h. apply meas_eq_refl.
Qed.

End UnboundedWeakReflexivity.
