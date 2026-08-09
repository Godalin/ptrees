Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program.

From Coinduction Require Import all.
From mathcomp Require Import eqtype.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import FrontierLift MeasureIteration.
From PTree.Eq Require Import PWeakAbstract.

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

Inductive aufrontier {R} :
    ptree' E M R -> M (aphead E M R) -> Prop :=
  | AUFFinite ot hs :
      apfrontier ot hs -> aufrontier ot hs
  | AUFIter {I : Type}
      (step : I -> ptree E M (I + R))
      (transition : I -> M (I + R)) i out :
      (forall j,
        apfrontier (observe (step j))
          (meas_bind (transition j)
            (fun next => meas_ret (APHRet next)))) ->
      meas_iter transition i out ->
      aufrontier (observe (PTree.iter step i))
        (meas_bind out (fun r => meas_ret (APHRet r))).

Lemma apfrontier_aufrontier {R} ot hs :
  @apfrontier E M MI R ot hs -> aufrontier ot hs.
Proof. apply AUFFinite. Qed.

(** Unbounded iteration is functional up to measure equality whenever the
    model's omega-limit is unique. *)
Lemma aufrontier_iter_unique
    `{OL : @MeasureOmegaLaws M MI MO}
    {I R} (transition : I -> M (I + R)) i out1 out2 :
  meas_iter transition i out1 ->
  meas_iter transition i out2 ->
  meas_eq out1 out2.
Proof. eapply meas_iter_unique. Qed.

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
  | AUWProb {X Y : eqType} (mu : M X) (nu : M Y) k1 k2 :
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

End UnboundedWeakReflexivity.
