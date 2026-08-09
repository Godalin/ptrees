Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program Morphisms Program.Equality.

From Coinduction Require Import all.
From mathcomp Require Import ssreflect eqtype.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import FrontierLift.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variant aphead (E : Type -> Type) (M : Type -> Type) (R : Type) : Type :=
  | APHRet (r : R)
  | APHVis {X : Type} (e : E X) (k : X -> ptree E M R).

Arguments APHRet {E M R} _.
Arguments APHVis {E M R X} _ _.

Inductive aprelcomp {A B C}
    (R : A -> B -> Prop) (S : B -> C -> Prop)
    (a : A) (c : C) : Prop :=
  | aprelcomp_intro b : R a b -> S b c -> aprelcomp R S a c.

Section AbstractFrontier.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M} {R : Type}.

Inductive apfrontier : ptree' E M R -> M (aphead E M R) -> Prop :=
  | APFReturn r :
      apfrontier (RetF r) (meas_ret (APHRet r))
  | APFVisible {X} (e : E X) k :
      apfrontier (VisF e k) (meas_ret (APHVis e k))
  | APFTau t hs :
      apfrontier (observe t) hs -> apfrontier (TauF t) hs
  | APFProb {X : eqType} (mu : M X) k
      (front : X -> M (aphead E M R)) (Good : X -> Prop) :
      meas_ae mu Good ->
      (forall x, Good x ->
        apfrontier (observe (k x)) (front x)) ->
      apfrontier (ProbF mu k) (meas_bind mu front).
End AbstractFrontier.

Section AbstractWeak.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

Inductive aphead_rel
    (sim : ptree E M R1 -> ptree E M R2 -> Prop) :
    aphead E M R1 -> aphead E M R2 -> Prop :=
  | APHRRet r1 r2 : RR r1 r2 ->
      aphead_rel sim (APHRet r1) (APHRet r2)
  | APHRVis {X} (e : E X) k1 k2 :
      (forall x, sim (k1 x) (k2 x)) ->
      aphead_rel sim (APHVis e k1) (APHVis e k2).

Definition apfrontier_match sim ot1 ot2 : Prop :=
  (forall hs1, apfrontier ot1 hs1 -> exists hs2,
      apfrontier ot2 hs2 /\ meas_lift (aphead_rel sim) hs1 hs2) /\
  (forall hs2, apfrontier ot2 hs2 -> exists hs1,
      apfrontier ot1 hs1 /\ meas_lift (aphead_rel sim) hs1 hs2).

Inductive apweakF
    (sim : ptree E M R1 -> ptree E M R2 -> Prop) :
    ptree' E M R1 -> ptree' E M R2 -> Prop :=
  | APWFrontier ot1 ot2 hs1 hs2 :
      apfrontier ot1 hs1 -> apfrontier ot2 hs2 ->
      meas_lift (aphead_rel sim) hs1 hs2 -> apweakF sim ot1 ot2
  | APWTau t1 t2 :
      apfrontier_match sim (TauF t1) (TauF t2) ->
      sim t1 t2 -> apweakF sim (TauF t1) (TauF t2)
  | APWProb {X Y : eqType} (mu : M X) (nu : M Y) k1 k2 :
      apfrontier_match sim (ProbF mu k1) (ProbF nu k2) ->
      meas_lift (fun x y => sim (k1 x) (k2 y)) mu nu ->
      apweakF sim (ProbF mu k1) (ProbF nu k2)
  | APWTauL t1 ot2 :
      apweakF sim (observe t1) ot2 -> apweakF sim (TauF t1) ot2
  | APWTauR ot1 t2 :
      apweakF sim ot1 (observe t2) -> apweakF sim ot1 (TauF t2).

Lemma aphead_rel_mono sim1 sim2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall h1 h2, aphead_rel sim1 h1 h2 -> aphead_rel sim2 h1 h2.
Proof.
  move=> H h1 h2 Hr. inversion Hr; subst; constructor; auto.
Qed.

Lemma apfrontier_match_mono sim1 sim2 ot1 ot2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  apfrontier_match sim1 ot1 ot2 -> apfrontier_match sim2 ot1 ot2.
Proof.
  move=> Hsim [HL HR]; split; move=> hs Hf.
  - move: (HL _ Hf) => [hs' [Hf' Hlift]].
    exists hs'; split=> //. eapply meas_lift_mono; [|exact Hlift].
    exact: aphead_rel_mono Hsim.
  - move: (HR _ Hf) => [hs' [Hf' Hlift]].
    exists hs'; split=> //. eapply meas_lift_mono; [|exact Hlift].
    exact: aphead_rel_mono Hsim.
Qed.

Lemma apweakF_monotone sim1 sim2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall ot1 ot2, apweakF sim1 ot1 ot2 -> apweakF sim2 ot1 ot2.
Proof.
  move=> Hsim ot1 ot2 H; induction H.
  - eapply APWFrontier; [exact H|exact H0|].
    eapply meas_lift_mono; [|exact H1]. exact: aphead_rel_mono Hsim.
  - constructor; [exact: apfrontier_match_mono Hsim H|exact: Hsim H0].
  - constructor; [exact: apfrontier_match_mono Hsim H|].
    eapply meas_lift_mono; [|exact H0].
    move=> x y Hxy. exact: Hsim _ _ Hxy.
  - exact: APWTauL IHapweakF.
  - exact: APWTauR IHapweakF.
Qed.

Definition apweak_body sim (t1 : ptree E M R1) (t2 : ptree E M R2) :=
  apweakF sim (observe t1) (observe t2).

Program Definition fapweak :
    mon (ptree E M R1 -> ptree E M R2 -> Prop) :=
  {| body := apweak_body |}.
Next Obligation.
  move=> sim1 sim2 Hsub t1 t2 H.
  eapply apweakF_monotone; [exact Hsub|exact H].
Qed.

Definition apweak : ptree E M R1 -> ptree E M R2 -> Prop := gfp fapweak.

Lemma apweak_unfold t1 t2 :
  apweak t1 t2 -> apweakF apweak (observe t1) (observe t2).
Proof.
  move=> H. apply (gfp_pfp fapweak) in H. exact H.
Qed.

Lemma apweak_fold t1 t2 :
  apweakF apweak (observe t1) (observe t2) -> apweak t1 t2.
Proof.
  move=> H. unfold apweak. apply (gfp_fp fapweak). exact H.
Qed.

End AbstractWeak.

Section AbstractFrontierComposition.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}
  `{ML : @MeasureLaws M MI MC}.

Lemma aphead_rel_comp {R1 R2 R3}
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
  move=> h1 h2 h3 H12 H23.
  dependent destruction H12; dependent destruction H23.
  - constructor. by econstructor; eassumption.
  - constructor=> x. exact: Hsim _ _ _ (H x) (H0 x).
Qed.

Lemma apfrontier_match_comp {R1 R2 R3}
    (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
    (sim1 : ptree E M R1 -> ptree E M R2 -> Prop)
    (sim2 : ptree E M R2 -> ptree E M R3 -> Prop)
    (sim3 : ptree E M R1 -> ptree E M R3 -> Prop)
    (Hsim : forall t1 t2 t3,
      sim1 t1 t2 -> sim2 t2 t3 -> sim3 t1 t3) :
  forall ot1 ot2 ot3,
    apfrontier_match RR1 sim1 ot1 ot2 ->
    apfrontier_match RR2 sim2 ot2 ot3 ->
    apfrontier_match (aprelcomp RR1 RR2) sim3 ot1 ot3.
Proof.
  move=> ot1 ot2 ot3 [H12L H12R] [H23L H23R]; split.
  - move=> hs1 Hf1.
    move: (H12L _ Hf1)=> [hs2 [Hf2 Hc12]].
    move: (H23L _ Hf2)=> [hs3 [Hf3 Hc23]].
    exists hs3; split=> //.
    have Hcomp := @meas_lift_comp M MI MC ML
      _ _ _ _ _ _ _ _ Hc12 Hc23.
    eapply meas_lift_mono; [|exact Hcomp].
    move=> h1 h3 [h2 [Hh12 Hh23]].
    eapply aphead_rel_comp; [exact Hsim|exact Hh12|exact Hh23].
  - move=> hs3 Hf3.
    move: (H23R _ Hf3)=> [hs2 [Hf2 Hc23]].
    move: (H12R _ Hf2)=> [hs1 [Hf1 Hc12]].
    exists hs1; split=> //.
    have Hcomp := @meas_lift_comp M MI MC ML
      _ _ _ _ _ _ _ _ Hc12 Hc23.
    eapply meas_lift_mono; [|exact Hcomp].
    move=> h1 h3 [h2 [Hh12 Hh23]].
    eapply aphead_rel_comp; [exact Hsim|exact Hh12|exact Hh23].
Qed.

End AbstractFrontierComposition.

Section AbstractWeakFacts.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}.

Lemma aphead_rel_refl {R}
    (sim : ptree E M R -> ptree E M R -> Prop) :
  Reflexive sim -> Reflexive (aphead_rel eq sim).
Proof.
  move=> Hsim h. destruct h as [r|X e k].
  - constructor. reflexivity.
  - constructor=> x. exact: Hsim (k x).
Qed.

Lemma apfrontier_match_refl {R}
    (sim : ptree E M R -> ptree E M R -> Prop)
    (Hhead : Reflexive (aphead_rel eq sim)) :
  forall ot, apfrontier_match eq sim ot ot.
Proof.
  move=> ot; split; move=> hs Hf; exists hs; split=> //.
  all: apply meas_lift_refl; exact Hhead.
Qed.

Lemma apweak_refl {R} : Reflexive (@apweak E M MI MC R R eq).
Proof.
  move=> t. revert t. unfold apweak.
  coinduction CH CIH. move=> t.
  unfold apweak_body. set ot := observe t.
  change (apweakF eq (elem CH) ot ot).
  destruct ot as [r|u|X e k|X mu k].
  - eapply APWFrontier with
        (hs1 := meas_ret (APHRet r))
        (hs2 := meas_ret (APHRet r)).
    + constructor.
    + constructor.
    + apply meas_lift_refl.
      apply aphead_rel_refl. exact CIH.
  - constructor.
    + apply apfrontier_match_refl.
      apply aphead_rel_refl. exact CIH.
    + exact: CIH u.
  - eapply APWFrontier with
        (hs1 := meas_ret (APHVis e k))
        (hs2 := meas_ret (APHVis e k)).
    + constructor.
    + constructor.
    + apply meas_lift_refl.
      apply aphead_rel_refl. exact CIH.
  - constructor.
    + apply apfrontier_match_refl.
      apply aphead_rel_refl. exact CIH.
    + apply meas_lift_refl=> x. exact: CIH (k x).
Qed.

End AbstractWeakFacts.

Section AbstractWeakSymmetry.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : MeasureInterface M} `{MC : @MeasureCoreLaws M MI}
  `{ML : @MeasureLaws M MI MC}.

Lemma aphead_rel_sym {R1 R2} (RR : R1 -> R2 -> Prop)
    (sim : ptree E M R1 -> ptree E M R2 -> Prop)
    (sim' : ptree E M R2 -> ptree E M R1 -> Prop) :
  (forall t1 t2, sim t1 t2 -> sim' t2 t1) ->
  forall h1 h2,
    aphead_rel RR sim h1 h2 ->
    aphead_rel (fun y x => RR x y) sim' h2 h1.
Proof.
  move=> Hsim h1 h2 H. inversion H; subst.
  - constructor. exact H0.
  - constructor=> x. exact: Hsim _ _ (H0 x).
Qed.

Lemma apfrontier_match_sym {R1 R2} (RR : R1 -> R2 -> Prop)
    (sim : ptree E M R1 -> ptree E M R2 -> Prop)
    (sim' : ptree E M R2 -> ptree E M R1 -> Prop)
    (Hsim : forall t1 t2, sim t1 t2 -> sim' t2 t1) :
  forall ot1 ot2,
    apfrontier_match RR sim ot1 ot2 ->
    apfrontier_match (fun y x => RR x y) sim' ot2 ot1.
Proof.
  move=> ot1 ot2 [HL HR]; split.
  - move=> hs2 Hf2. move: (HR _ Hf2)=> [hs1 [Hf1 Hlift]].
    exists hs1; split=> //.
    eapply meas_lift_mono; [|exact: meas_lift_sym Hlift].
    move=> h2 h1 Hh. eapply aphead_rel_sym; [exact Hsim|exact Hh].
  - move=> hs1 Hf1. move: (HL _ Hf1)=> [hs2 [Hf2 Hlift]].
    exists hs2; split=> //.
    eapply meas_lift_mono; [|exact: meas_lift_sym Hlift].
    move=> h2 h1 Hh. eapply aphead_rel_sym; [exact Hsim|exact Hh].
Qed.

Lemma apweakF_sym {R1 R2} (RR : R1 -> R2 -> Prop)
    (sim : ptree E M R1 -> ptree E M R2 -> Prop)
    (sim' : ptree E M R2 -> ptree E M R1 -> Prop) :
  (forall t1 t2, sim t1 t2 -> sim' t2 t1) ->
  forall ot1 ot2,
    apweakF RR sim ot1 ot2 ->
    apweakF (fun y x => RR x y) sim' ot2 ot1.
Proof.
  move=> Hsim ot1 ot2 H; induction H.
  - eapply APWFrontier; [exact H0|exact H|].
    eapply meas_lift_mono; [|exact: meas_lift_sym H1].
    move=> h2 h1 Hh. eapply aphead_rel_sym; [exact Hsim|exact Hh].
  - constructor.
    + eapply apfrontier_match_sym; [exact Hsim|exact H].
    + exact: Hsim _ _ H0.
  - constructor.
    + eapply apfrontier_match_sym; [exact Hsim|exact H].
    + eapply meas_lift_mono; [|exact: meas_lift_sym H0].
      move=> y x Hxy. exact: Hsim _ _ Hxy.
  - exact: APWTauR IHapweakF.
  - exact: APWTauL IHapweakF.
Qed.

Lemma apweak_sym {R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : ptree E M R1) (t2 : ptree E M R2),
    apweak RR t1 t2 ->
    apweak (fun y x => RR x y) t2 t1.
Proof.
  unfold apweak at 2. coinduction CH CIH.
  move=> t1 t2 Hrel. move: (apweak_unfold Hrel)=> Hstep.
  unfold apweak_body. eapply apweakF_sym; [exact CIH|exact Hstep].
Qed.

End AbstractWeakSymmetry.
