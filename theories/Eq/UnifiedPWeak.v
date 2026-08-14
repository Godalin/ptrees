Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Utf8 Program Morphisms.

From Coinduction Require Import all.
From mathcomp Require Import ssreflect.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import UnifiedFrontier.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section UnifiedWeak.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

Inductive frontier_head_rel
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop) :
    frontier_head E MN R1 -> frontier_head E MN R2 -> Prop :=
  | FHRRet r1 r2 : RR r1 r2 ->
      frontier_head_rel sim (FHRet r1) (FHRet r2)
  | FHRVis {X : Type} (e : E X) k1 k2 :
      (forall x, sim (k1 x) (k2 x)) ->
      frontier_head_rel sim (FHVis e k1) (FHVis e k2).

Lemma frontier_head_rel_mono sim1 sim2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall h1 h2,
    frontier_head_rel sim1 h1 h2 -> frontier_head_rel sim2 h1 h2.
Proof.
  intros Hsim h1 h2 Hh. inversion Hh; subst; constructor; auto.
Qed.

Definition unified_frontier_match
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop)
    (ot1 : ptree' E MN R1) (ot2 : ptree' E MN R2) : Prop :=
  (forall hs1, frontier ot1 hs1 -> exists hs2,
      frontier ot2 hs2 /\
      sem_lift (frontier_head_rel sim) hs1 hs2) /\
  (forall hs2, frontier ot2 hs2 -> exists hs1,
      frontier ot1 hs1 /\
      sem_lift (frontier_head_rel sim) hs1 hs2).

Inductive weak_bisimF
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop) :
    ptree' E MN R1 -> ptree' E MN R2 -> Prop :=
  | UWBFrontier ot1 ot2 hs1 hs2 :
      frontier ot1 hs1 -> frontier ot2 hs2 ->
      sem_lift (frontier_head_rel sim) hs1 hs2 ->
      weak_bisimF sim ot1 ot2
  | UWBTau t1 t2 :
      unified_frontier_match sim (TauF t1) (TauF t2) ->
      sim t1 t2 -> weak_bisimF sim (TauF t1) (TauF t2)
  | UWBProb {X Y : Type} (mu : MN X) (nu : MN Y) k1 k2 :
      unified_frontier_match sim (ProbF mu k1) (ProbF nu k2) ->
      sem_lift (fun x y => sim (k1 x) (k2 y)) mu nu ->
      weak_bisimF sim (ProbF mu k1) (ProbF nu k2)
  | UWBTauL t1 ot2 :
      weak_bisimF sim (observe t1) ot2 ->
      weak_bisimF sim (TauF t1) ot2
  | UWBTauR ot1 t2 :
      weak_bisimF sim ot1 (observe t2) ->
      weak_bisimF sim ot1 (TauF t2).

Lemma unified_frontier_match_mono sim1 sim2 ot1 ot2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  unified_frontier_match sim1 ot1 ot2 ->
  unified_frontier_match sim2 ot1 ot2.
Proof.
  intros Hsim [HL HR]. split; intros hs Hf.
  - destruct (HL _ Hf) as [hs' [Hf' Hlift]].
    exists hs'. split; [exact Hf'|].
    eapply sem_lift_mono; [|exact Hlift].
    exact (frontier_head_rel_mono Hsim).
  - destruct (HR _ Hf) as [hs' [Hf' Hlift]].
    exists hs'. split; [exact Hf'|].
    eapply sem_lift_mono; [|exact Hlift].
    exact (frontier_head_rel_mono Hsim).
Qed.

Lemma weak_bisimF_monotone sim1 sim2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall ot1 ot2, weak_bisimF sim1 ot1 ot2 ->
    weak_bisimF sim2 ot1 ot2.
Proof.
  intros Hsim ot1 ot2 Hstep. induction Hstep.
  - eapply UWBFrontier; [exact H|exact H0|].
    eapply sem_lift_mono; [|exact H1].
    exact (frontier_head_rel_mono Hsim).
  - apply UWBTau.
    + exact (unified_frontier_match_mono Hsim H).
    + exact (Hsim _ _ H0).
  - apply UWBProb.
    + exact (unified_frontier_match_mono Hsim H).
    + eapply sem_lift_mono; [|exact H0].
      intros x y Hxy. exact (Hsim _ _ Hxy).
  - exact (UWBTauL IHHstep).
  - exact (UWBTauR IHHstep).
Qed.

Definition weak_bisim_body sim
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) :=
  weak_bisimF sim (observe t1) (observe t2).

Program Definition funified_weak :
    mon (ptree E MN R1 -> ptree E MN R2 -> Prop) :=
  {| body := weak_bisim_body |}.
Next Obligation.
  intros sim1 sim2 Hsub t1 t2 Hstep.
  eapply weak_bisimF_monotone; eauto.
Qed.

Definition weak_bisim : ptree E MN R1 -> ptree E MN R2 -> Prop :=
  gfp funified_weak.

Lemma weak_bisim_unfold t1 t2 :
  weak_bisim t1 t2 ->
  weak_bisimF weak_bisim (observe t1) (observe t2).
Proof.
  intro H. apply (gfp_pfp funified_weak) in H. exact H.
Qed.

Lemma weak_bisim_fold t1 t2 :
  weak_bisimF weak_bisim (observe t1) (observe t2) ->
  weak_bisim t1 t2.
Proof.
  intro H. unfold weak_bisim. apply (gfp_fp funified_weak). exact H.
Qed.

End UnifiedWeak.

Section UnifiedWeakReflexivity.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.

Lemma unified_head_rel_refl {R}
    (sim : ptree E MN R -> ptree E MN R -> Prop) :
  Reflexive sim -> Reflexive (frontier_head_rel eq sim).
Proof.
  intros Hsim h. destruct h as [r|X e k].
  - constructor. reflexivity.
  - constructor. intro x. apply Hsim.
Qed.

Lemma unified_frontier_match_refl {R}
    (sim : ptree E MN R -> ptree E MN R -> Prop)
    (Hhead : Reflexive (frontier_head_rel eq sim)) :
  forall ot, unified_frontier_match eq sim ot ot.
Proof.
  intro ot. split; intros hs Hf; exists hs; split; auto.
  all: apply sem_lift_refl; exact Hhead.
Qed.

Lemma weak_bisim_refl {R} :
  Reflexive (@weak_bisim E MN MF NI FI NC FC MX FO R R eq).
Proof.
  intro t. revert t. unfold weak_bisim.
  coinduction CH CIH. intro t.
  unfold weak_bisim_body. set (ot := observe t).
  change (weak_bisimF eq (elem CH) ot ot).
  destruct ot as [r|u|X e k|X mu k].
  - eapply UWBFrontier with
        (hs1 := sem_ret (FHRet r)) (hs2 := sem_ret (FHRet r)).
    + constructor.
    + constructor.
    + apply sem_lift_refl. apply unified_head_rel_refl. exact CIH.
  - apply UWBTau.
    + apply unified_frontier_match_refl.
      apply unified_head_rel_refl. exact CIH.
    + exact (CIH u).
  - eapply UWBFrontier with
        (hs1 := sem_ret (FHVis e k)) (hs2 := sem_ret (FHVis e k)).
    + constructor.
    + constructor.
    + apply sem_lift_refl. apply unified_head_rel_refl. exact CIH.
  - apply UWBProb.
    + apply unified_frontier_match_refl.
      apply unified_head_rel_refl. exact CIH.
    + apply sem_lift_refl. intro x. exact (CIH (k x)).
Qed.

Lemma weak_bisim_of_common_frontier {R}
    (t1 t2 : ptree E MN R) hs :
  frontier (observe t1) hs ->
  frontier (observe t2) hs ->
  @weak_bisim E MN MF NI FI NC FC MX FO R R eq t1 t2.
Proof.
  intros Hf1 Hf2. apply weak_bisim_fold.
  eapply UWBFrontier; [exact Hf1|exact Hf2|].
  apply sem_lift_refl. apply unified_head_rel_refl.
  exact weak_bisim_refl.
Qed.

End UnifiedWeakReflexivity.

Section UnifiedWeakResultMonotonicity.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.

Lemma frontier_head_rel_map {R1 R2}
    (RR SS : R1 -> R2 -> Prop)
    (sim sim' : ptree E MN R1 -> ptree E MN R2 -> Prop)
    (HRS : forall x y, RR x y -> SS x y)
    (Hsim : forall t1 t2, sim t1 t2 -> sim' t1 t2) :
  forall h1 h2,
    frontier_head_rel RR sim h1 h2 ->
    frontier_head_rel SS sim' h1 h2.
Proof.
  intros h1 h2 Hh. inversion Hh; subst; constructor.
  - exact (HRS _ _ H).
  - intro x. exact (Hsim _ _ (H x)).
Qed.

Lemma weak_bisim_rel_mono {R1 R2}
    (RR SS : R1 -> R2 -> Prop)
    (HRS : forall x y, RR x y -> SS x y) :
  forall t1 t2,
    @weak_bisim E MN MF NI FI NC FC MX FO R1 R2 RR t1 t2 ->
    @weak_bisim E MN MF NI FI NC FC MX FO R1 R2 SS t1 t2.
Proof.
  unfold weak_bisim at 2. coinduction CH CIH.
  intros t1 t2 Hrel. move: (weak_bisim_unfold Hrel)=> Hstep.
  unfold weak_bisim_body.
  set ot1 := observe t1 in Hstep |- *.
  set ot2 := observe t2 in Hstep |- *.
  change (weak_bisimF SS (elem CH) ot1 ot2).
  induction Hstep.
  - eapply UWBFrontier; [exact H|exact H0|].
    eapply sem_lift_mono; [|exact H1].
    exact (frontier_head_rel_map HRS CIH).
  - apply UWBTau.
    + destruct H as [HL HR]. split; intros hs Hf.
      * destruct (HL _ Hf) as [hs' [Hf' Hl]]. exists hs'. split; auto.
        eapply sem_lift_mono; [|exact Hl].
        exact (frontier_head_rel_map HRS CIH).
      * destruct (HR _ Hf) as [hs' [Hf' Hl]]. exists hs'. split; auto.
        eapply sem_lift_mono; [|exact Hl].
        exact (frontier_head_rel_map HRS CIH).
    + exact (CIH _ _ H0).
  - apply UWBProb.
    + destruct H as [HL HR]. split; intros hs Hf.
      * destruct (HL _ Hf) as [hs' [Hf' Hl]]. exists hs'. split; auto.
        eapply sem_lift_mono; [|exact Hl].
        exact (frontier_head_rel_map HRS CIH).
      * destruct (HR _ Hf) as [hs' [Hf' Hl]]. exists hs'. split; auto.
        eapply sem_lift_mono; [|exact Hl].
        exact (frontier_head_rel_map HRS CIH).
    + eapply sem_lift_mono; [|exact H0].
      intros x y Hxy. exact (CIH _ _ Hxy).
  - exact (UWBTauL IHHstep).
  - exact (UWBTauR IHHstep).
Qed.

End UnifiedWeakResultMonotonicity.

Section UnifiedWeakSymmetry.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.

Lemma frontier_head_rel_sym {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop)
    (sim' : ptree E MN R2 -> ptree E MN R1 -> Prop)
    (HR : forall x y, RR x y -> RR x y)
    (Hs : forall t1 t2, sim t1 t2 -> sim' t2 t1) :
  forall h1 h2, frontier_head_rel RR sim h1 h2 ->
    frontier_head_rel (fun y x => RR x y) sim' h2 h1.
Proof.
  intros h1 h2 Hh. inversion Hh; subst.
  - constructor. exact (HR _ _ H).
  - constructor. intro x. exact (Hs _ _ (H x)).
Qed.

Lemma weak_bisim_sym {R1 R2} (RR : R1 -> R2 -> Prop) :
  forall t1 t2,
    @weak_bisim E MN MF NI FI NC FC MX FO R1 R2 RR t1 t2 ->
    @weak_bisim E MN MF NI FI NC FC MX FO R2 R1
      (fun y x => RR x y) t2 t1.
Proof.
  unfold weak_bisim at 2. coinduction CH CIH.
  intros t1 t2 Hrel. move: (weak_bisim_unfold Hrel)=> Hstep.
  unfold weak_bisim_body.
  set ot1 := observe t1 in Hstep |- *.
  set ot2 := observe t2 in Hstep |- *.
  change (weak_bisimF (fun y x => RR x y) (elem CH) ot2 ot1).
  induction Hstep.
  - eapply UWBFrontier; [exact H0|exact H|].
    apply sem_lift_sym in H1.
    eapply sem_lift_mono; [|exact H1].
    intros h2 h1 Hh.
    eapply frontier_head_rel_sym; [exact (fun _ _ H => H)|exact CIH|exact Hh].
  - apply UWBTau.
    + destruct H as [HL HR]. split; intros hs Hf.
      * destruct (HR _ Hf) as [hs' [Hf' Hl]]. exists hs'. split; auto.
        apply sem_lift_sym in Hl. eapply sem_lift_mono; [|exact Hl].
        intros h2 h1 Hh. eapply frontier_head_rel_sym;
          [exact (fun _ _ H => H)|exact CIH|exact Hh].
      * destruct (HL _ Hf) as [hs' [Hf' Hl]]. exists hs'. split; auto.
        apply sem_lift_sym in Hl. eapply sem_lift_mono; [|exact Hl].
        intros h2 h1 Hh. eapply frontier_head_rel_sym;
          [exact (fun _ _ H => H)|exact CIH|exact Hh].
    + exact (CIH _ _ H0).
  - apply UWBProb.
    + destruct H as [HL HR]. split; intros hs Hf.
      * destruct (HR _ Hf) as [hs' [Hf' Hl]]. exists hs'. split; auto.
        apply sem_lift_sym in Hl. eapply sem_lift_mono; [|exact Hl].
        intros h2 h1 Hh. eapply frontier_head_rel_sym;
          [exact (fun _ _ H => H)|exact CIH|exact Hh].
      * destruct (HL _ Hf) as [hs' [Hf' Hl]]. exists hs'. split; auto.
        apply sem_lift_sym in Hl. eapply sem_lift_mono; [|exact Hl].
        intros h2 h1 Hh. eapply frontier_head_rel_sym;
          [exact (fun _ _ H => H)|exact CIH|exact Hh].
    + apply sem_lift_sym in H0. eapply sem_lift_mono; [|exact H0].
      intros y x Hxy. exact (CIH _ _ Hxy).
  - exact (UWBTauR IHHstep).
  - exact (UWBTauL IHHstep).
Qed.

Lemma weak_bisim_sym_eq {R} :
  Symmetric (@weak_bisim E MN MF NI FI NC FC MX FO R R eq).
Proof.
  intros t1 t2 H12.
  eapply weak_bisim_rel_mono.
  - intros x y Hxy. symmetry. exact Hxy.
  - exact (weak_bisim_sym H12).
Qed.

End UnifiedWeakSymmetry.
