Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Utf8 Program Morphisms Program.Equality.

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

Section UnifiedFrontierCoherentFacts.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}
  `{UC : @UnifiedFrontierCoherence E MN MF NI FI MX FO}.

Lemma weak_bisimF_frontier_l {R1 R2} (RR : R1 -> R2 -> Prop)
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop)
    ot1 ot2 hs1 :
  weak_bisimF RR sim ot1 ot2 -> frontier ot1 hs1 ->
  exists hs2, frontier ot2 hs2 /\
    sem_lift (frontier_head_rel RR sim) hs1 hs2.
Proof.
  intros Hstep. revert hs1.
  induction Hstep; intros hs Hfront.
  - have Heq : sem_eq hs hs1.
    { eapply unified_frontier_unique; eassumption. }
    exists hs2. split; [exact H0|].
    eapply sem_lift_proper_l; [|exact H1].
    apply sem_eq_sym. exact Heq.
  - exact (proj1 H _ Hfront).
  - exact (proj1 H _ Hfront).
  - exact (IHHstep _ (unified_frontier_tau_inv Hfront)).
  - destruct (IHHstep _ Hfront) as [hs2 [Hf2 Hlift]].
    exists hs2. split; [exact (UFTau Hf2)|exact Hlift].
Qed.

Lemma weak_bisimF_frontier_r {R1 R2} (RR : R1 -> R2 -> Prop)
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop)
    ot1 ot2 hs2 :
  weak_bisimF RR sim ot1 ot2 -> frontier ot2 hs2 ->
  exists hs1, frontier ot1 hs1 /\
    sem_lift (frontier_head_rel RR sim) hs1 hs2.
Proof.
  intros Hstep. revert hs2.
  induction Hstep; intros hs Hfront.
  - have Heq : sem_eq hs2 hs.
    { eapply unified_frontier_unique; eassumption. }
    exists hs1. split; [exact H|].
    eapply sem_lift_proper_r; [exact Heq|exact H1].
  - exact (proj2 H _ Hfront).
  - exact (proj2 H _ Hfront).
  - destruct (IHHstep _ Hfront) as [hs1 [Hf1 Hlift]].
    exists hs1. split; [exact (UFTau Hf1)|exact Hlift].
  - exact (IHHstep _ (unified_frontier_tau_inv Hfront)).
Qed.

Lemma weak_bisimF_frontier_match {R1 R2} (RR : R1 -> R2 -> Prop)
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop) ot1 ot2 :
  weak_bisimF RR sim ot1 ot2 -> unified_frontier_match RR sim ot1 ot2.
Proof.
  intro Hstep. split; intros hs Hfront.
  - exact (weak_bisimF_frontier_l Hstep Hfront).
  - exact (weak_bisimF_frontier_r Hstep Hfront).
Qed.

Lemma unified_frontier_match_tau {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) sim :
  unified_frontier_match RR sim (observe t1) (observe t2) ->
  unified_frontier_match RR sim (TauF t1) (TauF t2).
Proof.
  intros [HL HR]. split; intros hs Hf.
  - destruct (HL _ (unified_frontier_tau_inv Hf)) as [hs' [Hf' Hl]].
    exists hs'. split; [exact (UFTau Hf')|exact Hl].
  - destruct (HR _ (unified_frontier_tau_inv Hf)) as [hs' [Hf' Hl]].
    exists hs'. split; [exact (UFTau Hf')|exact Hl].
Qed.

Lemma unified_frontier_match_untau_l {R1 R2}
    (RR : R1 -> R2 -> Prop) (t1 : ptree E MN R1) ot2 sim :
  unified_frontier_match RR sim (TauF t1) ot2 ->
  unified_frontier_match RR sim (observe t1) ot2.
Proof.
  intros [HL HR]. split; intros hs Hf.
  - exact (HL _ (UFTau Hf)).
  - destruct (HR _ Hf) as [hs' [Hf' Hl]].
    exists hs'. split; [exact (unified_frontier_tau_inv Hf')|exact Hl].
Qed.

Lemma unified_frontier_match_untau_r {R1 R2}
    (RR : R1 -> R2 -> Prop) ot1 (t2 : ptree E MN R2) sim :
  unified_frontier_match RR sim ot1 (TauF t2) ->
  unified_frontier_match RR sim ot1 (observe t2).
Proof.
  intros [HL HR]. split; intros hs Hf.
  - destruct (HL _ Hf) as [hs' [Hf' Hl]].
    exists hs'. split; [exact (unified_frontier_tau_inv Hf')|exact Hl].
  - exact (HR _ (UFTau Hf)).
Qed.

Definition unified_relcomp {A B C}
    (R : A -> B -> Prop) (S : B -> C -> Prop) : A -> C -> Prop :=
  fun x z => exists y, R x y /\ S y z.

Lemma frontier_head_rel_comp {R1 R2 R3}
    (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
    (sim1 : ptree E MN R1 -> ptree E MN R2 -> Prop)
    (sim2 : ptree E MN R2 -> ptree E MN R3 -> Prop)
    (sim3 : ptree E MN R1 -> ptree E MN R3 -> Prop)
    (Hsim : forall t1 t2 t3,
      sim1 t1 t2 -> sim2 t2 t3 -> sim3 t1 t3) :
  forall h1 h2 h3,
    frontier_head_rel RR1 sim1 h1 h2 ->
    frontier_head_rel RR2 sim2 h2 h3 ->
    frontier_head_rel (unified_relcomp RR1 RR2) sim3 h1 h3.
Proof.
  intros h1 h2 h3 H12 H23.
  dependent destruction H12; dependent destruction H23.
  - constructor. eexists. split; eassumption.
  - constructor. intro x. eapply Hsim; eauto.
Qed.

Lemma unified_frontier_match_comp {R1 R2 R3}
    (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
    (sim1 : ptree E MN R1 -> ptree E MN R2 -> Prop)
    (sim2 : ptree E MN R2 -> ptree E MN R3 -> Prop)
    (sim3 : ptree E MN R1 -> ptree E MN R3 -> Prop)
    (Hsim : forall t1 t2 t3,
      sim1 t1 t2 -> sim2 t2 t3 -> sim3 t1 t3) :
  forall ot1 ot2 ot3,
    unified_frontier_match RR1 sim1 ot1 ot2 ->
    unified_frontier_match RR2 sim2 ot2 ot3 ->
    unified_frontier_match (unified_relcomp RR1 RR2) sim3 ot1 ot3.
Proof.
  intros ot1 ot2 ot3 [H12L H12R] [H23L H23R]. split.
  - intros hs1 Hf1.
    destruct (H12L _ Hf1) as [hs2 [Hf2 Hc12]].
    destruct (H23L _ Hf2) as [hs3 [Hf3 Hc23]].
    exists hs3. split; [exact Hf3|].
    eapply sem_lift_mono; [|eapply sem_lift_comp; eassumption].
    intros h1 h3 [h2 [Hh12 Hh23]].
    eapply frontier_head_rel_comp; eauto.
  - intros hs3 Hf3.
    destruct (H23R _ Hf3) as [hs2 [Hf2 Hc23]].
    destruct (H12R _ Hf2) as [hs1 [Hf1 Hc12]].
    exists hs1. split; [exact Hf1|].
    eapply sem_lift_mono; [|eapply sem_lift_comp; eassumption].
    intros h1 h3 [h2 [Hh12 Hh23]].
    eapply frontier_head_rel_comp; eauto.
Qed.

End UnifiedFrontierCoherentFacts.

Section UnifiedWeakCoherentTauInversion.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}
  `{UC : @UnifiedFrontierCoherence E MN MF NI FI MX FO}.

Lemma weak_bisimF_inv_tau_l_step {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (t1 : ptree E MN R1) (ot2 : ptree' E MN R2) :
  weak_bisimF RR (weak_bisim RR) (TauF t1) ot2 ->
  weak_bisimF RR (weak_bisim RR) (observe t1) ot2.
Proof.
  intros Hstep. remember (TauF t1) as lhs eqn:Elhs in Hstep.
  dependent induction Hstep; try discriminate.
  - dependent destruction Elhs.
    eapply UWBFrontier;
      [exact (unified_frontier_tau_inv H)|exact H0|exact H1].
  - injection Elhs as Et. subst t0.
    apply UWBTauR. exact (weak_bisim_unfold H0).
  - injection Elhs as Et. subst t0. exact Hstep.
  - apply UWBTauR. eapply IHHstep; eauto.
Qed.

Lemma weak_bisimF_inv_tau_r_step {R1 R2}
    (RR : R1 -> R2 -> Prop)
    (ot1 : ptree' E MN R1) (t2 : ptree E MN R2) :
  weak_bisimF RR (weak_bisim RR) ot1 (TauF t2) ->
  weak_bisimF RR (weak_bisim RR) ot1 (observe t2).
Proof.
  intros Hstep. remember (TauF t2) as rhs eqn:Erhs in Hstep.
  dependent induction Hstep; try discriminate.
  - dependent destruction Erhs.
    eapply UWBFrontier;
      [exact H|exact (unified_frontier_tau_inv H0)|exact H1].
  - injection Erhs as Et. subst t2.
    apply UWBTauL. exact (weak_bisim_unfold H0).
  - apply UWBTauL. eapply IHHstep; eauto.
  - injection Erhs as Et. subst t2. exact Hstep.
Qed.

Lemma weak_bisim_inv_tau_r {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) :
  weak_bisim RR t1 (Tau t2) -> weak_bisim RR t1 t2.
Proof.
  revert t1 t2. unfold weak_bisim at 2. coinduction CH CIH.
  intros t1' t2' Hrel. unfold weak_bisim_body.
  eapply (weak_bisimF_monotone
    (sim1 := weak_bisim RR) (sim2 := elem CH)).
  - intros u v Huv. apply (gfp_chain (b := funified_weak RR) CH). exact Huv.
  - exact (weak_bisimF_inv_tau_r_step (weak_bisim_unfold Hrel)).
Qed.

Lemma weak_bisim_inv_tau_l {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) :
  weak_bisim RR (Tau t1) t2 -> weak_bisim RR t1 t2.
Proof.
  revert t1 t2. unfold weak_bisim at 2. coinduction CH CIH.
  intros t1' t2' Hrel. unfold weak_bisim_body.
  eapply (weak_bisimF_monotone
    (sim1 := weak_bisim RR) (sim2 := elem CH)).
  - intros u v Huv. apply (gfp_chain (b := funified_weak RR) CH). exact Huv.
  - exact (weak_bisimF_inv_tau_l_step (weak_bisim_unfold Hrel)).
Qed.

Lemma weak_bisim_inv_tau {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) :
  weak_bisim RR (Tau t1) (Tau t2) -> weak_bisim RR t1 t2.
Proof.
  intro H. apply weak_bisim_inv_tau_l in H.
  exact (weak_bisim_inv_tau_r H).
Qed.

End UnifiedWeakCoherentTauInversion.

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
