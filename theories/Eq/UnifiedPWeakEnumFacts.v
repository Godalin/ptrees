Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coinduction Require Import all.
From mathcomp Require Import ssreflect.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC EnumMap IndexedCoupling FrontierLift
  FrontierLiftEnum MeasureIteration MeasureIterationEnum TwoLevelMeasure
  TwoLevelMeasureEnum.
From PTree.Eq Require Import PWeakAbstract PWeakUnbounded UnifiedFrontierEnumFacts
  UnifiedPWeak.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum EnumMap.

(** Couplings are stable under the representation isomorphism between old
    [aphead] values and unified [frontier_head] values. *)
Lemma aphead_rel_to_frontier_head_rel {E R1 R2}
    (RR : R1 -> R2 -> Prop)
    (sim sim' : ptree E Enum R1 -> ptree E Enum R2 -> Prop)
    (Hsim : forall t1 t2, sim t1 t2 -> sim' t1 t2) :
  forall h1 h2,
    aphead_rel RR sim h1 h2 ->
    frontier_head_rel RR sim'
      (aphead_to_frontier_head h1)
      (aphead_to_frontier_head h2).
Proof.
  intros h1 h2 Hh. inversion Hh; subst; constructor; auto.
Qed.

Lemma enum_sem_lift_emap {A B C D}
    (S : A -> B -> Prop) (R : C -> D -> Prop)
    (f : A -> C) (g : B -> D) (mu : Enum A) (nu : Enum B) :
  (forall x y, S x y -> R (f x) (g y)) ->
  @meas_lift Enum Enum_MeasureInterface A B S mu nu ->
  @sem_lift Enum Enum_SemanticMeasureInterface C D R
    (emap f mu) (emap g nu).
Proof.
  move=> Hrel Hlift. cbn in Hlift |- *.
  rewrite !enum_prune_emap.
  exact: indexed_coupling_emap Hrel Hlift.
Qed.

Lemma aufrontier_match_to_unified {E R1 R2}
    (RR : R1 -> R2 -> Prop)
    (sim sim' : ptree E Enum R1 -> ptree E Enum R2 -> Prop)
    (Hsim : forall t1 t2, sim t1 t2 -> sim' t1 t2)
    ot1 ot2 :
  aufrontier_match RR sim ot1 ot2 ->
  @unified_frontier_match E Enum Enum
    Enum_SemanticMeasureInterface Enum_SemanticMeasureInterface
    Enum_MixedMeasureInterface Enum_SemanticOmegaInterface
    R1 R2 RR sim' ot1 ot2.
Proof.
  move=> [HL HR]. split.
  - move=> hs1 Hf1.
    move: (unified_frontier_to_aufrontier Hf1)=> Ho1.
    destruct (HL _ Ho1) as [hs2 [Ho2 Hlift]].
    exists (emap aphead_to_frontier_head hs2). split.
    + exact: aufrontier_to_unified_frontier Ho2.
    + move: (enum_sem_lift_emap
        (aphead_rel_to_frontier_head_rel Hsim) Hlift)=> Hnew.
      by rewrite emap_frontier_aphead_cancel in Hnew.
  - move=> hs2 Hf2.
    move: (unified_frontier_to_aufrontier Hf2)=> Ho2.
    destruct (HR _ Ho2) as [hs1 [Ho1 Hlift]].
    exists (emap aphead_to_frontier_head hs1). split.
    + exact: aufrontier_to_unified_frontier Ho1.
    + move: (enum_sem_lift_emap
        (aphead_rel_to_frontier_head_rel Hsim) Hlift)=> Hnew.
      by rewrite emap_frontier_aphead_cancel in Hnew.
Qed.

(** Every proof in the established Enum AST-aware relation denotes a proof
    in the backend-independent unified relation.  Thus existing unbounded
    examples remain usable while clients migrate away from [auweak]. *)
Theorem auweak_to_weak_bisim {E R1 R2} (RR : R1 -> R2 -> Prop) :
  forall t1 t2,
    @auweak E Enum Enum_MeasureInterface Enum_MeasureCoreLaws
      Enum_MeasureOmegaInterface R1 R2 RR t1 t2 ->
    @weak_bisim E Enum Enum
      Enum_SemanticMeasureInterface Enum_SemanticMeasureInterface
      Enum_SemanticMeasureCoreLaws Enum_SemanticMeasureCoreLaws
      Enum_MixedMeasureInterface Enum_SemanticOmegaInterface
      R1 R2 RR t1 t2.
Proof.
  unfold weak_bisim. coinduction CH CIH.
  intros t1 t2 Hold. move: (auweak_unfold Hold)=> Hstep.
  unfold weak_bisim_body.
  set ot1 := observe t1 in Hstep |- *.
  set ot2 := observe t2 in Hstep |- *.
  change (weak_bisimF RR (elem CH) ot1 ot2).
  induction Hstep.
  - eapply UWBFrontier.
    + exact: aufrontier_to_unified_frontier H.
    + exact: aufrontier_to_unified_frontier H0.
    + exact (enum_sem_lift_emap
        (aphead_rel_to_frontier_head_rel CIH) H1).
  - apply UWBTau.
    + exact (aufrontier_match_to_unified CIH H).
    + exact (CIH _ _ H0).
  - apply UWBProb.
    + exact (aufrontier_match_to_unified CIH H).
    + eapply sem_lift_mono; [|exact H0].
      intros x y Hxy. exact (CIH _ _ Hxy).
  - exact (UWBTauL IHHstep).
  - exact (UWBTauR IHHstep).
Qed.
