Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Morphisms Program.Equality.

From Coinduction Require Import all.
From mathcomp Require Import ssreflect ssrbool eqtype seq.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC Coupling IndexedCoupling.
From PTree.Eq Require Import PFrontier PWeak.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum Coupling IndexedCoupling.

Section PWeakFacts.

Context {E : Type -> Type}.

Lemma pweak_refl {R : Type} :
  Reflexive (@pweak E R R eq).
Proof.
  move=> t.
  revert t.
  unfold pweak.
  coinduction CH CIH.
  move=> t.
  unfold pweak_body.
  set ot := observe t.
  change (pweakF eq (elem CH) ot ot).
  destruct ot as [r|u|X e k|X mu k].
  - eapply PWFrontier.
    + constructor.
    + constructor.
    + apply indexed_coupling_refl.
      move=> h.
      destruct h as [r'|X' e' kh].
      * constructor. reflexivity.
      * constructor=> x. exact: CIH (kh x).
  - constructor.
    + apply frontier_match_refl.
      apply phead_rel_refl. exact CIH.
    + exact: CIH u.
  - eapply PWFrontier.
    + constructor.
    + constructor.
    + apply indexed_coupling_refl.
      move=> h.
      destruct h as [r'|X' e' kh].
      * constructor. reflexivity.
      * constructor=> x. exact: CIH (kh x).
  - constructor.
    + apply frontier_match_refl.
      apply phead_rel_refl. exact CIH.
    + eapply (coupling_mono
        (R := @eq X)
        (S := fun x y => elem CH (k x) (k y))).
      * move=> x y Hxy.
        subst y. exact: CIH (k x).
      * exact: coupling_refl mu.
Qed.

Lemma pweakF_sym {R1 R2} (RR : R1 -> R2 -> Prop)
    (sim : ptree E Enum R1 -> ptree E Enum R2 -> Prop)
    (sim' : ptree E Enum R2 -> ptree E Enum R1 -> Prop) :
  (forall t1 t2, sim t1 t2 -> sim' t2 t1) ->
  forall ot1 ot2,
    pweakF RR sim ot1 ot2 ->
    pweakF (fun y x => RR x y) sim' ot2 ot1.
Proof.
  move=> Hsim ot1 ot2 Hstep.
  induction Hstep.
  - eapply PWFrontier; [exact H0|exact H|].
    eapply indexed_coupling_mono.
    + move=> h2 h1 Hh.
      eapply phead_rel_sym; [exact Hsim|exact Hh].
    + exact: indexed_coupling_sym H1.
  - constructor.
    + eapply frontier_match_sym; [exact Hsim|exact H].
    + exact: Hsim H0.
  - constructor.
    + eapply frontier_match_sym; [exact Hsim|exact H].
    + eapply coupling_mono.
      * move=> y x Hxy. exact: Hsim Hxy.
      * exact: coupling_sym H0.
  - apply PWTauR. exact IHHstep.
  - apply PWTauL. exact IHHstep.
Qed.

Lemma pweak_sym {R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : ptree E Enum R1) (t2 : ptree E Enum R2),
    pweak RR t1 t2 ->
    pweak (fun y x => RR x y) t2 t1.
Proof.
  unfold pweak at 2.
  coinduction CH CIH.
  move=> t1 t2 Hrel.
  move: (pweak_unfold Hrel) => Hstep.
  unfold pweak_body.
  eapply pweakF_sym.
  - exact CIH.
  - exact Hstep.
Qed.

Lemma pweakF_frontier_l {R1 R2} (RR : R1 -> R2 -> Prop)
    (sim : ptree E Enum R1 -> ptree E Enum R2 -> Prop)
    ot1 ot2 hs1 :
  pweakF RR sim ot1 ot2 ->
  pfrontier ot1 hs1 ->
  exists hs2,
    pfrontier ot2 hs2 /\
    indexed_coupling (phead_rel RR sim) hs1 hs2.
Proof.
  move=> Hstep.
  move: hs1.
  induction Hstep; move=> hs Hfront.
  - have -> : hs = hs1.
      exact: pfrontier_deterministic Hfront H.
    by exists hs2.
  - exact: (proj1 H _ Hfront).
  - exact: (proj1 H _ Hfront).
  - dependent destruction Hfront.
    exact: IHHstep _ Hfront.
  - move: (IHHstep _ Hfront) => [hs2 [Hf2 Hc]].
    exists hs2. split=> //.
    exact: PFTau Hf2.
Qed.

Lemma pweakF_frontier_r {R1 R2} (RR : R1 -> R2 -> Prop)
    (sim : ptree E Enum R1 -> ptree E Enum R2 -> Prop)
    ot1 ot2 hs2 :
  pweakF RR sim ot1 ot2 ->
  pfrontier ot2 hs2 ->
  exists hs1,
    pfrontier ot1 hs1 /\
    indexed_coupling (phead_rel RR sim) hs1 hs2.
Proof.
  move=> Hstep.
  move: hs2.
  induction Hstep; move=> hs Hfront.
  - have -> : hs = hs2.
      exact: pfrontier_deterministic Hfront H0.
    by exists hs1.
  - exact: (proj2 H _ Hfront).
  - exact: (proj2 H _ Hfront).
  - move: (IHHstep _ Hfront) => [hs1 [Hf1 Hc]].
    exists hs1. split=> //.
    exact: PFTau Hf1.
  - dependent destruction Hfront.
    exact: IHHstep _ Hfront.
Qed.

Lemma pweakF_frontier_match {R1 R2} (RR : R1 -> R2 -> Prop)
    (sim : ptree E Enum R1 -> ptree E Enum R2 -> Prop)
    ot1 ot2 :
  pweakF RR sim ot1 ot2 ->
  frontier_match RR sim ot1 ot2.
Proof.
  move=> Hstep; split.
  - move=> hs1 Hf1.
    exact: pweakF_frontier_l Hstep Hf1.
  - move=> hs2 Hf2.
    exact: pweakF_frontier_r Hstep Hf2.
Qed.

Lemma pweak_frontier_l {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : ptree E Enum R1) (t2 : ptree E Enum R2) hs1 :
  pweak RR t1 t2 ->
  pfrontier (observe t1) hs1 ->
  exists hs2,
    pfrontier (observe t2) hs2 /\
    indexed_coupling (phead_rel RR (pweak RR)) hs1 hs2.
Proof.
  move=> Hrel Hfront.
  exact: pweakF_frontier_l (pweak_unfold Hrel) Hfront.
Qed.

Lemma pweak_frontier_r {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : ptree E Enum R1) (t2 : ptree E Enum R2) hs2 :
  pweak RR t1 t2 ->
  pfrontier (observe t2) hs2 ->
  exists hs1,
    pfrontier (observe t1) hs1 /\
    indexed_coupling (phead_rel RR (pweak RR)) hs1 hs2.
Proof.
  move=> Hrel Hfront.
  exact: pweakF_frontier_r (pweak_unfold Hrel) Hfront.
Qed.

Lemma tau_pweak_l {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : ptree E Enum R1) (t2 : ptree E Enum R2) :
  pweak RR t1 t2 -> pweak RR (Tau t1) t2.
Proof.
  move=> H.
  apply pweak_fold.
  apply PWTauL.
  exact: pweak_unfold H.
Qed.

Lemma tau_pweak_r {R1 R2} (RR : R1 -> R2 -> Prop)
    (t1 : ptree E Enum R1) (t2 : ptree E Enum R2) :
  pweak RR t1 t2 -> pweak RR t1 (Tau t2).
Proof.
  move=> H.
  apply pweak_fold.
  apply PWTauR.
  exact: pweak_unfold H.
Qed.

Lemma pweakF_rel_mono {R1 R2}
    (RR SS : R1 -> R2 -> Prop)
    (sim : ptree E Enum R1 -> ptree E Enum R2 -> Prop) :
  (forall x y, RR x y -> SS x y) ->
  forall ot1 ot2,
    pweakF RR sim ot1 ot2 ->
    pweakF SS sim ot1 ot2.
Proof.
  move=> HRS ot1 ot2 Hstep.
  induction Hstep.
  - eapply PWFrontier; [exact H | exact H0 |].
    eapply indexed_coupling_mono; [|exact H1].
    move=> h1 h2 Hh.
    exact: (phead_rel_rel_mono (RR := RR) (SS := SS) HRS Hh).
  - constructor.
    + exact: frontier_match_rel_mono HRS H.
    + exact H0.
  - constructor.
    + exact: frontier_match_rel_mono HRS H.
    + exact H0.
  - exact: PWTauL IHHstep.
  - exact: PWTauR IHHstep.
Qed.

Lemma pweak_rel_mono {R1 R2}
    (RR SS : R1 -> R2 -> Prop)
    (HRS : forall x y, RR x y -> SS x y) :
  forall (t1 : ptree E Enum R1) (t2 : ptree E Enum R2),
    pweak RR t1 t2 -> pweak SS t1 t2.
Proof.
  unfold pweak at 2.
  coinduction CH CIH.
  move=> t1 t2 Hrel.
  move: (pweak_unfold Hrel) => Hstep.
  eapply pweakF_rel_mono; [exact HRS|].
  eapply pweakF_monotone; [exact CIH|exact Hstep].
Qed.

End PWeakFacts.
