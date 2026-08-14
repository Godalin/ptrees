Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Program.

From Coinduction Require Import all.
From PTree.Core Require Import PTreeDefinitionNew.
From mathcomp Require Import ssreflect.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import UnifiedFrontier UnifiedPWeak.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Targets of the primitive distribution-valued transition system.  A
    primitive node distribution lives in [MN]; stable weak observations live
    in [MF], so the two levels are not silently identified. *)
Variant unified_ppts_target (E : Type -> Type) (MN : Type -> Type) (R : Type) :=
  | UPPTSStable (h : frontier_head E MN R)
  | UPPTSInternal (t : ptree E MN R).

Arguments UPPTSStable {E MN R} _.
Arguments UPPTSInternal {E MN R} _.

Section PrimitiveAndWeakTransitions.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.

(** One operational transition.  In particular, [Prob] uses only the node
    backend [MN]; no semantic/frontier measure occurs recursively in PTree. *)
Inductive unified_ppts_step {R} :
    ptree' E MN R -> MN (unified_ppts_target E MN R) -> Prop :=
  | UPPTSStepReturn r :
      unified_ppts_step (RetF r) (sem_ret (UPPTSStable (FHRet r)))
  | UPPTSStepVisible {X} (e : E X) k :
      unified_ppts_step (VisF e k) (sem_ret (UPPTSStable (FHVis e k)))
  | UPPTSStepTau t :
      unified_ppts_step (TauF t) (sem_ret (UPPTSInternal t))
  | UPPTSStepProb {X} (mu : MN X) k :
      unified_ppts_step (ProbF mu k)
        (sem_bind mu (fun x => sem_ret (UPPTSInternal (k x)))).

(** Weak distribution-valued transitions.  This is an operational
    presentation of the single public frontier: primitive node steps are
    explicit, while unbounded closure is one omega-limit rule rather than a
    separate finite/unbounded datatype. *)
Inductive unified_ppts_weak {R} :
    ptree' E MN R -> MF (frontier_head E MN R) -> Prop :=
  | UPPTSWeakReturn r targets :
      unified_ppts_step (RetF r) targets ->
      unified_ppts_weak (RetF r) (sem_ret (FHRet r))
  | UPPTSWeakVisible {X} (e : E X) k targets :
      unified_ppts_step (VisF e k) targets ->
      unified_ppts_weak (VisF e k) (sem_ret (FHVis e k))
  | UPPTSWeakTau t targets hs :
      unified_ppts_step (TauF t) targets ->
      unified_ppts_weak (observe t) hs ->
      unified_ppts_weak (TauF t) hs
  | UPPTSWeakProb {X} (mu : MN X) k targets
      (front : X -> MF (frontier_head E MN R)) (Good : X -> Prop) :
      unified_ppts_step (ProbF mu k) targets ->
      sem_ae mu Good ->
      (forall x, Good x -> unified_ppts_weak (observe (k x)) (front x)) ->
      unified_ppts_weak (ProbF mu k) (mixed_bind mu front)
  | UPPTSWeakIter {I}
      (step : I -> ptree E MN (I + R))
      (transition : I -> MN (I + R)) i out :
      (forall j, unified_ppts_weak (observe (step j))
        (mixed_bind (transition j)
          (fun next => sem_ret (FHRet next)))) ->
      mixed_iter transition i out -> sem_total out ->
      unified_ppts_weak (observe (PTree.iter step i))
        (sem_bind out (fun r => sem_ret (FHRet r)))
  | UPPTSWeakBind {A} (t : ptree E MN A) (k : A -> ptree E MN R)
      hs (front : A -> MF (frontier_head E MN R)) :
      unified_ppts_weak (observe t) hs ->
      (forall a, unified_ppts_weak (observe (k a)) (front a)) ->
      unified_ppts_weak (observe (PTree.bind t k))
        (sem_bind hs (frontier_head_bind_front k front))
  | UPPTSWeakNestedIter {I}
      (step : I -> ptree E MN (I + R))
      (transition : I -> MN (I + R)) i out :
      (forall j, unified_ppts_weak (observe (step j))
        (mixed_bind (transition j)
          (fun next => sem_ret (FHRet next)))) ->
      mixed_iter transition i out -> sem_total out ->
      unified_ppts_weak (observe (PTree.iter step i))
        (sem_bind out (fun r => sem_ret (FHRet r))).

Theorem frontier_to_unified_ppts_weak {R}
    (ot : ptree' E MN R) hs :
  frontier ot hs -> unified_ppts_weak ot hs.
Proof.
  move=> Hf. induction Hf.
  - apply UPPTSWeakReturn with
      (targets := sem_ret (UPPTSStable (FHRet r))). constructor.
  - apply UPPTSWeakVisible with
      (targets := sem_ret (UPPTSStable (FHVis e k))). constructor.
  - apply UPPTSWeakTau with
      (targets := sem_ret (UPPTSInternal t)); [constructor|exact IHHf].
  - apply UPPTSWeakProb with
      (targets := sem_bind mu (fun x => sem_ret (UPPTSInternal (k x))))
      (Good := Good); [constructor|exact H|exact H1].
  - eapply UPPTSWeakIter; eauto.
  - eapply UPPTSWeakBind; eauto.
  - eapply UPPTSWeakNestedIter; eauto.
Qed.

Theorem unified_ppts_weak_to_frontier {R}
    (ot : ptree' E MN R) hs :
  unified_ppts_weak ot hs -> frontier ot hs.
Proof.
  move=> Hw. induction Hw.
  - constructor.
  - constructor.
  - exact (UFTau IHHw).
  - exact (UFProb H0 H2).
  - eapply UFIter; eauto.
  - eapply UFBind; eauto.
  - eapply UFNestedIter; eauto.
Qed.

Theorem unified_ppts_weak_iff_frontier {R}
    (ot : ptree' E MN R) hs :
  unified_ppts_weak ot hs <-> frontier ot hs.
Proof.
  split; [apply unified_ppts_weak_to_frontier|
          apply frontier_to_unified_ppts_weak].
Qed.

End PrimitiveAndWeakTransitions.

Section GuardedBisimulation.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

Definition unified_ppts_match
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop)
    (ot1 : ptree' E MN R1) (ot2 : ptree' E MN R2) : Prop :=
  (forall hs1, unified_ppts_weak ot1 hs1 -> exists hs2,
      unified_ppts_weak ot2 hs2 /\
      sem_lift (frontier_head_rel RR sim) hs1 hs2) /\
  (forall hs2, unified_ppts_weak ot2 hs2 -> exists hs1,
      unified_ppts_weak ot1 hs1 /\
      sem_lift (frontier_head_rel RR sim) hs1 hs2).

Lemma unified_ppts_match_mono sim1 sim2 ot1 ot2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  unified_ppts_match sim1 ot1 ot2 ->
  unified_ppts_match sim2 ot1 ot2.
Proof.
  intros Hsim [HL HR]. split; intros hs Hw.
  - destruct (HL _ Hw) as [hs' [Hw' Hlift]].
    exists hs'. split; [exact Hw'|].
    eapply sem_lift_mono; [|exact Hlift].
    exact (frontier_head_rel_mono Hsim).
  - destruct (HR _ Hw) as [hs' [Hw' Hlift]].
    exists hs'. split; [exact Hw'|].
    eapply sem_lift_mono; [|exact Hlift].
    exact (frontier_head_rel_mono Hsim).
Qed.

Lemma frontier_match_to_unified_ppts_match sim ot1 ot2 :
  unified_frontier_match RR sim ot1 ot2 ->
  unified_ppts_match sim ot1 ot2.
Proof.
  intros [HL HR]. split; intros hs Hw.
  - destruct (HL _ (unified_ppts_weak_to_frontier Hw))
      as [hs' [Hf' Hlift]].
    exists hs'. split; [exact (frontier_to_unified_ppts_weak Hf')|exact Hlift].
  - destruct (HR _ (unified_ppts_weak_to_frontier Hw))
      as [hs' [Hf' Hlift]].
    exists hs'. split; [exact (frontier_to_unified_ppts_weak Hf')|exact Hlift].
Qed.

Lemma unified_ppts_match_to_frontier_match sim ot1 ot2 :
  unified_ppts_match sim ot1 ot2 ->
  unified_frontier_match RR sim ot1 ot2.
Proof.
  intros [HL HR]. split; intros hs Hf.
  - destruct (HL _ (frontier_to_unified_ppts_weak Hf))
      as [hs' [Hw' Hlift]].
    exists hs'. split; [exact (unified_ppts_weak_to_frontier Hw')|exact Hlift].
  - destruct (HR _ (frontier_to_unified_ppts_weak Hf))
      as [hs' [Hw' Hlift]].
    exists hs'. split; [exact (unified_ppts_weak_to_frontier Hw')|exact Hlift].
Qed.

(** Divergence-sensitive bisimulation on the distribution-valued PTS.  The
    guarded residual rules are essential: a transition-only relation would
    equate any two programs with no AST weak transition vacuously. *)
Inductive unified_ppts_bisimF
    (sim : ptree E MN R1 -> ptree E MN R2 -> Prop) :
    ptree' E MN R1 -> ptree' E MN R2 -> Prop :=
  | UPPTSBFrontier ot1 ot2 hs1 hs2 :
      unified_ppts_weak ot1 hs1 -> unified_ppts_weak ot2 hs2 ->
      sem_lift (frontier_head_rel RR sim) hs1 hs2 ->
      unified_ppts_bisimF sim ot1 ot2
  | UPPTSBTau t1 t2 :
      unified_ppts_match sim (TauF t1) (TauF t2) ->
      sim t1 t2 -> unified_ppts_bisimF sim (TauF t1) (TauF t2)
  | UPPTSBProb {X Y} (mu : MN X) (nu : MN Y) k1 k2 :
      unified_ppts_match sim (ProbF mu k1) (ProbF nu k2) ->
      sem_lift (fun x y => sim (k1 x) (k2 y)) mu nu ->
      unified_ppts_bisimF sim (ProbF mu k1) (ProbF nu k2)
  | UPPTSBTauL t1 ot2 :
      unified_ppts_bisimF sim (observe t1) ot2 ->
      unified_ppts_bisimF sim (TauF t1) ot2
  | UPPTSBTauR ot1 t2 :
      unified_ppts_bisimF sim ot1 (observe t2) ->
      unified_ppts_bisimF sim ot1 (TauF t2).

Lemma unified_ppts_bisimF_monotone sim1 sim2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall ot1 ot2, unified_ppts_bisimF sim1 ot1 ot2 ->
    unified_ppts_bisimF sim2 ot1 ot2.
Proof.
  intros Hsim ot1 ot2 Hstep. induction Hstep.
  - eapply UPPTSBFrontier; [exact H|exact H0|].
    eapply sem_lift_mono; [|exact H1].
    exact (frontier_head_rel_mono Hsim).
  - apply UPPTSBTau.
    + exact (unified_ppts_match_mono Hsim H).
    + exact (Hsim _ _ H0).
  - apply UPPTSBProb.
    + exact (unified_ppts_match_mono Hsim H).
    + eapply sem_lift_mono; [|exact H0].
      intros x y Hxy. exact (Hsim _ _ Hxy).
  - exact (UPPTSBTauL IHHstep).
  - exact (UPPTSBTauR IHHstep).
Qed.

Definition unified_ppts_bisim_body sim
    (t1 : ptree E MN R1) (t2 : ptree E MN R2) :=
  unified_ppts_bisimF sim (observe t1) (observe t2).

Program Definition funified_ppts_bisim :
    mon (ptree E MN R1 -> ptree E MN R2 -> Prop) :=
  {| body := unified_ppts_bisim_body |}.
Next Obligation.
  intros sim1 sim2 Hsub t1 t2 Hstep.
  eapply unified_ppts_bisimF_monotone; eauto.
Qed.

Definition unified_ppts_bisim :
    ptree E MN R1 -> ptree E MN R2 -> Prop :=
  gfp funified_ppts_bisim.

Lemma unified_ppts_bisim_unfold t1 t2 :
  unified_ppts_bisim t1 t2 ->
  unified_ppts_bisimF unified_ppts_bisim (observe t1) (observe t2).
Proof.
  intro H. apply (gfp_pfp funified_ppts_bisim) in H. exact H.
Qed.

Lemma unified_ppts_bisim_fold t1 t2 :
  unified_ppts_bisimF unified_ppts_bisim (observe t1) (observe t2) ->
  unified_ppts_bisim t1 t2.
Proof.
  intro H. unfold unified_ppts_bisim.
  apply (gfp_fp funified_ppts_bisim). exact H.
Qed.

Theorem weak_bisim_to_unified_ppts_bisim :
  forall t1 t2, weak_bisim RR t1 t2 -> unified_ppts_bisim t1 t2.
Proof.
  unfold unified_ppts_bisim. coinduction CH CIH.
  intros t1 t2 Hrel. move: (weak_bisim_unfold Hrel)=> Hstep.
  unfold unified_ppts_bisim_body.
  set ot1 := observe t1 in Hstep |- *.
  set ot2 := observe t2 in Hstep |- *.
  change (unified_ppts_bisimF (elem CH) ot1 ot2).
  induction Hstep.
  - eapply UPPTSBFrontier.
    + exact (frontier_to_unified_ppts_weak H).
    + exact (frontier_to_unified_ppts_weak H0).
    + eapply sem_lift_mono; [|exact H1].
      exact (frontier_head_rel_mono CIH).
  - apply UPPTSBTau.
    + apply frontier_match_to_unified_ppts_match.
      exact (unified_frontier_match_mono CIH H).
    + exact (CIH _ _ H0).
  - apply UPPTSBProb.
    + apply frontier_match_to_unified_ppts_match.
      exact (unified_frontier_match_mono CIH H).
    + eapply sem_lift_mono; [|exact H0].
      intros x y Hxy. exact (CIH _ _ Hxy).
  - exact (UPPTSBTauL IHHstep).
  - exact (UPPTSBTauR IHHstep).
Qed.

Theorem unified_ppts_bisim_to_weak_bisim :
  forall t1 t2, unified_ppts_bisim t1 t2 -> weak_bisim RR t1 t2.
Proof.
  unfold weak_bisim. coinduction CH CIH.
  intros t1 t2 Hrel. move: (unified_ppts_bisim_unfold Hrel)=> Hstep.
  unfold weak_bisim_body.
  set ot1 := observe t1 in Hstep |- *.
  set ot2 := observe t2 in Hstep |- *.
  change (weak_bisimF RR (elem CH) ot1 ot2).
  induction Hstep.
  - eapply UWBFrontier.
    + exact (unified_ppts_weak_to_frontier H).
    + exact (unified_ppts_weak_to_frontier H0).
    + eapply sem_lift_mono; [|exact H1].
      exact (frontier_head_rel_mono CIH).
  - apply UWBTau.
    + apply unified_ppts_match_to_frontier_match.
      exact (unified_ppts_match_mono CIH H).
    + exact (CIH _ _ H0).
  - apply UWBProb.
    + apply unified_ppts_match_to_frontier_match.
      exact (unified_ppts_match_mono CIH H).
    + eapply sem_lift_mono; [|exact H0].
      intros x y Hxy. exact (CIH _ _ Hxy).
  - exact (UWBTauL IHHstep).
  - exact (UWBTauR IHHstep).
Qed.

Theorem weak_bisim_iff_unified_ppts_bisim t1 t2 :
  weak_bisim RR t1 t2 <-> unified_ppts_bisim t1 t2.
Proof.
  split; [apply weak_bisim_to_unified_ppts_bisim|
          apply unified_ppts_bisim_to_weak_bisim].
Qed.

End GuardedBisimulation.
