Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program.Equality.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import FrontierLift.
From PTree.Eq Require Import PWeakAbstract.

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
