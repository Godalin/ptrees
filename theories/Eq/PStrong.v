(** Role: Canonical equational/hitting theory. Depends on Core and Prob; does not provide comparison or interpreter semantics. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program Morphisms.

From Coinduction Require Import all.
From mathcomp Require Import ssreflect ssrbool eqtype seq.

From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.FrontierLift PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
From PTree.Eq Require Import Shallow PStruct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "` R" := (elem R) (at level 10).

(** Syntax-sensitive comparison baseline, not the canonical behavioral
    equivalence.  Strong probabilistic bisimulation uses an abstract
    probabilistic
    relation lifting.  Constructors are matched in lockstep: this relation
    neither discards a one-sided [Tau] nor collapses an internal probability
    prefix.  It therefore remains the syntax-sensitive baseline for the
    canonical stable-hitting equivalence. *)

Section PStrong.

Context {E : Type -> Type}.
Context {M : Type -> Type}.
Context `{MI : SemanticMeasure M}.
Context `{MC : @SemanticMeasureCoreLaws M MI}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

Variant pstrongF
    (sim : ptree E M R1 -> ptree E M R2 -> Prop)
    : ptree' E M R1 -> ptree' E M R2 -> Prop :=
  | PSRet r1 r2 :
      RR r1 r2 ->
      pstrongF sim (RetF r1) (RetF r2)
  | PSTau t1 t2 :
      sim t1 t2 ->
      pstrongF sim (TauF t1) (TauF t2)
  | PSVis {X} (e : E X) k1 k2 :
      (forall x, sim (k1 x) (k2 x)) ->
      pstrongF sim (VisF e k1) (VisF e k2)
  | PSProb {X Y : Type} (mu : M X) (nu : M Y) k1 k2 :
      sem_lift (fun x y => sim (k1 x) (k2 y)) mu nu ->
      pstrongF sim (ProbF mu k1) (ProbF nu k2).

Definition pstrong_body
    (sim : ptree E M R1 -> ptree E M R2 -> Prop)
    (t1 : ptree E M R1) (t2 : ptree E M R2) : Prop :=
  pstrongF sim (observe t1) (observe t2).

Lemma pstrongF_monotone
    (sim1 sim2 : ptree E M R1 -> ptree E M R2 -> Prop) :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall ot1 ot2, pstrongF sim1 ot1 ot2 -> pstrongF sim2 ot1 ot2.
Proof.
  move=> Hmono t1 t2 Hs.
  inversion Hs as
      [r1 r2 HR | u1 u2 Hrel | X e k1 k2 Hk
       | X Y mu nu k1 k2 Hc]; subst.
  - constructor. exact HR.
  - constructor. exact: Hmono Hrel.
  - constructor=> x. exact: Hmono (Hk x).
  - constructor. eapply sem_lift_mono; [|exact Hc].
    move=> x y Hxy. exact: Hmono Hxy.
Qed.

Program Definition fpstrong :
    mon (ptree E M R1 -> ptree E M R2 -> Prop) :=
  {| body := pstrong_body |}.
Next Obligation.
  move=> sim1 sim2 Hsub t1 t2 Hs.
  eapply pstrongF_monotone.
  - exact Hsub.
  - exact Hs.
Qed.

Definition pstrong : ptree E M R1 -> ptree E M R2 -> Prop :=
  gfp fpstrong.

Lemma pstrong_unfold t1 t2 :
  pstrong t1 t2 -> pstrongF pstrong (observe t1) (observe t2).
Proof.
  move=> Hrel.
  apply (gfp_pfp fpstrong) in Hrel.
  exact Hrel.
Qed.

Lemma pstrong_fold t1 t2 :
  pstrongF pstrong (observe t1) (observe t2) -> pstrong t1 t2.
Proof.
  move=> Hrel.
  unfold pstrong.
  apply (gfp_fp fpstrong).
  exact Hrel.
Qed.

End PStrong.

Section PStrongFacts.
Context {E : Type -> Type}.
Context {M : Type -> Type}.
Context `{MI : SemanticMeasure M}.
Context `{MC : @SemanticMeasureCoreLaws M MI}.

Theorem pstruct_pstrong {R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : ptree E M R1) (t2 : ptree E M R2),
    pstruct RR t1 t2 -> pstrong RR t1 t2.
Proof.
  unfold pstrong. coinduction CH CIH. move=> t1 t2 Hrel.
  move: (pstruct_unfold Hrel)=> Hstep.
  set ot1 := observe t1 in Hstep |- *.
  set ot2 := observe t2 in Hstep |- *.
  change (pstrongF RR (` CH) ot1 ot2).
  inversion Hstep as
      [r1 r2 HR | u1 u2 Hsim | X e k1 k2 Hk
       | X mu k1 k2 Hk]; subst.
  - constructor. exact HR.
  - constructor. exact: CIH Hsim.
  - constructor=> x. exact: CIH (Hk x).
  - constructor.
    eapply sem_lift_mono.
    + move=> x y ->. exact: CIH (Hk y).
    + apply sem_lift_refl. unfold Reflexive. reflexivity.
Qed.

Lemma pstrong_refl {R : Type} :
  Reflexive (@pstrong E M MI MC R R eq).
Proof.
  red.
  unfold pstrong.
  coinduction CH CIH.
  move=> t.
  unfold pstrong_body.
  set ot := observe t.
  change (pstrongF eq (` CH) ot ot).
  destruct ot.
  - constructor. reflexivity.
  - constructor. apply CIH.
  - constructor=> x. apply CIH.
  - constructor.
    eapply sem_lift_mono.
    + move=> x y ->. apply CIH.
    + apply sem_lift_refl. unfold Reflexive. reflexivity.
Qed.

(** Intensional structural identity is contained in strong probabilistic
    bisimilarity.  This is the axiom-free left edge of the maintained
    hierarchy; the former coinductive [equ] development is legacy code and
    is not used by the probabilistic theory. *)
Lemma eq_pstrong {R : Type} (t1 t2 : ptree E M R) :
  t1 = t2 -> pstrong eq t1 t2.
Proof. move=> ->. exact: pstrong_refl. Qed.

Lemma pstrong_sym {R1 R2 : Type} (RR : R1 -> R2 -> Prop)
    (t1 : ptree E M R1) (t2 : ptree E M R2) :
  pstrong RR t1 t2 ->
  pstrong (fun y x => RR x y) t2 t1.
Proof.
  revert t1 t2.
  unfold pstrong at 2.
  coinduction CH CIH.
  move=> t1 t2 Huv.
  move: (pstrong_unfold Huv) => Hstep.
  set ot1 := observe t1 in Hstep |- *.
  set ot2 := observe t2 in Hstep |- *.
  change (pstrongF (fun y x => RR x y) (` CH) ot2 ot1).
  inversion Hstep as
      [r1 r2 HR | u1 u2 Hsim | X e k1 k2 Hk
       | X Y mu nu k1 k2 Hc]; subst.
  - constructor. exact HR.
  - constructor. exact: CIH Hsim.
  - constructor=> x. exact: CIH (Hk x).
  - constructor.
    eapply sem_lift_mono.
    + move=> y x Hxy. exact: CIH Hxy.
    + apply sem_lift_sym. exact Hc.
Qed.

Lemma pstrong_ret_intro {R1 R2} (RR : R1 -> R2 -> Prop) r1 r2 :
  RR r1 r2 ->
  @pstrong E M MI MC R1 R2 RR (Ret r1) (Ret r2).
Proof. move=> Hrel. apply pstrong_fold. constructor. exact Hrel. Qed.

Lemma pstrong_ret_inv {R1 R2} (RR : R1 -> R2 -> Prop) r1 r2 :
  @pstrong E M MI MC R1 R2 RR (Ret r1) (Ret r2) -> RR r1 r2.
Proof. move/pstrong_unfold. by inversion 1. Qed.

Lemma pstrong_vis_intro {R X} (e : E X)
    (k1 k2 : X -> ptree E M R) :
  (forall x, pstrong eq (k1 x) (k2 x)) ->
  pstrong eq (Vis e k1) (Vis e k2).
Proof. move=> Hrel. apply pstrong_fold. constructor. exact Hrel. Qed.

Lemma pstrong_vis_inv {R X} (e : E X)
    (k1 k2 : X -> ptree E M R) :
  pstrong eq (Vis e k1) (Vis e k2) ->
  forall x, pstrong eq (k1 x) (k2 x).
Proof.
  move=> Hrel.
  move: (pstrong_unfold Hrel) => Hs.
  dependent destruction Hs.
  assumption.
Qed.

Lemma pstrong_prob_intro {R} {X Y : Type}
    (mu : M X) (nu : M Y)
    (k1 : X -> ptree E M R) (k2 : Y -> ptree E M R) :
  sem_lift (fun x y => pstrong eq (k1 x) (k2 y)) mu nu ->
  pstrong eq (Prob mu k1) (Prob nu k2).
Proof. move=> Hrel. apply pstrong_fold. constructor. exact Hrel. Qed.

Lemma pstrong_prob_inv {R} {X Y : Type}
    (mu : M X) (nu : M Y)
    (k1 : X -> ptree E M R) (k2 : Y -> ptree E M R) :
  pstrong eq (Prob mu k1) (Prob nu k2) ->
  sem_lift (fun x y => pstrong eq (k1 x) (k2 y)) mu nu.
Proof.
  move=> Hrel.
  move: (pstrong_unfold Hrel) => Hs.
  dependent destruction Hs.
  assumption.
Qed.

Inductive pstrong_trans_clo {R : Type} :
    ptree E M R -> ptree E M R -> Prop :=
  | PSTC t1 t2 t3 :
      pstrong eq t1 t2 ->
      pstrong eq t2 t3 ->
      pstrong_trans_clo t1 t3.

Lemma pstrong_trans {R : Type} :
  Transitive (@pstrong E M MI MC R R eq).
Proof.
  move=> t1 t2 t3 H12 H23.
  have Hcomp : pstrong_trans_clo t1 t3.
    exact: (PSTC H12 H23).
  clear t2 H12 H23.
  revert t1 t3 Hcomp.
  unfold pstrong.
  coinduction CH CIH.
  move=> u w Hclo.
  inversion Hclo as [u' v w' Huv Hvw]; subst.
  move: (pstrong_unfold Huv) => Hstep1.
  move: (pstrong_unfold Hvw) => Hstep2.
  set ou := observe u in Hstep1 |- *.
  set ov := observe v in Hstep1 Hstep2.
  set ow := observe w in Hstep2 |- *.
  change (pstrongF eq (` CH) ou ow).
  destruct ov.
  - dependent destruction Hstep1.
    dependent destruction Hstep2.
    rewrite -x0 -x.
    constructor. reflexivity.
  - dependent destruction Hstep1.
    dependent destruction Hstep2.
    rewrite -x0 -x.
    constructor. apply CIH. exact: (PSTC H H0).
  - dependent destruction Hstep1.
    dependent destruction Hstep2.
    rewrite -x0 -x.
    constructor=> y. apply CIH. exact: (PSTC (H y) (H0 y)).
  - dependent destruction Hstep1.
    dependent destruction Hstep2.
    rewrite -x0 -x.
    constructor.
    have Hcomp := @sem_lift_comp M MI MC _ _ _ _ _ _ _ _ H H0.
    eapply sem_lift_mono; [|exact Hcomp].
    + move=> a c Hac.
      apply CIH.
      destruct Hac as [b [Hab Hbc]].
      exact: (PSTC Hab Hbc).
Qed.

Lemma pstrong_rel_mono {R1 R2 : Type}
    (RR SS : R1 -> R2 -> Prop)
    (HRS : forall x y, RR x y -> SS x y) :
  forall (t1 : ptree E M R1) (t2 : ptree E M R2),
    pstrong RR t1 t2 -> pstrong SS t1 t2.
Proof.
  unfold pstrong at 2.
  coinduction CH CIH.
  move=> t1 t2 Hrel.
  move: (pstrong_unfold Hrel) => Hstep.
  eapply pstrongF_monotone.
  - exact CIH.
  - inversion Hstep as
      [r1 r2 Hr | u1 u2 Hu | X e k1 k2 Hk
       | X Y mu nu k1 k2 Hc]; subst.
    + constructor. exact: HRS Hr.
    + constructor. exact Hu.
    + constructor. exact Hk.
    + constructor. exact Hc.
Qed.

Lemma pstrong_sym_eq {R : Type} :
  Symmetric (@pstrong E M MI MC R R eq).
Proof.
  move=> t1 t2 Hrel.
  revert t1 t2 Hrel.
  unfold pstrong at 2.
  coinduction CH CIH.
  move=> u v Huv.
  move: (pstrong_unfold Huv) => Hstep.
  set ou := observe u in Hstep |- *.
  set ov := observe v in Hstep |- *.
  change (pstrongF eq (` CH) ov ou).
  inversion Hstep as
      [r1 r2 Hr | u1 u2 Hu | X e k1 k2 Hk
       | X Y mu nu k1 k2 Hc]; subst.
  - constructor. reflexivity.
  - constructor. exact: CIH Hu.
  - constructor=> x. exact: CIH (Hk x).
  - constructor.
    eapply sem_lift_mono.
    + move=> y x Hxy. exact: CIH Hxy.
    + apply sem_lift_sym. exact Hc.
Qed.

#[global] Instance pstrong_equivalence {R : Type} :
  Equivalence (@pstrong E M MI MC R R eq).
Proof.
  split.
  - exact pstrong_refl.
  - exact pstrong_sym_eq.
  - exact pstrong_trans.
Qed.

#[global] Instance pstruct_pstrong_subrelation {R : Type} :
  subrelation (@pstruct E M R R eq) (@pstrong E M MI MC R R eq).
Proof. intros t1 t2. apply pstruct_pstrong. Qed.

End PStrongFacts.

Section PStrongBind.
Context {E : Type -> Type} {M : Type -> Type}
  `{MI : SemanticMeasure M}
  `{MC : @SemanticMeasureCoreLaws M MI}.
Context {A1 A2 B1 B2 : Type}.
Variables (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop).
Variables (k1 : A1 -> ptree E M B1) (k2 : A2 -> ptree E M B2).
Hypothesis Hcont : forall a1 a2, RA a1 a2 ->
  pstrong RB (k1 a1) (k2 a2).

Definition pstrong_bind_clo
    (u1 : ptree E M B1) (u2 : ptree E M B2) : Prop :=
  (exists t1 t2, u1 = PTree.bind t1 k1 /\
    u2 = PTree.bind t2 k2 /\ pstrong RA t1 t2) \/
  pstrong RB u1 u2.

Theorem pstrong_bind t1 t2 :
  pstrong RA t1 t2 ->
  pstrong RB (PTree.bind t1 k1) (PTree.bind t2 k2).
Proof.
  intro Hsource.
  assert (Hbind : forall u1 u2, pstrong_bind_clo u1 u2 ->
      pstrong RB u1 u2).
  { unfold pstrong. coinduction CH CIH.
    intros u1 u2 Hclo.
    destruct Hclo as [[s1 [s2 [-> [-> Hs]]]]|Hdone].
    - unfold pstrong_body.
      change (pstrongF RB (` CH)
        (observe (PTree.bind s1 k1)) (observe (PTree.bind s2 k2))).
      rewrite !observe_bind.
      pose proof (pstrong_unfold Hs) as Hstep.
      dependent destruction Hstep; cbn.
      + rewrite <- x0, <- x.
        pose proof (pstrong_unfold (Hcont H)) as Hret.
        eapply pstrongF_monotone; [|exact Hret].
        intros v1 v2 Hv. apply CIH. right. exact Hv.
      + rewrite <- x0, <- x. constructor. apply CIH. left.
        eexists _, _. repeat split; eauto.
      + rewrite <- x0, <- x. constructor=> y. apply CIH. left.
        eexists _, _. repeat split; eauto.
      + rewrite <- x0, <- x. constructor.
        eapply sem_lift_mono; [|exact H].
        intros a1 a2 Ha. apply CIH. left.
        eexists _, _. repeat split; eauto.
    - unfold pstrong_body.
      pose proof (pstrong_unfold Hdone) as Hstep.
      eapply pstrongF_monotone; [|exact Hstep].
      intros v1 v2 Hv. apply CIH. right. exact Hv. }
  apply Hbind. left. eexists _, _. repeat split; eauto.
Qed.

End PStrongBind.
