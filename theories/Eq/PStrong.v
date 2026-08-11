Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program Morphisms.

From Coinduction Require Import all.
From mathcomp Require Import ssreflect ssrbool eqtype seq.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC RelLift.
From PTree.Eq Require Import EquNew.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Strong probabilistic bisimulation over an abstract probabilistic
    relation lifting.  Constructors are matched in lockstep: unlike
    [apweak], this relation neither discards a one-sided [Tau] nor collapses
    a finite probabilistic frontier.  It therefore serves as the strong
    baseline between structural [equ] and the weak frontier relations. *)

Section PStrong.

Context {E : Type -> Type}.
Context {M : Type -> Type}.
Context `{DI : DiscreteInterface M}.
Context `{PL : @ProbRelLift M DI}.
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
  | PSProb {X Y : eqType} (mu : M X) (nu : M Y) k1 k2 :
      prob_lift (fun x y => sim (k1 x) (k2 y)) mu nu ->
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
  - constructor. eapply prob_lift_mono; [|exact Hc].
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
Import EquNotations.

Context {E : Type -> Type}.
Context {M : Type -> Type}.
Context `{DI : DiscreteInterface M}.
Context `{PL : @ProbRelLift M DI}.

Lemma pstrong_refl {R : Type} :
  Reflexive (@pstrong E M DI PL R R eq).
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
    eapply prob_lift_mono.
    + move=> x y ->. apply CIH.
    + apply prob_lift_refl.
Qed.

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
    eapply prob_lift_mono.
    + move=> y x Hxy. exact: CIH Hxy.
    + exact: prob_lift_sym Hc.
Qed.

Lemma equ_implies_pstrong {R : Type} (t1 t2 : ptree E M R) :
  equ eq t1 t2 -> pstrong eq t1 t2.
Proof.
  revert t1 t2.
  unfold pstrong.
  coinduction CH CIH.
  move=> t1 t2 Huv.
  unfold equ in Huv.
  apply (gfp_pfp (fequ eq)) in Huv.
  cbn in Huv.
  set ot1 := observe t1 in Huv |- *.
  set ot2 := observe t2 in Huv |- *.
  change (pstrongF eq (` CH) ot1 ot2).
  inversion Huv as
      [r1 r2 HR | u1 u2 Hsim | X e k1 k2 Hk
       | X mu nu k1 k2 Hmu Hk]; subst.
  - constructor. reflexivity.
  - constructor. exact: CIH Hsim.
  - constructor=> x. exact: CIH (Hk x).
  - constructor.
    have Hdisc : disc_eq mu nu.
      apply (proj2 (disc_RTeq mu nu)).
      exact Hmu.
    have Hc : @prob_lift M DI PL X X eq mu nu :=
      @prob_lift_of_eq M DI PL X mu nu Hdisc.
    eapply (prob_lift_mono
      (R := eq)
      (S := fun x y => (` CH) (k1 x) (k2 y))).
    + move=> x y Hxy. subst y. exact: CIH (Hk x).
    + exact Hc.
Qed.

Lemma pstrong_ret_intro {R1 R2} (RR : R1 -> R2 -> Prop) r1 r2 :
  RR r1 r2 ->
  @pstrong E M DI PL R1 R2 RR (Ret r1) (Ret r2).
Proof. move=> Hrel. apply pstrong_fold. constructor. exact Hrel. Qed.

Lemma pstrong_ret_inv {R1 R2} (RR : R1 -> R2 -> Prop) r1 r2 :
  @pstrong E M DI PL R1 R2 RR (Ret r1) (Ret r2) -> RR r1 r2.
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

Lemma pstrong_prob_intro {R} {X Y : eqType}
    (mu : M X) (nu : M Y)
    (k1 : X -> ptree E M R) (k2 : Y -> ptree E M R) :
  prob_lift (fun x y => pstrong eq (k1 x) (k2 y)) mu nu ->
  pstrong eq (Prob mu k1) (Prob nu k2).
Proof. move=> Hrel. apply pstrong_fold. constructor. exact Hrel. Qed.

Lemma pstrong_prob_inv {R} {X Y : eqType}
    (mu : M X) (nu : M Y)
    (k1 : X -> ptree E M R) (k2 : Y -> ptree E M R) :
  pstrong eq (Prob mu k1) (Prob nu k2) ->
  prob_lift (fun x y => pstrong eq (k1 x) (k2 y)) mu nu.
Proof.
  move=> Hrel.
  move: (pstrong_unfold Hrel) => Hs.
  dependent destruction Hs.
  assumption.
Qed.

Context `{PC : @ComposableProbRelLift M DI PL}.

Inductive pstrong_trans_clo {R : Type} :
    ptree E M R -> ptree E M R -> Prop :=
  | PSTC t1 t2 t3 :
      pstrong eq t1 t2 ->
      pstrong eq t2 t3 ->
      pstrong_trans_clo t1 t3.

Lemma pstrong_trans {R : Type} :
  Transitive (@pstrong E M DI PL R R eq).
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
    have Hcomp :=
      prob_lift_comp (ComposableProbRelLift := PC) H H0.
    eapply (prob_lift_mono
      (R := fun a c => exists b,
        pstrong eq (k1 a) (k b) /\ pstrong eq (k b) (k2 c))
      (S := fun a c => (` CH) (k1 a) (k2 c))).
    + move=> a c Hac.
      apply CIH.
      destruct Hac as [b [Hab Hbc]].
      exact: (PSTC Hab Hbc).
    + exact Hcomp.
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
  Symmetric (@pstrong E M DI PL R R eq).
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
    eapply prob_lift_mono.
    + move=> y x Hxy. exact: CIH Hxy.
    + exact: prob_lift_sym Hc.
Qed.

#[global] Instance pstrong_equivalence {R : Type} :
  Equivalence (@pstrong E M DI PL R R eq).
Proof.
  split.
  - exact pstrong_refl.
  - exact pstrong_sym_eq.
  - exact pstrong_trans.
Qed.

End PStrongFacts.
