Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program Morphisms.

From Coinduction Require Import all.
From mathcomp Require Import ssreflect ssrbool eqtype seq.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import FrontierLift.
From PTree.Eq Require Import ShallowNew.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "` R" := (elem R) (at level 10).

(** A purely structural lockstep relation.  Probability nodes must expose
    the same sampling measure and sampled type; only their continuations may
    differ recursively.  This replaces the axiom-bearing legacy [equ] as the
    maintained coinductive structural baseline. *)
Section PStructural.

Context {E : Type -> Type} {M : Type -> Type}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

Variant pstructuralF
    (sim : ptree E M R1 -> ptree E M R2 -> Prop) :
    ptree' E M R1 -> ptree' E M R2 -> Prop :=
  | PStRet r1 r2 : RR r1 r2 ->
      pstructuralF sim (RetF r1) (RetF r2)
  | PStTau t1 t2 : sim t1 t2 ->
      pstructuralF sim (TauF t1) (TauF t2)
  | PStVis {X} (e : E X) k1 k2 :
      (forall x, sim (k1 x) (k2 x)) ->
      pstructuralF sim (VisF e k1) (VisF e k2)
  | PStProb {X : Type} (mu : M X) k1 k2 :
      (forall x, sim (k1 x) (k2 x)) ->
      pstructuralF sim (ProbF mu k1) (ProbF mu k2).

Definition pstructural_body
    (sim : ptree E M R1 -> ptree E M R2 -> Prop)
    (t1 : ptree E M R1) (t2 : ptree E M R2) : Prop :=
  pstructuralF sim (observe t1) (observe t2).

Lemma pstructuralF_monotone sim1 sim2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall ot1 ot2, pstructuralF sim1 ot1 ot2 ->
    pstructuralF sim2 ot1 ot2.
Proof.
  move=> Hmono ot1 ot2 Hs. inversion Hs; subst.
  - constructor. exact H.
  - constructor. exact: Hmono H.
  - constructor=> x. exact: Hmono (H x).
  - constructor=> x. exact: Hmono (H x).
Qed.

Program Definition fpstructural :
    mon (ptree E M R1 -> ptree E M R2 -> Prop) :=
  {| body := pstructural_body |}.
Next Obligation.
  move=> sim1 sim2 Hsub t1 t2 Hs.
  eapply pstructuralF_monotone.
  - exact Hsub.
  - exact Hs.
Qed.

Definition pstructural : ptree E M R1 -> ptree E M R2 -> Prop :=
  gfp fpstructural.

Lemma pstructural_unfold t1 t2 :
  pstructural t1 t2 ->
  pstructuralF pstructural (observe t1) (observe t2).
Proof. move=> H. apply (gfp_pfp fpstructural) in H. exact H. Qed.

Lemma pstructural_fold t1 t2 :
  pstructuralF pstructural (observe t1) (observe t2) ->
  pstructural t1 t2.
Proof. move=> H. unfold pstructural. apply (gfp_fp fpstructural). exact H. Qed.

End PStructural.

Section PStructuralFacts.
Context {E : Type -> Type} {M : Type -> Type}.

Lemma pstructural_refl {R : Type} :
  Reflexive (@pstructural E M R R eq).
Proof.
  red. unfold pstructural. coinduction CH CIH. move=> t.
  unfold pstructural_body.
  set ot := observe t.
  change (pstructuralF eq (` CH) ot ot).
  destruct ot.
  - constructor. reflexivity.
  - constructor. apply CIH.
  - constructor=> x. apply CIH.
  - constructor=> x. apply CIH.
Qed.

Lemma eq_pstructural {R : Type} (t1 t2 : ptree E M R) :
  t1 = t2 -> pstructural eq t1 t2.
Proof. move=> ->. exact: pstructural_refl. Qed.

(** Structural equality only inspects one observation at a time.  Hence an
    exact equality of observations is enough even when the coinductive tree
    values themselves are not judgmentally equal. *)
Lemma observe_eq_pstructural {R : Type} (t1 t2 : ptree E M R) :
  observe t1 = observe t2 -> pstructural eq t1 t2.
Proof.
  intro Hobs. apply pstructural_fold. rewrite Hobs.
  apply pstructural_unfold. apply pstructural_refl.
Qed.

Lemma pstructural_sym {R : Type} :
  Symmetric (@pstructural E M R R eq).
Proof.
  move=> t1 t2. revert t1 t2.
  unfold pstructural at 2. coinduction CH CIH.
  move=> t1 t2 Hrel. move: (pstructural_unfold Hrel)=> Hstep.
  set ot1 := observe t1 in Hstep |- *.
  set ot2 := observe t2 in Hstep |- *.
  change (pstructuralF eq (` CH) ot2 ot1).
  inversion Hstep as
      [r1 r2 HR | u1 u2 Hsim | X e k1 k2 Hk
       | X mu k1 k2 Hk]; subst.
  - constructor. reflexivity.
  - constructor. exact: CIH Hsim.
  - constructor=> x. exact: CIH (Hk x).
  - constructor=> x. exact: CIH (Hk x).
Qed.

Inductive pstructural_trans_clo {R : Type} :
    ptree E M R -> ptree E M R -> Prop :=
  | PStTC t1 t2 t3 :
      pstructural eq t1 t2 ->
      pstructural eq t2 t3 ->
      pstructural_trans_clo t1 t3.

Lemma pstructural_trans {R : Type} :
  Transitive (@pstructural E M R R eq).
Proof.
  move=> t1 t2 t3 H12 H23.
  have Hcomp : pstructural_trans_clo t1 t3 := PStTC H12 H23.
  clear t2 H12 H23. revert t1 t3 Hcomp.
  unfold pstructural. coinduction CH CIH.
  move=> u w Hclo. inversion Hclo as [u' v w' Huv Hvw]; subst.
  move: (pstructural_unfold Huv)=> Hstep1.
  move: (pstructural_unfold Hvw)=> Hstep2.
  set ou := observe u in Hstep1 |- *.
  set ov := observe v in Hstep1 Hstep2.
  set ow := observe w in Hstep2 |- *.
  change (pstructuralF eq (` CH) ou ow).
  destruct ov.
  - dependent destruction Hstep1. dependent destruction Hstep2.
    rewrite -x0 -x. constructor. reflexivity.
  - dependent destruction Hstep1. dependent destruction Hstep2.
    rewrite -x0 -x. constructor. apply CIH. exact: PStTC H H0.
  - dependent destruction Hstep1. dependent destruction Hstep2.
    rewrite -x0 -x. constructor=> y. apply CIH.
    exact: PStTC (H y) (H0 y).
  - dependent destruction Hstep1. dependent destruction Hstep2.
    rewrite -x0 -x. constructor=> y. apply CIH.
    exact: PStTC (H y) (H0 y).
Qed.

#[global] Instance pstructural_equivalence {R : Type} :
  Equivalence (@pstructural E M R R eq).
Proof.
  split.
  - exact pstructural_refl.
  - exact pstructural_sym.
  - exact pstructural_trans.
Qed.

End PStructuralFacts.

Section PStructuralBind.
Context {E : Type -> Type} {M : Type -> Type}.
Context {A1 A2 B1 B2 : Type}.
Variables (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop).
Variables (k1 : A1 -> ptree E M B1) (k2 : A2 -> ptree E M B2).
Hypothesis Hcont : forall a1 a2, RA a1 a2 ->
  pstructural RB (k1 a1) (k2 a2).

Definition pstructural_bind_clo
    (u1 : ptree E M B1) (u2 : ptree E M B2) : Prop :=
  (exists t1 t2, u1 = PTree.bind t1 k1 /\
    u2 = PTree.bind t2 k2 /\ pstructural RA t1 t2) \/
  pstructural RB u1 u2.

Theorem pstructural_bind t1 t2 :
  pstructural RA t1 t2 ->
  pstructural RB (PTree.bind t1 k1) (PTree.bind t2 k2).
Proof.
  intro Hsource.
  assert (Hstrong : forall u1 u2, pstructural_bind_clo u1 u2 ->
      pstructural RB u1 u2).
  { unfold pstructural. coinduction CH CIH.
    intros u1 u2 Hclo.
    destruct Hclo as [[s1 [s2 [-> [-> Hs]]]]|Hdone].
    - unfold pstructural_body.
      change (pstructuralF RB (` CH)
        (observe (PTree.bind s1 k1)) (observe (PTree.bind s2 k2))).
      rewrite !observe_bind.
      pose proof (pstructural_unfold Hs) as Hstep.
      dependent destruction Hstep; cbn.
      + rewrite <- x0, <- x.
        pose proof (pstructural_unfold (Hcont H)) as Hret.
        eapply pstructuralF_monotone; [|exact Hret].
        intros v1 v2 Hv. apply CIH. right. exact Hv.
      + rewrite <- x0, <- x. constructor. apply CIH. left.
        eexists _, _. repeat split; eauto.
      + rewrite <- x0, <- x. constructor=> y. apply CIH. left.
        eexists _, _. repeat split; eauto.
      + rewrite <- x0, <- x. constructor=> y. apply CIH. left.
        eexists _, _. repeat split; eauto.
    - unfold pstructural_body.
      pose proof (pstructural_unfold Hdone) as Hstep.
      eapply pstructuralF_monotone; [|exact Hstep].
      intros x y Hxy. apply CIH. right. exact Hxy. }
  apply Hstrong. left. eexists _, _. repeat split; eauto.
Qed.

End PStructuralBind.

Section PStructuralBindAssoc.
Context {E : Type -> Type} {M : Type -> Type}.
Context {A B C : Type}.
Variables (k : A -> ptree E M B) (h : B -> ptree E M C).

Definition pstructural_bind_assoc_clo
    (u v : ptree E M C) : Prop :=
  (exists t, u = PTree.bind (PTree.bind t k) h /\
    v = PTree.bind t (fun a => PTree.bind (k a) h)) \/
  pstructural eq u v.

Theorem pstructural_bind_assoc (t : ptree E M A) :
  pstructural eq
    (PTree.bind (PTree.bind t k) h)
    (PTree.bind t (fun a => PTree.bind (k a) h)).
Proof.
  assert (Hstrong : forall u v, pstructural_bind_assoc_clo u v ->
      pstructural eq u v).
  { unfold pstructural. coinduction CH CIH.
    intros u v Hclo.
    destruct Hclo as [[s [-> ->]]|Hdone].
    - unfold pstructural_body.
      change (pstructuralF eq (` CH)
        (observe (PTree.bind (PTree.bind s k) h))
        (observe (PTree.bind s (fun a => PTree.bind (k a) h)))).
      rewrite !observe_bind.
      remember (observe s) as ot eqn:Hot.
      destruct ot as [a|s'|X e c|X mu c]; cbn.
      + pose proof (pstructural_refl
          (PTree.bind (k a) h)) as Hrefl.
        pose proof (pstructural_unfold Hrefl) as Hstep.
        eapply pstructuralF_monotone; [|exact Hstep].
        intros x y Hxy. apply CIH. right. exact Hxy.
      + constructor. apply CIH. left. eexists. split; reflexivity.
      + constructor=> x. apply CIH. left. eexists. split; reflexivity.
      + constructor=> x. apply CIH. left. eexists. split; reflexivity.
    - unfold pstructural_body.
      pose proof (pstructural_unfold Hdone) as Hstep.
      eapply pstructuralF_monotone; [|exact Hstep].
      intros x y Hxy. apply CIH. right. exact Hxy. }
  apply Hstrong. left. eexists. split; reflexivity.
Qed.

End PStructuralBindAssoc.

(** Strong probabilistic bisimulation over an abstract probabilistic
    relation lifting.  Constructors are matched in lockstep: unlike
    [apweak], this relation neither discards a one-sided [Tau] nor collapses
    a finite probabilistic frontier.  It therefore serves as the strong
    baseline between structural [equ] and the weak frontier relations. *)

Section PStrong.

Context {E : Type -> Type}.
Context {M : Type -> Type}.
Context `{MI : MeasureInterface M}.
Context `{MC : @MeasureCoreLaws M MI}.
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
      meas_lift (fun x y => sim (k1 x) (k2 y)) mu nu ->
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
  - constructor. eapply meas_lift_mono; [|exact Hc].
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
Context `{MI : MeasureInterface M}.
Context `{MC : @MeasureCoreLaws M MI}.
Context `{ML : @MeasureLaws M MI MC}.

Theorem pstructural_pstrong {R1 R2} (RR : R1 -> R2 -> Prop) :
  forall (t1 : ptree E M R1) (t2 : ptree E M R2),
    pstructural RR t1 t2 -> pstrong RR t1 t2.
Proof.
  unfold pstrong. coinduction CH CIH. move=> t1 t2 Hrel.
  move: (pstructural_unfold Hrel)=> Hstep.
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
    eapply meas_lift_mono.
    + move=> x y ->. exact: CIH (Hk y).
    + apply meas_lift_refl. unfold Reflexive. reflexivity.
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
    eapply meas_lift_mono.
    + move=> x y ->. apply CIH.
    + apply meas_lift_refl. unfold Reflexive. reflexivity.
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
    eapply meas_lift_mono.
    + move=> y x Hxy. exact: CIH Hxy.
    + apply meas_lift_sym. exact Hc.
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
  meas_lift (fun x y => pstrong eq (k1 x) (k2 y)) mu nu ->
  pstrong eq (Prob mu k1) (Prob nu k2).
Proof. move=> Hrel. apply pstrong_fold. constructor. exact Hrel. Qed.

Lemma pstrong_prob_inv {R} {X Y : Type}
    (mu : M X) (nu : M Y)
    (k1 : X -> ptree E M R) (k2 : Y -> ptree E M R) :
  pstrong eq (Prob mu k1) (Prob nu k2) ->
  meas_lift (fun x y => pstrong eq (k1 x) (k2 y)) mu nu.
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
    have Hcomp := @meas_lift_comp M MI MC ML _ _ _ _ _ _ _ _ H H0.
    eapply (meas_lift_mono
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
    eapply meas_lift_mono.
    + move=> y x Hxy. exact: CIH Hxy.
    + apply meas_lift_sym. exact Hc.
Qed.

#[global] Instance pstrong_equivalence {R : Type} :
  Equivalence (@pstrong E M MI MC R R eq).
Proof.
  split.
  - exact pstrong_refl.
  - exact pstrong_sym_eq.
  - exact pstrong_trans.
Qed.

End PStrongFacts.
