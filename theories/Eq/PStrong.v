Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program Morphisms.

From Coinduction Require Import all.
From mathcomp Require Import ssreflect ssrbool eqtype seq.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import FrontierLift TwoLevelMeasure.
From PTree.Eq Require Import Shallow.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "` R" := (elem R) (at level 10).

(** Auxiliary proof relation, not a public behavioral equivalence.  It is a
    purely structural lockstep relation.  Probability nodes must expose
    the same sampling measure and sampled type; only their continuations may
    differ recursively.  This replaces the axiom-bearing legacy [equ] as the
    maintained coinductive structural baseline. *)
Section PStruct.

Context {E : Type -> Type} {M : Type -> Type}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

Variant pstructF
    (sim : ptree E M R1 -> ptree E M R2 -> Prop) :
    ptree' E M R1 -> ptree' E M R2 -> Prop :=
  | PStRet r1 r2 : RR r1 r2 ->
      pstructF sim (RetF r1) (RetF r2)
  | PStTau t1 t2 : sim t1 t2 ->
      pstructF sim (TauF t1) (TauF t2)
  | PStVis {X} (e : E X) k1 k2 :
      (forall x, sim (k1 x) (k2 x)) ->
      pstructF sim (VisF e k1) (VisF e k2)
  | PStProb {X : Type} (mu : M X) k1 k2 :
      (forall x, sim (k1 x) (k2 x)) ->
      pstructF sim (ProbF mu k1) (ProbF mu k2).

Definition pstruct_body
    (sim : ptree E M R1 -> ptree E M R2 -> Prop)
    (t1 : ptree E M R1) (t2 : ptree E M R2) : Prop :=
  pstructF sim (observe t1) (observe t2).

Lemma pstructF_monotone sim1 sim2 :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall ot1 ot2, pstructF sim1 ot1 ot2 ->
    pstructF sim2 ot1 ot2.
Proof.
  move=> Hmono ot1 ot2 Hs. inversion Hs; subst.
  - constructor. exact H.
  - constructor. exact: Hmono H.
  - constructor=> x. exact: Hmono (H x).
  - constructor=> x. exact: Hmono (H x).
Qed.

Program Definition fpstruct :
    mon (ptree E M R1 -> ptree E M R2 -> Prop) :=
  {| body := pstruct_body |}.
Next Obligation.
  move=> sim1 sim2 Hsub t1 t2 Hs.
  eapply pstructF_monotone.
  - exact Hsub.
  - exact Hs.
Qed.

Definition pstruct : ptree E M R1 -> ptree E M R2 -> Prop :=
  gfp fpstruct.

Lemma pstruct_unfold t1 t2 :
  pstruct t1 t2 ->
  pstructF pstruct (observe t1) (observe t2).
Proof. move=> H. apply (gfp_pfp fpstruct) in H. exact H. Qed.

Lemma pstruct_fold t1 t2 :
  pstructF pstruct (observe t1) (observe t2) ->
  pstruct t1 t2.
Proof. move=> H. unfold pstruct. apply (gfp_fp fpstruct). exact H. Qed.

End PStruct.

Section PStructFacts.
Context {E : Type -> Type} {M : Type -> Type}.

Lemma pstruct_refl {R : Type} :
  Reflexive (@pstruct E M R R eq).
Proof.
  red. unfold pstruct. coinduction CH CIH. move=> t.
  unfold pstruct_body.
  set ot := observe t.
  change (pstructF eq (` CH) ot ot).
  destruct ot.
  - constructor. reflexivity.
  - constructor. apply CIH.
  - constructor=> x. apply CIH.
  - constructor=> x. apply CIH.
Qed.

Lemma eq_pstruct {R : Type} (t1 t2 : ptree E M R) :
  t1 = t2 -> pstruct eq t1 t2.
Proof. move=> ->. exact: pstruct_refl. Qed.

(** Structural equality only inspects one observation at a time.  Hence an
    exact equality of observations is enough even when the coinductive tree
    values themselves are not judgmentally equal. *)
Lemma observe_eq_pstruct {R : Type} (t1 t2 : ptree E M R) :
  observe t1 = observe t2 -> pstruct eq t1 t2.
Proof.
  intro Hobs. apply pstruct_fold. rewrite Hobs.
  apply pstruct_unfold. apply pstruct_refl.
Qed.

Lemma pstruct_sym {R : Type} :
  Symmetric (@pstruct E M R R eq).
Proof.
  move=> t1 t2. revert t1 t2.
  unfold pstruct at 2. coinduction CH CIH.
  move=> t1 t2 Hrel. move: (pstruct_unfold Hrel)=> Hstep.
  set ot1 := observe t1 in Hstep |- *.
  set ot2 := observe t2 in Hstep |- *.
  change (pstructF eq (` CH) ot2 ot1).
  inversion Hstep as
      [r1 r2 HR | u1 u2 Hsim | X e k1 k2 Hk
       | X mu k1 k2 Hk]; subst.
  - constructor. reflexivity.
  - constructor. exact: CIH Hsim.
  - constructor=> x. exact: CIH (Hk x).
  - constructor=> x. exact: CIH (Hk x).
Qed.

Inductive pstruct_trans_clo {R : Type} :
    ptree E M R -> ptree E M R -> Prop :=
  | PStTC t1 t2 t3 :
      pstruct eq t1 t2 ->
      pstruct eq t2 t3 ->
      pstruct_trans_clo t1 t3.

Lemma pstruct_trans {R : Type} :
  Transitive (@pstruct E M R R eq).
Proof.
  move=> t1 t2 t3 H12 H23.
  have Hcomp : pstruct_trans_clo t1 t3 := PStTC H12 H23.
  clear t2 H12 H23. revert t1 t3 Hcomp.
  unfold pstruct. coinduction CH CIH.
  move=> u w Hclo. inversion Hclo as [u' v w' Huv Hvw]; subst.
  move: (pstruct_unfold Huv)=> Hstep1.
  move: (pstruct_unfold Hvw)=> Hstep2.
  set ou := observe u in Hstep1 |- *.
  set ov := observe v in Hstep1 Hstep2.
  set ow := observe w in Hstep2 |- *.
  change (pstructF eq (` CH) ou ow).
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

#[global] Instance pstruct_equivalence {R : Type} :
  Equivalence (@pstruct E M R R eq).
Proof.
  split.
  - exact pstruct_refl.
  - exact pstruct_sym.
  - exact pstruct_trans.
Qed.

End PStructFacts.

Section PStructBind.
Context {E : Type -> Type} {M : Type -> Type}.
Context {A1 A2 B1 B2 : Type}.
Variables (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop).
Variables (k1 : A1 -> ptree E M B1) (k2 : A2 -> ptree E M B2).
Hypothesis Hcont : forall a1 a2, RA a1 a2 ->
  pstruct RB (k1 a1) (k2 a2).

Definition pstruct_bind_clo
    (u1 : ptree E M B1) (u2 : ptree E M B2) : Prop :=
  (exists t1 t2, u1 = PTree.bind t1 k1 /\
    u2 = PTree.bind t2 k2 /\ pstruct RA t1 t2) \/
  pstruct RB u1 u2.

Theorem pstruct_bind t1 t2 :
  pstruct RA t1 t2 ->
  pstruct RB (PTree.bind t1 k1) (PTree.bind t2 k2).
Proof.
  intro Hsource.
  assert (Hstrong : forall u1 u2, pstruct_bind_clo u1 u2 ->
      pstruct RB u1 u2).
  { unfold pstruct. coinduction CH CIH.
    intros u1 u2 Hclo.
    destruct Hclo as [[s1 [s2 [-> [-> Hs]]]]|Hdone].
    - unfold pstruct_body.
      change (pstructF RB (` CH)
        (observe (PTree.bind s1 k1)) (observe (PTree.bind s2 k2))).
      rewrite !observe_bind.
      pose proof (pstruct_unfold Hs) as Hstep.
      dependent destruction Hstep; cbn.
      + rewrite <- x0, <- x.
        pose proof (pstruct_unfold (Hcont H)) as Hret.
        eapply pstructF_monotone; [|exact Hret].
        intros v1 v2 Hv. apply CIH. right. exact Hv.
      + rewrite <- x0, <- x. constructor. apply CIH. left.
        eexists _, _. repeat split; eauto.
      + rewrite <- x0, <- x. constructor=> y. apply CIH. left.
        eexists _, _. repeat split; eauto.
      + rewrite <- x0, <- x. constructor=> y. apply CIH. left.
        eexists _, _. repeat split; eauto.
    - unfold pstruct_body.
      pose proof (pstruct_unfold Hdone) as Hstep.
      eapply pstructF_monotone; [|exact Hstep].
      intros x y Hxy. apply CIH. right. exact Hxy. }
  apply Hstrong. left. eexists _, _. repeat split; eauto.
Qed.

End PStructBind.

Section PStructBindAssoc.
Context {E : Type -> Type} {M : Type -> Type}.
Context {A B C : Type}.
Variables (k : A -> ptree E M B) (h : B -> ptree E M C).

Definition pstruct_bind_assoc_clo
    (u v : ptree E M C) : Prop :=
  (exists t, u = PTree.bind (PTree.bind t k) h /\
    v = PTree.bind t (fun a => PTree.bind (k a) h)) \/
  pstruct eq u v.

Theorem pstruct_bind_assoc (t : ptree E M A) :
  pstruct eq
    (PTree.bind (PTree.bind t k) h)
    (PTree.bind t (fun a => PTree.bind (k a) h)).
Proof.
  assert (Hstrong : forall u v, pstruct_bind_assoc_clo u v ->
      pstruct eq u v).
  { unfold pstruct. coinduction CH CIH.
    intros u v Hclo.
    destruct Hclo as [[s [-> ->]]|Hdone].
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.bind (PTree.bind s k) h))
        (observe (PTree.bind s (fun a => PTree.bind (k a) h)))).
      rewrite !observe_bind.
      remember (observe s) as ot eqn:Hot.
      destruct ot as [a|s'|X e c|X mu c]; cbn.
      + pose proof (pstruct_refl
          (PTree.bind (k a) h)) as Hrefl.
        pose proof (pstruct_unfold Hrefl) as Hstep.
        eapply pstructF_monotone; [|exact Hstep].
        intros x y Hxy. apply CIH. right. exact Hxy.
      + constructor. apply CIH. left. eexists. split; reflexivity.
      + constructor=> x. apply CIH. left. eexists. split; reflexivity.
      + constructor=> x. apply CIH. left. eexists. split; reflexivity.
    - unfold pstruct_body.
      pose proof (pstruct_unfold Hdone) as Hstep.
      eapply pstructF_monotone; [|exact Hstep].
      intros x y Hxy. apply CIH. right. exact Hxy. }
  apply Hstrong. left. eexists. split; reflexivity.
Qed.

End PStructBindAssoc.

Section PStructBindRetR.
Context {E : Type -> Type} {M : Type -> Type} {A : Type}.

Definition pstruct_bind_ret_r_clo
    (u v : ptree E M A) : Prop :=
  (exists t, u = PTree.bind t (fun x => Ret x) /\ v = t) \/
  pstruct eq u v.

Theorem pstruct_bind_ret_r (t : ptree E M A) :
  pstruct eq (PTree.bind t (fun x => Ret x)) t.
Proof.
  assert (Hstrong : forall u v, pstruct_bind_ret_r_clo u v ->
      pstruct eq u v).
  { unfold pstruct. coinduction CH CIH.
    intros u v Hclo. destruct Hclo as [[s [-> ->]]|Hdone].
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.bind s (fun x => Ret x))) (observe s)).
      rewrite observe_bind.
      remember (observe s) as os eqn:Hos.
      destruct os as [a|s'|X e k|X mu k]; cbn.
      + constructor. reflexivity.
      + constructor. apply CIH. left. eexists. split; reflexivity.
      + constructor=> x. apply CIH. left. eexists. split; reflexivity.
      + constructor=> x. apply CIH. left. eexists. split; reflexivity.
    - unfold pstruct_body.
      pose proof (pstruct_unfold Hdone) as Hstep.
      eapply pstructF_monotone; [|exact Hstep].
      intros x y Hxy. apply CIH. right. exact Hxy. }
  apply Hstrong. left. eexists. split; reflexivity.
Qed.

End PStructBindRetR.

Section PStructInterp.
Context {E F : Type -> Type} {M : Type -> Type}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.
Variable handler : forall X, E X -> ptree F M X.

Inductive pstruct_interp_clo :
    ptree F M R1 -> ptree F M R2 -> Prop :=
  | PStInterpMain t1 t2 :
      pstruct RR t1 t2 ->
      pstruct_interp_clo
        (PTree.interp handler t1) (PTree.interp handler t2)
  | PStInterpBind {X} (source : ptree F M X)
      (k1 : X -> ptree E M R1) (k2 : X -> ptree E M R2) :
      (forall x, pstruct RR (k1 x) (k2 x)) ->
      pstruct_interp_clo
        (PTree.bind source (fun x => PTree.interp handler (k1 x)))
        (PTree.bind source (fun x => PTree.interp handler (k2 x)))
  | PStInterpDone u1 u2 :
      pstruct RR u1 u2 -> pstruct_interp_clo u1 u2.

Theorem pstruct_interp (t1 : ptree E M R1) (t2 : ptree E M R2) :
  pstruct RR t1 t2 ->
  pstruct RR (PTree.interp handler t1) (PTree.interp handler t2).
Proof.
  intro Hsource.
  assert (Hinterp : forall u1 u2, pstruct_interp_clo u1 u2 ->
      pstruct RR u1 u2).
  { unfold pstruct. coinduction CH CIH.
    intros u1 u2 Hclo. inversion Hclo; subst.
    - unfold pstruct_body.
      change (pstructF RR (` CH)
        (observe (PTree.interp handler t0))
        (observe (PTree.interp handler t3))).
      rewrite !observe_interp.
      pose proof (pstruct_unfold H) as Hstep.
      dependent destruction Hstep.
      + rewrite <- x0. rewrite <- x. cbn. constructor. exact H0.
      + rewrite <- x0. rewrite <- x. cbn.
        constructor. apply CIH. constructor. exact H0.
      + rewrite <- x0. rewrite <- x. cbn.
        constructor. apply CIH. constructor. intro y. exact (H0 y).
      + rewrite <- x0. rewrite <- x. cbn.
        constructor=> y. apply CIH. constructor. exact (H0 y).
    - unfold pstruct_body.
      change (pstructF RR (` CH)
        (observe (PTree.bind source
          (fun x => PTree.interp handler (k1 x))))
        (observe (PTree.bind source
          (fun x => PTree.interp handler (k2 x))))).
      rewrite !observe_bind.
      remember (observe source) as os eqn:Hos.
      destruct os as [x|source'|Y e c|Y mu c]; cbn.
      + rewrite !observe_interp.
        pose proof (pstruct_unfold (H x)) as Hstep.
        dependent destruction Hstep.
        * rewrite <- x1. rewrite <- x. cbn. constructor. exact H0.
        * rewrite <- x1. rewrite <- x. cbn.
          constructor. apply CIH. constructor. exact H0.
        * rewrite <- x1. rewrite <- x. cbn.
          constructor. apply CIH. constructor. intro z. exact (H0 z).
        * rewrite <- x1. rewrite <- x. cbn.
          constructor=> z. apply CIH. constructor. exact (H0 z).
      + constructor. apply CIH. constructor. exact H.
      + constructor=> y. apply CIH. constructor. exact H.
      + constructor=> y. apply CIH. constructor. exact H.
    - unfold pstruct_body.
      pose proof (pstruct_unfold H) as Hstep.
      eapply pstructF_monotone; [|exact Hstep].
      intros x y Hxy. apply CIH. constructor. exact Hxy. }
  apply Hinterp. constructor. exact Hsource.
Qed.

End PStructInterp.

Section PStructInterpBind.
Context {E F : Type -> Type} {M : Type -> Type}.
Context {A B : Type}.
Variable handler : forall X, E X -> ptree F M X.

Inductive pstruct_interp_bind_clo :
    ptree F M B -> ptree F M B -> Prop :=
  | PStInterpBindMain (t : ptree E M A) (k : A -> ptree E M B) :
      pstruct_interp_bind_clo
        (PTree.interp handler (PTree.bind t k))
        (PTree.bind (PTree.interp handler t)
          (fun x => PTree.interp handler (k x)))
  | PStInterpBindHandler {X} (source : ptree F M X)
      (c : X -> ptree E M A) (k : A -> ptree E M B) :
      pstruct_interp_bind_clo
        (PTree.bind source
          (fun x => PTree.interp handler (PTree.bind (c x) k)))
        (PTree.bind
          (PTree.bind source (fun x => PTree.interp handler (c x)))
          (fun y => PTree.interp handler (k y)))
  | PStInterpBindDone (u v : ptree F M B) :
      pstruct eq u v -> pstruct_interp_bind_clo u v.

Theorem pstruct_interp_bind (t : ptree E M A)
    (k : A -> ptree E M B) :
  pstruct eq
    (PTree.interp handler (PTree.bind t k))
    (PTree.bind (PTree.interp handler t)
      (fun x => PTree.interp handler (k x))).
Proof.
  assert (Hstrong : forall u v, pstruct_interp_bind_clo u v ->
      pstruct eq u v).
  { unfold pstruct. coinduction CH CIH.
    intros u v Hclo. inversion Hclo; subst.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.interp handler (PTree.bind t0 k0)))
        (observe (PTree.bind (PTree.interp handler t0)
          (fun x => PTree.interp handler (k0 x))))).
      rewrite observe_interp. rewrite !observe_bind. rewrite observe_interp.
      remember (observe t0) as ot eqn:Hot.
      destruct ot as [a|t'|X e c|X mu c]; cbn.
      + rewrite <- observe_interp.
        pose proof (pstruct_unfold
          (pstruct_refl (PTree.interp handler (k0 a)))) as Hrefl.
        eapply pstructF_monotone; [|exact Hrefl].
        intros x y Hxy. apply CIH. constructor. exact Hxy.
      + constructor. apply CIH. constructor.
      + constructor. apply CIH. constructor.
      + constructor=> x. apply CIH. constructor.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.bind source
          (fun x => PTree.interp handler (PTree.bind (c x) k0))))
        (observe (PTree.bind
          (PTree.bind source (fun x => PTree.interp handler (c x)))
          (fun y => PTree.interp handler (k0 y))))).
      rewrite !observe_bind.
      remember (observe source) as os eqn:Hos.
      destruct os as [x|source'|Y e d|Y mu d]; cbn.
      + rewrite observe_interp. rewrite !observe_bind. rewrite observe_interp.
        remember (observe (c x)) as oc eqn:Hoc.
        destruct oc as [a|c'|Z e' d'|Z mu' d']; cbn.
        * rewrite <- observe_interp.
          pose proof (pstruct_unfold
            (pstruct_refl (PTree.interp handler (k0 a)))) as Hrefl.
          eapply pstructF_monotone; [|exact Hrefl].
          intros p q Hpq. apply CIH. constructor. exact Hpq.
        * constructor. apply CIH. constructor.
        * constructor. apply CIH. constructor.
        * constructor=> z. apply CIH. constructor.
      + constructor. apply CIH. constructor.
      + constructor=> y. apply CIH. constructor.
      + constructor=> y. apply CIH. constructor.
    - unfold pstruct_body.
      pose proof (pstruct_unfold H) as Hstep.
      eapply pstructF_monotone; [|exact Hstep].
      intros x y Hxy. apply CIH. constructor. exact Hxy. }
  apply Hstrong. constructor.
Qed.

End PStructInterpBind.

Section PStructInterpIter.
Context {E F : Type -> Type} {M : Type -> Type}.
Context {I R : Type}.
Variable handler : forall X, E X -> ptree F M X.
Variable step : I -> ptree E M (I + R).

Definition pstruct_interp_iter_source_cont
    (lr : I + R) : ptree E M R :=
  match lr with
  | inl i => Tau (PTree.iter step i)
  | inr r => Ret r
  end.

Definition pstruct_interp_iter_target_step
    (i : I) : ptree F M (I + R) :=
  PTree.interp handler (step i).

Definition pstruct_interp_iter_target_cont
    (lr : I + R) : ptree F M R :=
  match lr with
  | inl i => Tau (PTree.iter pstruct_interp_iter_target_step i)
  | inr r => Ret r
  end.

Inductive pstruct_interp_iter_clo :
    ptree F M R -> ptree F M R -> Prop :=
  | PStInterpIterMain i :
      pstruct_interp_iter_clo
        (PTree.interp handler (PTree.iter step i))
        (PTree.iter pstruct_interp_iter_target_step i)
  | PStInterpIterSource (t : ptree E M (I + R)) :
      pstruct_interp_iter_clo
        (PTree.interp handler
          (PTree.bind t pstruct_interp_iter_source_cont))
        (PTree.bind (PTree.interp handler t)
          pstruct_interp_iter_target_cont)
  | PStInterpIterHandler {X} (source : ptree F M X)
      (c : X -> ptree E M (I + R)) :
      pstruct_interp_iter_clo
        (PTree.bind source (fun x => PTree.interp handler
          (PTree.bind (c x) pstruct_interp_iter_source_cont)))
        (PTree.bind
          (PTree.bind source (fun x => PTree.interp handler (c x)))
          pstruct_interp_iter_target_cont)
  | PStInterpIterDone (u v : ptree F M R) :
      pstruct eq u v -> pstruct_interp_iter_clo u v.

(** Interpretation commutes with guarded iteration.  The proof is purely
    structural: the joint invariant records the source loop, the bind
    exposed by one loop unfolding, and the extra bind introduced when an
    effectful handler runs. *)
Theorem pstruct_interp_iter i :
  pstruct eq
    (PTree.interp handler (PTree.iter step i))
    (PTree.iter pstruct_interp_iter_target_step i).
Proof.
  assert (Hstrong : forall u v, pstruct_interp_iter_clo u v ->
      pstruct eq u v).
  { unfold pstruct. coinduction CH CIH.
    intros u v Hclo. inversion Hclo; subst.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.interp handler (PTree.iter step i0)))
        (observe (PTree.iter pstruct_interp_iter_target_step i0))).
      rewrite observe_interp.
      rewrite (observing_observe (unfold_aloop_ step i0)).
      rewrite (observing_observe
        (unfold_aloop_ pstruct_interp_iter_target_step i0)).
      rewrite !observe_bind. rewrite observe_interp.
      remember (observe (step i0)) as ot eqn:Hot.
      destruct ot as [lr|t'|X e c|X mu c]; cbn.
      + destruct lr as [j|r]; cbn [pstruct_interp_iter_source_cont
          pstruct_interp_iter_target_cont].
        * constructor. apply CIH. constructor.
        * constructor. reflexivity.
      + constructor. apply CIH. constructor.
      + constructor. apply CIH. constructor.
      + constructor=> x. apply CIH. constructor.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.interp handler
          (PTree.bind t pstruct_interp_iter_source_cont)))
        (observe (PTree.bind (PTree.interp handler t)
          pstruct_interp_iter_target_cont))).
      rewrite observe_interp. rewrite !observe_bind. rewrite observe_interp.
      remember (observe t) as ot eqn:Hot.
      destruct ot as [lr|t'|X e c|X mu c]; cbn.
      + destruct lr as [j|r]; cbn [pstruct_interp_iter_source_cont
          pstruct_interp_iter_target_cont].
        * constructor. apply CIH. constructor.
        * constructor. reflexivity.
      + constructor. apply CIH. constructor.
      + constructor. apply CIH. constructor.
      + constructor=> x. apply CIH. constructor.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.bind source (fun x => PTree.interp handler
          (PTree.bind (c x) pstruct_interp_iter_source_cont))))
        (observe (PTree.bind
          (PTree.bind source (fun x => PTree.interp handler (c x)))
          pstruct_interp_iter_target_cont))).
      rewrite !observe_bind.
      remember (observe source) as os eqn:Hos.
      destruct os as [x|source'|Y e d|Y mu d]; cbn.
      + rewrite observe_interp. rewrite !observe_bind. rewrite observe_interp.
        remember (observe (c x)) as oc eqn:Hoc.
        destruct oc as [lr|c'|Z e' d'|Z mu' d']; cbn.
        * destruct lr as [j|r]; cbn
              [pstruct_interp_iter_source_cont
               pstruct_interp_iter_target_cont].
          -- constructor. apply CIH. constructor.
          -- constructor. reflexivity.
        * constructor. apply CIH. constructor.
        * constructor. apply CIH. constructor.
        * constructor=> z. apply CIH. constructor.
      + constructor. apply CIH. constructor.
      + constructor=> y. apply CIH. constructor.
      + constructor=> y. apply CIH. constructor.
    - unfold pstruct_body.
      pose proof (pstruct_unfold H) as Hstep.
      eapply pstructF_monotone; [|exact Hstep].
      intros x y Hxy. apply CIH. constructor. exact Hxy. }
  apply Hstrong. constructor.
Qed.

End PStructInterpIter.

Section PStructInterpCompose.
Context {E F G : Type -> Type} {M : Type -> Type}.
Context {R : Type}.
Variable handler1 : forall X, E X -> ptree F M X.
Variable handler2 : forall X, F X -> ptree G M X.

Definition pstruct_interp_compose_handler
    (X : Type) (e : E X) : ptree G M X :=
  PTree.interp handler2 (handler1 e).

Inductive pstruct_interp_compose_clo :
    ptree G M R -> ptree G M R -> Prop :=
  | PStInterpComposeMain (t : ptree E M R) :
      pstruct_interp_compose_clo
        (PTree.interp handler2 (PTree.interp handler1 t))
        (PTree.interp pstruct_interp_compose_handler t)
  | PStInterpComposeBind {X} (source : ptree F M X)
      (k : X -> ptree E M R) :
      pstruct_interp_compose_clo
        (PTree.interp handler2
          (PTree.bind source (fun x => PTree.interp handler1 (k x))))
        (PTree.bind (PTree.interp handler2 source)
          (fun x => PTree.interp pstruct_interp_compose_handler (k x)))
  | PStInterpComposeHandler {X} (source : ptree G M X)
      {Y} (c : X -> ptree F M Y) (k : Y -> ptree E M R) :
      pstruct_interp_compose_clo
        (PTree.bind source (fun x => PTree.interp handler2
          (PTree.bind (c x) (fun y => PTree.interp handler1 (k y)))))
        (PTree.bind
          (PTree.bind source (fun x => PTree.interp handler2 (c x)))
          (fun y => PTree.interp pstruct_interp_compose_handler (k y)))
  | PStInterpComposeDone (u v : ptree G M R) :
      pstruct eq u v -> pstruct_interp_compose_clo u v.

(** Sequential effect handlers compose.  Both handlers are arbitrary
    PTrees; in particular their execution may contain Tau, Vis, and Prob. *)
Theorem pstruct_interp_compose (t : ptree E M R) :
  pstruct eq
    (PTree.interp handler2 (PTree.interp handler1 t))
    (PTree.interp pstruct_interp_compose_handler t).
Proof.
  assert (Hstrong : forall u v, pstruct_interp_compose_clo u v ->
      pstruct eq u v).
  { unfold pstruct. coinduction CH CIH.
    intros u v Hclo. inversion Hclo; subst.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.interp handler2 (PTree.interp handler1 t0)))
        (observe (PTree.interp pstruct_interp_compose_handler t0))).
      rewrite !observe_interp.
      remember (observe t0) as ot eqn:Hot.
      destruct ot as [r|t'|X e k|X mu k]; cbn.
      + constructor. reflexivity.
      + constructor. apply CIH. constructor.
      + constructor. apply CIH. constructor.
      + constructor=> x. apply CIH. constructor.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.interp handler2
          (PTree.bind source (fun x => PTree.interp handler1 (k x)))))
        (observe (PTree.bind (PTree.interp handler2 source)
          (fun x => PTree.interp pstruct_interp_compose_handler (k x))))).
      rewrite observe_interp. rewrite !observe_bind. rewrite observe_interp.
      remember (observe source) as os eqn:Hos.
      destruct os as [x|source'|Y e c|Y mu c]; cbn.
      + rewrite !observe_interp.
        remember (observe (k x)) as ok eqn:Hok.
        destruct ok as [r|k'|Z e' d|Z mu' d]; cbn.
        * constructor. reflexivity.
        * constructor. apply CIH. constructor.
        * constructor. apply CIH. constructor.
        * constructor=> z. apply CIH. constructor.
      + constructor. apply CIH. constructor.
      + constructor. apply CIH. constructor.
      + constructor=> y. apply CIH. constructor.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.bind source (fun x => PTree.interp handler2
          (PTree.bind (c x) (fun y => PTree.interp handler1 (k y))))))
        (observe (PTree.bind
          (PTree.bind source (fun x => PTree.interp handler2 (c x)))
          (fun y => PTree.interp pstruct_interp_compose_handler (k y))))).
      rewrite !observe_bind.
      remember (observe source) as os eqn:Hos.
      destruct os as [x|source'|Z e d|Z mu d]; cbn.
      + rewrite observe_interp. rewrite !observe_bind. rewrite observe_interp.
        remember (observe (c x)) as oc eqn:Hoc.
        destruct oc as [y|c'|W e' d'|W mu' d']; cbn.
        * rewrite !observe_interp.
          remember (observe (k y)) as ok eqn:Hok.
          destruct ok as [r|k'|V e'' q|V mu'' q]; cbn.
          -- constructor. reflexivity.
          -- constructor. apply CIH. constructor.
          -- constructor. apply CIH. constructor.
          -- constructor=> z. apply CIH. constructor.
        * constructor. apply CIH. constructor.
        * constructor. apply CIH. constructor.
        * constructor=> z. apply CIH. constructor.
      + constructor. apply CIH. constructor.
      + constructor=> z. apply CIH. constructor.
      + constructor=> z. apply CIH. constructor.
    - unfold pstruct_body.
      pose proof (pstruct_unfold H) as Hstep.
      eapply pstructF_monotone; [|exact Hstep].
      intros x y Hxy. apply CIH. constructor. exact Hxy. }
  apply Hstrong. constructor.
Qed.

End PStructInterpCompose.

Section PStructInterpHandlerCongruence.
Context {E F : Type -> Type} {M : Type -> Type}.
Context {R : Type}.
Variable handler1 handler2 : forall X, E X -> ptree F M X.
Hypothesis handlers_related : forall X (e : E X),
  pstruct eq (@handler1 X e) (@handler2 X e).

Inductive pstruct_interp_handler_clo :
    ptree F M R -> ptree F M R -> Prop :=
  | PStInterpHandlerMain (t : ptree E M R) :
      pstruct_interp_handler_clo
        (PTree.interp handler1 t) (PTree.interp handler2 t)
  | PStInterpHandlerBind {X}
      (source1 source2 : ptree F M X) (k : X -> ptree E M R) :
      pstruct eq source1 source2 ->
      pstruct_interp_handler_clo
        (PTree.bind source1 (fun x => PTree.interp handler1 (k x)))
        (PTree.bind source2 (fun x => PTree.interp handler2 (k x)))
  | PStInterpHandlerDone (u v : ptree F M R) :
      pstruct eq u v -> pstruct_interp_handler_clo u v.

(** Pointwise structurally equivalent effect handlers induce structurally
    equivalent interpretations.  Handler computations may themselves use
    Tau, Vis, and Prob. *)
Theorem pstruct_interp_handler (t : ptree E M R) :
  pstruct eq (PTree.interp handler1 t) (PTree.interp handler2 t).
Proof.
  assert (Hstrong : forall u v, pstruct_interp_handler_clo u v ->
      pstruct eq u v).
  { unfold pstruct. coinduction CH CIH.
    intros u v Hclo. inversion Hclo; subst.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.interp handler1 t0))
        (observe (PTree.interp handler2 t0))).
      rewrite !observe_interp.
      remember (observe t0) as ot eqn:Hot.
      destruct ot as [r|t'|X e k|X mu k]; cbn.
      + constructor. reflexivity.
      + constructor. apply CIH. constructor.
      + constructor. apply CIH. constructor. apply handlers_related.
      + constructor=> x. apply CIH. constructor.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.bind source1
          (fun x => PTree.interp handler1 (k x))))
        (observe (PTree.bind source2
          (fun x => PTree.interp handler2 (k x))))).
      rewrite !observe_bind.
      pose proof (pstruct_unfold H) as Hstep.
      dependent destruction Hstep.
      + rewrite <- x0, <- x. cbn. rewrite !observe_interp.
        remember (observe (k r2)) as ok eqn:Hok.
        destruct ok as [r|k'|Y e d|Y mu d]; cbn.
        * constructor. reflexivity.
        * constructor. apply CIH. constructor.
        * constructor. apply CIH. constructor. apply handlers_related.
        * constructor=> y. apply CIH. constructor.
      + rewrite <- x0, <- x. cbn. constructor. apply CIH. constructor. exact H0.
      + rewrite <- x0, <- x. cbn. constructor=> y.
        apply CIH. constructor. exact (H0 y).
      + rewrite <- x0, <- x. cbn. constructor=> y.
        apply CIH. constructor. exact (H0 y).
    - unfold pstruct_body.
      pose proof (pstruct_unfold H) as Hstep.
      eapply pstructF_monotone; [|exact Hstep].
      intros x y Hxy. apply CIH. constructor. exact Hxy. }
  apply Hstrong. constructor.
Qed.

End PStructInterpHandlerCongruence.

Section PStructIter.
Context {E : Type -> Type} {M : Type -> Type}.
Context {I R : Type}.
Variables (f g : I -> ptree E M (I + R)).
Hypothesis Hstep : forall i, pstruct eq (f i) (g i).

Definition pstruct_iter_handler_f (lr : I + R) : ptree E M R :=
  match lr with
  | inl i => Tau (PTree.iter f i)
  | inr r => Ret r
  end.

Definition pstruct_iter_handler_g (lr : I + R) : ptree E M R :=
  match lr with
  | inl i => Tau (PTree.iter g i)
  | inr r => Ret r
  end.

Inductive pstruct_iter_clo : ptree E M R -> ptree E M R -> Prop :=
  | PStIterC i : pstruct_iter_clo (PTree.iter f i) (PTree.iter g i)
  | PStIterBindC t1 t2 :
      pstruct eq t1 t2 ->
      pstruct_iter_clo
        (PTree.bind t1 pstruct_iter_handler_f)
        (PTree.bind t2 pstruct_iter_handler_g)
  | PStIterDoneC t1 t2 :
      pstruct eq t1 t2 -> pstruct_iter_clo t1 t2.

Theorem pstruct_iter i :
  pstruct eq (PTree.iter f i) (PTree.iter g i).
Proof.
  assert (Hstrong : forall u v, pstruct_iter_clo u v ->
      pstruct eq u v).
  { unfold pstruct. coinduction CH CIH.
    intros u v Hclo.
    inversion Hclo as [j|t1 t2 H12|t1 t2 H12]; subst.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.iter f j)) (observe (PTree.iter g j))).
      rewrite (observing_observe (unfold_aloop_ f j)).
      rewrite (observing_observe (unfold_aloop_ g j)).
      rewrite !observe_bind.
      pose proof (pstruct_unfold (Hstep j)) as Hs.
      dependent destruction Hs; cbn.
      + rewrite <- x0, <- x. destruct r2 as [j'|r].
        * constructor. apply CIH. constructor.
        * constructor. reflexivity.
      + rewrite <- x0, <- x. constructor. apply CIH.
        constructor. exact H.
      + rewrite <- x0, <- x. constructor=> y. apply CIH.
        constructor. exact (H y).
      + rewrite <- x0, <- x. constructor=> y. apply CIH.
        constructor. exact (H y).
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.bind t1 pstruct_iter_handler_f))
        (observe (PTree.bind t2 pstruct_iter_handler_g))).
      rewrite !observe_bind.
      pose proof (pstruct_unfold H12) as Hs.
      dependent destruction Hs; cbn.
      + rewrite <- x0, <- x. destruct r2 as [j'|r].
        * constructor. apply CIH. constructor.
        * constructor. reflexivity.
      + rewrite <- x0, <- x. constructor. apply CIH.
        constructor. exact H.
      + rewrite <- x0, <- x. constructor=> y. apply CIH.
        constructor. exact (H y).
      + rewrite <- x0, <- x. constructor=> y. apply CIH.
        constructor. exact (H y).
    - unfold pstruct_body.
      pose proof (pstruct_unfold H12) as Hs.
      eapply pstructF_monotone; [|exact Hs].
      intros x y Hxy. apply CIH. constructor. exact Hxy. }
  apply Hstrong. constructor.
Qed.

End PStructIter.

(** Relational iteration fusion.  The two loops may use different state and
    result types; one related step either produces related successor states
    or related final results. *)
Section PStructIterRel.
Context {E : Type -> Type} {M : Type -> Type}.
Context {I1 I2 R1 R2 : Type}.
Variable SI : I1 -> I2 -> Prop.
Variable RR : R1 -> R2 -> Prop.
Variables (f : I1 -> ptree E M (I1 + R1))
  (g : I2 -> ptree E M (I2 + R2)).

Inductive pstruct_iter_sum_rel : I1 + R1 -> I2 + R2 -> Prop :=
  | PStIterSumL i1 i2 : SI i1 i2 ->
      pstruct_iter_sum_rel (inl i1) (inl i2)
  | PStIterSumR r1 r2 : RR r1 r2 ->
      pstruct_iter_sum_rel (inr r1) (inr r2).

Hypothesis Hstep : forall i1 i2, SI i1 i2 ->
  pstruct pstruct_iter_sum_rel (f i1) (g i2).

Definition pstruct_iter_rel_handler_f
    (lr : I1 + R1) : ptree E M R1 :=
  match lr with
  | inl i => Tau (PTree.iter f i)
  | inr r => Ret r
  end.

Definition pstruct_iter_rel_handler_g
    (lr : I2 + R2) : ptree E M R2 :=
  match lr with
  | inl i => Tau (PTree.iter g i)
  | inr r => Ret r
  end.

Inductive pstruct_iter_rel_clo :
    ptree E M R1 -> ptree E M R2 -> Prop :=
  | PStIterRelC i1 i2 : SI i1 i2 ->
      pstruct_iter_rel_clo (PTree.iter f i1) (PTree.iter g i2)
  | PStIterRelBindC t1 t2 :
      pstruct pstruct_iter_sum_rel t1 t2 ->
      pstruct_iter_rel_clo
        (PTree.bind t1 pstruct_iter_rel_handler_f)
        (PTree.bind t2 pstruct_iter_rel_handler_g)
  | PStIterRelDoneC t1 t2 :
      pstruct RR t1 t2 -> pstruct_iter_rel_clo t1 t2.

Theorem pstruct_iter_rel i1 i2 :
  SI i1 i2 ->
  pstruct RR (PTree.iter f i1) (PTree.iter g i2).
Proof.
  assert (Hstrong : forall u v, pstruct_iter_rel_clo u v ->
      pstruct RR u v).
  { unfold pstruct. coinduction CH CIH.
    intros u v Hclo.
    inversion Hclo as [j1 j2 Hj|t1 t2 H12|t1 t2 H12]; subst.
    - unfold pstruct_body.
      change (pstructF RR (` CH)
        (observe (PTree.iter f j1)) (observe (PTree.iter g j2))).
      rewrite (observing_observe (unfold_aloop_ f j1)).
      rewrite (observing_observe (unfold_aloop_ g j2)).
      rewrite !observe_bind.
      pose proof (pstruct_unfold (Hstep Hj)) as Hs.
      dependent destruction Hs; cbn.
      + rewrite <- x0. rewrite <- x.
        dependent destruction H. cbn.
        * constructor. apply CIH. constructor. exact H.
        * constructor. exact H.
      + rewrite <- x0. rewrite <- x. constructor. apply CIH.
        constructor. exact H.
      + rewrite <- x0. rewrite <- x. constructor=> y. apply CIH.
        constructor. exact (H y).
      + rewrite <- x0. rewrite <- x. constructor=> y. apply CIH.
        constructor. exact (H y).
    - unfold pstruct_body.
      change (pstructF RR (` CH)
        (observe (PTree.bind t1 pstruct_iter_rel_handler_f))
        (observe (PTree.bind t2 pstruct_iter_rel_handler_g))).
      rewrite !observe_bind.
      pose proof (pstruct_unfold H12) as Hs.
      dependent destruction Hs; cbn.
      + rewrite <- x0. rewrite <- x.
        dependent destruction H. cbn.
        * constructor. apply CIH. constructor. exact H.
        * constructor. exact H.
      + rewrite <- x0. rewrite <- x. constructor. apply CIH.
        constructor. exact H.
      + rewrite <- x0. rewrite <- x. constructor=> y. apply CIH.
        constructor. exact (H y).
      + rewrite <- x0. rewrite <- x. constructor=> y. apply CIH.
        constructor. exact (H y).
    - unfold pstruct_body.
      pose proof (pstruct_unfold H12) as Hs.
      eapply pstructF_monotone; [|exact Hs].
      intros x y Hxy. apply CIH. constructor. exact Hxy. }
  intro Hij. apply Hstrong. constructor. exact Hij.
Qed.

End PStructIterRel.

(** Naturality (parameter identity) for guarded iteration. *)
Section PStructIterNatural.
Context {E : Type -> Type} {M : Type -> Type}.
Context {I A B : Type}.
Variable step : I -> ptree E M (I + A).
Variable k : A -> ptree E M B.

Definition pstruct_iter_natural_source_handler
    (ia : I + A) : ptree E M A :=
  match ia with
  | inl j => Tau (PTree.iter step j)
  | inr a => Ret a
  end.

Definition pstruct_iter_natural_step_handler
    (ia : I + A) : ptree E M (I + B) :=
  match ia with
  | inl j => Ret (inl j)
  | inr a => PTree.bind (k a) (fun b => Ret (inr b))
  end.

Definition pstruct_iter_natural_step (i : I) : ptree E M (I + B) :=
  PTree.bind (step i) pstruct_iter_natural_step_handler.

Definition pstruct_iter_natural_target_handler
    (ib : I + B) : ptree E M B :=
  match ib with
  | inl j => Tau (PTree.iter pstruct_iter_natural_step j)
  | inr b => Ret b
  end.

Inductive pstruct_iter_natural_clo :
    ptree E M B -> ptree E M B -> Prop :=
  | PStIterNaturalMain i :
      pstruct_iter_natural_clo
        (PTree.bind (PTree.iter step i) k)
        (PTree.iter pstruct_iter_natural_step i)
  | PStIterNaturalBind t :
      pstruct_iter_natural_clo
        (PTree.bind
          (PTree.bind t pstruct_iter_natural_source_handler) k)
        (PTree.bind
          (PTree.bind t pstruct_iter_natural_step_handler)
          pstruct_iter_natural_target_handler)
  | PStIterNaturalDone t1 t2 :
      pstruct eq t1 t2 -> pstruct_iter_natural_clo t1 t2.

Lemma pstruct_iter_natural_return (a : A) :
  pstruct eq (k a)
    (PTree.bind
      (PTree.bind (k a) (fun b => Ret (inr b)))
      pstruct_iter_natural_target_handler).
Proof.
  apply pstruct_sym.
  eapply pstruct_trans.
  - apply pstruct_bind_assoc.
  - eapply pstruct_trans.
    + eapply pstruct_bind with (RA := eq) (RB := eq).
      * intros b1 b2 ->. apply observe_eq_pstruct.
        exact (observing_observe (bind_ret_ (inr b2)
          pstruct_iter_natural_target_handler)).
      * apply pstruct_refl.
    + apply pstruct_bind_ret_r.
Qed.

Theorem pstruct_iter_natural i :
  pstruct eq
    (PTree.bind (PTree.iter step i) k)
    (PTree.iter pstruct_iter_natural_step i).
Proof.
  assert (Hstrong : forall u v, pstruct_iter_natural_clo u v ->
      pstruct eq u v).
  { unfold pstruct. coinduction CH CIH.
    intros u v Hclo.
    inversion Hclo as [j|t|t1 t2 Hdone]; subst.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.bind (PTree.iter step j) k))
        (observe (PTree.iter pstruct_iter_natural_step j))).
      rewrite observe_bind.
      rewrite (observing_observe (unfold_aloop_ step j)).
      rewrite (observing_observe
        (unfold_aloop_ pstruct_iter_natural_step j)).
      rewrite !observe_bind.
      remember (observe (step j)) as ot eqn:Hot.
      destruct ot as [ia|t'|X e c|X mu c]; cbn.
      + destruct ia as [j'|a]; cbn.
        * constructor. apply CIH. constructor.
        * pose proof (pstruct_iter_natural_return a) as Hr.
          pose proof (pstruct_unfold Hr) as Hstep.
          eapply pstructF_monotone; [|exact Hstep].
          intros x y Hxy. apply CIH. constructor. exact Hxy.
      + constructor. apply CIH. constructor.
      + constructor=> x. apply CIH. constructor.
      + constructor=> x. apply CIH. constructor.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.bind
          (PTree.bind t pstruct_iter_natural_source_handler) k))
        (observe (PTree.bind
          (PTree.bind t pstruct_iter_natural_step_handler)
          pstruct_iter_natural_target_handler))).
      rewrite !observe_bind.
      remember (observe t) as ot eqn:Hot.
      destruct ot as [ia|t'|X e c|X mu c]; cbn.
      + destruct ia as [j|a]; cbn.
        * constructor. apply CIH. constructor.
        * pose proof (pstruct_iter_natural_return a) as Hr.
          pose proof (pstruct_unfold Hr) as Hstep.
          eapply pstructF_monotone; [|exact Hstep].
          intros x y Hxy. apply CIH. constructor. exact Hxy.
      + constructor. apply CIH. constructor.
      + constructor=> x. apply CIH. constructor.
      + constructor=> x. apply CIH. constructor.
    - unfold pstruct_body.
      pose proof (pstruct_unfold Hdone) as Hstep.
      eapply pstructF_monotone; [|exact Hstep].
      intros x y Hxy. apply CIH. constructor. exact Hxy. }
  apply Hstrong. constructor.
Qed.

End PStructIterNatural.

(** Codiagonal / double-dagger identity: two nested loops over the same
    state space flatten to one loop whose first two sum branches both retry. *)
Section PStructIterCodiagonal.
Context {E : Type -> Type} {M : Type -> Type}.
Context {I R : Type}.
Variable step : I -> ptree E M (I + (I + R)).

Definition pstruct_iter_codiagonal_nested (i : I) : ptree E M R :=
  PTree.iter (fun j => PTree.iter step j) i.

Definition pstruct_iter_codiagonal_inner_handler
    (x : I + (I + R)) : ptree E M (I + R) :=
  match x with
  | inl j => Tau (PTree.iter step j)
  | inr q => Ret q
  end.

Definition pstruct_iter_codiagonal_outer_handler
    (x : I + R) : ptree E M R :=
  match x with
  | inl j => Tau (pstruct_iter_codiagonal_nested j)
  | inr r => Ret r
  end.

Definition pstruct_iter_codiagonal_flatten
    (x : I + (I + R)) : I + R :=
  match x with
  | inl j => inl j
  | inr (inl j) => inl j
  | inr (inr r) => inr r
  end.

Definition pstruct_iter_codiagonal_flat_step
    (i : I) : ptree E M (I + R) :=
  PTree.bind (step i)
    (fun x => Ret (pstruct_iter_codiagonal_flatten x)).

Definition pstruct_iter_codiagonal_flat_handler
    (x : I + R) : ptree E M R :=
  match x with
  | inl j => Tau (PTree.iter pstruct_iter_codiagonal_flat_step j)
  | inr r => Ret r
  end.

Inductive pstruct_iter_codiagonal_clo :
    ptree E M R -> ptree E M R -> Prop :=
  | PStIterCodiagonalMain i :
      pstruct_iter_codiagonal_clo
        (pstruct_iter_codiagonal_nested i)
        (PTree.iter pstruct_iter_codiagonal_flat_step i)
  | PStIterCodiagonalOuter i :
      pstruct_iter_codiagonal_clo
        (PTree.bind (PTree.iter step i)
          pstruct_iter_codiagonal_outer_handler)
        (PTree.iter pstruct_iter_codiagonal_flat_step i)
  | PStIterCodiagonalBind t :
      pstruct_iter_codiagonal_clo
        (PTree.bind
          (PTree.bind t pstruct_iter_codiagonal_inner_handler)
          pstruct_iter_codiagonal_outer_handler)
        (PTree.bind
          (PTree.bind t
            (fun x => Ret (pstruct_iter_codiagonal_flatten x)))
          pstruct_iter_codiagonal_flat_handler)
  | PStIterCodiagonalDone t1 t2 :
      pstruct eq t1 t2 -> pstruct_iter_codiagonal_clo t1 t2.

Theorem pstruct_iter_codiagonal i :
  pstruct eq
    (pstruct_iter_codiagonal_nested i)
    (PTree.iter pstruct_iter_codiagonal_flat_step i).
Proof.
  assert (Hstrong : forall u v, pstruct_iter_codiagonal_clo u v ->
      pstruct eq u v).
  { unfold pstruct. coinduction CH CIH.
    intros u v Hclo.
    inversion Hclo as [j|j|t|t1 t2 Hdone]; subst.
    - unfold pstruct_body, pstruct_iter_codiagonal_nested.
      change (pstructF eq (` CH)
        (observe (PTree.iter (fun j0 => PTree.iter step j0) j))
        (observe (PTree.iter pstruct_iter_codiagonal_flat_step j))).
      rewrite (observing_observe
        (unfold_aloop_ (fun j0 => PTree.iter step j0) j)).
      rewrite (observing_observe
        (unfold_aloop_ pstruct_iter_codiagonal_flat_step j)).
      rewrite !observe_bind.
      rewrite (observing_observe (unfold_aloop_ step j)).
      rewrite !observe_bind.
      remember (observe (step j)) as ot eqn:Hot.
      destruct ot as [x|t'|X e c|X mu c]; cbn.
      + destruct x as [j'|[j'|r]]; cbn.
        * constructor. apply CIH. constructor.
        * constructor. apply CIH. constructor.
        * constructor. reflexivity.
      + constructor. apply CIH. constructor.
      + constructor=> x. apply CIH. constructor.
      + constructor=> x. apply CIH. constructor.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.bind (PTree.iter step j)
          pstruct_iter_codiagonal_outer_handler))
        (observe (PTree.iter pstruct_iter_codiagonal_flat_step j))).
      rewrite observe_bind.
      rewrite (observing_observe (unfold_aloop_ step j)).
      rewrite (observing_observe
        (unfold_aloop_ pstruct_iter_codiagonal_flat_step j)).
      rewrite !observe_bind.
      remember (observe (step j)) as ot eqn:Hot.
      destruct ot as [x|t'|X e c|X mu c]; cbn.
      + destruct x as [j'|[j'|r]]; cbn.
        * constructor. apply CIH. constructor.
        * constructor. apply CIH. constructor.
        * constructor. reflexivity.
      + constructor. apply CIH. constructor.
      + constructor=> x. apply CIH. constructor.
      + constructor=> x. apply CIH. constructor.
    - unfold pstruct_body.
      change (pstructF eq (` CH)
        (observe (PTree.bind
          (PTree.bind t pstruct_iter_codiagonal_inner_handler)
          pstruct_iter_codiagonal_outer_handler))
        (observe (PTree.bind
          (PTree.bind t
            (fun x => Ret (pstruct_iter_codiagonal_flatten x)))
          pstruct_iter_codiagonal_flat_handler))).
      rewrite !observe_bind.
      remember (observe t) as ot eqn:Hot.
      destruct ot as [x|t'|X e c|X mu c]; cbn.
      + destruct x as [j'|[j'|r]]; cbn.
        * constructor. apply CIH. constructor.
        * constructor. apply CIH. constructor.
        * constructor. reflexivity.
      + constructor. apply CIH. constructor.
      + constructor=> x. apply CIH. constructor.
      + constructor=> x. apply CIH. constructor.
    - unfold pstruct_body.
      pose proof (pstruct_unfold Hdone) as Hstep.
      eapply pstructF_monotone; [|exact Hstep].
      intros x y Hxy. apply CIH. constructor. exact Hxy. }
  apply Hstrong. constructor.
Qed.

End PStructIterCodiagonal.

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
