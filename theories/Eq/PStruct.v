(** Role: Canonical equational/hitting theory. Depends on Core and Prob; does not provide comparison or interpreter semantics. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program Morphisms.

From Coinduction Require Import all.
From mathcomp Require Import ssreflect ssrbool eqtype seq.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import FrontierLift TwoLevelMeasure.
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

(** Heterogeneous converse, useful when transporting observations from a
    simpler return type back to the original program. *)
Lemma pstruct_converse {A B} (RR : A -> B -> Prop)
    (t1 : ptree E M A) (t2 : ptree E M B) :
  pstruct RR t1 t2 -> pstruct (fun b a => RR a b) t2 t1.
Proof.
  revert t1 t2. unfold pstruct at 2. coinduction CH CIH.
  move=> t1 t2 Hrel. move: (pstruct_unfold Hrel)=> Hstep.
  set ot1 := observe t1 in Hstep |- *.
  set ot2 := observe t2 in Hstep |- *.
  change (pstructF (fun b a => RR a b) (` CH) ot2 ot1).
  inversion Hstep as
      [r1 r2 HR | u1 u2 Hsim | X e k1 k2 Hk
       | X mu k1 k2 Hk]; subst.
  - constructor. exact HR.
  - constructor. exact: CIH Hsim.
  - constructor=> x. exact: CIH (Hk x).
  - constructor=> x. exact: CIH (Hk x).
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

(** First-stopping decomposition, without inserting a Tau at the boundary.
    Before the barrier the two bodies agree structurally and only retry.
    At the barrier the prefix returns the state from which the original
    iteration resumes.  No termination or probability hypothesis is needed.

    Unlike [pstruct_iter_rel], the stopping case does not compare two
    iteration bodies: only the prefix returns, while the source continues
    from the resumption state.  Naturality and codiagonal reorganize binds
    and nested iterations, but do not directly discharge this asymmetric
    boundary case.  This law packages that extra invariant argument. *)
Section PStructIterSplitAt.
Context {E M : Type -> Type} {I J B R : Type}.
Variables (step : I -> ptree E M (I + R))
  (prefix : J -> ptree E M (J + B)) (resume : B -> I).
Variable SI : I -> J -> Prop.

Let next_rel := pstruct_iter_sum_rel SI (fun (_ : R) (_ : B) => False).
Let source_cont (v : I + R) :=
  match v with inl i => Tau (PTree.iter step i) | inr r => Ret r end.
Let prefix_cont (v : J + B) :=
  match v with inl j => Tau (PTree.iter prefix j) | inr b => Ret b end.
Let rest b := PTree.iter step (resume b).

Hypothesis split_step : forall i j, SI i j ->
  (exists b, observe (prefix j) = RetF (inr b) /\ i = resume b) \/
  pstruct next_rel (step i) (prefix j).

Inductive pstruct_iter_split_clo : ptree E M R -> ptree E M R -> Prop :=
  | PStIterSplitMain i j : SI i j -> pstruct_iter_split_clo
      (PTree.iter step i) (PTree.bind (PTree.iter prefix j) rest)
  | PStIterSplitBind t1 t2 : pstruct next_rel t1 t2 -> pstruct_iter_split_clo
      (PTree.bind t1 source_cont)
      (PTree.bind (PTree.bind t2 prefix_cont) rest)
  | PStIterSplitDone t1 t2 : pstruct eq t1 t2 -> pstruct_iter_split_clo t1 t2.

Local Lemma iter_split_bind_step sim
    (Hmain : forall i j, SI i j ->
      sim (PTree.iter step i) (PTree.bind (PTree.iter prefix j) rest))
    (Hbind : forall t1 t2, pstruct next_rel t1 t2 ->
      sim (PTree.bind t1 source_cont)
        (PTree.bind (PTree.bind t2 prefix_cont) rest)) t1 t2 :
  pstruct next_rel t1 t2 ->
  pstructF eq sim (observe (PTree.bind t1 source_cont))
    (observe (PTree.bind (PTree.bind t2 prefix_cont) rest)).
Proof.
  intro Hrel. rewrite !observe_bind.
  pose proof (pstruct_unfold Hrel) as Hbody.
  remember (observe t1) as ot1 in Hbody |- *.
  remember (observe t2) as ot2 in Hbody |- *.
  destruct Hbody.
  - cbn.
    destruct H; [|contradiction]. cbn. constructor. apply Hmain. assumption.
  - cbn. constructor. apply Hbind. assumption.
  - cbn. constructor. intro v. apply Hbind. apply H.
  - cbn. constructor. intro v. apply Hbind. apply H.
Qed.

Theorem pstruct_iter_split_at i j :
  SI i j -> pstruct eq (PTree.iter step i)
    (PTree.bind (PTree.iter prefix j) (fun b => PTree.iter step (resume b))).
Proof.
  intro Hij.
  assert (Hsound : forall t1 t2, pstruct_iter_split_clo t1 t2 -> pstruct eq t1 t2).
  { unfold pstruct. coinduction CH CIH.
    intros t1 t2 Hclo. destruct Hclo as [i' j' Hstate|u1 u2 Hbody|u1 u2 Hdone].
    - change (pstructF eq (` CH) (observe (PTree.iter step i'))
        (observe (PTree.bind (PTree.iter prefix j') rest))).
      destruct (split_step Hstate) as [[b [Hstop ->]]|Hbody].
      + rewrite observe_bind.
        rewrite (observing_observe (unfold_aloop_ prefix j')).
        rewrite observe_bind Hstop. cbn.
        eapply pstructF_monotone; [|apply pstruct_unfold; apply pstruct_refl].
        intros v1 v2 Hv. apply CIH. apply PStIterSplitDone. exact Hv.
      + have Hprefix : observe (PTree.bind (PTree.iter prefix j') rest) =
            observe (PTree.bind (PTree.bind (prefix j') prefix_cont) rest).
        { rewrite !observe_bind.
          rewrite (observing_observe (unfold_aloop_ prefix j')).
          rewrite observe_bind. reflexivity. }
        rewrite (observing_observe (unfold_aloop_ step i')) Hprefix.
        eapply iter_split_bind_step; [| |exact Hbody].
        * intros i0 j0 Hs. apply CIH. now apply PStIterSplitMain.
        * intros v1 v2 Hv. apply CIH. now apply PStIterSplitBind.
    - change (pstructF eq (` CH) (observe (PTree.bind u1 source_cont))
        (observe (PTree.bind (PTree.bind u2 prefix_cont) rest))).
      eapply iter_split_bind_step; [| |exact Hbody].
      + intros i0 j0 Hs. apply CIH. now apply PStIterSplitMain.
      + intros v1 v2 Hv. apply CIH. now apply PStIterSplitBind.
    - change (pstructF eq (` CH) (observe u1) (observe u2)).
      eapply pstructF_monotone; [|exact (pstruct_unfold Hdone)].
      intros v1 v2 Hv. apply CIH. now apply PStIterSplitDone. }
  apply Hsound. now apply PStIterSplitMain.
Qed.

End PStructIterSplitAt.
