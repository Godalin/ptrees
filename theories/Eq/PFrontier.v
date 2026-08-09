Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Morphisms Program.Equality.

From mathcomp Require Import ssreflect ssrbool eqtype seq.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC EnumBindFacts IndexedCoupling.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.

(**
  A stable probabilistic frontier stops immediately before the next externally
  observable return or visible event.  Continuations are deliberately stored
  in the leaves; no equality on them is required.
*)
Variant phead (E : Type -> Type) (R : Type) : Type :=
  | PHRet (r : R)
  | PHVis {X : Type} (e : E X) (k : X -> ptree E Enum R).

Arguments PHRet {E R} _.
Arguments PHVis {E R X} _ _.

Section Frontier.

Context {E : Type -> Type}.
Context {R : Type}.

Inductive pfrontier :
    ptree' E Enum R -> Enum (phead E R) -> Prop :=
  | PFReturn r :
      pfrontier (RetF r) (ret_Enum (PHRet r))
  | PFVisible {X} (e : E X) k :
      pfrontier (VisF e k) (ret_Enum (PHVis e k))
  | PFTau t hs :
      pfrontier (observe t) hs ->
      pfrontier (TauF t) hs
  | PFProb {X : eqType} (mu : Enum X) k
      (front : X -> Enum (phead E R)) :
      (forall x, pfrontier (observe (k x)) (front x)) ->
      pfrontier (ProbF mu k) (bind_Enum mu front).

End Frontier.

Section HeadRel.

Context {E : Type -> Type}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.
Variable sim : ptree E Enum R1 -> ptree E Enum R2 -> Prop.

Inductive phead_rel : phead E R1 -> phead E R2 -> Prop :=
  | PHRRet r1 r2 :
      RR r1 r2 ->
      phead_rel (PHRet r1) (PHRet r2)
  | PHRVis {X} (e : E X) k1 k2 :
      (forall x, sim (k1 x) (k2 x)) ->
      phead_rel (PHVis e k1) (PHVis e k2).

End HeadRel.

Arguments phead_rel {E R1 R2} RR sim _ _.

Inductive prelcomp {A B C}
    (R : A -> B -> Prop) (S : B -> C -> Prop)
    (a : A) (c : C) : Prop :=
  | prelcomp_intro b : R a b -> S b c -> prelcomp R S a c.

Lemma phead_rel_mono {E R1 R2}
    (RR : R1 -> R2 -> Prop)
    (sim1 sim2 : ptree E Enum R1 -> ptree E Enum R2 -> Prop) :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall h1 h2,
    phead_rel RR sim1 h1 h2 ->
    phead_rel RR sim2 h1 h2.
Proof.
  move=> Hsim h1 h2 Hh.
  inversion Hh; subst.
  - constructor. assumption.
  - constructor=> x. exact: Hsim (H x).
Qed.

Lemma phead_rel_rel_mono {E R1 R2}
    (RR SS : R1 -> R2 -> Prop)
    (sim : ptree E Enum R1 -> ptree E Enum R2 -> Prop) :
  (forall x y, RR x y -> SS x y) ->
  forall h1 h2,
    phead_rel RR sim h1 h2 ->
    phead_rel SS sim h1 h2.
Proof.
  move=> HRS h1 h2 Hh.
  inversion Hh; subst.
  - constructor. exact: HRS H.
  - constructor. exact H.
Qed.

Lemma phead_rel_sym {E R1 R2}
    (RR : R1 -> R2 -> Prop)
    (sim : ptree E Enum R1 -> ptree E Enum R2 -> Prop)
    (sim' : ptree E Enum R2 -> ptree E Enum R1 -> Prop) :
  (forall t1 t2, sim t1 t2 -> sim' t2 t1) ->
  forall h1 h2,
    phead_rel RR sim h1 h2 ->
    phead_rel (fun y x => RR x y) sim' h2 h1.
Proof.
  move=> Hsim h1 h2 Hh.
  inversion Hh; subst.
  - constructor. assumption.
  - constructor=> x. exact: Hsim (H x).
Qed.

Lemma phead_rel_refl {E R}
    (sim : ptree E Enum R -> ptree E Enum R -> Prop) :
  Reflexive sim ->
  Reflexive (phead_rel eq sim).
Proof.
  move=> Hsim h.
  destruct h as [r|X e k].
  - constructor. reflexivity.
  - constructor=> x. exact: Hsim (k x).
Qed.

Lemma pfrontier_deterministic {E R}
    (ot : ptree' E Enum R) hs1 hs2 :
  pfrontier ot hs1 ->
  pfrontier ot hs2 ->
  hs1 = hs2.
Proof.
  move=> H1.
  move: hs2.
  induction H1 as
      [r | X e k | t hs Hfront IH
       | X mu k front Hfronts IHs];
      move=> hs2 H2; dependent destruction H2.
  - reflexivity.
  - reflexivity.
  - match goal with
    | Hother : pfrontier (observe t) _ |- _ =>
        exact: IH Hother
    end.
  - apply bind_Enum_ext=> x.
    match goal with
    | Hother : forall y, pfrontier (observe (k y)) _ |- _ =>
        exact: IHs x _ (Hother x)
    end.
Qed.

Lemma pfrontier_tau_inv {E R}
    (t : ptree E Enum R) hs :
  pfrontier (TauF t) hs ->
  pfrontier (observe t) hs.
Proof.
  move=> H. dependent destruction H. assumption.
Qed.

Definition frontier_match {E R1 R2}
    (RR : R1 -> R2 -> Prop)
    (sim : ptree E Enum R1 -> ptree E Enum R2 -> Prop)
    (ot1 : ptree' E Enum R1) (ot2 : ptree' E Enum R2) : Prop :=
  (forall hs1,
      pfrontier ot1 hs1 ->
      exists hs2,
        pfrontier ot2 hs2 /\
        indexed_coupling (phead_rel RR sim) hs1 hs2) /\
  (forall hs2,
      pfrontier ot2 hs2 ->
      exists hs1,
        pfrontier ot1 hs1 /\
        indexed_coupling (phead_rel RR sim) hs1 hs2).

Lemma frontier_match_mono {E R1 R2}
    (RR : R1 -> R2 -> Prop)
    (sim1 sim2 : ptree E Enum R1 -> ptree E Enum R2 -> Prop)
    (ot1 : ptree' E Enum R1) (ot2 : ptree' E Enum R2) :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  frontier_match RR sim1 ot1 ot2 ->
  frontier_match RR sim2 ot1 ot2.
Proof.
  move=> Hsim [HL HR]; split.
  - move=> hs1 Hf.
    move: (HL hs1 Hf) => [hs2 [Hf2 Hc]].
    exists hs2. split=> //.
    eapply indexed_coupling_mono; [|exact Hc].
    move=> h1 h2 Hh.
    eapply phead_rel_mono; [exact Hsim|exact Hh].
  - move=> hs2 Hf.
    move: (HR hs2 Hf) => [hs1 [Hf1 Hc]].
    exists hs1. split=> //.
    eapply indexed_coupling_mono; [|exact Hc].
    move=> h1 h2 Hh.
    eapply phead_rel_mono; [exact Hsim|exact Hh].
Qed.

Lemma frontier_match_rel_mono {E R1 R2}
    (RR SS : R1 -> R2 -> Prop)
    (sim : ptree E Enum R1 -> ptree E Enum R2 -> Prop)
    (ot1 : ptree' E Enum R1) (ot2 : ptree' E Enum R2) :
  (forall x y, RR x y -> SS x y) ->
  frontier_match RR sim ot1 ot2 ->
  frontier_match SS sim ot1 ot2.
Proof.
  move=> HRS [HL HR]; split.
  - move=> hs1 Hf.
    move: (HL hs1 Hf) => [hs2 [Hf2 Hc]].
    exists hs2. split=> //.
    eapply indexed_coupling_mono; [|exact Hc].
    move=> h1 h2 Hh.
    exact: (phead_rel_rel_mono (RR := RR) (SS := SS) HRS Hh).
  - move=> hs2 Hf.
    move: (HR hs2 Hf) => [hs1 [Hf1 Hc]].
    exists hs1. split=> //.
    eapply indexed_coupling_mono; [|exact Hc].
    move=> h1 h2 Hh.
    exact: (phead_rel_rel_mono (RR := RR) (SS := SS) HRS Hh).
Qed.

Lemma frontier_match_refl {E R}
    (sim : ptree E Enum R -> ptree E Enum R -> Prop)
    (Hhead : Reflexive (phead_rel eq sim)) :
  forall ot, frontier_match eq sim ot ot.
Proof.
  move=> ot; split; move=> hs Hf; exists hs; split=> //;
    apply indexed_coupling_refl; exact Hhead.
Qed.

Lemma frontier_match_sym {E R1 R2}
    (RR : R1 -> R2 -> Prop)
    (sim : ptree E Enum R1 -> ptree E Enum R2 -> Prop)
    (sim' : ptree E Enum R2 -> ptree E Enum R1 -> Prop)
    (Hsim : forall t1 t2, sim t1 t2 -> sim' t2 t1) :
  forall ot1 ot2,
    frontier_match RR sim ot1 ot2 ->
    frontier_match (fun y x => RR x y) sim' ot2 ot1.
Proof.
  move=> ot1 ot2 [HL HR]; split.
  - move=> hs2 Hf2.
    move: (HR hs2 Hf2) => [hs1 [Hf1 Hc]].
    exists hs1. split=> //.
    eapply indexed_coupling_mono.
    + move=> h2 h1 Hh.
      eapply phead_rel_sym; [exact Hsim|exact Hh].
    + exact: indexed_coupling_sym Hc.
  - move=> hs1 Hf1.
    move: (HL hs1 Hf1) => [hs2 [Hf2 Hc]].
    exists hs2. split=> //.
    eapply indexed_coupling_mono.
    + move=> h2 h1 Hh.
      eapply phead_rel_sym; [exact Hsim|exact Hh].
    + exact: indexed_coupling_sym Hc.
Qed.

Lemma phead_rel_comp {E R1 R2 R3}
    (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
    (sim1 : ptree E Enum R1 -> ptree E Enum R2 -> Prop)
    (sim2 : ptree E Enum R2 -> ptree E Enum R3 -> Prop)
    (sim3 : ptree E Enum R1 -> ptree E Enum R3 -> Prop)
    (Hsim : forall t1 t2 t3,
      sim1 t1 t2 -> sim2 t2 t3 -> sim3 t1 t3) :
  forall h1 h2 h3,
    phead_rel RR1 sim1 h1 h2 ->
    phead_rel RR2 sim2 h2 h3 ->
    phead_rel (prelcomp RR1 RR2) sim3 h1 h3.
Proof.
  move=> h1 h2 h3 H12 H23.
  dependent destruction H12; dependent destruction H23.
  - constructor. by econstructor; eassumption.
  - constructor=> x. exact: Hsim _ _ _ (H x) (H0 x).
Qed.

Lemma frontier_match_comp {E R1 R2 R3}
    (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop)
    (sim1 : ptree E Enum R1 -> ptree E Enum R2 -> Prop)
    (sim2 : ptree E Enum R2 -> ptree E Enum R3 -> Prop)
    (sim3 : ptree E Enum R1 -> ptree E Enum R3 -> Prop)
    (Hsim : forall t1 t2 t3,
      sim1 t1 t2 -> sim2 t2 t3 -> sim3 t1 t3) :
  forall ot1 ot2 ot3,
    frontier_match RR1 sim1 ot1 ot2 ->
    frontier_match RR2 sim2 ot2 ot3 ->
    frontier_match (prelcomp RR1 RR2) sim3 ot1 ot3.
Proof.
  move=> ot1 ot2 ot3 [H12L H12R] [H23L H23R].
  split.
  - move=> hs1 Hf1.
    move: (H12L hs1 Hf1) => [hs2 [Hf2 Hc12]].
    move: (H23L hs2 Hf2) => [hs3 [Hf3 Hc23]].
    exists hs3. split=> //.
    have Hc := indexed_coupling_comp Hc12 Hc23.
    eapply (indexed_coupling_mono
      (R := fun h1 h3 => exists h2,
        phead_rel RR1 sim1 h1 h2 /\
        phead_rel RR2 sim2 h2 h3)
      (S := phead_rel (prelcomp RR1 RR2) sim3)).
    + move=> h1 h3 [h2 [Hh12 Hh23]].
      eapply phead_rel_comp; [exact Hsim|exact Hh12|exact Hh23].
    + exact Hc.
  - move=> hs3 Hf3.
    move: (H23R hs3 Hf3) => [hs2 [Hf2 Hc23]].
    move: (H12R hs2 Hf2) => [hs1 [Hf1 Hc12]].
    exists hs1. split=> //.
    have Hc := indexed_coupling_comp Hc12 Hc23.
    eapply (indexed_coupling_mono
      (R := fun h1 h3 => exists h2,
        phead_rel RR1 sim1 h1 h2 /\
        phead_rel RR2 sim2 h2 h3)
      (S := phead_rel (prelcomp RR1 RR2) sim3)).
    + move=> h1 h3 [h2 [Hh12 Hh23]].
      eapply phead_rel_comp; [exact Hsim|exact Hh12|exact Hh23].
    + exact Hc.
Qed.

Lemma frontier_match_tau {E R1 R2}
    (RR : R1 -> R2 -> Prop)
    (sim : ptree E Enum R1 -> ptree E Enum R2 -> Prop)
    (t1 : ptree E Enum R1) (t2 : ptree E Enum R2) :
  frontier_match RR sim (observe t1) (observe t2) ->
  frontier_match RR sim (TauF t1) (TauF t2).
Proof.
  move=> [HL HR]; split.
  - move=> hs1 Hf1. dependent destruction Hf1.
    move: (HL _ Hf1) => [hs2 [Hf2 Hc]].
    exists hs2. split=> //.
    exact: PFTau Hf2.
  - move=> hs2 Hf2. dependent destruction Hf2.
    move: (HR _ Hf2) => [hs1 [Hf1 Hc]].
    exists hs1. split=> //.
    exact: PFTau Hf1.
Qed.

Lemma frontier_match_untau_r {E R1 R2}
    (RR : R1 -> R2 -> Prop)
    (sim : ptree E Enum R1 -> ptree E Enum R2 -> Prop)
    (ot1 : ptree' E Enum R1) (t2 : ptree E Enum R2) :
  frontier_match RR sim ot1 (TauF t2) ->
  frontier_match RR sim ot1 (observe t2).
Proof.
  move=> [HL HR]; split.
  - move=> hs1 Hf1.
    move: (HL _ Hf1) => [hs2 [Hf2 Hc]].
    apply pfrontier_tau_inv in Hf2.
    by exists hs2.
  - move=> hs2 Hf2.
    have Htau : pfrontier (TauF t2) hs2 := PFTau Hf2.
    exact: HR _ Htau.
Qed.

Lemma frontier_match_untau_l {E R1 R2}
    (RR : R1 -> R2 -> Prop)
    (sim : ptree E Enum R1 -> ptree E Enum R2 -> Prop)
    (t1 : ptree E Enum R1) (ot2 : ptree' E Enum R2) :
  frontier_match RR sim (TauF t1) ot2 ->
  frontier_match RR sim (observe t1) ot2.
Proof.
  move=> [HL HR]; split.
  - move=> hs1 Hf1.
    have Htau : pfrontier (TauF t1) hs1 := PFTau Hf1.
    exact: HL _ Htau.
  - move=> hs2 Hf2.
    move: (HR _ Hf2) => [hs1 [Hf1 Hc]].
    apply pfrontier_tau_inv in Hf1.
    by exists hs1.
Qed.
