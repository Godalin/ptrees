Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 Program Morphisms.

From Coinduction Require Import all.
From mathcomp Require Import ssreflect ssrbool eqtype seq.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC Coupling IndexedCoupling.
From PTree.Eq Require Import PFrontier.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum Coupling IndexedCoupling.

Section PWeak.

Context {E : Type -> Type}.
Context {R1 R2 : Type}.
Variable RR : R1 -> R2 -> Prop.

(**
  [PWFrontier] may consume any finite tree made from [Tau] and [Prob] before
  coupling its stable [Ret]/[Vis] leaves.  [PWTau] and [PWProb] remain as
  guarded coinductive rules, so divergent Tau/probability trees still relate
  to themselves without acquiring a finite frontier.

  The recursive premises of [PWTauL]/[PWTauR] remain inductive.  Consequently
  only finitely many unmatched Tau nodes can be discarded.
*)
Inductive pweakF
    (sim : ptree E Enum R1 -> ptree E Enum R2 -> Prop)
    : ptree' E Enum R1 -> ptree' E Enum R2 -> Prop :=
  | PWFrontier ot1 ot2 hs1 hs2 :
      pfrontier ot1 hs1 ->
      pfrontier ot2 hs2 ->
      indexed_coupling (phead_rel RR sim) hs1 hs2 ->
      pweakF sim ot1 ot2
  | PWTau t1 t2 :
      frontier_match RR sim (TauF t1) (TauF t2) ->
      sim t1 t2 ->
      pweakF sim (TauF t1) (TauF t2)
  | PWProb {X Y : eqType} (mu : Enum X) (nu : Enum Y) k1 k2 :
      frontier_match RR sim (ProbF mu k1) (ProbF nu k2) ->
      coupling (fun x y => sim (k1 x) (k2 y)) mu nu ->
      pweakF sim (ProbF mu k1) (ProbF nu k2)
  | PWTauL t1 ot2 :
      pweakF sim (observe t1) ot2 ->
      pweakF sim (TauF t1) ot2
  | PWTauR ot1 t2 :
      pweakF sim ot1 (observe t2) ->
      pweakF sim ot1 (TauF t2).

Lemma pweakF_monotone
    (sim1 sim2 : ptree E Enum R1 -> ptree E Enum R2 -> Prop) :
  (forall t1 t2, sim1 t1 t2 -> sim2 t1 t2) ->
  forall ot1 ot2,
    pweakF sim1 ot1 ot2 ->
    pweakF sim2 ot1 ot2.
Proof.
  move=> Hsim ot1 ot2 Hstep.
  induction Hstep.
  - eapply PWFrontier; [exact H|exact H0|].
    eapply indexed_coupling_mono; [|exact H1].
    move=> h1 h2 Hh.
    eapply phead_rel_mono; [exact Hsim|exact Hh].
  - constructor.
    + exact: frontier_match_mono Hsim H.
    + exact: Hsim H0.
  - constructor.
    + exact: frontier_match_mono Hsim H.
    + eapply coupling_mono; [|exact H0].
      move=> x y Hxy. exact: Hsim Hxy.
  - apply PWTauL. exact IHHstep.
  - apply PWTauR. exact IHHstep.
Qed.

Definition pweak_body
    (sim : ptree E Enum R1 -> ptree E Enum R2 -> Prop)
    (t1 : ptree E Enum R1) (t2 : ptree E Enum R2) : Prop :=
  pweakF sim (observe t1) (observe t2).

Program Definition fpweak :
    mon (ptree E Enum R1 -> ptree E Enum R2 -> Prop) :=
  {| body := pweak_body |}.
Next Obligation.
  move=> sim1 sim2 Hsub t1 t2 Hstep.
  eapply pweakF_monotone; [exact Hsub|exact Hstep].
Qed.

Definition pweak : ptree E Enum R1 -> ptree E Enum R2 -> Prop :=
  gfp fpweak.

Lemma pweak_unfold t1 t2 :
  pweak t1 t2 -> pweakF pweak (observe t1) (observe t2).
Proof.
  move=> H.
  apply (gfp_pfp fpweak) in H.
  exact H.
Qed.

Lemma pweak_fold t1 t2 :
  pweakF pweak (observe t1) (observe t2) -> pweak t1 t2.
Proof.
  move=> H.
  unfold pweak.
  apply (gfp_fp fpweak).
  exact H.
Qed.

End PWeak.
