Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Morphisms RelationClasses.
From Coq Require Import Program.Basics Relations.Relation_Definitions.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import PEutt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Generic endpoint rewriting.  Any proof relation registered as a
    [subrelation] of [peutt] can rewrite either endpoint; no relation-specific
    family of helper lemmas is needed. *)
Section PEuttRewrite.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.
Context {A : Type}.

Let W : relation (ptree E MN A) :=
  @peutt E MN MF FI FC MX FO A A eq.

Lemma peutt_rewrite_l (R : relation (ptree E MN A))
    `{Hsub : subrelation _ R W} x x' y :
  R x x' -> W x' y -> W x y.
Proof.
  intros Hxx' Hx'y. eapply peutt_trans; [exact (Hsub _ _ Hxx')|exact Hx'y].
Qed.

Lemma peutt_rewrite_r (R : relation (ptree E MN A))
    `{Hsub : subrelation _ R W} x y' y :
  W x y' -> R y' y -> W x y.
Proof.
  intros Hxy' Hy'y. eapply peutt_trans; [exact Hxy'|exact (Hsub _ _ Hy'y)].
Qed.

Lemma peutt_rewrite (R : relation (ptree E MN A))
    `{Hsub : subrelation _ R W} x x' y' y :
  R x x' -> W x' y' -> R y' y -> W x y.
Proof.
  intros Hxx' Hx'y' Hy'y.
  eapply peutt_trans; [exact (Hsub _ _ Hxx')|].
  eapply peutt_trans; [exact Hx'y'|exact (Hsub _ _ Hy'y)].
Qed.

#[global] Instance peutt_endpoint_Proper
    (R : relation (ptree E MN A)) `{Hsub : subrelation _ R W} :
  Proper (R ==> R ==> impl) W.
Proof.
  intros x x' Hxx' y y' Hyy' Hxy.
  eapply peutt_trans.
  - apply peutt_sym. exact (Hsub _ _ Hxx').
  - eapply peutt_trans; [exact Hxy|exact (Hsub _ _ Hyy')].
Qed.

End PEuttRewrite.
