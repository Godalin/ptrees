Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import FunctionalExtensionality.

From mathcomp Require Import ssreflect ssrbool eqtype seq.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC EnumBindFacts EnumMap FrontierLift
  FrontierLiftEnum MeasureIteration MeasureIterationEnum TwoLevelMeasure
  TwoLevelMeasureEnum.
From PTree.Eq Require Import PWeakAbstract UnifiedFrontier.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum EnumMap.

Definition aphead_to_frontier_head {E R}
    (h : aphead E Enum R) : frontier_head E Enum R :=
  match h with
  | APHRet r => FHRet r
  | @APHVis _ _ _ X e k => FHVis e k
  end.

(** Every finite derivation from the established API embeds into the single
    unified frontier.  The output is merely pushed forward along the
    representation-independent head translation. *)
Theorem apfrontier_to_unified_frontier {E R}
    (ot : ptree' E Enum R) hs :
  apfrontier ot hs ->
  frontier ot (emap aphead_to_frontier_head hs).
Proof.
  move=> Hf. induction Hf.
  - cbn. constructor.
  - cbn. constructor.
  - exact: UFTau IHHf.
  - rewrite emap_bind.
    apply (@UFProb E Enum Enum
      Enum_SemanticMeasureInterface Enum_SemanticMeasureInterface
      Enum_MixedMeasureInterface Enum_SemanticOmegaInterface
      R X mu k
      (fun x => emap aphead_to_frontier_head (front x)) Good).
    + exact H.
    + move=> x Hx. exact: H1 Hx.
Qed.

Lemma enum_mixed_iter_approx {I R} n
    (transition : I -> Enum (I + R)) i :
  mixed_iter_approx n transition i =
  meas_iter_approx n transition i.
Proof.
  elim: n i=> [|n IH] i; first reflexivity.
  cbn. apply bind_Enum_ext=> -[i'|r]; last reflexivity.
  exact: IH.
Qed.

Lemma enum_mixed_iter_iff_meas_iter {I R}
    (transition : I -> Enum (I + R)) i out :
  mixed_iter transition i out <-> meas_iter transition i out.
Proof.
  unfold mixed_iter, meas_iter.
  change (enum_converges
    (fun n => mixed_iter_approx n transition i) out <->
    enum_converges
      (fun n => meas_iter_approx n transition i) out).
  have E : (fun n => mixed_iter_approx n transition i) =
      (fun n => meas_iter_approx n transition i).
  { apply functional_extensionality=> n. exact: enum_mixed_iter_approx. }
  by rewrite E.
Qed.

(** The same bridge is available through the extensional closure: clients
    may choose any old frontier representative and then use [sem_eq] in the
    new layer. *)
Corollary apfrontier_sem_to_unified_frontier {E R}
    (ot : ptree' E Enum R) hs :
  apfrontier_sem ot hs ->
  exists hs0,
    frontier ot (emap aphead_to_frontier_head hs0) /\
    @meas_eq Enum Enum_MeasureInterface (aphead E Enum R) hs0 hs.
Proof.
  move=> [hs0 [Hf Heq]]. exists hs0. split.
  - exact: apfrontier_to_unified_frontier Hf.
  - exact Heq.
Qed.
