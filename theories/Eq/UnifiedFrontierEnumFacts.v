Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import FunctionalExtensionality.

From mathcomp Require Import ssreflect ssrbool eqtype seq.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC EnumBindFacts EnumMap FrontierLift
  FrontierLiftEnum MeasureIteration MeasureIterationEnum TwoLevelMeasure
  TwoLevelMeasureEnum.
From PTree.Eq Require Import PWeakAbstract PWeakUnbounded UnifiedFrontier.

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

Lemma bind_Enum_emap_source {A B C} (f : A -> B)
    (mu : Enum A) (k : B -> Enum C) :
  bind_Enum (emap f mu) k = bind_Enum mu (fun x => k (f x)).
Proof.
  elim: mu=> [|[p x] mu IH] //=.
  by rewrite IH.
Qed.

Lemma aphead_bind_translation {E A R}
    (k : A -> ptree E Enum R)
    (front : A -> Enum (aphead E Enum R))
    (h : aphead E Enum A) :
  emap aphead_to_frontier_head (aphead_bind_front k front h) =
  frontier_head_bind_front k
    (fun a => emap aphead_to_frontier_head (front a))
    (aphead_to_frontier_head h).
Proof. by destruct h. Qed.

(** Full compatibility bridge for the established AST-aware judgment.  All
    six old constructors map into native rules of the single frontier; no
    finite/infinite tag survives in the conclusion. *)
Theorem aufrontier_to_unified_frontier {E R}
    (ot : ptree' E Enum R) hs :
  aufrontier ot hs ->
  frontier ot (emap aphead_to_frontier_head hs).
Proof.
  move=> Hf. induction Hf.
  - exact: apfrontier_to_unified_frontier H.
  - exact: UFTau IHHf.
  - rewrite emap_bind.
    apply (@UFProb E Enum Enum
      Enum_SemanticMeasureInterface Enum_SemanticMeasureInterface
      Enum_MixedMeasureInterface Enum_SemanticOmegaInterface
      R X mu k
      (fun x => emap aphead_to_frontier_head (front x)) Good).
    + exact H.
    + move=> x Hx. exact: H1 Hx.
  - rewrite emap_bind.
    apply (@UFIter E Enum Enum
      Enum_SemanticMeasureInterface Enum_SemanticMeasureInterface
      Enum_MixedMeasureInterface Enum_SemanticOmegaInterface
      R I step transition i out).
    + move=> j. move: (H j)=> Hj.
      move: (apfrontier_to_unified_frontier Hj)=> Hnew.
      by rewrite emap_bind in Hnew.
    + apply enum_mixed_iter_iff_meas_iter. exact H0.
    + exact H1.
  - rewrite emap_bind.
    replace
      (bind_Enum hs
        (fun h => emap aphead_to_frontier_head
          (aphead_bind_front k front h)))
      with
      (bind_Enum (emap aphead_to_frontier_head hs)
        (frontier_head_bind_front k
          (fun a => emap aphead_to_frontier_head (front a)))).
    2:{ rewrite bind_Enum_emap_source. apply bind_Enum_ext=> h.
        symmetry. exact: aphead_bind_translation. }
    apply (@UFBind E Enum Enum
      Enum_SemanticMeasureInterface Enum_SemanticMeasureInterface
      Enum_MixedMeasureInterface Enum_SemanticOmegaInterface
      R A t k
      (emap aphead_to_frontier_head hs)
      (fun a => emap aphead_to_frontier_head (front a))).
    + exact IHHf.
    + assumption.
  - rewrite emap_bind.
    apply (@UFNestedIter E Enum Enum
      Enum_SemanticMeasureInterface Enum_SemanticMeasureInterface
      Enum_MixedMeasureInterface Enum_SemanticOmegaInterface
      R I step transition i out).
    + move=> j. move: (H0 j)=> Hnew.
      by rewrite emap_bind in Hnew.
    + apply enum_mixed_iter_iff_meas_iter. exact H1.
    + exact H2.
Qed.

Corollary aufrontier_sem_to_unified_frontier {E R}
    (ot : ptree' E Enum R) hs :
  aufrontier_sem ot hs ->
  exists hs0,
    frontier ot (emap aphead_to_frontier_head hs0) /\
    @meas_eq Enum Enum_MeasureInterface (aphead E Enum R) hs0 hs.
Proof.
  move=> [hs0 [Hf Heq]]. exists hs0. split.
  - exact: aufrontier_to_unified_frontier Hf.
  - exact Heq.
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
