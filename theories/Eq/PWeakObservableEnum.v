Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8.

From mathcomp Require Import ssreflect ssrbool eqtype seq.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC FrontierLift FrontierLiftEnum
  MeasureIteration MeasureIterationEnum.
From PTree.Eq Require Import PWeakAbstract PWeakUnbounded.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum EnumMap.

(** Boolean return observations on stable heads.  Visible heads do not count
    as returns; their continuations remain observable at later transitions. *)
Definition auhead_returns {E R} (P : R -> bool)
    (h : aphead E Enum R) : bool :=
  match h with
  | APHRet r => P r
  | @APHVis _ _ _ X e k => false
  end.

Section FiniteObservableConsequences.
Context {E : Type -> Type}.

Theorem apweak_preserves_return_observation {R1 R2}
    (RR : R1 -> R2 -> Prop) (P : R1 -> bool) (Q : R2 -> bool)
    (t1 : ptree E Enum R1) (t2 : ptree E Enum R2)
    (hs1 : Enum (aphead E Enum R1)) :
  (forall x y, RR x y -> P x = Q y) ->
  apweak RR t1 t2 ->
  apfrontier (observe t1) hs1 ->
  exists hs2,
    apfrontier (observe t2) hs2 /\
    @meas_eq Enum Enum_MeasureInterface bool
      (emap (auhead_returns P) hs1)
      (emap (auhead_returns Q) hs2).
Proof.
  move=> HPQ Hweak Hfront.
  have Hstep := apweak_unfold Hweak.
  destruct (apweakF_frontier_l
    (RR := RR) (sim := apweak RR) Hstep Hfront)
    as [hs2 [Hfront2 Hlift]].
  exists hs2. split=> //.
  apply enum_meas_lift_observe with
      (R := aphead_rel RR (apweak RR)); last exact Hlift.
  move=> h1 h2 Hh. inversion Hh; subst=> //=.
  exact (HPQ _ _ H).
Qed.

End FiniteObservableConsequences.

Lemma common_aufrontier_return_observation {E R}
    (P : R -> bool) (t1 t2 : ptree E Enum R)
    (hs : Enum (aphead E Enum R)) :
  aufrontier (observe t1) hs ->
  aufrontier (observe t2) hs ->
  exists hs1 hs2,
    aufrontier (observe t1) hs1 /\
    aufrontier (observe t2) hs2 /\
    @meas_eq Enum Enum_MeasureInterface bool
      (emap (auhead_returns P) hs1)
      (emap (auhead_returns P) hs2).
Proof.
  move=> H1 H2. exists hs, hs. repeat split=> //.
Qed.

Section ObservableConsequences.
Context {E : Type -> Type}.
Context `{UC : @UnboundedFrontierCoherence E Enum
  Enum_MeasureInterface Enum_MeasureOmegaInterface}.

(** A weak bisimulation preserves every pair of Boolean return events that
    its result relation identifies.  The conclusion is extensional equality
    of the complete Boolean distributions; in particular their [true] masses
    (the event probabilities) coincide. *)
Theorem auweak_preserves_return_observation {R1 R2}
    (RR : R1 -> R2 -> Prop) (P : R1 -> bool) (Q : R2 -> bool)
    (t1 : ptree E Enum R1) (t2 : ptree E Enum R2)
    (hs1 : Enum (aphead E Enum R1)) :
  (forall x y, RR x y -> P x = Q y) ->
  auweak RR t1 t2 ->
  aufrontier (observe t1) hs1 ->
  exists hs2,
    aufrontier (observe t2) hs2 /\
    @meas_eq Enum Enum_MeasureInterface bool
      (emap (auhead_returns P) hs1)
      (emap (auhead_returns Q) hs2).
Proof.
  move=> HPQ Hweak Hfront.
  have Hstep := auweak_unfold Hweak.
  destruct (auweakF_frontier_l
    (RR := RR) (sim := auweak RR) Hstep Hfront)
    as [hs2 [Hfront2 Hlift]].
  exists hs2. split=> //.
  apply enum_meas_lift_observe with
      (R := aphead_rel RR (auweak RR)); last exact Hlift.
  move=> h1 h2 Hh. inversion Hh; subst=> //=.
  exact (HPQ _ _ H).
Qed.

(** Most clients compare programs with the same return type. *)
Corollary auweak_eq_preserves_return_observation {R}
    (P : R -> bool) (t1 t2 : ptree E Enum R)
    (hs1 : Enum (aphead E Enum R)) :
  auweak eq t1 t2 ->
  aufrontier (observe t1) hs1 ->
  exists hs2,
    aufrontier (observe t2) hs2 /\
    @meas_eq Enum Enum_MeasureInterface bool
      (emap (auhead_returns P) hs1)
      (emap (auhead_returns P) hs2).
Proof.
  apply auweak_preserves_return_observation.
  move=> x y ->. reflexivity.
Qed.

End ObservableConsequences.
