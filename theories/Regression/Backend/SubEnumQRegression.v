(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

From Coq.Program Require Import Equality.
From mathcomp Require Import ssreflect ssrbool seq ssralg ssrnum order rat.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import WellFormedness.
Require Import PTree.Prob.Backend.EnumQ.Representation.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure PTree.Prob.Backend.SubEnumQ.Measure.
From PTree.Eq Require Import ProbabilisticTrace.
From PTree.Eq.FreeOmega Require Import Base Hitting Relation Bind Algebra Iter.
From PTree.Interp.FreeOmega Require Import Base Guarded.
From PTree.Eq Require Import PEutt.
From PTree.Regression.Backend Require Import EnumQMeasureRegression.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ.
Import RatSubTypes.
Import GRing.Theory Order.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

Unset Automatic Proposition Inductives.
Variant subenumQE : Type -> Type := .

Lemma reg_fair_subprob : enumQ_subprob reg_fair.
Proof.
  rewrite /enumQ_subprob /enumQ_mass /reg_fair /= !mulr1 addr0.
  native_compute.
  reflexivity.
Qed.

Definition subenumQ_fair : SubEnumQ bool :=
  @enumQ_as_subprob bool reg_fair reg_fair_subprob.

Lemma reg_fair_split_subprob : enumQ_subprob reg_fair_split.
Proof.
  rewrite /enumQ_subprob /enumQ_mass /reg_fair_split /= !mulr1 addr0.
  native_compute. reflexivity.
Qed.

Definition subenumQ_fair_split : SubEnumQ bool :=
  @enumQ_as_subprob bool reg_fair_split reg_fair_split_subprob.

Definition subenumQ_direct_coin : ptree subenumQE SubEnumQ bool :=
  Prob subenumQ_fair (fun b : bool => Ret b).

Definition subenumQ_split_coin : ptree subenumQE SubEnumQ bool :=
  Prob subenumQ_fair_split (fun b : bool => Ret b).

Local Notation SubMF := (FreeOmega SubEnumQ).
Local Notation subpeutt :=
  (@peutt subenumQE SubEnumQ SubMF
    (FreeOmegaObservableSemanticMeasure
      (NI := SubEnumQ_SemanticMeasure)
      (NO := SubEnumQ_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega).

Lemma subenumQ_fair_split_lift :
  @sem_lift SubEnumQ SubEnumQ_SemanticMeasure bool bool eq
    subenumQ_fair subenumQ_fair_split.
Proof. exact reg_split_mass_lift_eq. Qed.

(** The canonical bounded backend supports the same extensional rewriting:
    splitting probability mass changes representation, not behavior. *)
Theorem subenumQ_split_coin_equivalent :
  subpeutt eq subenumQ_direct_coin subenumQ_split_coin.
Proof.
  apply peutt_prob_measure.
  exact subenumQ_fair_split_lift.
Qed.

(** The same raw representation that served as the legacy unnormalised
    [disc_flip] has total weight two.  It is a valid [EnumQ] weighting but
    cannot be admitted as a native probability node through [SubEnumQ]. *)
Definition enumQ_overweight_flip : EnumQ bool :=
  [:: ((1 : nnQ), false); ((1 : nnQ), true)].

Lemma enumQ_overweight_flip_mass : enumQ_mass enumQ_overweight_flip = 2.
Proof. reflexivity. Qed.

Lemma enumQ_overweight_flip_not_subprob :
  ~ enumQ_subprob enumQ_overweight_flip.
Proof.
  rewrite /enumQ_subprob enumQ_overweight_flip_mass.
  native_compute.
  discriminate.
Qed.

Definition enumQ_overweight_program : ptree subenumQE EnumQ bool :=
  Prob enumQ_overweight_flip (fun b : bool => Ret b).

Lemma enumQ_overweight_program_not_probabilistic :
  ~ @probabilistic_ptree subenumQE EnumQ EnumQ_SemanticMeasure
      EnumQ_SemanticSubprobability bool enumQ_overweight_program.
Proof.
  intro Hwf. unfold probabilistic_ptree in Hwf. cbn in Hwf.
  dependent destruction Hwf.
  exact (enumQ_overweight_flip_not_subprob H).
Qed.

Lemma subenumQ_direct_coin_probabilistic :
  @probabilistic_ptree subenumQE SubEnumQ SubEnumQ_SemanticMeasure
    SubEnumQ_SemanticSubprobability bool subenumQ_direct_coin.
Proof. apply probabilistic_ptree_intrinsic. Qed.

(** Bind remains inside the carrier without asking clients to re-establish
    a global mass inequality after every probabilistic composition. *)
Definition subenumQ_two_coins : SubEnumQ (bool * bool) :=
  subenumQ_bind subenumQ_fair (fun b1 =>
    subenumQ_bind subenumQ_fair (fun b2 => subenumQ_ret (b1, b2))).

Lemma subenumQ_two_coins_bounded :
  enumQ_subprob (subenumQ_raw subenumQ_two_coins).
Proof. exact (subenumQ_bound subenumQ_two_coins). Qed.
