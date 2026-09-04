Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Program.Equality.
From mathcomp Require Import ssreflect ssrbool seq ssralg ssrnum order rat.
From PTree.Core Require Import PTreeDefinition PTreeProbability.
From PTree.Prob Require Import DiscreteMC FreeOmegaMeasure
  TwoLevelMeasure TwoLevelMeasureEnum TwoLevelMeasureSubEnum.
From PTree.Eq Require Import OperationalProbabilisticPTSFreeOmega
  ProbabilisticEutt.
From PTree.Examples Require Import EnumMeasureRegression.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.
Import RatSubTypes.
Import GRing.Theory Order.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

Unset Automatic Proposition Inductives.
Variant subenumE : Type -> Type := .

Lemma reg_fair_subprob : enum_subprob reg_fair.
Proof.
  rewrite /enum_subprob /enum_mass /reg_fair /= !mulr1 addr0.
  native_compute.
  reflexivity.
Qed.

Definition subenum_fair : SubEnum bool :=
  @enum_as_subprob bool reg_fair reg_fair_subprob.

Lemma reg_fair_split_subprob : enum_subprob reg_fair_split.
Proof.
  rewrite /enum_subprob /enum_mass /reg_fair_split /= !mulr1 addr0.
  native_compute. reflexivity.
Qed.

Definition subenum_fair_split : SubEnum bool :=
  @enum_as_subprob bool reg_fair_split reg_fair_split_subprob.

Definition subenum_direct_coin : ptree subenumE SubEnum bool :=
  Prob subenum_fair (fun b : bool => Ret b).

Definition subenum_split_coin : ptree subenumE SubEnum bool :=
  Prob subenum_fair_split (fun b : bool => Ret b).

Local Notation SubMF := (FreeOmega SubEnum).
Local Notation subpeutt :=
  (@probabilistic_eutt subenumE SubEnum SubMF
    (FreeOmegaObservableSemanticMeasure
      (NI := SubEnum_SemanticMeasure)
      (NO := SubEnum_SemanticOmega))
    FreeOmegaObservableSemanticMeasureCoreLaws
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega).

Lemma subenum_fair_split_lift :
  @sem_lift SubEnum SubEnum_SemanticMeasure bool bool eq
    subenum_fair subenum_fair_split.
Proof. exact reg_split_mass_lift_eq. Qed.

(** The canonical bounded backend supports the same extensional rewriting:
    splitting probability mass changes representation, not behavior. *)
Theorem subenum_split_coin_equivalent :
  subpeutt eq subenum_direct_coin subenum_split_coin.
Proof.
  apply probabilistic_eutt_prob_measure.
  exact subenum_fair_split_lift.
Qed.

(** The same raw representation that served as the legacy unnormalised
    [disc_flip] has total weight two.  It is a valid [Enum] weighting but
    cannot be admitted as a native probability node through [SubEnum]. *)
Definition enum_overweight_flip : Enum bool :=
  [:: ((1 : nnQ), false); ((1 : nnQ), true)].

Lemma enum_overweight_flip_mass : enum_mass enum_overweight_flip = 2.
Proof. reflexivity. Qed.

Lemma enum_overweight_flip_not_subprob :
  ~ enum_subprob enum_overweight_flip.
Proof.
  rewrite /enum_subprob enum_overweight_flip_mass.
  native_compute.
  discriminate.
Qed.

Definition enum_overweight_program : ptree subenumE Enum bool :=
  Prob enum_overweight_flip (fun b : bool => Ret b).

Lemma enum_overweight_program_not_probabilistic :
  ~ @probabilistic_ptree subenumE Enum Enum_SemanticMeasure
      Enum_SemanticSubprobability bool enum_overweight_program.
Proof.
  intro Hwf. unfold probabilistic_ptree in Hwf. cbn in Hwf.
  dependent destruction Hwf.
  exact (enum_overweight_flip_not_subprob H).
Qed.

Lemma subenum_direct_coin_probabilistic :
  @probabilistic_ptree subenumE SubEnum SubEnum_SemanticMeasure
    SubEnum_SemanticSubprobability bool subenum_direct_coin.
Proof. apply probabilistic_ptree_intrinsic. Qed.

(** Bind remains inside the carrier without asking clients to re-establish
    a global mass inequality after every probabilistic composition. *)
Definition subenum_two_coins : SubEnum (bool * bool) :=
  subenum_bind subenum_fair (fun b1 =>
    subenum_bind subenum_fair (fun b2 => subenum_ret (b1, b2))).

Lemma subenum_two_coins_bounded :
  enum_subprob (subenum_raw subenum_two_coins).
Proof. exact (subenum_bound subenum_two_coins). Qed.
