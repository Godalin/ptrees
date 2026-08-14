Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

From mathcomp Require Import ssreflect ssrbool eqtype.
From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import DiscreteMC FrontierLift FrontierLiftEnum
  TwoLevelMeasure TwoLevelMeasureEnum.
From PTree.Eq Require Import UnifiedFrontier.
From PTree.Examples Require Import EnumMeasureRegression.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.

(** First checked client of the two-level semantics.  Enum implements both
    layers, while the theorem itself mentions only the backend-independent
    unified frontier. *)
Definition unified_reg_split_heads :
    Enum (frontier_head regE Enum bool) :=
  mixed_bind reg_fair_split (fun b => sem_ret (FHRet b)).

Lemma reg_split_program_unified_frontier :
  frontier (observe reg_split_program) unified_reg_split_heads.
Proof.
  unfold reg_split_program, unified_reg_split_heads.
  apply (UFProb
    (front := fun b => sem_ret (FHRet b))
    (Good := fun _ => True)).
  - apply sem_ae_true.
  - move=> b _. constructor.
Qed.

(** Literal duplication and mass splitting remain invisible at the unified
    semantic layer because its Enum equality is the extensional coupling
    equality, not list equality. *)
Lemma unified_reg_split_extensional :
  sem_eq unified_reg_split_heads
    (mixed_bind reg_fair (fun b => sem_ret (FHRet b))).
Proof.
  change (@meas_eq Enum Enum_MeasureInterface
    (frontier_head regE Enum bool)
    (bind_Enum reg_fair_split (fun b => ret_Enum (FHRet b)))
    (bind_Enum reg_fair (fun b => ret_Enum (FHRet b)))).
  apply (@meas_bind_proper Enum Enum_MeasureInterface
    Enum_MeasureCongruenceLaws).
  - change (enum_meas_eq reg_fair_split reg_fair).
    apply enum_meas_eq_of_eqenum. apply enum_eq_sym.
    exact reg_fair_split_eqenum.
  - move=> b. apply (@meas_eq_refl Enum Enum_MeasureInterface
      Enum_MeasureCoreLaws Enum_MeasureLaws).
Qed.
