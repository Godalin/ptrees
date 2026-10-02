(** Role: finite probability/coupling/backend example. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

Require Import Program.

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssralg ssrnum rat.

Require Import PTree.Prob.Backend.EnumQ.Representation.
From PTree.Prob.Interface Require Import FrontierLift.
Require Import PTree.Prob.Backend.EnumQ.FrontierLift.
From PTree.Core Require Import PTreeDefinition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ GRing.Theory.
#[local] Open Scope ring_scope.

Definition reg_half : rat := 1/2.
Definition reg_quarter : rat := 1/4.

Definition reg_fair : EnumQ bool :=
  unif2 false true.

Definition reg_fair_reordered : EnumQ bool :=
  unif2 true false.

Definition reg_fair_split : EnumQ bool.
Proof.
  refine (enumQ_of_list (mu := [:: (reg_quarter, false); (reg_quarter, false);
      (reg_quarter, true); (reg_quarter, true)]) _).
  intros p x [He|[He|[He|[He|[]]]]]; inversion He; subst; by vm_compute.
Defined.

Lemma reg_fair_reordered_eqenum :
  reg_fair ==EnumQ reg_fair_reordered.
Proof. intros []; by vm_compute. Qed.

Lemma reg_fair_split_eqenum :
  reg_fair ==EnumQ reg_fair_split.
Proof. intros []; by vm_compute. Qed.

(** Ordering is representation-visible but measure-invisible. *)
Lemma reg_reordering_not_repr_eq :
  ¬ enumQ_repr_eq reg_fair reg_fair_reordered.
Proof. move=> H. discriminate H. Qed.

Lemma reg_reordering_meas_eq :
  @meas_eq EnumQ EnumQ_MeasureInterface bool
    reg_fair reg_fair_reordered.
Proof. exact: enumQ_meas_eq_of_eqenum reg_fair_reordered_eqenum. Qed.

(** Repeated outcomes and split probability mass cannot reproduce the old
    repeated-mass bug: only their accumulated probability matters. *)
Lemma reg_split_mass_not_repr_eq :
  ¬ enumQ_repr_eq reg_fair reg_fair_split.
Proof. move=> H. discriminate H. Qed.

Lemma reg_split_mass_meas_eq :
  @meas_eq EnumQ EnumQ_MeasureInterface bool reg_fair reg_fair_split.
Proof. exact: enumQ_meas_eq_of_eqenum reg_fair_split_eqenum. Qed.

Lemma reg_split_mass_lift_eq :
  @meas_lift EnumQ EnumQ_MeasureInterface bool bool eq
    reg_fair reg_fair_split.
Proof. exact: enumQ_meas_eq_of_eqenum reg_fair_split_eqenum. Qed.

Unset Automatic Proposition Inductives.
Variant regE : Type → Type := .

Definition reg_split_program : ptree regE EnumQ bool :=
  Prob reg_fair_split (fun b => Ret b).
