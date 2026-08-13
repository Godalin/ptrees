Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg rat.

From PTree.Prob Require Import RatSubTypes DiscreteMC FrontierLift
  FrontierLiftEnum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum GRing.Theory.
#[local] Open Scope ring_scope.

#[program] Definition reg_half : nnQ := [nn 1/2].
#[program] Definition reg_quarter : nnQ := [nn 1/4].

Definition reg_fair : Enum bool :=
  [:: (reg_half, false); (reg_half, true)].

Definition reg_fair_reordered : Enum bool :=
  [:: (reg_half, true); (reg_half, false)].

Definition reg_fair_split : Enum bool :=
  [:: (reg_quarter, false); (reg_quarter, false);
      (reg_quarter, true); (reg_quarter, true)].

Lemma reg_fair_reordered_eqenum :
  reg_fair ==Enum reg_fair_reordered.
Proof. move=> b. by destruct b; vm_compute. Qed.

Lemma reg_fair_split_eqenum :
  reg_fair ==Enum reg_fair_split.
Proof. move=> b. by destruct b; vm_compute. Qed.

(** Ordering is representation-visible but measure-invisible. *)
Lemma reg_reordering_not_repr_eq :
  ~ enum_repr_eq reg_fair reg_fair_reordered.
Proof. move=> H. vm_compute in H. discriminate. Qed.

Lemma reg_reordering_meas_eq :
  @meas_eq Enum Enum_MeasureInterface bool
    reg_fair reg_fair_reordered.
Proof. exact: enum_meas_eq_of_eqenum reg_fair_reordered_eqenum. Qed.

(** Repeated outcomes and split probability mass cannot reproduce the old
    repeated-mass bug: only their accumulated probability matters. *)
Lemma reg_split_mass_not_repr_eq :
  ~ enum_repr_eq reg_fair reg_fair_split.
Proof. move=> H. vm_compute in H. discriminate. Qed.

Lemma reg_split_mass_meas_eq :
  @meas_eq Enum Enum_MeasureInterface bool reg_fair reg_fair_split.
Proof. exact: enum_meas_eq_of_eqenum reg_fair_split_eqenum. Qed.

Lemma reg_split_mass_lift_eq :
  @meas_lift Enum Enum_MeasureInterface bool bool eq
    reg_fair reg_fair_split.
Proof. exact: enum_meas_eq_of_eqenum reg_fair_split_eqenum. Qed.
