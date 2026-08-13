Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

From mathcomp Require Import ssreflect ssrbool eqtype seq ssralg rat.

From PTree.Prob Require Import RatSubTypes DiscreteMC FrontierLift
  FrontierLiftEnum.
From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Eq Require Import PWeakAbstract.

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

Unset Automatic Proposition Inductives.
Variant regE : Type -> Type := .

Definition reg_split_program : ptree regE Enum bool :=
  Prob reg_fair_split (fun b => Ret b).

Definition reg_fair_heads : Enum (aphead regE Enum bool) :=
  bind_Enum reg_fair (fun b => ret_Enum (APHRet b)).

Definition reg_split_heads : Enum (aphead regE Enum bool) :=
  bind_Enum reg_fair_split (fun b => ret_Enum (APHRet b)).

Lemma reg_split_program_frontier :
  apfrontier (observe reg_split_program) reg_split_heads.
Proof.
  apply (APFProb
    (front := fun b => ret_Enum (APHRet b))
    (Good := fun _ => True)); first apply meas_ae_true.
  move=> b _. constructor.
Qed.

Lemma reg_split_heads_eqenum : reg_split_heads ==Enum reg_fair_heads.
Proof.
  apply bind_Enum_outer_proper. exact: reg_fair_split_eqenum.
Qed.

(** The extensional public judgment transports the canonical split frontier
    to the merged representation. *)
Lemma reg_split_program_extensional_frontier :
  apfrontier_sem (observe reg_split_program) reg_fair_heads.
Proof.
  exists reg_split_heads; split; first exact: reg_split_program_frontier.
  exact: enum_meas_eq_of_eqenum reg_split_heads_eqenum.
Qed.
