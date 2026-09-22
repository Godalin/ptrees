(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
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

Lemma reg_half_val : reg_half = (1 / 2 : rat).
Proof. reflexivity. Qed.

Lemma reg_quarter_val : reg_quarter = (1 / 4 : rat).
Proof. reflexivity. Qed.

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
  ~ enumQ_repr_eq reg_fair reg_fair_reordered.
Proof. move=> H. discriminate H. Qed.

Lemma reg_reordering_meas_eq :
  @meas_eq EnumQ EnumQ_MeasureInterface bool
    reg_fair reg_fair_reordered.
Proof. exact: enumQ_meas_eq_of_eqenum reg_fair_reordered_eqenum. Qed.

(** Repeated outcomes and split probability mass cannot reproduce the old
    repeated-mass bug: only their accumulated probability matters. *)
Lemma reg_split_mass_not_repr_eq :
  ~ enumQ_repr_eq reg_fair reg_fair_split.
Proof. move=> H. discriminate H. Qed.

Lemma reg_split_mass_meas_eq :
  @meas_eq EnumQ EnumQ_MeasureInterface bool reg_fair reg_fair_split.
Proof. exact: enumQ_meas_eq_of_eqenum reg_fair_split_eqenum. Qed.

Lemma reg_split_mass_lift_eq :
  @meas_lift EnumQ EnumQ_MeasureInterface bool bool eq
    reg_fair reg_fair_split.
Proof. exact: enumQ_meas_eq_of_eqenum reg_fair_split_eqenum. Qed.

Unset Automatic Proposition Inductives.
Variant regE : Type -> Type := .

Definition reg_split_program : ptree regE EnumQ bool :=
  Prob reg_fair_split (fun b => Ret b).

(** Dirac sampling is observationally silent, without requiring an [eqType]
    instance for the sampled carrier.  Its behavioral regression now belongs
    to the canonical stable-hitting examples, not to this measure fixture. *)
Definition reg_dirac_program : ptree regE EnumQ bool :=
  Prob (ret_EnumQ true) (fun b => Ret b).

(** The non-trivial flattening example from the roadmap:

       1/2 (1/2 A + 1/2 B) + 1/2 (1/2 A + 1/2 C)

    is weakly equivalent to [1/2 A + 1/4 B + 1/4 C]. *)
Definition reg_inner (side : bool) : EnumQ nat :=
  if side then unif2 0 2 else unif2 0 1.

Definition reg_nested_program : ptree regE EnumQ nat :=
  Prob reg_fair (fun side =>
    Prob (reg_inner side) (fun outcome => Ret outcome)).

Definition reg_merged_three : EnumQ nat.
Proof.
  refine (enumQ_of_list (mu := [:: (reg_half, 0); (reg_quarter, 1); (reg_quarter, 2)]) _).
  intros p x [He|[He|[He|[]]]]; inversion He; subst; by vm_compute.
Defined.

Definition reg_merged_program : ptree regE EnumQ nat :=
  Prob reg_merged_three (fun outcome => Ret outcome).

Lemma reg_nested_outcomes_eqenum :
  bind_EnumQ reg_fair reg_inner ==EnumQ reg_merged_three.
Proof. intros [|[|[|n]]]; by vm_compute. Qed.
