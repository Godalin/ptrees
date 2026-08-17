Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Program.

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssralg rat.

From PTree.Prob Require Import RatSubTypes DiscreteMC FrontierLift
  FrontierLiftEnum.
From PTree.Core Require Import PTreeDefinitionNew.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum GRing.Theory.
Import RatSubTypes.NonnegQNotations.
#[local] Open Scope ring_scope.

#[program] Definition reg_half : nnQ := [nn 1/2].
#[program] Definition reg_quarter : nnQ := [nn 1/4].

Lemma reg_half_val : Qval reg_half = (1 / 2 : rat).
Proof. reflexivity. Qed.

Lemma reg_quarter_val : Qval reg_quarter = (1 / 4 : rat).
Proof. reflexivity. Qed.

Definition reg_fair : Enum bool :=
  [:: (reg_half, false); (reg_half, true)].

Definition reg_fair_reordered : Enum bool :=
  [:: (reg_half, true); (reg_half, false)].

Definition reg_fair_split : Enum bool :=
  [:: (reg_quarter, false); (reg_quarter, false);
      (reg_quarter, true); (reg_quarter, true)].

Lemma reg_fair_reordered_eqenum :
  reg_fair ==Enum reg_fair_reordered.
Proof.
  move=> b; case: b; rewrite /reg_fair /reg_fair_reordered /acc_mass /=.
  all: apply val_inj; cbn; ring_to_rat; reflexivity.
Qed.

Lemma reg_fair_split_eqenum :
  reg_fair ==Enum reg_fair_split.
Proof.
  move=> b; case: b;
    rewrite /reg_fair /reg_fair_split /acc_mass /=.
  all: apply val_inj; cbn; ring_to_rat; reflexivity.
Qed.

(** Ordering is representation-visible but measure-invisible. *)
Lemma reg_reordering_not_repr_eq :
  ~ enum_repr_eq reg_fair reg_fair_reordered.
Proof. move=> H. discriminate H. Qed.

Lemma reg_reordering_meas_eq :
  @meas_eq Enum Enum_MeasureInterface bool
    reg_fair reg_fair_reordered.
Proof. exact: enum_meas_eq_of_eqenum reg_fair_reordered_eqenum. Qed.

(** Repeated outcomes and split probability mass cannot reproduce the old
    repeated-mass bug: only their accumulated probability matters. *)
Lemma reg_split_mass_not_repr_eq :
  ~ enum_repr_eq reg_fair reg_fair_split.
Proof. move=> H. discriminate H. Qed.

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

(** Dirac sampling is observationally silent, without requiring an [eqType]
    instance for the sampled carrier.  Its behavioral regression now belongs
    to the canonical stable-hitting examples, not to this measure fixture. *)
Definition reg_dirac_program : ptree regE Enum bool :=
  Prob (ret_Enum true) (fun b => Ret b).

(** The non-trivial flattening example from the roadmap:

       1/2 (1/2 A + 1/2 B) + 1/2 (1/2 A + 1/2 C)

    is weakly equivalent to [1/2 A + 1/4 B + 1/4 C]. *)
Definition reg_inner (side : bool) : Enum nat :=
  if side then [:: (reg_half, 0); (reg_half, 2)]
  else [:: (reg_half, 0); (reg_half, 1)].

Definition reg_nested_program : ptree regE Enum nat :=
  Prob reg_fair (fun side =>
    Prob (reg_inner side) (fun outcome => Ret outcome)).

Definition reg_merged_three : Enum nat :=
  [:: (reg_half, 0); (reg_quarter, 1); (reg_quarter, 2)].

Definition reg_merged_program : ptree regE Enum nat :=
  Prob reg_merged_three (fun outcome => Ret outcome).

Lemma reg_nested_outcomes_eqenum :
  bind_Enum reg_fair reg_inner ==Enum reg_merged_three.
Proof.
  move=> outcome.
  rewrite /reg_fair /reg_inner /reg_merged_three /bind_Enum /acc_mass /=.
  case: outcome=> [|[|[|outcome]]];
    apply val_inj; cbn; ring_to_rat; reflexivity.
Qed.
