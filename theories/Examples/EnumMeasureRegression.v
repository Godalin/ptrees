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

(** Dirac sampling is observationally silent, without requiring an [eqType]
    instance for the sampled carrier in the generic theorem. *)
Definition reg_dirac_program : ptree regE Enum bool :=
  Prob (ret_Enum true) (fun b => Ret b).

Lemma reg_dirac_program_frontier :
  apfrontier_sem (observe reg_dirac_program)
    (ret_Enum (APHRet true)).
Proof.
  apply apfrontier_sem_prob_ret. constructor.
Qed.

Lemma reg_dirac_program_apweak :
  apweak eq reg_dirac_program (Ret true).
Proof.
  apply apweak_of_common_frontier_sem with
      (hs := ret_Enum (APHRet true)).
  - exact reg_dirac_program_frontier.
  - apply apfrontier_apfrontier_sem. constructor.
Qed.

(** The non-trivial flattening example from the roadmap:

       1/2 (1/2 A + 1/2 B) + 1/2 (1/2 A + 1/2 C)

    is weakly equivalent to [1/2 A + 1/4 B + 1/4 C]. *)
Definition reg_inner (side : bool) : Enum nat :=
  if side then [:: (reg_half, 0%N); (reg_half, 2%N)]
  else [:: (reg_half, 0%N); (reg_half, 1%N)].

Definition reg_nested_program : ptree regE Enum nat :=
  Prob reg_fair (fun side =>
    Prob (reg_inner side) (fun outcome => Ret outcome)).

Definition reg_merged_three : Enum nat :=
  [:: (reg_half, 0%N); (reg_quarter, 1%N); (reg_quarter, 2%N)].

Definition reg_merged_program : ptree regE Enum nat :=
  Prob reg_merged_three (fun outcome => Ret outcome).

Definition reg_nested_heads : Enum (aphead regE Enum nat) :=
  bind_Enum (bind_Enum reg_fair reg_inner)
    (fun outcome => ret_Enum (APHRet outcome)).

Definition reg_merged_heads : Enum (aphead regE Enum nat) :=
  bind_Enum reg_merged_three
    (fun outcome => ret_Enum (APHRet outcome)).

Lemma reg_nested_heads_eqenum :
  reg_nested_heads ==Enum reg_merged_heads.
Proof. move=> [outcome|X e k]; last destruct e. vm_compute. Qed.

Lemma reg_nested_program_frontier :
  apfrontier_sem (observe reg_nested_program) reg_nested_heads.
Proof.
  apply apfrontier_sem_prob_flatten.
  move=> outcome. constructor.
Qed.

Lemma reg_merged_program_frontier :
  apfrontier_sem (observe reg_merged_program) reg_merged_heads.
Proof.
  apply apfrontier_apfrontier_sem.
  apply (APFProb
    (front := fun outcome => ret_Enum (APHRet outcome))
    (Good := fun _ => True)); first apply meas_ae_true.
  move=> outcome _. constructor.
Qed.

Lemma reg_nested_program_merged_frontier :
  apfrontier_sem (observe reg_nested_program) reg_merged_heads.
Proof.
  eapply apfrontier_sem_proper; first exact reg_nested_program_frontier.
  exact: enum_meas_eq_of_eqenum reg_nested_heads_eqenum.
Qed.

Theorem reg_nested_merged_apweak :
  apweak eq reg_nested_program reg_merged_program.
Proof.
  apply apweak_of_common_frontier_sem with (hs := reg_merged_heads).
  - exact reg_nested_program_merged_frontier.
  - exact reg_merged_program_frontier.
Qed.
