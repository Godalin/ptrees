(** Boundary tests for exact rational interval selection. No hypothesis
    about a random oracle is used or claimed by these replay tests. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order rat.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Backend.Common Require Import FiniteEnum.
From PTree.Prob.Backend.SubEnumQ Require Import Representation.
From PTree.Execution Require Import Runner.
From PTree.Execution.Backend Require Import SubEnumQ.
Import GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.

Example zero_entry_never_selected :
  pick_interval [(0,false);(1,true)] 0 = Some true.
Proof. native_compute. reflexivity. Qed.
Example upper_endpoint_belongs_to_next_interval :
  pick_interval [(2^-1,false);(2^-1,true)] (2^-1) = Some true.
Proof. native_compute. reflexivity. Qed.
Example partial_mass_not_normalized :
  pick_interval [(4^-1,true);(4^-1,false)] (3 * 4^-1) = None.
Proof. native_compute. reflexivity. Qed.
Example duplicate_value_intervals_retained :
  pick_interval [(4^-1,true);(4^-1,false);(4^-1,true)] (5 * 8^-1) = Some true.
Proof. native_compute. reflexivity. Qed.

Definition half_entries : list (rat * unit) := [(2^-1,tt)].
Lemma half_nonnegative : finite_nonnegative half_entries.
Proof. intros p x [H|[]]; inversion H; subst; native_compute; reflexivity. Qed.
Lemma half_bounded : finite_expect (fun _ => 1) half_entries <= 1.
Proof. native_compute. reflexivity. Qed.
Definition half : SubEnumQ unit := subenumQ_of_list half_nonnegative half_bounded.
Definition high : quantile.
Proof. refine (@Build_quantile (3 * 4^-1) _ _); native_compute; reflexivity. Defined.
Definition closed_half : ptree void1 SubEnumQ unit := Prob half (fun x => Ret x).

Example half_mass_execution_is_lost :
  run (@replay_sample) 10 closed_half
    [high;high] = (Lost, [high]).
Proof. native_compute. reflexivity. Qed.
Example empty_replay_not_lost : replay_sample half [] = (NoEntropy, []).
Proof. reflexivity. Qed.

Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Eq.PEutt.peutt.
