(** Whole finite execution laws, not just one-step sampling smoke tests. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq ssralg ssrnum order rat reals.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Backend.Common Require Import FiniteEnum.
From PTree.Prob.Backend.SubEnumQ Require Import Representation.
From PTree.Execution Require Import Runner.
From PTree.Execution.Backend Require Import RationalTickets FiniteDistribution UniformReplay.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Eq.PEutt.peutt.
From PTree.Examples Require Import RationalState.
From PTree.Interp Require Import State.
Import GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.

CoFixpoint retry : ptree void1 SubEnumQ unit :=
  Prob attempt_coin (fun b => if b then Ret tt else Tau retry).
CoFixpoint spin : ptree void1 SubEnumQ unit := Tau spin.
Definition is_return {A} (r : outcome A) : rat := match r with Returned _ => 1 | _ => 0 end.
Definition is_lost {A} (r : outcome A) : rat := match r with Lost => 1 | _ => 0 end.
Definition is_timeout {A} (r : outcome A) : rat := match r with Timeout => 1 | _ => 0 end.

Example first_attempt_outcomes :
  outcome_expectation 1 retry is_return = 3^-1 /\
  outcome_expectation 1 retry is_lost = 6^-1 /\
  outcome_expectation 1 retry is_timeout = 2^-1.
Proof. repeat split; reflexivity. Qed.

Example two_attempt_outcomes :
  outcome_expectation 3 retry is_return = 2^-1 /\
  outcome_expectation 3 retry is_lost = 4^-1 /\
  outcome_expectation 3 retry is_timeout = 4^-1.
Proof. repeat split; reflexivity. Qed.

Example actual_runner_two_attempts :
  replay_expectation (fun _ d => uniform_indices d) 3 retry [] is_return = 2^-1.
Proof.
  rewrite (finite_runner_distribution fresh_uniform_entropy).
  exact (proj1 two_attempt_outcomes).
Qed.

Example eliminated_state_distribution :
  replay_expectation (fun _ d => uniform_indices d) 3
    (run_state rational_attempts 0%nat) [] is_return = 3^-1.
Proof.
  rewrite (finite_runner_distribution fresh_uniform_entropy).
  reflexivity.
Qed.

Example divergence_is_timeout_not_loss :
  outcome_expectation 4 spin is_return = 0 /\
  outcome_expectation 4 spin is_lost = 0 /\
  outcome_expectation 4 spin is_timeout = 1.
Proof. repeat split; reflexivity. Qed.

Example missing_mass_is_not_timeout :
  outcome_expectation 1 (Prob (@subenumQ_zero Empty_set)
    (fun x => match x return ptree void1 SubEnumQ unit with end)) is_lost = 1.
Proof. reflexivity. Qed.

Example ret_requires_no_fuel :
  outcome_expectation 0 (Ret tt : ptree void1 SubEnumQ unit) is_return = 1.
Proof. reflexivity. Qed.

Example zero_fuel_draw_requests_no_entropy :
  trace_distribution (fun _ d => uniform_indices d) 0 retry [] = [(1,[])].
Proof. reflexivity. Qed.

Definition unfair_source (_ : list nat) (_ : nat) : list (rat * nat) := [(1,0%nat)].
Example biased_entropy_rejected : ~ uniform_entropy unfair_source.
Proof.
  intro H. have Hlaw := proj2 (H [] 2%nat (Logic.eq_refl true)) (fun i => if i == 0%nat then 1 else 0).
  have Hbad : ((1 : rat) == 2^-1) = false by reflexivity.
  have Heq : (1 : rat) = 2^-1.
  { exact Hlaw. }
  have Htrue : (1 : rat) == 2^-1 by apply/eqP.
  by move: Htrue; rewrite Hbad.
Qed.

(** Correct marginal uniformity is not enough without conditional freshness:
    the second draw repeats the first ticket. *)
Definition correlated_source (h : list nat) d : list (rat * nat) :=
  match h with [] => uniform_indices d | i :: _ => [(1,i)] end.
Example correlated_history_rejected : ~ uniform_entropy correlated_source.
Proof.
  intro H. have Hlaw := proj2 (H [0%nat] 2%nat (Logic.eq_refl true)) (fun i => if i == 0%nat then 1 else 0).
  have Hbad : ((1 : rat) == 2^-1) = false by reflexivity.
  have Heq : (1 : rat) = 2^-1.
  { exact Hlaw. }
  have Htrue : (1 : rat) == 2^-1 by apply/eqP.
  by move: Htrue; rewrite Hbad.
Qed.

Section LargeCarrier.
Universe u.
Example higher_universe_execution (t : ptree void1 SubEnumQ Type@{u}) n
    (f : outcome Type@{u} -> rat) :
  replay_expectation (fun _ d => uniform_indices d) n t [] f =
  outcome_expectation n t f.
Proof. apply finite_runner_distribution. exact fresh_uniform_entropy. Qed.
End LargeCarrier.

From PTree.Execution.Validation Require Import SubEnumQ.
From PTree.Prob.Domain Require Import Expectation.
From PTree.Eq.Backend Require Import StableHittingDomainSubEnumQ.

Example arbitrary_fuel_hitting (R : realType) n :
  ratr (replay_expectation (fun _ d => uniform_indices d) n retry [] (returned_test (fun _ => 1))) =
  oval_eval (ptree_domain_approx R n (observe retry)) (return_head_test R (fun _ => 1)).
Proof. apply replay_hitting. exact fresh_uniform_entropy. Qed.

Example unbounded_retry_limit (R : realType) :
  oval_eval (ptree_domain_hitting R (observe retry)) (return_head_test R (fun _ => 1)) =
  oval_sup (fun n => ratr (replay_expectation (fun _ d => uniform_indices d) n retry []
    (returned_test (fun _ => 1)))).
Proof. apply replay_hitting_limit. exact fresh_uniform_entropy. Qed.
