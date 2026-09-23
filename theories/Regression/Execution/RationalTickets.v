(** Uniform finite ticket correctness, signed tests, zero/duplicate entries,
    partial mass, empty carriers, and executable entropy boundaries. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order rat.
From PTree.Prob.Backend.Common Require Import FiniteEnum.
From PTree.Prob.Backend.EnumQ Require Import Representation.
From PTree.Prob.Backend.SubEnumQ Require Import Representation.
From PTree.Execution Require Import Runner.
From PTree.Execution.Backend Require Import RationalTickets.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Eq.PEutt.peutt.
From PTree.Examples Require Import RationalState.
Import EnumQ GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.

Example nonfair_success_mass :
  ticket_expectation attempt_coin (fun o => match o with Some true => 1 | _ => 0 end) = 3^-1.
Proof. native_compute. reflexivity. Qed.

Example nonfair_retry_mass :
  ticket_expectation attempt_coin (fun o => match o with Some false => 1 | _ => 0 end) = 2^-1.
Proof. native_compute. reflexivity. Qed.

Example partial_loss_is_exact :
  ticket_expectation attempt_coin (fun o => match o with None => 1 | _ => 0 end) = 6^-1.
Proof. native_compute. reflexivity. Qed.

Example arbitrary_signed_observable (f : option bool -> rat) :
  ticket_expectation attempt_coin f =
    finite_expect (fun b => f (Some b)) attempt_entries +
    (1 - enumQ_mass (subenumQ_raw attempt_coin)) * f None.
Proof. apply uniform_ticket_expectation. Qed.

Definition noisy_entries : list (rat * nat) :=
  [(0,99%nat); (4^-1,7%nat); (4^-1,7%nat); (0,88%nat)].
Lemma noisy_nonnegative : finite_nonnegative noisy_entries.
Proof.
  intros p x [H|[H|[H|[H|[]]]]]; inversion H; subst; native_compute; reflexivity.
Qed.
Lemma noisy_bounded : finite_expect (fun _ => 1) noisy_entries <= 1.
Proof. native_compute. reflexivity. Qed.
Definition noisy_coin := subenumQ_of_list noisy_nonnegative noisy_bounded.

Example zero_duplicates_keep_mass :
  ticket_count noisy_coin = 16%nat /\
  ticket_outcomes noisy_coin = List.repeat (Some 7%nat) 8 ++ List.repeat None 8.
Proof. split; native_compute; reflexivity. Qed.

Example zero_mass_has_one_missing_ticket :
  ticket_count (@subenumQ_zero Empty_set) = 1%nat /\
  ticket_outcomes (@subenumQ_zero Empty_set) = [None].
Proof. split; native_compute; reflexivity. Qed.

Example no_entropy_is_not_loss :
  ticket_replay attempt_coin [] = (NoEntropy, []).
Proof. reflexivity. Qed.

Example last_valid_ticket_is_loss :
  ticket_replay attempt_coin [5%nat;0%nat] = (Missing, [0%nat]).
Proof. native_compute. reflexivity. Qed.

Example bound_is_checked :
  ticket_replay attempt_coin [6%nat;0%nat] = (NoEntropy, [0%nat]).
Proof. native_compute. reflexivity. Qed.
