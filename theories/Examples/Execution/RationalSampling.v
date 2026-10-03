(** Role: concrete execution and resource-outcome example. *)
(** Exact rational interval and ticket replay: endpoint ownership,
    duplicates, zero weights, missing mass, signed tests and exhausted entropy. *)
From Coq Require Import Utf8.

Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Execution.Backend Require Import SubEnumQ RationalTickets.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Eq.PEutt.peutt.

From Coq Require List.
From mathcomp Require ssreflect ssrbool ssralg ssrnum order rat.
Require ITree.Indexed.Sum.
Require PTree.Core.PTreeDefinition.
Require PTree.Prob.Backend.Common.FiniteEnum.
Require PTree.Prob.Backend.SubEnumQ.Representation.
Require PTree.Execution.Runner.
Require PTree.Execution.Backend.SubEnumQ.
Module RationalReplay.
(** Boundary tests for exact rational interval selection. No hypothesis
    about a random oracle is used or claimed by these replay tests. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Import List.
Import ssreflect ssrbool ssralg ssrnum order rat.
Import ITree.Indexed.Sum.
Import PTree.Core.PTreeDefinition.
Import PTree.Prob.Backend.Common.FiniteEnum.
Import PTree.Prob.Backend.SubEnumQ.Representation.
Import PTree.Execution.Runner.
Import PTree.Execution.Backend.SubEnumQ.
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
Lemma half_bounded : finite_expect (λ _, 1) half_entries <= 1.
Proof. native_compute. reflexivity. Qed.
Definition half : SubEnumQ unit := subenumQ_of_list half_nonnegative half_bounded.
Definition high : quantile.
Proof. refine (@Build_quantile (3 * 4^-1) _ _); native_compute; reflexivity. Defined.
Definition closed_half : ptree void1 SubEnumQ unit := Prob half (λ x, Ret x).

Example half_mass_execution_is_lost :
  run (@replay_sample) 10 closed_half
    [high;high] = (Lost, [high]).
Proof. native_compute. reflexivity. Qed.
Example empty_replay_not_lost : replay_sample half [] = (NoEntropy, []).
Proof. reflexivity. Qed.


End RationalReplay.

From Coq Require List.
From mathcomp Require ssreflect ssrbool ssralg ssrnum order rat.
Require PTree.Prob.Backend.Common.FiniteEnum.
Require PTree.Prob.Backend.EnumQ.Representation.
Require PTree.Prob.Backend.SubEnumQ.Representation.
Require PTree.Execution.Runner.
Require PTree.Execution.Backend.RationalTickets.
Require PTree.Examples.RationalState.
Module RationalTickets.
(** Uniform finite ticket correctness, signed tests, zero/duplicate entries,
    partial mass, empty carriers, and executable entropy boundaries. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Import List.
Import ssreflect ssrbool ssralg ssrnum order rat.
Import PTree.Prob.Backend.Common.FiniteEnum.
Import PTree.Prob.Backend.EnumQ.Representation.
Import PTree.Prob.Backend.SubEnumQ.Representation.
Import PTree.Execution.Runner.
Import PTree.Execution.Backend.RationalTickets.
Import PTree.Examples.RationalState.
Import EnumQ GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.

Example nonfair_success_mass :
  ticket_expectation attempt_coin (λ o, match o with Some true => 1 | _ => 0 end) = 3^-1.
Proof. native_compute. reflexivity. Qed.

Example nonfair_retry_mass :
  ticket_expectation attempt_coin (λ o, match o with Some false => 1 | _ => 0 end) = 2^-1.
Proof. native_compute. reflexivity. Qed.

Example partial_loss_is_exact :
  ticket_expectation attempt_coin (λ o, match o with None => 1 | _ => 0 end) = 6^-1.
Proof. native_compute. reflexivity. Qed.

Example arbitrary_signed_observable (f : option bool → rat) :
  ticket_expectation attempt_coin f =
    finite_expect (λ b, f (Some b)) attempt_entries +
    (1 - enumQ_mass (subenumQ_raw attempt_coin)) * f None.
Proof. apply uniform_ticket_expectation. Qed.

Definition noisy_entries : list (rat * nat) :=
  [(0,99%nat); (4^-1,7%nat); (4^-1,7%nat); (0,88%nat)].
Lemma noisy_nonnegative : finite_nonnegative noisy_entries.
Proof.
  intros p x [H|[H|[H|[H|[]]]]]; inversion H; subst; native_compute; reflexivity.
Qed.
Lemma noisy_bounded : finite_expect (λ _, 1) noisy_entries <= 1.
Proof. native_compute. reflexivity. Qed.
Definition noisy_coin := subenumQ_of_list noisy_nonnegative noisy_bounded.

Example zero_duplicates_keep_mass :
  ticket_count noisy_coin = 16%nat ∧
  ticket_outcomes noisy_coin = List.repeat (Some 7%nat) 8 ++ List.repeat None 8.
Proof. split; native_compute; reflexivity. Qed.

Example zero_mass_has_one_missing_ticket :
  ticket_count (@subenumQ_zero Empty_set) = 1%nat ∧
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

End RationalTickets.
