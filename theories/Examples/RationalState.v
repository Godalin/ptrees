(** Case role: execution demo / shared supporting program.
    Proof mode: execution/validation.
    Reading entry: rational_counter; rational_missing_mass_stops.
    Scope: SubEnumQ; missing mass, fuel exhaustion and invalid entropy are distinct.
    See docs/CASE_STUDY_STANDARD.md and docs/CASE_STUDY_REFACTOR.md. *)
(** A genuinely non-fair, partial rational sampler inside an unbounded State
    loop. Each attempt succeeds with 1/3, retries with 1/2, or is lost with
    1/6. This example consumes the general verified uniform-ticket compiler. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order rat.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Backend.Common Require Import FiniteEnum.
From PTree.Prob.Backend.SubEnumQ Require Import Representation.
From PTree.Interp Require Import State.
From PTree.Execution Require Import Runner.
From PTree.Execution.Backend Require Import RationalTickets.
Import GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.

Definition attempt_entries : list (rat * bool) := [(3^-1,true); (2^-1,false)].
Lemma attempt_nonnegative : finite_nonnegative attempt_entries.
Proof. intros p b [H|[H|[]]]; inversion H; subst; native_compute; reflexivity. Qed.
Lemma attempt_bounded : finite_expect (fun _ => 1) attempt_entries <= 1.
Proof. native_compute. reflexivity. Qed.
Definition attempt_coin : SubEnumQ bool := subenumQ_of_list attempt_nonnegative attempt_bounded.

CoFixpoint rational_attempts : ptree (stateE nat +' void1) SubEnumQ unit :=
  Vis (inl1 (Get nat)) (fun s =>
    Vis (inl1 (Put nat (S s))) (fun _ =>
      Prob attempt_coin (fun b => if b then Ret tt else Tau rational_attempts))).

Definition rational_counter {Seed}
    (next : nat -> Seed -> option nat * Seed) fuel initial seed : outcome nat * Seed :=
  let '(result, rest) := run (fun A => @ticket_sample Seed A next) fuel
    (run_state rational_attempts initial) seed in
  (match result with
   | Returned sa => Returned (fst sa)
   | Lost => Lost | Timeout => Timeout | EntropyExhausted => EntropyExhausted
   end, rest).

Example rational_ticket_layout :
  ticket_count attempt_coin = 6%nat /\
  ticket_outcomes attempt_coin = [Some true;Some true;Some false;Some false;Some false;None].
Proof. split; native_compute; reflexivity. Qed.

Example rational_two_attempts :
  rational_counter ticket_replay_source 7 0 [2%nat;0%nat;5%nat] =
    (Returned 2%nat, [5%nat]).
Proof. native_compute. reflexivity. Qed.

Example rational_missing_mass_stops :
  rational_counter ticket_replay_source 100 0 [5%nat;0%nat] = (Lost, [0%nat]).
Proof. native_compute. reflexivity. Qed.

Example rational_timeout_no_redraw :
  rational_counter ticket_replay_source 4 0 [2%nat;0%nat] = (Timeout, [0%nat]).
Proof. native_compute. reflexivity. Qed.

Example rational_invalid_entropy_not_loss :
  rational_counter ticket_replay_source 3 0 [6%nat] = (EntropyExhausted, []).
Proof. native_compute. reflexivity. Qed.
