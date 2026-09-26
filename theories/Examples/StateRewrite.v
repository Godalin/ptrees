(** Case role: paper case study.
    Reading entry: source_program_rewrite; rewrite_then_handle.
    Scope: SubEnumQ / observable FreeOmega; equal behavior is not equal fuel or trace.
    See docs/CASE_STUDY_STANDARD.md and docs/CASE_STUDY_REFACTOR.md. *)
(** Rewrite -> eliminate State -> extract. Two consecutive native draws are
    fused by the generic probability algebra, before interpreting State.
    The continuation is the genuinely unbounded rational State loop. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order rat.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree Require Import PTree PTreeFacts.
From PTree.Eq.Backend Require Import SubEnumQ.
From PTree.Interp Require Import State.
Require PTree.Interp.FreeOmega.State.
From PTree.Interp.FreeOmega Require Import Rewriting.
Import FreeOmegaRewriting.
From PTree.Examples Require Import StateCounter RationalState.
From PTree.Execution Require Import Runner.
From PTree.Execution.Backend Require Import RationalTickets.
Import ListNotations.

Definition preparation_coin (b : bool) : SubEnumQ bool :=
  if b then attempt_coin else subenumQ_ret false.
Definition fused_preparation : SubEnumQ bool := subenumQ_bind coin preparation_coin.

Definition after_preparation (s : nat) (b : bool) :
    ptree (stateE nat +' void1) SubEnumQ unit :=
  Vis (inl1 (Put nat (if b then (s + 10)%nat else s)))
    (fun _ => rational_attempts).

Definition original_state_program : ptree (stateE nat +' void1) SubEnumQ unit :=
  Vis (inl1 (Get nat)) (fun s =>
    Prob coin (fun b => Prob (preparation_coin b) (after_preparation s))).

Definition rewritten_state_program : ptree (stateE nat +' void1) SubEnumQ unit :=
  Vis (inl1 (Get nat)) (fun s => Prob fused_preparation (after_preparation s)).

Theorem preparation_sampling_fusion s :
  Prob coin (fun b => Prob (preparation_coin b) (after_preparation s))
    ≈ₚ Prob fused_preparation (after_preparation s).
Proof.
  apply (peutt_prob_flatten (NI := PTree.Prob.Backend.SubEnumQ.Measure.SubEnumQ_SemanticMeasure)).
Qed.

Theorem source_program_rewrite : original_state_program ≈ₚ rewritten_state_program.
Proof.
  unfold original_state_program, rewritten_state_program.
  setoid_rewrite preparation_sampling_fusion. reflexivity.
Qed.

Theorem rewrite_then_handle s :
  run_state original_state_program s ≈ₚ run_state rewritten_state_program s.
Proof.
  setoid_rewrite source_program_rewrite. reflexivity.
Qed.

Definition execute_state_program {Seed}
    (program : ptree (stateE nat +' void1) SubEnumQ unit)
    (next : nat -> Seed -> option nat * Seed) fuel initial seed : outcome nat * Seed :=
  let '(result, rest) := run (fun A => @ticket_sample Seed A next) fuel
    (run_state program initial) seed in
  (match result with
   | Returned sa => Returned (fst sa)
   | Lost => Lost | Timeout => Timeout | EntropyExhausted => EntropyExhausted
   end, rest).

Definition original_counter {Seed} := @execute_state_program Seed original_state_program.
Definition rewritten_counter {Seed} := @execute_state_program Seed rewritten_state_program.

(** Equal probability behavior does not give same-fuel or same-trace equality:
    the rewrite removes one draw. These two corresponding traces differ. *)
Example original_preparation_trace :
  original_counter ticket_replay_source 7 0 [2%nat;0%nat;0%nat] = (Returned 11%nat, []).
Proof. native_compute. reflexivity. Qed.

Example rewritten_preparation_trace :
  rewritten_counter ticket_replay_source 6 0 [24%nat;0%nat] = (Returned 11%nat, []).
Proof. native_compute. reflexivity. Qed.

Theorem rewritten_trace_has_operational_path :
  executes (fun A => @ticket_sample (list nat) A ticket_replay_source)
    (run_state rewritten_state_program 0%nat) [24%nat;0%nat]
    (Returned (11%nat,tt)) [].
Proof.
  eapply run_sound with (fuel := 6%nat).
  - native_compute. reflexivity.
  - exact I.
Qed.

Example original_needs_an_extra_transition :
  original_counter ticket_replay_source 6 0 [2%nat;0%nat;0%nat] = (Timeout, [0%nat]).
Proof. native_compute. reflexivity. Qed.

Example fused_missing_mass_is_not_normalized :
  rewritten_counter ticket_replay_source 100 0 [47%nat;0%nat] = (Lost, [0%nat]).
Proof. native_compute. reflexivity. Qed.

Local Open Scope ring_scope.
Example preparation_success_probability :
  ticket_expectation fused_preparation
    (fun o => match o with Some true => 1 | _ => 0 end) = 6^-1.
Proof. native_compute. reflexivity. Qed.
Example preparation_other_probability :
  ticket_expectation fused_preparation
    (fun o => match o with Some false => 1 | _ => 0 end) = 3 * 4^-1.
Proof. native_compute. reflexivity. Qed.
Example preparation_lost_probability :
  ticket_expectation fused_preparation
    (fun o => match o with None => 1 | _ => 0 end) = 12^-1.
Proof. native_compute. reflexivity. Qed.
