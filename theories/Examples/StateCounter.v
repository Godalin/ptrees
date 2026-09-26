(** Case role: execution demo / shared supporting program.
    Proof mode: execution/validation.
    Reading entry: tick_state_equation; counter_replay_contract.
    Scope: SubEnumQ; exact replay is not a randomness theorem for the host source.
    See docs/CASE_STUDY_STANDARD.md and docs/CASE_STUDY_REFACTOR.md. *)
(** State + native probability, with exact rational replay. This example
    does not assert that an arbitrary supplied replay stream is random.
    Prob stays a native node throughout state elimination and execution. *)
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
From PTree.Interp Require Import State StateFacts.
From PTree.Eq Require Import PStruct.
From PTree.Execution Require Import Runner.
From PTree.Execution.Backend Require Import SubEnumQ.
Import GRing.Theory Num.Theory Order.Theory ListNotations.
Local Open Scope ring_scope.
Set Implicit Arguments.

Definition coin_entries : list (rat * bool) := [(2^-1,false);(2^-1,true)].
Lemma coin_nonnegative : finite_nonnegative coin_entries.
Proof.
  intros p b [H|[H|[]]]; inversion H; subst; native_compute; reflexivity.
Qed.
Lemma coin_bounded : finite_expect (fun _ => 1) coin_entries <= 1.
Proof. native_compute. reflexivity. Qed.
Definition coin : SubEnumQ bool := subenumQ_of_list coin_nonnegative coin_bounded.

Definition tick : ptree (stateE nat +' void1) SubEnumQ bool :=
  Vis (inl1 (Get nat)) (fun s =>
    Prob coin (fun b : bool =>
      Vis (inl1 (Put nat (if b then S s else s))) (fun _ => Ret b))).

Definition tick_normal s : ptree void1 SubEnumQ (nat * bool) :=
  Tau (Prob coin (fun b : bool => Tau (Ret ((if b then S s else s), b)))).

Theorem tick_state_equation s : pstruct eq (run_state tick s) (tick_normal s).
Proof.
  apply pstruct_fold. unfold pstruct_body. rewrite observe_run_state.
  cbn [tick tick_normal observe state_response]. constructor.
  apply pstruct_fold. unfold pstruct_body. rewrite observe_run_state.
  cbn [observe]. constructor. intro b.
  apply pstruct_fold. unfold pstruct_body. rewrite observe_run_state.
  cbn [observe state_response]. constructor.
  apply run_state_ret.
Qed.

Definition low_quantile : quantile.
Proof. refine (@Build_quantile (4^-1) _ _); native_compute; reflexivity. Defined.
Definition high_quantile : quantile.
Proof. refine (@Build_quantile (3 * 4^-1) _ _); native_compute; reflexivity. Defined.

Definition replay_tick fuel s entropy :=
  run (@replay_sample) fuel (run_state tick s) entropy.

Example replay_no_increment :
  replay_tick 3 9 [low_quantile] = (Returned (9%nat,false), []).
Proof. native_compute. reflexivity. Qed.
Example replay_increment :
  replay_tick 3 9 [high_quantile] = (Returned (10%nat,true), []).
Proof. native_compute. reflexivity. Qed.
Example replay_preserves_unused_entropy :
  replay_tick 3 9 [high_quantile;low_quantile] =
    (Returned (10%nat,true), [low_quantile]).
Proof. native_compute. reflexivity. Qed.

(** A recursively defined stateful service, not a finite syntax-only test. *)
CoFixpoint count_until_success : ptree (stateE nat +' void1) SubEnumQ unit :=
  Vis (inl1 (Get nat)) (fun s =>
    Vis (inl1 (Put nat (S s))) (fun _ =>
      Prob coin (fun b : bool => if b then Ret tt else Tau count_until_success))).

Example replay_two_attempts :
  run (@replay_sample) 7 (run_state count_until_success 0%nat)
    [low_quantile;high_quantile] = (Returned (2%nat,tt), []).
Proof. native_compute. reflexivity. Qed.
Example retry_timeout_is_not_loss :
  run (@replay_sample) 4 (run_state count_until_success 0%nat)
    [low_quantile;high_quantile] = (Timeout, [high_quantile]).
Proof. native_compute. reflexivity. Qed.
Example retry_entropy_exhaustion_is_not_loss :
  run (@replay_sample) 100 (run_state count_until_success 0%nat)
    [low_quantile] = (EntropyExhausted, []).
Proof. native_compute. reflexivity. Qed.

Theorem replay_two_attempts_path :
  executes (@replay_sample) (run_state count_until_success 0%nat)
    [low_quantile;high_quantile] (Returned (2%nat,tt)) [].
Proof. eapply run_sound with (fuel := 7); [exact replay_two_attempts|exact I]. Qed.

(** Only this fixed fair-coin program is exposed to the executable bit
    driver. Two quantiles are NOT a sampler for arbitrary SubEnumQ nodes. *)
Definition bit_quantile (b : bool) : quantile :=
  if b then high_quantile else low_quantile.

Lemma coin_selects_bit b :
  pick_interval (subenumQ_data coin) (quantile_value (bit_quantile b)) = Some b.
Proof. destruct b; native_compute; reflexivity. Qed.

Theorem coin_bit_expectation (f : bool -> rat) :
  finite_expect (fun b =>
    match pick_interval (subenumQ_data coin) (quantile_value (bit_quantile b)) with
    | Some x => f x | None => 0 end) coin_entries =
  finite_expect f (subenumQ_data coin).
Proof.
  transitivity (finite_expect f coin_entries).
  - apply finite_expect_ext. intro b. rewrite coin_selects_bit. reflexivity.
  - reflexivity.
Qed.

Definition counter_replay fuel initial (bits : list bool) : outcome nat * nat :=
  let '(result, rest) := run (@replay_sample) fuel
    (run_state count_until_success initial) (List.map bit_quantile bits) in
  (match result with
   | Returned sa => Returned (fst sa)
   | Lost => Lost
   | Timeout => Timeout
   | EntropyExhausted => EntropyExhausted
   end, List.length rest).

Example counter_replay_contract :
  counter_replay 7 0 [false;true;false] = (Returned 2%nat, 1%nat).
Proof. native_compute. reflexivity. Qed.
