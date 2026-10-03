(** Role: concrete execution and resource-outcome example. *)
(** Executable runner behavior and semantic-result/resource-failure boundaries.
    These deterministic tests make no entropy-uniformity claim. *)
From Coq Require Import Utf8.

Set Universe Polymorphism.
(** [option] is template-polymorphic. Eta-expand the native functor instead
    of fixing its universe by passing the bare template as a higher-kinded
    argument. This also checks after loading the entire safe library. *)
Local Notation Replay := (fun X : Type => option X).
From PTree.Core Require Import PTreeDefinition Fold.
From PTree.Execution Require Import Runner.
Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Eq.PEutt.peutt.
Fail Check PTree.Execution.Validation.UniformReplay.uniform_entropy.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.

From Coq Require List.
Require ITree.Events.State.
Require ITree.Indexed.Sum.
Require PTree.Core.PTreeDefinition PTree.Core.Fold.
Require PTree.Execution.Runner.
Require PTree.Interp.State PTree.Interp.StateFacts PTree.Interp.StateFold.
Require PTree.Eq.PStruct.
Module Execution.
(** Operational contracts only: this small deterministic sampler is NOT a
    model of uniform sampling and is never registered as a probability API. *)
Set Universe Polymorphism.
Import List.
Import ITree.Events.State.
Import ITree.Indexed.Sum.
Import PTree.Core.PTreeDefinition PTree.Core.Fold.
Import PTree.Execution.Runner.


Import PTree.Interp.State PTree.Interp.StateFacts PTree.Interp.StateFold.
Import PTree.Eq.PStruct.
Import ListNotations.

Definition replay_one X (mu : Replay X) (entropy : list unit) :
    draw_result X * list unit :=
  match entropy with
  | [] => (NoEntropy, [])
  | _ :: rest => (match mu with Some x => Drawn x | None => Missing end, rest)
  end.

Definition test_run := @run Replay (list unit) replay_one.
Arguments test_run {A} _ _ _.
Definition closed_choice : ptree void1 Replay bool := Prob (Some true) (λ b, Ret b).
Definition partial_choice : ptree void1 Replay bool := Prob None (λ b, Ret b).
CoFixpoint internal_loop : ptree void1 Replay bool := Tau internal_loop.

Example returned_needs_no_fuel : test_run 0 (Ret true) [] = (Returned true, []).
Proof. reflexivity. Qed.
Example sampling_consumes_one_token :
  test_run 1 closed_choice [tt;tt] = (Returned true, [tt]).
Proof. reflexivity. Qed.
Example missing_mass_is_not_retry :
  test_run 20 partial_choice [tt;tt] = (Lost, [tt]).
Proof. reflexivity. Qed.
Example fuel_exhaustion_preserves_entropy :
  test_run 0 closed_choice [tt] = (Timeout, [tt]).
Proof. reflexivity. Qed.
Example replay_exhaustion_is_not_missing_mass :
  test_run 20 closed_choice [] = (EntropyExhausted, []).
Proof. reflexivity. Qed.
Example infinite_internal_computation fuel :
  test_run fuel internal_loop [tt] = (Timeout, [tt]).
Proof. induction fuel; simpl; auto. Qed.
Example successful_path_has_operational_evidence :
  executes replay_one closed_choice [tt;tt] (Returned true) [tt].
Proof. eapply run_sound with (fuel := 1); [reflexivity|exact I]. Qed.
Example successful_path_has_stable_replay fuel :
  1 <= fuel → test_run fuel closed_choice [tt;tt] = (Returned true, [tt]).
Proof. intro H. eapply run_finished_more_fuel with (n := 1); eauto; reflexivity. Qed.
Example timeout_is_not_a_terminal_path :
  ¬ executes replay_one closed_choice [tt] Timeout [tt].
Proof. intro H. exact (executes_finished H). Qed.

Definition state_program : ptree (stateE nat +' void1) Replay nat :=
  Vis (inl1 (Get nat)) (λ s,
    Prob (Some true) (λ b : bool,
      Vis (inl1 (Put nat (if b then S s else s))) (λ _,
        Vis (inl1 (Get nat)) (λ result, Ret result)))).

Example execute_state_with_sampling :
  test_run 4 (run_state state_program 9) [tt;tt] = (Returned (10,10), [tt]).
Proof. reflexivity. Qed.
Example state_elimination_costs_fuel_not_entropy :
  test_run 1 (run_state state_program 9) [tt] = (Timeout, [tt]).
Proof. reflexivity. Qed.

Example state_bind_uses_updated_state {A B}
    (t : ptree (stateE nat +' void1) Replay A)
    (k : A → ptree (stateE nat +' void1) Replay B) s :
  pstruct eq (run_state (PTree.bind t k) s)
    (PTree.bind (run_state t s) (λ sa, run_state (k (snd sa)) (fst sa))).
Proof. apply run_state_bind. Qed.

Example standard_subevent_get :
  @get nat (stateE nat +' void1) Replay _ =
    Vis (inl1 (Get nat)) (λ s, Ret s).
Proof. reflexivity. Qed.
Example standard_subevent_put s :
  @put nat (stateE nat +' void1) Replay _ s =
    Vis (inl1 (Put nat s)) (λ x, Ret x).
Proof. reflexivity. Qed.

Section Forwarding.
Context {E : Type → Type} {X : Type} (e : E X).
Example state_forwards_unhandled_event (k : X → ptree (stateE nat +' E) Replay bool) s :
  pstruct eq (run_state (Vis (inr1 e) k) s)
    (Vis e (λ x, run_state (k x) s)).
Proof. apply run_state_forward. Qed.
End Forwarding.

End Execution.

Require ITree.Indexed.Sum.
Require PTree.Core.PTreeDefinition.
Require PTree.Execution.Runner.
Module Outcome.
(** Program results and execution-resource failures are disjoint views of
    the unchanged runner outcome. No probability correctness is assumed. *)
Set Universe Polymorphism.
Import ITree.Indexed.Sum.
Import PTree.Core.PTreeDefinition.
Import PTree.Execution.Runner.


Definition empty_sampler {X} (_ : Replay X) (s : unit) : draw_result X * unit :=
  (NoEntropy, s).
Definition missing_sampler {X} (_ : Replay X) (s : unit) : draw_result X * unit :=
  (Missing, s).
Definition request : ptree void1 Replay bool := Prob (Some true) (λ b, Ret b).

Example returned_is_semantic : outcome_view (Returned true) = inl (ResultReturned true).
Proof. reflexivity. Qed.
Example loss_is_semantic : outcome_view (@Lost bool) = inl ResultLost.
Proof. reflexivity. Qed.
Example zero_fuel_is_resource_failure :
  outcome_view (fst (run (@missing_sampler) 0 request tt)) = inr FuelExhausted.
Proof. reflexivity. Qed.
Example no_entropy_is_resource_failure :
  outcome_view (fst (run (@empty_sampler) 1 request tt)) = inr EntropyUnavailable.
Proof. reflexivity. Qed.
Example native_missing_is_completed :
  outcome_view (fst (run (@missing_sampler) 1 request tt)) = inl ResultLost.
Proof. reflexivity. Qed.

Example typed_loss_path : executes_result (@missing_sampler) request tt ResultLost tt.
Proof. apply run_result_iff. exists 1. reflexivity. Qed.

Example entropy_failure_has_no_completed_path :
  ¬ executes (@empty_sampler) request tt EntropyExhausted tt.
Proof. intro H. pose proof (executes_finished H) as Hdone. exact Hdone. Qed.
Example timeout_has_no_completed_path :
  ¬ executes (@missing_sampler) request tt Timeout tt.
Proof. intro H. pose proof (executes_finished H) as Hdone. exact Hdone. Qed.

Example typed_result_agrees_with_existing_runner
    {MN : Type → Type} {Seed A : Type}
    (sample : ∀ X, MN X → Seed → draw_result X * Seed)
    (t : ptree void1 MN A) seed result seed' :
  executes_result sample t seed result seed' ↔
  ∃ n, run sample n t seed = (outcome_of_view (inl result), seed').
Proof. apply run_result_iff. Qed.

End Outcome.
