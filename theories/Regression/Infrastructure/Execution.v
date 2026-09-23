(** Operational contracts only: this small deterministic sampler is NOT a
    model of uniform sampling and is never registered as a probability API. *)
Set Universe Polymorphism.
From Coq Require Import List.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition Fold.
From PTree.Execution Require Import Runner.

Fail Check PTree.Prob.Interface.Measure.SemanticMeasure.
Fail Check PTree.Prob.FreeOmega.Definition.FreeOmega.
Fail Check PTree.Eq.PEutt.peutt.

From PTree.Interp Require Import State StateFacts StateFold.
From PTree.Eq Require Import PStruct.
Import ListNotations.

Definition replay_one X (mu : option X) (entropy : list unit) :
    draw_result X * list unit :=
  match entropy with
  | [] => (NoEntropy, [])
  | _ :: rest => (match mu with Some x => Drawn x | None => Missing end, rest)
  end.

Definition test_run := @run option (list unit) replay_one.
Arguments test_run {A} _ _ _.
Definition closed_choice : ptree void1 option bool := Prob (Some true) (fun b => Ret b).
Definition partial_choice : ptree void1 option bool := Prob None (fun b => Ret b).
CoFixpoint internal_loop : ptree void1 option bool := Tau internal_loop.

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
  1 <= fuel -> test_run fuel closed_choice [tt;tt] = (Returned true, [tt]).
Proof. intro H. eapply run_finished_more_fuel with (n := 1); eauto; reflexivity. Qed.
Example timeout_is_not_a_terminal_path :
  ~ executes replay_one closed_choice [tt] Timeout [tt].
Proof. intro H. exact (executes_finished H). Qed.

Definition state_program : ptree (stateE nat +' void1) option nat :=
  Vis (inl1 (Get nat)) (fun s =>
    Prob (Some true) (fun b : bool =>
      Vis (inl1 (Put nat (if b then S s else s))) (fun _ =>
        Vis (inl1 (Get nat)) (fun result => Ret result)))).

Example execute_state_with_sampling :
  test_run 4 (run_state state_program 9) [tt;tt] = (Returned (10,10), [tt]).
Proof. reflexivity. Qed.
Example state_elimination_costs_fuel_not_entropy :
  test_run 1 (run_state state_program 9) [tt] = (Timeout, [tt]).
Proof. reflexivity. Qed.

Example state_bind_uses_updated_state {A B}
    (t : ptree (stateE nat +' void1) option A)
    (k : A -> ptree (stateE nat +' void1) option B) s :
  pstruct eq (run_state (PTree.bind t k) s)
    (PTree.bind (run_state t s) (fun sa => run_state (k (snd sa)) (fst sa))).
Proof. apply run_state_bind. Qed.

Example standard_subevent_get :
  @get nat (stateE nat +' void1) option _ =
    Vis (inl1 (Get nat)) (fun s => Ret s).
Proof. reflexivity. Qed.
Example standard_subevent_put s :
  @put nat (stateE nat +' void1) option _ s =
    Vis (inl1 (Put nat s)) (fun x => Ret x).
Proof. reflexivity. Qed.

Section Forwarding.
Context {E : Type -> Type} {X : Type} (e : E X).
Example state_forwards_unhandled_event (k : X -> ptree (stateE nat +' E) option bool) s :
  pstruct eq (run_state (Vis (inr1 e) k) s)
    (Vis e (fun x => run_state (k x) s)).
Proof. apply run_state_forward. Qed.
End Forwarding.
