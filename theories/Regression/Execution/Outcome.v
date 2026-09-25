(** Program results and execution-resource failures are disjoint views of
    the unchanged runner outcome. No probability correctness is assumed. *)
Set Universe Polymorphism.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Execution Require Import Runner.

Fail Check PTree.Execution.Validation.UniformReplay.uniform_entropy.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.

Definition empty_sampler {X} (_ : option X) (s : unit) : draw_result X * unit :=
  (NoEntropy, s).
Definition missing_sampler {X} (_ : option X) (s : unit) : draw_result X * unit :=
  (Missing, s).
Definition request : ptree void1 option bool := Prob (Some true) (fun b => Ret b).

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
  ~ executes (@empty_sampler) request tt EntropyExhausted tt.
Proof. intro H. pose proof (executes_finished H) as Hdone. exact Hdone. Qed.
Example timeout_has_no_completed_path :
  ~ executes (@missing_sampler) request tt Timeout tt.
Proof. intro H. pose proof (executes_finished H) as Hdone. exact Hdone. Qed.

Example typed_result_agrees_with_existing_runner
    {MN : Type -> Type} {Seed A : Type}
    (sample : forall X, MN X -> Seed -> draw_result X * Seed)
    (t : ptree void1 MN A) seed result seed' :
  executes_result sample t seed result seed' <->
  exists n, run sample n t seed = (outcome_of_view (inl result), seed').
Proof. apply run_result_iff. Qed.
