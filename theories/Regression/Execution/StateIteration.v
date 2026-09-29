(** State/iter preserves the updated state across retry boundaries. *)
Set Universe Polymorphism.
From Coq Require Import List.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import PStruct.
From PTree.Interp Require Import State StateIter.
From PTree.Execution Require Import Runner.
From PTree.Execution.Backend Require Import SubEnumQ.
From PTree.Prob.Backend.SubEnumQ Require Import Representation.
From PTree.Examples Require Import StateCounter.
Import ListNotations.

Definition retry_step (_ : unit) : ptree (stateE nat +' void1) SubEnumQ (unit + unit) :=
  Vis (inl1 (Get nat)) (fun s =>
    Vis (inl1 (Put nat (S s))) (fun _ =>
      Prob coin (fun b : bool => Ret (if b then inr tt else inl tt)))).

Example eliminate_state_before_or_after_iter :
  pstruct eq (run_state (PTree.iter retry_step tt) 0)
    (PTree.iter (state_iter_step retry_step) (0,tt)).
Proof. apply run_state_iter. Qed.

Example iter_replay_threads_updated_state :
  run (@replay_sample) 7 (run_state (PTree.iter retry_step tt) 0)
    [low_quantile;high_quantile] = (Returned (2,tt), []).
Proof. native_compute. reflexivity. Qed.

Example transformed_iter_has_same_replay :
  run (@replay_sample) 7 (PTree.iter (state_iter_step retry_step) (0,tt))
    [low_quantile;high_quantile] = (Returned (2,tt), []).
Proof. native_compute. reflexivity. Qed.

Section Eventful.
Context {E MN : Type -> Type} (e : E unit) (mu : MN bool).
Definition eventful_step (_ : unit) : ptree (stateE nat +' E) MN (unit + nat) :=
  Vis (inl1 (Get nat)) (fun s =>
    Vis (inl1 (Put nat (S s))) (fun _ =>
      Vis (inr1 e) (fun _ =>
        Prob mu (fun b : bool => Ret (if b then inr s else inl tt))))).

Example eventful_probabilistic_iter_commutes s :
  pstruct eq (run_state (PTree.iter eventful_step tt) s)
    (PTree.iter (state_iter_step eventful_step) (s,tt)).
Proof. apply run_state_iter. Qed.
End Eventful.
