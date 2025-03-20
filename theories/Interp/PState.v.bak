From Coq Require Import Reals.
From Coq Require Import List.
Import ListNotations.

Open Scope list_scope.
Open Scope R_scope.

From ExtLib Require Import Structures.Functor.
From ExtLib Require Import Structures.Monad.
From ExtLib Require Import Structures.MonadLaws.
From ExtLib Require Import Data.Monads.StateMonad.
Import MonadNotation.
Import MonadState.

Open Scope monad_scope.

From PTree.Prob Require Import FinSupp.



(*| a state monad suitable for imperative probabilistic programming |*)

Section PState.

Record pstate (Σ : Type) (A : Type) :=
  mkPState { runPState : Σ -> finSupp (A * Σ) }.

End PState.

Arguments mkPState {Σ A} _.
Arguments runPState {Σ A} _ _.



Section PStateMonad.

Definition pstate_fmap {Σ A B} : (A -> B) -> pstate Σ A -> pstate Σ B :=
  fun f u => mkPState (fun σ =>
    fmap (fun '(a, σ') => (f a, σ')) (runPState u σ)).

Definition pstate_ret {Σ A} : A -> pstate Σ A :=
  fun a => mkPState (fun σ => ret (a, σ)).

Definition pstate_bind {Σ A B} : pstate Σ A -> (A -> pstate Σ B) -> pstate Σ B :=
  fun u f => mkPState (fun σ =>
    bind (runPState u σ) (fun '(a, σ') => runPState (f a) σ')).

Global Instance PStateFunctor {Σ} : (Functor (pstate Σ)) := 
  { fmap := @pstate_fmap Σ
  }.

Global Instance PStateMonad {Σ} : (Monad (pstate Σ)) := 
  { ret := @pstate_ret Σ
  ; bind := @pstate_bind Σ
  }.

Definition get {Σ} : pstate Σ Σ :=
  mkPState (fun σ => ret (σ, σ)).

Definition put {Σ} (σ : Σ) : pstate Σ unit :=
  mkPState (fun _ => ret (tt, σ)).

Global Instance MonadState_pstate {Σ} : MonadState Σ (pstate Σ) :=
  { get := get
  ; put := put
  }.

End PStateMonad.



(*| embedding of state monad into pstate monad |*)

Definition embed {A Σ} (u : state Σ A) : pstate Σ A :=
  mkPState (fun σ =>
    let (a, σ') := runState u σ in
    mkFinSupp [(a, σ', 1)]).
