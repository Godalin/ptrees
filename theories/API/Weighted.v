(** Role: User-facing assembly or tree/backend adapter. Imports lower layers explicitly; not new semantic theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
From ExtLib.Structures Require Import Monads.
From PTree.Prob.Legacy Require Import Monad.
From PTree.Core Require Import PTreeDefinition.
From ITree.Basics Require Import Basics.
Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.
Section stuck.
Context {E M : Type -> Type}.
Context `{Monad M}.
Context `{MonadMeasure M}.
(** Thus M is a valid Inference Representation *)

Definition stuckE (e : E void) : ptree E M void
  := PTree.trigger e.

Definition stuckM {R} (u : ptree E M R) : ptree E M R
  := Prob (score 0) (fun _ => u).

End stuck.
