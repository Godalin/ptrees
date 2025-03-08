(** This file defines the monadic interfaces of
    the Bayes-Inference problem. *)

Require Import Utf8.
Require Export Rbase.
From ExtLib.Structures Require Import Monads.

Set Implicit Arguments.
Set Contextual Implicit.

Notation 𝕀 := R.

Class MonadDistribution (m : Type → Type) `{Monad m} : Type :=
  random : m 𝕀.
Arguments MonadDistribution m {_}.
Check MonadDistribution.



Class MonadFactor (m : Type → Type) `{Monad m} : Type :=
  score : R → m unit.
Arguments MonadFactor m {_}.
Check MonadFactor.

Class MonadMeasure (m : Type → Type) `{Monad m} :=
  { MeasureDistribution :: MonadDistribution m;
    MeasureFactor :: MonadFactor m;
  }.



Section test.
Context {m : Type → Type}.
Context `{Monad m} `{MonadMeasure m}.

Check ret (m := m).
Check bind (m := m).
Check random (m := m).
Check score (m := m).
End test.
