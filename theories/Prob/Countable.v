Require Import Utf8.
Require Import Reals.

Set Primitive Projections.

Notation "ℝ₊" := R : type_scope.

CoInductive InfSupp A : Type :=
  { this : ℝ₊ * A
  ; those : InfSupp A
  }.

Check this.
Check those.
Check InfSupp.


