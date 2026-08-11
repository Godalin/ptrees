Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import boolp classical_sets functions cardinality reals.
From mathcomp.analysis Require Import measure probability kernel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A uniform discrete measurable carrier for an arbitrary Coq type.  The
    extra [MCBottom] point is needed because MathComp's [measurableType]
    hierarchy is pointed/choice-based, whereas [MeasureInterface] ranges over
    every [Type], including empty ones. *)
Variant mc_carrier (A : Type) : Type :=
  | MCBottom
  | MCValue (value : A).

Arguments MCBottom {A}.
Arguments MCValue {A} _.

HB.instance Definition _ A := gen_eqMixin (mc_carrier A).
HB.instance Definition _ A := gen_choiceMixin (mc_carrier A).
HB.instance Definition _ A := isPointed.Build (mc_carrier A) MCBottom.

HB.instance Definition _ A := @isMeasurable.Build default_measure_display
  (mc_carrier A) discrete_measurable discrete_measurable0
  discrete_measurableC discrete_measurableU.

Section BackendShape.
Context (R : realType).

(** Candidate carrier for the MathComp-Analysis backend.  Bind will be
    integration/composition of subprobability kernels; [MCBottom] represents
    no returned value and therefore accounts for lost mass. *)
Definition MathCompMeasure (A : Type) : Type :=
  subprobability (mc_carrier A) R.

Definition mathcomp_measure_set (A : Type) :=
  classical_sets.set (mc_carrier A).

Definition mathcomp_measure_ret {A} (x : A) :
    subprobability (mc_carrier A) R :=
  [the subprobability (mc_carrier A) R of dirac (MCValue x)].

End BackendShape.
