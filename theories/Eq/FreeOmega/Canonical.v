(** Role: Explicit builder for an observable FreeOmega operation profile.
    This is NOT a blanket CanonicalBehavior instance. Concrete Eq adapters
    decide which native backends use this profile. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Prob.Interface Require Import Measure Omega.
Require Import PTree.Prob.FreeOmega.Definition
  PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import Canonical.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition observable_free_omega_behavior {MN}
    (NI : SemanticMeasure MN) (NO : @SemanticOmega MN NI) :
    CanonicalBehavior MN := {|
  behavior_frontier := FreeOmega MN;
  behavior_measure := @FreeOmegaObservableSemanticMeasure MN NI NO;
  behavior_mixed := @FreeOmegaMixedMeasure MN;
  behavior_omega := @FreeOmegaObservableSemanticOmega MN NI NO
|}.
