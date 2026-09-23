(** Role: Canonical observable FreeOmega profile for finite real sampling. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import reals.
From PTree.Prob.Backend.SubEnumR Require Export Representation.
From PTree.Prob.Backend.SubEnumR Require Import Measure Coupling Omega.
From PTree.Eq Require Import Canonical.
From PTree.Eq.FreeOmega Require Import Canonical.

#[global] Instance SubEnumR_CanonicalBehavior (R : realType) :
    CanonicalBehavior (SubEnumR R) :=
  @observable_free_omega_behavior (SubEnumR R)
    (SubEnumR_SemanticMeasure R) (SubEnumR_SemanticOmega R).
