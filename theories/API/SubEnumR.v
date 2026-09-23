(** Role: Canonical observable FreeOmega profile for finite real sampling. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import reals.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega.
From PTree.API Require Import Behavior BehaviorFreeOmega.

#[global] Instance SubEnumR_CanonicalBehavior (R : realType) :
    CanonicalBehavior (SubEnumR R) :=
  @observable_free_omega_behavior (SubEnumR R)
    (SubEnumR_SemanticMeasure R) (SubEnumR_SemanticOmega R).
