(** Role: Default behavioral interpretation for weighted rational native
    sampling. This does not assert a subprobability bound on programs. *)
From PTree.Prob.Backend.EnumQ Require Import Measure.
Require Export PTree.Prob.Backend.EnumQ.Representation.
From PTree.Eq Require Import Canonical.
From PTree.Eq.FreeOmega Require Import Canonical.

Export EnumQ.
#[global] Polymorphic Instance EnumQ_CanonicalBehavior : CanonicalBehavior EnumQ :=
  @observable_free_omega_behavior EnumQ
    EnumQ_SemanticMeasure EnumQ_SemanticOmega.
