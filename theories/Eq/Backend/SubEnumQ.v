(** Role: Default behavioral interpretation for rational subdistributions.
    Native mathematics lives in Prob; interpreter facts remain in Interp. *)
From PTree.Prob.Backend.SubEnumQ Require Import Measure.
From PTree.Prob.Backend.SubEnumQ Require Export Representation.
From PTree.Eq Require Import Canonical.
From PTree.Eq.FreeOmega Require Import Canonical.

#[global] Polymorphic Instance SubEnumQ_CanonicalBehavior : CanonicalBehavior SubEnumQ :=
  @observable_free_omega_behavior SubEnumQ
    SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega.
