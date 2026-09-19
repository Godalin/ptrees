Set Universe Polymorphism.
From PTree.Prob Require Import DiscreteMC TwoLevelMeasure TwoLevelMeasureEnum
  TwoLevelMeasureSubEnum FreeOmegaMeasure SemanticCoupling
  SemanticCouplingEnum FreeOmegaCoupling.
Import Enum.

Set Implicit Arguments.

(** These are concrete theorems, not new backend assumptions.  Their
    structural-lifting premise is intentionally visible in the API. *)
Theorem free_enum_structural_coupling_realization {A B : Type}
    (R : A -> B -> Prop) (mu : FreeOmega Enum A) (nu : FreeOmega Enum B) :
  free_omega_lift R mu nu ->
  exists joint, @semantic_coupling (FreeOmega Enum)
    (FreeOmegaObservableSemanticMeasure
      (NI := Enum_SemanticMeasure) (NO := Enum_SemanticOmega)) A B R mu nu joint.
Proof.
  intro Hlift. eapply free_omega_lift_realization.
  - exact (@enum_coupling_realization).
  - exact Hlift.
Qed.

Theorem free_subenum_structural_coupling_realization {A B : Type}
    (R : A -> B -> Prop) (mu : FreeOmega SubEnum A) (nu : FreeOmega SubEnum B) :
  free_omega_lift R mu nu ->
  exists joint, @semantic_coupling (FreeOmega SubEnum)
    (FreeOmegaObservableSemanticMeasure
      (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)) A B R mu nu joint.
Proof.
  intro Hlift. eapply free_omega_lift_realization.
  - exact (@subenum_coupling_realization).
  - exact Hlift.
Qed.
