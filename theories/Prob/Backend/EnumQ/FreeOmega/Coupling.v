(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Universe Polymorphism.
Require Import PTree.Prob.Backend.EnumQ.Representation.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.EnumQ.Measure PTree.Prob.Backend.SubEnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Prob.Interface Require Import SemanticCoupling.
Require Import PTree.Prob.Backend.EnumQ.SemanticCoupling.
Require Import PTree.Prob.FreeOmega.Coupling.
Import EnumQ.

Set Implicit Arguments.

(** These are concrete theorems, not new backend assumptions.  Their
    structural-lifting premise is intentionally visible in the API. *)
Theorem free_enumQ_structural_coupling_realization {A B : Type}
    (R : A -> B -> Prop) (mu : FreeOmega EnumQ A) (nu : FreeOmega EnumQ B) :
  free_omega_lift R mu nu ->
  exists joint, @semantic_coupling (FreeOmega EnumQ)
    (FreeOmegaObservableSemanticMeasure
      (NI := EnumQ_SemanticMeasure) (NO := EnumQ_SemanticOmega)) A B R mu nu joint.
Proof.
  intro Hlift. eapply free_omega_lift_realization.
  - exact (@enumQ_coupling_realization).
  - exact Hlift.
Qed.

Theorem free_subenumQ_structural_coupling_realization {A B : Type}
    (R : A -> B -> Prop) (mu : FreeOmega SubEnumQ A) (nu : FreeOmega SubEnumQ B) :
  free_omega_lift R mu nu ->
  exists joint, @semantic_coupling (FreeOmega SubEnumQ)
    (FreeOmegaObservableSemanticMeasure
      (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)) A B R mu nu joint.
Proof.
  intro Hlift. eapply free_omega_lift_realization.
  - exact (@subenumQ_coupling_realization).
  - exact Hlift.
Qed.
