(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Universe Polymorphism.
From mathcomp Require Import eqtype.
From PTree.Prob.Interface Require Import FrontierLift.
From PTree.Prob.Backend.EnumQ Require Import FrontierLift.
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

(** Optional native product exchange used by the completion bridge.
    This derives a concrete law; it adds no default commutativity requirement. *)
Lemma enumQ_semantic_product_swap {X Y : eqType}
    (mu : EnumQ X) (nu : EnumQ Y) :
  @sem_lift EnumQ EnumQ_SemanticMeasure _ _
    semantic_pair_swap_rel
    (semantic_product mu nu) (semantic_product nu mu).
Proof.
  change (@meas_lift EnumQ EnumQ_MeasureInterface _ _
    semantic_pair_swap_rel
    (bind_EnumQ mu (fun x => bind_EnumQ nu
      (fun y => ret_EnumQ (x, y))))
    (bind_EnumQ nu (fun y => bind_EnumQ mu
      (fun x => ret_EnumQ (y, x))))).
  refine (@meas_lift_bind_ret_exchange EnumQ EnumQ_MeasureInterface
    EnumQ_MeasureCommutativeLaws X Y (X * Y)%type (Y * X)%type
    (@semantic_pair_swap_rel X Y) mu nu
    (fun x y => (x, y)) (fun y x => (y, x)) _).
  intros x y. split; reflexivity.
Qed.
