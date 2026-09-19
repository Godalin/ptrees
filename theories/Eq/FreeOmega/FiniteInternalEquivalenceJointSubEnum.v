Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Classes.RelationClasses.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import TwoLevelMeasure TwoLevelMeasureSubEnum SemanticCouplingEnum
  FreeOmegaMeasure FreeOmegaNative FreeOmegaEquivalenceJointSubEnum.
From PTree.Eq Require Import PFiniteResidual FiniteInternalPlan.
From PTree.Eq.FreeOmega Require Import FiniteInternalNative FiniteInternalRoundCoupling
  FiniteInternalNativeJoint.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** In the finite backend, an EQUIVALENCE continuation candidate suffices
    to extract an actual round from the residual generator.  This theorem
    takes no joint/realization certificate from the caller.  Equivalence
    is an explicit mathematical premise; it is NOT asserted for the raw
    residual GFP or for an arbitrary heterogeneous candidate. *)
Section EquivalenceRounds.
Context {E : Type -> Type} {A : Type}.
Variable sim : ptree E SubEnum A -> ptree E SubEnum A -> Prop.
Hypothesis sim_equivalence : Equivalence sim.
Local Notation MF := (FreeOmega SubEnum).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnum_SemanticMeasure) (NO := SubEnum_SemanticOmega)).

Theorem pfinite_subenum_equivalence_joint_round t u :
  @pfinite_residualF E SubEnum MF SubEnum_SemanticMeasure FI
    FreeOmegaMixedMeasure A A eq sim t u ->
  exists (p : @finite_internal_plan E SubEnum A t)
         (q : @finite_internal_plan E SubEnum A u)
         (W : Type) (round : SubEnum W)
         (left : W -> native_sample_type (internal_plan_round_native p))
         (right : W -> native_sample_type (internal_plan_round_native q)),
    free_omega_qlift (fun w x => left w = x)
      (FOSample round (fun w => FORet w) : FreeOmegaAt SubEnum (ptree E SubEnum A) W)
      (FOSample (native_sample_measure (internal_plan_round_native p)) (fun x => FORet x)) /\
    free_omega_qlift (fun w y => right w = y)
      (FOSample round (fun w => FORet w) : FreeOmegaAt SubEnum (ptree E SubEnum A) W)
      (FOSample (native_sample_measure (internal_plan_round_native q)) (fun y => FORet y)) /\
    sem_ae round (fun w => internal_round_path_rel eq sim p q (left w) (right w)).
Proof.
  intro Hstep. apply pfinite_residual_native_characterization in Hstep.
  destruct Hstep as [p [q Hdecoded]].
  destruct (subenum_equivalence_quotient_joint
    (pfinite_guard_equivalence sim_equivalence) Hdecoded)
    as [Z [joint [left [right [Hl [Hr Hguard]]]]]].
  exists p, q.
  exact (finite_internal_native_joint_round (@subenum_coupling_realization) Hl Hr Hguard).
Qed.
End EquivalenceRounds.
