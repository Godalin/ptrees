(** Role: Internal execution/scheduling proof infrastructure. Supports hitting adequacy; not an additional behavioral equivalence. *)
Set Universe Polymorphism.
From Coq.Logic Require Import ClassicalChoice.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure SemanticCoupling.
From PTree.Eq.Internal Require Import FiniteInternal.
From PTree.Eq Require Import PStrong UnifiedFrontier PrimitiveStableHitting PTreeKernel.
From PTree.Eq.Internal Require Import FiniteInternalHitting.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section JointCompression.
Context {E MN MF : Type -> Type}
  `{NI : SemanticMeasure MN} `{NC : @SemanticMeasureCoreLaws MN NI}
  `{FI : SemanticMeasure MF} `{FC : @SemanticMeasureCoreLaws MF FI}
  `{FB : @SemanticMeasureBindLaws MF FI}
  `{FCAE : @SemanticMeasureCouplingAELaws MF FI}
  `{MX : MixedMeasure MN MF} `{ML : @MixedMeasureLaws MN MF NI FI MX}
  `{FO : @SemanticOmega MF FI}
  `{FOrd : @SemanticMeasureOrderLaws MF FI FO}
  `{FOL : @SemanticOmegaLaws MF FI FO}
  `{FCO : @SemanticOmegaCofinalityLaws MF FI FO}
  `{MOL : @MixedMeasureOmegaLaws MN MF NI FI MX FO}.
Context {A B : Type}.
Variable sim : ptree E MN A -> ptree E MN B -> Prop.
Variable mu : MF (ptree E MN A).
Variable nu : MF (ptree E MN B).
Variable joint : MF (ptree E MN A * ptree E MN B).
Hypothesis Hjoint : semantic_coupling sim mu nu joint.
Variable cut1 : ptree E MN A * ptree E MN B -> MF (ptree E MN A).
Variable cut2 : ptree E MN A * ptree E MN B -> MF (ptree E MN B).
Hypothesis Hcut1 : forall t u, sim t u -> finite_internal t (cut1 (t,u)).
Hypothesis Hcut2 : forall t u, sim t u -> finite_internal u (cut2 (t,u)).

Theorem finite_internal_joint_guarded (RR : A -> B -> Prop)
    (Hguard : forall t u, sim t u ->
      sem_lift (fun t u => pstrongF RR sim (observe t) (observe u)) (cut1 (t,u)) (cut2 (t,u))) :
  sem_lift (fun t u => pstrongF RR sim (observe t) (observe u))
    (sem_bind joint cut1) (sem_bind joint cut2).
Proof. eapply semantic_coupling_dependent_bind; eassumption. Qed.

(** After a correlated choice of finite cuts, the marginal residual
    distribution need not itself be one finite_internal derivation from a
    marginal tree.  Nevertheless, running its residuals to complete hitting
    preserves that marginal's behavior. *)
Theorem finite_internal_joint_hitting_left
    (front : ptree E MN A -> MF (stable_head E MN A))
    (Hfront : forall t, ptree_stable_hitting (observe t) (front t)) :
  sem_lift eq
    (sem_bind (sem_bind joint cut1) front) (sem_bind mu front).
Proof.
  eapply sem_lift_proper_l.
  - apply sem_eq_sym. apply sem_bind_assoc.
  - eapply semantic_coupling_dependent_bind_left; [exact Hjoint|].
    intros t u Hsim. eapply sem_lift_mono with (R := fun x y => y = x).
    + intros x y Hxy. symmetry. exact Hxy.
    + apply sem_lift_sym. eapply finite_internal_hitting_lift;
        [apply Hcut1; exact Hsim|exact Hfront|apply Hfront].
Qed.

Theorem finite_internal_joint_hitting_right
    (front : ptree E MN B -> MF (stable_head E MN B))
    (Hfront : forall u, ptree_stable_hitting (observe u) (front u)) :
  sem_lift eq
    (sem_bind (sem_bind joint cut2) front) (sem_bind nu front).
Proof.
  eapply sem_lift_proper_l.
  - apply sem_eq_sym. apply sem_bind_assoc.
  - eapply semantic_coupling_dependent_bind_right; [exact Hjoint|].
    intros t u Hsim. eapply sem_lift_mono with (R := fun x y => y = x).
    + intros x y Hxy. symmetry. exact Hxy.
    + apply sem_lift_sym. eapply finite_internal_hitting_lift;
        [apply Hcut2; exact Hsim|exact Hfront|apply Hfront].
Qed.

End JointCompression.
