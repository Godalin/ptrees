(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From mathcomp Require Import reals.
Require Import PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.MathComp.Kernel.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.EnumQ.Measure PTree.Prob.Backend.SubEnumQ.Measure PTree.Prob.Backend.MathComp.Measure.
Require Import PTree.Prob.FreeOmega.NativeCoupling.
Require Import PTree.Prob.Backend.SubEnumQ.FreeOmega.NativeCoupling.
From PTree.Prob.Interface Require Import SemanticCoupling.
Require Import PTree.Prob.Backend.MathComp.Coupling.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ.

(** Native-backend independent probes. In particular [NO] supplies operations,
    not native omega completeness; neither native BindLaws nor OmegaLaws is
    assumed. These definitions test the existing completion, not new laws. *)
Section GenericCompletionProfile.
Context {MN : Type -> Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI} `{NO : @SemanticOmega MN NI}.
Let MF := FreeOmega MN.
Let FI := FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO).
Let FO := FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO).
Definition generic_completion_core : @SemanticMeasureCoreLaws MF FI := _.
Definition generic_completion_order : @SemanticMeasureOrderLaws MF FI FO := _.
Definition generic_completion_omega : @SemanticOmegaLaws MF FI FO := _.
Definition generic_completion_total : @SemanticTotalProperLaws MF FI FO := _.
Definition generic_completion_cofinal : @SemanticOmegaCofinalityLaws MF FI FO := _.
Definition generic_completion_mixed_omega :
  @MixedMeasureOmegaLaws MN MF NI FI FreeOmegaMixedMeasure FO := _.
Section AELift.
Context `{NAL : @SemanticMeasureAELiftLaws MN NI}.
Definition generic_completion_bind : @SemanticMeasureBindLaws MF FI := _.
Definition generic_completion_mixed :
  @MixedMeasureLaws MN MF NI FI FreeOmegaMixedMeasure := _.
End AELift.
Section Unit.
Context `{ND : @SemanticMeasureDiracAELaws MN NI}.
Definition generic_completion_unit :
  @MixedMeasureUnitLaws MN MF NI FI FreeOmegaMixedMeasure := _.
End Unit.
Section Flatten.
Context `{NB : @SemanticMeasureBindAEExactLaws MN NI}.
Definition generic_completion_flatten :
  @MixedMeasureNodeBindLaws MN MF NI FI FreeOmegaMixedMeasure := _.
End Flatten.
Section Fubini.
Context `{NCA : @SemanticMeasureCouplingAELaws MN NI}.
Definition generic_completion_fubini : @SemanticOmegaFubiniLaws MF FI FO := _.
Section Countable.
Context `{NAC : @SemanticMeasureCountableAELaws MN NI}.
Definition generic_completion_diagonal : @SemanticMeasureDiagonalLaws MF FI FO := _.
Definition generic_completion_omega_ae : @SemanticOmegaAELaws MF FI FO := _.
Definition generic_completion_coupling_ae : @SemanticMeasureCouplingAELaws MF FI := _.
End Countable.
End Fubini.
End GenericCompletionProfile.

(** Compile-time audit of the maintained two-level backend profiles.

    Structure and elementary AE facts belong to the node measure [MN].
    Order, omega continuity, diagonal continuity, and Fubini belong to the
    completed behavior measure [MF = FreeOmega MN].  Commutativity remains
    optional and is deliberately absent from this required profile. *)

Section EnumQNodeProfile.

Definition enumQ_profile_subprobability_predicate :
    @SemanticSubprobability EnumQ EnumQ_SemanticMeasure := _.
Definition enumQ_profile_subprobability_closure :
    @SemanticSubprobabilityLaws EnumQ EnumQ_SemanticMeasure
      EnumQ_SemanticSubprobability := _.
(** Intentionally no [SemanticSubprobabilityCarrierLaws EnumQ]: raw EnumQ
    contains arbitrary finite weights. *)
Definition enumQ_profile_core :
    @SemanticMeasureCoreLaws EnumQ EnumQ_SemanticMeasure := _.
Definition enumQ_profile_ae_lift :
    @SemanticMeasureAELiftLaws EnumQ EnumQ_SemanticMeasure := _.
Definition enumQ_profile_ae_kleisli :
    @SemanticMeasureAEKleisliLaws EnumQ EnumQ_SemanticMeasure := _.
Definition enumQ_profile_dirac_ae :
    @SemanticMeasureDiracAELaws EnumQ EnumQ_SemanticMeasure := _.
Definition enumQ_profile_countable_ae :
    @SemanticMeasureCountableAELaws EnumQ EnumQ_SemanticMeasure := _.
Definition enumQ_profile_coupling_ae :
    @SemanticMeasureCouplingAELaws EnumQ EnumQ_SemanticMeasure := _.
Definition enumQ_profile_bind :
    @SemanticMeasureBindLaws EnumQ EnumQ_SemanticMeasure := _.
Definition enumQ_profile_bind_ae_exact :
    @SemanticMeasureBindAEExactLaws EnumQ EnumQ_SemanticMeasure := _.

End EnumQNodeProfile.

Section EnumQFreeOmegaProfile.

Let NI := EnumQ_SemanticMeasure.
Let NO := EnumQ_SemanticOmega.
Let MF := FreeOmega EnumQ.
Let FI := FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO).
Let FO := FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO).

Definition enumQ_profile_behavior_core :
    @SemanticMeasureCoreLaws MF FI := _.
Definition enumQ_profile_behavior_bind :
    @SemanticMeasureBindLaws MF FI := _.
Definition enumQ_profile_behavior_ae_kleisli :
    @SemanticMeasureAEKleisliLaws MF FI := _.
Definition enumQ_profile_behavior_countable_ae :
    @SemanticMeasureCountableAELaws MF FI := _.
Definition enumQ_profile_behavior_coupling_ae :
    @SemanticMeasureCouplingAELaws MF FI := _.
Definition enumQ_profile_behavior_omega :
    @SemanticOmega MF FI := FO.
Definition enumQ_profile_behavior_order :
    @SemanticMeasureOrderLaws MF FI FO := _.
Definition enumQ_profile_behavior_omega_laws :
    @SemanticOmegaLaws MF FI FO := _.
Definition enumQ_profile_behavior_total_proper :
    @SemanticTotalProperLaws MF FI FO := _.
Definition enumQ_profile_behavior_cofinality :
    @SemanticOmegaCofinalityLaws MF FI FO := _.
Definition enumQ_profile_behavior_omega_ae :
    @SemanticOmegaAELaws MF FI FO := _.
Definition enumQ_profile_behavior_diagonal :
    @SemanticMeasureDiagonalLaws MF FI FO := _.
Definition enumQ_profile_behavior_fubini :
    @SemanticOmegaFubiniLaws MF FI FO := _.
Definition enumQ_profile_mixed : @MixedMeasure EnumQ MF := _.
Definition enumQ_profile_mixed_laws :
    @MixedMeasureLaws EnumQ MF NI FI FreeOmegaMixedMeasure := _.
Definition enumQ_profile_mixed_unit :
    @MixedMeasureUnitLaws EnumQ MF NI FI FreeOmegaMixedMeasure := _.
Definition enumQ_profile_mixed_node_bind :
    @MixedMeasureNodeBindLaws EnumQ MF NI FI FreeOmegaMixedMeasure := _.
Definition enumQ_profile_mixed_omega :
    @MixedMeasureOmegaLaws EnumQ MF NI FI FreeOmegaMixedMeasure FO := _.

End EnumQFreeOmegaProfile.

(** The canonical finite probability backend.  Unlike raw [EnumQ], every
    inhabitant of [SubEnumQ] carries a proof that its total weight is at most
    one.  The FreeOmega behavior profile is otherwise the same. *)
Section SubEnumQNodeProfile.

Definition subenumQ_profile_measure : SemanticMeasure SubEnumQ := _.
Definition subenumQ_profile_subprobability :
    @SemanticSubprobability SubEnumQ SubEnumQ_SemanticMeasure := _.
Definition subenumQ_profile_subprobability_closure :
    @SemanticSubprobabilityLaws SubEnumQ SubEnumQ_SemanticMeasure
      SubEnumQ_SemanticSubprobability := _.
Definition subenumQ_profile_intrinsically_bounded :
    @SemanticSubprobabilityCarrierLaws SubEnumQ SubEnumQ_SemanticMeasure
      SubEnumQ_SemanticSubprobability := _.
Definition subenumQ_profile_core :
    @SemanticMeasureCoreLaws SubEnumQ SubEnumQ_SemanticMeasure := _.
Definition subenumQ_profile_ae_lift :
    @SemanticMeasureAELiftLaws SubEnumQ SubEnumQ_SemanticMeasure := _.
Definition subenumQ_profile_ae_kleisli :
    @SemanticMeasureAEKleisliLaws SubEnumQ SubEnumQ_SemanticMeasure := _.
Definition subenumQ_profile_dirac_ae :
    @SemanticMeasureDiracAELaws SubEnumQ SubEnumQ_SemanticMeasure := _.
Definition subenumQ_profile_countable_ae :
    @SemanticMeasureCountableAELaws SubEnumQ SubEnumQ_SemanticMeasure := _.
Definition subenumQ_profile_coupling_ae :
    @SemanticMeasureCouplingAELaws SubEnumQ SubEnumQ_SemanticMeasure := _.
Definition subenumQ_profile_bind :
    @SemanticMeasureBindLaws SubEnumQ SubEnumQ_SemanticMeasure := _.
Definition subenumQ_profile_bind_ae_exact :
    @SemanticMeasureBindAEExactLaws SubEnumQ SubEnumQ_SemanticMeasure := _.

End SubEnumQNodeProfile.

Section SubEnumQFreeOmegaProfile.

Let NI := SubEnumQ_SemanticMeasure.
Let NO := SubEnumQ_SemanticOmega.
Let MF := FreeOmega SubEnumQ.
Let FI := FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO).
Let FO := FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO).

Definition subenumQ_profile_behavior_core :
    @SemanticMeasureCoreLaws MF FI := _.
Definition subenumQ_profile_behavior_bind :
    @SemanticMeasureBindLaws MF FI := _.
Definition subenumQ_profile_behavior_ae_kleisli :
    @SemanticMeasureAEKleisliLaws MF FI := _.
Definition subenumQ_profile_behavior_countable_ae :
    @SemanticMeasureCountableAELaws MF FI := _.
Definition subenumQ_profile_behavior_coupling_ae :
    @SemanticMeasureCouplingAELaws MF FI := _.
Definition subenumQ_profile_behavior_omega : @SemanticOmega MF FI := FO.
Definition subenumQ_profile_behavior_order :
    @SemanticMeasureOrderLaws MF FI FO := _.
Definition subenumQ_profile_behavior_omega_laws :
    @SemanticOmegaLaws MF FI FO := _.
Definition subenumQ_profile_behavior_total_proper :
    @SemanticTotalProperLaws MF FI FO := _.
Definition subenumQ_profile_behavior_cofinality :
    @SemanticOmegaCofinalityLaws MF FI FO := _.
Definition subenumQ_profile_behavior_omega_ae :
    @SemanticOmegaAELaws MF FI FO := _.
Definition subenumQ_profile_behavior_diagonal :
    @SemanticMeasureDiagonalLaws MF FI FO := _.
Definition subenumQ_profile_behavior_fubini :
    @SemanticOmegaFubiniLaws MF FI FO := _.
Definition subenumQ_profile_mixed : @MixedMeasure SubEnumQ MF := _.
Definition subenumQ_profile_mixed_laws :
    @MixedMeasureLaws SubEnumQ MF NI FI FreeOmegaMixedMeasure := _.
Definition subenumQ_profile_mixed_unit :
    @MixedMeasureUnitLaws SubEnumQ MF NI FI FreeOmegaMixedMeasure := _.
Definition subenumQ_profile_mixed_node_bind :
    @MixedMeasureNodeBindLaws SubEnumQ MF NI FI FreeOmegaMixedMeasure := _.
Definition subenumQ_profile_mixed_omega :
    @MixedMeasureOmegaLaws SubEnumQ MF NI FI FreeOmegaMixedMeasure FO := _.

End SubEnumQFreeOmegaProfile.

(** Optional proof-relation capability.  Unlike the shared behavioral
    profile, native quotient-joint realization is currently established
    for SubEnumQ only; no EnumQ/MathComp instance is asserted here. *)
Definition subenumQ_profile_native_quotient_coupling :
  @FreeOmegaNativeCouplingLaws SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega := _.

Section MathCompFoundationalProfile.
Context (R : realType).

Definition mathcomp_profile_measure :
    SemanticMeasure (MathCompKernelMeasure R) :=
  MathCompNodeSemanticMeasure R.
Definition mathcomp_profile_subprobability :
    @SemanticSubprobability (MathCompKernelMeasure R)
      (MathCompNodeSemanticMeasure R) := _.
Definition mathcomp_profile_subprobability_closure :
    @SemanticSubprobabilityLaws (MathCompKernelMeasure R)
      (MathCompNodeSemanticMeasure R)
      (MathCompNodeSemanticSubprobability R) := _.
Definition mathcomp_profile_intrinsically_bounded :
    @SemanticSubprobabilityCarrierLaws (MathCompKernelMeasure R)
      (MathCompNodeSemanticMeasure R)
      (MathCompNodeSemanticSubprobability R) := _.
Definition mathcomp_profile_ae_lift :
    @SemanticMeasureAELiftLaws (MathCompKernelMeasure R)
      (MathCompNodeSemanticMeasure R) := _.
Definition mathcomp_profile_ae_kleisli :
    @SemanticMeasureAEKleisliLaws (MathCompKernelMeasure R)
      (MathCompNodeSemanticMeasure R) := _.
Definition mathcomp_profile_dirac_ae :
    @SemanticMeasureDiracAELaws (MathCompKernelMeasure R)
      (MathCompNodeSemanticMeasure R) := _.
Definition mathcomp_profile_countable_ae :
    @SemanticMeasureCountableAELaws (MathCompKernelMeasure R)
      (MathCompNodeSemanticMeasure R) := _.
Definition mathcomp_profile_coupling_ae :
    @SemanticMeasureCouplingAELaws (MathCompKernelMeasure R)
      (MathCompNodeSemanticMeasure R) := _.
Definition mathcomp_profile_bind_ae_exact :
    @SemanticMeasureBindAEExactLaws (MathCompKernelMeasure R)
      (MathCompNodeSemanticMeasure R) := _.

(** Native witness recovery needs no gluing. MathComp is a native analytic
    model, not a maintained formal-completion behavioral backend. *)
Definition mathcomp_profile_native_coupling {A B} (rel : A -> B -> Prop)
    (mu : MathCompKernelMeasure R A) (nu : MathCompKernelMeasure R B) :
  @sem_lift (MathCompKernelMeasure R) (MathCompNodeSemanticMeasure R)
    A B rel mu nu ->
  exists joint, @semantic_coupling (MathCompKernelMeasure R)
    (MathCompNodeSemanticMeasure R) A B rel mu nu joint :=
  @mathcomp_coupling_realization R A B rel mu nu.

(** No default value or nonempty return-carrier premise was introduced
    while repacking the backend's bookkeeping bottom points. *)
Example mathcomp_profile_empty_carrier_joint
    (mu : MathCompKernelMeasure R Empty_set) :
  exists joint, @semantic_coupling (MathCompKernelMeasure R)
    (MathCompNodeSemanticMeasure R) Empty_set Empty_set eq mu mu joint.
Proof.
  apply mathcomp_coupling_realization.
  apply mathcomp_kernel_lift_refl. intros x. reflexivity.
Qed.

End MathCompFoundationalProfile.

(** Coupling support transport above only uses the given coupling witness.
    Composition of two witnesses is the sole foundational capability in this
    audit that needs the explicit measurable gluing assumption. *)
Section MathCompRelationalCoreProfile.
Context (R : realType).
Context `{MathCompCouplingGluing R}.

Definition mathcomp_profile_core :
    @SemanticMeasureCoreLaws (MathCompKernelMeasure R)
      (MathCompNodeSemanticMeasure R) := _.

End MathCompRelationalCoreProfile.
