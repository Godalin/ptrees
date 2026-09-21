(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From mathcomp Require Import reals.
Require Import PTree.Prob.Backend.Enum.Representation PTree.Prob.Backend.MathComp.Kernel.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.Enum.Measure PTree.Prob.Backend.SubEnum.Measure PTree.Prob.Backend.MathComp.Measure.
Require Import PTree.Prob.FreeOmega.NativeCoupling.
Require Import PTree.Prob.Backend.SubEnum.FreeOmega.NativeCoupling.
From PTree.Prob.Interface Require Import SemanticCoupling.
Require Import PTree.Prob.Backend.MathComp.Coupling.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.

(** Compile-time audit of the maintained two-level backend profiles.

    Structure and elementary AE facts belong to the node measure [MN].
    Order, omega continuity, diagonal continuity, and Fubini belong to the
    completed behavior measure [MF = FreeOmega MN].  Commutativity remains
    optional and is deliberately absent from this required profile. *)

Section EnumNodeProfile.

Definition enum_profile_subprobability_predicate :
    @SemanticSubprobability Enum Enum_SemanticMeasure := _.
Definition enum_profile_subprobability_closure :
    @SemanticSubprobabilityLaws Enum Enum_SemanticMeasure
      Enum_SemanticSubprobability := _.
(** Intentionally no [SemanticSubprobabilityCarrierLaws Enum]: raw Enum
    contains arbitrary finite weights. *)
Definition enum_profile_core :
    @SemanticMeasureCoreLaws Enum Enum_SemanticMeasure := _.
Definition enum_profile_ae_lift :
    @SemanticMeasureAELiftLaws Enum Enum_SemanticMeasure := _.
Definition enum_profile_ae_kleisli :
    @SemanticMeasureAEKleisliLaws Enum Enum_SemanticMeasure := _.
Definition enum_profile_dirac_ae :
    @SemanticMeasureDiracAELaws Enum Enum_SemanticMeasure := _.
Definition enum_profile_countable_ae :
    @SemanticMeasureCountableAELaws Enum Enum_SemanticMeasure := _.
Definition enum_profile_coupling_ae :
    @SemanticMeasureCouplingAELaws Enum Enum_SemanticMeasure := _.
Definition enum_profile_bind :
    @SemanticMeasureBindLaws Enum Enum_SemanticMeasure := _.
Definition enum_profile_bind_ae_exact :
    @SemanticMeasureBindAEExactLaws Enum Enum_SemanticMeasure := _.

End EnumNodeProfile.

Section EnumFreeOmegaProfile.

Let NI := Enum_SemanticMeasure.
Let NO := Enum_SemanticOmega.
Let MF := FreeOmega Enum.
Let FI := FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO).
Let FO := FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO).

Definition enum_profile_behavior_core :
    @SemanticMeasureCoreLaws MF FI := _.
Definition enum_profile_behavior_bind :
    @SemanticMeasureBindLaws MF FI := _.
Definition enum_profile_behavior_ae_kleisli :
    @SemanticMeasureAEKleisliLaws MF FI := _.
Definition enum_profile_behavior_countable_ae :
    @SemanticMeasureCountableAELaws MF FI := _.
Definition enum_profile_behavior_coupling_ae :
    @SemanticMeasureCouplingAELaws MF FI := _.
Definition enum_profile_behavior_omega :
    @SemanticOmega MF FI := FO.
Definition enum_profile_behavior_order :
    @SemanticMeasureOrderLaws MF FI FO := _.
Definition enum_profile_behavior_omega_laws :
    @SemanticOmegaLaws MF FI FO := _.
Definition enum_profile_behavior_total_proper :
    @SemanticTotalProperLaws MF FI FO := _.
Definition enum_profile_behavior_cofinality :
    @SemanticOmegaCofinalityLaws MF FI FO := _.
Definition enum_profile_behavior_omega_ae :
    @SemanticOmegaAELaws MF FI FO := _.
Definition enum_profile_behavior_diagonal :
    @SemanticMeasureDiagonalLaws MF FI FO := _.
Definition enum_profile_behavior_fubini :
    @SemanticOmegaFubiniLaws MF FI FO := _.
Definition enum_profile_mixed : @MixedMeasure Enum MF := _.
Definition enum_profile_mixed_laws :
    @MixedMeasureLaws Enum MF NI FI FreeOmegaMixedMeasure := _.
Definition enum_profile_mixed_unit :
    @MixedMeasureUnitLaws Enum MF NI FI FreeOmegaMixedMeasure := _.
Definition enum_profile_mixed_node_bind :
    @MixedMeasureNodeBindLaws Enum MF NI FI FreeOmegaMixedMeasure := _.
Definition enum_profile_mixed_omega :
    @MixedMeasureOmegaLaws Enum MF NI FI FreeOmegaMixedMeasure FO := _.

End EnumFreeOmegaProfile.

(** The canonical finite probability backend.  Unlike raw [Enum], every
    inhabitant of [SubEnum] carries a proof that its total weight is at most
    one.  The FreeOmega behavior profile is otherwise the same. *)
Section SubEnumNodeProfile.

Definition subenum_profile_measure : SemanticMeasure SubEnum := _.
Definition subenum_profile_subprobability :
    @SemanticSubprobability SubEnum SubEnum_SemanticMeasure := _.
Definition subenum_profile_subprobability_closure :
    @SemanticSubprobabilityLaws SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticSubprobability := _.
Definition subenum_profile_intrinsically_bounded :
    @SemanticSubprobabilityCarrierLaws SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticSubprobability := _.
Definition subenum_profile_core :
    @SemanticMeasureCoreLaws SubEnum SubEnum_SemanticMeasure := _.
Definition subenum_profile_ae_lift :
    @SemanticMeasureAELiftLaws SubEnum SubEnum_SemanticMeasure := _.
Definition subenum_profile_ae_kleisli :
    @SemanticMeasureAEKleisliLaws SubEnum SubEnum_SemanticMeasure := _.
Definition subenum_profile_dirac_ae :
    @SemanticMeasureDiracAELaws SubEnum SubEnum_SemanticMeasure := _.
Definition subenum_profile_countable_ae :
    @SemanticMeasureCountableAELaws SubEnum SubEnum_SemanticMeasure := _.
Definition subenum_profile_coupling_ae :
    @SemanticMeasureCouplingAELaws SubEnum SubEnum_SemanticMeasure := _.
Definition subenum_profile_bind :
    @SemanticMeasureBindLaws SubEnum SubEnum_SemanticMeasure := _.
Definition subenum_profile_bind_ae_exact :
    @SemanticMeasureBindAEExactLaws SubEnum SubEnum_SemanticMeasure := _.

End SubEnumNodeProfile.

Section SubEnumFreeOmegaProfile.

Let NI := SubEnum_SemanticMeasure.
Let NO := SubEnum_SemanticOmega.
Let MF := FreeOmega SubEnum.
Let FI := FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO).
Let FO := FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO).

Definition subenum_profile_behavior_core :
    @SemanticMeasureCoreLaws MF FI := _.
Definition subenum_profile_behavior_bind :
    @SemanticMeasureBindLaws MF FI := _.
Definition subenum_profile_behavior_ae_kleisli :
    @SemanticMeasureAEKleisliLaws MF FI := _.
Definition subenum_profile_behavior_countable_ae :
    @SemanticMeasureCountableAELaws MF FI := _.
Definition subenum_profile_behavior_coupling_ae :
    @SemanticMeasureCouplingAELaws MF FI := _.
Definition subenum_profile_behavior_omega : @SemanticOmega MF FI := FO.
Definition subenum_profile_behavior_order :
    @SemanticMeasureOrderLaws MF FI FO := _.
Definition subenum_profile_behavior_omega_laws :
    @SemanticOmegaLaws MF FI FO := _.
Definition subenum_profile_behavior_total_proper :
    @SemanticTotalProperLaws MF FI FO := _.
Definition subenum_profile_behavior_cofinality :
    @SemanticOmegaCofinalityLaws MF FI FO := _.
Definition subenum_profile_behavior_omega_ae :
    @SemanticOmegaAELaws MF FI FO := _.
Definition subenum_profile_behavior_diagonal :
    @SemanticMeasureDiagonalLaws MF FI FO := _.
Definition subenum_profile_behavior_fubini :
    @SemanticOmegaFubiniLaws MF FI FO := _.
Definition subenum_profile_mixed : @MixedMeasure SubEnum MF := _.
Definition subenum_profile_mixed_laws :
    @MixedMeasureLaws SubEnum MF NI FI FreeOmegaMixedMeasure := _.
Definition subenum_profile_mixed_unit :
    @MixedMeasureUnitLaws SubEnum MF NI FI FreeOmegaMixedMeasure := _.
Definition subenum_profile_mixed_node_bind :
    @MixedMeasureNodeBindLaws SubEnum MF NI FI FreeOmegaMixedMeasure := _.
Definition subenum_profile_mixed_omega :
    @MixedMeasureOmegaLaws SubEnum MF NI FI FreeOmegaMixedMeasure FO := _.

End SubEnumFreeOmegaProfile.

(** Optional proof-relation capability.  Unlike the shared behavioral
    profile, native quotient-joint realization is currently established
    for SubEnum only; no Enum/MathComp instance is asserted here. *)
Definition subenum_profile_native_quotient_coupling :
  @FreeOmegaNativeCouplingLaws SubEnum SubEnum_SemanticMeasure SubEnum_SemanticOmega := _.

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

(** Native witness recovery needs no gluing.  Do not confuse this with
    reflection from [FreeOmega] quotient couplings, which remains open. *)
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

Section MathCompFreeOmegaProfile.
Context (R : realType).
Context `{MathCompCouplingGluing R}.

Let NI := MathCompNodeSemanticMeasure R.
Let NO := MathCompNodeSemanticOmega R.
Let MF := FreeOmega (MathCompKernelMeasure R).
Let FI := FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO).
Let FO := FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO).

Definition mathcomp_profile_behavior_core :
    @SemanticMeasureCoreLaws MF FI := _.
Definition mathcomp_profile_behavior_bind :
    @SemanticMeasureBindLaws MF FI := _.
Definition mathcomp_profile_behavior_ae_kleisli :
    @SemanticMeasureAEKleisliLaws MF FI := _.
Definition mathcomp_profile_behavior_countable_ae :
    @SemanticMeasureCountableAELaws MF FI := _.
Definition mathcomp_profile_behavior_coupling_ae :
    @SemanticMeasureCouplingAELaws MF FI := _.
Definition mathcomp_profile_behavior_omega :
    @SemanticOmega MF FI := FO.
Definition mathcomp_profile_behavior_order :
    @SemanticMeasureOrderLaws MF FI FO := _.
Definition mathcomp_profile_behavior_omega_laws :
    @SemanticOmegaLaws MF FI FO := _.
Definition mathcomp_profile_behavior_total_proper :
    @SemanticTotalProperLaws MF FI FO := _.
Definition mathcomp_profile_behavior_cofinality :
    @SemanticOmegaCofinalityLaws MF FI FO := _.
Definition mathcomp_profile_behavior_omega_ae :
    @SemanticOmegaAELaws MF FI FO := _.
Definition mathcomp_profile_behavior_diagonal :
    @SemanticMeasureDiagonalLaws MF FI FO := _.
Definition mathcomp_profile_behavior_fubini :
    @SemanticOmegaFubiniLaws MF FI FO := _.
Definition mathcomp_profile_mixed :
    @MixedMeasure (MathCompKernelMeasure R) MF := _.
Definition mathcomp_profile_mixed_laws :
    @MixedMeasureLaws (MathCompKernelMeasure R) MF NI FI
      FreeOmegaMixedMeasure := _.
Definition mathcomp_profile_mixed_unit :
    @MixedMeasureUnitLaws (MathCompKernelMeasure R) MF NI FI
      FreeOmegaMixedMeasure := _.
Definition mathcomp_profile_mixed_node_bind :
    @MixedMeasureNodeBindLaws (MathCompKernelMeasure R) MF NI FI
      FreeOmegaMixedMeasure := _.
Definition mathcomp_profile_mixed_omega :
    @MixedMeasureOmegaLaws (MathCompKernelMeasure R) MF NI FI
      FreeOmegaMixedMeasure FO := _.

End MathCompFreeOmegaProfile.
