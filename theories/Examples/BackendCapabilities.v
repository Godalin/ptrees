Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From mathcomp Require Import reals.
From PTree.Prob Require Import DiscreteMC MathCompMeasure TwoLevelMeasure
  FreeOmegaMeasure TwoLevelMeasureEnum TwoLevelMeasureMathComp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.

(** Compile-time audit of the two maintained two-level backend profiles.

    Structure and elementary AE facts belong to the node measure [MN].
    Order, omega continuity, diagonal continuity, and Fubini belong to the
    completed behavior measure [MF = FreeOmega MN].  Commutativity remains
    optional and is deliberately absent from this required profile. *)

Section EnumNodeProfile.

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

Section MathCompFoundationalProfile.
Context (R : realType).

Definition mathcomp_profile_measure :
    SemanticMeasure (MathCompKernelMeasure R) :=
  MathCompNodeSemanticMeasure R.
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
