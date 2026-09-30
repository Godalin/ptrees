(** Importing structural mathematics does not export its typeclass hints.
    Concrete native laws are available, so failure is NOT caused by absent
    backend capabilities. Explicit structural constants remain usable. *)
Set Universe Polymorphism.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega Mixed.
Require Import PTree.Prob.FreeOmega.Definition.
Require Import PTree.Prob.FreeOmega.StructuralMeasure.
From PTree.Prob.Backend.SubEnumQ Require Import Measure.

Local Notation MN := SubEnumQ.
Local Notation MF := (FreeOmega MN).
Local Notation NI := SubEnumQ_SemanticMeasure.
Local Notation FI := (@FreeOmegaSemanticMeasure MN NI).
Local Notation FO := (@FreeOmegaSemanticOmega MN NI SubEnumQ_SemanticOmega).
Local Notation MX := (@FreeOmegaMixedMeasure MN).

Fail Definition structural_measure : SemanticMeasure MF := _.
Fail Definition structural_core : @SemanticMeasureCoreLaws MF FI := _.
Fail Definition structural_bind : @SemanticMeasureBindLaws MF FI := _.
Fail Definition structural_kleisli : @SemanticMeasureAEKleisliLaws MF FI := _.
Fail Definition structural_countable : @SemanticMeasureCountableAELaws MF FI := _.
Fail Definition structural_coupling : @SemanticMeasureCouplingAELaws MF FI := _.
Fail Definition structural_mixed : @MixedMeasureLaws MN MF NI FI MX := _.
Fail Definition structural_omega : @SemanticOmega MF FI := _.
Fail Definition structural_omega_laws : @SemanticOmegaLaws MF FI FO := _.
Fail Definition structural_order : @SemanticMeasureOrderLaws MF FI FO := _.

Example shared_mixed_still_global : MixedMeasure MN MF.
Proof. typeclasses eauto. Qed.

Section ExplicitInternalUse.
#[local] Existing Instance FreeOmegaSemanticMeasureCoreLaws.
#[local] Existing Instance FreeOmegaSemanticOmegaLaws.
Example internal_core_available : @SemanticMeasureCoreLaws MF FI.
Proof. typeclasses eauto. Qed.
Example internal_omega_available : @SemanticOmegaLaws MF FI FO.
Proof. typeclasses eauto. Qed.
End ExplicitInternalUse.

Fail Definition structural_core_not_leaked : @SemanticMeasureCoreLaws MF FI := _.
