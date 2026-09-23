(** The completion discharges probability-level limit obligations; the
    arbitrary-handler proof belongs entirely to the generic interpreter. *)
Set Universe Polymorphism.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure.
From PTree.Prob.FreeOmega Require Import StructuralMeasure BindOrder RelationalLimit.
From PTree.Eq Require Import PEutt.
Require PTree.Interp.Unrestricted.
Set Implicit Arguments.
Unset Strict Implicit.

Section Completion.
Context {E F MN : Type -> Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).

Theorem peutt_interp {A B} (RR : A -> B -> Prop)
    (handler : forall X, E X -> ptree F MN X)
    (t : ptree E MN A) (u : ptree E MN B) :
  @peutt E MN MF FI FC FreeOmegaMixedMeasure FO A B RR t u ->
  @peutt F MN MF FI FC FreeOmegaMixedMeasure FO A B RR
    (PTree.interp handler t) (PTree.interp handler u).
Proof.
  apply (PTree.Interp.Unrestricted.peutt_interp
    free_omega_relational_zero free_omega_relational_lub).
Qed.
End Completion.
