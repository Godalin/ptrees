(** Canonical completion client of the generic state-indexed proof. *)
Set Universe Polymorphism.
From ITree.Events Require Import State.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure.
From PTree.Prob.FreeOmega Require Import StructuralMeasure BindOrder RelationalLimit.
From PTree.Eq Require Import PEutt.
From PTree.Interp Require Import State.
Require PTree.Interp.StatePreservation.
Set Implicit Arguments.
Unset Strict Implicit.

Section Completion.
Context {S : Type} {E MN : Type -> Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation FC := (FreeOmegaObservableSemanticMeasureCoreLaws (NI := NI) (NO := NO)).
Local Notation FO := (FreeOmegaObservableSemanticOmega (NI := NI) (NO := NO)).

Theorem run_state_peutt {A B} (RR : A -> B -> Prop)
    (t : ptree (stateE S +' E) MN A) (u : ptree (stateE S +' E) MN B) s :
  @peutt (stateE S +' E) MN MF FI FC FreeOmegaMixedMeasure FO A B RR t u ->
  @peutt E MN MF FI FC FreeOmegaMixedMeasure FO (S*A) (S*B) (state_result_rel RR)
    (run_state t s) (run_state u s).
Proof.
  apply (StatePreservation.run_state_peutt free_omega_relational_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem run_state_peutt_eq {A} (t u : ptree (stateE S +' E) MN A) s :
  @peutt (stateE S +' E) MN MF FI FC FreeOmegaMixedMeasure FO A A eq t u ->
  @peutt E MN MF FI FC FreeOmegaMixedMeasure FO (S*A) (S*A) eq (run_state t s) (run_state u s).
Proof.
  apply (StatePreservation.run_state_peutt_eq free_omega_relational_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.
End Completion.
