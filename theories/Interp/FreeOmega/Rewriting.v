(** Opt-in rewriting support for the observable FreeOmega interpretation.
    These are registrations of generic congruence proofs, not new proofs or
    native-backend copies. Import [FreeOmegaRewriting] to enable them.
    Merely loading this file does not register the instances globally. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Morphisms.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure.
From PTree.Prob.FreeOmega Require Import StructuralMeasure BindOrder RelationalLimit.
From PTree.Eq Require Import PEutt Algebra.
From PTree.Interp Require Import State StatePreservation Exception ExceptionFacts
  Unrestricted IterationUniform.
Set Implicit Arguments.
Unset Strict Implicit.

Module FreeOmegaRewriting.
Section Completion.
Context {MN : Type -> Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).
Local Notation W := (peutt (FI := FI) (MX := FreeOmegaMixedMeasure)
  (FO := FreeOmegaObservableSemanticOmega)).

(** Fix the frontier before resolving laws. Generic bind rewriting otherwise
    may search for laws of an unconstrained frontier during morphism inference. *)
#[export] Instance free_omega_bind_Proper {E A B} :
  Proper (W eq ==> pointwise_relation A (W eq) ==> W eq)
    (@PTree.bind E MN A B) | 1 :=
  peutt_bind_Proper (FI := FI) (MX := FreeOmegaMixedMeasure)
    (FO := FreeOmegaObservableSemanticOmega).

#[export] Instance free_omega_state_Proper {S E A} :
  Proper (W eq ==> eq ==> W eq) (@run_state S E MN A) :=
  run_state_peutt_eq_Proper free_omega_relational_bind
    free_omega_relational_zero free_omega_relational_lub.

#[export] Instance free_omega_interp_Proper {E F A}
    (h : forall X, E X -> ptree F MN X) :
  Proper (W eq ==> W eq) (@PTree.interp E F MN h A) :=
  peutt_interp_Proper free_omega_relational_zero free_omega_relational_lub h.

#[export] Instance free_omega_exception_Proper {Err E A} :
  Proper (W eq ==> W eq) (@run_exception Err E MN A) :=
  run_exception_peutt_eq_Proper free_omega_relational_bind.

#[export] Instance free_omega_iter_Proper {E I A} :
  Proper (pointwise_relation I (W eq) ==> eq ==> W eq) (@PTree.iter E MN A I) :=
  peutt_iter_Proper free_omega_relational_zero free_omega_relational_lub.
End Completion.
End FreeOmegaRewriting.
