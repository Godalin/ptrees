(** Role: Canonical equational/hitting theory. Depends on Core and Prob; does not provide comparison or interpreter semantics. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From mathcomp Require Import ssralg rat.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Backend.Enum.Representation PTree.Prob.Backend.Enum.FrontierLift PTree.Prob.Backend.Enum.Iteration.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.Enum.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import ProbabilisticTrace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Compatibility projection of the generic finite-cylinder semantics to
    raw finite weights.  Despite the historical [probability] identifier,
    the result is guaranteed to lie in [[0,1]] only when the input program's
    node measures satisfy [enum_subprob].  New probability-facing clients
    should use [ProbabilisticTraceSubEnum].  A certificate contains a query
    together
    with an observationally representable FreeOmega measure coupled to that
    query.  This respects the semantic quotient: it does not inspect the
    particular representative selected by [finite_interaction_sem]. *)
Definition enum_bool_indicator (b : bool) : rat :=
  if b then (1 : rat) else (0 : rat).

Definition enum_finite_interaction_probability {E : Type -> Type} {R}
    (tr : @finite_interaction_pattern E) (t : ptree E Enum R) (p : rat) : Prop :=
  exists (query representative : FreeOmega Enum bool) (out : Enum bool),
    @finite_interaction_query E Enum (FreeOmega Enum)
      FreeOmegaObservableSemanticMeasure
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega R tr t query /\
    @sem_lift (FreeOmega Enum)
      FreeOmegaObservableSemanticMeasure bool bool eq
      representative query /\
    @free_omega_denotes Enum Enum_SemanticMeasure
      Enum_SemanticOmega bool bool id representative out /\
    enum_expect enum_bool_indicator out = p.

Notation "'Prₜ[' t '|' pattern ']' '=' p" :=
  (enum_finite_interaction_probability pattern t p)
  (at level 70, t at next level, pattern at next level,
   p at next level, no associativity) : type_scope.

Lemma enum_finite_interaction_probability_intro {E : Type -> Type} {R}
    (tr : @finite_interaction_pattern E) (t : ptree E Enum R) p
    query representative out :
  @finite_interaction_query E Enum (FreeOmega Enum)
    FreeOmegaObservableSemanticMeasure
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R tr t query ->
  @sem_lift (FreeOmega Enum)
    FreeOmegaObservableSemanticMeasure bool bool eq
    representative query ->
  @free_omega_denotes Enum Enum_SemanticMeasure
    Enum_SemanticOmega bool bool id representative out ->
  enum_expect enum_bool_indicator out = p ->
  Prₜ[ t | tr ] = p.
Proof.
  intros Hquery Hlift Hdenotes Hprobability.
  exists query, representative, out. repeat split; assumption.
Qed.
