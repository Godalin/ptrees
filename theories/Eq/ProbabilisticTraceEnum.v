Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From mathcomp Require Import ssralg rat.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import DiscreteMC FrontierLiftEnum MeasureIterationEnum
  TwoLevelMeasure TwoLevelMeasureEnum FreeOmegaMeasure.
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
    particular representative selected by [finite_trace_sem]. *)
Definition enum_bool_indicator (b : bool) : rat :=
  if b then (1 : rat) else (0 : rat).

Definition enum_finite_trace_probability {E : Type -> Type} {R}
    (tr : @finite_event_trace E) (t : ptree E Enum R) (p : rat) : Prop :=
  exists (query representative : FreeOmega Enum bool) (out : Enum bool),
    @finite_trace_query E Enum (FreeOmega Enum)
      FreeOmegaObservableSemanticMeasure
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega R tr t query /\
    @sem_lift (FreeOmega Enum)
      FreeOmegaObservableSemanticMeasure bool bool eq
      representative query /\
    @free_omega_denotes Enum Enum_SemanticMeasure
      Enum_SemanticOmega bool bool id representative out /\
    enum_expect enum_bool_indicator out = p.

(** Canonical public name.  The argument is a dependent interaction pattern:
    selectors may recognize more than one event, so it need not denote a
    single concrete trace.  [enum_finite_trace_probability] is retained as a
    compatibility name. *)
Definition enum_finite_interaction_probability {E : Type -> Type} {R}
    (pattern : @finite_interaction_pattern E)
    (t : ptree E Enum R) (p : rat) : Prop :=
  enum_finite_trace_probability pattern t p.

Notation "'Prₜ[' t '|' pattern ']' '=' p" :=
  (enum_finite_interaction_probability pattern t p)
  (at level 70, t at next level, pattern at next level,
   p at next level, no associativity) : type_scope.

Lemma enum_finite_trace_probability_intro {E : Type -> Type} {R}
    (tr : @finite_event_trace E) (t : ptree E Enum R) p
    query representative out :
  @finite_trace_query E Enum (FreeOmega Enum)
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

Lemma enum_finite_interaction_probability_intro {E : Type -> Type} {R}
    (pattern : @finite_interaction_pattern E) (t : ptree E Enum R) p
    query representative out :
  @finite_interaction_query E Enum (FreeOmega Enum)
    FreeOmegaObservableSemanticMeasure
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R pattern t query ->
  @sem_lift (FreeOmega Enum)
    FreeOmegaObservableSemanticMeasure bool bool eq
    representative query ->
  @free_omega_denotes Enum Enum_SemanticMeasure
    Enum_SemanticOmega bool bool id representative out ->
  enum_expect enum_bool_indicator out = p ->
  Prₜ[ t | pattern ] = p.
Proof.
  apply enum_finite_trace_probability_intro.
Qed.
