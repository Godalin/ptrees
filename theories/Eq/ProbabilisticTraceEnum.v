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

(** Concrete paper-facing projection of the generic finite-cylinder
    semantics.  A probability certificate contains a valid query together
    with an observationally representable FreeOmega measure coupled to that
    query.  This respects the semantic quotient: it does not inspect the
    particular representative selected by [finite_trace_sem]. *)
Definition enum_bool_indicator (b : bool) : rat :=
  if b then (1 : rat) else (0 : rat).

Definition enum_finite_trace_probability {E : Type -> Type} {R}
    (tr : @finite_event_trace E) (t : ptree E Enum R) (p : rat) : Prop :=
  exists (query representative : FreeOmega Enum bool) (out : Enum bool),
    @finite_trace_query E Enum (FreeOmega Enum)
      FreeOmegaObservableSemanticMeasureInterface
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface R tr t query /\
    @sem_lift (FreeOmega Enum)
      FreeOmegaObservableSemanticMeasureInterface bool bool eq
      representative query /\
    @free_omega_denotes Enum Enum_SemanticMeasureInterface
      Enum_SemanticOmegaInterface bool bool id representative out /\
    enum_expect enum_bool_indicator out = p.

Notation "'Prₜ[' t '|' tr ']' '=' p" :=
  (enum_finite_trace_probability tr t p)
  (at level 70, t at next level, tr at next level,
   p at next level, no associativity) : type_scope.

Lemma enum_finite_trace_probability_intro {E : Type -> Type} {R}
    (tr : @finite_event_trace E) (t : ptree E Enum R) p
    query representative out :
  @finite_trace_query E Enum (FreeOmega Enum)
    FreeOmegaObservableSemanticMeasureInterface
    FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface R tr t query ->
  @sem_lift (FreeOmega Enum)
    FreeOmegaObservableSemanticMeasureInterface bool bool eq
    representative query ->
  @free_omega_denotes Enum Enum_SemanticMeasureInterface
    Enum_SemanticOmegaInterface bool bool id representative out ->
  enum_expect enum_bool_indicator out = p ->
  Prₜ[ t | tr ] = p.
Proof.
  intros Hquery Hlift Hdenotes Hprobability.
  exists query, representative, out. repeat split; assumption.
Qed.
