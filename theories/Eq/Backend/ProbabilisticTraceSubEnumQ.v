(** Role: Canonical equational/hitting theory. Depends on Core and Prob; does not provide comparison or interpreter semantics. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order rat.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Backend.EnumQ.Representation.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.EnumQ.Iteration.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure.
From PTree.Eq Require Import ProbabilisticTrace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ.
Import GRing.Theory Order.Theory.
Local Open Scope ring_scope.
Local Open Scope order_scope.

(** Paper-facing finite-cylinder probabilities for the bounded executable
    backend.  In contrast to the legacy raw-EnumQ projection, the denoted
    observable is a [SubEnumQ], so every result is provably in [[0,1]]. *)
Definition subenumQ_bool_indicator (b : bool) : rat :=
  if b then (1 : rat) else (0 : rat).

Definition subenumQ_finite_interaction_probability
    {E : Type -> Type} {R}
    (pattern : @finite_interaction_pattern E)
    (t : ptree E SubEnumQ R) (p : rat) : Prop :=
  exists (query representative : FreeOmega SubEnumQ bool)
      (out : SubEnumQ bool),
    @finite_interaction_query E SubEnumQ (FreeOmega SubEnumQ)
      FreeOmegaObservableSemanticMeasure
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega R pattern t query /\
    @sem_lift (FreeOmega SubEnumQ)
      FreeOmegaObservableSemanticMeasure bool bool eq
      representative query /\
    @free_omega_denotes SubEnumQ SubEnumQ_SemanticMeasure
      SubEnumQ_SemanticOmega bool bool id representative out /\
    enumQ_expect subenumQ_bool_indicator (subenumQ_raw out) = p.

Declare Scope subenumQ_probability_scope.
Delimit Scope subenumQ_probability_scope with subprob.

Notation "'Prₛ[' t '|' pattern ']' '=' p" :=
  (subenumQ_finite_interaction_probability pattern t p)
  (at level 70, t at next level, pattern at next level,
   p at next level, no associativity) : subenumQ_probability_scope.

Lemma subenumQ_finite_interaction_probability_intro
    {E : Type -> Type} {R}
    (pattern : @finite_interaction_pattern E)
    (t : ptree E SubEnumQ R) p query representative out :
  @finite_interaction_query E SubEnumQ (FreeOmega SubEnumQ)
    FreeOmegaObservableSemanticMeasure
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R pattern t query ->
  @sem_lift (FreeOmega SubEnumQ)
    FreeOmegaObservableSemanticMeasure bool bool eq
    representative query ->
  @free_omega_denotes SubEnumQ SubEnumQ_SemanticMeasure
    SubEnumQ_SemanticOmega bool bool id representative out ->
  enumQ_expect subenumQ_bool_indicator (subenumQ_raw out) = p ->
  (Prₛ[ t | pattern ] = p)%subprob.
Proof.
  intros Hquery Hlift Hdenotes Hprobability.
  exists query, representative, out. repeat split; assumption.
Qed.

Lemma subenumQ_bool_indicator_range b :
  is_true (0 <= subenumQ_bool_indicator b) /\
  is_true (subenumQ_bool_indicator b <= 1).
Proof. by case: b; split.
Qed.

Theorem subenumQ_finite_interaction_probability_range
    {E : Type -> Type} {R}
    (pattern : @finite_interaction_pattern E)
    (t : ptree E SubEnumQ R) p :
  (Prₛ[ t | pattern ] = p)%subprob ->
  is_true (0 <= p) /\ is_true (p <= 1).
Proof.
  intros [query [representative [out [_ [_ [_ Hprob]]]]]].
  have Hnonnegative :
      0 <= enumQ_expect subenumQ_bool_indicator (subenumQ_raw out).
  { apply: enumQ_expect_nonnegative=> q b Hin.
    exact (proj1 (subenumQ_bool_indicator_range b)). }
  have Hbelow_mass :
      enumQ_expect subenumQ_bool_indicator (subenumQ_raw out) <=
      enumQ_mass (subenumQ_raw out).
  { apply: enumQ_expect_le_mass=> q b Hin.
    exact (proj2 (subenumQ_bool_indicator_range b)). }
  rewrite Hprob in Hnonnegative Hbelow_mass.
  split; first exact Hnonnegative.
  exact (le_trans Hbelow_mass (subenumQ_bound out)).
Qed.
