Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

From mathcomp Require Import ssreflect ssrbool ssralg ssrnum order rat.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob Require Import DiscreteMC FreeOmegaMeasure MeasureIterationEnum
  TwoLevelMeasure TwoLevelMeasureSubEnum.
From PTree.Eq Require Import ProbabilisticTrace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.
Import GRing.Theory Order.Theory.
Local Open Scope ring_scope.
Local Open Scope order_scope.

(** Paper-facing finite-cylinder probabilities for the bounded executable
    backend.  In contrast to the legacy raw-Enum projection, the denoted
    observable is a [SubEnum], so every result is provably in [[0,1]]. *)
Definition subenum_bool_indicator (b : bool) : rat :=
  if b then (1 : rat) else (0 : rat).

Definition subenum_finite_interaction_probability
    {E : Type -> Type} {R}
    (pattern : @finite_interaction_pattern E)
    (t : ptree E SubEnum R) (p : rat) : Prop :=
  exists (query representative : FreeOmega SubEnum bool)
      (out : SubEnum bool),
    @finite_interaction_query E SubEnum (FreeOmega SubEnum)
      FreeOmegaObservableSemanticMeasure
      FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega R pattern t query /\
    @sem_lift (FreeOmega SubEnum)
      FreeOmegaObservableSemanticMeasure bool bool eq
      representative query /\
    @free_omega_denotes SubEnum SubEnum_SemanticMeasure
      SubEnum_SemanticOmega bool bool id representative out /\
    enum_expect subenum_bool_indicator (subenum_raw out) = p.

Declare Scope subenum_probability_scope.
Delimit Scope subenum_probability_scope with subprob.

Notation "'Prₛ[' t '|' pattern ']' '=' p" :=
  (subenum_finite_interaction_probability pattern t p)
  (at level 70, t at next level, pattern at next level,
   p at next level, no associativity) : subenum_probability_scope.

Lemma subenum_finite_interaction_probability_intro
    {E : Type -> Type} {R}
    (pattern : @finite_interaction_pattern E)
    (t : ptree E SubEnum R) p query representative out :
  @finite_interaction_query E SubEnum (FreeOmega SubEnum)
    FreeOmegaObservableSemanticMeasure
    FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega R pattern t query ->
  @sem_lift (FreeOmega SubEnum)
    FreeOmegaObservableSemanticMeasure bool bool eq
    representative query ->
  @free_omega_denotes SubEnum SubEnum_SemanticMeasure
    SubEnum_SemanticOmega bool bool id representative out ->
  enum_expect subenum_bool_indicator (subenum_raw out) = p ->
  (Prₛ[ t | pattern ] = p)%subprob.
Proof.
  intros Hquery Hlift Hdenotes Hprobability.
  exists query, representative, out. repeat split; assumption.
Qed.

Lemma subenum_bool_indicator_range b :
  is_true (0 <= subenum_bool_indicator b) /\
  is_true (subenum_bool_indicator b <= 1).
Proof. by case: b; split.
Qed.

Theorem subenum_finite_interaction_probability_range
    {E : Type -> Type} {R}
    (pattern : @finite_interaction_pattern E)
    (t : ptree E SubEnum R) p :
  (Prₛ[ t | pattern ] = p)%subprob ->
  is_true (0 <= p) /\ is_true (p <= 1).
Proof.
  intros [query [representative [out [_ [_ [_ Hprob]]]]]].
  have Hnonnegative :
      0 <= enum_expect subenum_bool_indicator (subenum_raw out).
  { apply: enum_expect_nonnegative=> q b Hin.
    exact (proj1 (subenum_bool_indicator_range b)). }
  have Hbelow_mass :
      enum_expect subenum_bool_indicator (subenum_raw out) <=
      enum_mass (subenum_raw out).
  { apply: enum_expect_le_mass=> q b Hin.
    exact (proj2 (subenum_bool_indicator_range b)). }
  rewrite Hprob in Hnonnegative Hbelow_mass.
  split; first exact Hnonnegative.
  exact (le_trans Hbelow_mass (subenum_bound out)).
Qed.
