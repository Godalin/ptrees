Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From PTree.Prob Require Import DiscreteMC TwoLevelMeasureEnum.
From PTree.Eq Require Import UnifiedPWeak UnifiedPWeakEnumFacts.
From PTree.Examples Require Import VonNeumannUnbounded BernoulliFactory.

(** An unbounded almost-surely terminating sampler is weakly bisimilar, in
    the new single-frontier semantics, to one terminating fair sample. *)
Theorem unified_von_neumann_third_equivalent_to_fair :
  @weak_bisim vnE Enum.Enum Enum.Enum
    Enum_SemanticMeasureInterface Enum_SemanticMeasureInterface
    Enum_SemanticMeasureCoreLaws Enum_SemanticMeasureCoreLaws
    Enum_MixedMeasureInterface Enum_SemanticOmegaInterface
    bool bool eq von_neumann_third direct_fair.
Proof.
  apply auweak_to_weak_bisim.
  exact von_neumann_third_equivalent_to_fair.
Qed.

(** Closed p-to-q Bernoulli factory example: repeated samples from a [1/3]
    coin implement a direct [2/5] coin, including both unbounded loops. *)
Theorem unified_third_coin_simulates_two_fifths :
  @weak_bisim factoryE Enum.Enum Enum.Enum
    Enum_SemanticMeasureInterface Enum_SemanticMeasureInterface
    Enum_SemanticMeasureCoreLaws Enum_SemanticMeasureCoreLaws
    Enum_MixedMeasureInterface Enum_SemanticOmegaInterface
    bool bool eq third_to_two_fifths direct_two_fifths.
Proof.
  apply auweak_to_weak_bisim.
  exact (proj2 (proj2 third_coin_simulates_two_fifths_correct)).
Qed.
