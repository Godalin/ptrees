Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import TwoLevelMeasure.
From PTree.Eq Require Import OperationalProbabilisticPTS ProbabilisticEutt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NotationRegression.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{FI : SemanticMeasureInterface MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasureInterface MN MF}
  `{FO : @SemanticOmegaInterface MF FI}.

Lemma probabilistic_eutt_notation_homogeneous {R}
    (t u : ptree E MN R) :
  (t ≈ₚ u) <-> probabilistic_eutt eq t u.
Proof. reflexivity. Qed.

Lemma probabilistic_eutt_notation_heterogeneous {R1 R2}
    (RR : R1 -> R2 -> Prop) (t : ptree E MN R1) (u : ptree E MN R2) :
  (t ≈ₚ[RR] u) <-> probabilistic_eutt RR t u.
Proof. reflexivity. Qed.

End NotationRegression.
