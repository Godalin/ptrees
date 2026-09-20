(** Role: Contract regression. Tests maintained boundaries; not a public theory endpoint or paper case study. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Eq Require Import PTreeKernel PEutt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section NotationRegression.
Context {E : Type -> Type} {MN MF : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{FI : SemanticMeasure MF}
  `{FC : @SemanticMeasureCoreLaws MF FI}
  `{MX : MixedMeasure MN MF}
  `{FO : @SemanticOmega MF FI}.

Lemma peutt_notation_homogeneous {R}
    (t u : ptree E MN R) :
  (t ≈ₚ u) <-> peutt eq t u.
Proof. reflexivity. Qed.

Lemma peutt_notation_heterogeneous {R1 R2}
    (RR : R1 -> R2 -> Prop) (t : ptree E MN R1) (u : ptree E MN R2) :
  (t ≈ₚ[RR] u) <-> peutt RR t u.
Proof. reflexivity. Qed.

End NotationRegression.
