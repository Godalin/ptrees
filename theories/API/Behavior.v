(** Role: API-only selection of existing behavioral operations. No laws are
    bundled here; raw [PEutt.peutt] remains parameterized by arbitrary MN/MF.
    Fields are deliberately not registered as capability instances. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure Mixed Omega.
From PTree.Eq Require Import PEutt.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class CanonicalBehavior (MN : Type -> Type) := {
  behavior_frontier : Type -> Type;
  behavior_measure : SemanticMeasure behavior_frontier;
  behavior_mixed : MixedMeasure MN behavior_frontier;
  behavior_omega : @SemanticOmega behavior_frontier behavior_measure
}.

(** This wrapper has no new mathematical content. Resolve the operation
    selector first, then obtain laws for exactly its selected measure. *)
Definition canonical_peutt {E MN} `{CB : CanonicalBehavior MN}
    `{FC : @SemanticMeasureCoreLaws behavior_frontier behavior_measure}
    {A B} (RR : A -> B -> Prop)
    (t : ptree E MN A) (u : ptree E MN B) : Prop :=
  @PEutt.peutt E MN behavior_frontier behavior_measure FC
    behavior_mixed behavior_omega A B RR t u.
