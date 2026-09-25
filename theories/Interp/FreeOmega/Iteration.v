(** Completion certificates only; the eventful iteration proof is generic. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure.
From PTree.Prob.FreeOmega Require Import StructuralMeasure BindOrder RelationalLimit.
From PTree.Eq Require Import PStruct PEutt.
From PTree.Interp Require Import Iteration.
Set Implicit Arguments.
Unset Strict Implicit.

Section Completion.
Context {MN : Type -> Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation FI := (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO)).

Theorem free_omega_peutt_iter_eventful_rel {E I J A B}
    (step1 : I -> ptree E MN (I+A)) (step2 : J -> ptree E MN (J+B))
    (SI : I -> J -> Prop) (RR : A -> B -> Prop) :
  (forall i j, SI i j -> peutt (FI := FI) (pstruct_iter_sum_rel SI RR)
    (step1 i) (step2 j)) ->
  forall i j, SI i j ->
    peutt (FI := FI) RR (PTree.iter step1 i) (PTree.iter step2 j).
Proof.
  apply (peutt_iter_eventful_rel free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Corollary free_omega_peutt_iter_eventful {E I A}
    (step1 step2 : I -> ptree E MN (I+A)) :
  (forall i, peutt (FI := FI) eq (step1 i) (step2 i)) ->
  forall i, peutt (FI := FI) eq (PTree.iter step1 i) (PTree.iter step2 i).
Proof.
  apply (peutt_iter_eventful free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.
End Completion.
