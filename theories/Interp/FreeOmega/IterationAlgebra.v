(** Explicit law constructors. Completion supplies probability certificates;
    it neither changes the PTree operations nor chooses a global Eq1. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From ITree.Basics Require Import Basics Monad.
From PTree.Core Require Import PTreeDefinition IterationLaws.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure.
From PTree.Prob.FreeOmega Require Import StructuralMeasure BindOrder RelationalLimit.
From PTree.Interp Require Import IterationAlgebra.
From PTree.Eq Require Import PEutt.
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

Definition free_omega_ptree_eq1 {E} : Eq1 (ptree E MN) :=
  ptree_peutt_eq1 (FI := FI).

Definition free_omega_ptree_equivalence {E} :
  @Eq1Equivalence (ptree E MN) Monad_ptree free_omega_ptree_eq1 :=
  ptree_peutt_equivalence (FI := FI).

Definition free_omega_ptree_monad_laws {E} :
  @MonadLawsE (ptree E MN) free_omega_ptree_eq1 Monad_ptree :=
  ptree_peutt_monad_laws free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub.

Theorem free_omega_peutt_iter_uniform {E I J A}
    (f : I -> ptree E MN (I+A)) (g : J -> ptree E MN (J+A)) (h : I -> J) :
  (forall i, peutt (FI := FI) eq
    (PTree.bind (f i) (fun v => Ret (iteration_map h v))) (g (h i))) ->
  forall i, peutt (FI := FI) eq (PTree.iter f i) (PTree.iter g (h i)).
Proof.
  apply (peutt_iter_uniform free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.
End Completion.
