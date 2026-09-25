(** Completion supplies only the existing probability certificates. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From ITree.Basics Require Import Basics Monad.
From PTree.Core Require Import PTreeDefinition IterationLaws.
From PTree.Prob.Interface Require Import Measure AE Coupling Omega.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Measure.
From PTree.Prob.FreeOmega Require Import StructuralMeasure BindOrder RelationalLimit.
From PTree.Interp Require Import IterationUniform.
From PTree.Interp.FreeOmega Require Import IterationAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.

Section Completion.
Context {MN : Type -> Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
  `{NCount : @SemanticMeasureCountableAELaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Theorem free_omega_ptree_iteration_uniform {E} :
  @iteration_uniform (ptree E MN) Monad_ptree MonadIter_ptree free_omega_ptree_eq1.
Proof.
  exact (ptree_peutt_iteration_uniform free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.
End Completion.
