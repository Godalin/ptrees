(** Public order tools must not load validating models, a concrete backend,
    or the PTree layer. This compilation client is not installed theory. *)
From Coq Require Import Utf8.
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From PTree.Prob.Interface Require Import Measure Omega.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Approximation Measure IterationOrder.
Import FreeOmegaOrderNotations.
Local Open Scope freeomega_scope.

Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
Fail Check PTree.Core.PTreeDefinition.ptree.
Fail Check PTree.Prob.Backend.SubEnumQ.Measure.SubEnumQ.

Section Client.
Universe u.
Context {MN : Type → Type} `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI} `{NO : @SemanticOmega MN NI}.

Example high_carrier_order (A : Type@{u}) :
  (@FORet MN Type@{u} A) ⊑ω FORet A.
Proof. apply free_omega_sem_le_refl. Qed.

Example structural_order_unchanged {A} (t u : FreeOmega MN A) :
  @sem_le (FreeOmega MN) (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticOmega _ t u ↔ free_omega_approx eq t u.
Proof. reflexivity. Qed.
End Client.

(** The PTree specialization is opt-in and still does not load validation.
    Real weights discharge the same native profile as the rational example,
    without native omega-completeness or a supplied supremum axiom. *)
From PTree.Core Require Import PTreeDefinition.
From PTree.Eq Require Import UnifiedFrontier.
From PTree.Interp.FreeOmega Require Import AbsorbingIteration FrontierOrder.
Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
From mathcomp Require Import reals.
From PTree.Prob.Backend.SubEnumR Require Import Representation Measure Coupling Omega.

Section RealClient.
Variable R : realType.
Context {E : Type → Type} {I A : Type}
  (step : I → ptree E (SubEnumR R) (I+A))
  (front : I → FreeOmega (SubEnumR R) (stable_head E (SubEnumR R) (I+A))).

Example real_summary_bound Y :
  (∀ i, free_omega_summary_step step front Y i ⊑ω Y i) →
  ∀ i, complete_iteration_frontier step front i ⊑ω Y i.
Proof. exact (proj2 (free_omega_summary_least_fixed_point step front) Y). Qed.
End RealClient.

Fail Check PTree.Prob.Domain.Expectation.OmegaVal.
