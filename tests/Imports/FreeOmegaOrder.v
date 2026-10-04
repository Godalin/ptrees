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
