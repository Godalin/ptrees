From PTree.Prob.FreeOmega Require Import RelationalLimit.
(** Role: Canonical equational/hitting theory. Depends on Core and Prob; does not provide comparison or interpreter semantics. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Morphisms.
From PTree.Core Require Import PTreeDefinition.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
From PTree.Eq Require Import Shallow PEutt PStruct.
From PTree.Eq Require Export Algebra.
From PTree.Eq.FreeOmega Require Import Relation Bind.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** User-facing Monad/Functor equations and setoid instances.  Scheduling
    cofinality remains in the Bind module; this file is the lightweight
    algebraic rewriting layer. *)
Section FreeOmegaAlgebra.
Context {E : Type -> Type} {MN : Type -> Type}
  `{NI : SemanticMeasure MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NO : @SemanticOmega MN NI}.
Local Notation MF := (FreeOmega MN).

Theorem peutt_bind_ret_l {A B}
    (a : A) (k : A -> ptree E MN B) :
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega B B eq
    (PTree.bind (Ret a) k) (k a).
Proof.
  apply Algebra.peutt_bind_ret_l.
Qed.

Theorem peutt_bind_ret_r {A} (t : ptree E MN A) :
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A A eq
    (PTree.bind t (fun x => Ret x)) t.
Proof.
  apply (Algebra.peutt_bind_ret_r
    free_omega_relational_bind free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem peutt_bind_assoc {A B C}
    (t : ptree E MN A) (k : A -> ptree E MN B)
    (h : B -> ptree E MN C) :
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega C C eq
    (PTree.bind (PTree.bind t k) h)
    (PTree.bind t (fun x => PTree.bind (k x) h)).
Proof.
  apply (Algebra.peutt_bind_assoc
    free_omega_relational_bind free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem peutt_fmap_id {A} (t : ptree E MN A) :
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A A eq
    (PTree.fmap (fun x => x) t) t.
Proof.
  apply (Algebra.peutt_fmap_id
    free_omega_relational_bind free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem peutt_fmap_compose {A B C}
    (f : A -> B) (g : B -> C) (t : ptree E MN A) :
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega C C eq
    (PTree.fmap g (PTree.fmap f t))
    (PTree.fmap (fun x => g (f x)) t).
Proof.
  apply (Algebra.peutt_fmap_compose
    free_omega_relational_bind free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

Theorem peutt_fmap_bind {A B C}
    (f : B -> C) (t : ptree E MN A) (k : A -> ptree E MN B) :
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega C C eq
    (PTree.fmap f (PTree.bind t k))
    (PTree.bind t (fun x => PTree.fmap f (k x))).
Proof.
  apply (Algebra.peutt_fmap_bind
    free_omega_relational_bind free_omega_relational_mixed_bind
    free_omega_relational_zero free_omega_relational_lub).
Qed.

End FreeOmegaAlgebra.
