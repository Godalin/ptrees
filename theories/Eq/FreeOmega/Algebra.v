(** Role: Canonical equational/hitting theory. Depends on Core and Prob; does not provide comparison or interpreter semantics. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Morphisms.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Interface Require Import TwoLevelMeasure.
From PTree.Prob.FreeOmega Require Import FreeOmegaMeasure.
From PTree.Eq Require Import Shallow PEutt PStruct.
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
  apply peutt_of_pstruct.
  apply observe_eq_pstruct.
  exact (observing_observe (bind_ret_ a k)).
Qed.

Theorem peutt_bind_ret_r {A} (t : ptree E MN A) :
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A A eq
    (PTree.bind t (fun x => Ret x)) t.
Proof.
  apply peutt_of_pstruct.
  apply pstruct_bind_ret_r.
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
  apply peutt_of_pstruct.
  apply pstruct_bind_assoc.
Qed.

Theorem peutt_fmap_id {A} (t : ptree E MN A) :
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega A A eq
    (PTree.fmap (fun x => x) t) t.
Proof. unfold PTree.fmap. apply peutt_bind_ret_r. Qed.

Theorem peutt_fmap_compose {A B C}
    (f : A -> B) (g : B -> C) (t : ptree E MN A) :
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega C C eq
    (PTree.fmap g (PTree.fmap f t))
    (PTree.fmap (fun x => g (f x)) t).
Proof.
  apply peutt_of_pstruct. unfold PTree.fmap.
  eapply pstruct_trans.
  - apply pstruct_bind_assoc.
  - eapply pstruct_bind with (RA := eq) (RB := eq).
    + intros x1 x2 ->. apply observe_eq_pstruct.
      exact (observing_observe (bind_ret_ (f x2) (fun y => Ret (g y)))).
    + apply pstruct_refl.
Qed.

Theorem peutt_fmap_bind {A B C}
    (f : B -> C) (t : ptree E MN A) (k : A -> ptree E MN B) :
  @peutt E MN MF
    (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
    FreeOmegaObservableSemanticOmega C C eq
    (PTree.fmap f (PTree.bind t k))
    (PTree.bind t (fun x => PTree.fmap f (k x))).
Proof. unfold PTree.fmap. apply peutt_bind_assoc. Qed.

#[global] Instance peutt_bind_Proper
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    {A B} :
  Proper
    (@peutt E MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega A A eq ==>
      pointwise_relation A
        (@peutt E MN MF
          (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
          FreeOmegaObservableSemanticMeasureCoreLaws
          FreeOmegaMixedMeasure
          FreeOmegaObservableSemanticOmega B B eq) ==>
      @peutt E MN MF
        (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
        FreeOmegaObservableSemanticOmega B B eq)
    (@PTree.bind E MN A B).
Proof.
  intros t1 t2 Ht k1 k2 Hk.
  eapply peutt_bind with (RR := eq).
  - exact Ht.
  - intros x1 x2 ->. exact (Hk x2).
Qed.

#[global] Instance peutt_fmap_Proper
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    {A B} (f : A -> B) :
  Proper
    (@peutt E MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega A A eq ==>
     @peutt E MN MF
      (FreeOmegaObservableSemanticMeasure (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasure
      FreeOmegaObservableSemanticOmega B B eq)
    (PTree.fmap f).
Proof.
  intros t1 t2 Ht. unfold PTree.fmap.
  eapply peutt_bind with (RR := eq).
  - exact Ht.
  - intros x1 x2 ->. apply peutt_refl.
Qed.

End FreeOmegaAlgebra.
