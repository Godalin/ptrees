Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From Coq Require Import Morphisms.
From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure.
From PTree.Eq Require Import ShallowNew ProbabilisticEutt PStrong
  OperationalProbabilisticPTSFreeOmegaBase.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** User-facing Monad/Functor equations and setoid instances.  Operational
    cofinality remains in the Base facts module; this file is the lightweight
    algebraic rewriting layer. *)
Section FreeOmegaRewrite.
Context {E : Type -> Type} {MN : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NO : @SemanticOmegaInterface MN NI}.
Local Notation MF := (FreeOmega MN).

Theorem free_probabilistic_eutt_bind_ret_l {A B}
    (a : A) (k : A -> ptree E MN B) :
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface B B eq
    (PTree.bind (Ret a) k) (k a).
Proof.
  apply free_probabilistic_eutt_of_pstructural.
  apply observe_eq_pstructural.
  exact (observing_observe (bind_ret_ a k)).
Qed.

Theorem free_probabilistic_eutt_bind_ret_r {A} (t : ptree E MN A) :
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A A eq
    (PTree.bind t (fun x => Ret x)) t.
Proof.
  apply free_probabilistic_eutt_of_pstructural.
  apply pstructural_bind_ret_r.
Qed.

Theorem free_probabilistic_eutt_bind_assoc {A B C}
    (t : ptree E MN A) (k : A -> ptree E MN B)
    (h : B -> ptree E MN C) :
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface C C eq
    (PTree.bind (PTree.bind t k) h)
    (PTree.bind t (fun x => PTree.bind (k x) h)).
Proof.
  apply free_probabilistic_eutt_of_pstructural.
  apply pstructural_bind_assoc.
Qed.

Theorem free_probabilistic_eutt_fmap_id {A} (t : ptree E MN A) :
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface A A eq
    (PTree.fmap (fun x => x) t) t.
Proof. unfold PTree.fmap. apply free_probabilistic_eutt_bind_ret_r. Qed.

Theorem free_probabilistic_eutt_fmap_compose {A B C}
    (f : A -> B) (g : B -> C) (t : ptree E MN A) :
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface C C eq
    (PTree.fmap g (PTree.fmap f t))
    (PTree.fmap (fun x => g (f x)) t).
Proof.
  apply free_probabilistic_eutt_of_pstructural. unfold PTree.fmap.
  eapply pstructural_trans.
  - apply pstructural_bind_assoc.
  - eapply pstructural_bind with (RA := eq) (RB := eq).
    + intros x1 x2 ->. apply observe_eq_pstructural.
      exact (observing_observe (bind_ret_ (f x2) (fun y => Ret (g y)))).
    + apply pstructural_refl.
Qed.

Theorem free_probabilistic_eutt_fmap_bind {A B C}
    (f : B -> C) (t : ptree E MN A) (k : A -> ptree E MN B) :
  @probabilistic_eutt E MN MF
    (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
    FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasureInterface
    FreeOmegaObservableSemanticOmegaInterface C C eq
    (PTree.fmap f (PTree.bind t k))
    (PTree.bind t (fun x => PTree.fmap f (k x))).
Proof. unfold PTree.fmap. apply free_probabilistic_eutt_bind_assoc. Qed.

#[global] Instance free_probabilistic_eutt_bind_Proper
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    {A B} :
  Proper
    (@probabilistic_eutt E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A A eq ==>
      pointwise_relation A
        (@probabilistic_eutt E MN MF
          (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
          FreeOmegaObservableSemanticMeasureCoreLaws
          FreeOmegaMixedMeasureInterface
          FreeOmegaObservableSemanticOmegaInterface B B eq) ==>
      @probabilistic_eutt E MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasureInterface
        FreeOmegaObservableSemanticOmegaInterface B B eq)
    (@PTree.bind E MN A B).
Proof.
  intros t1 t2 Ht k1 k2 Hk.
  eapply free_probabilistic_eutt_bind with (RR := eq).
  - exact Ht.
  - intros x1 x2 ->. exact (Hk x2).
Qed.

#[global] Instance free_probabilistic_eutt_fmap_Proper
    `{NCAE : @SemanticMeasureCouplingAELaws MN NI}
    `{NCountAE : @SemanticMeasureCountableAELaws MN NI}
    {A B} (f : A -> B) :
  Proper
    (@probabilistic_eutt E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A A eq ==>
     @probabilistic_eutt E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface B B eq)
    (PTree.fmap f).
Proof.
  intros t1 t2 Ht. unfold PTree.fmap.
  eapply free_probabilistic_eutt_bind with (RR := eq).
  - exact Ht.
  - intros x1 x2 ->. apply probabilistic_eutt_refl.
Qed.

End FreeOmegaRewrite.
