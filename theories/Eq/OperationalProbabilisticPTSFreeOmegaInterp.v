Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

From PTree.Core Require Import PTreeDefinitionNew.
From PTree.Prob Require Import TwoLevelMeasure FreeOmegaMeasure.
From PTree.Eq Require Import
  UnifiedFrontier OperationalProbabilisticPTS ProbabilisticEutt
  OperationalProbabilisticPTSFreeOmegaBase.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Focused behavioral facts for effect interpretation over the maintained
    FreeOmega backend.  This module deliberately exposes the one remaining
    algebraic boundary: an effectful handler must close the native generator
    at handler-produced binds.  Operational scheduling and omega-limit
    composition have already been discharged by
    [free_operational_interp_cofinal_all]. *)
Section FreeOmegaInterpCoinduction.
Context {E F : Type -> Type} {MN : Type -> Type}
  `{NI : SemanticMeasureInterface MN}
  `{NC : @SemanticMeasureCoreLaws MN NI}
  `{NAE : @SemanticMeasureAELiftLaws MN NI}
  `{NO : @SemanticOmegaInterface MN NI}.

Local Notation MF := (FreeOmega MN).

Context {A B : Type} (RR : A -> B -> Prop)
  (handler : forall X, E X -> ptree F MN X).

(** The smallest source-indexed candidate needed for full interpreter
    preservation.  It contains no syntax cases: a target-state pair belongs
    to the candidate exactly when it is obtained by interpreting a pair
    already related by the canonical source equivalence. *)
Definition free_interp_bisim_candidate
    (s1 : ptree' F MN A) (s2 : ptree' F MN B) : Prop :=
  exists (t1 : ptree E MN A) (t2 : ptree E MN B),
    s1 = observe (PTree.interp handler t1) /\
    s2 = observe (PTree.interp handler t2) /\
    @probabilistic_eutt E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A B RR t1 t2.

(** Exact closure obligation for an arbitrary effectful handler.  Compared
    with the generic PTree coinduction rule, the candidate is fixed to
    interpreted source equivalence.  Consequently an implementation of this
    premise cannot hide a different behavioral relation or strengthen the
    theorem's conclusion. *)
Definition free_interp_generator_closed : Prop :=
  forall (t1 : ptree E MN A) (t2 : ptree E MN B),
    @probabilistic_eutt E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A B RR t1 t2 ->
    @stable_hitting_match MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticOmegaInterface
      (ptree' F MN A) (ptree' F MN B)
      (frontier_head F MN A) (frontier_head F MN B)
      (@ptree_primitive_kernel F MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface A)
      (@ptree_primitive_kernel F MN MF
        (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
        FreeOmegaMixedMeasureInterface B)
      (@ptree_stable_head_rel F MN A B RR)
      free_interp_bisim_candidate
      (observe (PTree.interp handler t1))
      (observe (PTree.interp handler t2)).

(** Full behavioral preservation follows from precisely the candidate-level
    handler closure above.  The canonical generator is unchanged. *)
Theorem free_probabilistic_eutt_interp_of_generator_closed
    (Hclosed : free_interp_generator_closed) :
  forall (t1 : ptree E MN A) (t2 : ptree E MN B),
    @probabilistic_eutt E MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A B RR t1 t2 ->
    @probabilistic_eutt F MN MF
      (FreeOmegaObservableSemanticMeasureInterface (NI := NI) (NO := NO))
      FreeOmegaObservableSemanticMeasureCoreLaws
      FreeOmegaMixedMeasureInterface
      FreeOmegaObservableSemanticOmegaInterface A B RR
      (PTree.interp handler t1) (PTree.interp handler t2).
Proof.
  intros t1 t2 Hsource.
  eapply probabilistic_eutt_coinduction with
      (sim := free_interp_bisim_candidate).
  - intros s1 s2 [u1 [u2 [-> [-> Hu]]]]. exact (Hclosed u1 u2 Hu).
  - exists t1, t2. repeat split; try reflexivity. exact Hsource.
Qed.

End FreeOmegaInterpCoinduction.
