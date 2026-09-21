(** Role: Almost-everywhere capabilities; no omega or mixed-measure assumption. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PTree.Prob.Interface.Measure.

(** The diagonal coupling may be restricted to an almost-everywhere good
    set.  This capability is precisely what turns AE equality of kernels into
    Kleisli congruence; it is kept separate from the basic coupling algebra. *)
Polymorphic Class SemanticMeasureAELiftLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasure S} := {
  sem_lift_refl_ae : forall {A : Type@{carrier}}
      (mu : S A) (P : A -> Prop),
      sem_ae mu P ->
      sem_lift (fun x y => x = y /\ P x) mu mu
}.


(** Measures are closed under countable intersections of almost-everywhere
    predicates.  This is the measure-theoretic ingredient needed when an
    omega construction exposes one AE side condition at every finite
    approximation.  It is separate from finite conjunction so finite-state
    clients do not need to assume sigma-completeness. *)
Polymorphic Class SemanticMeasureCountableAELaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasure S} := {
  sem_ae_countable : forall {A : Type@{carrier}} (mu : S A)
      (P : nat -> A -> Prop),
    (forall n, sem_ae mu (P n)) ->
    sem_ae mu (fun x => forall n, P n x)
}.

(** Predicate semantics for the monadic operations.  These laws are kept
    separate from extensional equality and coupling: they are exactly the
    capability needed to propagate an invariant through a finite kernel
    computation. *)
Polymorphic Class SemanticMeasureAEKleisliLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasure S} := {
  sem_ae_ret : forall {A : Type@{carrier}} (P : A -> Prop) x,
      P x -> sem_ae (sem_ret x) P;
  sem_ae_bind : forall {A B : Type@{carrier}}
      (mu : S A) (k : A -> S B) (P : A -> Prop) (Q : B -> Prop),
      sem_ae mu P ->
      (forall x, P x -> sem_ae (k x) Q) ->
      sem_ae (sem_bind mu k) Q
}.

(** Exact almost-everywhere characterization of semantic Dirac measures.
    Positive AE introduction alone is insufficient to discard branches other
    than the selected point when quotienting a sampled Dirac. *)
Polymorphic Class SemanticMeasureDiracAELaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasure S} := {
  sem_ae_ret_iff : forall {A : Type@{carrier}} (x : A) (P : A -> Prop),
      sem_ae (sem_ret x) P <-> P x
}.

(** Exact support decomposition for node-level Kleisli bind.  The forward
    implication supplied by [SemanticMeasureAEKleisliLaws] is sufficient for
    many soundness arguments; quotienting one bound sample with two nested
    samples also needs this reverse characterization. *)
Polymorphic Class SemanticMeasureBindAEExactLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasure S} := {
  sem_ae_bind_iff : forall {A B : Type@{carrier}}
      (mu : S A) (k : A -> S B) (P : B -> Prop),
      sem_ae (sem_bind mu k) P <->
      sem_ae mu (fun x => sem_ae (k x) P)
}.
