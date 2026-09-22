(** Role: Individual validity, closure laws and intrinsic carrier validity; distinct capabilities. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PTree.Prob.Interface.Measure.

(** Probability-specific validity is deliberately separate from the generic
    measure-like algebra.  This permits raw weighted models (for example a
    future unrestricted Bayesian [score]) without weakening the contract of
    a native [Prob] node.  Concrete backends give [sem_subprob] their actual
    mass-bounded meaning. *)
Polymorphic Class SemanticSubprobability@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasure S} := {
  sem_subprob : forall {A : Type@{carrier}}, S A -> Prop
}.

(** Closure facts for individually validated measures.  Pointwise bind
    validity is intentionally sufficient; support/AE refinements can be
    added later without making the basic probability boundary depend on a
    particular representation of null branches. *)
Polymorphic Class SemanticSubprobabilityLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasure S}
    `{SP : @SemanticSubprobability S SI} := {
  sem_subprob_ret : forall {A : Type@{carrier}} (x : A),
      sem_subprob (sem_ret x);
  sem_subprob_bind : forall {A B : Type@{carrier}}
      (mu : S A) (k : A -> S B),
      sem_subprob mu ->
      (forall x, sem_subprob (k x)) ->
      sem_subprob (sem_bind mu k);
  sem_subprob_proper : forall {A : Type@{carrier}} (mu nu : S A),
      sem_eq mu nu -> (sem_subprob mu <-> sem_subprob nu)
}.

(** Intrinsically bounded carriers validate every inhabitant.  [SubEnumQ] and
    MathComp's subprobability kernels implement this package; raw [EnumQ]
    implements only the predicate and closure laws above. *)
Polymorphic Class SemanticSubprobabilityCarrierLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasure S}
    `{SP : @SemanticSubprobability S SI} := {
  sem_subprob_all : forall {A : Type@{carrier}} (mu : S A), sem_subprob mu
}.
