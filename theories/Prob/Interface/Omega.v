(** Role: Order, totality and countable-limit capabilities on one semantic carrier. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import PTree.Prob.Interface.Measure.


(** Omega structure belongs to the semantic/frontier layer.  The order is
    explicit so a unified frontier can state that finite approximants form an
    increasing chain instead of treating every arbitrary sequence as a lub. *)
Polymorphic Class SemanticOmega@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasure S} := {
  sem_zero : forall {A : Type@{carrier}}, S A;
  sem_le : forall {A : Type@{carrier}}, S A -> S A -> Prop;
  sem_lub : forall {A : Type@{carrier}}, (nat -> S A) -> S A -> Prop;
  sem_total : forall {A : Type@{carrier}}, S A -> Prop
}.

Definition sem_increasing {SM} `{SI : SemanticMeasure SM}
    `{SO : @SemanticOmega SM SI} {A}
    (chain : nat -> SM A) : Prop :=
  forall n, sem_le (chain n) (chain (Datatypes.S n)).

Definition sem_zero_prefix {SM} `{SI : SemanticMeasure SM}
    `{SO : @SemanticOmega SM SI} {A}
    (chain : nat -> SM A) : nat -> SM A :=
  fun n => match n with O => sem_zero | Datatypes.S n' => chain n' end.

(** Minimal order theory needed to show that primitive stable-hitting
    approximants form an increasing chain.  It is independent of omega-limit
    existence and can therefore be supplied by partial backends. *)
Polymorphic Class SemanticMeasureOrderLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasure S}
    `{SO : @SemanticOmega S SI} := {
  sem_le_refl : forall {A : Type@{carrier}} (mu : S A), sem_le mu mu;
  sem_le_trans : forall {A : Type@{carrier}} (mu nu xi : S A),
      sem_le mu nu -> sem_le nu xi -> sem_le mu xi;
  sem_zero_le : forall {A : Type@{carrier}} (mu : S A), sem_le sem_zero mu;
  sem_bind_le_mu : forall {A B : Type@{carrier}} (mu nu : S A)
      (k : A -> S B),
      sem_le mu nu -> sem_le (sem_bind mu k) (sem_bind nu k);
  sem_bind_le_k : forall {A B : Type@{carrier}} (mu : S A)
      (k h : A -> S B),
      (forall x, sem_le (k x) (h x)) ->
      sem_le (sem_bind mu k) (sem_bind mu h)
}.

(** Continuity needed by the absorbing PTS construction.  Existence is
    restricted to increasing chains; uniqueness and bind-continuity are
    extensional. *)
Polymorphic Class SemanticOmegaLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasure S}
    `{SO : @SemanticOmega S SI} := {
  sem_lub_exists : forall {A : Type@{carrier}} (chain : nat -> S A),
      sem_increasing chain -> exists out, sem_lub chain out;
  sem_lub_unique : forall {A : Type@{carrier}} (chain : nat -> S A) mu nu,
      sem_lub chain mu -> sem_lub chain nu -> sem_eq mu nu;
  sem_lub_proper : forall {A : Type@{carrier}}
      (chain chain' : nat -> S A) mu nu,
      (forall n, sem_eq (chain n) (chain' n)) ->
      sem_lub chain mu -> sem_lub chain' nu -> sem_eq mu nu;
  sem_lub_chain_proper : forall {A : Type@{carrier}}
      (chain chain' : nat -> S A) mu,
      (forall n, sem_eq (chain n) (chain' n)) ->
      sem_lub chain mu -> sem_lub chain' mu;
  sem_bind_lub : forall {A B : Type@{carrier}} (chain : nat -> S A) mu
      (k : A -> S B),
      sem_increasing chain -> sem_lub chain mu ->
      sem_lub (fun n => sem_bind (chain n) k) (sem_bind mu k)
}.

(** Almost-everywhere predicates are admissible for bottom and omega limits.
    Together with [SemanticMeasureAEKleisliLaws], this turns one-step AE
    kernel invariants into invariants of unbounded stable hitting. *)
Polymorphic Class SemanticOmegaAELaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasure S}
    `{SO : @SemanticOmega S SI} := {
  sem_ae_zero : forall {A : Type@{carrier}} (P : A -> Prop),
      sem_ae (@sem_zero S SI SO A) P;
  sem_ae_lub : forall {A : Type@{carrier}}
      (chain : nat -> S A) out (P : A -> Prop),
      sem_lub chain out ->
      (forall n, sem_ae (chain n) P) ->
      sem_ae out P
}.

(** Extensionality of almost-sure termination.  It is separated from omega
    completeness because a backend may support a relational limit without
    quotienting its concrete representation strongly enough to prove this
    law.  Operational AST transfer across denotational equality requires it
    explicitly. *)
Polymorphic Class SemanticTotalProperLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasure S}
    `{SO : @SemanticOmega S SI} := {
  sem_total_proper : forall {A : Type@{carrier}} (mu nu : S A),
      sem_eq mu nu -> (sem_total mu <-> sem_total nu)
}.

(** Cofinality needed for silent operational steps.  It is deliberately
    separate from ordinary omega completeness: a backend may provide formal
    lub syntax without quotienting away finite prefixes. *)
Polymorphic Class SemanticOmegaCofinalityLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasure S}
    `{SO : @SemanticOmega S SI} := {
  sem_lub_zero_prefix : forall {A : Type@{carrier}}
      (chain : nat -> S A) out,
      sem_lub chain out <-> sem_lub (sem_zero_prefix chain) out;
  sem_lub_constant : forall {A : Type@{carrier}} (mu : S A),
      sem_lub (fun _ => mu) mu
}.


(** Joint continuity for a growing source measure and growing continuation
    kernels.  This is stronger than [sem_bind_lub], whose kernel is fixed,
    and is exactly the measure-level half of operational Bind soundness. *)
Polymorphic Class SemanticMeasureDiagonalLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasure S}
    `{SO : @SemanticOmega S SI} := {
  sem_bind_diagonal_lub : forall {A B : Type@{carrier}}
      (source : nat -> S A) (source_out : S A)
      (kernels : A -> nat -> S B) (kernel_out : A -> S B),
      sem_increasing source ->
      (forall x, sem_increasing (kernels x)) ->
      sem_lub source source_out ->
      (forall x, sem_lub (kernels x) (kernel_out x)) ->
      sem_lub
        (fun n => sem_bind (source n) (fun x => kernels x n))
        (sem_bind source_out kernel_out)
}.

(** Fubini/diagonal continuity for two independent approximation indices.
    This is the semantic capability required by genuinely nested unbounded
    computation.  It is intentionally stronger than finite cofinality: an
    inner AST sampler need not expose its complete output at any finite
    fuel, so no finite maximum can replace this double-limit law.

    Monotonicity in both coordinates makes the diagonal chain cofinal in the
    product order.  Backends based on ordinary subprobability measures can
    discharge this with monotone convergence; formal completions may instead
    provide it through their observation quotient. *)
Polymorphic Class SemanticOmegaFubiniLaws@{carrier representation}
    (S : Type@{carrier} -> Type@{representation})
    `{SI : SemanticMeasure S}
    `{SO : @SemanticOmega S SI} := {
  sem_lub_double_diagonal : forall {A : Type@{carrier}}
      (grid : nat -> nat -> S A)
      (row_out : nat -> S A) (out : S A),
      (forall outer, sem_increasing (grid outer)) ->
      (forall inner, sem_increasing (fun outer => grid outer inner)) ->
      (forall outer, sem_lub (grid outer) (row_out outer)) ->
      sem_lub row_out out ->
      sem_lub (fun fuel => grid fuel fuel) out
}.
