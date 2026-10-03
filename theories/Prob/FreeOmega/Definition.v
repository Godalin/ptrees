(** Role: Universe-separated completion syntax, bind, structural AE and lifting; no concrete backend. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.

Require Import FunctionalExtensionality.
From Coq.Program Require Import Equality.
Require Import Morphisms Arith.

From PTree.Prob.Interface Require Import Measure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A universe-separated free behavior measure.  Samples remain in the
    carrier universe accepted by [MN], whereas results may inhabit a higher
    frontier universe.  [FOLub] is the formal omega completion; no HB
    measurable structure is requested for the result carrier. *)
Polymorphic Inductive FreeOmega@{node node_rep frontier}
    (MN : Type@{node} → Type@{node_rep})
    (A : Type@{frontier}) : Type :=
  | FORet (x : A)
  | FOZero
  | FOSample {X : Type@{node}} (mu : MN X) (k : X → FreeOmega MN A)
  | FOLub (chain : nat → FreeOmega MN A).

Arguments FORet {MN A} _.
Arguments FOZero {MN A}.
Arguments FOSample {MN A X} _ _.
Arguments FOLub {MN A} _.

(** [Anchor] pins the otherwise minimizable result universe.  This is useful
    when a low type such as [bool] must inhabit the same [MF] instance as a
    high recursive frontier head. *)
Polymorphic Definition FreeOmegaAt@{node node_rep frontier}
    (MN : Type@{node} → Type@{node_rep})
    (Anchor A : Type@{frontier}) : Type@{frontier} :=
  @FreeOmega@{node node_rep frontier} MN A.

Polymorphic Fixpoint free_omega_bind {MN A B}
    (mu : FreeOmega MN A) (k : A → FreeOmega MN B) : FreeOmega MN B :=
  match mu with
  | FORet x => k x
  | FOZero => FOZero
  | FOSample nu h => FOSample nu (λ x, free_omega_bind (h x) k)
  | FOLub chain => FOLub (λ n, free_omega_bind (chain n) k)
  end.

Polymorphic Inductive free_omega_ae {MN}
    `{NI : SemanticMeasure MN} {A}
    (P : A → Prop) : FreeOmega MN A → Prop :=
  | FOAERet x : P x → free_omega_ae P (FORet x)
  | FOAEZero : free_omega_ae P FOZero
  | FOAESample {X} (mu : MN X) k (Good : X → Prop) :
      sem_ae mu Good →
      (∀ x, Good x → free_omega_ae P (k x)) →
      free_omega_ae P (FOSample mu k)
  | FOAELub chain :
      (∀ n, free_omega_ae P (chain n)) →
      free_omega_ae P (FOLub chain).

Polymorphic Inductive free_omega_lift {MN}
    `{NI : SemanticMeasure MN} {A B}
    (R : A → B → Prop) : FreeOmega MN A → FreeOmega MN B → Prop :=
  | FOLRet x y : R x y →
      free_omega_lift R (FORet x) (FORet y)
  | FOLZero : free_omega_lift R FOZero FOZero
  | FOLSample {X Y} (S : X → Y → Prop)
      (mu : MN X) (nu : MN Y) k h :
      sem_lift S mu nu →
      (∀ x y, S x y → free_omega_lift R (k x) (h y)) →
      free_omega_lift R (FOSample mu k) (FOSample nu h)
  | FOLLub c d :
      (∀ n, free_omega_lift R (c n) (d n)) →
      free_omega_lift R (FOLub c) (FOLub d).

(** Identity-decoder embedding of a native sample. No normalization and no
    new semantics: this is definitionally [FOSample mu (fun x => FORet x)]. *)
Polymorphic Definition free_omega_sample@{node node_rep frontier}
    {MN : Type@{node} → Type@{node_rep}} {A : Type@{node}} (mu : MN A) :
    @FreeOmega@{node node_rep frontier} MN A :=
  FOSample mu (λ x, FORet x).

(** Opt-in client notation; no scope is opened here.
    [supω] denotes raw FOLub syntax, not a certified supremum: increasingness
    or modelability must still be established by the relevant semantic laws.
    [ηω] returns a value in FreeOmega, not a PTree program or a stable head.
    [>>=ω] is syntax-level bind, independent of any SemanticMeasure instance. *)
Declare Scope freeomega_scope.
Delimit Scope freeomega_scope with fo.

Notation "'ηω' x" := (FORet x)
  (at level 10, x at next level) : freeomega_scope.
Notation "'⊥ω'" := FOZero : freeomega_scope.
(** Match ExtLib's sequencing precedence so its [;;] cannot be consumed
    as part of the native distribution when both scopes are in use. *)
(** This samples [MN], unlike [>>=ω], which binds a FreeOmega expression. *)
Notation "x '←ω' mu ';;' t" := (FOSample mu (fun x => t))
  (at level 61, mu at next level, right associativity)
  : freeomega_scope.
Notation "mu '>>=ω' k" := (free_omega_bind mu k)
  (at level 50, left associativity) : freeomega_scope.
Notation "'supω' n ',' t" := (FOLub (fun n => t))
  (at level 100, n binder, right associativity) : freeomega_scope.
Notation "'↑ω' mu" := (free_omega_sample mu)
  (at level 10, mu at next level) : freeomega_scope.
