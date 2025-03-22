(** This file formalizes the probability tree: PTree, as an
    negative coinductive type.

    The most interesting part of this formalization lies in
    the fact that, with the constructor [Prob], we can create
    a stochastic choice with some weight provided by the [measure]
    construct. *)

Require Import Program.

From ExtLib Require Import Structures.Functor.
From ExtLib Require Import Structures.Applicative.
From ExtLib Require Import Structures.Monads.

From ITree.Basics Require Import Basics.
From ITree.Basics Require Import Monad.
From ITree.Core Require Import Subevent.
From ITree.Indexed Require Import Sum.
From ITree Require Eq.

From mathcomp Require Import eqtype seq.

From PTree.Core Require Import Utils.
From PTree.Prob Require Import Monad.
From PTree.Prob Require Import DiscreteMC.

Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.



Section ptree.

Context {E : Type -> Type}.
Context {M : Type -> Type}.
Context `{DiscreteInterface M}.
Context {R : Type}.

Variant ptreeF {ptree : Type} : Type :=
| RetF (r : R)
| TauF (e : ptree)
| VisF {X} (e : E X) (k : X -> ptree)
| ProbF {X : eqType} (μ : M X) (k : X -> ptree).

CoInductive ptree : Type :=
  go { _observe : @ptreeF ptree }.

End ptree.

(** A new [ptree_scope] for [PTrees] *)

Declare Scope ptree_scope.
Bind Scope ptree_scope with ptree.
Delimit Scope ptree_scope with ptree.
Local Open Scope ptree_scope.

Arguments ptree _ _ : clear implicits.
Arguments ptreeF _ _ : clear implicits.
Arguments ProbF {E M R} [ptree] {X} μ k.

Notation ptree' E M R := (ptreeF E M R (ptree E M R)).

Definition observe {E M R} (t : ptree E M R) : ptree' E M R :=
  @_observe E M R t.

Ltac __desobs t H := destruct (observe t) eqn:H.
Tactic Notation "desobs" ident(t) := destruct (observe t).
Tactic Notation "desobs" ident(t) ident(H) := __desobs t H.



(** Notations for constructors of PTrees. *)

Notation Ret x   := (go (RetF x)).
Notation Vis e k := (go (VisF e k)).
Notation Tau e   := (go (TauF e)).
Notation Prob μ k := (go (ProbF μ k)).

Definition ProbF0 {E M R} `{DiscreteInterface M} (μ : M void) k
  : ptree' E M R :=
    ProbF μ k.

Definition Prob0 {E M R} `{DiscreteInterface M} (μ : M void) k
  : ptree E M R :=
    Prob μ k.



(*| Main Operations for PTrees. |*)
Module PTree.

(*| Monadic Operations |*)
Import MonadNotation.

Definition ret {E M R} (r : R) : ptree E M R
  := Ret r.

Definition subst {E M T U} (k : T -> ptree E M U)
     : ptree E M T -> ptree E M U :=
  cofix _subst (u : ptree E M T) :=
    match observe u with
    | RetF r => k r
    | TauF t => Tau (_subst t)
    | VisF _ e h => Vis e (fun x => _subst (h x))
    | ProbF _ μ h => Prob μ (fun x => _subst (h x))
    end.

Definition bind {E M T U} (u : ptree E M T) (k : T -> ptree E M U)
  : ptree E M U := subst k u.

Definition cat {E M T U V} (k : T -> ptree E M U) (h : U -> ptree E M V)
  : (T -> ptree E M V)
  := fun x => bind (k x) h.



(** Iteration *)

Notation on_left lr l t :=
  (match lr with
  | inl l => t
  | inr r => Ret r
  end) (only parsing).

Definition iter {E M R I} (step : I -> ptree E M (I + R))
  : I -> ptree E M R
  := cofix iter_ i := bind (step i) (fun lr =>
    on_left lr l (Tau (iter_ l))).



(** Functorial Mapping *)

Definition fmap {E M T U} (f : T -> U) : ptree E M T -> ptree E M U
  := fun u => bind u (fun x => ret (f x)).


(** trigger plain events *)

Definition trigger {E M} : E ~> ptree E M :=
  fun _ e => Vis e (fun x => Ret x).
Arguments trigger {E M T} _.

End PTree.



Module PTreeNotations.
Infix ">=>" := PTree.cat
  (at level 61, right associativity)
    : ptree_scope.
End PTreeNotations.



(** Instances *)

Global Instance Functor_ptree {E M} : Functor (ptree E M) := {|
  fmap := @PTree.fmap E M
|}.

(*| Instead of [pure := @Ret E], [ret := @Ret E], we eta-expand
    [pure] and [ret] to make the extracted code respect OCaml's
    value restriction.
|*)

Global Instance Applicative_ptree {E M} : Applicative (ptree E M) := {|
  pure := fun _ x => Ret x;
  ap   := fun _ _ f x =>
    PTree.bind f (fun f => PTree.bind x (fun x => Ret (f x)))
|}.

Global Instance Monad_ptree {E M} : Monad (ptree E M) := {|
  ret := @PTree.ret E M ;
  bind := @PTree.bind E M
|}.

Global Instance MonadIter_ptree {E M} : MonadIter (ptree E M) :=
  fun _ _ => PTree.iter.

Global Instance MonadTrigger_ptree {E M} : MonadTrigger E (ptree E M) :=
  @PTree.trigger E M.



(** Remove [Tau]s from the front of an [ptree].
  TODO: replace [Tau] with [M.return] of the representation.
  *)

Fixpoint burn (n : nat) {E M R} (t : ptree E M R) :=
  match n with
  | O => t
  | S n =>
    match observe t with
    | RetF r => Ret r
    | VisF _ e k => Vis e k
    | TauF t' => burn n t'
    | ProbF _ μ k => Prob μ k
    end
  end.



(** [ptree E M R] satisfies monad laws up to the
    TODO: complete this monad laws with specific *)
Section MonadLaws.

Context {E : Type -> Type}.
Context {M : Type -> Type}.
Context {R : Type}.
Context `{Monad M}.

Instance Eq1_PTree : Eq1 (ptree E M) :=
  fun _ => eq.

Instance MonadLaws_PTree : MonadLawsE (ptree E M).
Proof. Admitted.

End MonadLaws.



(** probabilistic operations *)
Section prob.
Import Enum.

Definition meas {E} {X : eqType} (μ : Enum X) : ptree E Enum X
  := Prob μ ret.

Definition kernel {E} {X Y : eqType} (k : X -> Enum Y)
  : (X -> ptree E Enum Y)
  := fun x => meas (k x).



(** SampleE *)
Variant sampleE : eqType -> Type :=
| Sample {A : eqType} : Enum A -> sampleE A.

Definition handle_sample {E} {R : eqType} (e : sampleE R)
  : ptree E Enum R :=
  match e with
  | Sample _ μ => meas μ
  end.

End prob.





(** stuck trees *)
Section stuck.
Context {E M : Type -> Type}.
Context `{Monad M}.
Context `{MonadMeasure M}.
(** Thus M is a valid Inference Representation *)

Definition stuckE (e : E void) : ptree E M void
  := PTree.trigger e.

Definition stuckM {R} (u : ptree E M R) : ptree E M R
  := Prob (score 0) (fun _ => u).

End stuck.



Section spinning.
Context {E M : Type -> Type}.

End spinning.
