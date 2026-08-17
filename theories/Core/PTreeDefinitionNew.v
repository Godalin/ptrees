(** This file formalizes the probability tree: PTree, as an
    negative coinductive type.

    The most interesting part of this formalization lies in
    the fact that, with the constructor [Prob], we can create
    a stochastic choice with some weight provided by the [measure]
    construct. *)

Require Import Program.
Require Import Utf8.

From ExtLib Require Import Structures.Functor.
From ExtLib Require Import Structures.Applicative.
From ExtLib Require Import Structures.Monads.

From ITree.Basics Require Import Basics.
From ITree.Basics Require Import Monad.
From ITree.Core Require Import Subevent.
From ITree.Indexed Require Import Sum.
From ITree Require Eq.

From mathcomp Require Import eqtype seq.
From mathcomp Require Import ssreflect ssrbool.

From PTree.Core Require Import Utils.
From PTree.Prob Require Import Monad.

Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.



Section ptree.

Context {E : Type -> Type}.
Context {M : Type -> Type}.
Context {R : Type}.

Variant ptreeF {ptree : Type} : Type :=
| RetF (r : R)
| TauF (e : ptree)
| VisF {X} (e : E X) (k : X -> ptree)
| ProbF {X : Type} (μ : M X) (k : X -> ptree).

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

Definition ProbF0 {E : Type -> Type} {M : Type -> Type} {R : Type}
    (μ : M void) (k : void -> ptree E M R)
  : ptree' E M R :=
    ProbF μ k.

Definition Prob0 {E : Type -> Type} {M : Type -> Type} {R : Type}
    (μ : M void) (k : void -> ptree E M R)
  : ptree E M R :=
    Prob μ k.

Definition IsProbF {E M R} (p: ptree' E M R) : bool := match p with
| RetF r => false
| TauF t => false
| VisF _ e h => false
| ProbF _ μ h => true
end.

Theorem IsProbF_ex_ProbF {E M R} {p: ptree' E M R}
    (is_prob : IsProbF p = true) :
  exists (X : Type) (mu : M X) (k : X -> ptree E M R),
    p = ProbF mu k.
  destruct p; rewrite //= in is_prob.
  exists X, μ, k. reflexivity.
Qed.

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

(** Interpret visible events with a PTree handler.  The administrative
    [Tau] on the visible branch makes the corecursion syntactically guarded;
    it is intentionally invisible to the canonical weak equivalence. *)
CoFixpoint interp {E F M} (handler : E ~> ptree F M) {R}
    (t : ptree E M R) : ptree F M R :=
    match observe t with
    | RetF r => Ret r
    | TauF t' => Tau (interp handler t')
    | @VisF _ _ _ _ X e k =>
        Tau (bind (handler _ e) (fun x => interp handler (k x)))
    | @ProbF _ _ _ _ X mu k => Prob mu (fun x => interp handler (k x))
    end.

(** Event renaming is the pure-handler instance of [interp]. *)
Definition translate {E F M} (f : E ~> F) {R}
    (t : ptree E M R) : ptree F M R :=
  interp (fun _ e => @trigger F M _ (f _ e)) t.

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



(** Monad laws for coinductive trees do not hold under Coq's intensional
    equality: for example, [bind t Ret] is generally only bisimilar to [t].
    The former [Eq1 := eq] / admitted [MonadLawsE] instance was therefore
    unsound and has been removed.  Clients should state these laws using the
    maintained coinductive relations ([equ], [pstrong], or the appropriate
    weak probabilistic equivalence). *)



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
