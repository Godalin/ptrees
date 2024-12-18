(*|
This file formalize the probability tree: PTree, as an
negative coinductive type.

The most interesting part of this formalization lies in
the fact that, with the constructor [Prob], we can create
a stochastic choice with some weight provided by the [measure]
construct.
|*)

Set Primitive Projections.

From Coq Require Import Program.

From ExtLib Require Import
     Structures.Functor
     Structures.Applicative
     Structures.Monads.

From ITree Require Import
     Basics.Basics
     Core.Subevent
     Indexed.Sum.

From ProbAx Require Import
     ennr
     integration.

Open Scope ennr.
Check Meas.



Section ptree.
Context {E : Type -> Type} {R : Type}.

(*|

How to design the constructors:

probabilistic choice after a computation
_ (eμ : E (measure X ℝ)) (k : X -> ptree)

internal probabilistic choice
_ (μ : measure X ℝ) (k : X -> ptree)

internal nondeterministic choice
_ (fin n -> ptree)

_ (e : E X) (X ~~> ptree)

|*)

Variant ptreeF {ptree : Type} : Type :=
| RetF (r : R)
| TauF (e : ptree)
| VisF {X} (e : E X) (k : X -> ptree)
| PrbF {X} (μ : Meas X) (k : X -> ptree)
.
(* | SRetF {d} {R : measurableType d} (μ : measure R ℝ) *)
(* | ProbCPS {X d} {R : measurableType d} (e : E X) (k : X -> probability R ℝ) *)

CoInductive ptree : Type :=
  go { _observe : @ptreeF ptree }.

End ptree.



Declare Scope ptree_scope.
Bind Scope ptree_scope with ptree.
Delimit Scope ptree_scope with ptree.
Local Open Scope ptree_scope.

Arguments ptree _ _ : clear implicits.
Arguments ptreeF _ _ : clear implicits.

Check ptree.
Check ptreeF.



Notation ptree' E R := (ptreeF E R (ptree E R)).

Definition observe {E R} (t : ptree E R) : ptree' E R :=
  @_observe E R t.

Check observe.



(*|
Notations for constructors of PTrees.
|*)

Notation Ret x   := (go (RetF x)).
Notation Vis e k := (go (VisF e k)).
Notation Tau e   := (go (TauF e)).
Notation Prb μ k := (go (PrbF μ k)).



(*| Main Operations for PTrees. |*)

Module PTree.

(*| Monadic Operations |*)

Definition ret {E R} (r : R) : ptree E R
  := Ret r.

Definition subst {E T U} (k : T -> ptree E U) : ptree E T -> ptree E U :=
  cofix _subst (u : ptree E T) :=
    match observe u with
    | RetF r => k r
    | TauF t => Tau (_subst t)
    | VisF e h => Vis e (fun x => _subst (h x))
    | PrbF μ h => Prb μ (fun x => _subst (h x))
    end.

Definition bind {E T U} (u : ptree E T) (k : T -> ptree E U)
  : ptree E U := subst k u.

Definition cat {E T U V} (k : T -> ptree E U) (h : U -> ptree E V)
  : (T -> ptree E V)
  := fun x => bind (k x) h.

(* Functorial Mapping *)

Definition fmap {E T U} (f : T -> U) : ptree E T -> ptree E U
  := fun u => bind u (fun x => ret (f x)).



(*| Iteration |*)

Notation on_left lr l t :=
  (match lr with
  | inl l => t
  | inr r => Ret r
  end) (only parsing).

Definition iter {E : Type -> Type} {R I: Type}
           (step : I -> ptree E (I + R)) : I -> ptree E R :=
  cofix iter_ i := bind (step i) (fun lr => on_left lr l (Tau (iter_ l))).

End PTree.



Module PTreeNotations.
Notation "t1 >>= k2" := (PTree.bind t1 k2).
Notation "x <- t1 ;; t2" := (PTree.bind t1 (fun x => t2))
  (at level 61, t1 at next level, right associativity) : ptree_scope.
Notation "t1 ;; t2" := (PTree.bind t1 (fun _ => t2))
  (at level 61, right associativity) : ptree_scope.
Notation "' p <- t1 ;; t2" :=
  (PTree.bind t1 (fun x_ => match x_ with p => t2 end))
  (at level 61, t1 at next level, p pattern, right associativity)
    : ptree_scope.
Infix ">=>" := PTree.cat
  (at level 61, right associativity)
    : ptree_scope.
End PTreeNotations.



(*| Instances |*)

#[global] Instance Functor_itree {E} : Functor (ptree E) := {|
  fmap := @PTree.fmap E 
|}.

(* Instead of [pure := @Ret E], [ret := @Ret E], we eta-expand
   [pure] and [ret] to make the extracted code respect OCaml's
   value restriction. *)
#[global]
Instance Applicative_itree {E} : Applicative (ptree E) := {|
  pure := fun _ x => Ret x;
  ap   := fun _ _ f x =>
    PTree.bind f (fun f => PTree.bind x (fun x => Ret (f x)))
|}.

#[global]
Instance Monad_itree {E} : Monad (ptree E) := {|
  ret := fun _ x => Ret x;
  bind := @PTree.bind E
|}.

(* #[global] Instance MonadIter_itree {E} : MonadIter (ptree E) :=
  fun _ _ => ITree.iter. *)



(*| Remove [Tau]s from the front of an [itree].
|*)
Fixpoint burn (n : nat) {E R} (t : ptree E R) :=
  match n with
  | O => t
  | S n =>
    match observe t with
    | RetF r => Ret r
    | VisF e k => Vis e k
    | TauF t' => burn n t'
    | PrbF μ k => Prb μ k
    end
  end.
