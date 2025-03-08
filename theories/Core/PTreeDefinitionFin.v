(*|
This file formalize the probability tree: PTree, as an
negative coinductive type.

The most interesting part of this formalization lies in
the fact that, with the constructor [Prob], we can create
a stochastic choice with some weight provided by the [measure]
construct.
|*)

Set Warnings "-notation-overridden".
(* Set Warnings "-notation-incompatible-prefix". *)



From Coq Require Import Program.

From ExtLib Require Import Structures.Functor.
From ExtLib Require Import Structures.Applicative.
From ExtLib Require Import Structures.Monads.

From ITree Require Import
     Basics.Basics
     Core.Subevent
     Indexed.Sum.

From PTree.Core Require Import Utils.
From PTree.Prob Require Import FinSupp.



Set Primitive Projections.



Section ptree.

Context {E : Type -> Type} {R : Type}.


Variant ptreeF {ptree : Type} : Type :=
| RetF  (r : R)
| TauF  (e : ptree)
| VisF  {X} (e : E X) (k : X -> ptree)
| ProbF {X} (μ : finSupp X) (k : X -> ptree).

CoInductive ptree : Type :=
  go { _observe : @ptreeF ptree }.

End ptree.



Declare Scope ptree_scope.
Bind Scope ptree_scope with ptree.
Delimit Scope ptree_scope with ptree.
Local Open Scope ptree_scope.

Arguments ptree _ _ : clear implicits.
Arguments ptreeF _ _ : clear implicits.



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
Notation Prob μ k := (go (ProbF μ k)).



(*| Main Operations for PTrees. |*)

Module PTree.

(*| Monadic Operations |*)
Import MonadNotation.

Definition ret {E R} (r : R) : ptree E R
  := Ret r.

Definition subst {E T U} (k : T -> ptree E U)
  : ptree E T -> ptree E U :=
  cofix _subst (u : ptree E T) :=
    match observe u with
    | RetF r => k r
    | TauF t => Tau (_subst t)
    | VisF e h => Vis e (fun x => _subst (h x))
    | ProbF μ h => Prob μ (fun x => _subst (h x))
    end.

Definition bind {E T U} (u : ptree E T) (k : T -> ptree E U)
  : ptree E U := subst k u.

Definition cat {E T U V} (k : T -> ptree E U) (h : U -> ptree E V)
  : (T -> ptree E V)
  := fun x => bind (k x) h.



(*| Iteration |*)

CoFixpoint iter {E R I} (step : I -> ptree E (I + R)) (i : I)
  : ptree E R :=
    bind (step i) (fun lr => match lr with
      | inr r => ret r
      | inl l => Tau (iter step l)
      end).



(*| Functorial Mapping |*)

Definition fmap {E T U} (f : T -> U) : ptree E T -> ptree E U
  := fun u => bind u (fun x => ret (f x)).


(*| trigger |*)

Definition trigger {E} : E ~> ptree E :=
  fun _ e => Vis e (fun x => Ret x).
Arguments trigger {E} {T} _.
Check trigger.

End PTree.



Module PTreeNotations.
Infix ">=>" := PTree.cat
  (at level 61, right associativity)
    : ptree_scope.
End PTreeNotations.



(*| Instances |*)

Global Instance Functor_ptree {E} : Functor (ptree E) := {|
  fmap := @PTree.fmap E 
|}.

(*| Instead of [pure := @Ret E], [ret := @Ret E], we eta-expand
    [pure] and [ret] to make the extracted code respect OCaml's
    value restriction.
|*)

Global Instance Applicative_ptree {E} : Applicative (ptree E) := {|
  pure := fun _ x => Ret x;
  ap   := fun _ _ f x =>
    PTree.bind f (fun f => PTree.bind x (fun x => Ret (f x)))
|}.

Global Instance Monad_ptree {E} : Monad (ptree E) := {|
  ret := fun _ x => Ret x;
  bind := @PTree.bind E
|}.

Global Instance MonadIter_ptree {E} : MonadIter (ptree E) :=
  fun _ _ => PTree.iter.

Global Instance MonadTrigger_ptree {E} : MonadTrigger E (ptree E) :=
  @PTree.trigger _.



(*| Remove [Tau]s from the front of an [itree]. |*)

Fixpoint burn (n : nat) {E R} (t : ptree E R) :=
  match n with
  | O => t
  | S n =>
    match observe t with
    | RetF r => Ret r
    | VisF e k => Vis e k
    | TauF t' => burn n t'
    | ProbF μ k => Prob μ k
    end
  end.



(*| probabilistic operations |*)

Definition meas {E X} (μ : finSupp X) : ptree E X
  := Prob μ ret.

(* Definition kernel {E X Y} (k : Kernel X Y) : (X -> ptree E Y)
  := fun x => meas (k x). *)





(*| SampleE |*)

Variant sampleE : Type -> Type :=
| Sample {A} : finSupp A -> sampleE A.

Definition handle_sample {E R} (e : sampleE R) : ptree E R :=
  match e with
  | Sample μ => meas μ
  end.



(* stuck trees *)
Section stuck.
Variable E : Type -> Type.
Definition stuckE (e : E void) : ptree E void := PTree.trigger e.
Definition stuckM : ptree E void := meas pEmpty.
End stuck.
