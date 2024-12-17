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

From ExtLib Require Import
     Structures.Functor
     Structures.Monads.

From ITree Require Import
     Basics.Basics
     Core.Subevent
     Indexed.Sum.

From ProbAx Require Import integration.
Check Meas.



Set Primitive Projections.

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

Variant ptreeF (ptree : Type) : Type :=
| RetF  (r : R)
| Tau   (e : ptree)
| VisF  {X} (e : E X) (k : X -> ptree)
| ProbF {X} (μ : Meas X) (k : X -> ptree)
.
(* | SRetF {d} {R : measurableType d} (μ : measure R ℝ) *)
(* | ProbCPS {X d} {R : measurableType d} (e : E X) (k : X -> probability R ℝ) *)

CoInductive ptree : Type :=
  go { _observe : ptreeF ptree }.

End ptree.



Declare Scope ptree_scope.
Bind Scope ptree_scope with ptree.
Delimit Scope ptree_scope with ptree.
Local Open Scope ptree_scope.

Arguments ptree _ _ : clear implicits.
Arguments ptreeF _ _ : clear implicits.

