From ExtLib Require Import
     Structures.Functor
     Structures.Monads.

From ITree Require Import
     Basics.Basics
     Core.Subevent
     Indexed.Sum.

Section ptree.

  Context {E : Type -> Type} {B : Type -> Type} {R : Type}.

  Variant ptreeF (ptree : Type) : Type :=
    | RetF (r : R)
    | VisF {X : Type} (e : E X) (k : X -> ptree)
    | PrbF  (vis : bool) {X : Type} (c : B X) (k : X -> ptree).

  CoInductive ptree : Type :=
    go { _observe : ptreeF ptree }.

End ptree.


Declare Scope ptree_scope.
Bind Scope ptree_scope with ptree.
Delimit Scope ptree_scope with ptree.
Local Open Scope ptree_scope.

Arguments ptree _ _ : clear implicits.
Arguments ptreeF _ _ : clear implicits.
Arguments PrbF {E B R} [ptree] vis {X} c k.
