(** Pure handler combinators. No probability interpretation, equivalence,
    or backend is selected here. Composition reads left-to-right. *)
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From ITree.Indexed Require Import Sum.
From PTree.Core Require Import PTreeDefinition.
Set Implicit Arguments.
Unset Strict Implicit.

Definition Handler (MN E F : Type -> Type) := forall X, E X -> ptree F MN X.

Definition id_ {MN E} : Handler MN E E := fun X e => PTree.trigger e.

Definition cat {MN E F G} (h : Handler MN E F) (g : Handler MN F G) :
    Handler MN E G := fun X e => PTree.interp g (h X e).

Definition case_ {MN E F G} (h : Handler MN E G) (g : Handler MN F G) :
    Handler MN (E +' F) G :=
  fun X e => match e with inl1 e => h _ e | inr1 e => g _ e end.

Definition inl_ {MN E F} : Handler MN E (E +' F) :=
  fun X e => PTree.trigger (inl1 e).
Definition inr_ {MN E F} : Handler MN F (E +' F) :=
  fun X e => PTree.trigger (inr1 e).

Definition bimap {MN E1 E2 F1 F2}
    (h : Handler MN E1 F1) (g : Handler MN E2 F2) :
    Handler MN (E1 +' E2) (F1 +' F2) :=
  case_ (cat h inl_) (cat g inr_).

Definition empty {MN F} : Handler MN void1 F :=
  fun X e => match e with end.
