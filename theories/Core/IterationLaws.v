(** Pure-map uniformity for a monadic iteration operator. This is an explicit
    algebraic premise, not an instance, probability capability, or assertion
    about a particular PTree interpreter. MonadIter alone supplies no laws. *)
Set Universe Polymorphism.
From ExtLib.Structures Require Import Monad.
From ITree.Basics Require Import Basics Monad.
Set Implicit Arguments.
Unset Strict Implicit.
Local Open Scope type_scope.

Definition iteration_map {I J A} (h : I -> J) (v : I + A) : J + A :=
  match v with inl i => inl (h i) | inr a => inr a end.

Definition iteration_uniform {T : Type -> Type}
    `{MT : Monad T} `{IT : MonadIter T} `{QT : Eq1 T} : Prop :=
  forall (I J A : Type) (f : I -> T (I + A)) (g : J -> T (J + A))
    (h : I -> J),
    (forall i, eq1 (bind (f i) (fun v => ret (iteration_map h v))) (g (h i))) ->
    forall i, eq1 (iter f i) (iter g (h i)).
