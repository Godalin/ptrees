Require Import List.
Import ListNotations.

From ExtLib Require Import Structures.Functor.
From ExtLib Require Import Structures.Monad.
Import MonadNotation.

Global Instance MonadList : Monad list :=
  { ret := fun A x => [x]
  ; bind := fun A B x f => flat_map f x
  }.



(* Inductive mlist (m : Type -> Type) (A : Type) : Type :=
| mnil
| mcons (a : A) {X : Type} (mx : m X) (k : X -> mlist m A).

Record listT (m : Type -> Type) (A : Type) :=
  mkListT { runListT : m (mlist m A) }. *)


(* co-Yoneda encoding of monads *)
Inductive mlist (m : Type -> Type) (A : Type) : Type :=
| mkmlist {X : Type} (mx : m X) (k : X -> (mlist' m A))

with mlist' (m : Type -> Type) (A : Type) : Type :=
| mnil
| mcons (a : A) (ml : mlist m A).

(* Notation listT := (mlist). *)

Arguments mkmlist {m A X} _ _.
Arguments mnil {m A}.
Arguments mcons {m A} _ _.





Section MList.
Context {m : Type -> Type}.
Context {M : Monad m}.

Definition mNil {A : Type} : mlist m A :=
  mkmlist (ret tt) (fun _ => mnil).
Definition mCons {A : Type} (a : A) (mml : mlist m A) : mlist m A :=
  match mml with
  | mkmlist u k => mkmlist u (fun x => mcons a (mkmlist (ret tt) (fun _ => k x)))
  end.

End MList.



Section example.
Check option.
Global Instance MonadOption : Monad option := {|
  ret := fun A x => Some x ;
  bind := fun A B x f => match x with
    | None => None
    | Some y => f y
    end
  |}.

Fixpoint sum_all (x : mlist option nat) : option nat :=
  match x with
  | mkmlist mx k => bind mx (fun x => (sum_all' (k x)))
  end
with sum_all' (x : mlist' option nat) : option nat :=
  match x with
  | mnil => ret 0
  | mcons a ml => bind (sum_all ml) (fun n => ret (a + n))
  end.

Compute sum_all mNil.
Compute sum_all (mCons 1 (mCons 2 mNil)).
Compute sum_all (mCons 1 (mCons 2 (mCons 3 (mkmlist None _)))).
Compute sum_all (mCons 1 (mCons 2 (mCons 3 mNil))).

End example.


(* Definition mCons_original {A m} `{Monad m} (a : A) (mml : m (mlist m A)) :=
  bind mml (fun ml => ret (mcons a (ret tt) (fun _ => ml))). *)

Section MListMonad.
Context {m : Type -> Type}.
Context {M : Monad m}.

Fixpoint lift_list {A} (l : list A) : mlist m A :=
  match l with
  | [] => mNil
  | a :: l' => mCons a (lift_list l')
  end.

Compute lift_list [1; 2; 3].

Fixpoint mlist_fmap {A B} (f : A -> B) (ma : mlist m A) : mlist m B :=
  match ma with
  | mkmlist mx k => mkmlist mx (fun x => match k x with
    | mnil => mnil
    | mcons a ml => mcons (f a) (mlist_fmap f ml)
    end)
  end.

Global Instance FunctorMList : Functor (mlist m) :=
  { fmap := @mlist_fmap
  }.



(* Fixpoint mappend {A} (xs : mlist m A) (ys : mlist m A) : mlist m A :=
  match xs with
  | mkmlist mx k => bind (Monad := M) mx (fun x => mkmlist (ret x) (fun _ => mappend' (k x) ys))
  end
with mappend' {A} (xs : mlist' m A) (ys : mlist m A) : mlist m A :=
  match xs with
  | mnil => ys
  | mcons a mtl => mCons a (mappend mtl ys)
  end.

Definition ListT_ret {A} (a : A) : mlist m A := mCons a mNil.
Fixpoint ListT_bind {A B} (x : mlist m A) (f : A -> mlist m B) : mlist m B := _.

Global Instance MonadListT : Monad (listT m) :=
  { ret := @ListT_ret
  ; bind := @ListT_bind
  }. *)

End MListMonad.
