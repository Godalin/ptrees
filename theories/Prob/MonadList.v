Require Import List.
Import ListNotations.

From ExtLib Require Import Structures.Functor.
From ExtLib Require Import Structures.Monad.
Import MonadNotation.
Import MonadLetNotation.

Definition list_ret {A} (a : A) : list A := [a].

Definition list_bind {A B} (xs : list A) (f : A -> list B) : list B :=
  fold_right (fun x ys => f x ++ ys) [] xs.

Global Instance MonadList : Monad list :=
  { ret := @list_ret
  ; bind := @list_bind
  }.



(* The notorious list monad transformer *)

(* Section ListTR.
Context (m : Type -> Type).
Context `{M : Monad m}.

Definition listTR (m : Type -> Type) (A : Type) : Type :=
  m (list A).

Definition listTR_ret {A} (a : A) : listTR m A := ret [a].

Definition listTR_bind {A B} (x : listTR m A) (f : A -> listTR m B) : listTR m B :=
  bind x (fun xs => ret (concat (map f xs))).

End ListTR. *)



(* The correct list monad transformer, with the co-Yoneda encoding *)

Inductive mlist (m : Type -> Type) (A : Type) : Type :=
| mnil
| mcons (a : A) {X : Type} (mx : m X) (k : X -> mlist m A).

Record listT (m : Type -> Type) (A : Type) :=
  mkListT { runListT : m (mlist m A) }.


(* Notation listT := (mlist). *)

Arguments mnil {m A}.
Arguments mcons {m A} _ {X} _.
Arguments mkListT {m A} _.
Arguments runListT {m A} _.



Section MList.

Context {m : Type -> Type}.
Context {M : Monad m}.

Definition mNil {A : Type} : m (mlist m A) := ret mnil.
Definition mCons {A : Type} (a : A) (mml : m (mlist m A)) :=
  bind mml (fun ml => ret (mcons a (ret tt) (fun _ => ml))).

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

Fixpoint sum_all' (x : mlist option nat) : option nat :=
  match x with
  | mnil => ret 0
  | mcons a mx k => bind mx (fun x => bind (sum_all' (k x)) (fun n => ret (a + n)))
  end.

Definition sum_all (mml : option (mlist option nat)) : option nat :=
  bind mml (fun ml => sum_all' ml).

Compute sum_all mNil.
Compute sum_all (mCons 1 (mCons 2 mNil)).
Compute sum_all (mCons 1 (mCons 2 (mCons 3 None))).
Compute sum_all (mCons 1 (mCons 2 (mCons 3 mNil))).

End example.



(* Definition mCons_original {A m} `{Monad m} (a : A) (mml : m (mlist m A)) :=
  bind mml (fun ml => ret (mcons a (ret tt) (fun _ => ml))). *)

Section MListMonad.

Context {m : Type -> Type}.
Context {M : Monad m}.

Fixpoint lift_list {A} (l : list A) : m (mlist m A) :=
  match l with
  | [] => mNil
  | a :: l' => mCons a (lift_list l')
  end.

Compute lift_list [1; 2; 3].

Fixpoint mmap {A B} (f : A -> B) (xs : mlist m A) : mlist m B :=
  match xs with
  | mnil => mnil
  | mcons a mx k => mcons (f a) mx (fun x => mmap f (k x))
  end.

Fixpoint mappend' {A} (xs : mlist m A) (ys : m (mlist m A)) : m (mlist m A) :=
  match xs with
  | mnil => ys
  | mcons a mx k => bind mx (fun x => (mappend' (k x) ys))
  end.

Definition mappend {A} (mxs : m (mlist m A)) (mys : m (mlist m A)) : m (mlist m A) :=
  bind mxs (fun xs => mappend' xs mys).

Fixpoint mjoin' {A} (mml : mlist m (m (mlist m A))) : m (mlist m A) :=
  match mml with
  | mnil => mNil
  | mcons mas mx k => mappend mas (bind mx (fun x => (mjoin' (k x))))
  end.

Definition mjoin {A} (mml : m (mlist m (m (mlist m A)))) : m (mlist m A) :=
  bind mml (fun ml => mjoin' ml).



Definition mlist_ret {A} (a : A) : m (mlist m A) := mCons a mNil.
Definition mlist_bind {A B} (ma : m (mlist m A)) (f : A -> m (mlist m B)) : m (mlist m B) :=
  mjoin (bind ma (fun ml => ret (mmap f ml))).

Global Instance MonadmlistT : Monad (fun a => m (mlist m a)) :=
  { ret := @mlist_ret
  ; bind := @mlist_bind
  }.



Definition listT_ret {A} (a : A) : listT m A := mkListT (mCons a mNil).
Definition listT_bind {A B} (x : listT m A) (f : A -> listT m B) : listT m B :=
  mkListT (mjoin (bind (runListT x) (fun ml => ret (mmap (fun a => runListT (f a)) ml)))).

Global Instance MonadListT : Monad (listT m) :=
  { ret := @listT_ret
  ; bind := @listT_bind
  }.

End MListMonad.
