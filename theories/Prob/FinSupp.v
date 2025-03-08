From Coq Require Import Reals.
From Coq Require Import List.
Import ListNotations.

From ExtLib Require Import Structures.Functor.
From ExtLib Require Import Structures.Monad.
From ExtLib Require Import Structures.MonadLaws.
From ExtLib Require Import Data.Monads.StateMonad.
Import MonadNotation.
Import MonadLetNotation.
Import MonadState.

Open Scope R.
Open Scope list_scope.
Open Scope monad_scope.



Section finSupp.

Record finSupp (A : Type) :=
  mkFinSupp { runFinSupp : list (A * R) }.

End finSupp.

Notation finKernel A B := (A -> finSupp B).

Arguments mkFinSupp {A} _.
Arguments runFinSupp {A} _.



Section finSuppMonad.

Definition finSupp_fmap {A B} (f : A -> B) (x : finSupp A) : finSupp B :=
  mkFinSupp (map (fun '(a, p) => (f a, p)) (runFinSupp x)).

Definition finSupp_ret {A} (a : A) : finSupp A :=
  mkFinSupp [(a, 1)].

Definition finSupp_bind {A B} (x : finSupp A) (f : A -> finSupp B) : finSupp B :=
  mkFinSupp (flat_map (fun '(a, p) => map (fun '(b, q) => (b, p * q)) (runFinSupp (f a))) (runFinSupp x)).

Global Instance Functor_finSupp : Functor finSupp :=
  { fmap := @finSupp_fmap
  }.

Global Instance Monad_finSupp : Monad finSupp :=
  { ret := @finSupp_ret
  ; bind := @finSupp_bind
  }.

End finSuppMonad.



Section finSuppT.

Context (m : Type -> Type).

Record finSuppT (A : Type) : Type :=
  mkFinSuppT { runFinSuppT : m (list (A * R)) }.

End finSuppT.

Arguments mkFinSuppT {m A} _.
Arguments runFinSuppT {m A} _.



Definition sequence {m : Type -> Type} `{M : Monad m}
  {A : Type} (l : list (m A))
  : m (list A) :=
  fold_right (fun x acc => bind x (fun a => fmap (fun l => a :: l) acc)) (ret []) l.



Section finSuppTMonad.

Context (m : Type -> Type).
Context (M : Monad m).
Context (A B : Type).

Definition finSuppT_fmap (f : A -> B) (x : finSuppT m A)
  : finSuppT m B
  := mkFinSuppT (fmap (fun l => map (fun '(a, p) => (f a, p)) l) (runFinSuppT x)).

Definition finSuppT_ret (a : A) : finSuppT m A
  := mkFinSuppT (ret [(a, 1)]).

(* Definition finSuppT_bind (x : finSuppT m A) (f : A -> finSuppT m B)
  : finSuppT m B
  := mkFinSuppT (
    bind (runFinSuppT x) (fun l =>
      let results := map (fun '(a, p) =>
        fmap (fun l' => map (fun '(b, q) => (b, p * q)%R) l') (runFinSuppT (f a))) l in
      sequence results
    )
  ). *)



(*
f : A -> finSuppT m B
x : finSupp A

fmap x f : finSupp (finSuppT m B)
fmap x (fun y => runFinSuppT (f y)) : finSupp (m (finSupp B))

 *)

End finSuppTMonad.



Definition integrate {A} (f : A -> R) (μ : finSupp A) : R :=
  fold_left (fun acc '(a, p) => acc + p * f a) (runFinSupp μ) 0.

Definition uniform {A} (l : list A) : finSupp A :=
  mkFinSupp (map (fun x => (x, 1 / INR (length l))) l).

Definition pChoice (p : R) {A : Type} (x : A) (y : A) : finSupp A :=
  mkFinSupp [(x, p); (y, 1 - p)].

Definition pEmpty {A : Type} : finSupp A := mkFinSupp [].



Fixpoint addF {A} (x : A) (eq : A -> A -> bool) (r : R) (μ : list (A * R)) : list (A * R) :=
  match μ with
  | [] => [(x, r)]
  | (y, p) :: μ' => if eq x y then (y, p + r) :: μ' else (y, p) :: addF x eq r μ'
  end.
