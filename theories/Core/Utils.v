Set Warnings "-warn-library-file-stdlib-vector".
From Coq Require Import Fin.



Notation fin := Fin.t.

Polymorphic Class MonadTrigger (E : Type -> Type) (M : Type -> Type) : Type :=
  mtrigger : forall X, E X -> M X.

Polymorphic Class MonadBr (M : Type -> Type) : Type :=
  mbr : forall (b : bool) (n: nat), M (Fin.t n).

Notation rel X Y := (X -> Y -> Prop).



Ltac invert :=
  match goal with
  | h : existT _ _ _ = existT _ _ _ |- _ => dependent induction h
  end.

Ltac copy h :=
  let foo := fresh "cpy" in
  assert (foo := h).

Ltac break :=
  repeat match goal with
         | h : _ \/ _  |- _ => destruct h
         | h : _ /\ _  |- _ => destruct h
         | h : exists x, _ |- _ => destruct h
         end.
