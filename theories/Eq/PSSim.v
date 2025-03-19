(** Probabilistic Strong Simulation Relation *)

Require Import Reals.
Require Import Program Morphisms.
Require Import ssrbool.

From Coinduction Require Import all.

From RelationAlgebra Require Import rel srel.

From PTree.Core Require Import PTreeDefinitionPa Utils.
From PTree.Prob Require Import Discrete.
From PTree.Eq Require Import Shallow Equ Trans.



Section PSSim.
Import List.
Import ListNotations.
#[local] Open Scope list_scope.
Import Enum.

#[local] Notation ptree E := (ptree E Enum).

Definition reflects (x : bool) (P : Prop) : Prop :=
  (x = true <-> P) /\ (x = false <-> ~ P).

Notation "'[' x '`reflects`' P ']'" := (reflects x P).

Fixpoint transAll {E X} α (t : ptree E X)
  (tlist : list (ℝ₊ * ptree E X)) : Prop :=
  match tlist with
  | [] => True
  | (p, t') :: tlist' => transR α p t t' /\ transAll α t tlist'
  end.

Fixpoint transAllPrb {E X} (tlist : list (ℝ₊ * ptree E X)) : ℝ₊ :=
  match tlist with
  | [] => 0%R
  | (p, t') :: tlist' => p + transAllPrb tlist'
  end.

Fixpoint relateAll {X Y} (R : rel X Y) (x : X) (ys : list Y) : Prop :=
  match ys with
  | [] => True
  | y :: ys' => R x y /\ relateAll R x ys'
  end.


(* exists f : ptree E X -> ptree E Y -> bool, *)
(*         (forall x y, [ f x y `reflects` R x y ]) *)

#[program] Definition pss {E F M N : Type -> Type}
    {X Y : Type} (L : rel (@label E) (@label F))
  : mon (ptree E X -> ptree F Y -> Prop)
  := {| body R t u := forall l p t', trans l p t t' ->
          exists l' (u's : list (ℝ₊ * ptree F Y)), (* issue: how no dup *)
            transAll l' u u's
            /\ (p <= (transAllPrb u's))%R
            /\ relateAll R t' (map snd u's)
            /\ L l l' |}.
Next Obligation.
  rename x into R1. rename y into R2.

Admitted.



End PSSim.
