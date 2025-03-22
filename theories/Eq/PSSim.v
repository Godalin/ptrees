(** Probabilistic Strong Simulation Relation *)
Set Warnings "-ambiguous-paths".
Unset Universe Checking.

Require Import Program Morphisms.

From Coinduction Require Import all.
From RelationAlgebra Require Import rel srel.
From mathcomp Require Import ssrbool seq ssralg order.

From PTree.Core Require Import PTreeDefinitionNew Utils.
From PTree.Prob Require Import RatSubTypes DiscreteMC.
From PTree.Eq Require Import ShallowNew EquNew Trans.



Section PSSim.
Import Enum.
Import NonnegQNotations.

#[local] Notation ptree E := (ptree E Enum).

Fixpoint transAll {E X} α (t : ptree E X)
    (tlist : list (ℚ≥0 * ptree E X)) : Prop :=
  match tlist with
  | [::] => True
  | (p, t') :: tlist' => transR α p t t' /\ transAll α t tlist'
  end.

Fixpoint transAllPrb {E X} (tlist : list (ℚ≥0 * ptree E X)) : ℚ≥0 :=
  match tlist with
  | [::] => 0
  | (p, t') :: tlist' => p + transAllPrb tlist'
  end.

Fixpoint relateAll {X Y} (R : rel X Y) (x : X) (ys : list Y) : Prop :=
  match ys with
  | [::] => True
  | y :: ys' => R x y /\ relateAll R x ys'
  end.



#[program]
Definition pss {E F M N : Type -> Type}
    {X Y : Type} (L : rel (@label E) (@label F))
  : mon (ptree E X -> ptree F Y -> Prop)
  := {| body R t u := forall l p t', trans l p t t' ->
          exists l' (u's : list (ℚ≥0 * ptree F Y)),
            transAll l' u u's
            /\ p <= (transAllPrb u's)
            /\ relateAll R t' (map snd u's)
            /\ L l l' |}.
Next Obligation.
  rename x into R1. rename y into R2.

Admitted.



End PSSim.
