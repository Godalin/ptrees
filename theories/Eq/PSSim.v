(** Probabilistic Strong Simulation Relation *)
Set Warnings "-ambiguous-paths".
Unset Universe Checking.

Require Import Utf8.
Require Import Program Morphisms.

From Coinduction Require Import all.
From RelationAlgebra Require Import rel srel.
From mathcomp Require Import ssreflect ssrbool eqtype seq finset ssralg order.

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
  | (p, t') :: tlist' => transR α p t t' ∧ transAll α t tlist'
  end.

Fixpoint transAllPrb {E X} (tlist : Enum (ptree E X)) : ℚ≥0 :=
  match tlist with
  | [::] => 0
  | (p, t') :: tlist' => p + transAllPrb tlist'
  end.

Fixpoint relateAll {X Y} (R : rel X Y) (x : X) (ys : list Y) : Prop :=
  match ys with
  | [::] => True
  | y :: ys' => R x y /\ relateAll R x ys'
  end.

Lemma sub_relateAll {X Y} (R S : rel X Y) (x : X) (ys : list Y)
  : (∀ x y, R x y → S x y) → relateAll R x ys → relateAll S x ys.
Proof. elim: ys => [//|y ys IH //= H] [Hxy Hxys]. auto. Qed.



(* Old definition of [pss], probabilistic strong simulation.
  This version has the problem of not being unique in the provided
  [seq] of [weight * ptree]. *)

(* #[program] *)
(* Definition pss' {E F : Type → Type} *)
(*     {X Y : Type} (L : rel (@label E) (@label F)) *)
(*   : mon (ptree E X → ptree F Y → Prop) *)
(*   := {| body R t u := ∀ l p t', *)
(*         trans l p t t' → *)
(*           ∃ l' (u's : list (ℚ≥0 * ptree F Y)), *)
(*             transAll l' u u's *)
(*             ∧ p <= (transAllPrb u's) *)
(*             ∧ relateAll R t' (map snd u's) *)
(*             ∧ L l l' |}. *)
(* Next Obligation. *)
(* Admitted. *)



#[program]
Definition pss {E F : Type → Type}
    {X Y : Type} (L : rel (@label E) (@label F))
  : mon (ptree E X → ptree F Y → Prop)
  := {| body R t u := ∀ l p t',
        trans l p t t' →
          ∃ l' (X' : eqType) (k' : X' → ℚ≥0 * ptree F Y) (x's : seq X'),
            uniq x's
            ∧ let u's := [seq k' x | x <- x's] in
              transAll l' u u's
              ∧ p <= (transAllPrb u's)
              ∧ relateAll R t' (map snd u's)
              ∧ L l l' |}.
Next Obligation.
move: (H0 l p t' H1) =>
  [l' [X' [k' [x's [Huniq [Htrans [Hprob [Hrelate HL]]]]]]]].
exists l', X', k', x's. repeat (split; auto).
apply: sub_relateAll. apply H. auto.
Defined.



End PSSim.
