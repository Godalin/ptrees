(** Finite presentations by positions, not by distinct values.
    Every raw list entry gets its own ordinal, including zero weights and
    repeated values. Decoding restores the exact list. This module defines
    no semantic equality, lifting or coupling. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype tuple bigop ssralg ssrnum order.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section RawPresentation.
Context {W : Type}.

Definition finite_position {A : Type} (mu : list (W * A)) := 'I_(size mu).
Definition finite_position_entry {A} (mu : list (W * A)) (i : finite_position mu) :=
  tnth (in_tuple mu) i.
Arguments finite_position_entry {A} mu i.
Definition finite_position_weight {A} (mu : list (W * A)) (i : finite_position mu) :=
  (finite_position_entry mu i).1.
Definition finite_position_value {A} (mu : list (W * A)) (i : finite_position mu) :=
  (finite_position_entry mu i).2.
Arguments finite_position_weight {A} mu i.
Arguments finite_position_value {A} mu i.
Definition finite_positions {A} (mu : list (W * A)) : list (W * finite_position mu) :=
  [seq (finite_position_weight mu i, i) | i <- enum (finite_position mu)].

Lemma finite_positions_decode {A} (mu : list (W * A)) :
  [seq (px.1, finite_position_value mu px.2) | px <- finite_positions mu] = mu.
Proof.
  rewrite /finite_positions -map_comp.
  transitivity (map (tnth (in_tuple mu)) (enum 'I_(size mu))).
  - apply eq_map=> i. rewrite /=. unfold finite_position_weight, finite_position_value, finite_position_entry.
    by case: (tnth (in_tuple mu) i).
  - exact: map_tnth_enum.
Qed.

Lemma finite_position_entry_in {A} (mu : list (W * A)) (i : finite_position mu) :
  List.In (finite_position_entry mu i) mu.
Proof.
  have Hi : List.In i (enum (finite_position mu)).
  { have Hmem : i \in enum (finite_position mu) by rewrite mem_enum.
    elim: (enum (finite_position mu)) Hmem=> [|j js IH] //.
    rewrite in_cons=> /orP [/eqP ->|Hmem]; [by left|right; exact: IH]. }
  have H := List.in_map (tnth (in_tuple mu)) _ _ Hi.
  change (List.In (tnth (in_tuple mu) i)
    [seq tnth (in_tuple mu) j | j <- enum 'I_(size mu)]) in H.
  rewrite map_tnth_enum in H. exact H.
Qed.

Lemma finite_positions_size {A} (mu : list (W * A)) :
  size (finite_positions mu) = size mu.
Proof. by rewrite /finite_positions size_map -cardE card_ord. Qed.

Lemma finite_positions_indices {A} (mu : list (W * A)) :
  [seq px.2 | px <- finite_positions mu] = enum (finite_position mu).
Proof. by rewrite /finite_positions -map_comp; exact: map_id. Qed.
End RawPresentation.

Arguments finite_position_entry {W A} mu i.
Arguments finite_position_weight {W A} mu i.
Arguments finite_position_value {W A} mu i.
Arguments finite_position_entry_in {W A} mu i.

Section CheckedPresentation.
Variable R : numDomainType.

Lemma finite_positions_expect {A} (mu : list (R * A)) (f : A -> R) :
  finite_expect (fun i => f (finite_position_value mu i)) (finite_positions mu) =
  finite_expect f mu.
Proof.
  have Hd : List.map (fun px => (px.1, finite_position_value mu px.2))
      (finite_positions mu) = mu := finite_positions_decode mu.
  by rewrite -finite_expect_map Hd.
Qed.

Lemma finite_positions_nonnegative {A} (mu : list (R * A)) :
  finite_nonnegative mu -> finite_nonnegative (finite_positions mu).
Proof.
  move=> H p i Hin. apply List.in_map_iff in Hin.
  destruct Hin as [j [He Hj]]; inversion He; subst p i.
  have Hentry := finite_position_entry_in mu j.
  unfold finite_position_weight.
  destruct (finite_position_entry mu j) as [p x]; cbn.
  exact (H p x Hentry).
Qed.

Definition finite_enum_positions {A} (mu : FiniteEnum R A) :
    FiniteEnum R (finite_position (finite_enum_raw mu)) :=
  finite_enum_of_list (finite_positions_nonnegative (finite_enum_nonnegative mu)).

Lemma finite_enum_positions_decode {A} (mu : FiniteEnum R A) :
  finite_enum_raw
    (finite_enum_map (finite_position_value (finite_enum_raw mu)) (finite_enum_positions mu)) =
  finite_enum_raw mu.
Proof. exact: finite_positions_decode. Qed.

Lemma finite_enum_positions_expect {A} (mu : FiniteEnum R A) (f : A -> R) :
  finite_enum_expect (finite_enum_positions mu)
    (fun i => f (finite_position_value (finite_enum_raw mu) i)) = finite_enum_expect mu f.
Proof. exact: finite_positions_expect. Qed.

Lemma finite_enum_positions_mass {A} (mu : FiniteEnum R A) :
  finite_mass (finite_enum_positions mu) = finite_mass mu.
Proof. exact: finite_positions_expect. Qed.

Definition finite_subdist_positions {A} (mu : FiniteSubdist R A) :
    FiniteSubdist R (finite_position (finite_enum_raw (finite_subdist_enum mu))).
Proof.
  refine (@Build_FiniteSubdist R _ (finite_enum_positions (finite_subdist_enum mu)) _).
  rewrite finite_enum_positions_mass; exact: finite_subdist_mass_bound.
Defined.

Lemma finite_subdist_positions_expect {A} (mu : FiniteSubdist R A) (f : A -> R) :
  finite_subdist_expect (finite_subdist_positions mu)
    (fun i => f (finite_position_value (finite_enum_raw (finite_subdist_enum mu)) i)) =
  finite_subdist_expect mu f.
Proof. exact: finite_positions_expect. Qed.

Lemma finite_subdist_positions_decode {A} (mu : FiniteSubdist R A) :
  finite_enum_raw (finite_subdist_enum
    (finite_subdist_map (finite_position_value (finite_enum_raw (finite_subdist_enum mu)))
      (finite_subdist_positions mu))) = finite_enum_raw (finite_subdist_enum mu).
Proof. exact: finite_positions_decode. Qed.
End CheckedPresentation.
