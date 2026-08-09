Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 List Morphisms.

From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat.

From PTree.Prob Require Import DiscreteMC Coupling.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum EnumMap Coupling.

Module IndexedCoupling.

(**
  Attach a fresh natural-number position to every entry.  Unlike the values
  stored in an [Enum], positions have decidable equality even when the values
  are functions or observable heads containing continuations.
*)
Fixpoint index_from {A} (n : nat) (mu : Enum A) : Enum nat :=
  match mu with
  | [::] => [::]
  | (p, _) :: tl => (p, n) :: index_from n.+1 tl
  end.

Definition indexed {A} (mu : Enum A) : Enum nat :=
  index_from 0 mu.

(**
  [at_index R mu nu i j] relates positions extensionally.  Both implications
  are included so that out-of-range positions relate harmlessly, while any
  valid position forces the other position to be valid and its values to
  satisfy [R].
*)
Definition at_index {A B}
    (R : A -> B -> Prop) (mu : Enum A) (nu : Enum B)
    (i j : nat) : Prop :=
  (forall p a,
      nth_error mu i = Some (p, a) ->
      exists q b, nth_error nu j = Some (q, b) /\ R a b) /\
  (forall q b,
      nth_error nu j = Some (q, b) ->
      exists p a, nth_error mu i = Some (p, a) /\ R a b).

Definition indexed_coupling {A B}
    (R : A -> B -> Prop) (mu : Enum A) (nu : Enum B) : Prop :=
  coupling (at_index R mu nu) (indexed mu) (indexed nu).

Lemma at_index_mono {A B}
    (R S : A -> B -> Prop) (mu : Enum A) (nu : Enum B) i j :
  (forall a b, R a b -> S a b) ->
  at_index R mu nu i j ->
  at_index S mu nu i j.
Proof.
  move=> HRS [HL HR]; split.
  - move=> p a Hi.
    move: (HL p a Hi) => [q [b [Hj Hab]]].
    exists q, b. split=> //.
    exact: HRS Hab.
  - move=> q b Hj.
    move: (HR q b Hj) => [p [a [Hi Hab]]].
    exists p, a. split=> //.
    exact: HRS Hab.
Qed.

Lemma indexed_coupling_mono {A B}
    (R S : A -> B -> Prop) (mu : Enum A) (nu : Enum B) :
  (forall a b, R a b -> S a b) ->
  indexed_coupling R mu nu ->
  indexed_coupling S mu nu.
Proof.
  move=> HRS.
  eapply coupling_mono.
  move=> i j Hij.
  exact: at_index_mono HRS Hij.
Qed.

Lemma at_index_refl {A}
    (R : A -> A -> Prop) (mu : Enum A) :
  Reflexive R ->
  forall i, at_index R mu mu i i.
Proof.
  move=> HR i; split.
  - move=> p a Hi. exists p, a. split.
    + exact Hi.
    + exact: HR a.
  - move=> p a Hi. exists p, a. split.
    + exact Hi.
    + exact: HR a.
Qed.

Lemma indexed_coupling_refl {A}
    (R : A -> A -> Prop) (mu : Enum A) :
  Reflexive R ->
  indexed_coupling R mu mu.
Proof.
  move=> HR.
  eapply coupling_mono.
  - move=> i j Hij. move: Hij => ->.
    apply at_index_refl. exact HR.
  - exact: coupling_refl (indexed mu).
Qed.

Lemma at_index_sym {A B}
    (R : A -> B -> Prop) (mu : Enum A) (nu : Enum B) i j :
  at_index R mu nu i j ->
  at_index (fun b a => R a b) nu mu j i.
Proof.
  move=> [HL HR]. split.
  - exact HR.
  - exact HL.
Qed.

Lemma indexed_coupling_sym {A B}
    (R : A -> B -> Prop) (mu : Enum A) (nu : Enum B) :
  indexed_coupling R mu nu ->
  indexed_coupling (fun b a => R a b) nu mu.
Proof.
  move=> H.
  eapply coupling_mono.
  - move=> j i Hji. exact: at_index_sym Hji.
  - exact: coupling_sym H.
Qed.

Lemma at_index_comp {A B C}
    (R : A -> B -> Prop) (S : B -> C -> Prop)
    (mu : Enum A) (nu : Enum B) (xi : Enum C) i j k :
  at_index R mu nu i j ->
  at_index S nu xi j k ->
  at_index (fun a c => exists b, R a b /\ S b c) mu xi i k.
Proof.
  move=> [HAB HBA] [HBC HCB]. split.
  - move=> p a Hi.
    move: (HAB p a Hi) => [q [b [Hj Hab]]].
    move: (HBC q b Hj) => [s [c [Hk Hbc]]].
    exists s, c. split=> //.
    by exists b.
  - move=> s c Hk.
    move: (HCB s c Hk) => [q [b [Hj Hbc]]].
    move: (HBA q b Hj) => [p [a [Hi Hab]]].
    exists p, a. split=> //.
    by exists b.
Qed.

Lemma indexed_coupling_comp {A B C}
    (R : A -> B -> Prop) (S : B -> C -> Prop)
    (mu : Enum A) (nu : Enum B) (xi : Enum C) :
  indexed_coupling R mu nu ->
  indexed_coupling S nu xi ->
  indexed_coupling
    (fun a c => exists b, R a b /\ S b c) mu xi.
Proof.
  move=> HAB HBC.
  have Hcomp := coupling_comp HAB HBC.
  eapply coupling_mono; [|exact Hcomp].
  move=> i k [j [Hij Hjk]].
  exact: at_index_comp Hij Hjk.
Qed.

End IndexedCoupling.

Export IndexedCoupling.
