Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import Utf8 List Morphisms Lia PeanoNat.

From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat ssralg order rat.

From PTree.Prob Require Import RatSubTypes DiscreteMC EnumBindFacts Coupling.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum EnumMap Coupling.
Import GRing.Theory.
#[local] Open Scope ring_scope.

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

Fixpoint value_index_joint_from {A} (n : nat) (mu : Enum A)
    : Enum (A * nat) :=
  match mu with
  | [::] => [::]
  | (p, a) :: tl => (p, (a, n)) :: value_index_joint_from n.+1 tl
  end.

Lemma emap_fst_value_index_joint_from {A : eqType} n (mu : Enum A) :
  emap fst (value_index_joint_from n mu) = mu.
Proof. by elim: mu n=> [|[p a] mu IH] n //=; rewrite IH. Qed.

Lemma emap_snd_value_index_joint_from {A} n (mu : Enum A) :
  emap snd (value_index_joint_from n mu) = index_from n mu.
Proof. by elim: mu n=> [|[p a] mu IH] n //=; rewrite IH. Qed.

Lemma value_index_joint_nth {A : eqType} n (mu : Enum A) a i :
  acc_mass (a, i) (value_index_joint_from n mu) !=
      RatSubTypes.nnQ_0 ->
  exists p, nth_error mu (i - n) = Some (p, a) /\ n <= i.
Proof.
  elim: mu n=> [|[p x] mu IH] n //=.
  rewrite /acc_mass /=.
  case Epair: ((x, n) == (a, i)).
  - move/eqP: Epair=> [-> ->] _. exists p. split.
    + by rewrite subnn.
    + exact: leqnn.
  - move=> Hmass.
    move: (IH n.+1 Hmass)=> [q [Hnth Hle]].
    exists q. split=> //.
    have Hni : n < i := Hle.
    rewrite -(subnSK Hni).
    exact Hnth.
    exact: ltnW Hle.
Qed.

Lemma coupling_value_index {A : eqType} (mu : Enum A) :
  coupling
    (fun a i => exists p, nth_error mu i = Some (p, a))
    mu (indexed mu).
Proof.
  exists (value_index_joint_from 0 mu).
  - apply enum_eq_eq. exact: emap_fst_value_index_joint_from.
  - apply enum_eq_eq. exact: emap_snd_value_index_joint_from.
  - move=> a i Hai.
    move: (value_index_joint_nth
      (n := 0) (mu := mu) (a := a) (i := i) Hai)=> [p [Hnth _]].
    exists p. by rewrite subn0 in Hnth.
Qed.

Lemma indexed_coupling_of_coupling {A B : eqType}
    (R : A -> B -> Prop) (mu : Enum A) (nu : Enum B) :
  coupling R mu nu -> indexed_coupling R mu nu.
Proof.
  move=> Hmn.
  have Him := coupling_sym (coupling_value_index mu).
  have H1 := coupling_comp Him Hmn.
  have H2 := coupling_comp H1 (coupling_value_index nu).
  eapply coupling_mono; [|exact H2].
  move=> i j [b [[a [[p Hip] Hrab]] [q Hjq]]].
  split.
  - move=> p' a' Hip'.
    rewrite Hip in Hip'. inversion Hip'; subst p' a'.
    exists q, b. split=> //.
  - move=> q' b' Hjq'.
    rewrite Hjq in Hjq'. inversion Hjq'; subst q' b'.
    exists p, a. split=> //.
Qed.

Lemma index_from_emap {A B} (f : A -> B) n (mu : Enum A) :
  index_from n (emap f mu) = index_from n mu.
Proof. by elim: mu n=> [|[p a] mu IH] n //=; rewrite IH. Qed.

Lemma indexed_emap {A B} (f : A -> B) (mu : Enum A) :
  indexed (emap f mu) = indexed mu.
Proof. exact: index_from_emap. Qed.

Lemma nth_error_index_from_inv {A} n (mu : Enum A) i p j :
  nth_error (index_from n mu) i = Some (p, j) ->
  exists a, nth_error mu i = Some (p, a) /\ j = Nat.add n i.
Proof.
  revert n i p j.
  induction mu as [|[q a] mu IH]; intros n [|i] p j Hnth;
    cbn in Hnth; try discriminate.
  - inversion Hnth; subst p j. exists a. split=> //.
    symmetry. exact: Nat.add_0_r n.
  - move: (IH n.+1 i p j Hnth)=> [b [Hi ->]].
    exists b. split=> //.
    rewrite Nat.add_succ_l Nat.add_succ_r. reflexivity.
Qed.

Lemma indexed_nonzero_nth {A} (mu : Enum A) i :
  acc_mass i (indexed mu) != RatSubTypes.nnQ_0 ->
  exists p a, nth_error mu i = Some (p, a).
Proof.
  move=> Hi.
  have Hsupp : i \in supp (indexed mu).
  { apply/(in_supp_iff_acc_mass_ne_0 i (indexed mu)). exact Hi. }
  rewrite /supp mem_undup in Hsupp.
  move/mapP: Hsupp=> [[p j] Hentry Hij].
  cbn in Hij. subst j.
  rewrite mem_filter in Hentry. move/andP: Hentry=> [_ Hentry].
  rewrite /indexed in Hentry.
  have Hin : List.In (p, i) (index_from 0 mu).
  { move: Hentry. clear Hi.
    induction (index_from 0 mu) as [|x xs IH]=> //=.
    move=> /orP [H|H].
    - left. move/eqP: H=> H. symmetry. exact H.
    - right. exact: IH H. }
  move: (In_nth_error _ _ Hin)=> [pos Hpos].
  move: (nth_error_index_from_inv Hpos)=> [a [Hmu Heq]].
  rewrite Nat.add_0_l in Heq. subst pos.
  by exists p, a.
Qed.

Lemma nth_error_emap_inv {A B} (f : A -> B) (mu : Enum A) i p b :
  nth_error (emap f mu) i = Some (p, b) ->
  exists a, nth_error mu i = Some (p, a) /\ b = f a.
Proof.
  elim: mu i=> [|[q a] mu IH] [|i] //=.
  - move=> H. inversion H; subst. by exists a.
  - exact: IH.
Qed.

Definition shift_index (offset i : nat) : nat := Nat.add offset i.

Lemma index_from_shift_from {A} offset start (mu : Enum A) :
  index_from (Nat.add offset start) mu =
  emap (shift_index offset) (index_from start mu).
Proof.
  revert offset start.
  induction mu as [|[p a] mu IH]; intros offset start; cbn.
  - reflexivity.
  - unfold shift_index at 1.
    rewrite <- Nat.add_succ_r.
    rewrite IH. reflexivity.
Qed.

Lemma index_from_shift {A} offset (mu : Enum A) :
  index_from offset mu = emap (shift_index offset) (indexed mu).
Proof.
  unfold indexed.
  rewrite <- (Nat.add_0_r offset) at 1.
  exact: index_from_shift_from.
Qed.

Lemma index_from_scale {A} offset p (mu : Enum A) :
  index_from offset (scale_Enum p mu) =
  scale_Enum p (index_from offset mu).
Proof.
  revert offset.
  induction mu as [|[q a] mu IH]; intro offset; cbn=> //.
  rewrite IH. reflexivity.
Qed.

Lemma index_from_app {A} offset (mu nu : Enum A) :
  index_from offset (mu ++ nu) =
  index_from offset mu ++
    index_from (Nat.add offset (size mu)) nu.
Proof.
  revert offset.
  induction mu as [|[p a] mu IH]; intro offset; cbn.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH Nat.add_succ_r. reflexivity.
Qed.

Fixpoint indexed_bind_blocks {A B}
    (mu : Enum A) (k : A -> Enum B) (offset : nat) : Enum nat :=
  match mu with
  | [::] => [::]
  | (p, a) :: tl =>
      scale_Enum p (index_from offset (k a)) ++
      indexed_bind_blocks tl k (Nat.add offset (size (k a)))
  end.

Lemma index_from_bind_Enum {A B} offset
    (mu : Enum A) (k : A -> Enum B) :
  index_from offset (bind_Enum mu k) = indexed_bind_blocks mu k offset.
Proof.
  revert offset.
  induction mu as [|[p a] mu IH]; intro offset; cbn=> //.
  rewrite index_from_app index_from_scale size_scale_Enum IH.
  reflexivity.
Qed.

Lemma indexed_bind_Enum {A B} (mu : Enum A) (k : A -> Enum B) :
  indexed (bind_Enum mu k) = indexed_bind_blocks mu k 0.
Proof. exact: index_from_bind_Enum. Qed.

Definition shifted_at_index {A B} (R : A -> B -> Prop)
    (mu : Enum A) (nu : Enum B) (oi oj : nat) (i j : nat) : Prop :=
  exists li lj,
    i = shift_index oi li /\ j = shift_index oj lj /\
    at_index R mu nu li lj.

Lemma coupling_shift_index {A B} (R : A -> B -> Prop)
    (mu : Enum A) (nu : Enum B) oi oj :
  indexed_coupling R mu nu ->
  coupling (shifted_at_index R mu nu oi oj)
    (index_from oi mu) (index_from oj nu).
Proof.
  move=> H.
  rewrite !index_from_shift.
  have Hmap := coupling_emap
    (R := at_index R mu nu)
    (S := shifted_at_index R mu nu oi oj)
    (f := shift_index oi) (g := shift_index oj)
    (fun i j Hij => ex_intro _ i
      (ex_intro _ j (conj (Logic.eq_refl _)
        (conj (Logic.eq_refl _) Hij)))) H.
  exact Hmap.
Qed.

(** A related pair of continuation positions induces related global
    positions in the two flattened binds. *)
Lemma at_index_bind_entries {A B C D} (R : C -> D -> Prop)
    (mu : Enum A) (nu : Enum B)
    (k : A -> Enum C) (h : B -> Enum D)
    ix iy li lj p a q b :
  nth_error mu ix = Some (p, a) ->
  nth_error nu iy = Some (q, b) ->
  (exists r c, nth_error (k a) li = Some (r, c)) ->
  (exists s d, nth_error (h b) lj = Some (s, d)) ->
  at_index R (k a) (h b) li lj ->
  at_index R (bind_Enum mu k) (bind_Enum nu h)
    (Nat.add (bind_offset mu k ix) li)
    (Nat.add (bind_offset nu h iy) lj).
Proof.
  move=> Hmu Hnu [r [c0 Hka]] [s [d0 Hhb]] [HL HR]. split.
  - move=> w c Hleft.
    have Hknown := nth_error_bind_Enum Hmu Hka.
    rewrite Hleft in Hknown. inversion Hknown; subst w c0.
    move: (HL r c Hka)=> [s' [d [Hhd Rcd]]].
    exists (q * s'), d. split.
    - exact: nth_error_bind_Enum Hnu Hhd.
    - exact Rcd.
  - move=> w d Hright.
    have Hknown := nth_error_bind_Enum Hnu Hhb.
    rewrite Hright in Hknown. inversion Hknown; subst w d0.
    move: (HR s d Hhb)=> [r' [c [Hkc Rcd]]].
    exists (p * r'), c. split.
    - exact: nth_error_bind_Enum Hmu Hkc.
    - exact Rcd.
Qed.

Lemma nth_error_emap {A B} (f : A -> B) (mu : Enum A) i p a :
  nth_error mu i = Some (p, a) ->
  nth_error (emap f mu) i = Some (p, f a).
Proof.
  elim: mu i=> [|[q b] mu IH] [|i] //=.
  - move=> H. by inversion H; subst.
  - exact: IH.
Qed.

Lemma indexed_coupling_emap {A B C D}
    (S : A -> B -> Prop) (R : C -> D -> Prop)
    (f : A -> C) (g : B -> D) (mu : Enum A) (nu : Enum B) :
  (forall a b, S a b -> R (f a) (g b)) ->
  indexed_coupling S mu nu ->
  indexed_coupling R (emap f mu) (emap g nu).
Proof.
  move=> HSR Hc.
  rewrite /indexed_coupling !indexed_emap.
  eapply coupling_mono; [|exact Hc].
  move=> i j [HL HR]; split.
  - move=> p c Hic.
    move: (nth_error_emap_inv Hic)=> [a [Hia ->]].
    move: (HL p a Hia)=> [q [b [Hjb Hab]]].
    exists q, (g b). split.
    + exact: nth_error_emap Hjb.
    + exact: HSR Hab.
  - move=> q d Hjd.
    move: (nth_error_emap_inv Hjd)=> [b [Hjb ->]].
    move: (HR q b Hjb)=> [p [a [Hia Hab]]].
    exists p, (f a). split.
    + exact: nth_error_emap Hia.
    + exact: HSR Hab.
Qed.

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
