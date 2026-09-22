(** Position coupling for arbitrary result types over the shared rational
    carrier. Zero entries still occupy positions; pruning belongs elsewhere. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Utf8 List Morphisms Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype seq ssrnat ssralg ssrnum order rat.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteAtoms FiniteSupport
  FinitePositions FiniteListAlgebra FiniteIndexedBind.
From PTree.Prob.Backend.EnumQ Require Import Representation Bind Map Coupling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.
Module IndexedCoupling.

Definition index_from {A} (n : nat) (mu : EnumQ A) : EnumQ nat :=
  finite_enum_index_from n mu.
Definition indexed {A} (mu : EnumQ A) : EnumQ nat := index_from 0 mu.
Definition at_index {A B} (R : A -> B -> Prop) (mu : EnumQ A) (nu : EnumQ B)
    (i j : nat) : Prop :=
  (forall p a, nth_error (enumQ_raw mu) i = Some (p,a) ->
    exists q b, nth_error (enumQ_raw nu) j = Some (q,b) /\ R a b) /\
  (forall q b, nth_error (enumQ_raw nu) j = Some (q,b) ->
    exists p a, nth_error (enumQ_raw mu) i = Some (p,a) /\ R a b).
Definition indexed_coupling {A B} (R : A -> B -> Prop) (mu : EnumQ A) (nu : EnumQ B) : Prop :=
  coupling (at_index R mu nu) (indexed mu) (indexed nu).
Definition value_index_joint_from {A} n (mu : EnumQ A) : EnumQ (A*nat) :=
  finite_enum_value_index_from n mu.

Lemma emap_fst_value_index_joint_from {A : eqType} n (mu : EnumQ A) :
  enumQ_raw (emap fst (value_index_joint_from n mu)) = enumQ_raw mu.
Proof. exact: finite_value_index_fst. Qed.
Lemma emap_snd_value_index_joint_from {A} n (mu : EnumQ A) :
  enumQ_raw (emap snd (value_index_joint_from n mu)) = enumQ_raw (index_from n mu).
Proof. exact: finite_value_index_snd. Qed.

Lemma value_index_joint_nth {A : eqType} n (mu : EnumQ A) a i :
  acc_mass (a,i) (value_index_joint_from n mu) != 0 ->
  exists p, nth_error (enumQ_raw mu) (i-n)%N = Some (p,a) /\ (n <= i)%N.
Proof.
  move=> H; have Hpos : 0 < acc_mass (a,i) (value_index_joint_from n mu).
  { rewrite lt0r H /=; exact: acc_mass_nonnegative. }
  have [p [Hin _]] := proj1 (enumQ_atom_positive (value_index_joint_from n mu) (a,i)) Hpos.
  have [j Hj] := In_nth_error _ _ Hin.
  change (nth_error (finite_value_index_from n (enumQ_raw mu)) j = Some (p,(a,i))) in Hj.
  rewrite finite_value_index_nth in Hj.
  case Hnth: (nth_error (enumQ_raw mu) j)=> [[q x]|] in Hj; last discriminate.
  inversion Hj; subst q x i; exists p; split.
  - by rewrite -addnE addKn.
  - rewrite -addnE; exact: leq_addr.
Qed.
Lemma coupling_value_index {A : eqType} (mu : EnumQ A) :
  coupling (fun a i => exists p, nth_error (enumQ_raw mu) i = Some (p,a)) mu (indexed mu).
Proof.
  exists (value_index_joint_from 0 mu).
  - apply enumQ_eq_eq; exact: emap_fst_value_index_joint_from.
  - apply enumQ_eq_eq; exact: emap_snd_value_index_joint_from.
  - move=> a i H; have [p [Hi _]] := value_index_joint_nth H.
    exists p; by rewrite subn0 in Hi.
Qed.
Lemma indexed_coupling_of_coupling {A B : eqType} (R : A -> B -> Prop)
    (mu : EnumQ A) (nu : EnumQ B) : coupling R mu nu -> indexed_coupling R mu nu.
Proof.
  move=> H; have H1 := coupling_comp (coupling_sym (coupling_value_index mu)) H.
  have H2 := coupling_comp H1 (coupling_value_index nu).
  eapply coupling_mono; last exact H2.
  move=> i j [b [[a [[p Hip] Hab]] [q Hjq]]]; split.
  - move=> p' a' Hip'; rewrite Hip in Hip'; inversion Hip'; subst; by exists q,b.
  - move=> q' b' Hjq'; rewrite Hjq in Hjq'; inversion Hjq'; subst; by exists p,a.
Qed.

Lemma index_from_emap {A B} (f : A -> B) n (mu : EnumQ A) :
  enumQ_raw (index_from n (emap f mu)) = enumQ_raw (index_from n mu).
Proof. exact: finite_index_map_values. Qed.
Lemma indexed_emap {A B} (f : A -> B) (mu : EnumQ A) :
  enumQ_raw (indexed (emap f mu)) = enumQ_raw (indexed mu).
Proof. exact: index_from_emap. Qed.
Lemma nth_error_index_from_inv {A} n (mu : EnumQ A) i p j :
  nth_error (enumQ_raw (index_from n mu)) i = Some (p,j) ->
  exists a, nth_error (enumQ_raw mu) i = Some (p,a) /\ j = Nat.add n i.
Proof.
  change (nth_error (finite_index_from n (enumQ_raw mu)) i = Some (p,j) ->
    exists a, nth_error (enumQ_raw mu) i = Some (p,a) /\ j = Nat.add n i).
  rewrite finite_index_nth; case H: (nth_error (enumQ_raw mu) i)=> [[q a]|] //=.
  move=> He; inversion He; subst; by exists a.
Qed.
Lemma nth_error_index_from {A} n (mu : EnumQ A) i p x :
  nth_error (enumQ_raw mu) i = Some (p,x) ->
  nth_error (enumQ_raw (index_from n mu)) i = Some (p,Nat.add n i).
Proof.
  move=> H; change (nth_error (finite_index_from n (enumQ_raw mu)) i = Some (p,Nat.add n i)).
  by rewrite finite_index_nth H.
Qed.
Lemma indexed_nonzero_nth {A} (mu : EnumQ A) i :
  acc_mass i (indexed mu) != 0 -> exists p a, nth_error (enumQ_raw mu) i = Some (p,a).
Proof.
  move=> H; have Hpos : 0 < acc_mass i (indexed mu).
  { rewrite lt0r H /=; exact: acc_mass_nonnegative. }
  have [p [Hin _]] := proj1 (enumQ_atom_positive (indexed mu) i) Hpos.
  have [j Hj] := In_nth_error _ _ Hin.
  have [a [Ha He]] := nth_error_index_from_inv Hj.
  rewrite Nat.add_0_l in He; subst j; by exists p,a.
Qed.
Lemma indexed_nth_nonzero {A} (mu : EnumQ A) i p x :
  nth_error (enumQ_raw mu) i = Some (p,x) -> p != 0 -> acc_mass i (indexed mu) != 0.
Proof.
  move=> H Hp; apply entry_nonzero_acc_mass with p; last exact Hp.
  apply (proj2 (enumQ_raw_mem p i (indexed mu))); apply nth_error_In with i.
  have Hi := nth_error_index_from 0 H; by rewrite Nat.add_0_l in Hi.
Qed.
Lemma nth_error_emap_inv {A B} (f : A -> B) (mu : EnumQ A) i p b :
  nth_error (enumQ_raw (emap f mu)) i = Some (p,b) ->
  exists a, nth_error (enumQ_raw mu) i = Some (p,a) /\ b = f a.
Proof.
  change (nth_error (List.map (fun px => (px.1,f px.2)) (enumQ_raw mu)) i = Some (p,b) ->
    exists a, nth_error (enumQ_raw mu) i = Some (p,a) /\ b = f a).
  rewrite nth_error_map; case H: (nth_error (enumQ_raw mu) i)=> [[q a]|] //=.
  move=> He; inversion He; subst; by exists a.
Qed.
Lemma nth_error_emap {A B} (f : A -> B) (mu : EnumQ A) i p a :
  nth_error (enumQ_raw mu) i = Some (p,a) ->
  nth_error (enumQ_raw (emap f mu)) i = Some (p,f a).
Proof.
  move=> H; change (nth_error (List.map (fun px => (px.1,f px.2)) (enumQ_raw mu)) i = Some (p,f a)).
  by rewrite nth_error_map H.
Qed.

Definition shift_index (offset i : nat) := Nat.add offset i.
Lemma index_from_shift_from {A} offset start (mu : EnumQ A) :
  enumQ_raw (index_from (Nat.add offset start) mu) =
  enumQ_raw (emap (shift_index offset) (index_from start mu)).
Proof. exact: finite_index_shift_from. Qed.
Lemma index_from_shift {A} offset (mu : EnumQ A) :
  enumQ_raw (index_from offset mu) = enumQ_raw (emap (shift_index offset) (indexed mu)).
Proof. rewrite -{1}(Nat.add_0_r offset); exact: index_from_shift_from. Qed.
Lemma index_from_scale {A} offset p (Hp : 0 <= p) (mu : EnumQ A) :
  enumQ_raw (index_from offset (scale_EnumQ Hp mu)) =
  enumQ_raw (scale_EnumQ Hp (index_from offset mu)).
Proof. exact: finite_index_map_weights. Qed.
Lemma index_from_app {A} offset (mu nu : EnumQ A) :
  enumQ_raw (index_from offset (enumQ_app mu nu)) =
  enumQ_raw (enumQ_app (index_from offset mu)
    (index_from (Nat.add offset (size (enumQ_raw mu))) nu)).
Proof. exact: finite_index_app. Qed.
Lemma index_from_in_ge {A} n (mu : EnumQ A) p i :
  List.In (p,i) (enumQ_raw (index_from n mu)) -> (n <= i)%coq_nat.
Proof. exact: finite_index_in_ge. Qed.

Definition indexed_bind_blocks {A B} (mu : EnumQ A) (k : A -> EnumQ B) offset : EnumQ nat :=
  index_from offset (bind_EnumQ mu k).
Lemma index_from_bind_EnumQ {A B} offset (mu : EnumQ A) (k : A -> EnumQ B) :
  enumQ_raw (index_from offset (bind_EnumQ mu k)) = enumQ_raw (indexed_bind_blocks mu k offset).
Proof. reflexivity. Qed.
Lemma indexed_bind_EnumQ {A B} (mu : EnumQ A) (k : A -> EnumQ B) :
  enumQ_raw (indexed (bind_EnumQ mu k)) = enumQ_raw (indexed_bind_blocks mu k 0).
Proof. reflexivity. Qed.
Lemma indexed_bind_blocks_data {A B} (mu : EnumQ A) (k : A -> EnumQ B) offset :
  enumQ_raw (indexed_bind_blocks mu k offset) =
  finite_indexed_bind_blocks (fun p q : rat => p*q) (enumQ_raw mu)
    (fun x => enumQ_raw (k x)) offset.
Proof.
  change (finite_index_from offset (finite_bind (enumQ_raw mu) (fun x => enumQ_raw (k x))) =
    finite_indexed_bind_blocks (fun p q : rat => p*q) (enumQ_raw mu)
      (fun x => enumQ_raw (k x)) offset).
  rewrite -finite_bind_with_numeric; exact: finite_index_bind.
Qed.

Definition indexed_bind_block_from {A B} (mu : EnumQ A) (k : A -> EnumQ B)
    (start offset i : nat) : EnumQ nat.
Proof.
  refine (enumQ_of_list (mu := finite_indexed_bind_block_from (enumQ_raw mu)
    (fun x => enumQ_raw (k x)) start offset i) _).
  elim: (enumQ_raw mu) start offset=> [|[p a] tl IH] start offset /=.
  - by move=> q j [].
  - case: (Nat.eqb i start).
    + exact (finite_index_nonnegative (n := offset) (enumQ_nonnegative (k a))).
    + exact: IH.
Defined.
Lemma index_from_bind_as_position_bind {A B} (mu : EnumQ A) (k : A -> EnumQ B) start offset :
  enumQ_raw (index_from offset (bind_EnumQ mu k)) =
  enumQ_raw (bind_EnumQ (index_from start mu) (indexed_bind_block_from mu k start offset)).
Proof.
  change (finite_index_from offset (finite_bind (enumQ_raw mu) (fun x => enumQ_raw (k x))) =
    finite_bind (finite_index_from start (enumQ_raw mu))
      (finite_indexed_bind_block_from (enumQ_raw mu) (fun x => enumQ_raw (k x)) start offset)).
  rewrite -!finite_bind_with_numeric; exact: finite_index_bind_as_position_bind.
Qed.
Definition indexed_bind_block {A B} (mu : EnumQ A) (k : A -> EnumQ B) i :=
  indexed_bind_block_from mu k 0 0 i.
Lemma indexed_bind_as_position_bind {A B} (mu : EnumQ A) (k : A -> EnumQ B) :
  enumQ_raw (indexed (bind_EnumQ mu k)) =
  enumQ_raw (bind_EnumQ (indexed mu) (indexed_bind_block mu k)).
Proof. exact: index_from_bind_as_position_bind. Qed.
Lemma indexed_bind_block_from_nth {A B} (mu : EnumQ A) (k : A -> EnumQ B) start offset i p a :
  nth_error (enumQ_raw mu) i = Some (p,a) ->
  enumQ_raw (indexed_bind_block_from mu k start offset (Nat.add start i)) =
  enumQ_raw (index_from (Nat.add offset (bind_offset mu k i)) (k a)).
Proof. exact: finite_indexed_bind_block_from_nth. Qed.
Lemma indexed_bind_block_nth {A B} (mu : EnumQ A) (k : A -> EnumQ B) i p a :
  nth_error (enumQ_raw mu) i = Some (p,a) ->
  enumQ_raw (indexed_bind_block mu k i) = enumQ_raw (index_from (bind_offset mu k i) (k a)).
Proof. exact: (@indexed_bind_block_from_nth A B mu k 0 0 i p a). Qed.
Lemma index_from_nonzero_nth {A} n (mu : EnumQ A) i :
  acc_mass (Nat.add n i) (index_from n mu) != 0 ->
  exists p a, nth_error (enumQ_raw mu) i = Some (p,a).
Proof.
  move=> H; have Hpos : 0 < acc_mass (Nat.add n i) (index_from n mu).
  { rewrite lt0r H /=; exact: acc_mass_nonnegative. }
  have [p [Hin _]] := proj1 (enumQ_atom_positive (index_from n mu) (Nat.add n i)) Hpos.
  have [j Hj] := In_nth_error _ _ Hin.
  have [a [Ha He]] := nth_error_index_from_inv Hj.
  have Hji : j = i by lia.
  subst j; by exists p,a.
Qed.
Definition shifted_at_index {A B} (R : A -> B -> Prop) (mu : EnumQ A) (nu : EnumQ B)
    (oi oj i j : nat) : Prop :=
  exists li lj, i = shift_index oi li /\ j = shift_index oj lj /\ at_index R mu nu li lj.
Lemma coupling_shift_index {A B} (R : A -> B -> Prop) (mu : EnumQ A) (nu : EnumQ B) oi oj :
  indexed_coupling R mu nu -> coupling (shifted_at_index R mu nu oi oj)
    (index_from oi mu) (index_from oj nu).
Proof.
  move=> H; apply (coupling_raw
    (mu := emap (shift_index oi) (indexed mu)) (nu := emap (shift_index oj) (indexed nu))).
  - symmetry; exact: index_from_shift.
  - symmetry; exact: index_from_shift.
  - apply (coupling_emap (R := at_index R mu nu)); last exact H.
    move=> i j Hij; exists i,j; repeat split=> //; exact Hij.
Qed.

(** A related pair of continuation positions induces related global
    positions in the two flattened binds. *)
Lemma at_index_bind_entries {A B C D} (R : C -> D -> Prop)
    (mu : EnumQ A) (nu : EnumQ B)
    (k : A -> EnumQ C) (h : B -> EnumQ D)
    ix iy li lj p a q b :
  nth_error (enumQ_raw mu) ix = Some (p, a) ->
  nth_error (enumQ_raw nu) iy = Some (q, b) ->
  (exists r c, nth_error (enumQ_raw (k a)) li = Some (r, c)) ->
  (exists s d, nth_error (enumQ_raw (h b)) lj = Some (s, d)) ->
  at_index R (k a) (h b) li lj ->
  at_index R (bind_EnumQ mu k) (bind_EnumQ nu h)
    (Nat.add (bind_offset mu k ix) li)
    (Nat.add (bind_offset nu h iy) lj).
Proof.
  move=> Hmu Hnu [r [c0 Hka]] [s [d0 Hhb]] [HL HR]. split.
  - move=> w c Hleft.
    have Hknown := nth_error_bind_EnumQ Hmu Hka.
    rewrite Hleft in Hknown. inversion Hknown; subst w c0.
    move: (HL r c Hka)=> [s' [d [Hhd Rcd]]].
    exists (q * s'), d. split.
    - exact: nth_error_bind_EnumQ Hnu Hhd.
    - exact Rcd.
  - move=> w d Hright.
    have Hknown := nth_error_bind_EnumQ Hnu Hhb.
    rewrite Hright in Hknown. inversion Hknown; subst w d0.
    move: (HR s d Hhb)=> [r' [c [Hkc Rcd]]].
    exists (p * r'), c. split.
    - exact: nth_error_bind_EnumQ Hmu Hkc.
    - exact Rcd.
Qed.

Lemma coupling_shift_bind_entries {A B C D} (R : C -> D -> Prop)
    (mu : EnumQ A) (nu : EnumQ B)
    (k : A -> EnumQ C) (h : B -> EnumQ D)
    ix iy p a q b :
  nth_error (enumQ_raw mu) ix = Some (p, a) ->
  nth_error (enumQ_raw nu) iy = Some (q, b) ->
  indexed_coupling R (k a) (h b) ->
  coupling (at_index R (bind_EnumQ mu k) (bind_EnumQ nu h))
    (index_from (bind_offset mu k ix) (k a))
    (index_from (bind_offset nu h iy) (h b)).
Proof.
  move=> Hmu Hnu Hkab.
  move: (@coupling_shift_index C D R (k a) (h b)
    (bind_offset mu k ix) (bind_offset nu h iy) Hkab)
    => [j HL HR Hrel].
  exists j=> // gi gj Hgj.
  move: (joint_nonzero_marginals Hgj)=> [HgiL HgjR].
  move: (Hrel gi gj Hgj)=> [li [lj [Hgi [Hgj' Hij]]]].
  unfold shift_index in Hgi, Hgj'. subst gi gj.
  rewrite HL in HgiL. rewrite HR in HgjR.
  move: (index_from_nonzero_nth HgiL)=> [r [c Hkc]].
  move: (index_from_nonzero_nth HgjR)=> [s [d Hhd]].
  apply at_index_bind_entries with p a q b=> //.
  - by exists r, c.
  - by exists s, d.
Qed.

Lemma indexed_coupling_bind {A B C D : Type}
    (S : A -> B -> Prop) (R : C -> D -> Prop)
    (mu : EnumQ A) (nu : EnumQ B)
    (k : A -> EnumQ C) (h : B -> EnumQ D) :
  indexed_coupling S mu nu ->
  (forall a b, S a b -> indexed_coupling R (k a) (h b)) ->
  indexed_coupling R (bind_EnumQ mu k) (bind_EnumQ nu h).
Proof.
  move=> [outer HL HR Houter] Hk.
  unfold indexed_coupling.
  apply (coupling_raw
    (mu := bind_EnumQ (indexed mu) (indexed_bind_block mu k))
    (nu := bind_EnumQ (indexed nu) (indexed_bind_block nu h))).
  - symmetry; exact: indexed_bind_as_position_bind.
  - symmetry; exact: indexed_bind_as_position_bind.
  - {
  have Hjoint := coupling_bind_joint_on_nonzero
    (R := at_index R (bind_EnumQ mu k) (bind_EnumQ nu h))
    (outer := outer)
    (k := indexed_bind_block mu k)
    (h := indexed_bind_block nu h).
  eapply coupling_proper_l; [|eapply coupling_proper_r; [|apply Hjoint]].
  - exact: bind_EnumQ_outer_proper HL.
  - exact: bind_EnumQ_outer_proper HR.
  - move=> i j Hij.
    have [Hmi Hnj] := joint_nonzero_marginals Hij.
    rewrite HL in Hmi. rewrite HR in Hnj.
    move: (indexed_nonzero_nth Hmi)=> [p [a Hia]].
    move: (indexed_nonzero_nth Hnj)=> [q [b Hjb]].
    have Hijrel := Houter i j Hij.
    move: ((proj1 Hijrel) p a Hia)=> [q' [b' [Hjb' Sab]]].
    rewrite Hjb in Hjb'. inversion Hjb'; subst q' b'.
    apply (coupling_raw
      (mu := index_from (bind_offset mu k i) (k a))
      (nu := index_from (bind_offset nu h j) (h b))).
    + symmetry; exact: indexed_bind_block_nth Hia.
    + symmetry; exact: indexed_bind_block_nth Hjb.
    +
    exact: coupling_shift_bind_entries Hia Hjb (Hk a b Sab).
}
Qed.

Lemma indexed_coupling_bind_ae {A B C D : Type}
    (S : A -> B -> Prop) (R : C -> D -> Prop)
    (mu : EnumQ A) (nu : EnumQ B)
    (k : A -> EnumQ C) (h : B -> EnumQ D)
    (P : A -> Prop) (Q : B -> Prop) :
  indexed_coupling S mu nu ->
  (forall p a, List.In (p,a) (enumQ_raw mu) -> P a) ->
  (forall q b, List.In (q,b) (enumQ_raw nu) -> Q b) ->
  (forall a b, S a b -> P a -> Q b ->
    indexed_coupling R (k a) (h b)) ->
  indexed_coupling R (bind_EnumQ mu k) (bind_EnumQ nu h).
Proof.
  move=> [outer HL HR Houter] HP HQ Hk.
  unfold indexed_coupling.
  apply (coupling_raw
    (mu := bind_EnumQ (indexed mu) (indexed_bind_block mu k))
    (nu := bind_EnumQ (indexed nu) (indexed_bind_block nu h))).
  - symmetry; exact: indexed_bind_as_position_bind.
  - symmetry; exact: indexed_bind_as_position_bind.
  - {
  eapply coupling_proper_l; [exact: bind_EnumQ_outer_proper HL|].
  eapply coupling_proper_r; [exact: bind_EnumQ_outer_proper HR|].
  apply coupling_bind_joint_on_nonzero=> i j Hij.
  have [Hmi Hnj] := joint_nonzero_marginals Hij.
  rewrite HL in Hmi. rewrite HR in Hnj.
  move: (indexed_nonzero_nth Hmi)=> [p [a Hia]].
  move: (indexed_nonzero_nth Hnj)=> [q [b Hjb]].
  have Hijrel := Houter i j Hij.
  move: ((proj1 Hijrel) p a Hia)=> [q' [b' [Hjb' Sab]]].
  rewrite Hjb in Hjb'. inversion Hjb'; subst q' b'.
  apply (coupling_raw
    (mu := index_from (bind_offset mu k i) (k a))
    (nu := index_from (bind_offset nu h j) (h b))).
  + symmetry; exact: indexed_bind_block_nth Hia.
  + symmetry; exact: indexed_bind_block_nth Hjb.
  +
  eapply coupling_shift_bind_entries; [exact Hia|exact Hjb|].
  apply Hk=> //.
  - apply HP with p. exact: nth_error_In Hia.
  - apply HQ with q. exact: nth_error_In Hjb.
}
Qed.

Lemma indexed_coupling_emap {A B C D}
    (S : A -> B -> Prop) (R : C -> D -> Prop)
    (f : A -> C) (g : B -> D) (mu : EnumQ A) (nu : EnumQ B) :
  (forall a b, S a b -> R (f a) (g b)) ->
  indexed_coupling S mu nu ->
  indexed_coupling R (emap f mu) (emap g nu).
Proof.
  move=> HSR Hc.
  unfold indexed_coupling.
  apply (coupling_raw (mu := indexed mu) (nu := indexed nu)).
  - symmetry; exact: indexed_emap.
  - symmetry; exact: indexed_emap.
  - {
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
}
Qed.

Lemma at_index_mono {A B}
    (R S : A -> B -> Prop) (mu : EnumQ A) (nu : EnumQ B) i j :
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
    (R S : A -> B -> Prop) (mu : EnumQ A) (nu : EnumQ B) :
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
    (R : A -> A -> Prop) (mu : EnumQ A) :
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
    (R : A -> A -> Prop) (mu : EnumQ A) :
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
    (R : A -> B -> Prop) (mu : EnumQ A) (nu : EnumQ B) i j :
  at_index R mu nu i j ->
  at_index (fun b a => R a b) nu mu j i.
Proof.
  move=> [HL HR]. split.
  - exact HR.
  - exact HL.
Qed.

Lemma indexed_coupling_sym {A B}
    (R : A -> B -> Prop) (mu : EnumQ A) (nu : EnumQ B) :
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
    (mu : EnumQ A) (nu : EnumQ B) (xi : EnumQ C) i j k :
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
    (mu : EnumQ A) (nu : EnumQ B) (xi : EnumQ C) :
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

Lemma indexed_coupling_raw {A B} (R : A -> B -> Prop)
    (mu mu' : EnumQ A) (nu nu' : EnumQ B) :
  enumQ_raw mu = enumQ_raw mu' -> enumQ_raw nu = enumQ_raw nu' ->
  indexed_coupling R mu nu -> indexed_coupling R mu' nu'.
Proof.
  move=> H K HC; unfold indexed_coupling in *.
  eapply (coupling_mono (R := at_index R mu nu)).
  - move=> i j; by rewrite /at_index -H -K.
  - apply (coupling_raw (mu := indexed mu) (nu := indexed nu)); last exact HC.
    + change (finite_index_from 0 (enumQ_raw mu) = finite_index_from 0 (enumQ_raw mu')).
      by rewrite H.
    + change (finite_index_from 0 (enumQ_raw nu) = finite_index_from 0 (enumQ_raw nu')).
      by rewrite K.
Qed.
End IndexedCoupling.

Export IndexedCoupling.
