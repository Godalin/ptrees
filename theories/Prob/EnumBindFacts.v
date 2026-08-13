Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import List Lia Lra PeanoNat Arith.

From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat ssralg rat ssrint.

From PTree.Prob Require Import RatSubTypes DiscreteMC EnumMap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Enum.
Import RatSubTypes.
Import GRing.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

Lemma bind_Enum_app {A B}
    (mu nu : Enum A) (k : A -> Enum B) :
  bind_Enum (mu ++ nu) k =
  bind_Enum mu k ++ bind_Enum nu k.
Proof.
  elim: mu => [//=|[p a] mu IH] //=.
  by rewrite IH catA.
Qed.

Fixpoint enum_weightQ {A} (f : A -> rat) (mu : Enum A) : rat :=
  if mu is h :: tl then Qval (fst h) * f (snd h) + enum_weightQ f tl else 0.

Lemma enum_weightQ_filter_split {A : eqType} (f : A -> rat)
    (mu : Enum A) a :
  enum_weightQ f mu = Qval (acc_mass a mu) * f a +
    enum_weightQ f [seq h <- mu | snd h != a].
Proof.
  revert mu.
  refine (list_ind (fun mu => enum_weightQ f mu =
    Qval (acc_mass a mu) * f a +
    enum_weightQ f [seq h <- mu | snd h != a]) _ _).
  - by rewrite /= mul0r add0r.
  - intros [p x] tl IH. cbn [enum_weightQ filter].
    rewrite acc_mass_cons.
    destruct (x == a) eqn:Hxa.
    + move/eqP: Hxa=> Hxa. subst x.
      cbn. rewrite IH.
      rewrite eq_refl /=.
      change (Qval p * f a +
        (Qval (acc_mass a tl) * f a +
          enum_weightQ f [seq h <- tl | snd h != a]) =
        (Qval (acc_mass a tl) + Qval p) * f a +
          enum_weightQ f [seq h <- tl | snd h != a]).
      rewrite mulrDl !addrA.
      congr (_ + _). exact: addrC.
    + rewrite Hxa /=.
      rewrite IH.
      rewrite GRing.addr0.
      exact: addrCA.
Qed.

Lemma enum_weightQ_zero {A : eqType} (f : A -> rat) (mu : Enum A) :
  (forall a, acc_mass a mu = 0) -> enum_weightQ f mu = 0.
Proof.
  elim: mu=> [|[p x] tl IH] Hzero //=.
  have Hp : p = 0.
  { have Hx := Hzero x. rewrite acc_mass_cons eq_refl in Hx.
    apply/eqP.
    have Hsum : acc_mass x tl + p == 0 by rewrite Hx.
    have Hparts : (acc_mass x tl == 0) && (p == 0).
    { rewrite -ssrnum.Num.Theory.paddr_eq0 ?le_nnQ0 //. }
    exact (proj2 (andP Hparts)). }
  rewrite Hp /= mul0r add0r. apply IH=> a.
  move: (Hzero a). rewrite (@acc_mass_cons_zero _ tl a (p, x) Hp).
  exact.
Qed.

Lemma enum_weightQ_proper {A : eqType} (f : A -> rat)
    (mu nu : Enum A) :
  mu ==Enum nu -> enum_weightQ f mu = enum_weightQ f nu.
Proof.
  move: mu nu. refine (seq_strong_induction (P := fun mu =>
    forall nu, mu ==Enum nu ->
      enum_weightQ f mu = enum_weightQ f nu) _).
  move=> mu IH nu Hmn. destruct mu as [|[p a] tl].
  - symmetry. apply enum_weightQ_zero=> x.
    symmetry. move: (Hmn x). cbn. exact.
  -
    rewrite (enum_weightQ_filter_split f ((p, a) :: tl) a).
    rewrite (enum_weightQ_filter_split f nu a) (Hmn a).
    congr (_ + _). apply IH.
    + apply/ltP. rewrite size_filter /= eq_refl /=.
      apply/ltP. exact: leq_ltn_trans (count_size _ _) (ltnSn _).
    + exact: (enum_filter_proper (fun x : A => x != a) Hmn).
Qed.

Lemma acc_mass_scale {A : eqType} (x : A) p (mu : Enum A) :
  acc_mass x (scale_Enum p mu) = p * acc_mass x mu.
Proof.
  revert p.
  refine (list_ind (fun mu => forall p,
    acc_mass x (scale_Enum p mu) = p * acc_mass x mu) _ _ mu).
  - intro p. rewrite /= mulr0. reflexivity.
  - intros [q a] tl IH p.
    change (acc_mass x ((p * q, a) :: scale_Enum p tl) =
      p * acc_mass x ((q, a) :: tl)).
    rewrite !acc_mass_cons IH.
    destruct (a == x) eqn:Hax.
    + move/eqP: Hax=> Hax. subst a.
      rewrite !eq_refl -mulrDr. reflexivity.
    + rewrite Hax !addr0. reflexivity.
Qed.

Lemma acc_mass_bind_EnumQ {A} {B : eqType}
    (mu : Enum A) (k : A -> Enum B) b :
  Qval (acc_mass b (bind_Enum mu k)) =
  enum_weightQ (fun a => Qval (acc_mass b (k a))) mu.
Proof.
  elim: mu=> [|[p a] mu IH] //=.
  rewrite acc_app acc_mass_scale /=.
  change (Qval (p * acc_mass b (k a) +
    acc_mass b (bind_Enum mu k)) =
    Qval p * Qval (acc_mass b (k a)) +
      enum_weightQ (fun x => Qval (acc_mass b (k x))) mu).
  change (Qval p * Qval (acc_mass b (k a)) +
    Qval (acc_mass b (bind_Enum mu k)) =
    Qval p * Qval (acc_mass b (k a)) +
      enum_weightQ (fun x => Qval (acc_mass b (k x))) mu).
  rewrite IH.
  reflexivity.
Qed.

Lemma bind_Enum_outer_proper {A B : eqType}
    (mu nu : Enum A) (k : A -> Enum B) :
  mu ==Enum nu -> bind_Enum mu k ==Enum bind_Enum nu k.
Proof.
  move=> Hmn b. apply val_inj. change
    (Qval (acc_mass b (bind_Enum mu k)) =
     Qval (acc_mass b (bind_Enum nu k))).
  rewrite !acc_mass_bind_EnumQ.
  exact: enum_weightQ_proper Hmn.
Qed.

Lemma bind_Enum_scale {A B}
    (p : nnQ) (mu : Enum A) (k : A -> Enum B) :
  bind_Enum (scale_Enum p mu) k =
  scale_Enum p (bind_Enum mu k).
Proof.
  elim: mu => [//=|[q a] mu IH] //=.
  by rewrite IH scale_app !scale_scale.
Qed.

Lemma bind_Enum_assoc {A B C}
    (mu : Enum A) (k : A -> Enum B) (h : B -> Enum C) :
  bind_Enum (bind_Enum mu k) h =
  bind_Enum mu (fun x => bind_Enum (k x) h).
Proof.
  elim: mu => [//=|[p a] mu IH] //=.
  by rewrite bind_Enum_app bind_Enum_scale IH.
Qed.

Lemma bind_Enum_ext {A B}
    (mu : Enum A) (k1 k2 : A -> Enum B) :
  (forall x, k1 x = k2 x) ->
  bind_Enum mu k1 = bind_Enum mu k2.
Proof.
  move=> Hk.
  elim: mu => [//=|[p a] mu IH] //=.
  by rewrite Hk IH.
Qed.

Lemma bind_Enum_ext_in {A B}
    (mu : Enum A) (k1 k2 : A -> Enum B) :
  (forall p x, List.In (p, x) mu -> k1 x = k2 x) ->
  bind_Enum mu k1 = bind_Enum mu k2.
Proof.
  move=> Hk. elim: mu Hk=> [//=|[p a] mu IH] Hk //=.
  rewrite (Hk p a (or_introl (Logic.eq_refl _))).
  rewrite IH=> // q x Hx.
  exact: Hk q x (or_intror Hx).
Qed.

Lemma scale_Enum_proper {A : eqType} p (mu nu : Enum A) :
  mu ==Enum nu -> scale_Enum p mu ==Enum scale_Enum p nu.
Proof. move=> H x. by rewrite !acc_mass_scale H. Qed.

Lemma app_Enum_proper {A : eqType} (mu mu' nu nu' : Enum A) :
  mu ==Enum mu' -> nu ==Enum nu' -> mu ++ nu ==Enum mu' ++ nu'.
Proof. move=> Hmu Hnu x. by rewrite !acc_app Hmu Hnu. Qed.

Lemma bind_Enum_pointwise_proper {A} {B : eqType}
    (mu : Enum A) (k1 k2 : A -> Enum B) :
  (forall a, k1 a ==Enum k2 a) ->
  bind_Enum mu k1 ==Enum bind_Enum mu k2.
Proof.
  move=> Hk. elim: mu=> [|[p a] mu IH] //=.
  apply app_Enum_proper.
  - exact: scale_Enum_proper (Hk a).
  - exact IH.
Qed.

(** Starting position of the continuation block generated by the [i]-th
    entry of an outer enumeration. *)
Fixpoint bind_offset {A B} (mu : Enum A) (k : A -> Enum B)
    (i : nat) : nat :=
  match mu, i with
  | [::], _ => 0
  | _, 0 => 0
  | (_, a) :: tl, i'.+1 => (size (k a) + bind_offset tl k i')%N
  end.

Lemma size_scale_Enum {A} p (mu : Enum A) :
  size (scale_Enum p mu) = size mu.
Proof. by elim: mu=> [|[q a] mu IH] //=; rewrite IH. Qed.

Lemma nth_error_scale_Enum {A} p (mu : Enum A) i q a :
  nth_error mu i = Some (q, a) ->
  nth_error (scale_Enum p mu) i = Some (p * q, a).
Proof.
  elim: mu i=> [|[r x] mu IH] [|i] //=.
  - by move=> H; inversion H; subst.
  - exact: IH.
Qed.

Lemma nth_error_app_right {A} (xs ys : seq A) i y :
  nth_error ys i = Some y ->
  nth_error (xs ++ ys) (size xs + i)%N = Some y.
Proof.
  by elim: xs=> [|x xs IH] //=.
Qed.

Lemma nth_error_app_left {A} (xs ys : seq A) i x :
  nth_error xs i = Some x ->
  nth_error (xs ++ ys) i = Some x.
Proof.
  elim: xs i=> [|y xs IH] [|i] //=.
  exact: IH.
Qed.

Lemma nth_error_scale_Enum_inv {A} p (mu : Enum A) i w a :
  nth_error (scale_Enum p mu) i = Some (w, a) ->
  exists q, nth_error mu i = Some (q, a) /\ w = p * q.
Proof.
  elim: mu i=> [|[q b] mu IH] [|i] //=.
  - move=> H. inversion H; subst. by exists q.
  - exact: IH.
Qed.

Lemma nth_error_app_inv {A} (xs ys : seq A) n z :
  nth_error (xs ++ ys) n = Some z ->
  (Peano.lt n (size xs) /\ nth_error xs n = Some z) \/
  exists j, n = (size xs + j)%N /\ nth_error ys j = Some z.
Proof.
  move=> H.
  destruct (PeanoNat.Nat.lt_ge_cases n (size xs)) as [Hlt|Hge].
  - left. split=> //.
    rewrite -(@nth_error_app1 A xs ys n Hlt). exact H.
  - right. exists (n - size xs)%N. split.
    + change (n = size xs + (n - size xs))%coq_nat.
      rewrite Nat.add_comm. symmetry. apply Nat.sub_add. exact Hge.
    + rewrite -(@nth_error_app2 A xs ys n Hge). exact H.
Qed.

(** Exact position and weight of an entry after flattening an Enum bind. *)
Lemma nth_error_bind_Enum {A B} (mu : Enum A) (k : A -> Enum B)
    i j p a q b :
  nth_error mu i = Some (p, a) ->
  nth_error (k a) j = Some (q, b) ->
  nth_error (bind_Enum mu k) (bind_offset mu k i + j)%N =
    Some (p * q, b).
Proof.
  elim: mu i p a=> [|[r x] mu IH] [|i] p a //=.
  - move=> Houter Hinner. inversion Houter; subst r x.
    apply nth_error_app_left.
    apply nth_error_scale_Enum. exact Hinner.
  - move=> Houter Hinner.
    have Htail := IH i p a Houter Hinner.
    have Happ := @nth_error_app_right (nnQ * B)
      (scale_Enum r (k x)) (bind_Enum mu k)
      (bind_offset mu k i + j)%N (p * q, b) Htail.
    rewrite size_scale_Enum in Happ.
    replace (size (k x) + bind_offset mu k i + j)%N
      with (size (k x) + (bind_offset mu k i + j))%N.
    - exact Happ.
    - apply PeanoNat.Nat.add_assoc.
Qed.

(** Every successful position in a flattened bind comes from an outer entry
    and one entry of its continuation block. *)
Lemma nth_error_bind_Enum_inv {A B} (mu : Enum A) (k : A -> Enum B)
    n w b :
  nth_error (bind_Enum mu k) n = Some (w, b) ->
  exists i j p a q,
    nth_error mu i = Some (p, a) /\
    nth_error (k a) j = Some (q, b) /\
    n = (bind_offset mu k i + j)%N /\ w = p * q.
Proof.
  elim: mu n=> [|[p a] mu IH] n Hnth.
  - destruct n; cbn in Hnth; discriminate.
  - cbn in Hnth.
    move: (nth_error_app_inv Hnth)=> [[Hlt Hhead]|[n' [Hn Htail]]].
    + move: (nth_error_scale_Enum_inv Hhead)=> [q [Hq ->]].
      exists 0%N, n, p, a, q. repeat split=> //.
    + rewrite size_scale_Enum in Hn.
      move: (IH n' Htail)=> [i [j [r [x [q [Hi [Hj [Hoff Hw]]]]]]]].
      exists i.+1, j, r, x, q. repeat split=> //.
      rewrite Hn Hoff /=.
      rewrite addnA. reflexivity.
Qed.
