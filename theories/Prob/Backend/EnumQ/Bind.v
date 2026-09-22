(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".

Require Import List Lia Lra PeanoNat Arith.

From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat ssralg rat ssrint.

Require Import PTree.Prob.Backend.Common.RatSubTypes PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Map.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import EnumQ.
Import RatSubTypes.
Import GRing.Theory.
#[local] Open Scope ring_scope.
#[local] Open Scope order_scope.

Lemma bind_EnumQ_app {A B}
    (mu nu : EnumQ A) (k : A -> EnumQ B) :
  bind_EnumQ (mu ++ nu) k =
  bind_EnumQ mu k ++ bind_EnumQ nu k.
Proof.
  elim: mu => [//=|[p a] mu IH] //=.
  by rewrite IH catA.
Qed.

Fixpoint enumQ_weightQ {A} (f : A -> rat) (mu : EnumQ A) : rat :=
  if mu is h :: tl then Qval (fst h) * f (snd h) + enumQ_weightQ f tl else 0.

Lemma enumQ_weightQ_filter_split {A : eqType} (f : A -> rat)
    (mu : EnumQ A) a :
  enumQ_weightQ f mu = Qval (acc_mass a mu) * f a +
    enumQ_weightQ f [seq h <- mu | snd h != a].
Proof.
  revert mu.
  refine (list_ind (fun mu => enumQ_weightQ f mu =
    Qval (acc_mass a mu) * f a +
    enumQ_weightQ f [seq h <- mu | snd h != a]) _ _).
  - by rewrite /= mul0r add0r.
  - intros [p x] tl IH. cbn [enumQ_weightQ filter].
    rewrite acc_mass_cons.
    destruct (x == a) eqn:Hxa.
    + move/eqP: Hxa=> Hxa. subst x.
      cbn. rewrite IH.
      rewrite eq_refl /=.
      change (Qval p * f a +
        (Qval (acc_mass a tl) * f a +
          enumQ_weightQ f [seq h <- tl | snd h != a]) =
        (Qval (acc_mass a tl) + Qval p) * f a +
          enumQ_weightQ f [seq h <- tl | snd h != a]).
      rewrite mulrDl !addrA.
      congr (_ + _). exact: addrC.
    + rewrite Hxa /=.
      rewrite IH.
      rewrite GRing.addr0.
      exact: addrCA.
Qed.

Lemma enumQ_weightQ_zero {A : eqType} (f : A -> rat) (mu : EnumQ A) :
  (forall a, acc_mass a mu = 0) -> enumQ_weightQ f mu = 0.
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

Lemma enumQ_weightQ_proper {A : eqType} (f : A -> rat)
    (mu nu : EnumQ A) :
  mu ==EnumQ nu -> enumQ_weightQ f mu = enumQ_weightQ f nu.
Proof.
  move: mu nu. refine (seq_strong_induction (P := fun mu =>
    forall nu, mu ==EnumQ nu ->
      enumQ_weightQ f mu = enumQ_weightQ f nu) _).
  move=> mu IH nu Hmn. destruct mu as [|[p a] tl].
  - symmetry. apply enumQ_weightQ_zero=> x.
    symmetry. move: (Hmn x). cbn. exact.
  -
    rewrite (enumQ_weightQ_filter_split f ((p, a) :: tl) a).
    rewrite (enumQ_weightQ_filter_split f nu a) (Hmn a).
    congr (_ + _). apply IH.
    + apply/ltP. rewrite size_filter /= eq_refl /=.
      apply/ltP. exact: leq_ltn_trans (count_size _ _) (ltnSn _).
    + exact: (enumQ_filter_proper (fun x : A => x != a) Hmn).
Qed.

Lemma acc_mass_scale {A : eqType} (x : A) p (mu : EnumQ A) :
  acc_mass x (scale_EnumQ p mu) = p * acc_mass x mu.
Proof.
  revert p.
  refine (list_ind (fun mu => forall p,
    acc_mass x (scale_EnumQ p mu) = p * acc_mass x mu) _ _ mu).
  - intro p. rewrite /= mulr0. reflexivity.
  - intros [q a] tl IH p.
    change (acc_mass x ((p * q, a) :: scale_EnumQ p tl) =
      p * acc_mass x ((q, a) :: tl)).
    rewrite !acc_mass_cons IH.
    destruct (a == x) eqn:Hax.
    + move/eqP: Hax=> Hax. subst a.
      rewrite !eq_refl -mulrDr. reflexivity.
    + rewrite Hax !addr0. reflexivity.
Qed.

Lemma acc_mass_bind_EnumQ {A} {B : eqType}
    (mu : EnumQ A) (k : A -> EnumQ B) b :
  Qval (acc_mass b (bind_EnumQ mu k)) =
  enumQ_weightQ (fun a => Qval (acc_mass b (k a))) mu.
Proof.
  elim: mu=> [|[p a] mu IH] //=.
  rewrite acc_app acc_mass_scale /=.
  change (Qval (p * acc_mass b (k a) +
    acc_mass b (bind_EnumQ mu k)) =
    Qval p * Qval (acc_mass b (k a)) +
      enumQ_weightQ (fun x => Qval (acc_mass b (k x))) mu).
  change (Qval p * Qval (acc_mass b (k a)) +
    Qval (acc_mass b (bind_EnumQ mu k)) =
    Qval p * Qval (acc_mass b (k a)) +
      enumQ_weightQ (fun x => Qval (acc_mass b (k x))) mu).
  rewrite IH.
  reflexivity.
Qed.

Lemma bind_EnumQ_outer_proper {A B : eqType}
    (mu nu : EnumQ A) (k : A -> EnumQ B) :
  mu ==EnumQ nu -> bind_EnumQ mu k ==EnumQ bind_EnumQ nu k.
Proof.
  move=> Hmn b. apply val_inj. change
    (Qval (acc_mass b (bind_EnumQ mu k)) =
     Qval (acc_mass b (bind_EnumQ nu k))).
  rewrite !acc_mass_bind_EnumQ.
  exact: enumQ_weightQ_proper Hmn.
Qed.

Lemma bind_EnumQ_scale {A B}
    (p : nnQ) (mu : EnumQ A) (k : A -> EnumQ B) :
  bind_EnumQ (scale_EnumQ p mu) k =
  scale_EnumQ p (bind_EnumQ mu k).
Proof.
  elim: mu => [//=|[q a] mu IH] //=.
  by rewrite IH scale_app !scale_scale.
Qed.

Lemma bind_EnumQ_assoc {A B C}
    (mu : EnumQ A) (k : A -> EnumQ B) (h : B -> EnumQ C) :
  bind_EnumQ (bind_EnumQ mu k) h =
  bind_EnumQ mu (fun x => bind_EnumQ (k x) h).
Proof.
  elim: mu => [//=|[p a] mu IH] //=.
  by rewrite bind_EnumQ_app bind_EnumQ_scale IH.
Qed.

Lemma bind_EnumQ_ext {A B}
    (mu : EnumQ A) (k1 k2 : A -> EnumQ B) :
  (forall x, k1 x = k2 x) ->
  bind_EnumQ mu k1 = bind_EnumQ mu k2.
Proof.
  move=> Hk.
  elim: mu => [//=|[p a] mu IH] //=.
  by rewrite Hk IH.
Qed.

Lemma bind_EnumQ_ext_in {A B}
    (mu : EnumQ A) (k1 k2 : A -> EnumQ B) :
  (forall p x, List.In (p, x) mu -> k1 x = k2 x) ->
  bind_EnumQ mu k1 = bind_EnumQ mu k2.
Proof.
  move=> Hk. elim: mu Hk=> [//=|[p a] mu IH] Hk //=.
  rewrite (Hk p a (or_introl (Logic.eq_refl _))).
  rewrite IH=> // q x Hx.
  exact: Hk q x (or_intror Hx).
Qed.

Lemma scale_EnumQ_proper {A : eqType} p (mu nu : EnumQ A) :
  mu ==EnumQ nu -> scale_EnumQ p mu ==EnumQ scale_EnumQ p nu.
Proof. move=> H x. by rewrite !acc_mass_scale H. Qed.

Lemma app_EnumQ_proper {A : eqType} (mu mu' nu nu' : EnumQ A) :
  mu ==EnumQ mu' -> nu ==EnumQ nu' -> mu ++ nu ==EnumQ mu' ++ nu'.
Proof. move=> Hmu Hnu x. by rewrite !acc_app Hmu Hnu. Qed.

Lemma bind_EnumQ_pointwise_proper {A} {B : eqType}
    (mu : EnumQ A) (k1 k2 : A -> EnumQ B) :
  (forall a, k1 a ==EnumQ k2 a) ->
  bind_EnumQ mu k1 ==EnumQ bind_EnumQ mu k2.
Proof.
  move=> Hk. elim: mu=> [|[p a] mu IH] //=.
  apply app_EnumQ_proper.
  - exact: scale_EnumQ_proper (Hk a).
  - exact IH.
Qed.

(** Starting position of the continuation block generated by the [i]-th
    entry of an outer enumeration. *)
Fixpoint bind_offset {A B} (mu : EnumQ A) (k : A -> EnumQ B)
    (i : nat) : nat :=
  match mu, i with
  | [::], _ => 0
  | _, 0 => 0
  | (_, a) :: tl, i'.+1 => (size (k a) + bind_offset tl k i')%N
  end.

Lemma size_scale_EnumQ {A} p (mu : EnumQ A) :
  size (scale_EnumQ p mu) = size mu.
Proof. by elim: mu=> [|[q a] mu IH] //=; rewrite IH. Qed.

Lemma nth_error_scale_EnumQ {A} p (mu : EnumQ A) i q a :
  nth_error mu i = Some (q, a) ->
  nth_error (scale_EnumQ p mu) i = Some (p * q, a).
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

Lemma nth_error_scale_EnumQ_inv {A} p (mu : EnumQ A) i w a :
  nth_error (scale_EnumQ p mu) i = Some (w, a) ->
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

(** Exact position and weight of an entry after flattening an EnumQ bind. *)
Lemma nth_error_bind_EnumQ {A B} (mu : EnumQ A) (k : A -> EnumQ B)
    i j p a q b :
  nth_error mu i = Some (p, a) ->
  nth_error (k a) j = Some (q, b) ->
  nth_error (bind_EnumQ mu k) (bind_offset mu k i + j)%N =
    Some (p * q, b).
Proof.
  elim: mu i p a=> [|[r x] mu IH] [|i] p a //=.
  - move=> Houter Hinner. inversion Houter; subst r x.
    apply nth_error_app_left.
    apply nth_error_scale_EnumQ. exact Hinner.
  - move=> Houter Hinner.
    have Htail := IH i p a Houter Hinner.
    have Happ := @nth_error_app_right (nnQ * B)
      (scale_EnumQ r (k x)) (bind_EnumQ mu k)
      (bind_offset mu k i + j)%N (p * q, b) Htail.
    rewrite size_scale_EnumQ in Happ.
    replace (size (k x) + bind_offset mu k i + j)%N
      with (size (k x) + (bind_offset mu k i + j))%N.
    - exact Happ.
    - apply PeanoNat.Nat.add_assoc.
Qed.

(** Every successful position in a flattened bind comes from an outer entry
    and one entry of its continuation block. *)
Lemma nth_error_bind_EnumQ_inv {A B} (mu : EnumQ A) (k : A -> EnumQ B)
    n w b :
  nth_error (bind_EnumQ mu k) n = Some (w, b) ->
  exists i j p a q,
    nth_error mu i = Some (p, a) /\
    nth_error (k a) j = Some (q, b) /\
    n = (bind_offset mu k i + j)%N /\ w = p * q.
Proof.
  elim: mu n=> [|[p a] mu IH] n Hnth.
  - destruct n; cbn in Hnth; discriminate.
  - cbn in Hnth.
    move: (nth_error_app_inv Hnth)=> [[Hlt Hhead]|[n' [Hn Htail]]].
    + move: (nth_error_scale_EnumQ_inv Hhead)=> [q [Hq ->]].
      exists 0%N, n, p, a, q. repeat split=> //.
    + rewrite size_scale_EnumQ in Hn.
      move: (IH n' Htail)=> [i [j [r [x [q [Hi [Hj [Hoff Hw]]]]]]]].
      exists i.+1, j, r, x, q. repeat split=> //.
      rewrite Hn Hoff /=.
      rewrite addnA. reflexivity.
Qed.
