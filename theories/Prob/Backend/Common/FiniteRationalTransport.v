(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype choice ssrnat seq fintype finset bigop ssralg ssrnum ssrint order rat.
Require Import PTree.Prob.Backend.Common.FiniteMatching PTree.Prob.Backend.Common.FiniteCapacityMatching.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

(** Clear denominators by a PROVED finite common scale.  Clients need
    not supply a rationality/transport oracle. *)
Lemma nonnegative_rat_nat_scale (q : rat) : 0 <= q ->
  exists d n : nat, (0 < d)%N /\ q * d%:R = n%:R.
Proof.
  case: (ratP q)=> [z d Hcop]. case: z Hcop=> [n|n] Hcop Hq.
  - exists d.+1, n. split; [exact: ltn0Sn|].
    apply divfK. by rewrite pnatr_eq0.
  - have Hden : (0 : rat) < d.+1%:R by rewrite ltr0n.
    have Hneg : (-(n.+1%:R) / d.+1%:R : rat) < 0.
    { by rewrite ltr_pdivrMr // mul0r oppr_lt0 ltr0n. }
    have Hbad := lt_le_trans Hneg Hq. by rewrite ltxx in Hbad.
Qed.

Lemma rational_list_common_scale (values : seq rat) :
  (forall q, q \in values -> 0 <= q) ->
  exists d : nat, (0 < d)%N /\
    forall q, q \in values -> exists n : nat, q * d%:R = n%:R.
Proof.
  elim: values=> [|q qs IH] Hpos.
  - exists 1%nat. split; [reflexivity|]. by intros r; rewrite in_nil.
  - have Hq : 0 <= q by apply Hpos; rewrite in_cons eqxx.
    destruct (nonnegative_rat_nat_scale Hq) as [b [a [Hb Ha]]].
    have Htail : forall r, r \in qs -> 0 <= r.
    { intros r Hr. apply Hpos. by rewrite in_cons Hr orbT. }
    destruct (IH Htail) as [d [Hd Hscale]].
    exists (b * d)%N. split; [by rewrite muln_gt0 Hb Hd|].
    intros r. rewrite in_cons=> /orP [/eqP ->|Hr].
    + exists (a * d)%N. by rewrite !natrM mulrA Ha.
    + destruct (Hscale r Hr) as [n Hn]. exists (n * b)%N.
      by rewrite natrM [b%:R * d%:R]mulrC mulrA Hn natrM.
Qed.

Theorem rational_finite_common_scale {X : finType} (p : X -> rat) :
  (forall x, 0 <= p x) ->
  exists (d : nat) (n : X -> nat), (0 < d)%N /\ forall x, p x * d%:R = (n x)%:R.
Proof.
  intro Hp.
  have Hlist : forall r, r \in [seq p x | x <- enum X] -> 0 <= r.
  { move=> r /mapP [x _ ->]. exact (Hp x). }
  destruct (rational_list_common_scale Hlist) as [d [Hd Hscale]].
  have Hex : forall x, exists n : nat, p x * d%:R == n%:R.
  { intro x. have Hin : p x \in [seq p x | x <- enum X].
    { apply/mapP. exists x=> //; by rewrite mem_enum. }
    destruct (Hscale (p x) Hin) as [n Hn]. exists n. by rewrite Hn. }
  exists d, (fun x => xchoose (Hex x)). split=> //.
  intro x. exact (eqP (xchooseP (Hex x))).
Qed.

Lemma rational_scaled_sum {X : finType} (p : X -> rat) (n : X -> nat) d (P : pred X) :
  (forall x, p x * d%:R = (n x)%:R) ->
  (\sum_(x | P x) p x) * d%:R = (\sum_(x | P x) n x)%:R.
Proof.
  intro H. rewrite big_distrl natr_sum. apply eq_bigr=> x _. exact (H x).
Qed.

Section RationalTransport.
Context {X Y : finType} (p : X -> rat) (q : Y -> rat) (edge : X -> Y -> bool).

Definition rational_hall : Prop := forall S : {set X},
  \sum_(x in S) p x <= \sum_(y in matching_neighbors edge setT S) q y.

(** A finite rational joint matrix with exact marginals.  No total-mass
    one requirement: the construction also handles subprobabilities and
    the zero measure. *)
Theorem finite_rational_transport :
  (forall x, 0 <= p x) -> (forall y, 0 <= q y) ->
  rational_hall -> \sum_x p x = \sum_y q y ->
  exists w : X -> Y -> rat,
    (forall x y, 0 <= w x y) /\
    (forall x, \sum_y w x y = p x) /\
    (forall y, \sum_x w x y = q y) /\
    (forall x y, 0 < w x y -> edge x y).
Proof.
  intros Hp Hq Hall Htotal.
  pose (both := fun z : (X + Y)%type => match z with inl x => p x | inr y => q y end).
  have Hboth : forall z, 0 <= both z by intros [x|y]; [apply Hp|apply Hq].
  destruct (rational_finite_common_scale Hboth) as [d [counts [Hd Hscale]]].
  pose (np := fun x => counts (inl x)).
  pose (nq := fun y => counts (inr y)).
  have Hpscale : forall x, p x * d%:R = (np x)%:R := fun x => Hscale (inl x).
  have Hqscale : forall y, q y * d%:R = (nq y)%:R := fun y => Hscale (inr y).
  have Hdr : (0 : rat) < d%:R by rewrite ltr0n.
  have Hdnz : (d%:R : rat) != 0 by rewrite gt_eqF.
  have Hnat : capacity_hall np nq edge.
  { intro S.
    have Hreal : ((\sum_(x in S) np x)%:R : rat) <=
        (\sum_(y in matching_neighbors edge setT S) nq y)%:R.
    { rewrite -(rational_scaled_sum [in S] Hpscale)
        -(rational_scaled_sum [in matching_neighbors edge setT S] Hqscale).
      rewrite (ler_pM2r Hdr). exact (Hall S). }
    by move: Hreal; rewrite ler_nat. }
  have Hntotal : \sum_x np x = \sum_y nq y.
  { have Hreal : ((\sum_x np x)%:R : rat) = (\sum_y nq y)%:R.
    { rewrite -(rational_scaled_sum predT Hpscale)
        -(rational_scaled_sum predT Hqscale) Htotal. reflexivity. }
    apply/eqP. by move/eqP: Hreal; rewrite eqr_nat. }
  destruct (finite_capacity_transport Hnat Hntotal) as [c [Hrows [Hcols Hsupport]]].
  exists (fun x y => (c x y)%:R / d%:R). split.
  - intros x y. apply divr_ge0; [exact: ler0n|exact (ltW Hdr)].
  - split.
    + intro x. rewrite -big_distrl -natr_sum Hrows.
      change ((np x)%:R / d%:R = p x).
      by rewrite -(Hpscale x) mulfK.
    + split.
      * intro y. rewrite -big_distrl -natr_sum Hcols.
        change ((nq y)%:R / d%:R = q y).
        by rewrite -(Hqscale y) mulfK.
      * intros x y Hpositive. apply Hsupport.
        have Hnonzero : c x y != 0%N.
        { apply/eqP=> Hz. rewrite Hz mul0r ltxx in Hpositive. discriminate. }
        by rewrite lt0n Hnonzero.
Qed.

(** Bounded test comparison supplies all Hall inequalities.  This is the
    finite endpoint to be connected to the proved quotient test model. *)
Theorem finite_rational_transport_of_tests :
  (forall x, 0 <= p x) -> (forall y, 0 <= q y) ->
  (forall (f : X -> rat) (g : Y -> rat),
    (forall x, 0 <= f x /\ f x <= 1) ->
    (forall y, 0 <= g y /\ g y <= 1) ->
    (forall x y, edge x y -> f x <= g y) ->
    \sum_x p x * f x <= \sum_y q y * g y) ->
  \sum_x p x = \sum_y q y ->
  exists w : X -> Y -> rat,
    (forall x y, 0 <= w x y) /\
    (forall x, \sum_y w x y = p x) /\
    (forall y, \sum_x w x y = q y) /\
    (forall x y, 0 < w x y -> edge x y).
Proof.
  intros Hp Hq Htest Htotal. apply finite_rational_transport; [exact Hp|exact Hq| |exact Htotal].
  intro S.
  pose (f := fun x => if x \in S then (1 : rat) else 0).
  pose (g := fun y => if y \in matching_neighbors edge setT S then (1 : rat) else 0).
  have Hf : forall x, 0 <= f x /\ f x <= 1.
  { intro x. rewrite /f. case: (x \in S); split; try exact: lexx; exact: ler01. }
  have Hg : forall y, 0 <= g y /\ g y <= 1.
  { intro y. rewrite /g. case: (y \in matching_neighbors edge setT S);
      split; try exact: lexx; exact: ler01. }
  have Hfg : forall x y, edge x y -> f x <= g y.
  { intros x y Hxy. rewrite /f. case Hx: (x \in S).
    - have Hy : y \in matching_neighbors edge setT S.
      { apply/matching_neighborsP. split; [by rewrite inE|]. exists x. by split. }
      by rewrite /g Hy.
    - exact (proj1 (Hg y)). }
  have H := Htest f g Hf Hg Hfg.
  have HL : \sum_x p x * f x = \sum_(x in S) p x.
  { rewrite [RHS]big_mkcond. apply eq_bigr=> x _. rewrite /f.
    by case: (x \in S); rewrite ?mulr1 ?mulr0. }
  have HR : \sum_y q y * g y = \sum_(y in matching_neighbors edge setT S) q y.
  { rewrite [RHS]big_mkcond. apply eq_bigr=> y _. rewrite /g.
    by case: (y \in matching_neighbors edge setT S); rewrite ?mulr1 ?mulr0. }
  by rewrite HL HR in H.
Qed.
End RationalTransport.
