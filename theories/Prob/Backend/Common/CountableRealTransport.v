(** Countable transport by compact finite cuts with explicit tail capacity.
    Independent real analysis: no probability syntax or measure capability. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra finmap all_classical reals.
From mathcomp Require Import topology normedtype function_spaces.
From PTree.Prob.Backend.Common Require Import FiniteMatching RealTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.TTheory.
Import numFieldNormedType.Exports.
Import ArrowAsProduct.
Local Open Scope ring_scope.

Section Cuts.
Variable R : realType.
Definition transport_prefix (p : nat → R) n := \sum_(i < n) p i.
Definition transport_tail (p : nat → R) mass n := mass - transport_prefix p n.
Definition transport_cut (p : nat → R) mass n (i : nat) :=
  if (i < n)%N then p i else transport_tail p mass n.
Definition transport_cut_edge (T : nat → nat → Prop) n (i j : nat) :=
  (n <= i)%N || (n <= j)%N || asbool (T i j).

Lemma transport_cut_total p mass n :
  \sum_(i < n.+1) transport_cut p mass n i = mass.
Proof.
  rewrite big_ord_recr /= /transport_cut ltnn.
  have HE : (\sum_(i < n) (if (i < n)%N then p i else transport_tail p mass n)) = transport_prefix p n.
  { apply eq_bigr=> i _; by rewrite ltn_ord. }
  by rewrite HE /transport_tail addrCA subrr addr0.
Qed.

Lemma transport_cut_nonnegative p mass n :
  (∀ i, 0 <= p i) → transport_prefix p n <= mass →
  ∀ i, 0 <= transport_cut p mass n i.
Proof.
  intros Hp Hmass i; rewrite /transport_cut; case: (i < n)%N; first exact: Hp.
  by rewrite /transport_tail subr_ge0.
Qed.

Lemma transport_cut_prefix p mass n m : (m <= n)%N →
  \sum_(i < n.+1 | (i < m)%N) transport_cut p mass n i = transport_prefix p m.
Proof.
  intro Hmn; rewrite -(big_ord_widen n.+1) //; last exact: leq_trans Hmn (leqnSn n).
  apply eq_bigr=> i _; rewrite /transport_cut.
  have Hi : (i < n)%N := leq_trans (ltn_ord i) Hmn.
  by rewrite Hi.
Qed.

(** A finite matrix's missing row prefix is bounded by the TOTAL capacity
    outside that prefix. This is the no-escape estimate, before taking limits. *)
Lemma finite_transport_row_tail {X Y : finType} (p : X → R) (q : Y → R)
    (c : X → Y → R) (keep : pred Y) :
  (∀ x y, 0 <= c x y) →
  (∀ x, \sum_y c x y = p x) →
  (∀ y, \sum_x c x y = q y) →
  ∀ x,
    p x - (\sum_y q y - \sum_(y | keep y) q y) <= \sum_(y | keep y) c x y ∧
    \sum_(y | keep y) c x y <= p x.
Proof.
  intros Hc Hr Hcol x.
  have Hpart : \sum_y c x y = \sum_(y | keep y) c x y + \sum_(y | ~~ keep y) c x y.
  { exact: bigID. }
  have HQ : \sum_y q y = \sum_(y | keep y) q y + \sum_(y | ~~ keep y) q y.
  { exact: bigID. }
  have Hle : \sum_(y | ~~ keep y) c x y <= \sum_(y | ~~ keep y) q y.
  { apply ler_sum=> y _; rewrite -(Hcol y) (bigD1 x) //= lerDl.
    apply sumr_ge0=> z _; exact: Hc. }
  split.
  - rewrite HQ addrAC subrr add0r lerBlDr -(Hr x) Hpart lerD2l.
    exact Hle.
  - rewrite -(Hr x) Hpart lerDl; apply sumr_ge0=> y _; exact: Hc.
Qed.

Definition transport_extend n (c : 'I_n.+1 → 'I_n.+1 → R) i j :=
  if (i < n)%N && (j < n)%N then c (inord i) (inord j) else 0.

Lemma transport_extend_prefix n c i m : (i < n)%N → (m <= n)%N →
  \sum_(j < m) transport_extend c i j =
  \sum_(j < n.+1 | (j < m)%N) c (inord i) j.
Proof.
  intros Hi Hmn; rewrite (big_ord_widen n.+1) //; last exact: leq_trans Hmn (leqnSn n).
  apply eq_bigr=> j Hj; rewrite /transport_extend Hi.
  have Hjn : (j < n)%N := leq_trans Hj Hmn.
  rewrite Hjn /=; have HE : inord (val j) = j.
  { apply/val_inj; simpl; by rewrite inordK // ltn_ord. }
  by rewrite HE.
Qed.

Lemma transport_extend_transpose n c i j :
  transport_extend (λ x y : 'I_n.+1, c y x) i j = transport_extend c j i.
Proof. by rewrite /transport_extend andbC. Qed.

Theorem finite_cut_transport (p q : nat → R) mass (T : nat → nat → Prop) n :
  (∀ i, 0 <= p i) → (∀ j, 0 <= q j) →
  transport_prefix p n <= mass → transport_prefix q n <= mass →
  real_transport_hall
    (λ i : 'I_n.+1, transport_cut p mass n i)
    (λ j : 'I_n.+1, transport_cut q mass n j)
    (λ i j : 'I_n.+1, transport_cut_edge T n i j) →
  ∃ w : nat → nat → R,
    (∀ i j, 0 <= w i j ∧ w i j <= mass) ∧
    (∀ i j, ¬ T i j → w i j = 0) ∧
    (∀ i m, (i < n)%N → (m <= n)%N →
      p i - transport_tail q mass m <= transport_prefix (w i) m ∧
      transport_prefix (w i) m <= p i) ∧
    (∀ j m, (j < n)%N → (m <= n)%N →
      q j - transport_tail p mass m <= transport_prefix (λ i, w i j) m ∧
      transport_prefix (λ i, w i j) m <= q j).
Proof.
  intros Hp Hq Hpm Hqm Hall.
  have Hcp := transport_cut_nonnegative Hp Hpm.
  have Hcq := transport_cut_nonnegative Hq Hqm.
  have Htotal : (\sum_(i < n.+1) transport_cut p mass n i) =
      \sum_(j < n.+1) transport_cut q mass n j by rewrite !transport_cut_total.
  destruct (@finite_real_transport R _ _
    (λ i : 'I_n.+1, transport_cut p mass n i)
    (λ j : 'I_n.+1, transport_cut q mass n j)
    (λ i j : 'I_n.+1, transport_cut_edge T n i j)
    (λ i, Hcp i) (λ j, Hcq j) Hall Htotal) as [c [Hc [Hr [Hcol Hs]]]].
  have Hbound i j : c i j <= mass.
  { have Hrow : c i j <= \sum_y c i y.
    { rewrite (bigD1 j) //= lerDl; apply sumr_ge0=> y _; exact: Hc. }
    apply: le_trans Hrow _.
    rewrite Hr.
    have Hle : transport_cut p mass n i <= \sum_(x < n.+1) transport_cut p mass n x.
    { rewrite (bigD1 i) //= lerDl; apply sumr_ge0=> x _; exact: Hcp. }
    by rewrite transport_cut_total in Hle. }
  exists (transport_extend c); split.
  - intros i j; rewrite /transport_extend; case: ((i < n)%N && (j < n)%N).
    + split; [exact: Hc|exact: Hbound].
    + split; first exact: lexx.
      apply: le_trans Hpm; apply sumr_ge0=> x _; exact: Hp.
  - split.
    + intros i j HT; rewrite /transport_extend.
      case Hboth: ((i < n)%N && (j < n)%N); last reflexivity.
      move/andP: Hboth=> [Hi Hj]; apply Hs.
      have Hi' := leq_trans Hi (leqnSn n).
      have Hj' := leq_trans Hj (leqnSn n).
      rewrite /transport_cut_edge (inordK Hi') (inordK Hj').
      rewrite (leqNgt n i) (leqNgt n j) Hi Hj /=; apply/negP=> /asboolP; contradiction.
    + split.
      * intros i m Hi Hmn.
        have H := @finite_transport_row_tail _ _
          (λ i : 'I_n.+1, transport_cut p mass n i)
          (λ j : 'I_n.+1, transport_cut q mass n j) c
          (λ j, (j < m)%N) Hc Hr Hcol (inord i).
        rewrite transport_cut_total (transport_cut_prefix q mass Hmn) /transport_cut inordK in H;
          last exact: leq_trans Hi (leqnSn n).
        rewrite Hi in H.
        rewrite /transport_prefix (transport_extend_prefix c Hi Hmn).
        exact H.
      * intros j m Hj Hmn.
        have H := @finite_transport_row_tail _ _
          (λ j : 'I_n.+1, transport_cut q mass n j)
          (λ i : 'I_n.+1, transport_cut p mass n i) (λ j i, c i j)
          (λ i, (i < m)%N) (λ j i, Hc i j) Hcol Hr (inord j).
        rewrite transport_cut_total (transport_cut_prefix p mass Hmn) /transport_cut inordK in H;
          last exact: leq_trans Hj (leqnSn n).
        rewrite Hj in H.
        have HE : (λ i, transport_extend c i j) = transport_extend (λ y x, c x y) j.
        { apply funext=> i; symmetry; exact: transport_extend_transpose. }
        rewrite HE /transport_prefix (transport_extend_prefix (λ y x, c x y) Hj Hmn).
        exact H.
Qed.
End Cuts.

Local Open Scope classical_set_scope.
Section CountableLimit.
Variable R : realType.
Variables (p q : nat → R) (mass : R) (T : nat → nat → Prop).
Local Notation W := ((nat * nat)%type -> R).
Let row (w : W) i m := transport_prefix (λ j, w (i,j)) m.
Let col (w : W) j m := transport_prefix (λ i, w (i,j)) m.
Let cuts n (w : W) :=
  (∀ i m, (i < n)%N → (m <= n)%N →
    p i - transport_tail q mass m <= row w i m ∧ row w i m <= p i) ∧
  (∀ j m, (j < n)%N → (m <= n)%N →
    q j - transport_tail p mass m <= col w j m ∧ col w j m <= q j) ∧
  (∀ i j, ¬ T i j → w (i,j) = 0).

Lemma countable_row_continuous i m : continuous (λ w : W, row w i m).
Proof. apply transport_continuous_sum=> j; exact: proj_continuous. Qed.
Lemma countable_col_continuous j m : continuous (λ w : W, col w j m).
Proof. apply transport_continuous_sum=> i; exact: proj_continuous. Qed.

Lemma countable_cuts_closed n : closed (cuts n).
Proof.
  apply closedI.
  - apply transport_closed_forall=> i; apply transport_closed_forall=> m.
    apply transport_closed_forall=> Hi; apply transport_closed_forall=> Hm.
    apply closedI.
    + apply (@closed_comp _ _ (λ w : W, row w i m)
        [set x | p i - transport_tail q mass m <= x]);
        [intros w _; exact: countable_row_continuous|exact: closed_ge].
    + apply (@closed_comp _ _ (λ w : W, row w i m) [set x | x <= p i]);
        [intros w _; exact: countable_row_continuous|exact: closed_le].
  - apply closedI.
    + apply transport_closed_forall=> j; apply transport_closed_forall=> m.
      apply transport_closed_forall=> Hj; apply transport_closed_forall=> Hm.
      apply closedI.
      * apply (@closed_comp _ _ (λ w : W, col w j m)
          [set x | q j - transport_tail p mass m <= x]);
          [intros w _; exact: countable_col_continuous|exact: closed_ge].
      * apply (@closed_comp _ _ (λ w : W, col w j m) [set x | x <= q j]);
          [intros w _; exact: countable_col_continuous|exact: closed_le].
    + apply transport_closed_forall=> i; apply transport_closed_forall=> j.
      apply transport_closed_forall=> Hmiss.
      apply (@closed_comp _ _ (λ w : W, w (i,j)) [set x | x = 0]);
        [intros w _; exact: proj_continuous|exact: closed_eq].
Qed.

(** The input is numerical Hall inequalities on finite tail-lumped cuts,
    not a supplied family of plans and not a transport-existence principle. *)
Theorem countable_transport_no_escape :
  (∀ i, 0 <= p i) → (∀ j, 0 <= q j) →
  (∀ n, transport_prefix p n <= mass) →
  (∀ n, transport_prefix q n <= mass) →
  (∀ n, real_transport_hall
    (λ i : 'I_n.+1, transport_cut p mass n i)
    (λ j : 'I_n.+1, transport_cut q mass n j)
    (λ i j : 'I_n.+1, transport_cut_edge T n i j)) →
  ∃ w : nat → nat → R,
    (∀ i j, 0 <= w i j ∧ w i j <= mass) ∧
    (∀ i j, ¬ T i j → w i j = 0) ∧
    (∀ i m, p i - transport_tail q mass m <= transport_prefix (w i) m ∧
      transport_prefix (w i) m <= p i) ∧
    (∀ j m, q j - transport_tail p mass m <= transport_prefix (λ i, w i j) m ∧
      transport_prefix (λ i, w i j) m <= q j).
Proof.
  intros Hp Hq Hpm Hqm Hall.
  pose box : set W := λ w, ∀ z, `[0,mass] (w z).
  have HK : compact box.
  { exact (@tychonoff _ (λ _ : (nat * nat)%type, _) _
      (λ _ : (nat * nat)%type, @segment_compact R 0 mass)). }
  have Hnon : ∀ n, (box `&` cuts n) !=set0.
  { intro n; destruct (finite_cut_transport Hp Hq (Hpm n) (Hqm n) (Hall n))
      as [w [Hw [Hs [Hr Hc]]]].
    exists (λ z, w (fst z) (snd z)); split.
    - intros [i j]; change (is_true (0 <= w i j <= mass)); apply/andP; exact: Hw.
    - split; first exact Hr.
      split; [exact Hc|exact Hs]. }
  have Hnest : ∀ n m, (n <= m)%N -> cuts m `<=` cuts n.
  { intros n m Hnm w [Hr [Hc Hs]]; split.
    - intros i k Hi Hk; exact (Hr i k (leq_trans Hi Hnm) (leq_trans Hk Hnm)).
    - split; last exact Hs.
      intros j k Hj Hk; exact (Hc j k (leq_trans Hj Hnm) (leq_trans Hk Hnm)). }
  destruct (transport_compact_nested HK countable_cuts_closed Hnest Hnon) as [w [Hw HC]].
  exists (λ i j, w (i,j)); split.
  - intros i j; have /andP H := Hw (i,j); exact H.
  - split; first exact (proj2 (proj2 (HC O))).
    split.
    + intros i m; exact (proj1 (HC (maxn i.+1 m)) i m (leq_maxl _ _) (leq_maxr _ _)).
    + intros j m; exact (proj1 (proj2 (HC (maxn j.+1 m))) j m (leq_maxl _ _) (leq_maxr _ _)).
Qed.
End CountableLimit.

Section ExactMarginals.
Variable R : realType.
Definition transport_series (p : nat → R) := sup (range (transport_prefix p)).

Lemma transport_prefix_tight_exact (w : nat → R) p (tail : nat → R) :
  (∀ n, p - tail n <= transport_prefix w n ∧ transport_prefix w n <= p) →
  (∀ eps, 0 < eps → ∃ n, tail n < eps) →
  transport_series w = p.
Proof.
  intros Hbounds Htight.
  have Hupper : transport_series w <= p.
  { apply sup_le_ub.
    - exists (transport_prefix w O); by exists O.
    - apply/ubP=> x [n _ <-]; exact (proj2 (Hbounds n)). }
  have Hterm n : transport_prefix w n <= transport_series w.
  { apply sup_ubound.
    - exists p; apply/ubP=> x [m _ <-]; exact (proj2 (Hbounds m)).
    - by exists n. }
  apply/eqP; rewrite eq_le; apply/andP; split; first exact Hupper.
  apply transport_eps_limit=> k.
  destruct (Htight _ (transport_eps_pos R k)) as [n Hn].
  have Hlo := proj1 (Hbounds n); rewrite lerBlDr in Hlo.
  apply: le_trans Hlo _; apply lerD; [exact: Hterm|exact: ltW].
Qed.

Theorem countable_real_transport (p q : nat → R) mass (T : nat → nat → Prop) :
  (∀ i, 0 <= p i) → (∀ j, 0 <= q j) →
  (∀ n, transport_prefix p n <= mass) →
  (∀ n, transport_prefix q n <= mass) →
  (∀ eps, 0 < eps → ∃ n, transport_tail p mass n < eps) →
  (∀ eps, 0 < eps → ∃ n, transport_tail q mass n < eps) →
  (∀ n, real_transport_hall
    (λ i : 'I_n.+1, transport_cut p mass n i)
    (λ j : 'I_n.+1, transport_cut q mass n j)
    (λ i j : 'I_n.+1, transport_cut_edge T n i j)) →
  ∃ w : nat → nat → R,
    (∀ i j, 0 <= w i j) ∧
    (∀ i j, ¬ T i j → w i j = 0) ∧
    (∀ i, transport_series (w i) = p i) ∧
    (∀ j, transport_series (λ i, w i j) = q j) ∧
    (∀ i m, transport_prefix (w i) m <= p i) ∧
    (∀ j m, transport_prefix (λ i, w i j) m <= q j).
Proof.
  intros Hp Hq Hpm Hqm Hpt Hqt Hall.
  destruct (countable_transport_no_escape Hp Hq Hpm Hqm Hall) as [w [Hw [Hs [Hr Hc]]]].
  exists w; split; first exact (λ i j, proj1 (Hw i j)).
  split; first exact Hs.
  split; first exact (λ i, transport_prefix_tight_exact (Hr i) Hqt).
  split; first exact (λ j, transport_prefix_tight_exact (Hc j) Hpt).
  split; [exact (λ i m, proj2 (Hr i m))|exact (λ j m, proj2 (Hc j m))].
Qed.
End ExactMarginals.
