(** Role: Finite real-capacity transport from finite Hall inequalities.
    Pure arithmetic/combinatorics/topology: no probability interface,
    native carrier, FreeOmega syntax, or assumed transport principle. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra finmap all_classical reals.
From mathcomp Require Import topology normedtype function_spaces.
From PTree.Prob.Backend.Common Require Import FiniteMatching FiniteCapacityMatching.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.TTheory.
Import numFieldNormedType.Exports.
Local Open Scope ring_scope.

(** Unequal total capacities are essential for rounding: all source copies
    are matched, while some target capacity may remain unused. *)
Lemma finite_capacity_subtransport {X Y : finType}
    (p : X -> nat) (q : Y -> nat) (edge : X -> Y -> bool) :
  capacity_hall p q edge ->
  exists w : X -> Y -> nat,
    (forall x, \sum_y w x y = p x) /\
    (forall y, (\sum_x w x y <= q y)%N) /\
    (forall x y, (0 < w x y)%N -> edge x y).
Proof.
  intro Hall; destruct (capacity_hall_matching Hall) as [f [Hf Hinj]].
  pose CX := capacity_copies p.
  pose CY := capacity_copies q.
  have Hex : forall i : CX, exists j : CY, (f i == Some j) && edge (tag i) (tag j).
  { intro i; have Hi : i \in [set: CX] by rewrite inE.
    destruct (Hf i Hi) as [j [Hj [_ He]]]; exists j; by rewrite Hj eqxx He. }
  pose g i := xchoose (Hex i).
  have Hg i : f i = Some (g i) /\ edge (tag i) (tag (g i)).
  { have /andP [/eqP H He] := xchooseP (Hex i); by split. }
  have Hgi : injective g.
  { intros i j Hij; apply (Hinj i j); try by rewrite inE.
    by rewrite (proj1 (Hg i)) (proj1 (Hg j)) Hij. }
  pose w x y := #|[set i : CX | (tag i == x) && (tag (g i) == y)]|.
  have Hfiber : forall (Z : finType) (r : Z -> nat) z,
      #|[set i : capacity_copies r | tag i == z]| = r z.
  { intros Z r z; have H := capacity_fiber_card r [set z].
    have HE : [set i : capacity_copies r | tag i \in [set z]] =
        [set i : capacity_copies r | tag i == z].
    { by apply/setP=> i; rewrite !inE. }
    by rewrite HE big_set1 in H. }
  exists w; split.
  - intro x; rewrite -(Hfiber X p x) (finite_card_partition (fun i : CX => tag (g i))).
    apply eq_bigr=> y _; apply eq_card=> i; by rewrite !inE.
  - split.
    + intro y.
      have HE : \sum_x w x y = #|[set i : CX | tag (g i) == y]|.
      { rewrite (finite_card_partition (fun i : CX => tag i)).
        apply eq_bigr=> x _; apply eq_card=> i; by rewrite !inE andbC. }
      rewrite HE -(Hfiber Y q y) -(card_imset _ Hgi).
      apply subset_leq_card; apply/fintype.subsetP=> j /imsetP [i Hi ->].
      by move: Hi; rewrite !inE.
    + intros x y; rewrite /w card_gt0=> /set0Pn [i Hi].
      move: Hi; rewrite inE=> /andP [/eqP Hx /eqP Hy].
      have He := proj2 (Hg i); by rewrite Hx Hy in He.
Qed.

Section Rounding.
Variable R : realType.

Definition transport_floor (x : R) : nat := `|Num.floor x|%N.

Lemma transport_floor_bounds x : 0 <= x ->
  (transport_floor x)%:R <= x /\ x < (transport_floor x).+1%:R.
Proof.
  intro Hx.
  have H0 : (0 <= Num.floor x)%R by rewrite -floor_ge_int.
  have Hl := Rfloor_le x; have Hu := lt_succ_Rfloor x.
  rewrite /Rfloor /transport_floor in Hl Hu *.
  destruct (Num.floor x) as [n|n] eqn:E.
  - split; first exact Hl. by rewrite -addn1 natrD.
  - discriminate H0.
Qed.

Context {X Y : finType} (p : X -> R) (q : Y -> R) (edge : X -> Y -> bool).
Definition real_transport_hall := forall S : {set X},
  \sum_(x in S) p x <= \sum_(y in matching_neighbors edge finset.setT S) q y.

(** For each positive integer denominator, construct an actual supported
    matrix, rounding demand down and capacity up. No equal-total premise. *)
Theorem finite_real_transport_approx (d : nat) :
  (0 < d)%N -> (forall x, 0 <= p x) -> (forall y, 0 <= q y) ->
  real_transport_hall ->
  exists w : X -> Y -> R,
    (forall x y, 0 <= w x y) /\
    (forall x, p x - 1 / d%:R < \sum_y w x y /\ \sum_y w x y <= p x) /\
    (forall y, \sum_x w x y <= q y + 1 / d%:R) /\
    (forall x y, ~~ edge x y -> w x y = 0).
Proof.
  intros Hd Hp Hq Hall.
  have Hdr : (0 : R) < d%:R by rewrite ltr0n.
  have Hd0 : (d%:R : R) != 0 by rewrite gt_eqF.
  pose np x := transport_floor (p x * d%:R).
  pose nq y := (transport_floor (q y * d%:R)).+1.
  have Hpb x := transport_floor_bounds (mulr_ge0 (Hp x) (ltW Hdr)).
  have Hqb y := transport_floor_bounds (mulr_ge0 (Hq y) (ltW Hdr)).
  have Hnat : capacity_hall np nq edge.
  { intro S; rewrite -(@ler_nat R) natr_sum natr_sum.
    apply: le_trans (_ : \sum_(x in S) p x * d%:R <= _).
    - apply ler_sum=> x _; exact (proj1 (Hpb x)).
    - apply: le_trans (_ : \sum_(y in matching_neighbors edge finset.setT S) q y * d%:R <= _).
      + rewrite -!big_distrl; exact (ler_wpM2r (ltW Hdr) (Hall S)).
      + apply ler_sum=> y _; exact (ltW (proj2 (Hqb y))). }
  destruct (finite_capacity_subtransport Hnat) as [c [Hrow [Hcol Hsupp]]].
  exists (fun x y => (c x y)%:R / d%:R); split.
  - intros x y; apply divr_ge0; [exact: ler0n|exact: ltW].
  - split.
    + intro x; rewrite -big_distrl -natr_sum Hrow.
      split.
      * rewrite ltr_pdivlMr // mulrBl divfK // ltrBlDr.
        have H := proj2 (Hpb x); by rewrite -addn1 natrD in H.
      * rewrite ler_pdivrMr //; exact (proj1 (Hpb x)).
    + split.
      * intro y; rewrite -big_distrl -natr_sum ler_pdivrMr // mulrDl divfK //.
        apply: le_trans (_ : (nq y)%:R <= _).
        -- by rewrite ler_nat; apply Hcol.
        -- rewrite /nq -addn1 natrD; apply lerD; [exact (proj1 (Hqb y))|exact: lexx].
      * intros x y Hmiss.
        have Hzero : c x y = 0%N.
        { apply/eqP; rewrite -leqn0 leqNgt; apply/negP=> Hpos.
          have H := Hsupp x y Hpos; by rewrite H in Hmiss. }
        by rewrite Hzero mul0r.
Qed.
End Rounding.

Local Open Scope classical_set_scope.
Import ArrowAsProduct.

Lemma transport_compact_nested (V : topologicalType) (K : set V) (C : nat -> set V) :
  compact K -> (forall n, closed (C n)) ->
  (forall n m, (n <= m)%N -> C m `<=` C n) ->
  (forall n, (K `&` C n) !=set0) ->
  exists x, K x /\ forall n, C n x.
Proof.
  intros HK HC Hnest Hnon.
  pose F := filter_from setT (fun n => K `&` C n).
  have HF : ProperFilter F.
  { apply filter_from_proper.
    - apply filter_from_filter.
      + exists O; exact I.
      + intros n m _ _; exists (maxn n m); first exact I.
        intros x [Hx Hnm]; split; split; try exact Hx.
        * exact (Hnest n (maxn n m) (leq_maxl n m) x Hnm).
        * exact (Hnest m (maxn n m) (leq_maxr n m) x Hnm).
    - intros n _; exact (Hnon n). }
  have HFK : F K.
  { exists O; first exact I. intros x [Hx _]; exact Hx. }
  destruct (HK F HF HFK) as [x [Hx Hcl]]; exists x; split; first exact Hx.
  intro n; apply (HC n); rewrite clusterE in Hcl; apply Hcl.
  exists n; first exact I. intros y [_ Hy]; exact Hy.
Qed.

Section RealTopology.
Variable R : realType.

Definition transport_eps n : R := 1 / n.+1%:R.
Lemma transport_eps_pos n : 0 < transport_eps n.
Proof. by rewrite /transport_eps div1r invr_gt0 ltr0n. Qed.
Lemma transport_eps_antitone n m : (n <= m)%N -> transport_eps m <= transport_eps n.
Proof.
  intro H; rewrite /transport_eps !div1r.
  have Hn : (0 : R) < n.+1%:R by rewrite ltr0n.
  have Hm : (0 : R) < m.+1%:R by rewrite ltr0n.
  rewrite (lef_pV2 Hm Hn) ler_nat; exact H.
Qed.
Lemma transport_eps_small e : 0 < e -> exists n, transport_eps n < e.
Proof.
  intro He; exists (Num.bound e^-1).
  have Hd : (0 : R) < (Num.bound e^-1).+1%:R by rewrite ltr0n.
  rewrite /transport_eps div1r (invf_plt Hd He).
  have Hi : 0 <= e^-1 by rewrite invr_ge0; exact: ltW.
  apply: lt_trans (archi_boundP Hi) _; by rewrite ltr_nat.
Qed.
Lemma transport_eps_limit a b :
  (forall n, a <= b + transport_eps n) -> a <= b.
Proof.
  intro H; rewrite leNgt; apply/negP=> Hba.
  have Hpos : 0 < a - b by rewrite subr_gt0.
  destruct (transport_eps_small Hpos) as [n Hn].
  have Hbad : a < a.
  { apply: le_lt_trans (H n) _; by rewrite ltrBrDl in Hn. }
  by rewrite ltxx in Hbad.
Qed.

Lemma transport_continuous_sum (V : topologicalType) (I : finType) (f : I -> V -> R) :
  (forall i, continuous (f i)) -> continuous (fun v => \sum_i f i v).
Proof.
  intro H.
  have HS : forall s : seq I, continuous (fun v => \sum_(i <- s) f i v).
  { elim=> [|i s IH].
    - have HE : (fun v => \sum_(j <- [::]) f j v) = (fun _ : V => (0 : R)).
      { apply funext=> v; by rewrite big_nil. }
      rewrite HE; exact: cst_continuous.
    - have HE : (fun v => \sum_(j <- i :: s) f j v) =
        (fun v => f i v + \sum_(j <- s) f j v).
      { apply funext=> v; by rewrite big_cons. }
      rewrite HE; intro v; exact (continuousD (H i v) (IH v)). }
  apply HS.
Qed.
End RealTopology.

Lemma transport_closed_forall (V : topologicalType) I (C : I -> set V) :
  (forall i, closed (C i)) -> closed (fun v => forall i, C i v).
Proof.
  intro HC.
  have HE : (fun v => forall i, C i v) = \bigcap_i C i.
  { apply funext=> v; apply propext; split; [intros H i _; exact (H i)|intros H i; exact (H i Logic.I)]. }
  rewrite HE; apply closed_bigI=> i _; exact (HC i).
Qed.

Section RealTransportExistence.
Variable R : realType.
Context {X Y : finType} (p : X -> R) (q : Y -> R) (edge : X -> Y -> bool).
Local Notation W := ((X * Y)%type -> R).
Let rows (w : W) x := \sum_y w (x,y).
Let cols (w : W) y := \sum_x w (x,y).
Let constraints n (w : W) :=
  (forall x, p x - transport_eps R n <= rows w x /\ rows w x <= p x) /\
  (forall y, cols w y <= q y + transport_eps R n) /\
  (forall z, ~~ edge (fst z) (snd z) -> w z = 0).

Lemma transport_rows_continuous x : continuous (fun w : W => rows w x).
Proof. apply transport_continuous_sum=> y; exact: proj_continuous. Qed.
Lemma transport_cols_continuous y : continuous (fun w : W => cols w y).
Proof. apply transport_continuous_sum=> x; exact: proj_continuous. Qed.

Lemma transport_constraints_closed n : closed (constraints n).
Proof.
  apply closedI.
  - apply transport_closed_forall=> x; apply closedI.
    + apply (@closed_comp _ _ (fun w : W => rows w x) [set r | p x - transport_eps R n <= r]);
        [intros w _; exact: transport_rows_continuous|exact: closed_ge].
    + apply (@closed_comp _ _ (fun w : W => rows w x) [set r | r <= p x]);
        [intros w _; exact: transport_rows_continuous|exact: closed_le].
  - apply closedI.
    + apply transport_closed_forall=> y.
      apply (@closed_comp _ _ (fun w : W => cols w y) [set r | r <= q y + transport_eps R n]);
        [intros w _; exact: transport_cols_continuous|exact: closed_le].
    + apply transport_closed_forall=> z; apply transport_closed_forall=> Hz.
      apply (@closed_comp _ _ (fun w : W => w z) [set r | r = 0]);
        [intros w _; exact: proj_continuous|exact: closed_eq].
Qed.

Theorem finite_real_subtransport :
  (forall x, 0 <= p x) -> (forall y, 0 <= q y) -> real_transport_hall p q edge ->
  exists w : X -> Y -> R,
    (forall x y, 0 <= w x y) /\
    (forall x, \sum_y w x y = p x) /\
    (forall y, \sum_x w x y <= q y) /\
    (forall x y, ~~ edge x y -> w x y = 0).
Proof.
  intros Hp Hq Hall.
  pose bound := \sum_x p x.
  pose box : set W := fun w => forall z, `[0, bound] (w z).
  have Hcompact : compact box.
  { have H := @tychonoff _ (fun _ : (X * Y)%type => _) _
      (fun _ : (X * Y)%type => @segment_compact R 0 bound).
    exact H. }
  have Hsum : forall (Z : finType) (f : Z -> R),
      (forall z, 0 <= f z) -> forall z, f z <= \sum_i f i.
  { intros Z f Hf z; rewrite (bigD1 z) //= lerDl; apply sumr_ge0=> i _; exact (Hf i). }
  have Hnon : forall n, (box `&` constraints n) !=set0.
  { intro n; destruct (finite_real_transport_approx (ltn0Sn n) Hp Hq Hall)
      as [w [Hw0 [Hwr [Hwc Hws]]]].
    exists (fun z => w (fst z) (snd z)); split.
    - intros [x y]; change (is_true (0 <= w x y <= bound)).
      apply/andP; split; first exact (Hw0 x y).
      apply: le_trans (@Hsum Y (w x) (Hw0 x) y) _.
      exact (le_trans (proj2 (Hwr x)) (@Hsum X p Hp x)).
    - split.
      + intro x; split; [exact (ltW (proj1 (Hwr x)))|exact (proj2 (Hwr x))].
      + split; [exact Hwc|intros [x y]; exact (Hws x y)]. }
  have Hnest : forall n m, (n <= m)%N -> constraints m `<=` constraints n.
  { intros n m Hnm w [Hr [Hc Hs]]; split.
    - intro x; split; last exact (proj2 (Hr x)).
      apply: le_trans (_ : p x - transport_eps R m <= rows w x); last exact (proj1 (Hr x)).
      by rewrite lerD2l lerNl opprK; apply transport_eps_antitone.
    - split; last exact Hs.
      intro y; apply: le_trans (Hc y) _; rewrite lerD2l; exact: transport_eps_antitone. }
  destruct (transport_compact_nested Hcompact transport_constraints_closed Hnest Hnon)
    as [w [Hw HC]].
  exists (fun x y => w (x,y)); split.
  - intros x y; have /andP [H _] := Hw (x,y); exact H.
  - split.
    + intro x; apply/eqP; rewrite eq_le; apply/andP; split.
      * exact (proj2 (proj1 (HC O) x)).
      * apply transport_eps_limit=> n; rewrite -lerBlDr; exact (proj1 (proj1 (HC n) x)).
    + split.
      * intro y; apply transport_eps_limit=> n; exact (proj1 (proj2 (HC n)) y).
      * intros x y; exact (proj2 (proj2 (HC O)) (x,y)).
Qed.
End RealTransportExistence.

(** Equal total mass makes every target capacity exact. This includes zero
    mass, subprobabilities, and arbitrary finite real masses. *)
Theorem finite_real_transport (R : realType) {X Y : finType}
    (p : X -> R) (q : Y -> R) (edge : X -> Y -> bool) :
  (forall x, 0 <= p x) -> (forall y, 0 <= q y) -> real_transport_hall p q edge ->
  \sum_x p x = \sum_y q y ->
  exists w : X -> Y -> R,
    (forall x y, 0 <= w x y) /\
    (forall x, \sum_y w x y = p x) /\
    (forall y, \sum_x w x y = q y) /\
    (forall x y, ~~ edge x y -> w x y = 0).
Proof.
  intros Hp Hq Hall Htotal.
  destruct (finite_real_subtransport Hp Hq Hall) as [w [Hw [Hr [Hc Hs]]]].
  exists w; split; first exact Hw.
  split; first exact Hr.
  split; last exact Hs.
  have Hsum : \sum_y \sum_x w x y = \sum_x p x.
  { rewrite exchange_big; apply eq_bigr=> x _; exact (Hr x). }
  have Hdiff : \sum_y (q y - \sum_x w x y) = 0.
  { by rewrite sumrB Hsum Htotal subrr. }
  have Hpos : forall y : Y, true -> 0 <= q y - \sum_x w x y.
  { intros y _; rewrite subr_ge0; exact (Hc y). }
  intro y; have Hz := @psumr_eq0P R Y predT (fun y => q y - \sum_x w x y) Hpos Hdiff y isT.
  apply/esym/eqP; by rewrite -subr_eq0 Hz.
Qed.

(** The test-function premise supplies Hall using indicators. Equality of
    total masses is separate, so no implicit normalization is involved. *)
Theorem finite_real_transport_of_tests (R : realType) {X Y : finType}
    (p : X -> R) (q : Y -> R) (edge : X -> Y -> bool) :
  (forall x, 0 <= p x) -> (forall y, 0 <= q y) ->
  (forall f g,
    (forall x, 0 <= f x /\ f x <= 1) ->
    (forall y, 0 <= g y /\ g y <= 1) ->
    (forall x y, edge x y -> f x <= g y) ->
    \sum_x p x * f x <= \sum_y q y * g y) ->
  \sum_x p x = \sum_y q y ->
  exists w : X -> Y -> R,
    (forall x y, 0 <= w x y) /\
    (forall x, \sum_y w x y = p x) /\
    (forall y, \sum_x w x y = q y) /\
    (forall x y, ~~ edge x y -> w x y = 0).
Proof.
  intros Hp Hq Htests Htotal; apply finite_real_transport; auto.
  intro S.
  pose N := matching_neighbors edge finset.setT S.
  pose f x : R := if x \in S then 1 else 0.
  pose g y : R := if y \in N then 1 else 0.
  have Hf : forall x, 0 <= f x /\ f x <= 1.
  { intro x; rewrite /f; case: (x \in S); split; try exact: lexx; exact: ler01. }
  have Hg : forall y, 0 <= g y /\ g y <= 1.
  { intro y; rewrite /g; case: (y \in N); split; try exact: lexx; exact: ler01. }
  have Hfg : forall x y, edge x y -> f x <= g y.
  { intros x y Hxy; rewrite /f; case Hx: (x \in S); last exact (proj1 (Hg y)).
    have Hy : y \in N.
    { apply/matching_neighborsP; split; first by rewrite inE.
      exists x; by split. }
    by rewrite /g Hy. }
  have H := Htests f g Hf Hg Hfg.
  have HL : \sum_x p x * f x = \sum_(x in S) p x.
  { rewrite [RHS]big_mkcond; apply eq_bigr=> x _; rewrite /f.
    by case: (x \in S); rewrite ?mulr0 ?mulr1. }
  have HR : \sum_y q y * g y = \sum_(y in N) q y.
  { rewrite [RHS]big_mkcond; apply eq_bigr=> y _; rewrite /g.
    by case: (y \in N); rewrite ?mulr0 ?mulr1. }
  by rewrite HL HR in H.
Qed.

Corollary finite_real_transport_relation (R : realType) {X Y : finType}
    (p : X -> R) (q : Y -> R) (T : X -> Y -> Prop) :
  (forall x, 0 <= p x) -> (forall y, 0 <= q y) ->
  (forall f g,
    (forall x, 0 <= f x /\ f x <= 1) ->
    (forall y, 0 <= g y /\ g y <= 1) ->
    (forall x y, T x y -> f x <= g y) ->
    \sum_x p x * f x <= \sum_y q y * g y) ->
  \sum_x p x = \sum_y q y ->
  exists w : X -> Y -> R,
    (forall x y, 0 <= w x y) /\
    (forall x, \sum_y w x y = p x) /\
    (forall y, \sum_x w x y = q y) /\
    (forall x y, 0 < w x y -> T x y).
Proof.
  intros Hp Hq Htests Htotal.
  have Htest : forall f g,
      (forall x, 0 <= f x /\ f x <= 1) ->
      (forall y, 0 <= g y /\ g y <= 1) ->
      (forall x y, asbool (T x y) -> f x <= g y) ->
      \sum_x p x * f x <= \sum_y q y * g y.
  { intros f g Hf Hg Hfg; apply Htests; auto.
    intros x y Hxy; apply Hfg; exact/asboolP. }
  destruct (finite_real_transport_of_tests Hp Hq Htest Htotal) as [w [Hw [Hr [Hc Hs]]]].
  exists w; split; first exact Hw.
  split; first exact Hr.
  split; first exact Hc.
  intros x y Hpos; destruct (pselect (T x y)) as [HT|HT]; first exact HT.
  have Hmiss : ~~ asbool (T x y) by apply/negP=> /asboolP.
  by rewrite (Hs x y Hmiss) ltxx in Hpos.
Qed.
