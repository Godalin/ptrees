(** Role: Independent standard-measure adapter for the expectation domain.
    The lifted carrier below is an ordinary measurable space, not free
    probability syntax. No native backend or FreeOmega module is imported. *)
Set Warnings "-notation-overridden,-ambiguous-paths,-redundant-canonical-projection".
(* HB's measurable-space carrier uses its ordinary monomorphic universe;
   the independent expectation domain itself remains universe polymorphic. *)
Local Unset Universe Minimization ToSet.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap.
From mathcomp Require Import boolp classical_sets functions cardinality reals fsbigop.
From mathcomp Require Import ereal topology normedtype sequences numfun measure probability.
From mathcomp Require Import measurable_realfun lebesgue_integral.
From PTree.Prob.Domain Require Import Expectation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.TTheory.
Import numFieldNormedType.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Variant oval_carrier (A : Type) := OVBottom | OVValue (x : A).
Arguments OVBottom {A}.
Arguments OVValue {A} _.
HB.instance Definition _ A := gen_eqMixin (oval_carrier A).
HB.instance Definition _ A := gen_choiceMixin (oval_carrier A).
HB.instance Definition _ A := isPointed.Build (oval_carrier A) OVBottom.
HB.instance Definition _ A := @isMeasurable.Build default_measure_display
  (oval_carrier A) discrete_measurable discrete_measurable0
  discrete_measurableC discrete_measurableU.

Section IndicatorFacts.
Variable R : realType.

Lemma oval_test_indic {A} (U : set A) : oval_test (\1_U : A -> R).
Proof. intro x; rewrite indicE; case: (x \in U); split; by []. Qed.

Lemma oval_indic_mono {A} (U V : set A) :
  U `<=` V -> forall x, (\1_U x : R) <= \1_V x.
Proof.
  intros H x; rewrite !indicE; case HU: (x \in U); last exact: ler0n.
  have HV : x \in V by apply/asboolP; apply H; apply/asboolP.
  by rewrite HV.
Qed.

Lemma oval_indic_union {A} (U V : set A) :
  U `&` V = set0 ->
  forall x, (\1_(U `|` V) x : R) = \1_U x + \1_V x.
Proof.
  move=> Hd x; rewrite !indicE in_setU.
  case HU: (x \in U); case HV: (x \in V); simpl; try by rewrite ?addr0 ?add0r.
  have Hboth : (U `&` V) x by split; apply/asboolP.
  by rewrite Hd in Hboth.
Qed.

Lemma oval_indic_bigcup {A} (F : nat -> set A)
    (Hi : forall n, F n `<=` F n.+1) :
  forall x, (\1_(\bigcup_n F n) x : R) =
    oval_sup (fun n => \1_(F n) x).
Proof.
  intro x; apply/eqP; rewrite eq_le; apply/andP; split.
  - rewrite indicE; case Hmem: (x \in \bigcup_n F n).
    + move/asboolP: Hmem => [n _ Hn].
      have H1 : (\1_(F n) x : R) = 1 by rewrite indicE mem_set.
      rewrite -H1; exact (oval_sup_ge n (fun i => proj2 (oval_test_indic (F i) x))).
    + change (is_true (0 <= oval_sup (fun n => (\1_(F n) x : R)))).
      exact: le_trans (proj1 (oval_test_indic (F 0%nat) x))
        (oval_sup_ge 0%nat (fun i => proj2 (oval_test_indic (F i) x))).
  - apply oval_sup_le=> n; apply oval_indic_mono=> y Hy.
    by exists n.
Qed.
End IndicatorFacts.

Section MeasureConstruction.
Context {d} {T : measurableType d} {R : realType}.
Variable L : OmegaVal R T.

Definition oval_set_measure (U : set T) : \bar R :=
  (oval_eval L (\1_U))%:E.

Lemma oval_set_measure0 : oval_set_measure set0 = 0%:E.
Proof. by rewrite /oval_set_measure indic0 (oval_zero (oval_laws L)). Qed.

Lemma oval_set_measure_ge0 U : (0 <= oval_set_measure U)%E.
Proof. rewrite /oval_set_measure lee_fin; exact (proj1 (oval_eval_bounds L (oval_test_indic R U))). Qed.

Lemma oval_set_measure_additive2 : additive2 oval_set_measure.
Proof.
  move=> U V _ _ Hd.
  have HE := oval_indic_union R Hd.
  rewrite /oval_set_measure -EFinD.
  rewrite (oval_eval_ext L HE).
  congr EFin; apply (oval_add (oval_laws L) (oval_test_indic R U) (oval_test_indic R V)).
  intro x; rewrite -(HE x); exact (proj2 (oval_test_indic R (U `|` V) x)).
Qed.

Lemma oval_set_measure_additive : measure.semi_additive oval_set_measure.
Proof. apply/(additive2P oval_set_measure0); exact oval_set_measure_additive2. Qed.

Lemma oval_set_measure_continuous (F : nat -> set T)
    (Hi : forall n, F n `<=` F n.+1) :
  oval_eval L (\1_(\bigcup_n F n)) =
  oval_sup (fun n => oval_eval L (\1_(F n))).
Proof.
  rewrite (oval_eval_ext L (oval_indic_bigcup R Hi)).
  apply (oval_continuous (oval_laws L)).
  - intro n; exact (oval_test_indic R (F n)).
  - intros n x; exact (oval_indic_mono R (Hi n) x).
Qed.

Lemma oval_set_measure_sigma_additive : semi_sigma_additive oval_set_measure.
Proof.
  move=> F Hmeas Hdisj Hunion.
  pose U n := \big[setU/set0]_(i < n) F i.
  have HU : forall n, U n `<=` U n.+1.
  { intro n; rewrite /U big_ord_recr /=; exact: subsetUl. }
  have Heq : \bigcup_n U n = \bigcup_n F n.
  { apply/seteqP; split.
    - intros x [n _ Hx]; exact (bigsetU_bigcup Hx).
    - intros x [n _ Hnx]; exists n.+1; first exact I.
      exact (bigsetU_sup (ltnSn n) Hnx). }
  have Hbound : forall n, oval_eval L (\1_(U n)) <= 1 :=
    fun n => proj2 (oval_eval_bounds L (oval_test_indic R (U n))).
  have Hinc : nondecreasing_seq (fun n => oval_eval L (\1_(U n))).
  { move=> n m /ssrnat.leP Hnm.
    eapply (@oval_increasing_le R (fun i => oval_eval L (\1_(U i)))); [|exact Hnm].
    intro i; apply (oval_mono (oval_laws L) (oval_test_indic R (U i)) (oval_test_indic R (U i.+1))).
    exact (oval_indic_mono R (HU i)). }
  have Hub : has_ubound (range (fun n => oval_eval L (\1_(U n)))).
  { exists 1; apply/ubP=> x [n _ <-]; exact (Hbound n). }
  have Hcv := nondecreasing_cvgn Hinc Hub.
  have HS : forall n, oval_set_measure (U n) = \sum_(i < n) oval_set_measure (F i).
  { intro n; apply oval_set_measure_additive; try assumption.
    exact: bigsetU_measurable. }
  have Hseq : (fun n => \sum_(0 <= i < n) oval_set_measure (F i)) =
      (fun n => (oval_eval L (\1_(U n)))%:E).
  { apply/funext=> n; by rewrite big_mkord -HS. }
  rewrite Hseq /oval_set_measure -Heq (oval_set_measure_continuous HU).
  apply: cvg_EFin; [exact: nearW|exact Hcv].
Qed.

HB.instance Definition _ := @isMeasure.Build d T R oval_set_measure
  oval_set_measure0 oval_set_measure_ge0 oval_set_measure_sigma_additive.

Lemma oval_set_measure_le1 : (oval_set_measure setT <= 1)%E.
Proof. rewrite /oval_set_measure indicT lee_fin; exact (oval_mass_le1 (oval_laws L)). Qed.
HB.instance Definition _ := @Measure_isSubProbability.Build d T R
  oval_set_measure oval_set_measure_le1.

Definition oval_subprobability : subprobability T R :=
  [the subprobability T R of oval_set_measure].
End MeasureConstruction.

Section FiniteTests.
Context {R : realType} {A : Type} (L : OmegaVal R A).

Lemma oval_eval_sum {I : eqType} (s : seq I) (f : I -> A -> R) :
  (forall i, i \in s -> forall x, 0 <= f i x) ->
  (forall x, \sum_(i <- s) f i x <= 1) ->
  oval_eval L (fun x => \sum_(i <- s) f i x) =
  \sum_(i <- s) oval_eval L (f i).
Proof.
  elim: s=> [|a s IH] H0 H1.
  - rewrite big_nil; transitivity (oval_eval L (fun _ => 0));
      [apply oval_eval_ext=> x; by rewrite big_nil|exact (oval_zero (oval_laws L))].
  - have Ha0 : forall x, 0 <= f a x := fun x => H0 a (mem_head a s) x.
    have Hs0 : forall i, i \in s -> forall x, 0 <= f i x.
    { intros i Hi; apply H0; by rewrite in_cons Hi orbT. }
    have Hsum0 : forall x, 0 <= \sum_(i <- s) f i x.
    { intro x; rewrite big_seq; apply sumr_ge0=> i Hi; exact (Hs0 i Hi x). }
    have Ha : oval_test (f a).
    { intro x; split; first exact (Ha0 x).
      apply: le_trans (_ : f a x + \sum_(i <- s) f i x <= 1).
      - by rewrite lerDl.
      - by move: (H1 x); rewrite big_cons. }
    have Hs : oval_test (fun x => \sum_(i <- s) f i x).
    { intro x; split; first exact (Hsum0 x).
      apply: le_trans (_ : f a x + \sum_(i <- s) f i x <= 1).
      - by rewrite lerDr.
      - by move: (H1 x); rewrite big_cons. }
    transitivity (oval_eval L (fun x => f a x + \sum_(i <- s) f i x)).
    + apply oval_eval_ext=> x; by rewrite big_cons.
    + rewrite (oval_add (oval_laws L) Ha Hs); last by intro x; move: (H1 x); rewrite big_cons.
      rewrite (IH Hs0 (fun x => proj2 (Hs x))) big_cons; reflexivity.
Qed.
End FiniteTests.

Section IntegralRecovery.
Context {d} {T : measurableType d} {R : realType}.
Variable L : OmegaVal R T.
Import HBNNSimple.

Lemma oval_simple_integral (g : {nnsfun T >-> R}) :
  oval_test g ->
  sintegral (oval_set_measure L) g = (oval_eval L g)%:E.
Proof.
  intro Hg.
  pose s := fset_set (range g).
  have Hcoef : forall r, r \in s -> 0 <= r /\ r <= 1.
  { intros r Hr; move: Hr; rewrite /s in_fset_set // inE => -[x _ <-]; exact (Hg x). }
  have HE : forall x, g x = \sum_(r <- s) r * \1_(g @^-1` [set r]) x.
  { intro x; rewrite -fsbig_finite //; exact: fimfunE. }
  have Hnonneg : forall r, r \in s -> forall x, 0 <= r * \1_(g @^-1` [set r]) x.
  { intros r Hr x; apply mulr_ge0; [exact (proj1 (Hcoef r Hr))|exact (proj1 (oval_test_indic R _ x))]. }
  have Hbound : forall x, \sum_(r <- s) r * \1_(g @^-1` [set r]) x <= 1.
  { intro x; rewrite -(HE x); exact (proj2 (Hg x)). }
  rewrite (oval_eval_ext L HE) (oval_eval_sum L Hnonneg Hbound).
  rewrite sintegralE fsbig_finite // sumEFin.
  congr EFin; apply eq_big_seq=> r Hr; symmetry.
  exact (oval_scale (oval_laws L) (proj1 (Hcoef r Hr)) (proj2 (Hcoef r Hr)) (oval_test_indic R _)).
Qed.

(** Recovery is a theorem about MathComp's Lebesgue integral, proved through
    its increasing nonnegative simple-function approximations. *)
Theorem oval_integral_recovery (f : T -> R) :
  oval_test f -> measurable_fun setT (fun x => (f x)%:E) ->
  (\int[oval_set_measure L]_x (f x)%:E)%E = (oval_eval L f)%:E.
Proof.
  intros Hf Hmf.
  pose g := nnsfun_approx measurableT Hmf.
  have Hf0 : forall x, setT x -> (0 <= (f x)%:E)%E.
  { intros x _; rewrite lee_fin; exact (proj1 (Hf x)). }
  have Hg_le : forall n x, g n x <= f x.
  { intros n x; rewrite /g nnsfun_approxE -lee_fin; exact (le_approx n Hf0 I). }
  have Hg : forall n, oval_test (g n).
  { intros n x; split; first exact: fun_ge0.
    exact: le_trans (Hg_le n x) (proj2 (Hf x)). }
  have Hnd : forall x, nondecreasing_seq (fun n => g n x).
  { intros x n m Hnm; apply/lefP; exact (nd_nnsfun_approx measurableT Hmf Hnm). }
  have Hcvg : forall x, (fun n => g n x) @ \oo --> f x.
  { intro x; rewrite /g; under eq_fun do rewrite nnsfun_approxE.
    exact (cvg_approx Hf0 I (ltry (f x))). }
  have Hsup : forall x, f x = oval_sup (fun n => g n x).
  { intro x.
    have Hb : has_ubound (range (fun n => g n x)).
    { exists 1; apply/ubP=> z [n _ <-]; exact (proj2 (Hg n x)). }
    have H1 : limn (fun n => g n x) = f x.
    { exact (cvg_lim (@Rhausdorff R) (FF := eventually_filter) (Hcvg x)). }
    have H2 : limn (fun n => g n x) = oval_sup (fun n => g n x).
    { exact (cvg_lim (@Rhausdorff R) (FF := eventually_filter)
        (nondecreasing_cvgn (Hnd x) Hb)). }
    by rewrite -H1 H2. }
  have HE : oval_eval L f = oval_sup (fun n => oval_eval L (g n)).
  { rewrite (oval_eval_ext L Hsup); apply (oval_continuous (oval_laws L) Hg).
    intros n x; exact (Hnd x n n.+1 (leqnSn n)). }
  have HndL : nondecreasing_seq (fun n => oval_eval L (g n)).
  { intros n m Hnm; apply (oval_mono (oval_laws L) (Hg n) (Hg m)).
    intro x; exact (Hnd x n m Hnm). }
  have HbL : has_ubound (range (fun n => oval_eval L (g n))).
  { exists 1; apply/ubP=> z [n _ <-]; exact (proj2 (oval_eval_bounds L (Hg n))). }
  have HcvL : (fun n => (oval_eval L (g n))%:E) @ \oo --> (oval_eval L f)%:E.
  { rewrite HE; apply: cvg_EFin; [exact: nearW|exact (nondecreasing_cvgn HndL HbL)]. }
  rewrite (@nd_ge0_integral_lim _ _ _ (oval_set_measure L) (fun x => (f x)%:E) g).
  - have Heval : (sintegral (oval_set_measure L) \o g) =
        (fun n => (oval_eval L (g n))%:E).
    { apply/funext=> n; exact (oval_simple_integral (Hg n)). }
    rewrite Heval; exact (cvg_lim (@ereal_hausdorff R)
      (FF := eventually_filter) HcvL).
  - intro x; exact (Hf0 x I).
  - exact Hnd.
  - intro x; apply: cvg_EFin; [exact: nearW|exact (Hcvg x)].
Qed.
End IntegralRecovery.

(** The reverse construction uses a discrete measurable space: every bounded
    test in the domain contract must be measurable. This is a restriction on
    this adapter, not on the polymorphic expectation domain. *)
Section MeasureExpectation.
Context {d} {T : measurableType d} {R : realType}.
Hypothesis Hall : forall U : set T, measurable U.
Variable mu : subprobability T R.

Lemma oval_all_measurable (f : T -> \bar R) : measurable_fun setT f.
Proof. intros _ U HU; exact: Hall. Qed.

Definition measure_oval_eval (f : T -> R) : R :=
  fine (\int[mu]_x (f x)%:E)%E.

Lemma measure_oval_integral_bounds (f : T -> R) : oval_test f ->
  (0 <= \int[mu]_x (f x)%:E <= 1)%E.
Proof.
  intro Hf; apply/andP; split.
  - apply integral_ge0=> x _; rewrite lee_fin; exact (proj1 (Hf x)).
  - eapply le_trans; last exact (@sprobability_setT _ _ _ mu).
    rewrite -(mul1e (mu setT)) -(integral_cst mu measurableT 1%E).
    apply: ge0_le_integral; try exact: measurableT;
      try exact: oval_all_measurable.
    + intros x _; rewrite lee_fin; exact (proj1 (Hf x)).
    + intros x _; by rewrite lee_fin ler01.
    + intros x _; rewrite lee_fin; exact (proj2 (Hf x)).
Qed.

Lemma measure_oval_integral_finite (f : T -> R) : oval_test f ->
  (\int[mu]_x (f x)%:E)%E \is a fin_num.
Proof.
  move=> /measure_oval_integral_bounds /andP[H0 H1].
  rewrite ge0_fin_numE //; exact: le_lt_trans H1 (ltry 1).
Qed.

Lemma measure_oval_evalE f : oval_test f ->
  (measure_oval_eval f)%:E = (\int[mu]_x (f x)%:E)%E.
Proof. intro Hf; rewrite /measure_oval_eval; apply: fineK;
  exact: measure_oval_integral_finite. Qed.

Lemma measure_oval_eval_bounds f : oval_test f ->
  0 <= measure_oval_eval f /\ measure_oval_eval f <= 1.
Proof.
  intro Hf; split; rewrite -lee_fin measure_oval_evalE //;
    have /andP[H0 H1] := measure_oval_integral_bounds Hf; assumption.
Qed.

Lemma measure_oval_eval_mono f g : oval_test f -> oval_test g ->
  (forall x, f x <= g x) -> measure_oval_eval f <= measure_oval_eval g.
Proof.
  intros Hf Hg Hfg; rewrite -lee_fin !measure_oval_evalE //.
  apply: ge0_le_integral; try exact: measurableT;
    try exact: oval_all_measurable.
  - intros x _; rewrite lee_fin; exact (proj1 (Hf x)).
  - intros x _; rewrite lee_fin; exact (proj1 (Hg x)).
  - intros x _; rewrite lee_fin; exact: Hfg.
Qed.

Lemma measure_oval_eval_zero : measure_oval_eval (fun _ => 0) = 0.
Proof. by rewrite /measure_oval_eval integral0. Qed.

Lemma measure_oval_eval_scale p f : 0 <= p -> p <= 1 -> oval_test f ->
  measure_oval_eval (fun x => p * f x) = p * measure_oval_eval f.
Proof.
  intros Hp Hp1 Hf.
  have Hpf := oval_test_scale Hp Hp1 Hf.
  apply: EFin_inj; rewrite measure_oval_evalE // EFinM measure_oval_evalE //.
  under eq_integral do rewrite EFinM.
  apply: ge0_integralZl_EFin; try exact: measurableT;
    try exact: oval_all_measurable; try assumption.
  intros x _; rewrite lee_fin; exact (proj1 (Hf x)).
Qed.

Lemma measure_oval_eval_add f g : oval_test f -> oval_test g ->
  (forall x, f x + g x <= 1) ->
  measure_oval_eval (fun x => f x + g x) =
    measure_oval_eval f + measure_oval_eval g.
Proof.
  intros Hf Hg Hfg.
  apply: EFin_inj.
  rewrite (measure_oval_evalE (oval_test_add Hf Hg Hfg))
    EFinD (measure_oval_evalE Hf) (measure_oval_evalE Hg).
  under eq_integral do rewrite EFinD.
  apply: ge0_integralD; try exact: measurableT;
    try exact: oval_all_measurable.
  - intros x _; rewrite lee_fin; exact (proj1 (Hf x)).
  - intros x _; rewrite lee_fin; exact (proj1 (Hg x)).
Qed.
Lemma measure_oval_eval_continuous (f : nat -> T -> R) :
  (forall n, oval_test (f n)) ->
  (forall n x, f n x <= f n.+1 x) ->
  measure_oval_eval (oval_pointwise_sup f) =
    oval_sup (fun n => measure_oval_eval (f n)).
Proof.
  intros Hf Hi.
  have Hnd x : nondecreasing_seq (fun n => f n x).
  { move=> n m /ssrnat.leP Hnm; exact (@oval_increasing_le R
      (fun i => f i x) (fun i => Hi i x) n m Hnm). }
  have Hcv x : (fun n => (f n x)%:E) @ \oo -->
      (oval_pointwise_sup f x)%:E.
  { apply: cvg_EFin; first exact: nearW.
    apply: nondecreasing_cvgn (Hnd x) _.
    exists 1; apply/ubP=> z [n _ <-]; exact (proj2 (Hf n x)). }
  have Hlim x : limn (fun n => (f n x)%:E) =
      (oval_pointwise_sup f x)%:E.
  { exact (cvg_lim (@ereal_hausdorff R) (FF := eventually_filter) (Hcv x)). }
  have HndE x : nondecreasing_seq (fun n => (f n x)%:E).
  { intros n m Hnm; rewrite lee_fin; exact: Hnd. }
  have HndL : nondecreasing_seq (fun n => measure_oval_eval (f n)).
  { intros n m Hnm; apply (measure_oval_eval_mono (Hf n) (Hf m)).
    intro x; exact: Hnd. }
  have HbL : has_ubound (range (fun n => measure_oval_eval (f n))).
  { exists 1; apply/ubP=> z [n _ <-]; exact (proj2 (measure_oval_eval_bounds (Hf n))). }
  have HcvL : (fun n => (measure_oval_eval (f n))%:E) @ \oo -->
      (oval_sup (fun n => measure_oval_eval (f n)))%:E.
  { apply: cvg_EFin; [exact: nearW|exact (nondecreasing_cvgn HndL HbL)]. }
  apply: EFin_inj; rewrite measure_oval_evalE ?(oval_test_sup Hf) //.
  have HE : (\int[mu]_x (oval_pointwise_sup f x)%:E)%E =
      limn (fun n => (\int[mu]_x (f n x)%:E)%E).
  { under eq_integral do rewrite -Hlim.
    apply: monotone_convergence; try exact: measurableT.
    - intro n; exact: oval_all_measurable.
    - intros n x _; rewrite lee_fin; exact (proj1 (Hf n x)).
    - intros x _; exact: HndE. }
  rewrite HE.
  have Heval : (fun n => (\int[mu]_x (f n x)%:E)%E) =
      (fun n => (measure_oval_eval (f n))%:E).
  { apply/funext=> n; symmetry; exact: measure_oval_evalE. }
  rewrite Heval; exact (cvg_lim (@ereal_hausdorff R)
    (FF := eventually_filter) HcvL).
  Unshelve. exact (oval_test_sup Hf).
Qed.

Definition measure_oval_laws : OmegaValLaws measure_oval_eval.
Proof.
  constructor.
  - exact measure_oval_eval_zero.
  - exact measure_oval_eval_mono.
  - exact measure_oval_eval_scale.
  - exact measure_oval_eval_add.
  - exact (proj2 (measure_oval_eval_bounds (oval_test_one R))).
  - exact measure_oval_eval_continuous.
Defined.

Definition measure_oval : OmegaVal R T :=
  {| oval_eval := measure_oval_eval; oval_laws := measure_oval_laws |}.
End MeasureExpectation.

Section SubprobabilityCorrespondence.
Context {d} {T : measurableType d} {R : realType}.
Hypothesis Hall : forall U : set T, measurable U.

Theorem oval_measure_roundtrip (L : OmegaVal R T) :
  oval_eq (measure_oval Hall (oval_subprobability L)) L.
Proof.
  intros f Hf; change (fine (\int[oval_set_measure L]_x (f x)%:E)%E = oval_eval L f).
  by rewrite oval_integral_recovery //; exact: oval_all_measurable.
Qed.

Theorem measure_oval_roundtrip (mu : subprobability T R) (U : set T) :
  oval_set_measure (measure_oval Hall mu) U = mu U.
Proof.
  rewrite /oval_set_measure /= (measure_oval_evalE Hall mu (oval_test_indic R U)).
  by rewrite integral_indic ?setIT ?setTI ?setIT ?setTI //; exact: Hall.
Qed.

Theorem oval_measure_extensional (L M : OmegaVal R T) :
  oval_eq L M <-> forall U, oval_set_measure L U = oval_set_measure M U.
Proof.
  split.
  - intros H U; rewrite /oval_set_measure (H _ (oval_test_indic R U)); reflexivity.
  - intros H f Hf.
    have Hfun : oval_set_measure L = oval_set_measure M by exact/funext.
    apply: EFin_inj.
    rewrite -(oval_integral_recovery L Hf (oval_all_measurable Hall _))
      -(oval_integral_recovery M Hf (oval_all_measurable Hall _)) Hfun.
    reflexivity.
Qed.
End SubprobabilityCorrespondence.

Section CemeteryCompletion.
Context {R : realType} {A : Type}.
Variable L : OmegaVal R A.

Definition oval_missing_mass : R := 1 - oval_mass L.
Lemma oval_missing_mass_ge0 : 0 <= oval_missing_mass.
Proof. rewrite /oval_missing_mass subr_ge0; exact (oval_mass_le1 (oval_laws L)). Qed.

Definition oval_complete_eval (f : oval_carrier A -> R) : R :=
  oval_eval L (fun x => f (OVValue x)) + oval_missing_mass * f OVBottom.

Definition oval_complete_laws : OmegaValLaws oval_complete_eval.
Proof.
  have Hval (f : oval_carrier A -> R) :
      oval_test f -> oval_test (fun x => f (OVValue x)).
  { intros H x; exact: H. }
  constructor.
  - by rewrite /oval_complete_eval (oval_zero (oval_laws L)) mulr0 addr0.
  - intros f g Hf Hg Hfg; rewrite /oval_complete_eval; apply: lerD.
    + exact (oval_mono (oval_laws L) (Hval _ Hf) (Hval _ Hg) (fun x => Hfg _)).
    + exact (ler_wpM2l oval_missing_mass_ge0 (Hfg OVBottom)).
  - intros p f Hp Hp1 Hf; rewrite /oval_complete_eval
      (oval_scale (oval_laws L) Hp Hp1 (Hval _ Hf)) mulrDr.
    by rewrite !mulrA [oval_missing_mass * p]mulrC.
  - intros f g Hf Hg Hfg; rewrite /oval_complete_eval
      (oval_add (oval_laws L) (Hval _ Hf) (Hval _ Hg) (fun x => Hfg _)) mulrDr.
    exact: addrACA.
  - rewrite /oval_complete_eval mulr1 /oval_missing_mass /oval_mass addrC subrK.
    exact: lexx.
  - intros f Hf Hi; rewrite /oval_complete_eval.
    have Hsub : oval_eval L (fun x => oval_pointwise_sup f (OVValue x)) =
        oval_sup (fun n => oval_eval L (fun x => f n (OVValue x))).
    { exact (oval_continuous (oval_laws L) (fun n => Hval _ (Hf n))
        (fun n x => Hi n (OVValue x))). }
    rewrite Hsub /oval_pointwise_sup -(oval_sup_scale oval_missing_mass_ge0
      (fun n => proj2 (Hf n OVBottom))).
    symmetry; apply: (@oval_sup_add R _ _ 1 oval_missing_mass).
    + intro n; exact (oval_mono (oval_laws L) (Hval _ (Hf n))
        (Hval _ (Hf n.+1)) (fun x => Hi n (OVValue x))).
    + intro n; exact (ler_wpM2l oval_missing_mass_ge0 (Hi n OVBottom)).
    + intro n; exact (proj2 (oval_eval_bounds L (Hval _ (Hf n)))).
    + intro n; have H := ler_wpM2l oval_missing_mass_ge0 (proj2 (Hf n OVBottom)).
      by rewrite mulr1 in H.
Defined.

Definition oval_complete : OmegaVal R (oval_carrier A) :=
  {| oval_eval := oval_complete_eval; oval_laws := oval_complete_laws |}.

Lemma oval_complete_mass : oval_mass oval_complete = 1.
Proof.
  by rewrite /oval_mass /oval_complete /= /oval_complete_eval
    mulr1 /oval_missing_mass /oval_mass addrC subrK.
Qed.

Definition oval_probability_function : set (oval_carrier A) -> \bar R :=
  oval_set_measure oval_complete.
HB.instance Definition _ := Measure.on oval_probability_function.
Lemma oval_probability_setT : oval_probability_function setT = 1%E.
Proof.
  rewrite /oval_probability_function /oval_set_measure.
  have H : (\1_setT : oval_carrier A -> R) = (fun _ => 1).
  { apply/funext=> x; by rewrite indicT. }
  by rewrite H -/(oval_mass oval_complete) oval_complete_mass.
Qed.
HB.instance Definition _ := @Measure_isProbability.Build _ _ _
  oval_probability_function oval_probability_setT.
Definition oval_probability : probability (oval_carrier A) R :=
  [the probability (oval_carrier A) R of oval_probability_function].
End CemeteryCompletion.

Section ProbabilityCorrespondence.
Context {R : realType} {A : Type}.

Lemma oval_carrier_measurable (U : set (oval_carrier A)) : measurable U.
Proof. exact I. Qed.

Definition oval_extend (f : A -> R) (x : oval_carrier A) : R :=
  match x with OVBottom => 0 | OVValue a => f a end.
Definition oval_bottom_test (x : oval_carrier A) : R :=
  match x with OVBottom => 1 | OVValue _ => 0 end.
Lemma oval_extend_test f : oval_test f -> oval_test (oval_extend f).
Proof. move=> H [|a]; [split; [exact: lexx|exact: ler01]|exact: H]. Qed.
Lemma oval_bottom_test_bounded : oval_test oval_bottom_test.
Proof. move=> [|a]; split; try exact: lexx; exact: ler01. Qed.

Definition probability_oval (p : probability (oval_carrier A) R) : OmegaVal R A :=
  oval_bind (measure_oval oval_carrier_measurable p)
    (fun x => match x with OVBottom => oval_bottom R | OVValue a => oval_ret R a end).

Lemma probability_oval_eval (p : probability (oval_carrier A) R) f :
  oval_eval (probability_oval p) f =
    measure_oval_eval p (oval_extend f).
Proof.
  change (measure_oval_eval p (fun x =>
    oval_eval (match x with OVBottom => oval_bottom R | OVValue a => oval_ret R a end) f)
    = measure_oval_eval p (oval_extend f)).
  congr (measure_oval_eval p _); apply/funext=> x; case: x=> [|a]; reflexivity.
Qed.

Theorem oval_probability_integral (L : OmegaVal R A) f : oval_test f ->
  (\int[oval_probability L]_x (oval_extend f x)%:E)%E = (oval_eval L f)%:E.
Proof.
  intro Hf; rewrite /oval_probability /oval_probability_function
    (oval_integral_recovery (oval_complete L) (oval_extend_test Hf)
      (oval_all_measurable oval_carrier_measurable _)).
  by rewrite /oval_complete /= /oval_complete_eval /oval_extend mulr0 addr0.
Qed.

Theorem oval_probability_roundtrip (L : OmegaVal R A) :
  oval_eq (probability_oval (oval_probability L)) L.
Proof.
  intros f Hf; rewrite probability_oval_eval /measure_oval_eval
    (oval_probability_integral L Hf); reflexivity.
Qed.

Theorem oval_probability_bottom (L : OmegaVal R A) :
  oval_probability L [set OVBottom] = (1 - oval_mass L)%:E.
Proof.
  change ((oval_complete_eval L (\1_[set OVBottom]))%:E = (1 - oval_mass L)%:E).
  have Hval : (fun a : A => (\1_[set OVBottom] (OVValue a) : R)) = (fun _ => 0).
  { apply/funext=> a; rewrite indicE.
    have H : OVValue a \notin [set OVBottom].
    { apply/asboolPn=> H; discriminate H. }
    by rewrite (negbTE H). }
  have Hb : (\1_[set (@OVBottom A)] OVBottom : R) = 1.
  { by rewrite indicE mem_set. }
  by rewrite /oval_complete_eval Hval Hb (oval_zero (oval_laws L))
    mulr1 add0r.
Qed.

Definition oval_values (U : set A) : set (oval_carrier A) :=
  fun x => match x with OVBottom => False | OVValue a => U a end.

Theorem oval_probability_values (L : OmegaVal R A) (U : set A) :
  oval_probability L (oval_values U) = (oval_eval L (\1_U))%:E.
Proof.
  change ((oval_complete_eval L (\1_(oval_values U)))%:E = (oval_eval L (\1_U))%:E).
  have Hval : (fun a : A => (\1_(oval_values U) (OVValue a) : R)) = \1_U.
  { apply/funext=> a; rewrite !indicE; congr (_%:R); apply/propext; reflexivity. }
  have Hb : (\1_(oval_values U) OVBottom : R) = 0.
  { rewrite indicE; have H : OVBottom \notin oval_values U by apply/asboolPn.
    by rewrite (negbTE H). }
  by rewrite /oval_complete_eval Hval Hb mulr0 addr0.
Qed.

(** For a total evaluator, the bottom indicator is forced to carry exactly
    the mass not carried by values. This is what makes the inverse unique. *)
Lemma oval_complete_restrict (J : OmegaVal R (oval_carrier A)) :
  oval_mass J = 1 ->
  forall f, oval_test f ->
  oval_eval J f =
    oval_eval J (oval_extend (fun a => f (OVValue a))) +
    (1 - oval_eval J (oval_extend (fun _ => 1))) * f OVBottom.
Proof.
  intros Hmass f Hf.
  have Hval : oval_test (fun a => f (OVValue a)) by intro a; exact: Hf.
  have Hsplit : forall g : oval_carrier A -> R,
    g = (fun x => oval_extend (fun a => g (OVValue a)) x +
      g OVBottom * oval_bottom_test x).
  { intro g; apply/funext=> x; case: x=> [|a]; by rewrite /oval_extend /oval_bottom_test
      ?mulr1 ?mulr0 ?add0r ?addr0. }
  have Hsum : forall x, oval_extend (fun a => f (OVValue a)) x +
      f OVBottom * oval_bottom_test x <= 1.
  { intro x; rewrite -(congr1 (fun h => h x) (Hsplit f)); exact (proj2 (Hf x)). }
  have Heq : oval_eval J f =
      oval_eval J (oval_extend (fun a => f (OVValue a))) +
      f OVBottom * oval_eval J oval_bottom_test.
  { rewrite {1}(Hsplit f) (oval_add (oval_laws J) (oval_extend_test Hval)
      (oval_test_scale (proj1 (Hf OVBottom)) (proj2 (Hf OVBottom))
        oval_bottom_test_bounded) Hsum).
    by rewrite (oval_scale (oval_laws J) (proj1 (Hf OVBottom))
      (proj2 (Hf OVBottom)) oval_bottom_test_bounded). }
  have Htotal : oval_eval J (oval_extend (fun _ => 1)) +
      oval_eval J oval_bottom_test = 1.
  { rewrite -(oval_add (oval_laws J) (oval_extend_test (oval_test_one R))
      oval_bottom_test_bounded).
    - rewrite -Hmass; apply oval_eval_ext=> x; case: x=> [|a]; by rewrite /= ?addr0 ?add0r.
    - move=> [|a]; by rewrite /= ?addr0 ?add0r. }
  have Hb : oval_eval J oval_bottom_test =
      1 - oval_eval J (oval_extend (fun _ => 1)).
  { have H := congr1 (fun z => z - oval_eval J (oval_extend (fun _ => 1))) Htotal.
    by rewrite addrAC subrr add0r in H. }
  by rewrite Heq Hb mulrC.
Qed.

Theorem probability_oval_roundtrip (p : probability (oval_carrier A) R) U :
  oval_probability (probability_oval p) U = p U.
Proof.
  pose J := measure_oval oval_carrier_measurable p.
  have Hmass : oval_mass J = 1.
  { rewrite /J /oval_mass /measure_oval /= /measure_oval_eval
      integral_cst // mul1e.
    change (fine (p setT) = 1).
    exact (congr1 fine (probability_setT p)). }
  have Heq : oval_eq (oval_complete (probability_oval p)) J.
  { intros f Hf; rewrite /oval_complete /= /oval_complete_eval
      /oval_missing_mass /oval_mass !probability_oval_eval.
    symmetry; exact (oval_complete_restrict Hmass Hf). }
  change (oval_set_measure (oval_complete (probability_oval p)) U = p U).
  rewrite (proj1 (oval_measure_extensional oval_carrier_measurable _ _) Heq U).
  exact (measure_oval_roundtrip oval_carrier_measurable p U).
Qed.
End ProbabilityCorrespondence.
