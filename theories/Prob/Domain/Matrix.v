(** Direct countable sums of expectation values and matrix-joint realization.
    This is analysis of nonnegative series, not a new free representation. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import all_ssreflect all_algebra reals boolp.
From PTree.Prob.Domain Require Import Expectation Countable Coupling Atomic Series.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Sum.
Variable R : realType.
Context {A : Type} (c : nat -> OmegaVal R A).
Hypothesis Hmass : forall n, \sum_(i < n) oval_mass (c i) <= 1.
Definition oval_sum_prefix f n := \sum_(i < n) oval_eval (c i) f.

Lemma oval_eval_le_mass {B} (L : OmegaVal R B) f : oval_test f -> oval_eval L f <= oval_mass L.
Proof.
  intro Hf; apply (oval_mono (oval_laws L) Hf (@oval_test_one R B))=> x; exact (proj2 (Hf x)).
Qed.

Lemma oval_sum_prefix_bound f n : oval_test f -> oval_sum_prefix f n <= 1.
Proof.
  intro Hf; apply: le_trans (Hmass n); apply ler_sum=> i _; exact: oval_eval_le_mass.
Qed.
Lemma oval_sum_prefix_increasing f : oval_test f -> forall n,
  oval_sum_prefix f n <= oval_sum_prefix f n.+1.
Proof.
  intros Hf n; rewrite /oval_sum_prefix big_ord_recr /= lerDl.
  exact (proj1 (oval_eval_bounds (c n) Hf)).
Qed.

Lemma oval_sum_prefix_continuous (f : nat -> A -> R) :
  (forall n, oval_test (f n)) -> (forall n x, f n x <= f n.+1 x) ->
  forall m, oval_sum_prefix (oval_pointwise_sup f) m =
    oval_sup (fun n => oval_sum_prefix (f n) m).
Proof.
  intros Hf Hi m; induction m as [|m IH].
  - rewrite /oval_sum_prefix big_ord0.
    transitivity (oval_sup (fun _ => (0 : R))); first symmetry; first exact: oval_sup_const.
    apply oval_sup_ext=> n; by rewrite big_ord0.
  - transitivity (oval_sum_prefix (oval_pointwise_sup f) m + oval_eval (c m) (oval_pointwise_sup f)).
    { by rewrite /oval_sum_prefix big_ord_recr. }
    rewrite IH.
    rewrite (oval_continuous (oval_laws (c m)) Hf Hi).
    rewrite -(oval_sup_add
      (fun n => _ : oval_sum_prefix (f n) m <= oval_sum_prefix (f n.+1) m)
      (fun n => oval_mono (oval_laws (c m)) (Hf n) (Hf n.+1) (Hi n))
      (fun n => oval_sum_prefix_bound m (Hf n))
      (fun n => proj2 (oval_eval_bounds (c m) (Hf n)))).
    + apply oval_sup_ext=> n; by rewrite /oval_sum_prefix big_ord_recr.
    + intro n; apply ler_sum=> i _; exact (oval_mono (oval_laws (c i)) (Hf n) (Hf n.+1) (Hi n)).
Qed.

Definition oval_sum : OmegaVal R A.
Proof.
  refine (@Build_OmegaVal R A (fun f => oval_sup (oval_sum_prefix f)) _); constructor.
  - transitivity (oval_sup (fun _ => (0 : R))); last exact: oval_sup_const.
    apply oval_sup_ext=> n; apply big1=> i _; exact (oval_zero (oval_laws (c i))).
  - intros f g Hf Hg Hfg; apply (oval_sup_mono (fun n => oval_sum_prefix_bound n Hg))=> n.
    apply ler_sum=> i _; exact (oval_mono (oval_laws (c i)) Hf Hg Hfg).
  - intros a f Ha Ha1 Hf.
    transitivity (oval_sup (fun n => a * oval_sum_prefix f n)).
    + apply oval_sup_ext=> n; rewrite /oval_sum_prefix mulr_sumr.
      apply eq_bigr=> i _; exact (oval_scale (oval_laws (c i)) Ha Ha1 Hf).
    + exact (oval_sup_scale Ha (fun n => oval_sum_prefix_bound n Hf)).
  - intros f g Hf Hg Hfg.
    transitivity (oval_sup (fun n => oval_sum_prefix f n + oval_sum_prefix g n)).
    + apply oval_sup_ext=> n; rewrite /oval_sum_prefix -big_split.
      apply eq_bigr=> i _; exact (oval_add (oval_laws (c i)) Hf Hg Hfg).
    + exact (oval_sup_add (oval_sum_prefix_increasing Hf) (oval_sum_prefix_increasing Hg)
        (fun n => oval_sum_prefix_bound n Hf) (fun n => oval_sum_prefix_bound n Hg)).
  - apply oval_sup_le=> n; exact: oval_sum_prefix_bound.
  - intros f Hf Hi.
    transitivity (oval_sup (fun m => oval_sup (fun n => oval_sum_prefix (f n) m))).
    + apply oval_sup_ext=> m; exact: oval_sum_prefix_continuous.
    + exact (@oval_sup_swap R _ 1 (fun m n => oval_sum_prefix_bound m (Hf n))).
Defined.
End Sum.

Section Matrix.
Variable R : realType.

Lemma oval_series_atom (w : nat -> R) (H0 : forall i, 0 <= w i)
    (H1 : forall n, \sum_(i < n) w i <= 1) j :
  oval_atom (oval_series H0 H1) j = w j.
Proof.
  have Hpref n : (\sum_(i < n) w i * (if (i : nat) == j then 1 else 0)) =
      if (j < n)%N then w j else 0.
  { induction n as [|n IH]; first by rewrite big_ord0 ltn0.
    rewrite big_ord_recr /= IH (ltnS j n) (leq_eqVlt j n) (eq_sym j n).
    case Hnj: (n == j).
    - move/eqP: Hnj=> ->; by rewrite ltnn /= mulr1 add0r.
    - by case: (j < n)%N; rewrite /= mulr0 addr0. }
  change (oval_sup (fun n => \sum_(i < n) w i * (if (i : nat) == j then 1 else 0)) = w j).
  apply/eqP; rewrite eq_le; apply/andP; split.
  - apply oval_sup_le=> n; rewrite Hpref; case: (j < n)%N; [exact: lexx|exact: H0].
  - have HB n : (\sum_(i < n) w i * (if (i : nat) == j then 1 else 0)) <= 1.
    { rewrite Hpref; case: (j < n)%N; last exact: ler01.
      apply: le_trans (H1 j.+1); rewrite (bigD1 (Ordinal (ltnSn j))) //= lerDl.
      apply sumr_ge0=> i _; exact: H0. }
    have H := oval_sup_ge j.+1 HB; by rewrite Hpref ltnSn in H.
Qed.

Lemma oval_eval_constant {A} (L : OmegaVal R A) a : 0 <= a -> a <= 1 ->
  oval_eval L (fun _ => a) = a * oval_mass L.
Proof.
  intros Ha Ha1; rewrite -(oval_scale (oval_laws L) Ha Ha1 (@oval_test_one R A)).
  apply oval_eval_ext=> x; by rewrite mulr1.
Qed.

Theorem oval_matrix_joint (T : nat -> nat -> Prop) (L M : OmegaVal R nat)
    (w : nat -> nat -> R) :
  (forall i j, 0 <= w i j) ->
  (forall i j, w i j != 0 -> T i j) ->
  (forall i, oval_sup (fun n => \sum_(j < n) w i j) = oval_atom L i) ->
  (forall j, oval_sup (fun n => \sum_(i < n) w i j) = oval_atom M j) ->
  (forall i n, \sum_(j < n) w i j <= oval_atom L i) ->
  exists J, oval_joint T L M J.
Proof.
  intros H0 HT Hr Hc Hbound.
  have H1 i n : \sum_(j < n) w i j <= 1 :=
    le_trans (Hbound i n) (proj2 (oval_atom_bounds L i)).
  pose row i := oval_series (H0 i) (H1 i).
  pose c i := oval_bind (row i) (fun j => oval_ret R (i,j)).
  have Hmass i : oval_mass (c i) = oval_atom L i.
  { change (oval_sup (fun n => \sum_(j < n) w i j * 1) = oval_atom L i).
    rewrite -Hr; apply oval_sup_ext=> n; apply eq_bigr=> j _; exact: mulr1. }
  have Hsummable n : \sum_(i < n) oval_mass (c i) <= 1.
  { have HE : (\sum_(i < n) oval_mass (c i)) = \sum_(i < n) oval_atom L i.
    { apply eq_bigr=> i _; exact: Hmass. }
    rewrite HE; exact: oval_atoms_summable. }
  exists (oval_sum Hsummable); split.
  - intros f Hf; rewrite (oval_atomic_representation L Hf).
    apply oval_sup_ext=> n; apply eq_bigr=> i _.
    change (oval_eval (row i) (fun _ => f i) = oval_atom L i * f i).
    rewrite (oval_eval_constant (row i) (proj1 (Hf i)) (proj2 (Hf i))) mulrC.
    congr (_ * _); exact (Hmass i).
  - split.
    + have He : oval_eq (oval_bind (oval_sum Hsummable) (fun z => oval_ret R (snd z))) M.
      { apply oval_atomic_ext=> j; change (oval_sup (fun n =>
          \sum_(i < n) oval_atom (row i) j) = oval_atom M j).
        rewrite -Hc; apply oval_sup_ext=> n; apply eq_bigr=> i _; exact: oval_series_atom. }
      exact He.
    + intros f g Hf Hg Hfg; apply oval_sup_ext=> n; apply eq_bigr=> i _.
      apply (oval_series_concentrated (H0 i) (H1 i) (HT i)).
      * intro j; exact (Hf ((i : nat),j)).
      * intro j; exact (Hg ((i : nat),j)).
      * intros j Hij; exact (Hfg ((i : nat),j) Hij).
Qed.
End Matrix.
