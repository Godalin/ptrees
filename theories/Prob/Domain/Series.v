(** Role: Direct realization of nonnegative, summable real weights as an
    expectation functional. This is a mathematical series, not free syntax. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype ssralg ssrnum bigop order reals boolp.
From PTree.Prob.Domain Require Import Expectation Countable Coupling Atomic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Series.
Variable R : realType.
Variable w : nat -> R.
Hypothesis w0 : forall i, 0 <= w i.
Hypothesis w1 : forall n, \sum_(i < n) w i <= 1.

Definition oval_weighted_prefix (f : nat -> R) n := \sum_(i < n) w i * f i.
Definition oval_series_eval (f : nat -> R) := oval_sup (oval_weighted_prefix f).

Lemma oval_weighted_prefix_bounds f n : oval_test f ->
  0 <= oval_weighted_prefix f n /\ oval_weighted_prefix f n <= 1.
Proof.
  intro Hf; split.
  - apply sumr_ge0=> i _; exact (mulr_ge0 (w0 i) (proj1 (Hf i))).
  - apply: le_trans (w1 n); apply ler_sum=> i _.
    rewrite -[X in _ <= X]mulr1; exact (ler_wpM2l (w0 i) (proj2 (Hf i))).
Qed.

Lemma oval_weighted_prefix_increasing f : oval_test f ->
  forall n, oval_weighted_prefix f n <= oval_weighted_prefix f n.+1.
Proof.
  intros Hf n; rewrite /oval_weighted_prefix big_ord_recr /= lerDl.
  exact (mulr_ge0 (w0 n) (proj1 (Hf n))).
Qed.

Lemma oval_weighted_prefix_continuous (f : nat -> nat -> R) :
  (forall n, oval_test (f n)) ->
  (forall n i, f n i <= f n.+1 i) ->
  forall m, oval_weighted_prefix (oval_pointwise_sup f) m =
    oval_sup (fun n => oval_weighted_prefix (f n) m).
Proof.
  intros Hf Hi m; induction m as [|m IH].
  - rewrite /oval_weighted_prefix big_ord0.
    transitivity (oval_sup (fun _ => (0 : R))).
    + symmetry; exact: oval_sup_const.
    + apply oval_sup_ext=> n; by rewrite big_ord0.
  - transitivity (oval_weighted_prefix (oval_pointwise_sup f) m +
      w m * oval_pointwise_sup f m).
    { by rewrite /oval_weighted_prefix big_ord_recr. }
    rewrite IH.
    transitivity (oval_sup (fun n => oval_weighted_prefix (f n) m) +
      oval_sup (fun n => w m * f n m)).
    + congr (_ + _); symmetry; exact (oval_sup_scale (w0 m) (fun n => proj2 (Hf n m))).
    + rewrite -(oval_sup_add
        (fun n => _ : oval_weighted_prefix (f n) m <= oval_weighted_prefix (f n.+1) m)
        (fun n => ler_wpM2l (w0 m) (Hi n m))
        (fun n => proj2 (oval_weighted_prefix_bounds m (Hf n)))
        (fun n => _ : w m * f n m <= w m)).
      * apply oval_sup_ext=> n; by rewrite /oval_weighted_prefix big_ord_recr.
      * intro n; apply ler_sum=> i _; exact (ler_wpM2l (w0 i) (Hi n i)).
      * intro n; rewrite -[X in _ <= X]mulr1; exact (ler_wpM2l (w0 m) (proj2 (Hf n m))).
Qed.

Definition oval_series : OmegaVal R nat.
Proof.
  refine (@Build_OmegaVal R nat oval_series_eval _); constructor.
  - transitivity (oval_sup (fun _ => (0 : R))); last exact: oval_sup_const.
    apply oval_sup_ext=> n; apply big1=> i _; exact: mulr0.
  - intros f g Hf Hg Hfg; apply (oval_sup_mono (fun n => proj2 (oval_weighted_prefix_bounds n Hg)))=> n.
    apply ler_sum=> i _; exact (ler_wpM2l (w0 i) (Hfg i)).
  - intros p f Hp Hp1 Hf.
    transitivity (oval_sup (fun n => p * oval_weighted_prefix f n)).
    + apply oval_sup_ext=> n; rewrite /oval_weighted_prefix mulr_sumr.
      apply eq_bigr=> i _; by rewrite mulrCA.
    + exact (oval_sup_scale Hp (fun n => proj2 (oval_weighted_prefix_bounds n Hf))).
  - intros f g Hf Hg Hfg.
    transitivity (oval_sup (fun n => oval_weighted_prefix f n + oval_weighted_prefix g n)).
    + apply oval_sup_ext=> n; rewrite /oval_weighted_prefix -big_split.
      apply eq_bigr=> i _; exact: mulrDr.
    + exact (oval_sup_add (oval_weighted_prefix_increasing Hf) (oval_weighted_prefix_increasing Hg)
        (fun n => proj2 (oval_weighted_prefix_bounds n Hf))
        (fun n => proj2 (oval_weighted_prefix_bounds n Hg))).
  - apply oval_sup_le=> n; exact (proj2 (oval_weighted_prefix_bounds n (@oval_test_one R nat))).
  - intros f Hf Hi.
    transitivity (oval_sup (fun m => oval_sup (fun n => oval_weighted_prefix (f n) m))).
    + apply oval_sup_ext=> m; exact: oval_weighted_prefix_continuous.
    + apply (@oval_sup_swap R _ 1)=> m n; exact (proj2 (oval_weighted_prefix_bounds m (Hf n))).
Defined.
End Series.

Section Realization.
Variable R : realType.

Lemma oval_atoms_summable (L : OmegaVal R nat) n :
  \sum_(i < n) oval_atom L i <= 1.
Proof. exact (le_trans (oval_prefix_mass_le L n) (oval_mass_le1 (oval_laws L))). Qed.

Theorem oval_series_roundtrip (L : OmegaVal R nat) :
  oval_eq (oval_series (fun i => proj1 (oval_atom_bounds L i)) (oval_atoms_summable L)) L.
Proof. intros f Hf; symmetry; exact: oval_atomic_representation. Qed.

Lemma oval_series_concentrated (w : nat -> R) (w0 : forall i, 0 <= w i)
    (w1 : forall n, \sum_(i < n) w i <= 1) P :
  (forall i, w i != 0 -> P i) -> oval_ae (oval_series w0 w1) P.
Proof.
  intros HP f g Hf Hg Hfg; apply oval_sup_ext=> n; apply eq_bigr=> i _.
  destruct (eqVneq (w i) 0) as [Hw|Hw].
  - by rewrite Hw !mul0r.
  - by rewrite (Hfg i (HP i Hw)).
Qed.

(** An enumerated matrix may list an edge more than once: the series sums
    its weights. All weights are real, not necessarily rational. The scalar
    row/column equations suffice to recover full bounded-test marginals. *)
Theorem oval_transport_plan_joint (T : nat -> nat -> Prop)
    (L M : OmegaVal R nat) (edge : nat -> nat * nat) (w : nat -> R)
    (w0 : forall i, 0 <= w i) (w1 : forall n, \sum_(i < n) w i <= 1) :
  (forall x, oval_series_eval w (fun i => if (fst (edge i)) == x then 1 else 0) = oval_atom L x) ->
  (forall y, oval_series_eval w (fun i => if (snd (edge i)) == y then 1 else 0) = oval_atom M y) ->
  (forall i, w i != 0 -> T (fst (edge i)) (snd (edge i))) ->
  oval_joint T L M (oval_bind (oval_series w0 w1) (fun i => oval_ret R (edge i))).
Proof.
  intros Hrow Hcol HT; split.
  - have He : oval_eq
        (oval_bind (oval_series w0 w1) (fun i => oval_ret R (fst (edge i)))) L.
    { apply oval_atomic_ext=> x; exact (Hrow x). }
    exact He.
  - split.
    + have He : oval_eq
          (oval_bind (oval_series w0 w1) (fun i => oval_ret R (snd (edge i)))) M.
      { apply oval_atomic_ext=> y; exact (Hcol y). }
      exact He.
    + intros f g Hf Hg Hfg.
      apply (oval_series_concentrated w0 w1 HT).
      * intro i; exact (Hf (edge i)).
      * intro i; exact (Hg (edge i)).
      * intro i; exact (Hfg (edge i)).
Qed.
End Realization.
