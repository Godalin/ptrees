(** Role: Atomic normal form and finite-prefix tightness in the independent
    expectation domain. These are proved from evaluator continuity; no
    transportation-existence principle is assumed. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype ssralg ssrnum bigop order reals boolp.
From mathcomp.classical Require Import classical_sets.
From PTree.Prob.Domain Require Import Expectation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section Atomic.
Variable R : realType.

Definition oval_atom (L : OmegaVal R nat) i :=
  oval_eval L (fun j => if j == i then 1 else 0).

Definition oval_prefix (f : nat -> R) n i :=
  if (i < n)%N then f i else 0.

Lemma oval_singleton_test i :
  oval_test (fun j : nat => if j == i then (1 : R) else 0).
Proof. intro j; case: (j == i); [exact: oval_test_one|exact: oval_test_zero]. Qed.

Lemma oval_atom_bounds L i : 0 <= oval_atom L i /\ oval_atom L i <= 1.
Proof. exact (oval_eval_bounds L (oval_singleton_test i)). Qed.

Lemma oval_prefix_test f n : oval_test f -> oval_test (oval_prefix f n).
Proof. intros Hf i; rewrite /oval_prefix; case: (i < n)%N; [exact: Hf|exact: oval_test_zero]. Qed.

Lemma oval_prefix_step f n i :
  oval_prefix f n.+1 i =
  oval_prefix f n i + f n * (if i == n then 1 else 0).
Proof.
  rewrite /oval_prefix ltnS leq_eqVlt.
  case: eqP=> [->|Hne]; first by rewrite ltnn mulr1 add0r.
  by case: (i < n)%N; rewrite mulr0 addr0.
Qed.

Lemma oval_prefix_increasing f : oval_test f ->
  forall n i, oval_prefix f n i <= oval_prefix f n.+1 i.
Proof.
  intros Hf n i; rewrite oval_prefix_step lerDl.
  apply mulr_ge0; [exact (proj1 (Hf n))|].
  case: (i == n); [exact: ler01|exact: lexx].
Qed.

Lemma oval_prefix_sup f : oval_test f ->
  forall i, oval_pointwise_sup (oval_prefix f) i = f i.
Proof.
  intros Hf i; apply/eqP; rewrite eq_le; apply/andP; split.
  - apply oval_sup_le=> n; rewrite /oval_prefix.
    case: (i < n)%N; [exact: lexx|exact (proj1 (Hf i))].
  - have Hb : forall n, oval_prefix f n i <= 1.
    { intro n; exact (proj2 (oval_prefix_test n Hf i)). }
    have := oval_sup_ge i.+1 Hb.
    by rewrite /oval_prefix ltnSn.
Qed.

Lemma oval_prefix_eval (L : OmegaVal R nat) f n : oval_test f ->
  oval_eval L (oval_prefix f n) = \sum_(i < n) oval_atom L i * f i.
Proof.
  intro Hf; induction n as [|n IH].
  - rewrite big_ord0; exact (oval_zero (oval_laws L)).
  - rewrite big_ord_recr /= -IH.
    transitivity (oval_eval L (fun i => oval_prefix f n i +
      f n * (if i == n then 1 else 0))).
    + apply oval_eval_ext=> i; exact: oval_prefix_step.
    + rewrite (oval_add (oval_laws L) (oval_prefix_test n Hf)
        (oval_test_scale (proj1 (Hf n)) (proj2 (Hf n)) (oval_singleton_test n))).
      * rewrite (oval_scale (oval_laws L) (proj1 (Hf n)) (proj2 (Hf n))
          (oval_singleton_test n)) mulrC; reflexivity.
      * intro i; rewrite -oval_prefix_step; exact (proj2 (oval_prefix_test n.+1 Hf i)).
Qed.

(** Countable additivity made concrete: every bounded expectation is the
    supremum of its finite atomic sums, not merely a code/decode factorization. *)
Theorem oval_atomic_representation (L : OmegaVal R nat) f : oval_test f ->
  oval_eval L f = oval_sup (fun n => \sum_(i < n) oval_atom L i * f i).
Proof.
  intro Hf; transitivity (oval_eval L (oval_pointwise_sup (oval_prefix f))).
  - apply oval_eval_ext=> i; symmetry; exact: oval_prefix_sup.
  - rewrite (oval_continuous (oval_laws L) (fun n => oval_prefix_test n Hf)
      (oval_prefix_increasing Hf)).
    apply oval_sup_ext=> n; exact: oval_prefix_eval.
Qed.

Theorem oval_atomic_mass (L : OmegaVal R nat) :
  oval_mass L = oval_sup (fun n => \sum_(i < n) oval_atom L i).
Proof.
  rewrite /oval_mass (oval_atomic_representation L (@oval_test_one R nat)).
  apply oval_sup_ext=> n; apply eq_bigr=> i _; exact: mulr1.
Qed.

Theorem oval_atomic_ext (L M : OmegaVal R nat) :
  (forall i, oval_atom L i = oval_atom M i) -> oval_eq L M.
Proof.
  intros H f Hf; rewrite (oval_atomic_representation L Hf) (oval_atomic_representation M Hf).
  apply oval_sup_ext=> n; apply eq_bigr=> i _; by rewrite H.
Qed.

Lemma oval_prefix_mass_le (L : OmegaVal R nat) n :
  \sum_(i < n) oval_atom L i <= oval_mass L.
Proof.
  have He : \sum_(i < n) oval_atom L i = oval_eval L (oval_prefix (fun _ => 1) n).
  { rewrite (oval_prefix_eval L n (@oval_test_one R nat)); apply eq_bigr=> i _; by rewrite mulr1. }
  rewrite He; apply (oval_mono (oval_laws L) (oval_prefix_test n (@oval_test_one R nat)) (@oval_test_one R nat))=> i.
  exact (proj2 (oval_prefix_test n (@oval_test_one R nat) i)).
Qed.
(** Tightness, including subprobabilities of mass strictly below one. The
    tail is relative to the actual mass, not to an artificially normalized 1. *)
Theorem oval_atomic_tight (L : OmegaVal R nat) eps : 0 < eps ->
  exists n, oval_mass L - \sum_(i < n) oval_atom L i < eps.
Proof.
  intro Heps.
  have Hsup : has_sup (range (fun n => \sum_(i < n) oval_atom L i)).
  { split.
    - exists (\sum_(i < 0%N) oval_atom L i); by exists 0%N.
    - exists (oval_mass L); apply/ubP=> x [n _ <-]; exact: oval_prefix_mass_le. }
  destruct (sup_adherent Heps Hsup) as [x [n _ <-] Hnear].
  exists n; rewrite ltrBlDr addrC.
  rewrite ltrBlDr -/(oval_sup _) -oval_atomic_mass in Hnear; exact Hnear.
Qed.

Theorem oval_atomic_tail (L : OmegaVal R nat) n :
  oval_eval L (fun i => if (n <= i)%N then 1 else 0) =
  oval_mass L - \sum_(i < n) oval_atom L i.
Proof.
  have Ht : oval_test (fun i => if (n <= i)%N then (1 : R) else 0).
  { intro i; case: (n <= i)%N; [exact: oval_test_one|exact: oval_test_zero]. }
  have Hsplit : forall i, oval_prefix (fun _ => (1 : R)) n i +
      (if (n <= i)%N then 1 else 0) = 1.
  { intro i; rewrite /oval_prefix (leqNgt n i); by case: (i < n)%N; rewrite /= ?addr0 ?add0r. }
  have He : oval_mass L = oval_eval L (oval_prefix (fun _ => 1) n) +
      oval_eval L (fun i => if (n <= i)%N then 1 else 0).
  { rewrite -(oval_add (oval_laws L) (oval_prefix_test n (@oval_test_one R nat)) Ht).
    - apply oval_eval_ext=> i; symmetry; exact: Hsplit.
    - intro i; rewrite Hsplit; exact: lexx. }
  rewrite (oval_prefix_eval L n (@oval_test_one R nat)) in He.
  have Hsum : (\sum_(i < n) oval_atom L i * 1) = \sum_(i < n) oval_atom L i.
  { apply eq_bigr=> i _; exact: mulr1. }
  by rewrite He Hsum addrAC subrr add0r.
Qed.
End Atomic.
