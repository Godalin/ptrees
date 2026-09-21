(** One-way external-validation adapter: expectation-domain dual inequalities
    instantiate independent real transport. Not a native backend or API export. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra all_classical reals.
From PTree.Prob.Backend.Common Require Import FiniteMatching RealTransport CountableRealTransport.
From PTree.Prob.Domain Require Import Expectation Coupling Atomic Matrix.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Section DomainTransport.
Variable R : realType.
Definition oval_cut_index n i : 'I_n.+1 :=
  if (i < n)%N then inord i else ord_max.

Lemma oval_cut_index_small n i : (i < n)%N -> val (oval_cut_index n i) = i.
Proof.
  intro Hi; rewrite /oval_cut_index Hi /= inordK //; exact: leq_trans Hi (leqnSn n).
Qed.

Lemma oval_cut_eval (L : OmegaVal R nat) n (f : 'I_n.+1 -> R) : oval_test f ->
  oval_eval L (fun i => f (oval_cut_index n i)) =
  \sum_(i < n.+1) transport_cut (oval_atom L) (oval_mass L) n i * f i.
Proof.
  intro Hf.
  pose test i := f (oval_cut_index n i).
  pose tail i : R := if (n <= i)%N then 1 else 0.
  have Htest : oval_test test := fun i => Hf (oval_cut_index n i).
  have Htail : oval_test tail.
  { intro i; rewrite /tail; case: (n <= i)%N; [exact: oval_test_one|exact: oval_test_zero]. }
  have HE i : oval_prefix test n i + f ord_max * tail i = test i.
  { rewrite /oval_prefix /test /tail /oval_cut_index (leqNgt n i).
    by case: (i < n)%N; rewrite /= ?mulr0 ?addr0 ?mulr1 ?add0r. }
  have HL : oval_eval L test = oval_eval L (oval_prefix test n) +
      f ord_max * oval_eval L tail.
  { rewrite -(oval_scale (oval_laws L) (proj1 (Hf ord_max)) (proj2 (Hf ord_max)) Htail).
    rewrite -(oval_add (oval_laws L) (oval_prefix_test n Htest)
      (oval_test_scale (proj1 (Hf ord_max)) (proj2 (Hf ord_max)) Htail)).
    - apply oval_eval_ext=> i; symmetry; exact: HE.
    - intro i; rewrite HE; exact (proj2 (Htest i)). }
  change (oval_eval L test = \sum_(i < n.+1) transport_cut (oval_atom L) (oval_mass L) n i * f i).
  rewrite HL (oval_prefix_eval L n Htest) /tail oval_atomic_tail.
  rewrite big_ord_recr /= /transport_cut ltnn.
  congr (_ + _); last exact: mulrC.
  apply eq_bigr=> i _; rewrite ltn_ord /test /oval_cut_index ltn_ord.
  have Hi : inord (val i) = widen_ord (leqnSn n) i.
  { apply/val_inj; simpl; rewrite inordK //; exact: leq_trans (ltn_ord i) (leqnSn n). }
  by rewrite Hi.
Qed.

Lemma oval_cut_edge_lift (T : nat -> nat -> Prop) n i j : T i j ->
  transport_cut_edge T n (oval_cut_index n i) (oval_cut_index n j).
Proof.
  intro HT; rewrite /oval_cut_index /transport_cut_edge.
  case Hi: (i < n)%N; case Hj: (j < n)%N; simpl.
  - rewrite (inordK (leq_trans Hi (leqnSn n))) (inordK (leq_trans Hj (leqnSn n))).
    apply/orP; right; exact/asboolP.
  - by rewrite leqnn orbT.
  - by rewrite leqnn.
  - by rewrite leqnn.
Qed.

Theorem oval_bidual_cut_hall (T : nat -> nat -> Prop) (L M : OmegaVal R nat) :
  oval_bidual T L M -> forall n,
  real_transport_hall
    (fun i : 'I_n.+1 => transport_cut (oval_atom L) (oval_mass L) n i)
    (fun j : 'I_n.+1 => transport_cut (oval_atom M) (oval_mass L) n j)
    (fun i j : 'I_n.+1 => transport_cut_edge T n i j).
Proof.
  intros HT n S.
  pose edge (i j : 'I_n.+1) := transport_cut_edge T n i j.
  pose N := matching_neighbors edge finset.setT S.
  pose f (i : 'I_n.+1) : R := if i \in S then 1 else 0.
  pose g (j : 'I_n.+1) : R := if j \in N then 1 else 0.
  have Hf : oval_test f.
  { intro i; rewrite /f; case: (i \in S); [exact: oval_test_one|exact: oval_test_zero]. }
  have Hg : oval_test g.
  { intro j; rewrite /g; case: (j \in N); [exact: oval_test_one|exact: oval_test_zero]. }
  have Hfg i j : edge i j -> f i <= g j.
  { intro Hij; rewrite /f; case Hi: (i \in S); last exact (proj1 (Hg j)).
    have HN : j \in N.
    { apply/matching_neighborsP; split; first by rewrite inE.
      exists i; by split. }
    by rewrite /g HN. }
  have H := proj1 HT (fun i => f (oval_cut_index n i)) (fun j => g (oval_cut_index n j))
    (fun i => Hf _) (fun j => Hg _) (fun i j Hij => Hfg _ _ (oval_cut_edge_lift n Hij)).
  rewrite (oval_cut_eval L Hf) (oval_cut_eval M Hg) -(oval_bidual_mass HT) in H.
  have HS : (\sum_(i < n.+1) transport_cut (oval_atom L) (oval_mass L) n i * f i) =
      \sum_(i in S) transport_cut (oval_atom L) (oval_mass L) n i.
  { rewrite [RHS]big_mkcond; apply eq_bigr=> i _; rewrite /f.
    by case: (i \in S); rewrite ?mulr1 ?mulr0. }
  have HN : (\sum_(j < n.+1) transport_cut (oval_atom M) (oval_mass L) n j * g j) =
      \sum_(j in N) transport_cut (oval_atom M) (oval_mass L) n j.
  { rewrite [RHS]big_mkcond; apply eq_bigr=> j _; rewrite /g.
    by case: (j \in N); rewrite ?mulr1 ?mulr0. }
  by rewrite HS HN in H.
Qed.

(** Actual matrix existence from the established dual contract. The tail
    bounds are derived from OmegaVal continuity, not added as capabilities. *)
Theorem oval_bidual_transport_matrix (T : nat -> nat -> Prop) (L M : OmegaVal R nat) :
  oval_bidual T L M ->
  exists w : nat -> nat -> R,
    (forall i j, 0 <= w i j) /\
    (forall i j, ~ T i j -> w i j = 0) /\
    (forall i, transport_series (w i) = oval_atom L i) /\
    (forall j, transport_series (fun i => w i j) = oval_atom M j) /\
    (forall i m, transport_prefix (w i) m <= oval_atom L i) /\
    (forall j m, transport_prefix (fun i => w i j) m <= oval_atom M j).
Proof.
  intro HT; apply (@countable_real_transport R (oval_atom L) (oval_atom M) (oval_mass L) T).
  - intro i; exact (proj1 (oval_atom_bounds L i)).
  - intro j; exact (proj1 (oval_atom_bounds M j)).
  - exact: oval_prefix_mass_le.
  - rewrite (oval_bidual_mass HT); exact: oval_prefix_mass_le.
  - exact: oval_atomic_tight.
  - rewrite (oval_bidual_mass HT); exact: oval_atomic_tight.
  - exact: oval_bidual_cut_hall.
Qed.
End DomainTransport.

(** Countable Hall/Strassen realization on nat. No supplied joint or plan,
    no finite-support premise, and no normalization to total mass one. *)
Theorem oval_bidual_coupled_nat (R : realType) (T : nat -> nat -> Prop)
    (L M : OmegaVal R nat) : oval_bidual T L M -> oval_coupled T L M.
Proof.
  intro HT; destruct (oval_bidual_transport_matrix HT) as [w [H0 [Hs [Hr [Hc [Hrb Hcb]]]]]].
  apply (@oval_matrix_joint R T L M w H0); auto.
  intros i j Hnz; destruct (pselect (T i j)) as [Hyes|Hno]; first exact Hyes.
  by rewrite (Hs i j Hno) eqxx in Hnz.
Qed.
