From Coq Require Import Utf8.

From PTree.Prob.Backend.SubEnumQ Require Import Expectation.
From PTree.Prob.Backend.Common Require Import FiniteEnum.
(** Role: Native rational convergence and real expectation limits. No FreeOmega dependency. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From Coq.Arith Require Import PeanoNat.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat ssralg ssrnum order rat reals interval.
From mathcomp.classical Require Import classical_sets.
Require Import PTree.Prob.Backend.Common.FiniteAtoms PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Bind PTree.Prob.Backend.EnumQ.Iteration PTree.Prob.Backend.EnumQ.Support PTree.Prob.Backend.EnumQ.SemanticCoupling.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ PTree.Prob.Backend.EnumQ.Map GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.


Section RationalLimit.
Variable R : realType.

Lemma rat_monotone_limit_bound (values : nat → rat) out :
  (∀ n, values n <= values (S n)) →
  (∀ eps : rat, 0 < eps → ∃ N,
    ∀ n, Peano.le N n → `|values n - out| < eps) →
  ∀ n, values n <= out.
Proof.
  intros Hi Hlim n.
  have Hmono : ∀ i j, Peano.le i j -> values i <= values j.
  { intros i j Hle. induction Hle; [exact: lexx|].
    eapply le_trans; [exact IHHle|exact (Hi m)]. }
  case: (leP (values n) out)=> [Hyes|Hno]; [by []|].
  have Heps : 0 < values n - out by rewrite subr_gt0.
  destruct (Hlim _ Heps) as [N HN].
  have Htest := HN (Nat.max N n) (Nat.le_max_l N n).
  have Hlower : values n - out <= values (Nat.max N n) - out.
  { rewrite lerD2r. exact (Hmono n _ (Nat.le_max_r N n)). }
  have Hbad := le_lt_trans (le_trans Hlower (ler_norm _)) Htest.
  rewrite ltxx in Hbad. discriminate.
Qed.

Lemma rat_monotone_limit_upper (values : nat → rat) out :
  (∀ n, values n <= values (S n)) →
  (∀ eps : rat, 0 < eps → ∃ N,
    ∀ n, Peano.le N n → `|values n - out| < eps) →
  countable_upper (λ n, (ratr (values n) : R)) = ratr out.
Proof.
  intros Hi Hlim.
  have Hb : ∀ n, (ratr (values n) : R) <= ratr out.
  { intro n. rewrite ler_rat. exact (rat_monotone_limit_bound Hi Hlim n). }
  apply/eqP. rewrite eq_le. apply/andP. split.
  - exact (countable_upper_le Hb).
  - case: (leP (ratr out : R) (countable_upper (λ n, ratr (values n))))=> [Hyes|Hno];
      [by []|].
    have Hgap : 0 < (ratr out : R) - countable_upper (λ n, ratr (values n))
      by rewrite subr_gt0.
    destruct (rat_in_itvoo Hgap) as [eps Heps].
    move: Heps. rewrite in_itv /= => /andP [Heps0 Hepsgap].
    have Hepsrat : (0 : rat) < eps by move: Heps0; rewrite ltr0q.
    destruct (Hlim eps Hepsrat) as [N HN].
    have Hnear := HN N (Nat.le_refl N).
    have Hlower : out - eps < values N.
    { move: Hnear. rewrite ltr_norml => /andP [Hlo _].
      move: Hlo. by rewrite ltrBrDr addrC. }
    have Hreal : (ratr out : R) - ratr eps < ratr (values N).
    { rewrite -rmorphB ltr_rat. exact Hlower. }
    have Hsup : countable_upper (λ n, (ratr (values n) : R)) < ratr out - ratr eps.
    { move: Hepsgap. by rewrite ltrBrDr addrC -ltrBrDr. }
    have Hbad := lt_le_trans (lt_trans Hsup Hreal)
      (@countable_upper_ge R (λ n, ratr (values n)) (ratr out) N Hb).
    rewrite ltxx in Hbad. discriminate.
Qed.
End RationalLimit.

Section FiniteAtomicLimit.
Variable R : realType.
Local Notation expect := (enumQ_real_expect (R := R)).

Lemma enumQ_real_expect_atom_le {A : eqType} (f : A → R) mu nu :
  (∀ x, 0 <= f x) →
  (∀ x, ratr ((acc_mass x mu)) <= (ratr ((acc_mass x nu)) : R)) →
  expect f mu <= expect f nu.
Proof.
  intro Hf. move: mu nu. refine (enumQ_size_induction (P := λ mu, ∀ nu,
    (∀ x, ratr ((acc_mass x mu)) <= (ratr ((acc_mass x nu)) : R)) ->
    expect f mu <= expect f nu) _).
  intros mu IH nu Hmass. case Hraw: (enumQ_raw mu)=> [|[p a] tail].
  - rewrite /enumQ_real_expect Hraw /=; apply enumQ_real_expect_nonnegative. exact Hf.
  - rewrite (enumQ_real_expect_filter_split f mu a).
    rewrite (enumQ_real_expect_filter_split f nu a). apply lerD.
    + apply ler_wpM2r; [exact (Hf a)|exact (Hmass a)].
    + apply IH.
      * change (List.length (List.filter (λ px, snd px != a) (enumQ_raw mu)) < List.length (enumQ_raw mu))%coq_nat.
        rewrite Hraw /= eq_refl /=.
        apply Nat.lt_succ_r; apply List.filter_length_le.
      * intro x. rewrite !(@acc_mass_filter A (λ y, y != a)).
        destruct (x != a); [apply Hmass|exact: lexx].
Qed.

Lemma enumQ_indicator_atom {A : eqType} (mu : EnumQ A) a :
  enumQ_expect (λ x, if x == a then 1 else 0) mu = (acc_mass a mu).
Proof.
  change (finite_expect (λ x, if x == a then 1 else 0) (enumQ_raw mu) = finite_atom a (enumQ_raw mu)).
  reflexivity.
Qed.

Theorem enumQ_real_expect_atomic_lub {A : eqType} (out : EnumQ A)
    (chain : nat → EnumQ A) (f : A → R) :
  (∀ x, 0 <= f x) →
  (∀ x n, ratr ((acc_mass x (chain n))) <=
    (ratr ((acc_mass x (chain (S n)))) : R)) →
  (∀ x, countable_upper (λ n, (ratr ((acc_mass x (chain n))) : R)) =
    ratr ((acc_mass x out))) →
  (∀ x n, (ratr ((acc_mass x (chain n))) : R) <= ratr ((acc_mass x out))) →
  countable_upper (λ n, expect f (chain n)) = expect f out.
Proof.
  intro Hf. revert chain.
  refine (enumQ_size_induction (P := λ out, ∀ chain,
    (∀ x n, ratr ((acc_mass x (chain n))) <=
      (ratr ((acc_mass x (chain (S n)))) : R)) ->
    (∀ x, countable_upper (λ n, (ratr ((acc_mass x (chain n))) : R)) =
      ratr ((acc_mass x out))) ->
    (∀ x n, (ratr ((acc_mass x (chain n))) : R) <= ratr ((acc_mass x out))) ->
    countable_upper (λ n, expect f (chain n)) = expect f out) _ out).
  intros target IH chain Hinc Hlim Hbound.
  have Hexpect : ∀ n, expect f (chain n) <= expect f target.
  { intro n. apply enumQ_real_expect_atom_le; [exact Hf|]. intro x. exact (Hbound x n). }
  case Hraw: (enumQ_raw target)=> [|[p a] tail].
  - have Hzero : expect f target = 0 by rewrite /enumQ_real_expect Hraw.
    rewrite Hzero in Hexpect *.
    apply/eqP. rewrite eq_le. apply/andP. split.
    + exact (countable_upper_le Hexpect).
    + cbn [enumQ_real_expect]. eapply le_trans.
      * exact (enumQ_real_expect_nonnegative (chain 0%nat) Hf).
      * exact (@countable_upper_ge R (λ n, expect f (chain n)) 0 0%nat Hexpect).
  - pose (rest := λ mu : EnumQ A, enumQ_filter (λ h, snd h != a) mu).
    have Hrest : countable_upper (λ n, expect f (rest (chain n))) =
        expect f (rest target).
    { apply IH.
      - change (List.length (List.filter (λ px, snd px != a) (enumQ_raw target)) < List.length (enumQ_raw target))%coq_nat.
        rewrite Hraw /= eq_refl /=.
        apply Nat.lt_succ_r; apply List.filter_length_le.
      - intros x n. rewrite /rest !(@acc_mass_filter A (λ y, y != a)).
        destruct (x != a); [apply Hinc|exact: lexx].
      - intro x.
        have Heq : (λ n, (ratr ((acc_mass x (rest (chain n)))) : R)) =
          (λ n, ratr ((if x != a then acc_mass x (chain n) else sumq nil))).
        { apply functional_extensionality=> n.
          by rewrite /rest (@acc_mass_filter A (λ y, y != a)). }
        rewrite Heq /rest (@acc_mass_filter A (λ y, y != a)). destruct (x != a).
        + exact (Hlim x).
        + apply countable_upper_constant.
      - intros x n. rewrite /rest !(@acc_mass_filter A (λ y, y != a)).
        destruct (x != a); [apply Hbound|exact: lexx]. }
    have Hsplit : (λ n, expect f (chain n)) =
      (λ n, f a * ratr ((acc_mass a (chain n))) + expect f (rest (chain n))).
    { apply functional_extensionality=> n.
      rewrite (enumQ_real_expect_filter_split f (chain n) a) mulrC. reflexivity. }
    rewrite Hsplit.
    rewrite (@countable_upper_add R
      (λ n, f a * ratr ((acc_mass a (chain n))))
      (λ n, expect f (rest (chain n)))
      (f a * ratr ((acc_mass a target))) (expect f (rest target))).
    + rewrite (@countable_upper_scale R _ (f a) (ratr ((acc_mass a target)))
        (Hf a) (Hbound a)) Hlim Hrest.
      rewrite (enumQ_real_expect_filter_split f target a) mulrC. reflexivity.
    + intro n. exact (ler_wpM2l (Hf a) (Hinc a n)).
    + intro n. apply enumQ_real_expect_atom_le; [exact Hf|]. intro x.
      rewrite /rest !(@acc_mass_filter A (λ y, y != a)). destruct (x != a); [apply Hinc|exact: lexx].
    + intro n. exact (ler_wpM2l (Hf a) (Hbound a n)).
    + intro n. apply enumQ_real_expect_atom_le; [exact Hf|]. intro x.
      rewrite /rest !(@acc_mass_filter A (λ y, y != a)). destruct (x != a); [apply Hbound|exact: lexx].
Qed.
End FiniteAtomicLimit.

Section NativeObservationLimit.
Variable R : realType.
Local Notation expect := (enumQ_real_expect (R := R)).

Lemma enumQ_monotone_converges_upper_eqtype {A : eqType}
    (chain : nat → EnumQ A) out (f : A → R) :
  enumQ_chain_increasing chain → enumQ_converges chain out →
  (∀ x, 0 <= f x) →
  countable_upper (λ n, expect f (chain n)) = expect f out.
Proof.
  intros Hmono Hlim Hf.
  have Hstep : ∀ x n, (acc_mass x (chain n)) <= (acc_mass x (chain (S n))).
  { intros x n. rewrite -!enumQ_indicator_atom.
    exact (Hmono (λ y, y == x) n (S n) (Nat.le_succ_diag_r n)). }
  have Hatom : ∀ x eps, (0 : rat) < eps -> exists N,
      ∀ n, Peano.le N n ->
        `|(acc_mass x (chain n)) - (acc_mass x out)| < eps.
  { intros x eps Heps. destruct (Hlim (λ y, y == x) eps Heps) as [N HN].
    exists N. intros n Hn. rewrite -!enumQ_indicator_atom. exact (HN n Hn). }
  apply enumQ_real_expect_atomic_lub; [exact Hf| | |].
  - intros x n. rewrite ler_rat. exact (Hstep x n).
  - intro x. apply rat_monotone_limit_upper; [exact (Hstep x)|exact (Hatom x)].
  - intros x n. rewrite ler_rat. exact (rat_monotone_limit_bound (Hstep x) (Hatom x) n).
Qed.

Import EnumQCouplingClassical.
Theorem enumQ_monotone_converges_upper {A : Type}
    (chain : nat → EnumQ A) out (f : A → R) :
  enumQ_chain_increasing chain → enumQ_converges chain out →
  (∀ x, 0 <= f x) →
  countable_upper (λ n, expect f (chain n)) = expect f out.
Proof.
  exact (@enumQ_monotone_converges_upper_eqtype
    (@Equality.Pack (EnumQCouplingClassical.carrier A)
      (Equality.on (EnumQCouplingClassical.carrier A))) chain out f).
Qed.

Lemma enumQ_real_expect_indicator {A} (mu : EnumQ A) (P : A → bool) :
  expect (λ x, if P x then 1 else 0) mu =
  ratr (enumQ_expect (λ x, if P x then 1 else 0) mu).
Proof.
  rewrite (_ : (λ x, if P x then (1 : R) else 0) =
      (λ x, ratr (if P x then (1 : rat) else 0)));
    last by apply functional_extensionality=> x; case: (P x); rewrite ?rmorph1 ?rmorph0.
  apply enumQ_real_expect_rat.
Qed.
End NativeObservationLimit.
