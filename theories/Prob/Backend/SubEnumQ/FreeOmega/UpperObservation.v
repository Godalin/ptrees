From PTree.Prob.Backend.SubEnumQ Require Import Expectation.
(** Role: Concrete probability infrastructure. Depends on measure interfaces/realization; not PTree equality theory. *)
Set Warnings "-notation-overridden".
Set Warnings "-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List.
From Coq.Arith Require Import PeanoNat.
From Coq.Logic Require Import FunctionalExtensionality.
From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat ssralg ssrnum order rat reals interval.
From mathcomp.classical Require Import classical_sets.
Require Import PTree.Prob.Backend.Common.RatSubTypes PTree.Prob.Backend.EnumQ.Representation PTree.Prob.Backend.EnumQ.Map PTree.Prob.Backend.EnumQ.Bind PTree.Prob.Backend.EnumQ.Iteration PTree.Prob.Backend.EnumQ.Support PTree.Prob.Backend.EnumQ.SemanticCoupling.
Require Import PTree.Prob.Interface.Measure PTree.Prob.Interface.Subprobability PTree.Prob.Interface.AE PTree.Prob.Interface.Coupling PTree.Prob.Interface.Omega PTree.Prob.Interface.Mixed.
Require Import PTree.Prob.Backend.SubEnumQ.Measure.
Require Import PTree.Prob.FreeOmega.Definition PTree.Prob.FreeOmega.Approximation PTree.Prob.FreeOmega.Observation PTree.Prob.FreeOmega.StructuralMeasure PTree.Prob.FreeOmega.SupportLift PTree.Prob.FreeOmega.Quotient PTree.Prob.FreeOmega.Measure.
Require Import PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperExpectation PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperCoupling PTree.Prob.Backend.SubEnumQ.FreeOmega.UpperContinuity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import EnumQ PTree.Prob.Backend.EnumQ.Map RatSubTypes GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

(** Observation uses a native, eventwise rational limit.  The first part
    connects this existing limit notion to real-valued upper expectations;
    no numerical consistency axiom is added to the measure interface. *)
Section RationalLimit.
Variable R : realType.

Lemma rat_monotone_limit_bound (values : nat -> rat) out :
  (forall n, values n <= values (S n)) ->
  (forall eps : rat, 0 < eps -> exists N,
    forall n, Peano.le N n -> `|values n - out| < eps) ->
  forall n, values n <= out.
Proof.
  intros Hi Hlim n.
  have Hmono : forall i j, Peano.le i j -> values i <= values j.
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

Lemma rat_monotone_limit_upper (values : nat -> rat) out :
  (forall n, values n <= values (S n)) ->
  (forall eps : rat, 0 < eps -> exists N,
    forall n, Peano.le N n -> `|values n - out| < eps) ->
  countable_upper (fun n => (ratr (values n) : R)) = ratr out.
Proof.
  intros Hi Hlim.
  have Hb : forall n, (ratr (values n) : R) <= ratr out.
  { intro n. rewrite ler_rat. exact (rat_monotone_limit_bound Hi Hlim n). }
  apply/eqP. rewrite eq_le. apply/andP. split.
  - exact (countable_upper_le Hb).
  - case: (leP (ratr out : R) (countable_upper (fun n => ratr (values n))))=> [Hyes|Hno];
      [by []|].
    have Hgap : 0 < (ratr out : R) - countable_upper (fun n => ratr (values n))
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
    have Hsup : countable_upper (fun n => (ratr (values n) : R)) < ratr out - ratr eps.
    { move: Hepsgap. by rewrite ltrBrDr addrC -ltrBrDr. }
    have Hbad := lt_le_trans (lt_trans Hsup Hreal)
      (@countable_upper_ge R (fun n => ratr (values n)) (ratr out) N Hb).
    rewrite ltxx in Hbad. discriminate.
Qed.
End RationalLimit.

Section FiniteAtomicLimit.
Variable R : realType.
Local Notation expect := (enumQ_real_expect (R := R)).

Lemma enumQ_real_expect_atom_le {A : eqType} (f : A -> R) mu nu :
  (forall x, 0 <= f x) ->
  (forall x, ratr (Qval (acc_mass x mu)) <= (ratr (Qval (acc_mass x nu)) : R)) ->
  expect f mu <= expect f nu.
Proof.
  intro Hf. move: mu nu. refine (seq_strong_induction (P := fun mu => forall nu,
    (forall x, ratr (Qval (acc_mass x mu)) <= (ratr (Qval (acc_mass x nu)) : R)) ->
    expect f mu <= expect f nu) _).
  intros mu IH nu Hmass. destruct mu as [|[p a] tail].
  - apply enumQ_real_expect_nonnegative. exact Hf.
  - rewrite (enumQ_real_expect_filter_split f ((p,a)::tail) a).
    rewrite (enumQ_real_expect_filter_split f nu a). apply lerD.
    + apply ler_wpM2r; [exact (Hf a)|exact (Hmass a)].
    + apply IH.
      * apply/ssrnat.ltP. rewrite size_filter /= eq_refl /=.
        apply/ssrnat.ltP. exact: leq_ltn_trans (count_size _ _) (ltnSn _).
      * intro x. rewrite !(@acc_mass_filter A (fun y => y != a)).
        destruct (x != a); [apply Hmass|exact: lexx].
Qed.

Lemma enumQ_indicator_atom {A : eqType} (mu : EnumQ A) a :
  enumQ_expect (fun x => if x == a then 1 else 0) mu = Qval (acc_mass a mu).
Proof.
  induction mu as [|[p x] tail IH]; cbn [enumQ_expect]; [reflexivity|].
  rewrite acc_mass_cons IH. cbn [fst snd]. destruct (x == a).
  - change (Qval p * 1 + Qval (acc_mass a tail) = Qval (acc_mass a tail) + Qval p).
    rewrite mulr1. exact: addrC.
  - change (Qval p * 0 + Qval (acc_mass a tail) = Qval (acc_mass a tail) + 0).
    by rewrite mulr0 add0r addr0.
Qed.

Theorem enumQ_real_expect_atomic_lub {A : eqType} (out : EnumQ A)
    (chain : nat -> EnumQ A) (f : A -> R) :
  (forall x, 0 <= f x) ->
  (forall x n, ratr (Qval (acc_mass x (chain n))) <=
    (ratr (Qval (acc_mass x (chain (S n)))) : R)) ->
  (forall x, countable_upper (fun n => (ratr (Qval (acc_mass x (chain n))) : R)) =
    ratr (Qval (acc_mass x out))) ->
  (forall x n, (ratr (Qval (acc_mass x (chain n))) : R) <= ratr (Qval (acc_mass x out))) ->
  countable_upper (fun n => expect f (chain n)) = expect f out.
Proof.
  intro Hf. revert chain.
  refine (seq_strong_induction (P := fun out => forall chain,
    (forall x n, ratr (Qval (acc_mass x (chain n))) <=
      (ratr (Qval (acc_mass x (chain (S n)))) : R)) ->
    (forall x, countable_upper (fun n => (ratr (Qval (acc_mass x (chain n))) : R)) =
      ratr (Qval (acc_mass x out))) ->
    (forall x n, (ratr (Qval (acc_mass x (chain n))) : R) <= ratr (Qval (acc_mass x out))) ->
    countable_upper (fun n => expect f (chain n)) = expect f out) _ out).
  intros target IH chain Hinc Hlim Hbound.
  have Hexpect : forall n, expect f (chain n) <= expect f target.
  { intro n. apply enumQ_real_expect_atom_le; [exact Hf|]. intro x. exact (Hbound x n). }
  destruct target as [|[p a] tail].
  - apply/eqP. rewrite eq_le. apply/andP. split.
    + exact (countable_upper_le Hexpect).
    + cbn [enumQ_real_expect]. eapply le_trans.
      * exact (enumQ_real_expect_nonnegative (chain 0%nat) Hf).
      * exact (@countable_upper_ge R (fun n => expect f (chain n)) 0 0%nat Hexpect).
  - pose (rest := fun mu : EnumQ A => [seq h <- mu | snd h != a]).
    have Hrest : countable_upper (fun n => expect f (rest (chain n))) =
        expect f (rest ((p,a)::tail)).
    { apply IH.
      - apply/ssrnat.ltP. rewrite /rest size_filter /= eq_refl /=.
        apply/ssrnat.ltP. exact: leq_ltn_trans (count_size _ _) (ltnSn _).
      - intros x n. rewrite /rest !(@acc_mass_filter A (fun y => y != a)).
        destruct (x != a); [apply Hinc|exact: lexx].
      - intro x.
        have Heq : (fun n => (ratr (Qval (acc_mass x (rest (chain n)))) : R)) =
          (fun n => ratr (Qval (if x != a then acc_mass x (chain n) else sumq nil))).
        { apply functional_extensionality=> n.
          by rewrite /rest (@acc_mass_filter A (fun y => y != a)). }
        rewrite Heq /rest (@acc_mass_filter A (fun y => y != a)). destruct (x != a).
        + exact (Hlim x).
        + apply countable_upper_constant.
      - intros x n. rewrite /rest !(@acc_mass_filter A (fun y => y != a)).
        destruct (x != a); [apply Hbound|exact: lexx]. }
    have Hsplit : (fun n => expect f (chain n)) =
      (fun n => f a * ratr (Qval (acc_mass a (chain n))) + expect f (rest (chain n))).
    { apply functional_extensionality=> n.
      rewrite (enumQ_real_expect_filter_split f (chain n) a) mulrC. reflexivity. }
    rewrite Hsplit.
    rewrite (@countable_upper_add R
      (fun n => f a * ratr (Qval (acc_mass a (chain n))))
      (fun n => expect f (rest (chain n)))
      (f a * ratr (Qval (acc_mass a ((p,a)::tail)))) (expect f (rest ((p,a)::tail)))).
    + rewrite (@countable_upper_scale R _ (f a) (ratr (Qval (acc_mass a ((p,a)::tail))))
        (Hf a) (Hbound a)) Hlim Hrest.
      rewrite (enumQ_real_expect_filter_split f ((p,a)::tail) a) mulrC. reflexivity.
    + intro n. exact (ler_wpM2l (Hf a) (Hinc a n)).
    + intro n. apply enumQ_real_expect_atom_le; [exact Hf|]. intro x.
      rewrite /rest !(@acc_mass_filter A (fun y => y != a)). destruct (x != a); [apply Hinc|exact: lexx].
    + intro n. exact (ler_wpM2l (Hf a) (Hbound a n)).
    + intro n. apply enumQ_real_expect_atom_le; [exact Hf|]. intro x.
      rewrite /rest !(@acc_mass_filter A (fun y => y != a)). destruct (x != a); [apply Hbound|exact: lexx].
Qed.
End FiniteAtomicLimit.

Section NativeObservationLimit.
Variable R : realType.
Local Notation expect := (enumQ_real_expect (R := R)).

Lemma enumQ_monotone_converges_upper_eqtype {A : eqType}
    (chain : nat -> EnumQ A) out (f : A -> R) :
  enumQ_chain_increasing chain -> enumQ_converges chain out ->
  (forall x, 0 <= f x) ->
  countable_upper (fun n => expect f (chain n)) = expect f out.
Proof.
  intros Hmono Hlim Hf.
  have Hstep : forall x n, Qval (acc_mass x (chain n)) <= Qval (acc_mass x (chain (S n))).
  { intros x n. rewrite -!enumQ_indicator_atom.
    exact (Hmono (fun y => y == x) n (S n) (Nat.le_succ_diag_r n)). }
  have Hatom : forall x eps, (0 : rat) < eps -> exists N,
      forall n, Peano.le N n ->
        `|Qval (acc_mass x (chain n)) - Qval (acc_mass x out)| < eps.
  { intros x eps Heps. destruct (Hlim (fun y => y == x) eps Heps) as [N HN].
    exists N. intros n Hn. rewrite -!enumQ_indicator_atom. exact (HN n Hn). }
  apply enumQ_real_expect_atomic_lub; [exact Hf| | |].
  - intros x n. rewrite ler_rat. exact (Hstep x n).
  - intro x. apply rat_monotone_limit_upper; [exact (Hstep x)|exact (Hatom x)].
  - intros x n. rewrite ler_rat. exact (rat_monotone_limit_bound (Hstep x) (Hatom x) n).
Qed.

Import EnumQCouplingClassical.
Theorem enumQ_monotone_converges_upper {A : Type}
    (chain : nat -> EnumQ A) out (f : A -> R) :
  enumQ_chain_increasing chain -> enumQ_converges chain out ->
  (forall x, 0 <= f x) ->
  countable_upper (fun n => expect f (chain n)) = expect f out.
Proof.
  exact (@enumQ_monotone_converges_upper_eqtype
    (@Equality.Pack (EnumQCouplingClassical.carrier A)
      (Equality.on (EnumQCouplingClassical.carrier A))) chain out f).
Qed.

Lemma enumQ_real_expect_indicator {A} (mu : EnumQ A) (P : A -> bool) :
  expect (fun x => if P x then 1 else 0) mu =
  ratr (enumQ_expect (fun x => if P x then 1 else 0) mu).
Proof.
  rewrite (_ : (fun x => if P x then (1 : R) else 0) =
      (fun x => ratr (if P x then (1 : rat) else 0)));
    last by apply functional_extensionality=> x; case: (P x); rewrite ?rmorph1 ?rmorph0.
  apply enumQ_real_expect_rat.
Qed.
End NativeObservationLimit.

(** Full scalar consistency of the existing observation judgment, including
    formal Lub observations.  This is a theorem about the actual native
    output, not a consistency premise supplied by clients. *)
Section ObservationConsistency.
Variable R : realType.
Local Notation expect := (enumQ_real_expect (R := R)).
Local Notation upper := (free_omega_upper (R := R)).

Theorem free_omega_observes_upper {A O} (obs : A -> O)
    (mu : FreeOmega SubEnumQ A) (out : SubEnumQ O) :
  @free_omega_observes SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
    A O obs mu out ->
  forall f : O -> R, (forall y, 0 <= f y /\ f y <= 1) ->
    upper mu (fun x => f (obs x)) = expect f (subenumQ_raw out).
Proof.
  intro Hobs. induction Hobs as [x| |X node k front Hobs IH|chain outs out Hobs IH Hlim Hinc];
    intros f Hf.
  - change (f (obs x) = ratr (1 : rat) * f (obs x) + 0).
    by rewrite rmorph1 mul1r addr0.
  - reflexivity.
  - change (expect (fun x => upper (k x) (fun y => f (obs y))) (subenumQ_raw node) =
      expect f (bind_EnumQ (subenumQ_raw node) (fun x => subenumQ_raw (front x)))).
    rewrite enumQ_real_expect_bind. f_equal. apply functional_extensionality=> x.
    exact (IH x f Hf).
  - cbn [free_omega_upper].
    have Hrows : (fun n => upper (chain n) (fun x => f (obs x))) =
      (fun n => expect f (subenumQ_raw (outs n))).
    { apply functional_extensionality=> n. exact (IH n f Hf). }
    rewrite Hrows. apply enumQ_monotone_converges_upper; [|exact Hlim|].
    + intros P n m Hnm.
      have HP : forall y, 0 <= (if P y then (1 : R) else 0) /\
          (if P y then (1 : R) else 0) <= 1.
      { intro y. destruct (P y); split; try exact: ler01; exact: lexx. }
      have Hstep : forall i,
          expect (fun y => if P y then 1 else 0) (subenumQ_raw (outs i)) <=
          expect (fun y => if P y then 1 else 0) (subenumQ_raw (outs (S i))).
      { intro i. rewrite -(IH i _ HP) -(IH (S i) _ HP).
        apply free_omega_upper_approx_mono; [exact (Hinc i)|].
        intro x. exact (HP (obs x)). }
      have Hreal := scalar_increasing_le Hstep Hnm.
      rewrite !enumQ_real_expect_indicator ler_rat in Hreal. exact Hreal.
    + intro y. exact (proj1 (Hf y)).
Qed.

Theorem free_omega_denotes_upper {A O} (obs : A -> O)
    (mu : FreeOmega SubEnumQ A) (out : SubEnumQ O) (f : O -> R) :
  @free_omega_denotes SubEnumQ SubEnumQ_SemanticMeasure SubEnumQ_SemanticOmega
    A O obs mu out ->
  (forall y, 0 <= f y /\ f y <= 1) ->
  upper mu (fun x => f (obs x)) = expect f (subenumQ_raw out).
Proof.
  intros [represented [Hobs Heq]] Hf.
  rewrite (free_omega_observes_upper Hobs Hf).
  apply/eqP. rewrite eq_le. apply/andP. split.
  - eapply subenumQ_lift_real_expect; [exact Heq|]. intros x y ->. exact: lexx.
  - eapply subenumQ_lift_real_expect; [apply sem_lift_sym; exact Heq|].
    intros x y ->. exact: lexx.
Qed.
End ObservationConsistency.
