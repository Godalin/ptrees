(** DS4 expressivity witness: an actual guarded PTree uses only finite
    rational coins, while its complete stable-hitting mass can be irrational.
    The real-indexed rational schedule is a classical representation witness,
    not a claim that an arbitrary real input has a computable sampler. *)
Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import Arith.PeanoNat.
From mathcomp Require Import ssreflect ssrbool eqtype choice ssralg ssrnum order rat reals interval.
From mathcomp Require Import trigo pi_irrational.
From PTree.Core Require Import PTreeDefinition.
From PTree.Prob.Domain Require Import Expectation.
From PTree.Prob.Backend.Common Require Import RatSubTypes.
From PTree.Prob.Backend.SubEnum Require Import Measure Expectation.
From PTree.Prob.Backend.SubEnum.FreeOmega Require Import Admissibility.
From PTree.Eq Require Import UnifiedFrontier.
From PTree.Eq.Backend Require Import StableHittingDomainSubEnum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import RatSubTypes GRing.Theory Num.Theory Order.Theory.
Local Open Scope ring_scope.

Section RationalSchedule.
Variable q : nat -> rat.
Hypothesis q_bound : forall n, 0 <= q n /\ q n < 1.
Hypothesis q_increasing : forall n, q n <= q (S n).

Definition continue_weight n := (1 - q (S n)) / (1 - q n).
Lemma continue_weight_nonnegative n : 0 <= continue_weight n.
Proof. apply divr_ge0; rewrite subr_ge0; exact (ltW (proj2 (q_bound _))). Qed.
Lemma continue_weight_le_one n : continue_weight n <= 1.
Proof.
  have Hp : 0 < 1 - q n by rewrite subr_gt0; exact (proj2 (q_bound n)).
  rewrite /continue_weight ler_pdivrMr // mul1r lerD2l lerN2.
  exact: q_increasing.
Qed.
Lemma stop_weight_nonnegative n : 0 <= 1 - continue_weight n.
Proof. rewrite subr_ge0; exact: continue_weight_le_one. Qed.

Definition schedule_coin (n : nat) : SubEnum bool.
Proof.
  refine {| subenum_raw := ((mknnQ (1 - continue_weight n) (stop_weight_nonnegative n), false) ::
    (mknnQ (continue_weight n) (continue_weight_nonnegative n), true) :: nil)%list |}.
  change ((1 - continue_weight n) * 1 + (continue_weight n * 1 + 0) <= 1).
  by rewrite !mulr1 addr0 subrK.
Defined.

Lemma schedule_coin_total n : subenum_total (schedule_coin n).
Proof.
  change ((1 - continue_weight n) * 1 + (continue_weight n * 1 + 0) = 1).
  by rewrite !mulr1 addr0 subrK.
Qed.

Context {E : Type -> Type}.
CoFixpoint scheduled_retry n : ptree E SubEnum unit :=
  Prob (schedule_coin n) (fun again => if again then scheduled_retry (S n) else Ret tt).

Variable R : realType.
Local Notation Hn := (@ptree_domain_approx R E unit).

Lemma scheduled_retry_finite_mass fuel n :
  oval_mass (Hn fuel (observe (scheduled_retry n))) =
  ratr (1 - (1 - q (Nat.add n fuel)) / (1 - q n)).
Proof.
  induction fuel as [|fuel IH] in n |- *.
  - change (oval_eval (Hn O (ProbF (schedule_coin n)
      (fun again => if again then scheduled_retry (S n) else Ret tt))) (fun _ => 1) =
      ratr (1 - (1 - q (Nat.add n O)) / (1 - q n))).
    rewrite ptree_domain_approx_prob_zero Nat.add_0_r divff ?subrr ?rmorph0 //.
    apply/eqP=> Hz; have Hp := proj2 (q_bound n).
    have Hq : q n = 1 by move/eqP: Hz; rewrite subr_eq0=> /eqP <-.
    by rewrite Hq ltxx in Hp.
  - change (oval_eval (Hn (S fuel) (ProbF (schedule_coin n)
      (fun again => if again then scheduled_retry (S n) else Ret tt))) (fun _ => 1) =
      ratr (1 - (1 - q (Nat.add n (S fuel))) / (1 - q n))).
    rewrite ptree_domain_approx_prob_succ.
    change (ratr (1 - continue_weight n) *
      oval_eval (Hn fuel (RetF tt)) (fun _ => 1) +
      (ratr (continue_weight n) * oval_mass (Hn fuel (observe (scheduled_retry (S n)))) + 0) =
      ratr (1 - (1 - q (Nat.add n (S fuel))) / (1 - q n))).
    rewrite ptree_domain_approx_ret mulr1 addr0 IH -rmorphM -rmorphD.
    f_equal.
    have Hnz : 1 - q (S n) != 0 by rewrite gt_eqF // subr_gt0; exact (proj2 (q_bound _)).
    rewrite mulrBr mulr1 addrA subrK.
    rewrite /continue_weight [(_ / _) * (_ / _)]mulrC mulrA divfK //.
    by rewrite Nat.add_succ_r Nat.add_succ_l.
Qed.

Lemma scheduled_retry_from_zero_mass fuel : q O = 0 ->
  oval_mass (Hn fuel (observe (scheduled_retry O))) = ratr (q fuel).
Proof.
  intro H0; rewrite scheduled_retry_finite_mass H0 subr0 divr1.
  by rewrite opprB addrCA subrr addr0.
Qed.

Theorem scheduled_retry_hitting_mass : q O = 0 ->
  oval_mass (ptree_domain_hitting R (observe (scheduled_retry O))) =
  oval_sup (fun n => ratr (q n) : R).
Proof.
  intro H0; apply oval_sup_ext=> n; exact (scheduled_retry_from_zero_mass n H0).
Qed.
End RationalSchedule.

(** Enumerate rational lower bounds and take finite running maxima. Density
    of Q proves that their supremum is alpha; no new choice axiom is added. *)
Section RationalDensity.
Variable R : realType.
Variable alpha : R.
Hypothesis alpha_pos : 0 < alpha.
Hypothesis alpha_lt_one : alpha < 1.

Definition rational_candidate n : rat :=
  match (@unpickle _ n : option rat) with
  | Some r => if (0 <= r) && ((ratr r : R) < alpha) then r else 0
  | None => 0
  end.

Fixpoint rational_chain n : rat :=
  match n with O => 0 | S m => Num.max (rational_chain m) (rational_candidate m) end.

Lemma rational_candidate_nonnegative n : 0 <= rational_candidate n.
Proof.
  rewrite /rational_candidate; case: unpickle=> [r|]; last exact: lexx.
  case: ifP=> [/andP [H0 _]|_]; [exact H0|exact: lexx].
Qed.
Lemma rational_candidate_below n : (ratr (rational_candidate n) : R) < alpha.
Proof.
  rewrite /rational_candidate; case: unpickle=> [r|]; last by rewrite rmorph0.
  case: ifP=> [/andP [_ Hr]|_]; [exact Hr|by rewrite rmorph0].
Qed.
Lemma rational_chain_increasing n : rational_chain n <= rational_chain (S n).
Proof. change (rational_chain n <= Num.max (rational_chain n) (rational_candidate n)); by rewrite le_max lexx. Qed.
Lemma rational_chain_nonnegative n : 0 <= rational_chain n.
Proof.
  induction n; first exact: lexx.
  exact (le_trans IHn (rational_chain_increasing n)).
Qed.
Lemma rational_chain_below n : (ratr (rational_chain n) : R) < alpha.
Proof.
  induction n as [|n IH]; first by rewrite /= rmorph0.
  change (ratr (Num.max (rational_chain n) (rational_candidate n)) < alpha).
  by rewrite maxr_rat gt_max IH rational_candidate_below.
Qed.
Lemma rational_chain_bound n : 0 <= rational_chain n /\ rational_chain n < 1.
Proof.
  split; first exact: rational_chain_nonnegative.
  have H := lt_trans (rational_chain_below n) alpha_lt_one.
  by move: H; rewrite -(rmorph1 (ratr : {rmorphism rat -> R})) ltr_rat.
Qed.

Lemma rational_chain_covers r : 0 <= r -> (ratr r : R) < alpha ->
  r <= rational_chain (S (pickle r)).
Proof.
  intros H0 Hr; change (r <= Num.max (rational_chain (pickle r)) (rational_candidate (pickle r))).
  rewrite /rational_candidate pickleK H0 Hr /=.
  by rewrite le_max lexx orbT.
Qed.

Theorem rational_chain_sup : oval_sup (fun n => ratr (rational_chain n) : R) = alpha.
Proof.
  have Hb n : (ratr (rational_chain n) : R) <= alpha := ltW (rational_chain_below n).
  have Hz := @oval_sup_ge R (fun n => ratr (rational_chain n)) alpha O Hb.
  change (is_true ((ratr (0 : rat) : R) <= oval_sup (fun n => ratr (rational_chain n) : R))) in Hz.
  rewrite rmorph0 in Hz.
  apply/eqP; rewrite eq_le; apply/andP; split; first exact: oval_sup_le.
  rewrite leNgt; apply/negP=> Hlt.
  have [r Hr] := rat_in_itvoo Hlt.
  move: Hr; rewrite in_itv /=; move/andP=> [Hlo Hhi].
  have Hr0 : 0 <= r.
  { have H := le_trans Hz (ltW Hlo); by move: H; rewrite ler0q. }
  have Hcover := rational_chain_covers Hr0 Hhi.
  have Hembed : (ratr r : R) <= ratr (rational_chain (S (pickle r))) by rewrite ler_rat.
  have Hsup := le_trans Hembed (@oval_sup_ge R _ alpha (S (pickle r)) Hb).
  have Hbad := lt_le_trans Hlo Hsup; by rewrite ltxx in Hbad.
Qed.

Definition real_schedule_tree {E : Type -> Type} : ptree E SubEnum unit :=
  @scheduled_retry rational_chain rational_chain_bound rational_chain_increasing E O.

Theorem real_schedule_hitting_mass {E : Type -> Type} :
  oval_mass (ptree_domain_hitting R (observe (@real_schedule_tree E))) = alpha.
Proof.
  rewrite scheduled_retry_hitting_mass; [exact rational_chain_sup|reflexivity].
Qed.
End RationalDensity.

Section IrrationalInstance.
Variable R : realType.
Definition pi_quarter : R := pi / 2 / 2.
Lemma pi_quarter_pos : 0 < pi_quarter.
Proof. apply divr_gt0; [apply divr_gt0; [exact: pi_gt0|by []]|by []]. Qed.
Lemma pi_quarter_lt_one : pi_quarter < 1.
Proof. rewrite /pi_quarter ltr_pdivrMr // mul1r; exact: pihalf_lt2. Qed.
Lemma pi_quarter_irrational : ~ rational pi_quarter.
Proof.
  intros [q _ Hq]; apply (@pi_irrationnal R).
  exists (q * 2 * 2); first exact I.
  rewrite !rmorphM !rmorph_nat.
  change ((ratr q : R) * 2 * 2 = pi).
  rewrite Hq /pi_quarter.
  by rewrite !divfK ?pnatr_eq0.
Qed.

Definition pi_schedule_tree {E : Type -> Type} : ptree E SubEnum unit :=
  @real_schedule_tree R pi_quarter pi_quarter_pos pi_quarter_lt_one E.

Theorem pi_schedule_mass {E : Type -> Type} :
  oval_mass (ptree_domain_hitting R (observe (@pi_schedule_tree E))) = pi_quarter.
Proof. exact: real_schedule_hitting_mass. Qed.

Theorem pi_canonical_hitting_mass {E : Type -> Type} :
  oval_mass (free_omega_domain
    (ptree_canonical_hitting_admissible R (observe (@pi_schedule_tree E)))) = pi_quarter.
Proof.
  transitivity (oval_mass (ptree_domain_hitting R (observe (@pi_schedule_tree E)))).
  - exact (stable_hitting_denotational_adequacy (R := R)
      (ptree_canonical_hitting_spec (observe (@pi_schedule_tree E))) (oval_test_one R)).
  - exact: pi_schedule_mass.
Qed.

Theorem pi_canonical_hitting_irrational {E : Type -> Type} :
  ~ rational (oval_mass (free_omega_domain
    (ptree_canonical_hitting_admissible R (observe (@pi_schedule_tree E))))).
Proof. rewrite pi_canonical_hitting_mass; exact: pi_quarter_irrational. Qed.
End IrrationalInstance.
