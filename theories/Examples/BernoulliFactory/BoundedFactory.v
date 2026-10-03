(** Bounded native factory component. Programs use SubEnumQ; EnumQ appears
    only in the finite-analysis bridge to the existing binary convergence
    certificate. The raw projection preserves list positions and weights;
    no sampling conversion or normalization takes place during execution. *)
From Coq Require Import Utf8.

Set Warnings "-notation-overridden,-ambiguous-paths".
Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
From Coq Require Import List Morphisms.
From Coq.Program Require Import Equality.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssralg ssrnum order rat.
From PTree Require Import PTreeFacts.
From PTree.Eq.Backend Require Import SubEnumQ.
From PTree.Eq Require Import PTreeKernel UnifiedFrontier.
From PTree.Eq.FreeOmega Require Import Hitting.
From PTree.Prob.Interface Require Import Measure AE Omega Mixed Iteration.
From PTree.Prob.Backend.Common Require Import FiniteEnum FiniteSubdist FiniteRecordExtensionality.
From PTree.Prob.Backend.SubEnumQ Require Import Representation Measure.
From PTree.Prob.Backend.EnumQ Require Import Representation Bind Iteration FrontierLift Measure Support.
Require Import PTree.Prob.FreeOmega.Definition.
From PTree.Prob.FreeOmega Require Import Observation StructuralMeasure SupportLift Support Quotient Measure.
From PTree.Interp.FreeOmega Require Import IterationSummary Rewriting.
From PTree.Examples.BernoulliFactory Require Import VonNeumannUnbounded RationalBernoulli BernoulliFactory.
Import EnumQ GRing.Theory Num.Theory Order.Theory FreeOmegaRewriting.
Local Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.

Module BoundedFactory.
Lemma fair_bounded : enumQ_subprob vn_fair.
Proof. change (enumQ_expect (λ _, 1) vn_fair <= 1). rewrite vn_fair_total. exact: lexx. Qed.
Definition fair_coin : SubEnumQ bool := enumQ_as_subprob fair_bounded.
Lemma bernoulli_bounded q (q0 : 0 <= q) (q1 : q <= 1) :
  enumQ_subprob (rational_bernoulli_measure q0 q1).
Proof. change (enumQ_expect (λ _, 1) (rational_bernoulli_measure q0 q1) <= 1).
  rewrite rational_bernoulli_total. exact: lexx. Qed.
Definition bernoulli q (q0 : 0 <= q) (q1 : q <= 1) : SubEnumQ bool :=
  enumQ_as_subprob (bernoulli_bounded q0 q1).
Lemma fair_coin_raw : subenumQ_raw fair_coin = vn_fair.
Proof. reflexivity. Qed.
Lemma bernoulli_raw q (q0 : 0 <= q) (q1 : q <= 1) :
  subenumQ_raw (bernoulli q0 q1) = rational_bernoulli_measure q0 q1.
Proof. reflexivity. Qed.
Definition kernel x : SubEnumQ (rat+bool) :=
  sem_bind fair_coin (λ b, sem_ret (binary_round_result x b)).
Lemma kernel_raw x : subenumQ_raw (kernel x) = binary_coin_transition x.
Proof. exact (fair_binary_round_measure x). Qed.

Local Notation MN := SubEnumQ.
Local Notation MF := (FreeOmega MN).
Local Notation FI := (FreeOmegaObservableSemanticMeasure
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation FO := (FreeOmegaObservableSemanticOmega
  (NI := SubEnumQ_SemanticMeasure) (NO := SubEnumQ_SemanticOmega)).
Local Notation head := (stable_head factoryE MN bool).
Definition value (h : head) : bool :=
  match h with FHRet b => b | FHVis _ e _ => match e with end end.
Definition heads q := iteration_frontier (E := factoryE) kernel q.
Definition rows n q := iteration_observation_round kernel (λ b, b) n q.

(** Reuse the old scalar analysis, not its EnumQ program-equivalence theorem. *)
Lemma rows_raw n q : subenumQ_raw (rows n q) = meas_iter_approx n binary_coin_transition q.
Proof.
  revert q; induction n as [|n IH]; intro q; [reflexivity|].
  change (bind_EnumQ (subenumQ_raw (kernel q)) (λ next, subenumQ_raw
    (match next with inl x => rows n x | inr b => sem_ret b end)) =
    bind_EnumQ (binary_coin_transition q) (λ next,
    match next with inl x => meas_iter_approx n binary_coin_transition x | inr b => ret_EnumQ b end)).
  rewrite kernel_raw. apply finite_enum_bind_ext_eq. intros [x|b]; [apply IH|reflexivity].
Qed.
Lemma rows_limit q (q0 : 0 <= q) (q1 : q <= 1) :
  sem_lub (λ n, rows n q) (bernoulli q0 q1).
Proof.
  intros P eps Heps.
  destruct (rational_binary_iteration_converges q0 q1 P Heps) as [N HN].
  exists N. intros n Hn. change (`|enumQ_expect (λ b, if P b then 1 else 0) (subenumQ_raw (rows n q)) -
    enumQ_expect (λ b, if P b then 1 else 0) (rational_bernoulli_measure q0 q1)| < eps).
  rewrite rows_raw. exact (HN n Hn).
Qed.
Lemma heads_observe q (q0 : 0 <= q) (q1 : q <= 1) :
  free_omega_observes value (heads q) (bernoulli q0 q1).
Proof. apply iteration_frontier_observes with (value := λ b, b);
  [reflexivity|apply rows_limit]. Qed.
Lemma row_support n q P :
  free_omega_ae (λ h, P (value h)) (iteration_frontier_round (E := factoryE) kernel n q)
  ↔ sem_ae (rows n q) P.
Proof.
  revert q; induction n as [|n IH]; intro q.
  - split; intro H; [intros w b Hin; contradiction|constructor].
  - cbn [iteration_frontier_round ptree_iter_round_approx mixed_iter_approx
      rows iteration_observation_round mixed_bind sem_bind sem_ret
      FreeOmegaMixedMeasure FreeOmegaObservableSemanticMeasure free_omega_bind].
    rewrite sem_ae_bind_iff. split; intro H.
    + apply free_omega_ae_sample_inv in H. eapply sem_ae_mono; [|exact H].
      intros [x|b] Hb; [apply (proj1 (IH x)); exact Hb|].
      dependent destruction Hb. apply sem_ae_ret. assumption.
    + eapply FOAESample; [exact H|]. intros [x|b] Hb.
      * apply (proj2 (IH x)); exact Hb.
      * constructor. exact ((proj1 (sem_ae_ret_iff _ _)) Hb).
Qed.
Lemma heads_support q (q0 : 0 <= q) (q1 : q <= 1) P :
  free_omega_ae (λ h, P (value h)) (heads q) ↔ sem_ae (bernoulli q0 q1) P.
Proof.
  change (free_omega_ae (λ h, P (value h)) (FOLub (λ n, iteration_frontier_round kernel n q)) ↔
    enumQ_ae (rational_bernoulli_measure q0 q1) P).
  rewrite (enumQ_converges_ae_iff (enumQ_iter_approx_increasing binary_coin_transition q)
    (rational_binary_iteration_converges q0 q1)).
  split.
  - intro H. dependent destruction H. intro n. rewrite -(rows_raw n q).
    exact ((proj1 (row_support n q P)) (H n)).
  - intro H. constructor. intro n. apply (proj2 (row_support n q P)).
    change (enumQ_ae (subenumQ_raw (rows n q)) P). rewrite rows_raw. apply H.
Qed.
Definition direct_heads q (q0 : 0 <= q) (q1 : q <= 1) : MF head :=
  FOSample (bernoulli q0 q1) (λ b, FORet (FHRet b)).
Lemma direct_support q (q0 : 0 <= q) (q1 : q <= 1) P :
  free_omega_ae (λ h, P (value h)) (direct_heads q0 q1) ↔ sem_ae (bernoulli q0 q1) P.
Proof.
  split; intro H.
  - apply free_omega_ae_sample_inv in H. eapply sem_ae_mono; [|exact H].
    intros b Hb. inversion Hb; subst. assumption.
  - eapply FOAESample; [exact H|]. intros b Hb. constructor. exact Hb.
Qed.
Lemma heads_lift q (q0 : 0 <= q) (q1 : q <= 1) sim :
  free_omega_qlift (stable_head_rel eq sim) (heads q) (direct_heads q0 q1).
Proof.
  eapply FOQLObserve with (obsA := value) (obsB := value)
    (outA := bernoulli q0 q1) (outB := bernoulli q0 q1) (S := eq).
  - apply heads_observe.
  - have Hunit : sem_bind (bernoulli q0 q1) (λ b, sem_ret b) = bernoulli q0 q1.
    { apply finite_subdist_raw_eq.
      change (finite_enum_raw (finite_enum_bind (subenumQ_raw (bernoulli q0 q1))
        (λ b, finite_enum_ret _ b)) = finite_enum_raw (subenumQ_raw (bernoulli q0 q1))).
      by rewrite finite_enum_bind_right_unit_eq. }
    rewrite -Hunit.
    constructor. intro b. constructor.
  - apply sem_lift_refl. intro b. reflexivity.
  - intros [b|X e k] [c|Y f l] H; try destruct e; try destruct f.
    constructor. exact H.
  - eapply free_omega_support_lift_observation_ae with
      (obsA := value) (obsB := value) (outA := bernoulli q0 q1) (outB := bernoulli q0 q1) (S := eq).
    + apply heads_support.
    + apply direct_support.
    + apply sem_lift_refl. intro b. reflexivity.
    + intros [b|X e k] [c|Y f l] H; try destruct e; try destruct f.
      constructor. exact H.
Qed.
Theorem fair_factory_direct q (q0 : 0 <= q) (q1 : q <= 1) :
  factory_with_sampler (Prob fair_coin (λ b, Ret b) : ptree factoryE MN bool) q ≈ₚ
    Prob (bernoulli q0 q1) (λ b, Ret b).
Proof.
  unfold factory_with_sampler, factory_sampler_step.
  setoid_rewrite peutt_bind_prob. setoid_rewrite peutt_bind_ret_l.
  eapply peutt_of_hitting_lift.
  - eapply (iteration_frontier_summary_hitting (transition := kernel)); try typeclasses eauto.
    intro x. apply stable_hitting_native_sample. intro b. apply stable_hitting_native_ret.
  - apply (stable_hitting_prob (FI := FI) (FO := FO) (MX := FreeOmegaMixedMeasure))
      with (Good := λ _, True); [apply sem_ae_true|].
    intros b _. apply stable_hitting_ret.
  - apply heads_lift.
Qed.
End BoundedFactory.
